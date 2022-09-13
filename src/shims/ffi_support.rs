use libffi::{high::call::*, low::CodePtr};
use std::ops::{Deref, Range};
use std::mem::MaybeUninit;
use std::borrow::Cow;


use rustc_data_structures::stable_hasher::{HashStable, StableHasher};

use rustc_middle::ty::{IntTy, Ty, TyKind, TypeAndMut, UintTy};
use rustc_middle::ty::layout::LayoutOf;
use rustc_span::Symbol;
use rustc_target::abi::{Align, Size};

use crate::*;

/// Representation of a section of memory, starting at a particular
/// address and of a specified length.
/// This is how we represent bytes in an `Allocation` that can't be 
/// owned, since they belong to a foreign process -- in particular, we
/// use this to store pointers to C memory passed back from C FFI calls 
/// in Miri.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[derive(TyEncodable, TyDecodable)]
pub struct AddrAllocBytes {
    /// Address of the beginning of the bytes.
    pub addr: u64,
    /// Size of the type of the data being stored in these bytes.
    pub type_size: usize,
    /// Length of the bytes, in multiples of `type_size`; 
    /// it's in a `RefCell` since it can change depending on how it's used
    /// in the program. UNSAFE
    pub len: std::cell::RefCell<usize>,
}

impl AddrAllocBytes {
    /// Length of the bytes.
    pub fn total_len(&self) -> usize {
        self.type_size * *self.len.borrow()
    }
}

// Satisfy the `Hash` and `HashStable` trait requirements; can't be automatically derived.
impl hash::Hash for AddrAllocBytes {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.addr.hash(state);
        self.type_size.hash(state);
    }
}   
impl<CTX> HashStable<CTX> for AddrAllocBytes {
    fn hash_stable(&self, hcx: &mut CTX, hasher: &mut StableHasher) {
        self.addr.hash_stable(hcx, hasher);
        self.type_size.hash_stable(hcx, hasher);
    }
}

// Types that can be used to represent the `bytes field of an `Allocation`. 
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[derive(TyEncodable, TyDecodable)]
#[derive(HashStable)]
pub enum MachineBytes {
    /// Owned, boxed slice of [u8].
    Boxed(Box<[u8]>),
    /// Address, size of the type stored, and length of the allocation.
    /// This is used for representing pointers to bytes that belong to a 
    /// foreign process (such as pointers into C memory, passed back to Rust
    /// through an FFI call).
    Addr(AddrAllocBytes),
}



    // pub fn from_raw_addr(
    //     addr: u64,
    //     type_size: usize,
    //     len: usize,
    //     align: Align,
    //     mutability: Mutability,
    // ) -> Self {
    //     let addr_alloc_bytes = AddrAllocBytes { addr, type_size, len: std::cell::RefCell::new(len)};
    //     let size = Size::from_bytes(addr_alloc_bytes.total_len());
    //     Self {
    //         bytes: AllocBytes::Addr(addr_alloc_bytes),
    //         relocations: Relocations::new(),
    //         init_mask: InitMask::new(size, true),
    //         align,
    //         mutability,
    //         extra: (),
    //     }
    // }

impl AllocBytes for MachineBytes {

    fn adjust_to_align(&self, _align: Align) -> Self {
        let len = self.get_len();
        match self {
            Self::Boxed(b) => {
                let align_usize: usize = _align.bytes().try_into().unwrap();
                let layout = std::alloc::Layout::from_size_align(len, align_usize).unwrap();
                let mut bytes = unsafe {
                    let buf = std::alloc::alloc(layout);
                    let mut boxed = Box::<[MaybeUninit<u8>]>::from_raw(std::slice::from_raw_parts_mut(buf as *mut MaybeUninit<u8>, len));
                    MachineBytes::write_maybe_uninit_slice(&mut boxed, &b);
                    boxed.assume_init()
                };
                assert!(bytes.as_ptr() as usize % align_usize == 0);
                Self::Boxed(bytes)
            },
            Self::Addr(_) => self
        }
        
    }

    fn uninit<'tcx>(size: Size, align: Align, handle_alloc_fail: () -> InterpError) -> Result<Self, InterpError<'tcx>> {
        let align_usize: usize = align.bytes().try_into().unwrap();
        let layout = std::alloc::Layout::from_size_align(size.bytes_usize(), align_usize).unwrap();
        let vec_align = unsafe {
            // https://doc.rust-lang.org/nightly/std/alloc/trait.GlobalAlloc.html#tymethod.alloc
            // std::alloc::alloc returns null to indicate an allocation failure: 
            // "Returning a null pointer indicates that either memory is exhausted 
            // or layout does not meet this allocator’s size or alignment constraints."
            let buf = std::alloc::alloc(layout);
            // Handle allocation failure.
            if buf.is_null() {
                return Err(handle_alloc_fail())
            } 
            Vec::from_raw_parts(buf as *mut u8, size.bytes_usize(), size.bytes_usize())
        };
        
        let bytes = vec_align.into_boxed_slice();
        assert!(bytes.as_ptr() as u64 % align.bytes() == 0);
        Ok(Self::Boxed(bytes))
    }

    fn from_bytes<'tcx>(slice: impl Into<Cow<'tcx, [u8]>>, _align: Align) -> Self {
        let slice: Cow<'tcx, [u8]> = slice.into();
        let align_usize: usize = _align.bytes().try_into().unwrap();
        let layout = std::alloc::Layout::from_size_align(slice.len(), align_usize).unwrap();
        let bytes = unsafe {
            let buf = std::alloc::alloc(layout);
            let mut boxed = Box::<[MaybeUninit<u8>]>::from_raw(std::slice::from_raw_parts_mut(buf as *mut MaybeUninit<u8>, slice.len()));
            MaybeUninit::write_slice(&mut boxed, &slice);
            boxed.assume_init()
        };
        
        assert!(bytes.as_ptr() as u64 % _align.bytes() == 0);
        Self::Boxed(bytes)
    }

    /// The length of the bytes.
    fn len(&self) -> usize {
        match self {
            Self::Boxed(b) => b.len(),
            Self::Addr(addr_alloc_bytes) => addr_alloc_bytes.total_len(),
        }
    }

    /// The real address of the bytes.
    fn get_addr(&self) -> u64 {
        match self {
            Self::Boxed(b) => b.as_ptr() as u64,
            Self::Addr(AddrAllocBytes{ addr, ..}) => *addr,
        }
    }

    /// Slice of the bytes, for a specified range.
    fn get_slice_from_range(&self, range: Range<usize>) -> &[u8] {
        match &self {
            Self::Boxed(b) => &b[range],
            Self::Addr(AddrAllocBytes { addr, type_size, len }) => {
                unsafe {
                    let addr = *addr as *const u8;
                    let max_len = range.end;
                    let mut cur_len = len.borrow_mut();
                    if max_len/(*type_size) > *cur_len {
                        *cur_len = max_len/(*type_size);
                    }
                    let whole_slice = std::slice::from_raw_parts(addr, (*type_size)*(*cur_len));
                    &whole_slice[range]
                }
            }
        }
    }

    /// Mutable slice of the bytes, for a specified range.
    fn get_slice_from_range_mut<'a>(&'a mut self, range: Range<usize>) -> &'a mut [u8]{
        match self {
            Self::Boxed(ref mut b) => &mut b[range],
            Self::Addr(AddrAllocBytes{..}) => {
                // TODO! Should this be allowed?
                todo!();
            }
        }
    }

    /// Pointer addition to the base address of the bytes.
    fn add_ptr(&mut self, to_add: usize) -> *mut u8 {
        match self {
            Self::Boxed(b) => {
                b.as_mut_ptr().wrapping_add(to_add)
            },
            Self::Addr(AddrAllocBytes{..}) => {
                // TODO! Should this be allowed?
                todo!();
            }
        }
    }

    /// Write an `AllocBytes` to a boxed slice of `MaybeUninit` -- this serves to initialize 
    /// the elements in `boxed`, for the length of the `AllocBytes` passed in.
    fn write_maybe_uninit_slice(boxed: &mut Box<[MaybeUninit<u8>]>, to_write: &Self) {
        match to_write {
            Self::Boxed(ref b) => {
                MaybeUninit::write_slice(boxed, &b);
            },
            Self::Addr(AddrAllocBytes{addr, ..}) => {
                unsafe {
                    let addr = *addr as *const u8;
                    let boxed_len = boxed.len();
                    MaybeUninit::write_slice(boxed, std::slice::from_raw_parts(addr, boxed_len));
                }
            }
        }
    }
}


impl<'mir, 'tcx: 'mir> EvalContextExt<'mir, 'tcx> for crate::MiriEvalContext<'mir, 'tcx> {}

pub trait EvalContextExt<'mir, 'tcx: 'mir>: crate::MiriEvalContextExt<'mir, 'tcx> {

    const C_POINTER_DEFAULT_LEN: usize = 1000;

    /// Extract the scalar value from the result of reading a scalar from the machine,
    /// and convert it to a `CArg`.
    fn scalar_to_carg(
        k: ScalarMaybeUninit<Provenance>,
        arg_type: &Ty<'tcx>,
        cx: &mut MiriEvalContext<'mir, 'tcx>,
    ) -> InterpResult<'tcx, CArg> {
        match arg_type.kind() {
            // If the primitive provided can be converted to a type matching the type pattern
            // then create a `CArg` of this primitive value with the corresponding `CArg` constructor.
            // the ints
            TyKind::Int(IntTy::I8) => {
                return Ok(CArg::Int8(k.to_i8()?));
            }
            TyKind::Int(IntTy::I16) => {
                return Ok(CArg::Int16(k.to_i16()?));
            }
            TyKind::Int(IntTy::I32) => {
                return Ok(CArg::Int32(k.to_i32()?));
            }
            TyKind::Int(IntTy::I64) => {
                return Ok(CArg::Int64(k.to_i64()?));
            }
            TyKind::Int(IntTy::Isize) => {
                return Ok(CArg::ISize(k.to_machine_isize(cx)?.try_into().unwrap()));
            }
            // the uints
            TyKind::Uint(UintTy::U8) => {
                return Ok(CArg::UInt8(k.to_u8()?));
            }
            TyKind::Uint(UintTy::U16) => {
                return Ok(CArg::UInt16(k.to_u16()?));
            }
            TyKind::Uint(UintTy::U32) => {
                return Ok(CArg::UInt32(k.to_u32()?));
            }
            TyKind::Uint(UintTy::U64) => {
                return Ok(CArg::UInt64(k.to_u64()?));
            }
            TyKind::Uint(UintTy::Usize) => {
                return Ok(CArg::USize(k.to_machine_usize(cx)?.try_into().unwrap()));
            }
            // pointers
            TyKind::RawPtr(TypeAndMut { ty: some_ty, mutbl: some_mut }) => {
                match k {
                    ScalarMaybeUninit::Scalar(Scalar::Ptr(mut ptr, ofs)) => {
                        machine::Evaluator::<'mir, 'tcx>::expose_ptr(cx, ptr)?;
                        
                        let qq = ptr.into_parts().1.bytes_usize();
                        match (some_ty.kind(), some_mut) {
                            // int
                            (TyKind::Int(IntTy::I8), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt8(qq as *mut i8));
                            }
                            (TyKind::Int(IntTy::I8), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt8(qq as *const i8));
                            }
                            (TyKind::Int(IntTy::I16), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt16(qq as *mut i16));
                            }
                            (TyKind::Int(IntTy::I16), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt16(qq as *const i16));
                            }
                            (TyKind::Int(IntTy::I32), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt32(qq as *mut i32));
                            }
                            (TyKind::Int(IntTy::I32), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt32(qq as *const i32));
                            }
                            (TyKind::Int(IntTy::I64), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt64(qq as *mut i64));
                            }
                            (TyKind::Int(IntTy::I64), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt64(qq as *const i64));
                            }
                            // uints
                            (TyKind::Uint(UintTy::U8), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt8(qq as *mut u8));
                            }
                            (TyKind::Uint(UintTy::U8), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt8(qq as *const u8));
                            }
                            (TyKind::Uint(UintTy::U16), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt16(qq as *mut u16));
                            }
                            (TyKind::Uint(UintTy::U16), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt16(qq as *const u16));
                            }
                            (TyKind::Uint(UintTy::U32), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt32(qq as *mut u32));
                            }
                            (TyKind::Uint(UintTy::U32), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt32(qq as *const u32));
                            }
                            (TyKind::Uint(UintTy::U64), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt64(qq as *mut u64));
                            }
                            (TyKind::Uint(UintTy::U64), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt64(qq as *const u64));
                            }
                            // recursive case
                            (TyKind::RawPtr(..), _) => {
                                return Ok(CArg::RecCarg(Box::new(Self::scalar_to_carg(
                                    k, some_ty, cx,
                                )?)));
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        // If no primitives were returned then we have an unsupported type.
        throw_unsup_format!(
            "unsupported scalar argument type to external C function: {:?}",
            arg_type
        );
    }

    /// Call external C function and
    /// store output, depending on return type in the function signature.
    fn call_external_c_and_store_return<'a>(
        &mut self,
        link_name: Symbol,
        dest: &PlaceTy<'tcx, Provenance>,
        ptr: CodePtr,
        libffi_args: Vec<libffi::high::Arg<'a>>,
    ) -> InterpResult<'tcx, ()> {
        let this = self.eval_context_mut();

        // Unsafe because of the call to external C code.
        // Because this is calling a C function it is not necessarily sound,
        // but there is no way around this and we've checked as much as we can.
        unsafe {
            // If the return type of a function is a primitive integer type,
            // then call the function (`ptr`) with arguments `libffi_args`, store the return value as the specified
            // primitive integer type, and then write this value out to the miri memory as an integer.
            match dest.layout.ty.kind() {
                // ints
                TyKind::Int(IntTy::I8) => {
                    let x = call::<i8>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Int(IntTy::I16) => {
                    let x = call::<i16>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Int(IntTy::I32) => {
                    let x = call::<i32>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Int(IntTy::I64) => {
                    let x = call::<i64>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Int(IntTy::Isize) => {
                    let x = call::<isize>(ptr, libffi_args.as_slice());
                    // `isize` doesn't `impl Into<i128>`, so convert manually.
                    // Convert to `i64` since this covers both 32- and 64-bit machines.
                    this.write_int(i64::try_from(x).unwrap(), dest)?;
                    return Ok(());
                }
                // uints
                TyKind::Uint(UintTy::U8) => {
                    let x = call::<u8>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Uint(UintTy::U16) => {
                    let x = call::<u16>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Uint(UintTy::U32) => {
                    let x = call::<u32>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Uint(UintTy::U64) => {
                    let x = call::<u64>(ptr, libffi_args.as_slice());
                    this.write_int(x, dest)?;
                    return Ok(());
                }
                TyKind::Uint(UintTy::Usize) => {
                    let x = call::<usize>(ptr, libffi_args.as_slice());
                    // `usize` doesn't `impl Into<i128>`, so convert manually.
                    // Convert to `u64` since this covers both 32- and 64-bit machines.
                    this.write_int(u64::try_from(x).unwrap(), dest)?;
                    return Ok(());
                }
                // pointers
                TyKind::RawPtr(TypeAndMut{ ty: some_ty, mutbl } ) => {
                    // FIXME! Eventually, don't just use a giant allocation for C pointers.
                    let len = Self::C_POINTER_DEFAULT_LEN;
                    let align = 1;
                    if let Some((raw_addr, type_size)) = 
                        match some_ty.kind() {
                            TyKind::Int(IntTy::I8) => {
                                let raw_addr = call::<*mut i8>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<i8>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Int(IntTy::I16) => {
                                let raw_addr = call::<*mut i16>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<i16>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Int(IntTy::I32) => {
                                let raw_addr = call::<*mut i32>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<i32>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Int(IntTy::I64) => {
                                let raw_addr = call::<*mut i64>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<i64>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Int(IntTy::Isize) => {
                                let raw_addr = call::<*mut isize>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<isize>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Uint(UintTy::U8) => {
                                let raw_addr = call::<*mut u8>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<u8>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Uint(UintTy::U16) => {
                                let raw_addr = call::<*mut u16>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<u16>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Uint(UintTy::U32) => {
                                let raw_addr = call::<*mut u32>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<u32>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Uint(UintTy::U64) => {
                                let raw_addr = call::<*mut u64>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<u64>();
                                Some((raw_addr as u64, type_size))
                            },
                            TyKind::Uint(UintTy::Usize) => {
                                let raw_addr = call::<*mut usize>(ptr, libffi_args.as_slice());
                                let type_size = std::mem::size_of::<usize>();
                                Some((raw_addr as u64, type_size))
                            },
                            _ => { None }
                        } {
                        let mut ptr = this.allocate_ptr_raw_addr(
                            raw_addr,
                            type_size,
                            len,
                            Align::from_bytes(align).unwrap(),
                            *mutbl,
                            MiriMemoryKind::C.into(),
                        );
                        match ptr.provenance {
                            Provenance::Concrete { alloc_id, sb } => {
                                intptrcast::GlobalStateInner::expose_ptr(this, alloc_id, sb)?;
                                ptr.provenance = Provenance::Wildcard;
                            }
                            Provenance::Wildcard => {
                            }
                        }
                        this.write_pointer(ptr, dest)?;
                        return Ok(());
                    }
                }
                // Functions with no declared return type (i.e., the default return)
                // have the output_type `Tuple([])`.
                TyKind::Tuple(t_list) =>
                    if t_list.len() == 0 {
                        call::<()>(ptr, libffi_args.as_slice());
                        return Ok(());
                    },
                _ => {}
            }
            // TODO ellen! deal with all the other return types
            throw_unsup_format!("unsupported return type to external C function: {:?}", link_name);
        }
    }

    /// Get the pointer to the function of the specified name in the shared object file,
    /// if it exists. The function must be in the shared object file specified: we do *not*
    /// return pointers to functions in dependencies of the library.  
    fn get_func_ptr_explicitly_from_lib(&mut self, link_name: Symbol) -> Option<CodePtr> {
        let this = self.eval_context_mut();
        // Try getting the function from the shared library.
        // On windows `_lib_path` will be unused, hence the name starting with `_`.
        let (lib, _lib_path) = this.machine.external_so_lib.as_ref().unwrap();
        let func: libloading::Symbol<'_, unsafe extern "C" fn()> = unsafe {
            match lib.get(link_name.as_str().as_bytes()) {
                Ok(x) => x,
                Err(_) => {
                    return None;
                }
            }
        };

        // FIXME: this is a hack!
        // The `libloading` crate will automatically load system libraries like `libc`.
        // On linux `libloading` is based on `dlsym`: https://docs.rs/libloading/0.7.3/src/libloading/os/unix/mod.rs.html#202
        // and `dlsym`(https://linux.die.net/man/3/dlsym) looks through the dependency tree of the
        // library if it can't find the symbol in the library itself.
        // So, in order to check if the function was actually found in the specified
        // `machine.external_so_lib` we need to check its `dli_fname` and compare it to
        // the specified SO file path.
        // This code is a reimplementation of the mechanism for getting `dli_fname` in `libloading`,
        // from: https://docs.rs/libloading/0.7.3/src/libloading/os/unix/mod.rs.html#411
        // using the `libc` crate where this interface is public.
        // No `libc::dladdr` on windows.
        #[cfg(unix)]
        let mut info = std::mem::MaybeUninit::<libc::Dl_info>::uninit();
        #[cfg(unix)]
        unsafe {
            if libc::dladdr(*func.deref() as *const _, info.as_mut_ptr()) != 0 {
                if std::ffi::CStr::from_ptr(info.assume_init().dli_fname).to_str().unwrap()
                    != _lib_path.to_str().unwrap()
                {
                    return None;
                }
            }
        }
        // Return a pointer to the function.
        Some(CodePtr(*func.deref() as *mut _))
    }

    /// Call specified external C function, with supplied arguments.
    /// Need to convert all the arguments from their hir representations to
    /// a form compatible with C (through `libffi` call).
    /// Then, convert return from the C call into a corresponding form that
    /// can be stored in Miri internal memory.
    fn call_and_add_external_c_fct_to_context(
        &mut self,
        link_name: Symbol,
        dest: &PlaceTy<'tcx, Provenance>,
        args: &[OpTy<'tcx, Provenance>],
    ) -> InterpResult<'tcx, bool> {
        // Get the pointer to the function in the shared object file if it exists.
        let code_ptr = match self.get_func_ptr_explicitly_from_lib(link_name) {
            Some(ptr) => ptr,
            None => {
                // Shared object file does not export this function -- try the shims next.
                return Ok(false);
            }
        };

        let this = self.eval_context_mut();

        // Get the function arguments, and convert them to `libffi`-compatible form.
        let mut libffi_args = Vec::<CArg>::with_capacity(args.len());
        for cur_arg in args.iter() {
            libffi_args.push(Self::scalar_to_carg(
                this.read_scalar(cur_arg)?,
                &cur_arg.layout.ty,
                this,
            )?);
        }

        // Convert them to `libffi::high::Arg` type.
        let libffi_args = libffi_args
            .iter()
            .map(|cur_arg| cur_arg.arg_downcast())
            .collect::<Vec<libffi::high::Arg<'_>>>();

        // Code pointer to C function.
        // let ptr = CodePtr(*func.deref() as *mut _);
        // Call the function and store output, depending on return type in the function signature.
        self.call_external_c_and_store_return(link_name, dest, code_ptr, libffi_args)?;

        // FIXME! ellen: get the `Wildcard` provenance propagation working.
        // All exposed pointers now get marked with the `Wildcard` provenance.
        // let this = self.eval_context_mut();
        // let mut all_exposed = /* not implemented: */ intptrcast::GlobalStateInner::get_all_exposed(this);
        // for (exp_id, exp_ptr) in all_exposed.iter() {
        //     let (size, align, kind) = this.get_alloc_info(*exp_id);
        //     if matches!(kind, AllocKind::LiveData) {
        //         let alloc_ref = this.get_ptr_alloc((*exp_ptr).into(), size, align)?.unwrap();
        //         let exp_alloc_mut = this.get_ptr_alloc_mut((*exp_ptr).into(), size, align)?;
        //         exp_ptr.provenance = Provenance::Wildcard;
        //         exp_alloc_mut.unwrap().write_ptr_sized(/*some offset*/, exp_ptr.into())?;
        //     }
        // }

        Ok(true)
    }
}

#[derive(Debug, Clone)]
/// Enum of supported arguments to external C functions.
pub enum CArg {
    /// 8-bit signed integer.
    Int8(i8),
    /// 16-bit signed integer.
    Int16(i16),
    /// 32-bit signed integer.
    Int32(i32),
    /// 64-bit signed integer.
    Int64(i64),
    /// isize.
    ISize(isize),
    /// 8-bit unsigned integer.
    UInt8(u8),
    /// 16-bit unsigned integer.
    UInt16(u16),
    /// 32-bit unsigned integer.
    UInt32(u32),
    /// 64-bit unsigned integer.
    UInt64(u64),
    /// usize.
    USize(usize),
    // mutable pointers
    MutPtrInt8(*mut i8),
    MutPtrInt16(*mut i16),
    MutPtrInt32(*mut i32),
    MutPtrInt64(*mut i64),
    MutPtrUInt8(*mut u8),
    MutPtrUInt16(*mut u16),
    MutPtrUInt32(*mut u32),
    MutPtrUInt64(*mut u64),
    // const pointers
    ConstPtrInt8(*const i8),
    ConstPtrInt16(*const i16),
    ConstPtrInt32(*const i32),
    ConstPtrInt64(*const i64),
    ConstPtrUInt8(*const u8),
    ConstPtrUInt16(*const u16),
    ConstPtrUInt32(*const u32),
    ConstPtrUInt64(*const u64),
    /// Recursive `CArg` (for nested pointers).
    RecCarg(Box<CArg>),
}

impl<'a> CArg {
    /// Convert a `CArg` to a `libffi` argument type.
    pub fn arg_downcast(&'a self) -> libffi::high::Arg<'a> {
        match self {
            CArg::Int8(i) => arg(i),
            CArg::Int16(i) => arg(i),
            CArg::Int32(i) => arg(i),
            CArg::Int64(i) => arg(i),
            CArg::ISize(i) => arg(i),
            CArg::UInt8(i) => arg(i),
            CArg::UInt16(i) => arg(i),
            CArg::UInt32(i) => arg(i),
            CArg::UInt64(i) => arg(i),
            CArg::USize(i) => arg(i),
            CArg::MutPtrInt8(i) => arg(i),
            CArg::MutPtrInt16(i) => arg(i),
            CArg::MutPtrInt32(i) => arg(i),
            CArg::MutPtrInt64(i) => arg(i),
            CArg::MutPtrUInt8(i) => arg(i),
            CArg::MutPtrUInt16(i) => arg(i),
            CArg::MutPtrUInt32(i) => arg(i),
            CArg::MutPtrUInt64(i) => arg(i),
            CArg::ConstPtrInt8(i) => arg(i),
            CArg::ConstPtrInt16(i) => arg(i),
            CArg::ConstPtrInt32(i) => arg(i),
            CArg::ConstPtrInt64(i) => arg(i),
            CArg::ConstPtrUInt8(i) => arg(i),
            CArg::ConstPtrUInt16(i) => arg(i),
            CArg::ConstPtrUInt32(i) => arg(i),
            CArg::ConstPtrUInt64(i) => arg(i),
            CArg::RecCarg(box_carg) => (*box_carg).arg_downcast(),
        }
    }
}
