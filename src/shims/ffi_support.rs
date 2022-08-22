use libffi::{high::call::*, low::CodePtr};
use std::ops::Deref;

use rustc_middle::ty::{IntTy, Ty, TypeAndMut, TyKind, UintTy, 
    layout::LayoutOf};
use rustc_span::Symbol;
use rustc_target::abi::Align;

use crate::*;

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
            TyKind::RawPtr(TypeAndMut{ ty: some_ty, mutbl: some_mut } ) => {
                match k {
                    ScalarMaybeUninit::Scalar(Scalar::Ptr(mut ptr, ofs)) => {
                        match ptr.provenance {
                            Provenance::Concrete { alloc_id, sb } => {
                                intptrcast::GlobalStateInner::expose_ptr(cx, alloc_id, sb)?;
                            },
                            Provenance::Wildcard => { }
                        }
                        // FIXME: something is wrong with this code, it's meant to just change 
                        // the provenance of the current pointer to `Wildcard`...
                        // but even just writing back the original place it breaks the pointers.
                        // seems to be an issue with the layout, some sort of mixup between the 
                        // pointer and pointee layouts. 
                        // one clue is that double dereference runs but produces the wrong 
                        // result when this code is here?
                        // the logic here is inspired from the `retag_reference` function in 
                        // the stacked borrows mod file.

                        // let layout = cx.layout_of(*arg_type)?;
                        // let ptr_place = MPlaceTy::from_aligned_ptr(ptr.into(), layout);

                        // // // get the place the pointer is pointing to
                        // let imm = ImmTy::from_immediate(k.into(), ptr_place.layout);
                        // let place = cx.deref_operand(&imm.into())?;
                        // let new_place = place;
                        // // let new_place = place.map_provenance(|p| {
                        // //     p.map(|sub_p| { Provenance::Wildcard })
                        // // });
                        // let new_imm = new_place.to_ref(cx);
                        // let new_ptr = ImmTy::from_immediate(new_imm.into(), ptr_place.layout);
                        // cx.write_immediate(*new_ptr, &ptr_place.into())?;
                        
                        let qq = ptr.into_parts().1.bytes_usize();
                        match (some_ty.kind(), some_mut) {
                            // int
                            (TyKind::Int(IntTy::I8), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt8(qq as *mut i8));
                            },
                            (TyKind::Int(IntTy::I8), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt8(qq as *const i8));
                            },
                            (TyKind::Int(IntTy::I16), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt16(qq as *mut i16));
                            },
                            (TyKind::Int(IntTy::I16), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt16(qq as *const i16));
                            },
                            (TyKind::Int(IntTy::I32), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt32(qq as *mut i32));
                            },
                            (TyKind::Int(IntTy::I32), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt32(qq as *const i32));
                            },
                            (TyKind::Int(IntTy::I64), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrInt64(qq as *mut i64));
                            },
                            (TyKind::Int(IntTy::I64), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrInt64(qq as *const i64));
                            },
                            // uints
                            (TyKind::Uint(UintTy::U8), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt8(qq as *mut u8));
                            },
                            (TyKind::Uint(UintTy::U8), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt8(qq as *const u8));
                            },
                            (TyKind::Uint(UintTy::U16), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt16(qq as *mut u16));
                            },
                            (TyKind::Uint(UintTy::U16), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt16(qq as *const u16));
                            },
                            (TyKind::Uint(UintTy::U32), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt32(qq as *mut u32));
                            },
                            (TyKind::Uint(UintTy::U32), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt32(qq as *const u32));
                            },
                            (TyKind::Uint(UintTy::U64), rustc_hir::Mutability::Mut) => {
                                return Ok(CArg::MutPtrUInt64(qq as *mut u64));
                            },
                            (TyKind::Uint(UintTy::U64), rustc_hir::Mutability::Not) => {
                                return Ok(CArg::ConstPtrUInt64(qq as *const u64));
                            },
                            // recursive case
                            (TyKind::RawPtr(..), _) => {
                                return Ok(CArg::RecCarg(Box::new(Self::scalar_to_carg(k.into(), some_ty, cx)?)));
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            },
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
