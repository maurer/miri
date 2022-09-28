//@only-target-linux
//@only-on-host
//@compile-flags: -Zmiri-extern-so-file=tests/extern-so/libtestlib.so

extern "C" {
    fn double_deref(x: *const *const i32) -> i32;
    fn add_one_int(x: i32) -> i32;
    fn add_int16(x: i16) -> i16;
    fn test_stack_spill(
        a: i32,
        b: i32,
        c: i32,
        d: i32,
        e: i32,
        f: i32,
        g: i32,
        h: i32,
        i: i32,
        j: i32,
        k: i32,
        l: i32,
    ) -> i32;
    fn add_short_to_long(x: i16, y: i64) -> i64;
    fn get_unsigned_int() -> u32;
    fn printer();
    fn pointer_test() -> *mut i32;
    fn deref_and_print(x: *mut i32);
    fn array_pointer_test() -> *mut i32;
    fn swap_double_ptrs(x: *mut *mut i16, y: *mut *mut i16);
    fn set(x: *mut i16, v: i16);
    fn set2(x: *mut *mut i16, v: i16);
    fn setptr(p: *mut *mut i16, x: *mut i16);
    fn setptr2(p: *mut *mut *mut i16, x: *mut i16);
}

fn main() {
    unsafe {
        // test function that adds 2 to a provided int
        assert_eq!(add_one_int(1), 3);

        // test function that takes the sum of its 12 arguments
        assert_eq!(test_stack_spill(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12), 78);

        // test function that adds 3 to a 16 bit int
        assert_eq!(add_int16(-1i16), 2i16);

        // test function that adds an i16 to an i64
        assert_eq!(add_short_to_long(-1i16, 123456789123i64), 123456789122i64);

        // test function that returns -10 as an unsigned int
        assert_eq!(get_unsigned_int(), (-10i32) as u32);

        // test void function that prints from C -- call it twice
        printer();
        printer();

        // test double dereference
        let base: i32 = 42;
        let base_p: *const i32 = &base as *const i32;
        let base_pp: *const *const i32 = &base_p as *const *const i32;
        assert_eq!(double_deref(base_pp), 42);

        // test return pointer to i32 from C, dereference, modify in Rust, and see changes in C
        let ptr = pointer_test();
        assert_eq!(*ptr, 1);
        *ptr = 5;
        assert_eq!(*ptr, 5);
        deref_and_print(ptr);

        // test return pointer to array of i32 from C, and read part of the array as a slice
        let arr_ptr = array_pointer_test();
        let slice = std::slice::from_raw_parts(arr_ptr as *const i32, 3u64 as usize);
        assert_eq!(slice, [0, 1, 2]);
        assert_eq!(*arr_ptr, 0);
        assert_eq!(*arr_ptr.offset(1), 1);

        // mutate the pointer and see it reflected in the slice
        *arr_ptr.offset(1) = 5;
        assert_eq!(slice, [0, 5, 2]);

        // test passing a Rust pointer to C and reassigning its value
        let mut set_base: i16 = 1;
        let mut set_base_p: *mut i16 = &mut set_base as *mut i16;
        set(set_base_p, 3);
        assert_eq!(set_base, 3);
        assert_eq!(*set_base_p, 3);

        // test passing a double pointer, double dereferencing in C and reassigning its value
        let set_base_pp: *mut *mut i16 = &mut set_base_p as *mut *mut i16;
        set2(set_base_pp, 8);
        assert_eq!(*set_base_p, 8);
        assert_eq!(**set_base_pp, 8);

		// test passing two double pointers, and swapping the _values_ they point to 
		// note: this is _not_ C writing pointers to Miri memory
        let mut new_base: i16 = 2;
        let mut new_base_p: *mut i16 = &mut new_base as *mut i16;
        let new_base_pp: *mut *mut i16 = &mut new_base_p as *mut *mut i16;
        let mut set_base: i16 = 1;
        let mut set_base_p: *mut i16 = &mut set_base as *mut i16;
        let set_base_pp: *mut *mut i16 = &mut set_base_p as *mut *mut i16;
        assert_eq!(**set_base_pp, 1);
        assert_eq!(**new_base_pp, 2);
        assert_ne!(*new_base_pp, *set_base_pp);
        swap_double_ptrs(set_base_pp, new_base_pp);
        assert_ne!(*new_base_pp, *set_base_pp);
        assert_eq!(**set_base_pp, 2);
        assert_eq!(**new_base_pp, 1);

        /*
		 * STILL IN PROGRESS
		 * 
         * Tests for C writing _pointers_ to Miri memory.
         * These are not fully supported yet. The calls to C are allowed, but after the pointers
         * are modified by C dereferencing them to a value in Rust crashes Miri (with a UB error, stating
         * that the memory access is invalid).
         * The lines that crash the code are commented out below -- uncomment to see the error.
         */
        // test passing a double pointer and a single pointer, and reassigning the double pointer
        // to point to the single pointer
        let mut new_base: i16 = 2;
        let new_base_p: *mut i16 = &mut new_base as *mut i16;
        assert_ne!(new_base_p, set_base_p);
        setptr(set_base_pp, new_base_p);
        assert_eq!(new_base_p, set_base_p);

        // uh oh: the following code breaks
        // let rust_ddref = **set_base_pp;
        // let rust_dref = *set_base_p;

        // test passing a triple pointer and a single pointer, double dereferencing the triple
        // pointer, and reassigning it to the single pointer
        let mut new_base: i16 = 2;
        let mut new_base_p: *mut i16 = &mut new_base as *mut i16;
        let mut new_base_pp: *mut *mut i16 = &mut new_base_p as *mut *mut i16;
        let new_base_ppp: *mut *mut *mut i16 = &mut new_base_pp as *mut *mut *mut i16;
        assert_ne!(**new_base_ppp, set_base_p);
        setptr2(new_base_ppp, set_base_p);
        assert_eq!(**new_base_ppp, set_base_p);

        // uh oh: the following code breaks
        // let rust_dref = *new_base_p;
        // let rust_ddref = **new_base_pp;
        // let rust_dddref = ***new_base_ppp;

        // avoid memory leaks
        libc::free(ptr as *mut _);
        libc::free(arr_ptr as *mut _);
    }
}
