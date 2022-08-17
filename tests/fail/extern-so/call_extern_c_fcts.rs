//@only-target-linux
//@only-on-host
//@compile-flags: -Zmiri-extern-so-file=tests/extern-so/libtestlib.so
//@error-pattern: /reborrow .* tag does not exist in the borrow stack/

extern "C" {
    fn array_pointer_test() -> *mut i32;
}

fn main() {
    unsafe {
        let arr_ptr = array_pointer_test();
        let slice = std::slice::from_raw_parts(arr_ptr as *const i32, 3u64 as usize);
        
        assert_eq!(slice, [0, 1, 2]);
        assert_eq!(*arr_ptr, 0);
        assert_eq!(*arr_ptr.offset(1), 1);

        *arr_ptr.offset(1) = 5;
        assert_eq!(slice, [0, 5, 2]);

        libc::free(arr_ptr as *mut _);
    }
}
