//! The implementation of built-in functions in the Eight standard library.
//!
//! NOTE: The functions here are merely placeholders for now. The primary goal is to be able to
//! compile a C dylib that can the compiler can link against.

use libc::c_int;

#[no_mangle]
unsafe extern "C" fn __eight_std_print_i32(v: c_int) {
    static FORMAT: &[u8] = b"%d";
    libc::printf(FORMAT.as_ptr() as *const i8, v);
}
