pub mod context;
pub mod errors;
pub mod span;

#[macro_export]
macro_rules! ice {
    ($($arg:tt)*) => {{
        let file = file!();
        let line = line!();
        let column = column!();
        panic!(
            "internal compiler error ({}:{}:{}):\n{}",
            file, line, column, format_args!($($arg)*)
        )
    }};
}
