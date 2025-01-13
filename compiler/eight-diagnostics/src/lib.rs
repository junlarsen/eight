#[macro_export]
macro_rules! ice {
    ($message:expr) => {{
        let message = $message;
        let file = file!();
        let line = line!();
        let column = column!();
        panic!(
            "internal compiler error ({}:{}:{}):\n{}",
            file, line, column, message
        )
    }};
}
