mod ast;
mod lexer;
mod parser;
mod span;

pub use ast::*;
pub use lexer::*;
pub use parser::*;
pub use span::*;

#[cfg(test)]
pub mod assertions {
    /// Assert that a `Result` is `Ok`, returning the value inside the `Ok` variant.
    #[macro_export]
    macro_rules! assert_ok {
        ($expr:expr) => {{
            match $expr {
                ::std::result::Result::Ok(val) => val,
                ::std::result::Result::Err(err) => {
                    panic!("assertion failed: Err({:?})", err);
                }
            }
        }};
    }

    /// Assert that a `Result` is `Err`, returning the error inside the `Err` variant.
    #[macro_export]
    macro_rules! assert_err {
        ($expr:expr) => {{
            match $expr {
                ::std::result::Result::Ok(val) => {
                    panic!("assertion failed: Ok({:?})", val);
                }
                ::std::result::Result::Err(err) => err,
            }
        }};
    }

    /// Assert that an `Option` is `Some`, returning the value inside the `Some` variant.
    #[macro_export]
    macro_rules! assert_some {
        ($expr:expr) => {{
            match $expr {
                ::std::option::Option::Some(val) => val,
                ::std::option::Option::None => {
                    panic!("assertion failed: None");
                }
            }
        }};
    }

    /// Assert that an `Option` is `None`.
    #[macro_export]
    macro_rules! assert_none {
        ($expr:expr) => {{
            if let ::std::option::Option::Some(val) = $expr {
                panic!("assertion failed: Some({:?})", val);
            };
        }};
    }
}
