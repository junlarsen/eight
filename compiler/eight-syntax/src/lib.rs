use eight_diagnostics::errors::syntax::ParseError;

pub mod arena;
pub mod ast;
pub mod lexer;
pub mod parser;
pub mod tok;

pub type ParseResult<T> = Result<T, ParseError>;
