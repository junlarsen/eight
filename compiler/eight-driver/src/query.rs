use nom::bytes::complete::take_while;
use nom::character::complete::char;
use nom::combinator::rest;
use nom::IResult;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum QueryError {
    #[error("failed to parse emit query")]
    InvalidQuery(#[from] nom::Err<nom::error::Error<String>>),
}

/// A query for the output of the compiler.
///
/// The compiler supports emitting various intermediate representations of the program. This query
/// parser allows the user to query specific information to emit.
///
/// The reason for this infrastructure existing, is that dumping the HIR of a single function might
/// produce a lot of output, or the LLVM IR for a module. This makes the FileCheck test files very
/// large and verbose.
///
/// Instead, we can enable textual passes that print intermediate representations to accept the
/// queries. It is not required for passes to accept queries, but it means that we can enable it for
/// passes that make sense.
///
/// The query syntax is loosely as follows. The `query` part is passed to the parsers for the
/// specific pass query parser.
///
/// ```text
/// query     ::= namespace DOT category DOT query
/// namespace ::= identifier
/// category  ::= identifier
/// query     ::= any
/// ```
///
/// For example, the query `hir.fn.must_return_i32_ptr` would request the HIR for the function named
/// `must_return_i32_ptr` to be emitted.
pub enum EmitQuery {
    Hir(HirEmitQuery),
}

impl EmitQuery {
    pub fn new(input: &str) -> Result<Self, QueryError> {
        todo!()
    }

    fn parse(input: &str) -> IResult<&str, Self> {
        let (input, namespace) = take_while(|c: char| c != '.')(input)?;
        let (input, _) = char('.')(input)?;
        match namespace {
            "hir" => {
                let (input, query) = HirEmitQuery::parse(input)?;
                Ok((input, Self::Hir(query)))
            }
            _ => unreachable!(),
        }
    }
}

pub enum HirEmitQuery {
    /// Emit the HIR for this function
    Function(String),
}

impl HirEmitQuery {
    pub fn parse(input: &str) -> IResult<&str, Self> {
        let (input, category) = take_while(|c: char| c != '.')(input)?;
        let (input, _) = char('.')(input)?;
        match category {
            "fn" => {
                let (input, query) = Self::parse_function_query(input)?;
                Ok((input, query))
            }
            _ => unreachable!(),
        }
    }

    fn parse_function_query(input: &str) -> IResult<&str, Self> {
        let (input, name) = rest(input)?;
        Ok((input, Self::Function(name.to_owned())))
    }
}
