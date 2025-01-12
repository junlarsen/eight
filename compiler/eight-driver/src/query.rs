use miette::Diagnostic;
use nom::bytes::complete::take_while;
use nom::character::complete::char;
use nom::combinator::{complete, rest};
use nom::IResult;
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum QueryError {
    #[error("failed to parse emit query")]
    InvalidQuery,
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
#[derive(Debug)]
pub enum EmitQuery {
    Hir(HirEmitQuery),
}

impl EmitQuery {
    /// Parse a list of queries.
    pub fn from_queries(queries: &[&str]) -> Result<Vec<Self>, QueryError> {
        let mut parsed_queries = Vec::with_capacity(queries.len());
        for query in queries {
            let (_, query) = EmitQuery::parse(query).map_err(|_| QueryError::InvalidQuery)?;
            parsed_queries.push(query);
        }
        Ok(parsed_queries)
    }

    /// Parse a single query.
    fn parse(input: &str) -> IResult<&str, Self> {
        let (input, namespace) = take_while(|c: char| c != '.')(input)?;
        let (input, _) = char('.')(input)?;
        match namespace {
            "hir" => {
                let (_, query) = complete(HirEmitQuery::parse)(input)?;
                Ok((input, Self::Hir(query)))
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
pub enum HirEmitQuery {
    /// Emit the HIR for this function
    Function(String),
}

impl HirEmitQuery {
    /// Parse a `hir` namespace query.
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

    /// Parse a `hir.fn` category query.
    fn parse_function_query(input: &str) -> IResult<&str, Self> {
        let (input, name) = rest(input)?;
        Ok((input, Self::Function(name.to_owned())))
    }
}

#[cfg(test)]
mod tests {
    use crate::query::{EmitQuery, HirEmitQuery};
    use eight_macros::{assert_matches, assert_ok};

    #[test]
    fn test_parse_hir_fn_query() {
        let query = EmitQuery::from_queries(&["hir.fn.must_return_i32_ptr"]);
        let query = assert_ok!(query);
        assert_eq!(query.len(), 1);
        let function_name =
            assert_matches!(&query[0], EmitQuery::Hir(HirEmitQuery::Function(p)) => p);
        assert_eq!(function_name, "must_return_i32_ptr");
    }
}
