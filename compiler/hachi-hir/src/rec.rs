use crate::ty::HirTy;
use crate::HirName;
use hachi_span::Span;
use std::collections::BTreeMap;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirRecord {
    /// Span encapsulating the entire record definition.
    pub span: Span,
    pub name: HirName,
    pub fields: BTreeMap<String, Box<HirRecordField>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirRecordField {
    pub span: Span,
    pub name: HirName,
    pub ty: Box<HirTy>,
}
