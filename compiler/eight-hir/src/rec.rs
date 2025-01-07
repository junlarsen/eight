use crate::ty::HirTy;
use crate::HirName;
use eight_span::Span;
use std::collections::BTreeMap;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirRecord<'ta> {
    /// Span encapsulating the entire record definition.
    pub span: Span,
    pub name: HirName,
    pub fields: BTreeMap<String, HirRecordField<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirRecordField<'ta> {
    pub span: Span,
    pub name: HirName,
    pub r#type: &'ta HirTy<'ta>,
    pub type_annotation: Span,
}
