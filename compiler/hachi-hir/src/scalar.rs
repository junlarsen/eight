use crate::ty::HirTy;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirIntrinsicScalar<'ta> {
    pub name: String,
    pub ty: &'ta HirTy<'ta>,
}
