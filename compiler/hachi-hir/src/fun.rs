use crate::stmt::HirStmt;
use crate::ty::HirTy;
use crate::{HirId, HirName};

/// A function defined in a HIR module.
///
/// Functions are either user-defined with code, or forward-declared intrinsic functions. We do
/// currently not have any syntax to specify linkage types of intrinsic functions, so for now it's
/// safe to assume everything comes from if it's intrinsic.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirFun<'hir> {
    Function(HirFun<'hir>),
    Intrinsic(HirIntrinsicFunction<'hir>),
}

impl HirFun {
    pub fn id(&self) -> HirId {
        match self {
            HirFun::Function(node) => node.id,
            HirFun::Intrinsic(node) => node.id,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirFunction<'hir> {
    pub id: HirId,
    pub name: HirName<'hir>,
    pub parameters: Vec<&'hir HirTy<'hir>>,
    pub return_type: &'hir HirTy<'hir>,
    pub body: Vec<&'hir HirStmt<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirIntrinsicFunction<'hir> {
    pub id: HirId,
    pub name: HirName<'hir>,
    pub parameters: Vec<&'hir HirTy<'hir>>,
    pub return_type: &'hir HirTy<'hir>,
}
