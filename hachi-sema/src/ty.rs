use hachi_syntax::Type;
use std::fmt::Debug;

#[derive(Clone)]
pub enum Ty {
    TVariable(usize),
    TFunction(Box<Ty>, Vec<Box<Ty>>),
    TConst(String),
    TPointer(Box<Ty>),
    TReference(Box<Ty>),
}

impl From<&Type> for Ty {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Unit(_) => Ty::TConst("void".to_owned()),
            Type::Integer32(_) => Ty::TConst("i32".to_owned()),
            Type::Boolean(_) => Ty::TConst("bool".to_owned()),
            Type::Named(t) => Ty::TConst(t.name.name.clone()),
            Type::Pointer(t) => Ty::TPointer(Box::new(t.inner.as_ref().into())),
            Type::Reference(t) => Ty::TReference(Box::new(t.inner.as_ref().into())),
        }
    }
}

impl Debug for Ty {
    /// Manual implementation of Debug for Ty
    ///
    /// This is done so we can have a nicer print of the more complex types like TFunction.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::TVariable(id) => write!(f, "${}", id),
            Ty::TFunction(return_type, args) => {
                let args = args
                    .iter()
                    .map(|a| format!("{:?}", a))
                    .collect::<Vec<String>>()
                    .join(", ");
                let name = format!("{:?}", return_type);
                write!(f, "({}) -> {}", args, name)
            }
            Ty::TConst(name) => write!(f, "{}", name),
            Ty::TPointer(inner) => write!(f, "*{:?}", inner),
            Ty::TReference(inner) => write!(f, "&{:?}", inner),
        }
    }
}
