#[macro_export]
macro_rules! declare_ast_node {
    {
        $(#[$attr:meta])*
        $vis:vis struct $name:ident {
            $($field_vis:vis $field:ident: $ty:ty,)*
        }
    } => {
        $(#[$attr])*
        #[cfg_attr(feature = "serde", derive(serde::Serialize))]
        #[derive(Debug)]
        $vis struct $name {
            $($field_vis $field: $ty),*
        }

        impl $name {
            pub fn new($($field: $ty),*) -> Self {
                Self { $($field),* }
            }

            /// Get the node ID of the AST node.
            pub fn node_id(&self) -> &$crate::ast::NodeId {
                &self.id
            }

            pub fn span(&self) -> &hachi_span::Span {
                &self.span
            }
        }
    }
}

#[macro_export]
macro_rules! declare_ast_variant {
    {
        $(#[$attr:meta])*
        $vis:vis enum $name:ident {
            $($field:ident($ty:ty),)*
        }
    } => {
        $(#[$attr])*
        #[cfg_attr(feature = "serde", derive(serde::Serialize))]
        #[derive(Debug)]
        $vis enum $name {
            $($field($ty),)*
        }

        impl $name {
            /// Get the node ID of the AST node.
            pub fn node_id(&self) -> &$crate::ast::NodeId {
                match self {
                    $(Self::$field(v) => &v.node_id()),*
                }
            }
        }
    }
}
