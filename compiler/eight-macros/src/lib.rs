#[cfg(feature = "assertion-macros")]
pub mod assertions;
pub mod error;

#[macro_export]
macro_rules! declare_ref_type {
    ($name:ident, $storage:ty) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
        pub struct $name(pub $storage);

        impl $name {
            pub fn new(id: $storage) -> Self {
                Self(id)
            }

            pub fn id(&self) -> $storage {
                self.0
            }
        }
    };
}
