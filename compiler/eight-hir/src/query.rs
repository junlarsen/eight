use crate::signature::{HirInstanceApiSignature, HirModuleSignature};
use crate::ty::HirTy;
use eight_diagnostics::ice;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// A stable reference that does hashing and comparison by pointer.
#[derive(Debug)]
pub struct StableRef<'a, T: ?Sized>(&'a T);

impl<'a, T: ?Sized> Hash for StableRef<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0 as *const T, state);
    }
}

impl<'a, T: ?Sized> PartialEq for StableRef<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0 as *const T, other.0 as *const T)
    }
}

impl<'a, T: ?Sized> Eq for StableRef<'a, T> {}

/// Efficient query cache for trait instances.
///
/// This is a two-level hashmap, with the first level naming the trait, and the second level
/// indexing the first argument of the trait.
///
/// This is efficient because we require traits to have at least one type parameter, and it's
/// usually used to represent the left-hand side of an operator.
///
/// Because HirTy is interned and two equal types are guaranteed to point to th same address in
/// memory, we use a pointer identity map as the inner hashmap.
pub type TraitInstanceQueryCache<'hir> = HashMap<
    &'hir str,
    HashMap<StableRef<'hir, HirTy<'hir>>, Vec<&'hir HirInstanceApiSignature<'hir>>>,
>;

/// A query database over a Hir module.
pub struct HirQueryDatabase<'hir> {
    sig: &'hir HirModuleSignature<'hir>,
    trait_instance_cache: TraitInstanceQueryCache<'hir>,
}

impl<'hir> HirQueryDatabase<'hir> {
    /// Build a new query database from the given module signature.
    pub fn new(sig: &'hir HirModuleSignature<'hir>) -> Self {
        let mut tree = TraitInstanceQueryCache::new();
        for instance in sig.instances.iter() {
            let trait_index = tree.entry(instance.trait_name).or_default();
            let stable_ref = StableRef(
                *instance
                    .type_arguments
                    .first()
                    .unwrap_or_else(|| ice!("trait instance has no type arguments")),
            );
            let instance_index = trait_index.entry(stable_ref).or_default();
            instance_index.push(instance);
        }
        Self {
            sig,
            trait_instance_cache: tree,
        }
    }

    /// Query the database for a trait instance that matches the given name and type arguments.
    ///
    /// This does an optimized search by first finding the trait index, then linearly searching
    /// through all instances that match the first type argument.
    pub fn query_trait_instance_by_name_and_type_arguments(
        &self,
        trait_name: &str,
        arguments: &[&'hir HirTy<'hir>],
    ) -> Option<&'hir HirInstanceApiSignature<'hir>> {
        let trait_index = self.trait_instance_cache.get(trait_name)?;
        let stable_ref = StableRef(*arguments.first()?);
        let instance_index = trait_index.get(&stable_ref)?;
        for instance in instance_index {
            // TODO: Do best-match search here when we have generic types.
            let is_suitable_match = instance.type_arguments.len() == arguments.len()
                && instance
                    .type_arguments
                    .iter()
                    .zip(arguments)
                    .all(|(a, b)| a.is_trivially_equal(b) || b.is_variable());
            if is_suitable_match {
                return Some(instance);
            }
        }
        None
    }
}
