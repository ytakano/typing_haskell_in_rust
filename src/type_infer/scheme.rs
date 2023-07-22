use std::collections::BTreeSet;

use crate::{
    predicate::Qual,
    types::{Kind, Subst, Type, Types, Tyvar},
    CowVec,
};

/// Type schemes are used to describe polymorphic types,
/// and are represented using a list of kinds and a qualified type
///
/// In a type scheme `Scheme { kind, qt }`,  each type of the form
/// `Type::TGen(n)` that appears in the qualified type `qt`
/// represents a generic, or universally quantified type variable
/// whose kind is given by `ks[n]`.
///
/// This is the only place where we will allow `Type::TGen` values to appear in a type.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Scheme {
    pub(super) kind: CowVec<Kind>,
    pub(super) qt: Qual<Type>,
}

impl Types for Scheme {
    fn apply(&self, subst: Subst) -> Scheme {
        Scheme {
            kind: self.kind.clone(),
            qt: self.qt.apply(subst),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        self.qt.tv()
    }
}
