//! # Predicate Module
//!
//! The `Pred` struct represents a type class predicate in a polymorphically typed language.
//! Each instance of `Pred` includes a class identifier (`id`) and a type (`t`).
//! The `id` is a string representing the name of the class,
//! and the `t` denotes the type that is asserted to be a member of the class named by `id`.
//!
//! Consider the following Haskell type class declaration and instance declaration:
//!
//! ```haskell
//! class Num a where
//!     (+) :: a -> a -> a
//!
//! instance Num Int where
//!     (+) = intPlus
//! ```
//! In the above code, `Num` is a type class and `Int` is a type that is an instance of `Num`.
//! This relationship can be expressed as a predicate in the following manner: `Num Int`.
//! In the `Pred` struct, this relationship would be represented as
//! `Pred { id: "Num", t: Type::TCon(Tycon{ id: "Int", kind: Kind::Star })) }`.
//!
//! Methods in the `Pred` struct include the constructor `new`,
//! and private implementations for the `apply` and `tv` methods from the `Types` trait.
//! These methods allow for operations such as the substitution of types (`apply`) and fetching type variables (`tv`) within predicates.
//!
//! By providing a robust representation of type class predicates and associated operations,
//! the `Pred` struct plays a key role in handling class constraints within a type system.

use crate::{
    error::DynError,
    types::{mgu, type_match, Subst, Type, Types, Tyvar},
    CowStr, CowVec,
};

use std::collections::BTreeSet;

/// Predicates consisting of a class identifier and a type. It asserts that `t`
/// is a member of the class named `id`.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Pred {
    pub id: CowStr,
    pub t: Type,
}

impl Pred {
    /// Constructs a new predicate with given class identifier `id` and `Type` `t`.
    pub fn new(id: CowStr, t: Type) -> Self {
        Pred { id, t }
    }
}

/// A qualifier that represents a type `T` qualified by a (possibly empty) list
/// of predicates (class constraints). It restricts the ways in which type variables
/// are instantiated.
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) struct Qual<T> {
    pub preds: CowVec<Pred>,
    pub t: T,
}

/// Implementation of `Types` for `Pred`. It provides the necessary functionality
/// to apply a substitution to the type in the `Pred`, and to get all type variables
/// within the `Pred`.
impl Types for Pred {
    fn apply(&self, subst: Subst) -> Self {
        Pred {
            id: self.id.clone(),
            t: self.t.apply(subst),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        self.t.tv()
    }
}

/// Implementation of `Types` for `Qual<T>`. It provides the necessary functionality
/// to apply a substitution to all predicates and the type in the `Qual<T>`,
/// and to get all type variables within the `Qual<T>`.
impl<T: Types> Types for Qual<T> {
    fn apply(&self, subst: Subst) -> Self {
        Qual {
            preds: self.preds.iter().map(|p| p.apply(subst.clone())).collect(),
            t: self.t.apply(subst),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        let mut set1 = self.preds.tv();
        let mut set2 = self.t.tv();
        set1.append(&mut set2);
        set1
    }
}

/// Calculates the most general unifier (mgu) of two predicates.
/// It checks if both predicates are from the same class (`id`),
/// then calculates the mgu of their types.
///
/// # Errors
/// Returns an error if the predicates are from different classes.
pub(crate) fn mgu_pred(p1: &Pred, p2: &Pred) -> Result<Subst, DynError> {
    if p1.id != p2.id {
        return Err("classes differ".into());
    }
    mgu(&p1.t, &p2.t)
}

/// Performs type matching on two predicates.
/// It checks if both predicates are from the same class (`id`),
/// then attempts to match their types.
///
/// # Errors
/// Returns an error if the predicates are from different classes.
pub(crate) fn type_match_pred(p1: &Pred, p2: &Pred) -> Result<Subst, DynError> {
    if p1.id != p2.id {
        return Err("classes differ".into());
    }
    type_match(&p1.t, &p2.t)
}

/// Check if pred.t is the head normal form.
pub(crate) fn in_hnf(pred: &Pred) -> bool {
    fn hnf(t: &Type) -> bool {
        match t {
            Type::TVar(_) => true,
            Type::TCon(_) => false,
            Type::TAp(t, _) => hnf(t),
            Type::TGen(_) => unreachable!(),
        }
    }
    hnf(&pred.t)
}
