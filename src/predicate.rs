use crate::{
    error::DynError,
    types::{mgu, type_match, Subst, Type, Types, Tyvar},
    CowStr,
};

use std::collections::BTreeSet;

/// Predicate.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Pred {
    pub id: CowStr,
    pub t: Type,
}

impl Pred {
    pub fn new(id: CowStr, t: Type) -> Self {
        Pred { id, t }
    }
}

/// Qualifier.
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) struct Qual<T> {
    pub preds: Vec<Pred>,
    pub t: T,
}

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

/// Get the most general unifier of two predicates.
pub(crate) fn mgu_pred(p1: &Pred, p2: &Pred) -> Result<Subst, DynError> {
    if p1.id != p2.id {
        return Err("classes differ".into());
    }
    mgu(&p1.t, &p2.t)
}

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
