use crate::{
    error::DynError,
    predicate::{in_hnf, mgu_pred, type_match_pred, Pred, Qual},
    types::{Type, Types},
    CowStr,
};

use std::collections::BTreeMap;

/// Type class.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Class {
    super_class: Vec<CowStr>,
    insts: Vec<Inst>,
}

/// Instance.
pub(crate) type Inst = Qual<Pred>;

pub struct ClassEnv {
    classes: BTreeMap<CowStr, Class>,
    pub(crate) default_types: Vec<Type>, // default types
}

impl ClassEnv {
    pub fn new(default_types: Vec<Type>) -> Self {
        ClassEnv {
            classes: BTreeMap::new(),
            default_types,
        }
    }

    /// Add a type class.
    ///
    /// # Examples
    ///
    /// ```
    /// // Add type classes as follows.
    /// // trait Eq {}
    /// // trait Ord : Eq {}
    ///
    /// use typing_haskell_in_rust::type_class::ClassEnv;
    ///
    /// let mut env = ClassEnv::new(vec![]);
    /// env.add_class("Eq".into(), vec![]);
    /// env.add_class("Ord".into(), vec!["Eq".into()]);
    /// ```
    pub fn add_class(&mut self, id: CowStr, super_class: Vec<CowStr>) -> Result<(), DynError> {
        if self.classes.contains_key(&id) {
            return Err("class already defined".into());
        }

        if super_class.iter().any(|id| !self.classes.contains_key(id)) {
            return Err("super class not defined".into());
        }

        self.classes.insert(
            id,
            Class {
                super_class,
                insts: Vec::new(),
            },
        );

        Ok(())
    }

    /// Add an instance.
    ///
    /// # Examples
    ///
    /// ```
    /// // Add an instance as follows.
    /// // trait Eq {}        // type class
    /// // struct Int {}      // type
    /// // impl Eq for Int {} // instance
    ///
    /// use typing_haskell_in_rust::{type_class::ClassEnv, predicate::Pred, types::T_INT};
    ///
    /// // add `Eq` class
    /// let mut env = ClassEnv::new(vec![]);
    /// env.add_class("Eq".into(), vec![]).unwrap();
    ///
    /// // add a instance of `Eq` for `Int`
    /// let eq_int = Pred {
    ///     id: "Eq".into(),
    ///     t: T_INT.clone(),
    /// };
    /// env.add_inst(vec![], eq_int).unwrap();
    /// ```
    pub fn add_inst(&mut self, ps: Vec<Pred>, p: Pred) -> Result<(), DynError> {
        if !self.classes.contains_key(&p.id) {
            return Err("no class for instance".into());
        }

        fn overlap(p: &Pred, q: &Pred) -> bool {
            mgu_pred(p, q).is_ok()
        }

        if let Some(its) = self.insts(&p.id) {
            if its.iter().any(|inst| overlap(&p, &inst.t)) {
                return Err("instance already defined".into());
            }
        }

        self.classes
            .get_mut(&p.id)
            .unwrap()
            .insts
            .push(Inst { preds: ps, t: p });

        Ok(())
    }

    fn super_class(&self, id: &CowStr) -> Option<&[CowStr]> {
        self.classes.get(id).map(|c| c.super_class.as_slice())
    }

    /// Get instances of a class.
    fn insts(&self, id: &CowStr) -> Option<&[Inst]> {
        self.classes.get(id).map(|c| c.insts.as_slice())
    }

    fn by_super(&self, pred: &Pred) -> Vec<Pred> {
        let mut result = vec![pred.clone()];

        if let Some(super_classes) = self.super_class(&pred.id) {
            for super_class in super_classes {
                result.append(&mut self.by_super(&Pred {
                    id: super_class.clone(),
                    t: pred.t.clone(),
                }));
            }
        }

        result
    }

    fn by_inst(&self, pred: &Pred) -> Option<Vec<Pred>> {
        for it in self.insts(&pred.id)?.iter() {
            if let Ok(u) = type_match_pred(&it.t, pred) {
                let result = it.preds.apply(u);
                return Some(result);
            }
        }

        None
    }

    /// Given a particular class environment `self`,
    /// the intention here is that `self.entail(ps, p)` will be True
    /// if, and only if, the predicate `p` will hold
    /// whenever all of the predicates in `ps` are satisfied.
    pub(crate) fn entail(&self, ps: &mut dyn Iterator<Item = &Pred>, p: &Pred) -> bool {
        if ps.map(|p_| self.by_super(p_)).any(|ps_| ps_.contains(p)) {
            true
        } else if let Some(qs) = self.by_inst(p) {
            qs.iter().all(|p_| self.entail(ps, p_))
        } else {
            false
        }
    }

    fn sc_entail(&self, ps: &mut dyn Iterator<Item = &Pred>, p: &Pred) -> bool {
        ps.map(|p_| self.by_super(p_)).any(|ps_| ps_.contains(p))
    }

    fn to_hnfs(&self, ps: Vec<Pred>) -> Result<Vec<Pred>, DynError> {
        let mut result = Vec::new();
        for p in ps {
            result.append(&mut self.to_hnf(p)?);
        }
        Ok(result)
    }

    fn to_hnf(&self, p: Pred) -> Result<Vec<Pred>, DynError> {
        if in_hnf(&p) {
            return Ok(vec![p]);
        }

        if let Some(inst) = self.by_inst(&p) {
            self.to_hnfs(inst)
        } else {
            Err("context reduction".into())
        }
    }

    fn simplify(&self, ps: Vec<Pred>) -> Vec<Pred> {
        let mut result = Vec::new();
        for i in 0..ps.len() {
            let mut it = result.iter().chain(ps[(i + 1)..].iter());
            if !self.sc_entail(&mut it, &ps[i]) {
                result.push(ps[i].clone());
            }
        }
        result
    }

    pub(crate) fn reduce(&self, ps: Vec<Pred>) -> Result<Vec<Pred>, DynError> {
        let qs = self.to_hnfs(ps)?;
        Ok(self.simplify(qs))
    }
}

#[cfg(test)]
mod tests {
    use crate::types::T_INT;

    use super::*;

    #[test]
    fn test_insts() {
        // trait Eq {}        // type class
        // struct Int {}      // type
        // impl Eq for Int {} // instance

        // add `Eq` class
        let mut env = ClassEnv::new(vec![]);
        env.add_class("Eq".into(), vec![]).unwrap();

        // add a instance of `Eq` for `Int`
        let eq_int = Pred {
            id: "Eq".into(),
            t: T_INT.clone(),
        };
        env.add_inst(vec![], eq_int).unwrap();

        // get the instances of `Eq`
        let eq_insts = env.insts(&"Eq".into()).unwrap();
        eprintln!("{:?}", eq_insts);

        let expected = vec![Inst {
            preds: Vec::new(),
            t: Pred {
                id: "Eq".into(),
                t: T_INT.clone(),
            },
        }];

        assert_eq!(eq_insts, expected);
    }
}
