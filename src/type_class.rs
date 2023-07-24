use crate::{
    error::DynError,
    predicate::{in_hnf, mgu_pred, type_match_pred, Pred, Qual},
    types::{Type, Types},
    CowStr, CowVec,
};

use std::collections::BTreeMap;

/// Represents a class, which includes its superclasses and instances.
///
/// `super_class`: A vector of superclass identifiers, stored as CowStr for efficient memory usage.
/// Each identifier in the vector represents a superclass of the class.
///
/// `insts`: A vector of instances, represented as `Inst` which is equivalent to `Qual<Pred>`.
/// Each instance represents a specific implementation of the class for a given type.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Class {
    super_class: CowVec<CowStr>,
    insts: CowVec<Inst>,
}

/// Represents a qualified predicate `Inst`, used for defining instances.
///
/// It is equivalent to `Qual<Pred>`, representing a predicate (`Pred`) possibly qualified by other predicates.
pub(crate) type Inst = Qual<Pred>;

/// Represents a class environment, which is essentially a mapping of class identifiers to class declarations.
/// It also includes default types used in the environment.
pub struct ClassEnv {
    classes: BTreeMap<CowStr, Class>,
    pub(crate) default_types: CowVec<Type>, // default types
}

impl ClassEnv {
    /// Creates a new `ClassEnv` with the given default types.
    ///
    /// `default_types`: The default types to be used in the class environment.
    ///
    /// Returns: A new `ClassEnv` with no classes defined and the provided default types.
    pub fn new(default_types: CowVec<Type>) -> Self {
        ClassEnv {
            classes: BTreeMap::new(),
            default_types,
        }
    }

    /// Adds a new class with the given identifier and superclasses to the class environment.
    ///
    /// `id`: The identifier for the new class.
    /// `super_class`: The superclasses for the new class.
    ///
    /// Returns: `Ok(())` if the class was successfully added, or an `Err(DynError)` if the class already
    /// exists in the environment or if any of the superclasses are not defined.
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
    /// let mut env = ClassEnv::new(vec![].into());
    /// env.add_class("Eq".into(), vec![].into());
    /// env.add_class("Ord".into(), vec!["Eq".into()].into());
    /// ```
    pub fn add_class(&mut self, id: CowStr, super_class: CowVec<CowStr>) -> Result<(), DynError> {
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
                insts: Vec::new().into(),
            },
        );

        Ok(())
    }

    /// Adds a new instance to the class identified by the predicate `p` with the given set of predicates `ps`.
    ///
    /// `ps`: The set of predicates that make up the instance.
    /// `p`: The predicate identifying the class to which the instance should be added.
    ///
    /// Returns: `Ok(())` if the instance was successfully added, or an `Err(DynError)` if the class does not exist
    /// in the environment, or if the instance overlaps with any existing instance of the class.
    ///
    /// Overlapping instances are those for which there exists a substitution that makes the head of the instance equal
    /// to the head of an existing instance. This is checked using the `overlap` function, which is defined here as a closure
    /// that uses the `mgu_pred` function to attempt to unify the two predicates. If unification succeeds, the instances overlap.
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
    /// let mut env = ClassEnv::new(vec![].into());
    /// env.add_class("Eq".into(), vec![].into()).unwrap();
    ///
    /// // add a instance of `Eq` for `Int`
    /// let eq_int = Pred {
    ///     id: "Eq".into(),
    ///     t: T_INT.clone(),
    /// };
    /// env.add_inst(vec![].into(), eq_int).unwrap();
    /// ```
    pub fn add_inst(&mut self, ps: CowVec<Pred>, p: Pred) -> Result<(), DynError> {
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
            .to_mut()
            .push(Inst { preds: ps, t: p });

        Ok(())
    }

    /// Returns a vector of super classes corresponding to the given identifier.
    ///
    /// # Arguments
    ///
    /// * `id` - A string slice that holds the identifier of the class.
    ///
    /// # Returns
    ///
    /// * `Option<CowVec<CowStr>>` - An Option wrapping a vector of super classes (as CowStr) if
    /// they exist, else None.
    fn super_classes(&self, id: &str) -> Option<CowVec<CowStr>> {
        self.classes.get(id).map(|c| c.super_class.clone())
    }

    /// Returns a copy of the instance declarations associated with a given class identifier.
    ///
    /// # Arguments
    ///
    /// * `id`: The identifier of a class.
    ///
    /// # Returns
    ///
    /// An `Option` containing a `CowVec` of instance declarations (`Inst`) associated with the class.
    /// If the class does not exist, `None` is returned.
    fn insts(&self, id: &str) -> Option<CowVec<Inst>> {
        self.classes.get(id).map(|c| c.insts.clone())
    }

    /// Calculates and returns a vector of Pred instances which hold for the given predicate's
    /// class and its superclasses recursively.
    ///
    /// For example, in Haskell, if we have a class hierarchy where `Num` is a superclass of `Integral`
    /// `(class Num a => Integral a)`, and we want to find all the classes a type must be an instance
    /// of given that it is an instance of `Integral`, we could use this function.
    ///
    /// # Arguments
    ///
    /// * `pred` - A reference to a predicate instance.
    ///
    /// # Returns
    ///
    /// * `Vec<Pred>` - A vector of Pred instances which hold for the class of given predicate
    /// and its superclasses.
    fn by_super(&self, pred: &Pred) -> Vec<Pred> {
        let mut result = vec![pred.clone()];

        if let Some(super_classes) = self.super_classes(&pred.id) {
            for super_class in super_classes.iter() {
                result.append(&mut self.by_super(&Pred {
                    id: super_class.clone(),
                    t: pred.t.clone(),
                }));
            }
        }

        result
    }

    /// Determines the list of predicates (sub-goals) that need to be satisfied for the given predicate
    /// to be an instance of a certain class.
    ///
    /// The method iterates through the instance declarations associated with the class of the given
    /// predicate. If it finds an instance declaration whose head matches the given predicate,
    /// it applies the corresponding substitution to the predicates in the instance declaration,
    /// and returns these as a list of sub-goals.
    ///
    /// # Arguments
    ///
    /// * `pred`: A predicate for which the list of sub-goals is determined.
    ///
    /// # Returns
    ///
    /// An `Option` containing a `CowVec` of predicates (sub-goals) that need to be satisfied for the
    /// given predicate to be an instance of a certain class. If no matching instance is found, `None` is returned.
    fn by_inst(&self, pred: &Pred) -> Option<CowVec<Pred>> {
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

    fn to_hnfs(&self, ps: CowVec<Pred>) -> Result<Vec<Pred>, DynError> {
        let mut result = Vec::new();
        for p in ps.iter() {
            result.append(&mut self.to_hnf(p.clone())?);
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

    pub(crate) fn reduce(&self, ps: CowVec<Pred>) -> Result<Vec<Pred>, DynError> {
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
        let mut env = ClassEnv::new(vec![].into());
        env.add_class("Eq".into(), vec![].into()).unwrap();

        // add a instance of `Eq` for `Int`
        let eq_int = Pred {
            id: "Eq".into(),
            t: T_INT.clone(),
        };
        env.add_inst(vec![].into(), eq_int).unwrap();

        // get the instances of `Eq`
        let eq_insts = env.insts("Eq").unwrap();
        eprintln!("{:?}", eq_insts);

        let expected = vec![Inst {
            preds: Vec::new().into(),
            t: Pred {
                id: "Eq".into(),
                t: T_INT.clone(),
            },
        }];

        assert_eq!(eq_insts, expected);
    }
}
