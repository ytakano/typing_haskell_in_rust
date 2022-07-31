use crate::error::DynError;
use once_cell::sync::Lazy;
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

type Subst = Vec<(Tyvar, Type)>;
const NULL_SUBST: Subst = vec![];

/// Kind of type.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub enum Kind {
    Star,
    Kfun(Box<Kind>, Box<Kind>),
}

/// Type variable.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub struct Tyvar {
    pub id: Cow<'static, str>,
    pub kind: Kind,
}

/// Type constructor.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Tycon {
    pub id: Cow<'static, str>,
    pub kind: Kind,
}

/// Type.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Type {
    TVar(Tyvar),               // type variable
    TCon(Tycon),               // type constructor
    TAp(Box<Type>, Box<Type>), // type application
    TGen(usize),               // generic or quantified type variables
}

macro_rules! def_type {
    ( $id:ident, $ty:expr) => {
        pub static $id: Lazy<Type> = Lazy::new(|| {
            Type::TCon(Tycon {
                id: $ty.into(),
                kind: Kind::Star,
            })
        });
    };
}

def_type!(TUNIT, "Unit");
def_type!(TCHAR, "Char");
def_type!(TINT, "Int");
def_type!(TINTEGER, "Integer");
def_type!(TFOLAT, "Float");
def_type!(TDOUBLE, "Double");

pub static TLIST: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "[]".into(),
        kind: Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star)),
    })
});

pub static TARROW: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(->)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

pub static TTUPLE2: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(,)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

pub fn mk_fn(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(TARROW.clone()),
        Box::new(Type::TAp(Box::new(a), Box::new(b))),
    )
}

pub fn mk_list(a: Type) -> Type {
    Type::TAp(Box::new(TLIST.clone()), Box::new(a))
}

pub fn mk_pair(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(Type::TAp(Box::new(TTUPLE2.clone()), Box::new(a))),
        Box::new(b),
    )
}

trait HasKind {
    fn kind(&self) -> Kind;
}

impl HasKind for Tyvar {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

impl HasKind for Tycon {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

impl HasKind for Type {
    fn kind(&self) -> Kind {
        match self {
            Type::TCon(tc) => tc.kind(),
            Type::TVar(u) => u.kind(),
            Type::TAp(t, _) => match t.kind() {
                Kind::Star => unreachable!(),

                // an application `(TAp t t′)` using only the kind of its first argument `t`.
                // Assuming that the type is well-formed, `t` must have a kind `k′ → k`,
                // where `k′` is the kind of `t′` and `k` is the kind of the whole application.
                Kind::Kfun(_, k) => *k,
            },
            Type::TGen(_) => unreachable!(),
        }
    }
}

trait Types {
    fn apply(&self, subst: &Subst) -> Self; // apply `subst` to `self`
    fn tv(&self) -> BTreeSet<Tyvar>; // set of type variables in `self`
}

impl Types for Type {
    fn apply(&self, subst: &Subst) -> Self {
        match self {
            Type::TVar(u) => subst
                .iter()
                .find(|(u_, _)| u == u_)
                .map(|(_, t)| t.clone())
                .unwrap_or(Type::TVar(u.clone())),
            Type::TAp(l, r) => Type::TAp(Box::new(l.apply(subst)), Box::new(r.apply(subst))),
            _ => self.clone(),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        match self {
            Type::TVar(u) => {
                let mut result = BTreeSet::new();
                result.insert(u.clone());
                result
            }
            Type::TAp(l, r) => {
                let mut set1 = l.tv();
                let mut set2 = r.tv();
                set1.append(&mut set2);
                set1
            }
            _ => BTreeSet::new(),
        }
    }
}

impl<T: Types> Types for Vec<T> {
    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        self.iter().flat_map(|t| t.tv()).collect()
    }
}

/// Predicate.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Pred {
    pub id: Cow<'static, str>,
    pub t: Type,
}

/// Qualifier.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Qual<T> {
    pub preds: Vec<Pred>,
    pub t: T,
}

impl Types for Pred {
    fn apply(&self, subst: &Subst) -> Self {
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
    fn apply(&self, subst: &Subst) -> Self {
        Qual {
            preds: self.preds.iter().map(|p| p.apply(subst)).collect(),
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

/// Type class.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Class {
    super_class: Vec<Cow<'static, str>>,
    insts: Vec<Inst>,
}

/// Instance.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Inst {
    qual: Qual<Pred>,
}

pub struct ClassEnv {
    classes: BTreeMap<Cow<'static, str>, Class>,
    default_types: Vec<Type>, // default types
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
    /// use typing_haskell_in_rust::type_checker::*;
    ///
    /// let mut env = ClassEnv::new(vec![]);
    /// env.add_class("Eq".into(), vec![]);
    /// env.add_class("Ord".into(), vec!["Eq".into()]);
    /// ```
    pub fn add_class(
        &mut self,
        id: Cow<'static, str>,
        super_class: Vec<Cow<'static, str>>,
    ) -> Result<(), DynError> {
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
    /// use typing_haskell_in_rust::type_checker::*;
    ///
    /// // add `Eq` class
    /// let mut env = ClassEnv::new(vec![]);
    /// env.add_class("Eq".into(), vec![]).unwrap();
    ///
    /// // add a instance of `Eq` for `Int`
    /// let eq_int = Pred {
    ///     id: "Eq".into(),
    ///     t: TINT.clone(),
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
            if its.iter().any(|inst| overlap(&p, &inst.qual.t)) {
                return Err("instance already defined".into());
            }
        }

        self.classes.get_mut(&p.id).unwrap().insts.push(Inst {
            qual: Qual { preds: ps, t: p },
        });

        Ok(())
    }

    fn super_class(&self, id: &Cow<'static, str>) -> Option<&[Cow<'static, str>]> {
        self.classes.get(id).map(|c| c.super_class.as_slice())
    }

    /// Get instances of a class.
    fn insts(&self, id: &Cow<'static, str>) -> Option<&[Inst]> {
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
            if let Ok(u) = type_match_pred(&it.qual.t, pred) {
                let result = it.qual.preds.apply(&u);
                return Some(result);
            }
        }

        None
    }

    /// Given a particular class environment `self`,
    /// the intention here is that `self.entail(ps, p)` will be True
    /// if, and only if, the predicate `p` will hold
    /// whenever all of the predicates in `ps` are satisfied.
    fn entail(&self, ps: &mut dyn Iterator<Item = &Pred>, p: &Pred) -> bool {
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

    fn reduce(&self, ps: Vec<Pred>) -> Result<Vec<Pred>, DynError> {
        let qs = self.to_hnfs(ps)?;
        Ok(self.simplify(qs))
    }
}

/// Type schemes are used to describe polymorphic types,
/// and are represented using a list of kinds and a qualified type
///
/// In a type scheme `Scheme { kind, qt }`,  each type of the form
/// `Type::TGen(n)` that appears in the qualified type `qt`
/// represents a generic, or universally quantified type variable
/// whose kind is given by `ks[n]`.
///
/// This is the only place where we will allow `Type::TGen` values to appear in a type.
struct Scheme {
    kind: Vec<Kind>,
    qt: Qual<Type>,
}

impl Types for Scheme {
    fn apply(&self, subst: &Subst) -> Scheme {
        Scheme {
            kind: self.kind.clone(),
            qt: self.qt.apply(subst),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        self.qt.tv()
    }
}

/// Type schemes are constructed by quantifying a qualified type `qt`
/// with respect to a list of type variables `vs`.
///
/// Note that the order of the kinds in `ks` is determined by the order
/// in which the variables `v` appear in `qt.tv()`,
/// and not by the order in which they appear in `vs`.
/// So, for example, the leftmost quantified variable
/// in a type scheme will always be represented by `Type::TGen(0)`.
fn quantify(vs: &[Tyvar], qt: Qual<Type>) -> Scheme {
    let vs = qt.tv().into_iter().filter(|v| vs.contains(v));

    let mut subst = Subst::new();
    for (i, v) in vs.enumerate() {
        subst.push((v, Type::TGen(i)));
    }

    let kind: Vec<_> = subst.iter().map(|(v, _)| v.kind.clone()).collect();

    Scheme {
        kind,
        qt: qt.apply(&subst),
    }
}

fn to_scheme(t: &Type) -> Scheme {
    Scheme {
        kind: vec![],
        qt: Qual {
            preds: vec![],
            t: t.clone(),
        },
    }
}

/// Get the most general unifier of two predicates.
fn mgu_pred(p1: &Pred, p2: &Pred) -> Result<Subst, DynError> {
    if p1.id != p2.id {
        return Err("classes differ".into());
    }
    mgu(&p1.t, &p2.t)
}

fn type_match_pred(p1: &Pred, p2: &Pred) -> Result<Subst, DynError> {
    if p1.id != p2.id {
        return Err("classes differ".into());
    }
    type_match(&p1.t, &p2.t)
}

/// Compose two substitutions.
fn compose(s1: &Subst, s2: &Subst) -> Subst {
    s2.iter()
        .map(|(u, t)| (u.clone(), t.apply(s1)))
        .chain(s1.clone().into_iter())
        .collect()
}

/// Merge two substitutions.
/// If there is a conflict, return `Err`.
fn merge(mut s1: Subst, s2: Subst) -> Result<Subst, DynError> {
    fn agree(s1: &Subst, s2: &Subst) -> bool {
        let set1: BTreeSet<_> = s1.iter().map(|(t, _)| t).collect();
        let set2: BTreeSet<_> = s2.iter().map(|(t, _)| t).collect();
        set1.intersection(&set2)
            .all(|t| Type::TVar((*t).clone()).apply(s1) == Type::TVar((*t).clone()).apply(s2))
    }

    if agree(&s1, &s2) {
        s1.extend(s2.into_iter());
        Ok(s1)
    } else {
        Err("merge: type variable conflict".into())
    }
}

/// Get the most general unifier.
fn mgu(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
    match (t1, t2) {
        (Type::TAp(l1, r1), Type::TAp(l2, r2)) => {
            let s1 = mgu(l1, l2)?;
            let s2 = mgu(&r1.apply(&s1), &r2.apply(&s1))?;
            Ok(compose(&s2, &s1))
        }
        (Type::TVar(u), t) => var_bind(u, t),
        (t, Type::TVar(u)) => var_bind(u, t),
        (Type::TCon(tc1), Type::TCon(tc2)) if tc1 == tc2 => Ok(NULL_SUBST),
        _ => Err("types do not unify".into()),
    }
}

/// Special case of unifying a variable `u` with a type `t`.
fn var_bind(u: &Tyvar, t: &Type) -> Result<Subst, DynError> {
    // t == Type::TVar(u)
    if let Type::TVar(u_) = t {
        if u == u_ {
            return Ok(NULL_SUBST);
        }
    }

    if t.tv().contains(u) {
        return Err("occurs check fails".into());
    }

    // ensure that the substitution is kind-preserving
    if u.kind() != t.kind() {
        return Err("kinds do not match".into());
    }

    Ok(vec![(u.clone(), t.clone())])
}

/// Given two types `t1` and `t2`, the goal of matching is to find a substitution s such that apply `t1.(s) == t2`.
/// Because the substitution is applied only to one type, this operation is often described as one-way matching.
fn type_match(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
    match (t1, t2) {
        (Type::TAp(l1, r1), Type::TAp(l2, r2)) => {
            let s1 = type_match(l1, l2)?;
            let s2 = type_match(r1, r2)?;
            merge(s1, s2)
        }
        (Type::TVar(u), t) if u.kind() == t.kind() => Ok(vec![(u.clone(), t.clone())]),
        (Type::TCon(tc1), Type::TCon(tc2)) if tc1 == tc2 => Ok(NULL_SUBST),
        _ => Err("types do not match".into()),
    }
}

fn enum_id(n: usize) -> String {
    format!("v{n}")
}

/// Check if pred.t is the head normal form.
fn in_hnf(pred: &Pred) -> bool {
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

#[cfg(test)]
mod tests {
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
            t: TINT.clone(),
        };
        env.add_inst(vec![], eq_int).unwrap();

        // get the instances of `Eq`
        let eq_insts = env.insts(&"Eq".into()).unwrap();
        eprintln!("{:?}", eq_insts);

        let expected = vec![Inst {
            qual: Qual {
                preds: Vec::new(),
                t: Pred {
                    id: "Eq".into(),
                    t: TINT.clone(),
                },
            },
        }];

        assert_eq!(eq_insts, expected);
    }
}
