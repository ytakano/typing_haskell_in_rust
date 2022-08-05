use once_cell::sync::Lazy;
use std::{borrow::Cow, collections::BTreeSet};

use crate::error::DynError;

pub(crate) type Subst = Vec<(Tyvar, Type)>;
pub(crate) const NULL_SUBST: Subst = vec![];

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

def_type!(T_UNIT, "Unit");
def_type!(T_CHAR, "Char");
def_type!(T_BOOL, "Bool");
def_type!(T_INT, "Int");
def_type!(T_INTEGER, "Integer");
def_type!(T_FOLAT, "Float");
def_type!(T_DOUBLE, "Double");

pub static T_LIST: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "[]".into(),
        kind: Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star)),
    })
});

pub static T_ARROW: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(->)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

pub static T_TUPLE2: Lazy<Type> = Lazy::new(|| {
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
        Box::new(T_ARROW.clone()),
        Box::new(Type::TAp(Box::new(a), Box::new(b))),
    )
}

pub fn mk_list(a: Type) -> Type {
    Type::TAp(Box::new(T_LIST.clone()), Box::new(a))
}

pub fn mk_pair(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(Type::TAp(Box::new(T_TUPLE2.clone()), Box::new(a))),
        Box::new(b),
    )
}

pub(crate) trait HasKind {
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

pub(crate) trait Types {
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

/// Get the most general unifier.
pub(crate) fn mgu(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
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

/// Compose two substitutions.
pub(crate) fn compose(s1: &Subst, s2: &Subst) -> Subst {
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

/// Given two types `t1` and `t2`, the goal of matching is to find a substitution s such that apply `t1.(s) == t2`.
/// Because the substitution is applied only to one type, this operation is often described as one-way matching.
pub(crate) fn type_match(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
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
