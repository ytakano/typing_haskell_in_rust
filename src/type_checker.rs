use crate::error::DynError;
use once_cell::sync::Lazy;
use std::{borrow::Cow, collections::BTreeSet};

type Subst = Vec<(Tyvar, Type)>;
const NULL_SUBST: Subst = vec![];

/// Kind of type.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
enum Kind {
    Star,
    Kfun(Box<Kind>, Box<Kind>),
}

/// Type variable.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
struct Tyvar {
    id: Cow<'static, str>,
    kind: Kind,
}

/// Type constructor.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Tycon {
    id: Cow<'static, str>,
    kind: Kind,
}

/// Type
#[derive(PartialEq, Eq, Debug, Clone)]
enum Type {
    TVar(Tyvar),               // type variable
    TCon(Tycon),               // type constructor
    TAp(Box<Type>, Box<Type>), // type application
    TGen(usize),               // generic or quantified type variables
}

macro_rules! def_type {
    ( $id:ident, $ty:expr) => {
        static $id: Lazy<Type> = Lazy::new(|| {
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

static TLIST: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "[]".into(),
        kind: Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star)),
    })
});

static TARROW: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(->)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

static TTUPLE2: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(,)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

fn mk_fn(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(TARROW.clone()),
        Box::new(Type::TAp(Box::new(a), Box::new(b))),
    )
}

fn mk_list(a: Type) -> Type {
    Type::TAp(Box::new(TLIST.clone()), Box::new(a))
}

fn mk_pair(a: Type, b: Type) -> Type {
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
    fn tv(&self) -> Vec<Tyvar>; // set of type variables in `self`
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

    fn tv(&self) -> Vec<Tyvar> {
        match self {
            Type::TVar(u) => vec![u.clone()],
            Type::TAp(l, r) => l.tv().into_iter().chain(r.tv()).collect(),
            _ => vec![],
        }
    }
}

impl<T: Types> Types for Vec<T> {
    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }

    fn tv(&self) -> Vec<Tyvar> {
        self.iter().flat_map(|t| t.tv()).collect()
    }
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
fn merge(s1: &Subst, s2: &Subst) -> Result<Subst, DynError> {
    fn agree(s1: &Subst, s2: &Subst) -> bool {
        let set1: BTreeSet<_> = s1.iter().map(|(t, _)| t).collect();
        let set2: BTreeSet<_> = s2.iter().map(|(t, _)| t).collect();
        set1.intersection(&set2)
            .all(|t| Type::TVar((*t).clone()).apply(s1) == Type::TVar((*t).clone()).apply(s2))
    }

    if agree(s1, s2) {
        Ok([s1.clone(), s2.clone()].concat())
    } else {
        Err("merge: type variable conflict".into())
    }
}

fn enum_id(n: usize) -> String {
    format!("v{n}")
}
