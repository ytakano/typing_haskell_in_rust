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
struct Pred {
    id: Cow<'static, str>,
    t: Type,
}

/// Qualifier.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Qual<T> {
    preds: Vec<Pred>,
    t: T,
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
struct Class {
    super_class: Vec<Cow<'static, str>>,
    insts: Vec<Inst>,
}

/// Instance.
struct Inst {
    qual: Qual<Pred>,
}

struct ClassEnv {
    classes: BTreeMap<Cow<'static, str>, Class>,
    default_types: Vec<Type>, // default types
}

impl ClassEnv {
    fn new(default_types: Vec<Type>) -> Self {
        ClassEnv {
            classes: BTreeMap::new(),
            default_types,
        }
    }

    fn add_class(
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

    fn add_inst(&mut self, id: Cow<'static, str>, qual: Qual<Pred>) -> Result<(), DynError> {
        if !self.classes.contains_key(&id) {
            return Err("class not defined".into());
        }

        fn overlap(p1: &Pred, p2: &Pred) -> bool {
            mgu_pred(p1, p2).is_ok()
        }

        if qual.preds.iter().any(|p| overlap(&qual.t, p)) {
            return Err("overlapping instance".into());
        }

        self.classes.get_mut(&id).unwrap().insts.push(Inst { qual });

        Ok(())
    }

    fn super_class(&self, id: &Cow<'static, str>) -> Option<&Vec<Cow<'static, str>>> {
        self.classes.get(id).map(|c| &c.super_class)
    }

    fn insts(&self, id: &Cow<'static, str>) -> Option<&Vec<Inst>> {
        self.classes.get(id).map(|c| &c.insts)
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
