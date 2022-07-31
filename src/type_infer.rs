use crate::{
    ast::Literal,
    error::DynError,
    predicate::{Pred, Qual},
    types::*,
};
use std::{borrow::Cow, collections::BTreeSet};

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

/// Assumptions about the type of a variable are represented by values of the `Assump` datatype,
/// each of which pairs a variable name with a type scheme.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Assump {
    id: Cow<'static, str>,
    scheme: Scheme,
}

impl Types for Assump {
    fn apply(&self, subst: &Subst) -> Self {
        Assump {
            id: self.id.clone(),
            scheme: self.scheme.apply(subst),
        }
    }

    fn tv(&self) -> BTreeSet<Tyvar> {
        self.scheme.tv()
    }
}

fn find(id: &str, assumps: &[Assump]) -> Result<Scheme, DynError> {
    for assump in assumps {
        if assump.id == id {
            return Ok(assump.scheme.clone());
        }
    }

    Err("unbound identifier".into())
}

#[derive(Debug)]
struct TypeInfer {
    subst: Subst,
    n: usize,
}

impl TypeInfer {
    fn new() -> Self {
        TypeInfer {
            subst: Subst::new(),
            n: 0,
        }
    }

    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), DynError> {
        let t1 = t1.apply(&self.subst);
        let t2 = t2.apply(&self.subst);
        let u = mgu(&t1, &t2)?;

        self.subst = compose(&u, &self.subst);

        Ok(())
    }

    fn new_tvar(&mut self, kind: Kind) -> Type {
        let id = enum_id(self.n);
        self.n += 1;
        Type::TVar(Tyvar {
            id: id.into(),
            kind,
        })
    }

    fn fresh_inst(&mut self, scheme: &Scheme) -> Qual<Type> {
        let ts: Vec<_> = scheme
            .kind
            .iter()
            .map(|k| self.new_tvar(k.clone()))
            .collect();
        scheme.qt.inst(&ts)
    }

    fn ti_lit(&mut self, lit: &Literal) -> Result<(Vec<Pred>, Type), DynError> {
        match lit {
            Literal::Bool(_) => Ok((vec![], T_BOOL.clone())),
            Literal::Char(_) => Ok((vec![], T_CHAR.clone())),
            Literal::Int(_) => {
                let v = self.new_tvar(Kind::Star);
                Ok((
                    vec![
                        Pred::new("Integral".into(), v.clone()),
                        Pred::new("Eq".into(), v.clone()),
                        Pred::new("Show".into(), v.clone()),
                    ],
                    v,
                ))
            }
            Literal::Float(_) => {
                let v = self.new_tvar(Kind::Star);
                Ok((
                    vec![
                        Pred::new("RealFrac".into(), v.clone()),
                        Pred::new("Show".into(), v.clone()),
                    ],
                    v,
                ))
            }
            Literal::Str(_) => Ok((vec![], mk_list(T_CHAR.clone()))),
        }
    }
}

trait Instantiate {
    fn inst(&self, types: &[Type]) -> Self;
}

impl Instantiate for Type {
    fn inst(&self, types: &[Type]) -> Self {
        match self {
            Type::TAp(l, r) => Type::TAp(Box::new(l.inst(types)), Box::new(r.inst(types))),
            Type::TGen(n) => types[*n].clone(),
            t => t.clone(),
        }
    }
}

impl<T: Instantiate> Instantiate for Vec<T> {
    fn inst(&self, types: &[Type]) -> Self {
        self.iter().map(|t| t.inst(types)).collect()
    }
}

impl<T: Instantiate> Instantiate for Qual<T> {
    fn inst(&self, types: &[Type]) -> Self {
        Qual {
            preds: self.preds.inst(types),
            t: self.t.inst(types),
        }
    }
}

impl Instantiate for Pred {
    fn inst(&self, types: &[Type]) -> Self {
        Pred {
            id: self.id.clone(),
            t: self.t.inst(types),
        }
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

fn enum_id(n: usize) -> String {
    format!("v{n}")
}
