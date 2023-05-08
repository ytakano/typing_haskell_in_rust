use crate::{
    ast::{Expr, Literal, Pat},
    error::DynError,
    predicate::{Pred, Qual},
    type_class::ClassEnv,
    types::*,
};
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    ops::ControlFlow,
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
    id: Cow<'static, str>, // variable name
    scheme: Scheme,        // type scheme
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

pub struct Ambiguity {
    tyvar: Tyvar,
    preds: Vec<Pred>,
}

fn ambiguities(ce: &ClassEnv, vs: &[Tyvar], ps: &Vec<Pred>) -> Vec<Ambiguity> {
    let mut multiset = BTreeMap::new();
    vs.iter().for_each(|t| {
        if let Some(val) = multiset.get_mut(t) {
            *val += 1;
        } else {
            multiset.insert(t.clone(), 1);
        }
    });

    let mut result = Vec::new();

    ps.tv()
        .into_iter()
        .filter(|t| {
            if let Some(val) = multiset.get_mut(t) {
                *val -= 1;
                if *val == 0 {
                    multiset.remove(t);
                }
                true
            } else {
                false
            }
        })
        .for_each(|tyvar| {
            let preds = ps
                .iter()
                .filter(|p| p.tv().contains(&tyvar))
                .map(|p| p.clone())
                .collect();
            let ambiguity = Ambiguity { tyvar, preds };
            result.push(ambiguity)
        });

    result
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
                Ok((vec![Pred::new("Integral".into(), v.clone())], v))
            }
            Literal::Float(_) => {
                let v = self.new_tvar(Kind::Star);
                Ok((vec![Pred::new("RealFloat".into(), v.clone())], v))
            }
            Literal::Str(_) => Ok((vec![], mk_list(T_CHAR.clone()))),
        }
    }

    fn ti_pat(&mut self, pat: &Pat) -> Result<(Vec<Pred>, Vec<Assump>, Type), DynError> {
        match pat {
            Pat::Var(i) => {
                let v = self.new_tvar(Kind::Star);
                Ok((
                    Vec::new(),
                    vec![Assump {
                        id: i.clone().into(),
                        scheme: to_scheme(&v),
                    }],
                    v,
                ))
            }
            Pat::Wildcard => {
                let v = self.new_tvar(Kind::Star);
                Ok((Vec::new(), Vec::new(), v))
            }
            Pat::Lit(l) => {
                let (ps, t) = self.ti_lit(l)?;
                Ok((ps, Vec::new(), t))
            }
            Pat::As { id, pat } => {
                let (ps, mut assump, t) = self.ti_pat(pat)?;
                let mut new_assump = vec![Assump {
                    id: id.clone().into(),
                    scheme: to_scheme(&t),
                }];
                new_assump.append(&mut assump);
                Ok((ps, new_assump, t))
            }
            Pat::Con {
                assump: Assump { id: _, scheme },
                pat,
            } => {
                let (mut ps, assump, ts) = self.ti_pats(pat)?;
                let tv = self.new_tvar(Kind::Star);
                let Qual { mut preds, t } = self.fresh_inst(scheme);
                let t2 = ts
                    .iter()
                    .rev()
                    .fold(tv.clone(), |acc, t| mk_fn(t.clone(), acc));

                self.unify(&t, &t2)?;
                ps.append(&mut preds);

                Ok((ps, assump, tv))
            }
        }
    }

    fn ti_pats(&mut self, pats: &[Pat]) -> Result<(Vec<Pred>, Vec<Assump>, Vec<Type>), DynError> {
        let mut ps = Vec::new();
        let mut assump = Vec::new();
        let mut ts = Vec::new();

        let result = pats
            .iter()
            .map(|pat| self.ti_pat(pat))
            .try_for_each(|result| match result {
                Ok((mut ps_, mut assump_, t)) => {
                    ps.append(&mut ps_);
                    assump.append(&mut assump_);
                    ts.push(t);
                    ControlFlow::Continue(())
                }
                Err(e) => ControlFlow::Break(e),
            });

        if let ControlFlow::Break(e) = result {
            Err(e)
        } else {
            Ok((ps, assump, ts))
        }
    }

    fn ti_expr(ce: &ClassEnv, assump: &Assump, expr: &Expr) -> Result<(Vec<Pred>, Type), DynError> {
        todo!()
    }

    fn split(
        &mut self,
        ce: &ClassEnv,
        fs: &[Tyvar], // The set of ‘fixed’ variables, which are just the variables appearing free in the assumptions.
        gs: &[Tyvar], // The set of variables over which we would like to quantify.
        ps: Vec<Pred>,
    ) -> Result<(Vec<Pred>, Vec<Pred>), DynError> {
        let ps = ce.reduce(ps)?;
        let (ds, rs): (Vec<_>, Vec<_>) = ps
            .into_iter()
            .partition(|p| p.tv().iter().all(|t| fs.contains(t)));
        // TODO: defaultedPreds

        Ok((ds, rs))
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
