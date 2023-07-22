use crate::{
    ast::{Expr, Literal, Pat},
    error::DynError,
    predicate::{Pred, Qual},
    type_class::ClassEnv,
    type_infer::ambiguity::ambiguities,
    types::*,
};

use std::{borrow::Cow, ops::ControlFlow};

use self::{ambiguity::Ambiguity, assump::Assump, instantiate::Instantiate, scheme::Scheme};

mod ambiguity;
pub mod assump;
mod instantiate;
pub mod scheme;

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

    fn ti_expr(
        &mut self,
        ce: &ClassEnv,
        assumps: &[Assump],
        expr: &Expr,
    ) -> Result<(Vec<Pred>, Type), DynError> {
        match expr {
            Expr::Var(id) => {
                let sc = find(id, assumps)?;
                let inst = self.fresh_inst(&sc);
                Ok((inst.preds.clone(), inst.t.clone()))
            }
            Expr::Const(assump) => {
                let inst = self.fresh_inst(&assump.scheme);
                Ok((inst.preds.clone(), inst.t.clone()))
            }
            Expr::Lit(l) => self.ti_lit(l),
            Expr::Ap(e, f) => {
                let (mut ps, te) = self.ti_expr(ce, assumps, e)?;
                let (mut qs, tf) = self.ti_expr(ce, assumps, f)?;

                let t = self.new_tvar(Kind::Star);
                let fn_type = mk_fn(tf, t.clone());

                self.unify(&fn_type, &te)?;
                ps.append(&mut qs);

                Ok((ps, t))
            }
            Expr::Let(bg, e) => {
                // TODO: ti_bind_group
                todo!()
            }
        }
    }

    fn split(
        &mut self,
        ce: &ClassEnv,
        fs: &[Tyvar], // The set of ‘fixed’ variables, which are just the variables appearing free in the assumptions.
        gs: &[Tyvar], // The set of variables over which we would like to quantify.
        ps: Vec<Pred>,
        num_classes: &[Cow<str>],
        std_classes: &[Cow<str>],
    ) -> Result<(Vec<Pred>, Vec<Pred>), DynError> {
        let ps = ce.reduce(ps)?;
        let (ds, rs): (Vec<_>, Vec<_>) = ps
            .into_iter()
            .partition(|p| p.tv().iter().all(|t| fs.contains(t)));

        let mut vs = Vec::new();

        for tv in fs.iter() {
            vs.push(tv.clone());
        }
        for tv in gs.iter() {
            vs.push(tv.clone());
        }

        let rs2 = defaulted_preds(ce, &vs, &rs, num_classes, std_classes)?;

        let rs3: Vec<_> = rs.into_iter().filter(|p| !rs2.contains(p)).collect();

        Ok((ds, rs3))
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

fn with_defaults<F, A>(
    f: F,
    ce: &ClassEnv,
    vs: &[Tyvar],
    ps: &Vec<Pred>,
    num_classes: &[Cow<str>],
    std_classes: &[Cow<str>],
) -> Result<A, &'static str>
where
    F: Fn(&[Ambiguity], &[Type]) -> A,
{
    let vps = ambiguities(ce, vs, ps);
    let tss: Vec<_> = vps
        .iter()
        .map(|a| a.candidates(ce, num_classes, std_classes))
        .collect();

    if tss.iter().any(|t| t.is_empty()) {
        return Err("cannot resolve ambiguity");
    }

    let mut types = Vec::new();

    fn take<T>(mut vec: Vec<T>, index: usize) -> Option<T> {
        if vec.get(index).is_none() {
            None
        } else {
            Some(vec.swap_remove(index))
        }
    }

    for ts in tss {
        let a = take(ts, 0).ok_or("empty types")?;
        types.push(a);
    }

    Ok(f(&vps, &types))
}

fn defaulted_preds(
    ce: &ClassEnv,
    vs: &[Tyvar],
    ps: &Vec<Pred>,
    num_classes: &[Cow<str>],
    std_classes: &[Cow<str>],
) -> Result<Vec<Pred>, &'static str> {
    with_defaults(
        |vps, _ts| {
            let mut result = Vec::new();
            for vp in vps.iter() {
                for pred in vp.preds.iter() {
                    result.push(pred.clone());
                }
            }
            result
        },
        ce,
        vs,
        ps,
        num_classes,
        std_classes,
    )
}

fn defaulted_subst(
    ce: &ClassEnv,
    vs: &[Tyvar],
    ps: &Vec<Pred>,
    num_classes: &[Cow<str>],
    std_classes: &[Cow<str>],
) -> Result<Subst, &'static str> {
    with_defaults(
        |vps, ts| {
            let mut result = Vec::new();

            for (vp, t) in vps.iter().zip(ts.iter()) {
                result.push((vp.tyvar.clone(), t.clone()));
            }

            result
        },
        ce,
        vs,
        ps,
        num_classes,
        std_classes,
    )
}
