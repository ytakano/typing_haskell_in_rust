use crate::{
    ast::{Alt, Expr, Literal, Pat},
    error::DynError,
    predicate::{Pred, Qual},
    type_class::ClassEnv,
    type_infer::ambiguity::ambiguities,
    types::*,
    CowStr, CowVec,
};

use std::{borrow::Cow, collections::BTreeSet, ops::ControlFlow};

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

struct Expl {
    id: CowStr,
    scheme: Scheme,
    alts: CowVec<Alt>,
}

struct Impl {
    id: CowStr,
    alts: CowVec<Alt>,
}

fn restricted(bs: &[Impl]) -> bool {
    fn simple(im: &Impl) -> bool {
        im.alts.iter().any(|alt| alt.pats.is_empty())
    }
    bs.iter().any(simple)
}

#[derive(Debug)]
struct TypeInfer {
    subst: Subst,
    n: usize,
    num_classes: CowVec<CowStr>,
    std_classes: CowVec<CowStr>,
}

impl TypeInfer {
    fn new(num_classes: CowVec<CowStr>, std_classes: CowVec<CowStr>) -> Self {
        TypeInfer {
            subst: null_subst(),
            n: 0,
            num_classes,
            std_classes,
        }
    }

    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), DynError> {
        let t1 = t1.apply(self.subst.clone());
        let t2 = t2.apply(self.subst.clone());
        let u = mgu(&t1, &t2)?;

        self.subst = compose(u, self.subst.clone());

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

    /// Instantiate a type scheme with new type variables of appropriate kinds.
    fn fresh_inst(&mut self, scheme: &Scheme) -> Qual<Type> {
        let ts: Vec<_> = scheme
            .kind
            .iter()
            .map(|k| self.new_tvar(k.clone()))
            .collect();
        scheme.qt.inst(&ts)
    }

    fn ti_lit(&mut self, lit: &Literal) -> Result<(CowVec<Pred>, Type), DynError> {
        match lit {
            Literal::Bool(_) => Ok((vec![].into(), T_BOOL.clone())),
            Literal::Char(_) => Ok((vec![].into(), T_CHAR.clone())),
            Literal::Int(_) => {
                let v = self.new_tvar(Kind::Star);
                Ok((vec![Pred::new("Integral".into(), v.clone())].into(), v))
            }
            Literal::Float(_) => {
                let v = self.new_tvar(Kind::Star);
                Ok((vec![Pred::new("RealFloat".into(), v.clone())].into(), v))
            }
            Literal::Str(_) => Ok((vec![].into(), mk_list(T_CHAR.clone()))),
        }
    }

    fn ti_pat(&mut self, pat: &Pat) -> Result<(CowVec<Pred>, Vec<Assump>, Type), DynError> {
        match pat {
            Pat::Var(i) => {
                let v = self.new_tvar(Kind::Star);
                Ok((
                    Vec::new().into(),
                    vec![Assump {
                        id: i.clone().into(),
                        scheme: to_scheme(&v),
                    }],
                    v,
                ))
            }
            Pat::Wildcard => {
                let v = self.new_tvar(Kind::Star);
                Ok((Vec::new().into(), Vec::new(), v))
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
                ps.to_mut().append(preds.to_mut());

                Ok((ps, assump, tv))
            }
        }
    }

    fn ti_pats(
        &mut self,
        pats: &[Pat],
    ) -> Result<(CowVec<Pred>, Vec<Assump>, Vec<Type>), DynError> {
        let mut ps = Vec::new();
        let mut assump = Vec::new();
        let mut ts = Vec::new();

        let result = pats
            .iter()
            .map(|pat| self.ti_pat(pat))
            .try_for_each(|result| match result {
                Ok((mut ps_, mut assump_, t)) => {
                    ps.append(ps_.to_mut());
                    assump.append(&mut assump_);
                    ts.push(t);
                    ControlFlow::Continue(())
                }
                Err(e) => ControlFlow::Break(e),
            });

        if let ControlFlow::Break(e) = result {
            Err(e)
        } else {
            Ok((ps.into(), assump, ts))
        }
    }

    fn ti_expr(
        &mut self,
        ce: &ClassEnv,
        assumps: &[Assump],
        expr: &Expr,
    ) -> Result<(CowVec<Pred>, Type), DynError> {
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
                ps.to_mut().append(qs.to_mut());

                Ok((ps, t))
            }
            Expr::Let(bg, e) => {
                // TODO: ti_bind_group
                todo!()
            }
        }
    }

    fn ti_alt(
        &mut self,
        ce: &ClassEnv,
        assumps: &[Assump],
        alt: &Alt,
    ) -> Result<(CowVec<Pred>, Type), DynError> {
        let (mut ps, mut ass, ts) = self.ti_pats(&alt.pats)?;
        ass.extend(assumps.iter().map(|a| a.clone()));
        let (mut qs, t) = self.ti_expr(ce, &ass, &alt.expr)?;

        ps.to_mut().append(qs.to_mut());

        let t2 = ts.iter().rev().fold(t, |acc, t| mk_fn(t.clone(), acc));

        Ok((ps, t2))
    }

    fn ti_alts(
        &mut self,
        ce: &ClassEnv,
        assumps: &[Assump],
        alts: &[Alt],
        t: &Type,
    ) -> Result<CowVec<Pred>, DynError> {
        let mut preds = Vec::new();
        let mut ts = Vec::new();
        for alt in alts.iter() {
            let (mut ps, t2) = self.ti_alt(ce, assumps, alt)?;
            preds.append(ps.to_mut());
            ts.push(t2);
        }

        for t2 in ts.iter() {
            self.unify(t, t2)?;
        }

        Ok(preds.into())
    }

    fn ti_expl(
        &mut self,
        ce: &ClassEnv,
        assumps: CowVec<Assump>,
        expl: &Expl,
    ) -> Result<CowVec<Pred>, DynError> {
        let qt = self.fresh_inst(&expl.scheme);
        let ps = self.ti_alts(ce, &assumps, &expl.alts, &qt.t)?;

        let qs2 = qt.preds.apply(self.subst.clone());
        let t2 = qt.t.apply(self.subst.clone());
        let fs = assumps.apply(self.subst.clone()).tv();
        let gs: Vec<_> = t2.tv().difference(&fs).cloned().collect();
        let sc2 = quantify(
            &gs,
            Qual {
                preds: qs2.clone(),
                t: t2,
            },
        );
        let ps = ps
            .apply(self.subst.clone())
            .iter()
            .filter(|p| !ce.entail(&mut qs2.iter(), p))
            .cloned()
            .collect();

        let (ds, rs) = self.split(ce, &fs, &gs, ps)?;

        if expl.scheme != sc2 {
            Err("signature too general".into())
        } else if !rs.is_empty() {
            Err("context too weak".into())
        } else {
            Ok(ds)
        }
    }

    fn ti_impl(
        &mut self,
        ce: &ClassEnv,
        assumps: CowVec<Assump>,
        bs: &[Impl],
    ) -> Result<(CowVec<Pred>, CowVec<Assump>), DynError> {
        let ts: CowVec<_> = bs.iter().map(|_| self.new_tvar(Kind::Star)).collect();

        let is: Vec<_> = bs.iter().map(|im| im.id.clone()).collect();
        let scs = ts.iter().map(|t| to_scheme(&t));
        let assumps2: Vec<_> = is
            .iter()
            .zip(scs)
            .map(|(id, scheme)| Assump {
                id: id.clone(),
                scheme,
            })
            .chain(assumps.iter().cloned())
            .collect();
        let altss = bs.iter().map(|im| im.alts.clone());

        let pss: Result<Vec<_>, _> = altss
            .zip(ts.iter())
            .map(|(alts, t)| self.ti_alts(ce, &assumps2, &alts, t))
            .collect();
        let pss = pss?;

        let ps2 = CowVec::Owned(pss.concat()).apply(self.subst.clone());
        let ts2 = ts.apply(self.subst.clone());
        let fs = assumps.apply(self.subst.clone()).tv();
        let vss: Vec<_> = ts2.iter().map(|t| t.tv()).collect();

        let mut it = vss.clone().into_iter().rev();
        let first = it.next().ok_or("vss is empty")?;
        let it = it.fold(first, |acc, s| s.union(&acc).cloned().collect());
        let gs = it.difference(&fs);

        let mut it = vss.into_iter().rev();
        let first = it.next().ok_or("vss is empty")?;
        let gs_vec: Vec<_> = it
            .fold(first, |acc, s| s.intersection(&acc).cloned().collect())
            .into_iter()
            .collect();

        let (mut ds, mut rs) = self.split(ce, &fs, &gs_vec, ps2)?;

        if restricted(&bs) {
            let tv_rs = rs.tv();
            let gs2: Vec<_> = gs.filter(|p| !tv_rs.contains(p)).cloned().collect();
            let scs2 = ts2.iter().map(|t| {
                quantify(
                    &gs2,
                    Qual {
                        preds: Cow::Borrowed(&[]),
                        t: t.clone(),
                    },
                )
            });

            ds.to_mut().append(rs.to_mut());

            let right = is
                .into_iter()
                .zip(scs2)
                .map(|(id, scheme)| Assump { id, scheme })
                .collect();

            Ok((ds, right))
        } else {
            let gs: Vec<_> = gs.cloned().collect();
            let scs2 = ts2.iter().map(|t| {
                quantify(
                    &gs,
                    Qual {
                        preds: rs.clone(),
                        t: t.clone(),
                    },
                )
            });

            let right = is
                .into_iter()
                .zip(scs2)
                .map(|(id, scheme)| Assump { id, scheme })
                .collect();

            Ok((ds, right))
        }
    }

    fn split(
        &mut self,
        ce: &ClassEnv,
        fs: &BTreeSet<Tyvar>, // The set of ‘fixed’ variables, which are just the variables appearing free in the assumptions.
        gs: &[Tyvar],         // The set of variables over which we would like to quantify.
        ps: CowVec<Pred>,
    ) -> Result<(CowVec<Pred>, CowVec<Pred>), DynError> {
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

        let rs: CowVec<Pred> = Cow::Owned(rs);

        let rs2 = defaulted_preds(ce, &vs, rs.clone(), &self.num_classes, &self.std_classes)?;

        let rs3: Vec<_> = rs
            .to_vec()
            .into_iter()
            .filter(|p| !rs2.contains(p))
            .collect();

        Ok((ds.into(), rs3.into()))
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

    let mut subst = Vec::new();
    for (i, v) in vs.enumerate() {
        subst.push((v, Type::TGen(i)));
    }

    let kind: Vec<_> = subst.iter().map(|(v, _)| v.kind.clone()).collect();

    Scheme {
        kind: kind.into(),
        qt: qt.apply(subst.into()),
    }
}

fn to_scheme(t: &Type) -> Scheme {
    Scheme {
        kind: vec![].into(),
        qt: Qual {
            preds: vec![].into(),
            t: t.clone(),
        },
    }
}

/// Generates a unique identifier string from a given usize value.
///
/// This function takes an usize `n` as input and returns a String of the form "v{n}".
/// This function is typically used to generate fresh variable names during processes such as type inference.
///
/// # Arguments
///
/// * `n` - A usize value used to generate a unique identifier string.
fn enum_id(n: usize) -> String {
    format!("v{n}")
}

fn with_defaults<F, A>(
    f: F,
    ce: &ClassEnv,
    vs: &[Tyvar],
    ps: CowVec<Pred>,
    num_classes: &[CowStr],
    std_classes: &[CowStr],
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
    ps: CowVec<Pred>,
    num_classes: &[CowStr],
    std_classes: &[CowStr],
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
    ps: CowVec<Pred>,
    num_classes: &[CowStr],
    std_classes: &[CowStr],
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
    .map(|r| r.into())
}
