use std::borrow::Cow;

use crate::{
    predicate::Pred,
    type_class::ClassEnv,
    types::{Type, Types, Tyvar},
    CowVec,
};

pub struct Ambiguity {
    pub tyvar: Tyvar,
    pub preds: CowVec<Pred>,
}

impl Ambiguity {
    pub fn candidates(
        &self,
        ce: &ClassEnv,
        num_classes: &[Cow<str>],
        std_classes: &[Cow<str>],
    ) -> Vec<Type> {
        let mut result = Vec::new();

        let is = self.preds.iter().map(|n| &n.id);
        let mut ts = self.preds.iter().map(|n| &n.t);

        let v = Type::TVar(self.tyvar.clone());
        let ref_v = &v;

        if ts.all(|t| *t == *ref_v)
            && is.clone().any(|i| num_classes.contains(i))
            && is.clone().all(|i| std_classes.contains(i))
        {
            for t in ce.default_types.iter() {
                if is
                    .clone()
                    .map(|i| Pred {
                        id: i.clone(),
                        t: t.clone(),
                    })
                    .all(|pred| {
                        let empty = Vec::new();
                        ce.entail(&mut empty.iter(), &pred)
                    })
                {
                    result.push(t.clone());
                }
            }
        }

        result
    }
}

pub fn ambiguities(ce: &ClassEnv, vs: &[Tyvar], ps: CowVec<Pred>) -> Vec<Ambiguity> {
    let mut result = Vec::new();

    ps.tv()
        .into_iter()
        .filter(|t| vs.contains(t))
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
