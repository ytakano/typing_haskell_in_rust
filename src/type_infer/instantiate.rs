use crate::{
    predicate::{Pred, Qual},
    types::Type,
};

pub trait Instantiate {
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
