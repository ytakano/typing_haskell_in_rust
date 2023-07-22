use std::{borrow::Cow, collections::BTreeSet};

use crate::types::{Subst, Types, Tyvar};

use super::scheme::Scheme;

/// Assumptions about the type of a variable are represented by values of the `Assump` datatype,
/// each of which pairs a variable name with a type scheme.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Assump {
    pub(super) id: Cow<'static, str>, // variable name
    pub(super) scheme: Scheme,        // type scheme
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
