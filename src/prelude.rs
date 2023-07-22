use crate::{
    predicate::Pred,
    type_class::ClassEnv,
    types::{
        mk_list, mk_tvar, Kind, Type, T_BOOL, T_CHAR, T_DOUBLE, T_FOLAT, T_INT, T_INTEGER, T_LIST,
        T_UNIT,
    },
};

use std::vec;

pub fn haskell(class_env: &mut ClassEnv) {
    // core classes
    class_env.add_class("Eq".into(), Vec::new()).unwrap();
    class_env
        .add_class("Ord".into(), vec!["Eq".into()])
        .unwrap();
    class_env.add_class("Show".into(), vec![]).unwrap();
    class_env.add_class("Read".into(), vec![]).unwrap();
    class_env.add_class("Bounded".into(), vec![]).unwrap();
    class_env.add_class("Enum".into(), vec![]).unwrap();
    class_env.add_class("Functor".into(), vec![]).unwrap();
    class_env
        .add_class("Applicative".into(), vec!["Functor".into()])
        .unwrap();
    class_env
        .add_class("Monad".into(), vec!["Applicative".into()])
        .unwrap();

    // numeric classes
    class_env.add_class("Num".into(), vec![]).unwrap();
    class_env
        .add_class("Real".into(), vec!["Num".into(), "Ord".into()])
        .unwrap();
    class_env
        .add_class("Fractional".into(), vec!["Num".into()])
        .unwrap();
    class_env
        .add_class("Integral".into(), vec!["Real".into(), "Enum".into()])
        .unwrap();
    class_env
        .add_class("RealFrac".into(), vec!["Real".into(), "Fractional".into()])
        .unwrap();
    class_env
        .add_class("Floating".into(), vec!["Fractional".into()])
        .unwrap();
    class_env
        .add_class(
            "RealFloat".into(),
            vec!["RealFrac".into(), "Floating".into()],
        )
        .unwrap();

    // instances
    instances_of_unit(class_env);
    instances_of_char(class_env);
    instances_of_int(class_env);
    instances_of_bool(class_env);
    instances_of_integer(class_env);
    instances_of_fp(class_env, &T_FOLAT);
    instances_of_fp(class_env, &T_DOUBLE);
    instances_of_list(class_env);
}

fn instances_of_char(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), T_CHAR.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), T_CHAR.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Enum".into(), T_CHAR.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Bounded".into(), T_CHAR.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), T_CHAR.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), T_CHAR.clone()))
        .unwrap();
}

fn instances_of_int(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Bounded".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Enum".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Num".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Real".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Integral".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), T_INT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), T_INT.clone()))
        .unwrap();
}

fn instances_of_bool(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Enum".into(), T_BOOL.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), T_BOOL.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), T_BOOL.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Bounded".into(), T_BOOL.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), T_BOOL.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), T_BOOL.clone()))
        .unwrap();
}

fn instances_of_integer(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Num".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Real".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Integral".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), T_INTEGER.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), T_INTEGER.clone()))
        .unwrap();
}

fn instances_of_fp(class_env: &mut ClassEnv, t: &Type) {
    class_env
        .add_inst(Vec::new(), Pred::new("Enum".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Num".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Fractional".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Real".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Floating".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("RealFrac".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("RealFloat".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), t.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), t.clone()))
        .unwrap();
}

fn instances_of_unit(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Eq".into(), T_UNIT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Ord".into(), T_UNIT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Enum".into(), T_UNIT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Bounded".into(), T_UNIT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Show".into(), T_UNIT.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Read".into(), T_UNIT.clone()))
        .unwrap();
}

fn instances_of_list(class_env: &mut ClassEnv) {
    class_env
        .add_inst(Vec::new(), Pred::new("Functor".into(), T_LIST.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Applicative".into(), T_LIST.clone()))
        .unwrap();
    class_env
        .add_inst(Vec::new(), Pred::new("Monad".into(), T_LIST.clone()))
        .unwrap();

    let tv = mk_tvar("a".into(), Kind::Star);
    let list_type = mk_list(tv.clone());
    class_env
        .add_inst(
            vec![Pred::new("Eq".into(), tv.clone())],
            Pred::new("Eq".into(), list_type.clone()),
        )
        .unwrap();
    class_env
        .add_inst(
            vec![Pred::new("Ord".into(), tv.clone())],
            Pred::new("Ord".into(), list_type.clone()),
        )
        .unwrap();
    class_env
        .add_inst(
            vec![Pred::new("Show".into(), tv.clone())],
            Pred::new("Show".into(), list_type.clone()),
        )
        .unwrap();
    class_env
        .add_inst(
            vec![Pred::new("Read".into(), tv.clone())],
            Pred::new("Read".into(), list_type.clone()),
        )
        .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_instances() {
        let mut env = ClassEnv::new(vec![]);
        haskell(&mut env);

        // overlapped instance
        assert!(env
            .add_inst(Vec::new(), Pred::new("Enum".into(), T_INT.clone()))
            .is_err());

        // no class
        assert!(env
            .add_inst(Vec::new(), Pred::new("NotDefined".into(), T_INT.clone()))
            .is_err());
    }
}
