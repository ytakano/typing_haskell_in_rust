use once_cell::sync::Lazy;

use std::{borrow::Cow, collections::BTreeSet};

use crate::{error::DynError, CowStr, CowVec};

/// A substitution type, which maps type variables (`Tyvar`) to types (`Type`).
pub(crate) type Subst = CowVec<(Tyvar, Type)>;

/// Returns an empty substitution, which is represented by an empty vector.
pub(crate) fn null_subst() -> Subst {
    Cow::Owned(vec![])
}

/// Represents the kind of a type constructor in Haskell's type system.
/// Kinds play a similar role for type constructors as types do for values.
///
/// # Variants
///
/// - `Star`: Represents the set of all simple type expressions (i.e., nullary type expressions),
///   such as `Int` and `Char → Bool`.
///
/// - `Kfun(Box<Kind>, Box<Kind>)`: Represents type constructors that take an argument type of
///   one kind and return a result type of another kind. For instance, the standard list,
///   `Maybe`, and `IO` constructors all have kind `Star → Star` in Haskell.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub enum Kind {
    Star,
    Kfun(Box<Kind>, Box<Kind>),
}

/// A `Tyvar` represents a type variable in the type system.
/// It consists of an identifier and a kind.
/// The identifier is a unique name for the variable,
/// and the kind classifies the variable into a category.
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub struct Tyvar {
    pub id: CowStr,
    pub kind: Kind,
}

/// A `Tycon` represents a type constructor in the type system.
/// It consists of an identifier and a kind.
/// The identifier is a unique name for the constructor,
/// and the kind represents the "type" of the constructor.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Tycon {
    pub id: CowStr,
    pub kind: Kind,
}

/// The `Type` enum represents the different kinds of types in the type system.
/// - `TVar(Tyvar)`: A type variable.
/// - `TCon(Tycon)`: A type constructor.
/// - `TAp(Box<Type>, Box<Type>)`: An application of one type to another.
/// - `TGen(usize)`: A generic or quantified type variable, used in the representation of type schemes.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Type {
    TVar(Tyvar),               // type variable
    TCon(Tycon),               // type constructor
    TAp(Box<Type>, Box<Type>), // type application
    TGen(usize),               // generic or quantified type variables
}

/// A macro to easily define standard primitive datatypes as type constants.
/// Each primitive datatype has `Star` kind, and is represented as a `Type::TCon` variant.
macro_rules! def_type {
    ( $id:ident, $ty:expr) => {
        /// A Lazy static variable representing the `$ty` type.
        pub static $id: Lazy<Type> = Lazy::new(|| {
            Type::TCon(Tycon {
                id: $ty.into(),
                kind: Kind::Star,
            })
        });
    };
}

def_type!(T_UNIT, "Unit"); // The `Unit` type.
def_type!(T_CHAR, "Char"); // The `Char` type.
def_type!(T_BOOL, "Bool"); // The `Bool` type.
def_type!(T_INT, "Int"); // The `Int` type.
def_type!(T_INTEGER, "Integer"); // The `Integer` type.
def_type!(T_FOLAT, "Float"); // The `Float` type.
def_type!(T_DOUBLE, "Double"); // The `Double` type.

/// A Lazy static variable representing the list type.
/// The list type is represented as a type constructor with a kind of `Star -> Star`.
pub static T_LIST: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "[]".into(),
        kind: Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star)),
    })
});

/// A Lazy static variable representing the function type.
/// The function type is represented as a type constructor with a kind of `Star -> Star -> Star`.
pub static T_ARROW: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(->)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

/// A Lazy static variable representing the 2-tuple type.
/// The 2-tuple type is represented as a type constructor with a kind of `Star -> Star -> Star`.
pub static T_TUPLE2: Lazy<Type> = Lazy::new(|| {
    Type::TCon(Tycon {
        id: "(,)".into(),
        kind: Kind::Kfun(
            Box::new(Kind::Star),
            Box::new(Kind::Kfun(Box::new(Kind::Star), Box::new(Kind::Star))),
        ),
    })
});

/// Constructs a function type by taking two types as arguments and
/// returns a type application of the function arrow `T_ARROW`.
///
/// # Arguments
///
/// * `a` - The type of the argument to the function.
/// * `b` - The return type of the function.
pub fn mk_fn(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(Type::TAp(Box::new(T_ARROW.clone()), Box::new(a))),
        Box::new(b),
    )
}

/// Constructs a list type by taking a type as an argument and
/// returns a type application of the list type constructor `T_LIST`.
///
/// # Arguments
///
/// * `a` - The type of the elements in the list.
pub fn mk_list(a: Type) -> Type {
    Type::TAp(Box::new(T_LIST.clone()), Box::new(a))
}

/// Constructs a pair type by taking two types as arguments and
/// returns a type application of the tuple type constructor `T_TUPLE2`.
///
/// # Arguments
///
/// * `a` - The first element of the pair.
/// * `b` - The second element of the pair.
pub fn mk_pair(a: Type, b: Type) -> Type {
    Type::TAp(
        Box::new(Type::TAp(Box::new(T_TUPLE2.clone()), Box::new(a))),
        Box::new(b),
    )
}

/// Constructs a type variable by taking an identifier and a kind as arguments.
///
/// # Arguments
///
/// * `id` - The identifier for the type variable.
/// * `kind` - The kind of the type variable.
pub fn mk_tvar(id: CowStr, kind: Kind) -> Type {
    Type::TVar(Tyvar { id, kind })
}

/// The `HasKind` trait represents types that have a `Kind`.
/// It provides a method `kind` which returns the `Kind` of the implementing type.
pub(crate) trait HasKind {
    fn kind(&self) -> Kind;
}

/// Implementation of the `HasKind` trait for `Tyvar`.
/// A `Tyvar` has a `Kind` stored in it, so it simply returns a clone of that `Kind`.
impl HasKind for Tyvar {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

/// Implementation of the `HasKind` trait for `Tycon`.
/// Similar to `Tyvar`, a `Tycon` has a `Kind` stored in it, so it simply returns a clone of that `Kind`.
impl HasKind for Tycon {
    fn kind(&self) -> Kind {
        self.kind.clone()
    }
}

/// Implementation of the `HasKind` trait for `Type`.
/// The `Kind` of a `Type` depends on its variant. For `TCon` and `TVar`, it simply returns
/// the `Kind` of the contained `Tycon` or `Tyvar`. For `TAp`, it recursively calls `kind` on the first type
/// assuming the type is well-formed, the first type `t` must have a kind `k′ → k`,
/// where `k′` is the kind of the second type `t′` and `k` is the kind of the whole application.
/// `TGen` variant is not supposed to be reachable.
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

/// A trait for types that can have substitutions applied to them and
/// that can return the set of type variables they contain.
pub(crate) trait Types {
    /// Applies a given substitution `subst` to `self` and returns the result.
    fn apply(&self, subst: Subst) -> Self;

    /// Returns the set of type variables in `self`.
    fn tv(&self) -> BTreeSet<Tyvar>;
}

impl Types for Type {
    /// Applies a given substitution `subst` to this type. If the type is a type
    /// variable that appears in `subst`, it is replaced by the corresponding
    /// type. Otherwise, the type is left unchanged.
    fn apply(&self, subst: Subst) -> Self {
        match self {
            Type::TVar(u) => subst
                .iter()
                .find(|(u_, _)| u == u_)
                .map(|(_, t)| t.clone())
                .unwrap_or(Type::TVar(u.clone())),
            Type::TAp(l, r) => {
                Type::TAp(Box::new(l.apply(subst.clone())), Box::new(r.apply(subst)))
            }
            _ => self.clone(),
        }
    }

    /// Returns the set of type variables in this type. For type variables, this
    /// is a set containing the type variable itself. For application types, this
    /// is the union of the sets of type variables in the types being applied.
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

/// Implements the `Types` trait for a vector of elements of a type that also
/// implements the `Types` trait. This allows substitutions to be applied to
/// each element in the vector and the set of type variables in the vector to
/// be computed.
impl<T: Types + Clone> Types for CowVec<T>
where
    [T]: ToOwned,
{
    /// Applies a given substitution to each element in this vector.
    /// The resulting vector consists of the results of applying the
    /// substitution to each individual element.
    fn apply(&self, subst: Subst) -> Self {
        self.iter().map(|t| t.apply(subst.clone())).collect()
    }

    /// Computes the set of type variables in this vector.
    /// The resulting set is the union of the sets of type variables in each
    /// individual element.
    fn tv(&self) -> BTreeSet<Tyvar> {
        self.iter().flat_map(|t| t.tv()).collect()
    }
}

/// Binds a type variable `u` to a type `t`, resulting in a substitution.
///
/// This function takes a type variable and a type, and attempts to create a substitution
/// from `u` to `t`. However, before the substitution is created, several checks are performed
/// to ensure its validity:
///
/// - If `t` is a type variable that is the same as `u`, the function will return an empty substitution.
/// - An occurs check is performed to ensure that `u` does not appear within `t` to avoid infinite types.
/// - A kind check is performed to ensure that `u` and `t` have the same kind, preserving kind correctness.
///
/// # Arguments
///
/// * `u` - A type variable to be substituted.
/// * `t` - A type that `u` should be substituted to.
///
/// # Returns
///
/// If the binding is successful, a `Subst` is returned where `Subst` is the substitution from `u` to `t`.
/// If the binding fails due to an occurs check or kind check, an error is returned with a description of the issue.
fn var_bind(u: &Tyvar, t: &Type) -> Result<Subst, DynError> {
    // t == Type::TVar(u)
    if let Type::TVar(u_) = t {
        if u == u_ {
            return Ok(null_subst());
        }
    }

    if t.tv().contains(u) {
        return Err("occurs check fails".into());
    }

    // ensure that the substitution is kind-preserving
    if u.kind() != t.kind() {
        return Err("kinds do not match".into());
    }

    Ok(vec![(u.clone(), t.clone())].into())
}

/// Compute the most general unifier (mgu) of two given types.
///
/// The function follows the algorithm described by J. A. Robinson (1965) and attempts to
/// find the smallest substitution `s` that when applied to both input types `t1` and `t2`,
/// makes them equal. In other words, it finds `s` such that `apply(s, t1) == apply(s, t2)`.
///
/// The function will return an error if the input types cannot be unified.
/// For instance, if they are different type constants, or if a occurs-check or a kind-check fails.
///
/// # Arguments
///
/// * `t1` - A type to be unified.
/// * `t2` - Another type to be unified.
///
/// # Returns
///
/// If unification is successful, a `Subst` is returned where `Subst` is the most general unifier.
/// If unification fails, an error is returned with a description of the issue.
pub(crate) fn mgu(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
    match (t1, t2) {
        (Type::TAp(l1, r1), Type::TAp(l2, r2)) => {
            let s1 = mgu(l1, l2)?;
            let s2 = mgu(&r1.apply(s1.clone()), &r2.apply(s1.clone()))?;
            Ok(compose(s2, s1))
        }
        (Type::TVar(u), t) => var_bind(u, t),
        (t, Type::TVar(u)) => var_bind(u, t),
        (Type::TCon(tc1), Type::TCon(tc2)) if tc1 == tc2 => Ok(null_subst()),
        _ => Err("types do not unify".into()),
    }
}

/// Composes two substitutions `s1` and `s2`.
///
/// The composition of substitutions `s1` and `s2` represented as `s1@@s2` is
/// computed such that `apply(s1@@s2)` is equivalent to `apply s1 . apply s2`.
/// The operation is performed in two steps: first, for each `(u, t)` pair in `s2`,
/// `apply s1` is called on `t`, and then `s1` is chained onto the result.
/// This means that the bindings in `s1` take precedence over the bindings in `s2`
/// for any common variables.
///
/// # Arguments
///
/// * `s1` - A `Subst` (substitution) instance
/// * `s2` - Another `Subst` instance
///
/// # Returns
///
/// * A new `Subst` instance that represents the composition of `s1` and `s2`.
pub(crate) fn compose(s1: Subst, s2: Subst) -> Subst {
    s2.to_owned()
        .iter()
        .map(|(u, t)| (u.clone(), t.apply(s1.clone())))
        .chain(s1.iter().cloned())
        .collect()
}

/// Merges two substitutions `s1` and `s2`.
///
/// The merge operation attempts to combine two substitutions, checking for conflicts
/// between the substitutions. It returns a `Result` containing either the merged
/// substitution if successful, or an error if there is a conflict.
///
/// A conflict occurs when there is a type variable that is common to both `s1` and `s2`
/// but is associated with different types in each substitution.
///
/// If no conflicts are found, the function returns the combined substitution.
/// If a conflict is detected, the function returns an error with a message indicating
/// the conflict.
///
/// # Arguments
///
/// * `s1` - A mutable `Subst` (substitution) instance.
/// * `s2` - Another `Subst` instance.
///
/// # Returns
///
/// * `Ok(Subst)` - A new `Subst` instance that represents the merge of `s1` and `s2`
///                 if there are no conflicts.
/// * `Err(DynError)` - An error indicating a conflict between `s1` and `s2` if any conflicts
///                     are detected.
///
/// # Errors
///
/// This function will return an error if there is a conflict between `s1` and `s2` with respect to any common type variable.
fn merge(mut s1: Subst, s2: Subst) -> Result<Subst, DynError> {
    fn agree(s1: Subst, s2: Subst) -> bool {
        let set1: BTreeSet<_> = s1.iter().map(|(t, _)| t).collect();
        let set2: BTreeSet<_> = s2.iter().map(|(t, _)| t).collect();
        set1.intersection(&set2).all(|t| {
            Type::TVar((*t).clone()).apply(s1.clone()) == Type::TVar((*t).clone()).apply(s2.clone())
        })
    }

    if agree(s1.clone(), s2.clone()) {
        s1.to_mut().extend(s2.iter().cloned());
        Ok(s1)
    } else {
        Err("merge: type variable conflict".into())
    }
}

/// Performs one-way matching between two types.
///
/// This function takes two types and attempts to find a substitution `s` such that
/// `apply s t1 = t2`. This operation is often described as one-way matching,
/// because the substitution is applied only to `t1`.
///
/// The matching process follows the structure of the types:
///
/// - If both types are application types, it recursively matches both halves.
/// - If `t1` is a type variable and its kind matches with `t2`, it creates a substitution from `t1` to `t2`.
/// - If both types are the same type constructor, it returns a null substitution.
/// - In all other cases, matching fails and it returns an error.
///
/// # Arguments
///
/// * `t1` - The first type for matching.
/// * `t2` - The second type for matching.
///
/// # Returns
///
/// If the matching is successful, a `Subst` is returned where `Subst` is the substitution that makes `t1` match `t2`.
/// If the matching fails, an error is returned with a description of the issue.
pub(crate) fn type_match(t1: &Type, t2: &Type) -> Result<Subst, DynError> {
    match (t1, t2) {
        (Type::TAp(l1, r1), Type::TAp(l2, r2)) => {
            let s1 = type_match(l1, l2)?;
            let s2 = type_match(r1, r2)?;
            merge(s1, s2)
        }
        (Type::TVar(u), t) if u.kind() == t.kind() => Ok(vec![(u.clone(), t.clone())].into()),
        (Type::TCon(tc1), Type::TCon(tc2)) if tc1 == tc2 => Ok(null_subst()),
        _ => Err("types do not match".into()),
    }
}
