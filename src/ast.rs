use crate::type_infer::{assump::Assump, scheme::Scheme};

#[derive(Debug, Clone)]
pub enum Literal {
    Int(num::BigInt),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
}

#[derive(Debug, Clone)]
pub enum Pat {
    Var(String),                           // variable
    Wildcard,                              // wildcard
    As { id: String, pat: Box<Pat> },      // as pattern
    Lit(Literal),                          // literal
    Con { assump: Assump, pat: Vec<Pat> }, // type constructor
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var(String),               // variable
    Lit(Literal),              // literal
    Const(Assump),             // constructor
    Ap(Box<Expr>, Box<Expr>),  // application
    Let(BindGroup, Box<Expr>), // let
}

/// Function bindings.
/// An `Alt` specifies the left and right hand sides of a function definition.
/// With a more complete syntax for `Expr`, values of type `Alt` might also be used
/// in the representation of lambda and case expressions.
#[derive(Debug, Clone)]
pub struct Alt {
    pub pats: Vec<Pat>,
    pub expr: Expr,
}

/// Explicitly Typed Bindings.
#[derive(Debug, Clone)]
pub struct Expl {
    pub id: String,
    pub scheme: Scheme,
    pub alt: Vec<Alt>,
}

/// Implicitly Typed Bindings.
#[derive(Debug, Clone)]
pub struct Impl {
    pub id: String,
    pub alt: Vec<Alt>,
}

#[derive(Debug, Clone)]
pub struct BindGroup {
    pub explicit: Vec<Expl>,
    pub implicit: Vec<Impl>,
}
