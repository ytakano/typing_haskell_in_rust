use crate::type_infer::Assump;

pub enum Literal {
    Int(num::BigInt),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
}

pub enum Pat {
    Var(String),                           // variable
    Wildcard,                              // wildcard
    As { id: String, pat: Box<Pat> },      // as pattern
    Lit(Literal),                          // literal
    Con { assump: Assump, pat: Vec<Pat> }, // type constructor
}

pub enum Expr {
    Var(String),
    Lit(Literal),
    Ap(Box<Expr>, Box<Expr>),
    // BindGroup
}

/// Function bindings.
/// An `Alt` specifies the left and right hand sides of a function definition.
/// With a more complete syntax for `Expr`, values of type `Alt` might also be used
/// in the representation of lambda and case expressions.
pub struct Alt {
    pats: Vec<Pat>,
    expr: Expr,
}
