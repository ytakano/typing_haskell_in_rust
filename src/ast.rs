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
