use std::borrow::Cow;

pub mod ast;
pub mod error;
pub mod predicate;
pub mod prelude;
pub mod type_class;
pub mod type_infer;
pub mod types;

type CowStr = Cow<'static, str>;
type CowVec<T> = Cow<'static, [T]>;
