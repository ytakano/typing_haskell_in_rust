use std::borrow::Cow;

pub mod ast;
pub mod error;
pub mod predicate;
pub mod prelude;
pub mod type_class;
pub mod type_infer;
pub mod types;

/// `CowStr` is a type alias for a clone-on-write string with a 'static lifetime.
/// This type can be useful when working with string data that may or may not
/// need to be cloned. In many cases, a `CowStr` will simply be a borrowed
/// reference to an existing string (`&'static str`). However, if the string data
/// needs to be modified, it can be cloned into a new, owned `String` dynamically.
type CowStr = Cow<'static, str>;

/// `CowVec<T>` is a type alias for a clone-on-write vector with elements of type `T`
/// and a 'static lifetime. Like `CowStr`, this type is useful for handling situations
/// where the data may or may not need to be cloned. `CowVec<T>` can either borrow a
/// slice of data (`&'static [T]`) or, if mutation is required, clone the data into a
/// new, owned `Vec<T>` dynamically.
type CowVec<T> = Cow<'static, [T]>;
