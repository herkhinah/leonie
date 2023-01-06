pub use std::backtrace::Backtrace;

use crate::{
    metas::MetaVar,
    value::{Spine, Value},
};

#[derive(Debug)]
pub struct Error<'src> {
    pub backtrace: Backtrace,
    pub kind: ErrorKind<'src>,
}

#[derive(Debug, Clone)]
pub enum ErrorKind<'src> {
    Unbound,
    Unify,
    MetaOccurs(MetaVar, Value<'src>),
    MetaScope(Value<'src>),
    MetaSpine(Spine<'src>, Spine<'src>),
    MetaInvert,
    MetaUnify(Value<'src>, Value<'src>),
    InferUnbound(),
}

macro_rules! error {
    ($error_kind:expr) => {
        Error {
            backtrace: std::backtrace::Backtrace::capture(),
            kind: $error_kind,
        }
    };
}
