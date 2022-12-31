pub use std::backtrace::Backtrace;

use crate::{
    metas::MetaVar,
    value::{Spine, Value},
};

#[derive(Debug)]
pub struct Error {
    pub backtrace: Backtrace,
    pub kind: ErrorKind,
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    Unbound,
    Unify,
    MetaOccurs(MetaVar, Value),
    MetaScope(Value),
    MetaSpine(Spine, Spine),
    MetaInvert,
    MetaUnify(Value, Value),
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
