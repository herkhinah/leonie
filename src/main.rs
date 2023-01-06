#![feature(arc_unwrap_or_clone)]

use ariadne::{Label, Report, ReportKind, Source};
use chumsky::zero_copy::{prelude::Rich, Parser};
use const_format::concatcp;
use leonie::{lexer::lex, parser::raw_local_scope};

const TEST0: &str = r#"
let id : (A : _) -> A -> A := λ A x. x
let List : U -> U := λ A. (L : _) -> (A -> L -> L) -> L -> L
let nil : (A : _) -> List A := λ A L cons nil. nil
let cons : (A : _) -> A -> List A -> List A := λ A x xs L cons nil. cons x (xs _ cons nil)
let Bool : U := (B : _) -> B -> B -> B
let true : Bool := λ B t f. t
let false : Bool := λ B t f. f
let not : Bool -> Bool := λ b B t f. b B f t
let list1 : List Bool := cons _ (id _ true) (nil _)
let Eq : (A : _) -> A -> A -> U := λ A x y. (P : A -> U) -> P x -> P y
let refl : (A : _) -> (x : A) -> Eq A x x := λ A x P px. px
let list1 : List Bool := cons _ true (cons _ false (nil _))
let Nat  : U := (N : U) -> (N -> N) -> N -> N
let five : Nat := λ N s z. s (s (s (s (s z))))
let add  : Nat -> Nat -> Nat := λ a b N s z. a N s (b N s z)
let mul  : Nat -> Nat -> Nat := λ a b N s z. a N (b N s) z
let ten      : Nat := add five five
let hundred  : Nat := mul ten ten
let thousand : Nat := mul ten hundred
let eqTest : Eq _ hundred hundred := refl _ _
"#;

fn main() -> Result<(), ()> {
    let bump = bumpalo::Bump::new();

    let (res, errs_lex) = lex::<Rich<str>>(concatcp!(TEST0, "id"));

    let parser = raw_local_scope(&bump);

    if let Some(res) = &res {
        let (res, errs_parse) = parser.parse(res);
        dbg!(res, errs_parse);
    }

    Ok(())
}
