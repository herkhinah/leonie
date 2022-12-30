#![feature(arc_unwrap_or_clone)]

use leonie::{parser::parse, Cxt};

const PRUNE_INTERSECTION: &str = r#"
let Eq : (A : U) -> A -> A -> U := λ A x y. (P : A -> U) -> P x -> P y
let refl : (A : U) -> (x : A) -> Eq A x x := λ _ _ . λ _ px. px
let the : (A : U) -> A -> A := λ _ x. x
let m : U -> U -> U -> U := _
let test : _ := λ a b c. the (Eq _ (m a b c) (m c b a)) (refl _ _)
U
"#;

#[test]
fn prune_intersection() -> Result<(), ()> {
    let raw = parse(PRUNE_INTERSECTION)
        .map_err(|err| {
            println!("{err:#?}");
        })
        .unwrap()
        .unwrap();
    let mut cxt = Cxt::default();

    cxt.infer(raw).map(|_| ()).map_err(|err| {
        println!("{}\n{:#?}", err.backtrace, err.kind);
        ()
    })
}

const PRUNE_NON_LINEAR: &str = r#"
let Eq : (A : U) -> A -> A -> U := λ A x y. (P : A -> U) -> P x -> P y
let refl : (A : U) -> (x : A) -> Eq A x x := λ _ _ . λ _ px. px
let the : (A : U) -> A -> A := λ _ x. x
let m : (A : U) -> (B : U) -> U -> U -> U := _
let test : _ := λ a b. the (Eq _ (m a a) (λ x y. y)) (refl _ _)
U
"#;

#[test]
fn prune_non_linear() -> Result<(), ()> {
    let raw = parse(PRUNE_NON_LINEAR)
        .map_err(|err| {
            println!("{err:#?}");
        })
        .unwrap()
        .unwrap();
    let mut cxt = Cxt::default();

    cxt.infer(raw).map(|_| ()).map_err(|err| {
        println!("{}\n{:#?}", err.backtrace, err.kind);
        ()
    })
}

const PRUNE0: &str = r#"
let pr0 : _ -> _ -> _  := λ f x. f x
U
"#;

const PRUNE1: &str = r#"
let pr1 : _ := λ f x y. f x y
U
"#;

const PRUNE2: &str = r#"
let pr2 : _ := λ f. f U
U
"#;

#[test]
fn prune0() -> Result<(), ()> {
    let raw = parse(PRUNE0)
        .map_err(|err| {
            println!("{err:#?}");
        })
        .unwrap()
        .unwrap();
    let mut cxt = Cxt::default();

    cxt.infer(raw).map(|_| ()).map_err(|err| {
        println!("{}\n{:#?}", err.backtrace, err.kind);
        ()
    })
}

#[test]
fn prune1() -> Result<(), ()> {
    let raw = parse(PRUNE1)
        .map_err(|err| {
            println!("{err:#?}");
        })
        .unwrap()
        .unwrap();
    let mut cxt = Cxt::default();

    cxt.infer(raw).map(|_| ()).map_err(|err| {
        println!("{}\n{:#?}", err.backtrace, err.kind);
        ()
    })
}

#[test]
fn prune2() -> Result<(), ()> {
    let raw = parse(PRUNE2)
        .map_err(|err| {
            println!("{err:#?}");
        })
        .unwrap()
        .unwrap();
    let mut cxt = Cxt::default();

    cxt.infer(raw).map(|_| ()).map_err(|err| {
        println!("{}\n{:#?}", err.backtrace, err.kind);
        ()
    })
}
