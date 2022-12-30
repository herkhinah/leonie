#![feature(arc_unwrap_or_clone)]

use std::rc::Rc;

use const_format::concatcp;

use leonie::{parser::parse, term::TPrettyPrinter, Cxt};

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

#[test]
fn normal_forms() -> Result<(), &'static str> {
    let test_cases = [
        (
            concat!(
                "let id : (A : _) -> A -> _ := λ A a. a\n",
                "let id2 : (A : _) -> _ -> A := λ A a. id _ a\n",
                "id2\n"
            ),
            "λ A a. a",
            "(A : U) → A → A",
        ),
        (
            concatcp!(TEST0, "id\n"),
            "λ A x. x",
            "(A : U) → A → A",
        ),
        (
            concatcp!(TEST0, "List"),
            "λ A. (L : U) → (A → L → L) → L → L",
            "U → U",
        ),
        (
            concatcp!(TEST0, "nil"),
            "λ A L cons nil. nil",
            "(A : U) → (L : U) → (A → L → L) → L → L",
        ),
        (
            concatcp!(TEST0, "cons"),
            "λ A x xs L cons nil. cons x (xs L cons nil)",
            "(A : U) → A → ((L : U) → (A → L → L) → L → L) → (L : U) → (A → L → L) → L → L",
        ),
        (
            concatcp!(TEST0, "Bool"),
            "(B : U) → B → B → B",
            "U",
        ),
        (
            concatcp!(TEST0, "true"),
            "λ B t f. t",
            "(B : U) → B → B → B",
        ),
        (
            concatcp!(TEST0, "false"),
            "λ B t f. f",
            "(B : U) → B → B → B",
        ),
        (
            concatcp!(TEST0, "not"),
            "λ b B t f. b B f t",
            "((B : U) → B → B → B) → (B : U) → B → B → B",
        ),
        (
            concatcp!(TEST0, "list1"),
            "λ L cons nil. cons (λ B t f. t) (cons (λ B t f. f) nil)",
            "(L : U) → (((B : U) → B → B → B) → L → L) → L → L",
        ),
        (
            concatcp!(TEST0, "Eq"),
            "λ A x y. (P : A → U) → P x → P y",
            "(A : U) → A → A → U",
        ),
        (
            concatcp!(TEST0, "refl"),
            "λ A x P px. px",
            "(A : U) → (x : A) → (P : A → U) → P x → P x",
        ),
        (
            concatcp!(TEST0, "list1"),
            "λ L cons nil. cons (λ B t f. t) (cons (λ B t f. f) nil)",
            "(L : U) → (((B : U) → B → B → B) → L → L) → L → L",
        ),
        (
            concatcp!(TEST0, "Nat"),
            "(N : U) → (N → N) → N → N",
            "U",
        ),
        (
            concatcp!(TEST0, "five"),
            "λ N s z. s (s (s (s (s z))))",
            "(N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "add"),
            "λ a b N s z. a N s (b N s z)",
            "((N : U) → (N → N) → N → N) → ((N : U) → (N → N) → N → N) → (N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "mul"),
            "λ a b N s z. a N (b N s) z",
            "((N : U) → (N → N) → N → N) → ((N : U) → (N → N) → N → N) → (N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "ten"),
            "λ N s z. s (s (s (s (s (s (s (s (s (s z)))))))))",
            "(N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "hundred"),
            "λ N s z. s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
            "(N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "thousand"),
            "λ N s z. s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
            "(N : U) → (N → N) → N → N",
        ),
        (
            concatcp!(TEST0, "eqTest"),
            "λ P px. px",
            "(P : ((N : U) → (N → N) → N → N) → U) → P (λ N s z. s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) → P (λ N s z. s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
        ),
    ];

    for (input, expected_nf_term, expected_nf_type) in test_cases {
        let raw = parse(input)
            .map_err(|err| {
                println!("{err:#?}");
            })
            .unwrap()
            .unwrap();
        let mut cxt = Cxt::default();

        let (term, ty) = cxt.infer(raw).map_err(|err| {
            println!("{}\n{:#?}", err.backtrace, err.kind);
            input
        })?;

        let nf_term = format!(
            "{}",
            TPrettyPrinter(&Cxt::default(), &cxt.normal_form(term))
        );

        assert_eq!(nf_term, expected_nf_term);
        let lvl = cxt.lvl();

        let nf_type = format!(
            "{}",
            TPrettyPrinter(
                &Cxt::default(),
                &Rc::unwrap_or_clone(ty).quote(&mut cxt.metas, lvl)
            )
        );

        assert_eq!(nf_type, expected_nf_type);
    }

    Ok(())
}
