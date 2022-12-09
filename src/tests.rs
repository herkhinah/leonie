use crate::{
    env::Env, infer, metas::MetaCxt, normal_form, parser::parse, term::TPrettyPrinter, Cxt,
};

#[test]
fn normal_forms() -> Result<(), ()> {
    let test_cases = [
        (
            concat!("let id : (A : _) -> A -> A := λ A x. x\n", "id"),
            "λ A x. x",
            "(A : U) → A → A",
        ),
        (
            concat!(
                "let id : (A : U) -> A -> A := λ A a. a\n",
                "let id2 : (A : U) -> A -> A := λ A a. id _ a\n",
                "id2\n"
            ),
            "λ A a. a",
            "(A : U) → A → A",
        ),
    ];

    for (input, expected_nf_term, expected_nf_type) in test_cases {
        let raw = parse(input).map_err(|_| ())?.unwrap();
        let (mut metas, mut cxt) = (MetaCxt::default(), Cxt::default());

        let (term, ty) = infer(&mut metas, &mut cxt, raw).map_err(|_| ())?;

        let nf_term = normal_form(&mut Env::default(), &mut metas, term);
        assert_eq!(
            format!("{}", TPrettyPrinter(&Cxt::default(), &nf_term)),
            expected_nf_term
        );

        let nf_type = ty.quote(&mut metas, cxt.lvl());
        assert_eq!(
            format!("{}", TPrettyPrinter(&cxt, &nf_type)),
            expected_nf_type
        );
    }

    Ok(())
}
