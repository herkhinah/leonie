use chumsky::prelude::Simple;

use leonie::{
    infer,
    metas::MetaCxt,
    parser::{parse, Token},
    Cxt,
};

fn main() -> Result<(), Vec<Simple<Token>>> {
    let str = r#"
    let id : (A : U) -> A -> A := λ A. (λ a. a)
    let id2 : (A : U) -> A -> A := λ A. (λ a. id _ a)
    U
    "#;

    if let Some(raw) = parse(str)? {
        let mut metas = MetaCxt::default();
        let mut cxt = Cxt::default();

        match infer(&mut metas, &mut cxt, raw) {
            Ok((norm, ty)) => println!("success: {norm:?} {ty:?}"),
            Err(err) => println!("error: {:?} {err:#?}", cxt.pos()),
        }
    }

    Ok(())
}
