use std::io::Read;

use leonie::{parser::parse, term::TPrettyPrinter, Cxt};

fn main() -> Result<(), ()> {
    let mut input = String::new();
    let stdin = std::io::stdin();
    let mut handle = stdin.lock();
    if handle.read_to_string(&mut input).is_err() {
        println!("failed to read input");
    }

    if let Ok(Some(raw)) = parse(&input) {
        let mut cxt = Cxt::default();

        if let Ok((term, ty)) = cxt.infer(raw) {
            let nf_term = cxt.normal_form(term);
            let lvl = cxt.lvl();
            let nf_type = ty.quote(&mut cxt.metas, lvl);

            println!(
                "{}\n  :\n{}",
                TPrettyPrinter(&Cxt::default(), &nf_term),
                TPrettyPrinter(&Cxt::default(), &nf_type)
            );

            Ok(())
        } else {
            println!("failed to typecheck input");

            Err(())
        }
    } else {
        println!("failed to parse input");
        Err(())
    }
}
