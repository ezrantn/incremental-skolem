use incremental_skolem::smt2::Interpreter;
use incremental_skolem::z3_bridge::default_context;
use std::env;
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <file.smt2>", args[0]);
        return ExitCode::FAILURE;
    }
    let src = match fs::read_to_string(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error reading {}: {}", args[1], e);
            return ExitCode::FAILURE;
        }
    };

    let ctx = default_context();
    let mut interp = Interpreter::new(&ctx);
    if let Err(e) = interp.run_source(&src) {
        eprintln!("error: {:?}", e);
        return ExitCode::FAILURE;
    }

    for r in &interp.results {
        println!("{:?}", r);
    }
    for d in &interp.diagnostics {
        eprintln!("note: {}", d);
    }
    let (fresh, reuse, size) = interp.solver_stats();
    eprintln!(
        "skolem stats: {} fresh generations, {} cache hits, {} entries currently cached",
        fresh,
        reuse,
        size
    );

    ExitCode::SUCCESS
}
