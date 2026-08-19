//! Regression test for a real bug found while building the SMT-LIB2
//! front end: variable numbering that persists across separate `assert`
//! commands breaks structural equality (and therefore Skolem-cache reuse)
//! for textually-identical formulas asserted more than once. See the doc
//! comment on `Interpreter::run_command`'s "assert" arm in smt2.rs.

use incremental_skolem::smt2::Interpreter;
use incremental_skolem::z3_bridge::default_context;
use z3::SatResult;

#[test]
fn identical_assert_text_across_push_pop_reuses_skolem_symbol() {
    let src =
        r#"
        (declare-fun Knows (U U) Bool)
        (push 1)
        (assert (forall ((x U)) (exists ((y U)) (Knows x y))))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (forall ((x U)) (exists ((y U)) (Knows x y))))
        (check-sat)
    "#;

    let ctx = default_context();
    let mut interp = Interpreter::new(&ctx);
    interp.run_source(src).expect("script should run without errors");

    assert_eq!(interp.results, vec![SatResult::Sat, SatResult::Sat]);

    let (fresh, reuse, _size) = interp.solver_stats();
    assert_eq!(fresh, 1, "identical formula text should only mint one Skolem symbol");
    assert_eq!(reuse, 1, "the second identical assert should hit the cache");
}

/// A different variable NAME but the same shape should also reuse -- this
/// is a slightly stronger property than the exact-text case above (parser
/// output alpha-consistency, not just text-identity), and is worth
/// tracking as a known limitation if it ever fails: the current fix
/// (per-assert-local variable numbering starting at 0) only guarantees
/// reuse for formulas whose bound variables are introduced in the same
/// ORDER, not full alpha-equivalence in general.
#[test]
fn same_shape_different_variable_names_reuses_skolem_symbol() {
    let src =
        r#"
        (declare-fun Knows (U U) Bool)
        (push 1)
        (assert (forall ((x U)) (exists ((y U)) (Knows x y))))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (forall ((a U)) (exists ((b U)) (Knows a b))))
        (check-sat)
    "#;

    let ctx = default_context();
    let mut interp = Interpreter::new(&ctx);
    interp.run_source(src).expect("script should run without errors");

    let (fresh, reuse, _size) = interp.solver_stats();
    assert_eq!(fresh, 1, "same-shaped formula with different variable names should still reuse");
    assert_eq!(reuse, 1);
}

/// Sanity check the full demo file from examples/ still behaves as
/// documented: two SAT results from the reused-formula pair, one UNSAT
/// from the unrelated contradiction, and correct reuse stats.
#[test]
fn full_demo_script_end_to_end() {
    let src = std::fs
        ::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/incremental_demo.smt2"))
        .expect("demo file should exist");

    let ctx = default_context();
    let mut interp = Interpreter::new(&ctx);
    interp.run_source(&src).expect("demo script should run without errors");

    assert_eq!(interp.results, vec![SatResult::Sat, SatResult::Sat, SatResult::Unsat]);
    let (fresh, reuse, _size) = interp.solver_stats();
    assert_eq!(fresh, 1);
    assert_eq!(reuse, 1);
}
