pub mod term;
pub mod skolem_table;
pub mod skolemize;
pub mod z3_bridge;
pub mod sexpr;
pub mod nnf;
pub mod smt2;

pub use skolem_table::SkolemTable;
pub use skolemize::Skolemizer;
pub use term::{ Formula, Interner, Term };

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ mk_exists, mk_forall, mk_pred };
    use std::rc::Rc;

    /// Builds: forall x. exists y. P(x, y)
    /// Skolemizing should produce: forall x. P(x, f1(x))
    fn build_simple_formula(interner: &mut Interner) -> Rc<Formula> {
        let x: u32 = 0;
        let y: u32 = 1;
        let p = mk_pred(interner, "P", vec![Rc::new(Term::Var(x)), Rc::new(Term::Var(y))], false);
        let exists_y = mk_exists(interner, y, p);
        mk_forall(interner, x, exists_y)
    }

    #[test]
    fn basic_skolemization_produces_dependent_symbol() {
        let mut interner = Interner::new();
        let mut table = SkolemTable::new("sk");
        let formula = build_simple_formula(&mut interner);

        let mut skolemizer = Skolemizer::new(&mut interner, &mut table);
        let result = skolemizer.skolemize(&formula, &[]);

        // Expect: ForAll(x, Pred("P", [Var(x), Func("sk1", [Var(x)])]))
        match &*result {
            Formula::ForAll(x, body) => {
                match &**body {
                    Formula::Pred { name, args, .. } => {
                        assert_eq!(name, "P");
                        assert_eq!(args.len(), 2);
                        match &*args[1] {
                            Term::Func(sym, fargs) => {
                                assert_eq!(sym, "sk1");
                                assert_eq!(fargs.len(), 1); // depends on x
                                assert_eq!(*fargs[0], Term::Var(*x));
                            }
                            other => panic!("expected Skolem function term, got {:?}", other),
                        }
                    }
                    other => panic!("expected Pred, got {:?}", other),
                }
            }
            other => panic!("expected ForAll, got {:?}", other),
        }
        assert_eq!(table.fresh_generations, 1);
        assert_eq!(table.reuse_hits, 0);
    }

    /// The core incremental-reuse property: push, assert phi, pop, push
    /// again, assert the SAME phi again (simulating DFS backtracking in
    /// symbolic execution / incremental BMC). The second skolemization
    /// should hit the cache instead of minting a new symbol.
    #[test]
    fn identical_formula_reasserted_after_pop_reuses_skolem_symbol() {
        let mut interner = Interner::new();
        let mut table = SkolemTable::new("sk");

        table.push(); // enter scope 1
        let formula_a = build_simple_formula(&mut interner);
        let result_a = {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            sk.skolemize(&formula_a, &[])
        };
        table.pop(1); // back to scope 0 (as SMT-LIB pop would do)

        table.push(); // enter scope 1 again -- different push, same content
        let formula_b = build_simple_formula(&mut interner); // structurally identical, re-interned to same Rc
        let result_b = {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            sk.skolemize(&formula_b, &[])
        };

        assert_eq!(result_a, result_b, "skolemized output should be identical");
        assert_eq!(table.fresh_generations, 1, "only ONE symbol should ever have been minted");
        assert_eq!(table.reuse_hits, 1, "the second assertion should be a cache hit");
    }

    /// Soundness guard: if the SAME body is asserted under a DIFFERENT
    /// dependency context (different surrounding universal variables),
    /// reuse must NOT happen -- a different symbol is required because the
    /// Skolem function's argument list would otherwise be wrong.
    #[test]
    fn same_body_different_deps_does_not_reuse() {
        let mut interner = Interner::new();
        let mut table = SkolemTable::new("sk");
        let mut sk = Skolemizer::new(&mut interner, &mut table);

        let x: u32 = 0;
        let z: u32 = 2;
        let y: u32 = 1;
        let p = mk_pred(sk.interner, "P", vec![Rc::new(Term::Var(y))], false);
        let exists_y = mk_exists(sk.interner, y, p);

        // exists y. P(y), under deps=[x]
        sk.skolemize(&exists_y, &[x]);
        // structurally the SAME formula `exists_y`, but under deps=[z] this time
        sk.skolemize(&exists_y, &[z]);

        assert_eq!(
            table.fresh_generations,
            2,
            "different dependency contexts must not share a Skolem symbol"
        );
    }

    /// The new eviction mechanism: an entry that goes idle for longer
    /// than the configured window becomes eligible for eviction, and its
    /// physical slot gets recycled (freelist reuse -- no growth) for the
    /// next distinct formula, without ever crashing or corrupting state.
    #[test]
    fn evict_cold_reclaims_and_recycles_slot() {
        let mut interner = Interner::new();
        // small window so the test doesn't need thousands of iterations
        let mut table = SkolemTable::with_capacity("sk", 4096, 5);

        let formula_a = build_simple_formula(&mut interner);
        {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            sk.skolemize(&formula_a, &[]);
        }
        assert_eq!(table.len(), 1);
        assert_eq!(table.slot_count(), 1);

        // advance the epoch clock well past the idle window without
        // touching formula_a's entry
        for _ in 0..10 {
            table.push();
            table.pop(1);
        }

        let freed = table.evict_cold();
        assert_eq!(freed, 1);
        assert_eq!(table.len(), 0);
        assert_eq!(table.slot_count(), 1, "slot should be freed, not deallocated");

        // a DIFFERENT formula should recycle the freed slot rather than
        // growing the slot array
        let x: u32 = 10;
        let y: u32 = 11;
        let p2 = mk_pred(
            &mut interner,
            "Q",
            vec![Rc::new(Term::Var(x)), Rc::new(Term::Var(y))],
            false
        );
        let exists_y2 = mk_exists(&mut interner, y, p2);
        let formula_b = mk_forall(&mut interner, x, exists_y2);
        {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            sk.skolemize(&formula_b, &[]);
        }
        assert_eq!(table.slot_count(), 1, "freed slot should have been recycled, not grown");
        assert_eq!(
            table.fresh_generations,
            2,
            "the recycled slot's formula is genuinely new -> fresh symbol"
        );
    }

    /// Soundness-adjacent regression: even after a slot is evicted and
    /// recycled for a different formula, the ORIGINAL formula's next
    /// lookup must mint a brand-new, distinct symbol name -- never reuse
    /// the name that's now occupied by the unrelated recycled formula.
    #[test]
    fn evicted_then_recreated_entry_gets_a_fresh_never_reused_name() {
        let mut interner = Interner::new();
        let mut table = SkolemTable::with_capacity("sk", 4096, 3);

        let formula_a = build_simple_formula(&mut interner);
        let original_symbol = {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            let result = sk.skolemize(&formula_a, &[]);
            extract_skolem_symbol(&result)
        };

        for _ in 0..10 {
            table.push();
            table.pop(1);
        }
        table.evict_cold();

        // re-assert the SAME formula after eviction: must mint a fresh
        // name, not silently collide with anything
        let recreated_symbol = {
            let mut sk = Skolemizer::new(&mut interner, &mut table);
            let result = sk.skolemize(&formula_a, &[]);
            extract_skolem_symbol(&result)
        };

        assert_ne!(
            original_symbol,
            recreated_symbol,
            "names must never be reused, even across eviction"
        );
    }

    fn extract_skolem_symbol(f: &Rc<Formula>) -> String {
        match &**f {
            Formula::ForAll(_, body) =>
                match &**body {
                    Formula::Pred { args, .. } =>
                        match &*args[1] {
                            Term::Func(sym, _) => sym.clone(),
                            other => panic!("expected Skolem function term, got {:?}", other),
                        }
                    other => panic!("expected Pred, got {:?}", other),
                }
            other => panic!("expected ForAll, got {:?}", other),
        }
    }

    /// Baseline comparison: full re-skolemization with a FRESH table every
    /// "check-sat cycle" (i.e. no incrementality at all) should mint a new
    /// symbol every time, even for identical formulas -- this is exactly
    /// the naive behavior this project is trying to improve on.
    #[test]
    fn naive_baseline_always_mints_fresh_symbols() {
        let mut interner = Interner::new();
        let formula = build_simple_formula(&mut interner);

        let mut symbols = Vec::new();
        for _ in 0..3 {
            let mut fresh_table = SkolemTable::new("sk"); // no state carried over -- the naive baseline
            let mut sk = Skolemizer::new(&mut interner, &mut fresh_table);
            let result = sk.skolemize(&formula, &[]);
            if let Formula::ForAll(_, body) = &*result {
                if let Formula::Pred { args, .. } = &**body {
                    if let Term::Func(sym, _) = &*args[1] {
                        symbols.push(sym.clone());
                    }
                }
            }
        }
        // all three should be "sk1" because each table is independent and
        // starts counting from scratch -- illustrating that naive
        // per-call re-skolemization can't even be distinguished from
        // reuse by symbol NAME alone; the real cost this project measures
        // is the WORK done to arrive there (full tree walk every time)
        // plus, in a real solver, re-registering the symbol/axioms with
        // the theory solver from scratch on every check-sat.
        assert_eq!(symbols, vec!["sk1", "sk1", "sk1"]);
    }
}
