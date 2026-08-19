# incremental-skolemizer (prototype)

Standalone Rust core for incremental, scope-aware Skolemization. This is
Phase 1/2 of the research plan: the algorithmic core, deliberately kept
independent of any specific SMT solver so it can be validated on its own
before wiring it in front of Z3.

## What's implemented

- `term.rs` — FOL AST (`Term`, `Formula`) with a hash-consing `Interner`.
  Structurally identical subformulas collapse to the same `Rc` allocation,
  which is what makes pointer-identity comparison in the Skolem cache key
  valid and O(1).
- `skolem_table.rs` — **v2 fixed-slot design** (see below). A cache keyed
  on `(structural identity of existential body, ordered list of universal
  dependency variables)`. Reclamation is now automatic (epoch-idle-based
  eviction with freelist slot reuse) rather than requiring the caller to
  explicitly call a scope-based GC.
- `skolemizer.rs` — the top-down NNF skolemization pass that ties the two
  together. Unchanged across the v1 -> v2 table redesign, since the
  table's public API stayed identical.

## Skolem table design (v2): fixed slots + epoch-idle eviction

The first version (still worth reading the reasoning for -- see git
history / the module doc in `skolem_table.rs`) used an unbounded
`HashMap` plus an opt-in, caller-triggered `gc_scope()`. That's sound but
assumes the caller knows when a scope is truly dead, which in real DFS
backtracking (symbolic execution, incremental BMC) it often doesn't know
until much later, if ever -- so in practice memory would grow unbounded
unless someone remembered to call it.

**v2 replaces manual GC with automatic, freelist-based slot recycling:**
fixed-size slots in a `Vec`, a `HashMap<SkolemKey, usize>` mapping keys to
slot indices, and an idle-epoch eviction sweep (`evict_cold`) triggered
automatically when the table grows past a soft capacity. No copying-GC,
no forwarding pointers -- because every slot is a uniform fixed-size
record (unlike a variable-length bump-arena span), a "cold" slot just
gets marked free and handed to the next allocation.

**Two soundness details that matter and are easy to get wrong:**
1. The lookup key MUST be the full `SkolemKey`, not a hash compared
   directly -- `HashMap<SkolemKey, usize>` gets this for free (Rust's
   `HashMap` always verifies full `Eq` on a hash-bucket match), avoiding
   any birthday-paradox collision risk. **Porting note for a C++
   rewrite:** use `unordered_map<FullKey, ...>`, never trust a raw
   `uint64_t` hash as if it were unique.
2. Symbol *names* are minted from a monotonic counter, completely
   decoupled from slot indices. Slots (memory) are freely recycled;
   symbol identities (names already asserted into Z3) never are --
   otherwise an evicted-and-reused slot could hand out a name colliding
   with the original occupant's.

Eviction *timing* turns out not to be a soundness concern at all: whatever
is already asserted into Z3 is entirely decoupled from this cache (Z3
tracks its own push/pop state). Evicting a still-"live" entry too eagerly
just costs a redundant re-mint on the next identical assertion -- wasteful
(two Skolem functions for what's conceptually one witness), never wrong.

## Key assumption (stated, not hidden)

Input formulas must already be in **Negation Normal Form** — negation only
on atoms. NNF conversion is a separate, well-understood pass and is
deliberately kept out of this crate so the novel part (incremental reuse)
stays isolated and easy to reason about / prove things about.

## What the tests demonstrate

Run with `cargo test`. 18 tests across the crate; the ones most worth
reading, each targeting one claim from the research plan:

1. `basic_skolemization_produces_dependent_symbol` — sanity check that
   plain (non-incremental) skolemization is correct.
2. `identical_formula_reasserted_after_pop_reuses_skolem_symbol` — **the
   core claim**: push → assert φ → pop → push → assert φ again reuses the
   same Skolem symbol instead of minting a new one. This is the DFS
   backtracking pattern from symbolic execution / incremental BMC that
   motivates the whole project.
3. `same_body_different_deps_does_not_reuse` — soundness guard: same
   subformula body under a *different* universal-dependency context must
   NOT reuse a symbol, since that would generate a Skolem function with
   the wrong argument list.
4. `evict_cold_reclaims_and_recycles_slot` — the v2 eviction mechanism:
   an idle entry gets freed automatically, and its physical slot is
   recycled (freelist reuse) by the next distinct formula rather than
   growing the slot array.
5. `evicted_then_recreated_entry_gets_a_fresh_never_reused_name` —
   soundness regression: after eviction+recycling, re-asserting the
   original formula mints a genuinely new name rather than risking any
   collision with whatever now occupies the recycled slot.
6. `naive_baseline_always_mints_fresh_symbols` — illustrates what a naive
   (non-incremental, fresh-table-per-check-sat) implementation does, as a
   reference point for what this project improves on.

## What's NOT here yet (honest gap list)

- **`let` bindings are not supported** in the SMT-LIB2 parser.
- **Full alpha-equivalence is not guaranteed** — see the regression-test
  note above. Only positional/order-based equivalence is currently
  handled; two formulas that bind variables in a different order but are
  otherwise equivalent will not reuse a Skolem symbol.
- **No sort checking.** All declared sorts collapse into one domain `U`;
  a benchmark that actually depends on multiple distinct sorts will be
  translated incorrectly (silently, not with an error) rather than
  rejected. This is the same limitation as the domain-sort assumption in
  `z3_bridge.rs`, now inherited by the parser.
- **Equisatisfiability validation is only spot-checked, not systematic.**
  The integration tests confirm SAT/UNSAT verdicts stay correct across a
  handful of hand-built formulas. Phase 3's actual correctness pipeline
  (running the full benchmark corpus through both incremental and
  from-scratch skolemization and diffing verdicts) still needs building.
- **Term-level hash-consing is not implemented**, only Formula-level. A
  production version should also intern `Term`, since Skolem function
  applications with identical arguments currently allocate separately.
  Left out here to keep the core minimal and auditable.
- **No formal soundness proof**, only the empirical soundness guard test
  (#3 above). The research plan calls for a proof sketch in Phase 1 — this
  code is a good testbed for finding the exact conditions that proof needs
  to state, but it is not itself that proof.

## Next steps

1. Pull a handful of real push/pop sequences from the SMT-LIB incremental
   benchmark set (now that there's a parser to feed them through) and run
   them via `run_smt2`, checking for parse failures / unsupported
   constructs before investing further.
2. Build the systematic correctness pipeline from the Phase 3 protocol:
   for each benchmark formula, run both incremental and fresh-table
   ("naive baseline") skolemization, translate both to Z3, and diff the
   SAT/UNSAT verdicts across the full corpus. Consider using Z3's own
   `snf` (Skolem Normal Form) tactic as the authoritative naive baseline
   instead of hand-rolling one -- it's literally what production tooling
   does with no incrementality, which makes for a stronger comparison.
3. Add Term-level hash-consing (currently only Formula-level) once the
   benchmark corpus is large enough that duplicate Skolem-function-argument
   allocation shows up as a measurable cost.
4. Start the `criterion` benchmarks from the earlier protocol document,
   now that there's a real (if minimal) system to measure.
5. `let`-binding support in the parser, if benchmark files need it (common
   in generated SMT-LIB output).
