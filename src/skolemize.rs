//! The skolemization pass itself.
//!
//! Input MUST be in NNF (see term.rs). Under that assumption, skolemization
//! is a single top-down pass: `ForAll` accumulates a dependency variable;
//! `Exists` is eliminated by substituting a Skolem term built from the
//! accumulated dependencies, looked up (or freshly created) in the
//! `SkolemTable`.

use crate::skolem_table::SkolemTable;
use crate::term::{ substitute, Formula, Interner, Term, VarId };
use std::rc::Rc;

pub struct Skolemizer<'a> {
    pub interner: &'a mut Interner,
    pub table: &'a mut SkolemTable,
}

impl<'a> Skolemizer<'a> {
    pub fn new(interner: &'a mut Interner, table: &'a mut SkolemTable) -> Self {
        Skolemizer { interner, table }
    }

    pub fn skolemize(&mut self, f: &Rc<Formula>, deps: &[VarId]) -> Rc<Formula> {
        match &**f {
            Formula::Pred { .. } => f.clone(),

            Formula::And(l, r) => {
                let nl = self.skolemize(l, deps);
                let nr = self.skolemize(r, deps);
                self.interner.intern(Formula::And(nl, nr))
            }
            Formula::Or(l, r) => {
                let nl = self.skolemize(l, deps);
                let nr = self.skolemize(r, deps);
                self.interner.intern(Formula::Or(nl, nr))
            }
            Formula::ForAll(v, body) => {
                let mut new_deps = deps.to_vec();
                new_deps.push(*v);
                let new_body = self.skolemize(body, &new_deps);
                self.interner.intern(Formula::ForAll(*v, new_body))
            }
            Formula::Exists(v, body) => {
                // Look up (or create) the Skolem symbol for THIS body under
                // THESE deps -- this is the one line that makes the whole
                // thing incremental: identical (body, deps) pairs across
                // different push/pop episodes hit the cache.
                let entry = self.table.get_or_create(body, deps);
                let args: Vec<Rc<Term>> = deps
                    .iter()
                    .map(|d| Rc::new(Term::Var(*d)))
                    .collect();
                let skolem_term = if args.is_empty() {
                    Rc::new(Term::Func(entry.symbol.clone(), vec![])) // Skolem constant
                } else {
                    Rc::new(Term::Func(entry.symbol.clone(), args))
                };
                let substituted = substitute(self.interner, body, *v, &skolem_term);
                self.skolemize(&substituted, deps)
            }
            Formula::True | Formula::False => f.clone(),
        }
    }
}
