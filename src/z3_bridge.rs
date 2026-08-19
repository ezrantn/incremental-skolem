//! Bridge to Z3: translates the (post-skolemization) `Formula`/`Term` AST
//! into `z3::ast` nodes and wraps a `z3::Solver` with an incremental
//! `assert`/`push`/`pop`/`check_sat` API that runs the incremental
//! skolemizer first.
//!
//! DOMAIN SORT ASSUMPTION: this is untyped first-order logic, so every
//! variable, Skolem function, and predicate argument lives in a single
//! uninterpreted sort ("U"). Predicates are uninterpreted functions into
//! Bool; ordinary functions are uninterpreted functions into U. This is
//! the standard, simplest-possible encoding for validating skolemization
//! logic against a real solver -- a multi-sorted version is future work,
//! not needed to test the incrementality claim itself.
//!
//! API NOTE: this targets z3 crate 0.12.x, which uses an explicit `'ctx`
//! Context lifetime (later crate versions switched to an implicit
//! thread-local context). Pinned to 0.12 here because that's what links
//! cleanly against the system-installed Z3 4.8.12 in this environment;
//! bump both together if a newer system Z3 becomes available.

use crate::skolem_table::SkolemTable;
use crate::skolemize::Skolemizer;
use crate::term::{ Formula, Interner, Term, VarId };
use std::collections::HashMap;
use std::rc::Rc;
use z3::ast::{ Ast, Bool, Dynamic };
use z3::{ FuncDecl, SatResult, Solver, Sort, Symbol };

struct DeclRegistry {
    u_sort: Sort,
    preds: HashMap<(String, usize), FuncDecl>,
    funcs: HashMap<(String, usize), FuncDecl>,
    fresh_var_counter: usize,
}

impl DeclRegistry {
    fn new() -> Self {
        DeclRegistry {
            u_sort: Sort::uninterpreted(Symbol::String("U".to_string())),
            preds: HashMap::new(),
            funcs: HashMap::new(),
            fresh_var_counter: 0,
        }
    }

    /// `FuncDecl` isn't `Clone` in this crate version, so instead of
    /// returning it out of the cache (which would require cloning), these
    /// helpers apply it in place and return the resulting `Dynamic`.
    fn apply_pred(&mut self, name: &str, args: &[&dyn Ast]) -> Dynamic {
        let key = (name.to_string(), args.len());
        if !self.preds.contains_key(&key) {
            let domain: Vec<&Sort> = std::iter::repeat(&self.u_sort).take(args.len()).collect();
            let bool_sort = Sort::bool();
            let decl = FuncDecl::new(name, &domain, &bool_sort);
            self.preds.insert(key.clone(), decl);
        }
        self.preds.get(&key).unwrap().apply(args)
    }

    fn apply_func(&mut self, name: &str, args: &[&dyn Ast]) -> Dynamic {
        let key = (name.to_string(), args.len());
        if !self.funcs.contains_key(&key) {
            let domain: Vec<&Sort> = std::iter::repeat(&self.u_sort).take(args.len()).collect();
            let decl = FuncDecl::new(name, &domain, &self.u_sort);
            self.funcs.insert(key.clone(), decl);
        }
        self.funcs.get(&key).unwrap().apply(args)
    }

    /// A fresh 0-arity FuncDecl application, used both as the translation
    /// of a free/bound variable and as the placeholder constant that
    /// `z3::ast::forall_const` binds over -- the same idiom the z3 crate's
    /// own quantifier examples use (an ordinary constant, not a special
    /// "bound variable" type).
    fn fresh_const(&mut self, hint: &str) -> Dynamic {
        self.fresh_var_counter += 1;
        let name = format!("{}!{}", hint, self.fresh_var_counter);
        let decl = FuncDecl::new(name.as_str(), &[], &self.u_sort);
        decl.apply(&[])
    }
}

#[derive(Debug)]
pub enum BridgeError {
    UnboundVariable(VarId),
    UnskolemizedExistential,
}

fn translate_term<'ctx>(
    decls: &mut DeclRegistry,
    bound: &HashMap<VarId, Dynamic>,
    t: &Term
) -> Result<Dynamic, BridgeError> {
    match t {
        Term::Var(v) => bound.get(v).cloned().ok_or(BridgeError::UnboundVariable(*v)),
        Term::Func(name, args) => {
            let mut translated_args = Vec::with_capacity(args.len());
            for a in args {
                translated_args.push(translate_term(decls, bound, a)?);
            }
            let arg_refs: Vec<&dyn Ast> = translated_args
                .iter()
                .map(|a| a as &dyn Ast)
                .collect();
            Ok(decls.apply_func(name, &arg_refs))
        }
    }
}

fn translate_formula(
    decls: &mut DeclRegistry,
    bound: &HashMap<VarId, Dynamic>,
    f: &Formula
) -> Result<Bool, BridgeError> {
    match f {
        Formula::Pred { name, args, negated } => {
            let mut translated_args = Vec::with_capacity(args.len());
            for a in args {
                translated_args.push(translate_term(decls, bound, a)?);
            }
            let arg_refs: Vec<&dyn Ast> = translated_args
                .iter()
                .map(|a| a as &dyn Ast)
                .collect();
            let applied = decls.apply_pred(name, &arg_refs);
            let as_bool: Bool = applied
                .as_bool()
                .expect("predicate FuncDecl must have Bool range sort");
            Ok(if *negated { as_bool.not() } else { as_bool })
        }
        Formula::And(l, r) => {
            let nl = translate_formula(decls, bound, l)?;
            let nr = translate_formula(decls, bound, r)?;
            Ok(Bool::and(&[&nl, &nr]))
        }
        Formula::Or(l, r) => {
            let nl = translate_formula(decls, bound, l)?;
            let nr = translate_formula(decls, bound, r)?;
            Ok(Bool::or(&[&nl, &nr]))
        }
        Formula::ForAll(v, body) => {
            let bound_var = decls.fresh_const("v");
            let mut new_bound = bound.clone();
            new_bound.insert(*v, bound_var.clone());
            let body_translated = translate_formula(decls, &new_bound, body)?;
            let quantified: Bool = z3::ast::forall_const(&[&bound_var], &[], &body_translated);
            Ok(quantified)
        }
        Formula::Exists(_, _) => Err(BridgeError::UnskolemizedExistential),
    }
}

/// A Z3 solver wrapped with an incremental skolemization preprocessing
/// layer. Every `assert` runs the formula through the skolemizer (sharing
/// `Interner`/`SkolemTable` state across calls, so reuse across push/pop
/// works exactly as demonstrated in the core crate's unit tests) before
/// translating to `z3::ast` and handing it to the underlying solver.
pub struct SkolemizingSolver {
    solver: Solver,
    interner: Interner,
    table: SkolemTable,
    decls: DeclRegistry,
}

impl<'ctx> SkolemizingSolver {
    pub fn new() -> Self {
        SkolemizingSolver {
            solver: Solver::new(),
            interner: Interner::new(),
            table: SkolemTable::new("sk!"),
            decls: DeclRegistry::new(),
        }
    }

    pub fn assert(&mut self, formula: &Rc<Formula>) -> Result<(), BridgeError> {
        let skolemized = {
            let mut sk = Skolemizer::new(&mut self.interner, &mut self.table);
            sk.skolemize(formula, &[])
        };
        let bound = HashMap::new();
        let translated = translate_formula(&mut self.decls, &bound, &skolemized)?;
        self.solver.assert(&translated);
        Ok(())
    }

    pub fn push(&mut self) {
        self.solver.push();
        self.table.push();
    }

    /// Pop `n` levels. Note: per the SkolemTable design, this does NOT
    /// discard cached Skolem symbols -- only Z3's own assertion stack is
    /// rolled back. Call `self.table_mut().gc_scope(..)` explicitly if
    /// memory reclamation in the Skolem cache is needed.
    pub fn pop(&mut self, n: u32) {
        self.solver.pop(n);
        self.table.pop(n as usize);
    }

    pub fn check_sat(&self) -> SatResult {
        self.solver.check()
    }

    /// (fresh_generations, reuse_hits, current_table_size) -- for
    /// benchmarking/instrumentation.
    pub fn stats(&self) -> (usize, usize, usize) {
        (self.table.fresh_generations, self.table.reuse_hits, self.table.len())
    }

    pub fn table_mut(&mut self) -> &mut SkolemTable {
        &mut self.table
    }
}
