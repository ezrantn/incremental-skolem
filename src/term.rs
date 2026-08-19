//! Core FOL AST.
//!
//! ASSUMPTION (documented, not hidden): input formulas are expected to
//! already be in Negation Normal Form (NNF) -- negation only applies to
//! atomic predicates. This is standard practice: NNF conversion is a
//! separate, well-understood preprocessing pass, and keeping it out of
//! this module lets the skolemizer stay focused on the one thing that's
//! actually novel here (incremental/scope-aware Skolem symbol reuse).

use std::collections::HashMap;
use std::rc::Rc;

pub type VarId = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Var(VarId),
    Func(String, Vec<Rc<Term>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    /// Predicate application, possibly negated (NNF assumption: `negated`
    /// only ever appears on atoms).
    Pred {
        name: String,
        args: Vec<Rc<Term>>,
        negated: bool,
    },
    And(Rc<Formula>, Rc<Formula>),
    Or(Rc<Formula>, Rc<Formula>),
    ForAll(VarId, Rc<Formula>),
    Exists(VarId, Rc<Formula>),
    True,
    False,
}

/// Hash-consing interner: structurally identical formulas collapse to the
/// same `Rc` allocation. This is what makes pointer-identity comparison in
/// `SkolemKey` valid -- two subformulas that are `==` are also the *same
/// object* after going through `intern`.
#[derive(Default)]
pub struct Interner {
    table: HashMap<Formula, Rc<Formula>>,
    pub hits: usize,
    pub total: usize,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, f: Formula) -> Rc<Formula> {
        self.total += 1;
        if let Some(existing) = self.table.get(&f) {
            self.hits += 1;
            return existing.clone();
        }
        let rc = Rc::new(f.clone());
        self.table.insert(f, rc.clone());
        rc
    }

    pub fn dedup_ratio(&self) -> f64 {
        if self.total == 0 { 0.0 } else { (self.hits as f64) / (self.total as f64) }
    }
}

/// Convenience constructors that go through the interner, so callers never
/// accidentally build a non-interned (and therefore reuse-invisible) node.
pub fn mk_pred(
    interner: &mut Interner,
    name: &str,
    args: Vec<Rc<Term>>,
    negated: bool
) -> Rc<Formula> {
    interner.intern(Formula::Pred { name: name.to_string(), args, negated })
}
pub fn mk_and(interner: &mut Interner, l: Rc<Formula>, r: Rc<Formula>) -> Rc<Formula> {
    interner.intern(Formula::And(l, r))
}
pub fn mk_or(interner: &mut Interner, l: Rc<Formula>, r: Rc<Formula>) -> Rc<Formula> {
    interner.intern(Formula::Or(l, r))
}
pub fn mk_forall(interner: &mut Interner, v: VarId, body: Rc<Formula>) -> Rc<Formula> {
    interner.intern(Formula::ForAll(v, body))
}
pub fn mk_exists(interner: &mut Interner, v: VarId, body: Rc<Formula>) -> Rc<Formula> {
    interner.intern(Formula::Exists(v, body))
}
pub fn mk_true(interner: &mut Interner) -> Rc<Formula> {
    interner.intern(Formula::True)
}
pub fn mk_false(interner: &mut Interner) -> Rc<Formula> {
    interner.intern(Formula::False)
}

pub fn substitute_term(t: &Rc<Term>, var: VarId, replacement: &Rc<Term>) -> Rc<Term> {
    match &**t {
        Term::Var(v) if *v == var => replacement.clone(),
        Term::Var(_) => t.clone(),
        Term::Func(name, args) =>
            Rc::new(
                Term::Func(
                    name.clone(),
                    args
                        .iter()
                        .map(|a| substitute_term(a, var, replacement))
                        .collect()
                )
            ),
    }
}

pub fn substitute(
    interner: &mut Interner,
    f: &Rc<Formula>,
    var: VarId,
    replacement: &Rc<Term>
) -> Rc<Formula> {
    match &**f {
        Formula::Pred { name, args, negated } => {
            let new_args = args
                .iter()
                .map(|a| substitute_term(a, var, replacement))
                .collect();
            interner.intern(Formula::Pred { name: name.clone(), args: new_args, negated: *negated })
        }
        Formula::And(l, r) => {
            let nl = substitute(interner, l, var, replacement);
            let nr = substitute(interner, r, var, replacement);
            interner.intern(Formula::And(nl, nr))
        }
        Formula::Or(l, r) => {
            let nl = substitute(interner, l, var, replacement);
            let nr = substitute(interner, r, var, replacement);
            interner.intern(Formula::Or(nl, nr))
        }
        Formula::ForAll(v, body) => {
            if *v == var {
                f.clone() // shadowed: inner quantifier rebinds the variable
            } else {
                let nb = substitute(interner, body, var, replacement);
                interner.intern(Formula::ForAll(*v, nb))
            }
        }
        Formula::Exists(v, body) => {
            if *v == var {
                f.clone()
            } else {
                let nb = substitute(interner, body, var, replacement);
                interner.intern(Formula::Exists(*v, nb))
            }
        }
        Formula::True | Formula::False => f.clone(),
    }
}
