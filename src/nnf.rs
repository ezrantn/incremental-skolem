//! Pre-NNF formula representation, plus the conversion pass into the
//! restricted (NNF-only) `Formula` type the skolemizer expects.
//!
//! This is the "quick win" NNF converter -- kept deliberately separate
//! from `term::Formula` because real SMT-LIB2 input formulas are not
//! pre-normalized, and it turned out simpler to write ~30 lines pushing
//! negations inward on our own AST than to round-trip through Z3's `nnf`
//! tactic (the safe `z3` crate API doesn't expose enough quantifier
//! introspection to walk an arbitrary `z3::ast::Bool` back into our own
//! representation).

use crate::term::{ self, Formula, Interner, Term, VarId };
use std::rc::Rc;

/// Arbitrary (non-NNF) formula: negation and implication may appear
/// anywhere.
#[derive(Debug, Clone)]
pub enum RawFormula {
    Pred {
        name: String,
        args: Vec<Rc<Term>>,
    },
    Not(Box<RawFormula>),
    And(Vec<RawFormula>),
    Or(Vec<RawFormula>),
    Implies(Box<RawFormula>, Box<RawFormula>),
    ForAll(Vec<VarId>, Box<RawFormula>),
    Exists(Vec<VarId>, Box<RawFormula>),
    True,
    False,
}

/// Convert to NNF. `polarity = true` means "as written"; `polarity =
/// false` means "under an odd number of enclosing negations", which is
/// how `Not` is eliminated: instead of building a `Not` node, we just flip
/// polarity and push down, applying De Morgan / quantifier-duality at
/// each connective.
pub fn to_nnf(interner: &mut Interner, f: &RawFormula, polarity: bool) -> Rc<Formula> {
    match f {
        RawFormula::Pred { name, args } => {
            term::mk_pred(interner, name, args.clone(), !polarity)
        }
        RawFormula::Not(inner) => to_nnf(interner, inner, !polarity),
        RawFormula::And(items) => {
            // positive polarity: and stays and; negative: De Morgan -> or
            fold_conjunction_like(interner, items, polarity, true)
        }
        RawFormula::Or(items) => fold_conjunction_like(interner, items, polarity, false),
        RawFormula::Implies(l, r) => {
            // a => b  ==  not(a) or b
            // Under negative polarity this flips to: a and not(b)
            if polarity {
                let nl = to_nnf(interner, l, false);
                let nr = to_nnf(interner, r, true);
                term::mk_or(interner, nl, nr)
            } else {
                let nl = to_nnf(interner, l, true);
                let nr = to_nnf(interner, r, false);
                term::mk_and(interner, nl, nr)
            }
        }
        RawFormula::ForAll(vars, body) => fold_quantifier(interner, vars, body, polarity, true),
        RawFormula::Exists(vars, body) => fold_quantifier(interner, vars, body, polarity, false),
        RawFormula::True => {
            if polarity { term::mk_true(interner) } else { term::mk_false(interner) }
        }
        RawFormula::False => {
            if polarity { term::mk_false(interner) } else { term::mk_true(interner) }
        }
    }
}

fn fold_conjunction_like(
    interner: &mut Interner,
    items: &[RawFormula],
    polarity: bool,
    is_and: bool
) -> Rc<Formula> {
    // positive polarity + is_and, or negative polarity + !is_and -> AND
    // positive polarity + !is_and, or negative polarity + is_and -> OR
    let use_and = polarity == is_and;
    if items.is_empty() {
        return if use_and { term::mk_true(interner) } else { term::mk_false(interner) };
    }
    let mut parts: Vec<Rc<Formula>> = items
        .iter()
        .map(|i| to_nnf(interner, i, polarity))
        .collect();
    let mut acc = parts.pop().unwrap();
    while let Some(p) = parts.pop() {
        acc = if use_and { term::mk_and(interner, p, acc) } else { term::mk_or(interner, p, acc) };
    }
    acc
}

fn fold_quantifier(
    interner: &mut Interner,
    vars: &[VarId],
    body: &RawFormula,
    polarity: bool,
    is_forall: bool
) -> Rc<Formula> {
    // forall under positive polarity stays forall; under negative
    // polarity, "not (forall x. P)" == "exists x. not P" (and dually).
    let use_forall = polarity == is_forall;
    let mut result = to_nnf(interner, body, polarity);
    for &v in vars.iter().rev() {
        result = if use_forall {
            term::mk_forall(interner, v, result)
        } else {
            term::mk_exists(interner, v, result)
        };
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Formula;

    #[test]
    fn not_of_and_becomes_or_of_negated_atoms() {
        let mut interner = Interner::new();
        // not (P and Q)  ->  (not P) or (not Q)
        let raw = RawFormula::Not(
            Box::new(
                RawFormula::And(
                    vec![
                        RawFormula::Pred { name: "P".into(), args: vec![] },
                        RawFormula::Pred { name: "Q".into(), args: vec![] }
                    ]
                )
            )
        );
        let result = to_nnf(&mut interner, &raw, true);
        match &*result {
            Formula::Or(l, r) => {
                assert!(matches!(&**l, Formula::Pred { negated: true, name, .. } if name == "P"));
                assert!(matches!(&**r, Formula::Pred { negated: true, name, .. } if name == "Q"));
            }
            other => panic!("expected Or, got {:?}", other),
        }
    }

    #[test]
    fn not_of_forall_becomes_exists_of_negated_body() {
        let mut interner = Interner::new();
        let raw = RawFormula::Not(
            Box::new(
                RawFormula::ForAll(
                    vec![0],
                    Box::new(RawFormula::Pred {
                        name: "P".into(),
                        args: vec![Rc::new(Term::Var(0))],
                    })
                )
            )
        );
        let result = to_nnf(&mut interner, &raw, true);
        match &*result {
            Formula::Exists(v, body) => {
                assert_eq!(*v, 0);
                assert!(matches!(&**body, Formula::Pred { negated: true, .. }));
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn implies_under_negation_becomes_and() {
        let mut interner = Interner::new();
        // not (P => Q)  ->  P and not Q
        let raw = RawFormula::Not(
            Box::new(
                RawFormula::Implies(
                    Box::new(RawFormula::Pred { name: "P".into(), args: vec![] }),
                    Box::new(RawFormula::Pred { name: "Q".into(), args: vec![] })
                )
            )
        );
        let result = to_nnf(&mut interner, &raw, true);
        match &*result {
            Formula::And(l, r) => {
                assert!(matches!(&**l, Formula::Pred { negated: false, name, .. } if name == "P"));
                assert!(matches!(&**r, Formula::Pred { negated: true, name, .. } if name == "Q"));
            }
            other => panic!("expected And, got {:?}", other),
        }
    }
}
