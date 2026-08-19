//! SMT-LIB2 command interpreter. Supports the subset needed to drive
//! `SkolemizingSolver` from real benchmark files: `declare-sort`,
//! `declare-fun`, `declare-const`, `assert`, `push`, `pop`, `check-sat`.
//! `set-logic`/`set-info`/`set-option` are accepted and ignored. Unknown
//! commands are ignored with a diagnostic recorded rather than a hard
//! error, so a run doesn't die on the first unsupported feature (e.g.
//! `get-model`) in an otherwise-usable benchmark file.
//!
//! SCOPE LIMITATION (see also z3_bridge.rs's domain-sort note): this
//! targets the single-sorted uninterpreted-function fragment (roughly,
//! SMT-LIB's UF logic family) with quantifiers. Arithmetic, bit-vectors,
//! arrays, strings etc. are not handled -- symbols of those sorts get
//! folded into the single domain sort `U`, which is semantically wrong
//! for anything that actually relies on arithmetic. `let` bindings are
//! also not supported yet.

use crate::nnf::{ self, RawFormula };
use crate::sexpr::{ parse_all, ParseError, Sexpr };
use crate::term::{ Interner, Term, VarId };
use crate::z3_bridge::{ BridgeError, SkolemizingSolver };
use std::collections::HashMap;
use std::rc::Rc;
use z3::SatResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DeclKind {
    arity: usize,
    is_bool: bool,
}

#[derive(Debug)]
pub enum InterpError {
    Parse(String),
    Bridge(String),
    Semantic(String),
}

impl From<ParseError> for InterpError {
    fn from(e: ParseError) -> Self {
        InterpError::Parse(e.0)
    }
}
impl From<BridgeError> for InterpError {
    fn from(e: BridgeError) -> Self {
        InterpError::Bridge(format!("{:?}", e))
    }
}

pub struct Interpreter {
    solver: SkolemizingSolver,
    /// Shared across all `assert` commands in this session -- this is
    /// what makes structurally-identical subformulas across separate
    /// `(assert ...)` texts collapse to the same `Rc`, which is what the
    /// Skolem cache's pointer-identity key depends on.
    interner: Interner,
    declared: HashMap<String, DeclKind>,
    /// Every `(check-sat)` result encountered, in order, for the CLI
    /// driver / test harness to inspect.
    pub results: Vec<SatResult>,
    pub diagnostics: Vec<String>,
}

impl<'ctx> Interpreter {
    pub fn new(ctx: &'ctx z3::Context) -> Self {
        let mut declared = HashMap::new();
        // Built-in equality gets special-cased in the z3 bridge (real
        // z3 equality, not an uninterpreted predicate), but it still
        // needs a DeclKind entry so parsing treats `=` as a 2-ary
        // Bool-valued symbol like any other predicate.
        declared.insert("=".to_string(), DeclKind { arity: 2, is_bool: true });
        Interpreter {
            solver: SkolemizingSolver::new(),
            interner: Interner::new(),
            declared,
            results: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn run_source(&mut self, src: &str) -> Result<(), InterpError> {
        let commands = parse_all(src)?;
        for cmd in commands {
            if !self.run_command(&cmd)? {
                break; // (exit) encountered
            }
        }
        Ok(())
    }

    /// Returns `false` if this was an `(exit)` command and the caller
    /// should stop processing further commands.
    fn run_command(&mut self, cmd: &Sexpr) -> Result<bool, InterpError> {
        let list = cmd
            .list()
            .ok_or_else(|| InterpError::Semantic("top-level command must be a list".into()))?;
        if list.is_empty() {
            return Ok(true);
        }
        let head = list[0]
            .atom()
            .ok_or_else(|| InterpError::Semantic("command head must be a symbol".into()))?;

        match head {
            "set-logic" | "set-info" | "set-option" => {}
            "declare-sort" => {
                // Single-domain-sort simplification: nothing to record.
            }
            "declare-const" => {
                let name = list[1]
                    .atom()
                    .ok_or_else(|| {
                        InterpError::Semantic("declare-const: expected symbol name".into())
                    })?;
                let sort = list[2].atom().unwrap_or("");
                self.declared.insert(name.to_string(), DeclKind {
                    arity: 0,
                    is_bool: sort == "Bool",
                });
            }
            "declare-fun" => {
                let name = list[1]
                    .atom()
                    .ok_or_else(|| {
                        InterpError::Semantic("declare-fun: expected symbol name".into())
                    })?;
                let domain = list[2]
                    .list()
                    .ok_or_else(||
                        InterpError::Semantic("declare-fun: expected domain sort list".into())
                    )?;
                let range_sort = list[3].atom().unwrap_or("");
                self.declared.insert(name.to_string(), DeclKind {
                    arity: domain.len(),
                    is_bool: range_sort == "Bool",
                });
            }
            "assert" => {
                // Fresh, LOCAL variable counter starting at 0 for every
                // top-level assert -- see the doc comment above on why
                // this must not be a persistent session-wide counter.
                let mut var_counter: VarId = 0;
                let raw = self.parse_formula(&list[1], &mut HashMap::new(), &mut var_counter)?;
                let formula = nnf::to_nnf(&mut self.interner, &raw, true);
                self.solver.assert(&formula)?;
            }
            "push" => {
                let n = list
                    .get(1)
                    .and_then(|s| s.atom())
                    .and_then(|a| a.parse::<u32>().ok())
                    .unwrap_or(1);
                for _ in 0..n {
                    self.solver.push();
                }
            }
            "pop" => {
                let n = list
                    .get(1)
                    .and_then(|s| s.atom())
                    .and_then(|a| a.parse::<u32>().ok())
                    .unwrap_or(1);
                self.solver.pop(n);
            }
            "check-sat" => {
                self.results.push(self.solver.check_sat());
            }
            "exit" => {
                return Ok(false);
            }
            other => {
                self.diagnostics.push(format!("ignored unsupported command: {}", other));
            }
        }
        Ok(true)
    }

    fn fresh_var(counter: &mut VarId) -> VarId {
        let v = *counter;
        *counter += 1;
        v
    }

    pub fn solver_stats(&self) -> (usize, usize, usize) {
        self.solver.stats()
    }

    fn parse_term(
        &mut self,
        s: &Sexpr,
        env: &HashMap<String, VarId>
    ) -> Result<Rc<Term>, InterpError> {
        match s {
            Sexpr::Atom(name) => {
                if let Some(&v) = env.get(name) {
                    return Ok(Rc::new(Term::Var(v)));
                }
                if let Some(decl) = self.declared.get(name) {
                    if decl.arity == 0 && !decl.is_bool {
                        return Ok(Rc::new(Term::Func(name.clone(), vec![])));
                    }
                }
                // Fallback: treat bare numerals / unknown atoms as unique
                // 0-arity domain constants named after their text. This
                // is a deliberate simplification -- see module doc.
                Ok(Rc::new(Term::Func(name.clone(), vec![])))
            }
            Sexpr::List(items) => {
                let name = items[0]
                    .atom()
                    .ok_or_else(|| InterpError::Semantic("term head must be a symbol".into()))?;
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(self.parse_term(a, env)?);
                }
                Ok(Rc::new(Term::Func(name.to_string(), args)))
            }
        }
    }

    fn parse_formula(
        &mut self,
        s: &Sexpr,
        env: &mut HashMap<String, VarId>,
        counter: &mut VarId
    ) -> Result<RawFormula, InterpError> {
        match s {
            Sexpr::Atom(name) =>
                match name.as_str() {
                    "true" => Ok(RawFormula::True),
                    "false" => Ok(RawFormula::False),
                    _ => Ok(RawFormula::Pred { name: name.clone(), args: vec![] }),
                }
            Sexpr::List(items) => {
                let head = items[0]
                    .atom()
                    .ok_or_else(|| InterpError::Semantic("formula head must be a symbol".into()))?;
                match head {
                    "and" => {
                        let mut parts = Vec::with_capacity(items.len() - 1);
                        for it in &items[1..] {
                            parts.push(self.parse_formula(it, env, counter)?);
                        }
                        Ok(RawFormula::And(parts))
                    }
                    "or" => {
                        let mut parts = Vec::with_capacity(items.len() - 1);
                        for it in &items[1..] {
                            parts.push(self.parse_formula(it, env, counter)?);
                        }
                        Ok(RawFormula::Or(parts))
                    }
                    "not" =>
                        Ok(RawFormula::Not(Box::new(self.parse_formula(&items[1], env, counter)?))),
                    "=>" => {
                        // right-fold: (=> a b c) == a => (b => c)
                        let mut parts = Vec::with_capacity(items.len() - 1);
                        for it in &items[1..] {
                            parts.push(self.parse_formula(it, env, counter)?);
                        }
                        let mut acc = parts.pop().expect("=> needs at least 2 args");
                        while let Some(p) = parts.pop() {
                            acc = RawFormula::Implies(Box::new(p), Box::new(acc));
                        }
                        Ok(acc)
                    }
                    "=" => {
                        let l = self.parse_term(&items[1], env)?;
                        let r = self.parse_term(&items[2], env)?;
                        Ok(RawFormula::Pred { name: "=".to_string(), args: vec![l, r] })
                    }
                    "distinct" => {
                        let mut terms = Vec::with_capacity(items.len() - 1);
                        for it in &items[1..] {
                            terms.push(self.parse_term(it, env)?);
                        }
                        let mut pairs = Vec::new();
                        for i in 0..terms.len() {
                            for j in i + 1..terms.len() {
                                pairs.push(
                                    RawFormula::Not(
                                        Box::new(RawFormula::Pred {
                                            name: "=".to_string(),
                                            args: vec![terms[i].clone(), terms[j].clone()],
                                        })
                                    )
                                );
                            }
                        }
                        Ok(RawFormula::And(pairs))
                    }
                    "forall" | "exists" => {
                        let bindings = items[1]
                            .list()
                            .ok_or_else(|| {
                                InterpError::Semantic("quantifier: expected binding list".into())
                            })?;
                        let mut new_vars = Vec::with_capacity(bindings.len());
                        let mut shadowed = Vec::new();
                        for b in bindings {
                            let pair = b
                                .list()
                                .ok_or_else(|| {
                                    InterpError::Semantic(
                                        "quantifier binding must be (name sort)".into()
                                    )
                                })?;
                            let name = pair[0]
                                .atom()
                                .ok_or_else(|| {
                                    InterpError::Semantic(
                                        "quantifier binding name must be a symbol".into()
                                    )
                                })?;
                            let v = Self::fresh_var(counter);
                            shadowed.push((name.to_string(), env.get(name).copied()));
                            env.insert(name.to_string(), v);
                            new_vars.push(v);
                        }
                        let body = self.parse_formula(&items[2], env, counter)?;
                        for (name, prev) in shadowed {
                            match prev {
                                Some(v) => {
                                    env.insert(name, v);
                                }
                                None => {
                                    env.remove(&name);
                                }
                            }
                        }
                        if head == "forall" {
                            Ok(RawFormula::ForAll(new_vars, Box::new(body)))
                        } else {
                            Ok(RawFormula::Exists(new_vars, Box::new(body)))
                        }
                    }
                    pred_name => {
                        let mut args = Vec::with_capacity(items.len() - 1);
                        for a in &items[1..] {
                            args.push(self.parse_term(a, env)?);
                        }
                        Ok(RawFormula::Pred { name: pred_name.to_string(), args })
                    }
                }
            }
        }
    }
}
