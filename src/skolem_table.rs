//! Scope-aware Skolem symbol table.
//!
//! Design note (see accompanying writeup): `pop` does NOT delete cache
//! entries by default. Soundness of reuse is guaranteed entirely by the
//! cache key (structural identity of the existential's body + the exact
//! list of universal variables it depends on), not by scope bookkeeping.
//! Scope is tracked only so a caller can explicitly reclaim memory via
//! `gc_scope` once it knows a region of the search will never be revisited.

use crate::term::Formula;
use std::collections::HashMap;
use std::rc::Rc;

pub type ScopeId = usize;
pub type VarId = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SkolemKey {
    /// Pointer identity of the (hash-consed) existential body. Valid only
    /// because all `Formula` construction goes through `Interner::intern`,
    /// so structurally-equal subformulas share one allocation.
    body_ptr: usize,
    /// Universal variables this existential's witness may depend on, in
    /// the order they were introduced. Order matters: it fixes the
    /// argument order of the generated Skolem function.
    deps: Vec<VarId>,
}

impl SkolemKey {
    pub fn new(body: &Rc<Formula>, deps: &[VarId]) -> Self {
        SkolemKey { body_ptr: Rc::as_ptr(body) as usize, deps: deps.to_vec() }
    }
}

#[derive(Debug, Clone)]
pub struct SkolemEntry {
    pub symbol: String,
    pub deps: Vec<VarId>,
    pub introduced_at_scope: ScopeId,
}

pub struct SkolemTable {
    cache: HashMap<SkolemKey, SkolemEntry>,
    /// keys introduced at each scope depth, indexed by scope id, purely
    /// for optional GC bookkeeping -- not consulted for correctness.
    by_scope: Vec<Vec<SkolemKey>>,
    scope_stack_depth: ScopeId,
    next_id: usize,
    prefix: String,
    pub reuse_hits: usize,
    pub fresh_generations: usize,
}

impl SkolemTable {
    pub fn new(prefix: &str) -> Self {
        SkolemTable {
            cache: HashMap::new(),
            by_scope: vec![Vec::new()],
            scope_stack_depth: 0,
            next_id: 0,
            prefix: prefix.to_string(),
            reuse_hits: 0,
            fresh_generations: 0,
        }
    }

    pub fn current_scope(&self) -> ScopeId {
        self.scope_stack_depth
    }

    pub fn push(&mut self) {
        self.scope_stack_depth += 1;
        if self.by_scope.len() <= self.scope_stack_depth {
            self.by_scope.push(Vec::new());
        }
    }

    /// Pop `n` scopes. Cache entries are deliberately NOT removed here --
    /// see module doc. This only shrinks the bookkeeping depth pointer.
    pub fn pop(&mut self, n: usize) {
        self.scope_stack_depth = self.scope_stack_depth.saturating_sub(n);
    }

    /// Explicit, opt-in memory reclamation: purge every cache entry
    /// introduced at or below `scope_id`. Caller is asserting "we will
    /// never push back into this region again" -- calling this
    /// incorrectly does not break soundness (worst case: a symbol gets
    /// regenerated with a fresh name instead of reused), it only gives up
    /// a caching opportunity. That asymmetry is intentional: it's always
    /// safe to under-GC, never silently unsound to over-GC.
    pub fn gc_scope(&mut self, scope_id: ScopeId) {
        for depth in (scope_id..self.by_scope.len()).rev() {
            for key in self.by_scope[depth].drain(..) {
                self.cache.remove(&key);
            }
        }
    }

    /// Core operation: look up or create the Skolem symbol for an
    /// existential with the given (interned) body and dependency list.
    pub fn get_or_create(&mut self, body: &Rc<Formula>, deps: &[VarId]) -> SkolemEntry {
        let key = SkolemKey::new(body, deps);
        if let Some(existing) = self.cache.get(&key) {
            self.reuse_hits += 1;
            return existing.clone();
        }
        self.fresh_generations += 1;
        self.next_id += 1;
        let entry = SkolemEntry {
            symbol: format!("{}{}", self.prefix, self.next_id),
            deps: deps.to_vec(),
            introduced_at_scope: self.scope_stack_depth,
        };
        self.by_scope[self.scope_stack_depth].push(key.clone());
        self.cache.insert(key, entry.clone());
        entry
    }

    pub fn len(&self) -> usize {
        self.cache.len()
    }
}
