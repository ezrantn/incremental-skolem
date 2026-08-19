//! Scope-aware Skolem symbol table -- v2, fixed-slot design.
//!
//! DESIGN HISTORY (kept because the reasoning matters for the paper):
//! the first version used an unbounded `HashMap<SkolemKey, SkolemEntry>`
//! with an opt-in, caller-triggered `gc_scope()` for memory reclamation.
//! That's sound but relies on the caller knowing when a scope is truly
//! dead, which in real DFS-style incremental usage (symbolic execution,
//! backtracking search) it often doesn't know until much later, if ever.
//!
//! This version replaces that with fixed-size, reusable slots (a
//! freelist, like the `slotmap`/`generational-arena` family of data
//! structures) plus epoch-based idle eviction. No copying-GC, no
//! forwarding pointers: because every slot is a uniform fixed-size
//! record (not a variable-length byte span like a bump arena), a "dead"
//! slot can just be marked free and handed to the next allocation --
//! there is nothing to compact.
//!
//! SOUNDNESS NOTES (both resolved, see the two fixes below the naive
//! version of this design would have needed):
//!
//! 1. Lookup key MUST be the full structural key (`SkolemKey`), not a
//!    truncated hash compared directly. `HashMap<SkolemKey, usize>`
//!    gets this for free -- Rust's `HashMap` always verifies full `Eq`
//!    on any hash-bucket match, so a hash collision between two
//!    genuinely different keys can never cause an incorrect cache hit.
//!    (Porting note for a C++ rewrite: use `unordered_map<FullKey, ...>`,
//!    never compare a raw `uint64_t` hash directly as if it were unique.)
//!
//! 2. Symbol NAMES are minted from a monotonic counter (`next_symbol_id`)
//!    that is never reset or derived from a slot index. Slots (memory)
//!    are freely recycled; symbol identities (names asserted into Z3)
//!    never are. Conflating the two would let an evicted-and-reused slot
//!    hand out a name that collides with the original occupant's name.
//!
//! Eviction timing itself is NOT a soundness concern: whatever has
//! already been asserted into Z3 is Z3's own push/pop stack's problem,
//! entirely decoupled from this cache. Evicting a "live" entry too
//! eagerly just means a later identical assertion mints a fresh,
//! differently-named Skolem function instead of reusing the old one --
//! redundant (two axioms instead of one for what's conceptually the same
//! witness) but not unsound.

use crate::term::Formula;
use std::collections::HashMap;
use std::rc::Rc;

pub type ScopeId = usize;
pub type VarId = u32;
pub type Epoch = u64;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SkolemKey {
    /// Pointer identity of the (hash-consed) existential body -- valid
    /// because all `Formula` construction goes through `Interner::intern`.
    body_ptr: usize,
    /// Universal variables this existential's witness may depend on, in
    /// the order they were introduced.
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

struct Slot {
    occupied: bool,
    key: Option<SkolemKey>,
    entry: Option<SkolemEntry>,
    /// Bumped every time this physical slot is recycled for a new
    /// occupant. Not currently consulted internally (nothing hands out
    /// raw slot indices to callers yet), but kept because it's the
    /// standard generational-index safety net if that ever changes --
    /// cheap to maintain, expensive to retrofit later.
    generation: u32,
    last_active_epoch: Epoch,
}

impl Slot {
    fn empty() -> Self {
        Slot { occupied: false, key: None, entry: None, generation: 0, last_active_epoch: 0 }
    }
}

pub struct SkolemTable {
    slots: Vec<Slot>,
    free_list: Vec<usize>,
    key_to_slot: HashMap<SkolemKey, usize>,
    /// Soft capacity: once exceeded, `get_or_create` triggers an eviction
    /// sweep before growing further.
    soft_capacity: usize,
    /// Idle window (in epochs): a slot not revived within this many
    /// epochs becomes eligible for eviction.
    idle_window: Epoch,
    global_epoch: Epoch,
    current_scope: ScopeId,
    next_symbol_id: usize,
    prefix: String,
    pub reuse_hits: usize,
    pub fresh_generations: usize,
    pub evictions: usize,
}

impl SkolemTable {
    pub fn new(prefix: &str) -> Self {
        Self::with_capacity(prefix, 4096, 2000)
    }

    pub fn with_capacity(prefix: &str, soft_capacity: usize, idle_window: Epoch) -> Self {
        SkolemTable {
            slots: Vec::new(),
            free_list: Vec::new(),
            key_to_slot: HashMap::new(),
            soft_capacity,
            idle_window,
            global_epoch: 0,
            current_scope: 0,
            next_symbol_id: 0,
            prefix: prefix.to_string(),
            reuse_hits: 0,
            fresh_generations: 0,
            evictions: 0,
        }
    }

    pub fn current_scope(&self) -> ScopeId {
        self.current_scope
    }

    pub fn push(&mut self) {
        self.current_scope += 1;
        self.global_epoch += 1;
    }

    /// O(1): no rewind, no traversal, no per-entry invalidation. Just
    /// bookkeeping counters.
    pub fn pop(&mut self, n: usize) {
        self.current_scope = self.current_scope.saturating_sub(n);
        self.global_epoch += 1;
    }

    /// Core operation. A hit -- regardless of how many push/pop cycles
    /// separate it from the original creation -- revives the entry
    /// in-place (updates `last_active_epoch`) rather than requiring the
    /// caller to have kept it "in scope" by any bookkeeping measure.
    pub fn get_or_create(&mut self, body: &Rc<Formula>, deps: &[VarId]) -> SkolemEntry {
        let key = SkolemKey::new(body, deps);

        if let Some(&slot_idx) = self.key_to_slot.get(&key) {
            self.reuse_hits += 1;
            let slot = &mut self.slots[slot_idx];
            slot.last_active_epoch = self.global_epoch;
            return slot.entry.clone().expect("occupied slot must have an entry");
        }

        if self.slots.len() >= self.soft_capacity && self.free_list.is_empty() {
            self.evict_cold();
        }

        let slot_idx = if let Some(idx) = self.free_list.pop() {
            idx
        } else {
            self.slots.push(Slot::empty());
            self.slots.len() - 1
        };

        self.next_symbol_id += 1;
        let entry = SkolemEntry {
            symbol: format!("{}{}", self.prefix, self.next_symbol_id),
            deps: deps.to_vec(),
            introduced_at_scope: self.current_scope,
        };

        let slot = &mut self.slots[slot_idx];
        slot.occupied = true;
        slot.key = Some(key.clone());
        slot.entry = Some(entry.clone());
        slot.last_active_epoch = self.global_epoch;

        self.key_to_slot.insert(key, slot_idx);
        self.fresh_generations += 1;
        entry
    }

    /// Sweep every occupied slot; free anything idle longer than
    /// `idle_window` epochs. O(number of slots), amortized -- called
    /// lazily when capacity pressure is detected, not on every pop.
    pub fn evict_cold(&mut self) -> usize {
        let mut freed = 0;
        for idx in 0..self.slots.len() {
            let slot = &self.slots[idx];
            if !slot.occupied {
                continue;
            }
            if self.global_epoch.saturating_sub(slot.last_active_epoch) > self.idle_window {
                let key = slot.key.clone().expect("occupied slot must have a key");
                self.key_to_slot.remove(&key);
                let slot = &mut self.slots[idx];
                slot.occupied = false;
                slot.key = None;
                slot.entry = None;
                slot.generation += 1;
                self.free_list.push(idx);
                freed += 1;
            }
        }
        self.evictions += freed;
        freed
    }

    /// Number of slots physically allocated (occupied + free-but-held),
    /// for tests/instrumentation to confirm the freelist is actually
    /// being reused rather than the slot array growing unboundedly.
    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn len(&self) -> usize {
        self.slots.len() - self.free_list.len()
    }
}
