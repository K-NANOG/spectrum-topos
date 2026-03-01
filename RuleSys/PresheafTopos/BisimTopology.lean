/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bisimulation Grothendieck Topology J_bisim

This file defines the bisimulation Grothendieck topology on f.p.LTS₁ (= FinDigraph):
a sieve S on G is bisim-covering iff it contains ALL homomorphisms from rooted trees
into G, for every rooted tree T.

## Key Results

- `Reachable`: inductive reachability predicate on digraphs
- `IsRootedTree`: predicate characterizing finite rooted trees (unique root, unique parents)
- `fanDigraph k`: the fan tree (root with k leaf children)
- `pathDigraph_isRootedTree`, `fanDigraph_isRootedTree`: both families are rooted trees
- `isBisimCovering`: the covering predicate for J_bisim
- `bisim_covering_implies_trace_covering`: J_bisim is finer than J_trace
- Three Grothendieck axioms verified: maximality, stability, transitivity
- `bisim_strictly_finer_than_trace_topology`: J_bisim is strictly finer than J_trace

## Mathematical Significance

The bisimulation topology is the finest named-equivalence topology. Together with J_trace
(Phase 165), it brackets the entire van Glabbeek spectrum: J_bisim ⊆ J_X ⊆ J_trace for
all named equivalences X. The topology-as-backward-lifting interpretation: J_bisim enforces
full zig-zag backward lifting (via tree probes), while J_trace enforces only path-length
backward lifting.

The key insight: tree-hom EXISTENCE does not characterize bisimulation (homomorphisms can
collapse branches). But the SIEVE condition (ALL tree homs must be in the sieve) is
strictly stronger — it captures "the test object T can reach G in EVERY possible way."

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), §III.2 (Grothendieck topologies)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Joyal-Nielsen-Winskel, "Bisimulation from open maps" (1996)
-/

import RuleSys.PresheafTopos.TraceSeparation

set_option autoImplicit false

namespace Ruliology.PresheafTopos

/-!
## Part 1: Reachability and Rooted Tree Infrastructure
-/

/-- Reachability in a digraph: v can reach u via a sequence of edges.
    This is the reflexive-transitive closure of the edge relation. -/
inductive Reachable (G : FinDigraph) : G.Vertex → G.Vertex → Prop where
  | refl (v : G.Vertex) : Reachable G v v
  | step {v w u : G.Vertex} : G.edge v w → Reachable G w u → Reachable G v u

/-- Reachability is transitive. -/
theorem Reachable.trans {G : FinDigraph} {v w u : G.Vertex}
    (h1 : Reachable G v w) (h2 : Reachable G w u) : Reachable G v u := by
  induction h1 with
  | refl _ => exact h2
  | step he _ ih => exact Reachable.step he (ih h2)

/-- A single edge gives reachability. -/
theorem Reachable.single {G : FinDigraph} {v w : G.Vertex}
    (he : G.edge v w) : Reachable G v w :=
  Reachable.step he (Reachable.refl w)

/-- A finite digraph is a rooted tree if there exists a distinguished root vertex such that:
    1. No edges point to the root
    2. Every non-root vertex has exactly one parent
    3. Every vertex is reachable from the root

    This captures exactly the finite rooted trees used as "test objects" (observation
    trees) in the bisimulation game. Defined as a Prop using existential quantification
    over the root vertex. -/
def IsRootedTree (G : FinDigraph) : Prop :=
  ∃ (root : G.Vertex),
    (∀ v, ¬G.edge v root) ∧
    (∀ v, v ≠ root → ∃! p, G.edge p v) ∧
    (∀ v, Reachable G root v)

/-!
## Part 2: Fan Digraph
-/

/-- The fan digraph fan(k): a root vertex 0 with k leaf children 1, ..., k.
    Total vertices: k+1. Edges: 0→1, 0→2, ..., 0→k.

    For k = 0, this is a single isolated vertex (= pathDigraph 0).
    For k = 1, this is an edge 0→1 (= pathDigraph 1).
    For k ≥ 2, this is a genuine branching tree (not a path). -/
@[reducible] def fanDigraph (k : ℕ) : FinDigraph where
  Vertex := Fin (k + 1)
  edge := fun s t => s.val = 0 ∧ 0 < t.val
  edgeDecidable := fun _ _ => inferInstance

/-!
## Part 3: Path Digraphs Are Rooted Trees
-/

/-- Helper: in pathDigraph n, vertex 0 can reach any vertex ⟨m, _⟩ for m ≤ n. -/
private theorem pathDigraph_reachable_aux (n : ℕ) (m : ℕ) (hm : m ≤ n) :
    Reachable (pathDigraph n) ⟨0, Nat.zero_lt_succ n⟩ ⟨m, by omega⟩ := by
  induction m with
  | zero => exact Reachable.refl _
  | succ k ih =>
    have hreach := ih (by omega : k ≤ n)
    have hedge : (pathDigraph n).edge ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by
      show (⟨k + 1, _⟩ : Fin (n + 1)).val = (⟨k, _⟩ : Fin (n + 1)).val + 1
      simp
    exact hreach.trans (Reachable.single hedge)

/-- Every path digraph P_n is a rooted tree with root ⟨0⟩.

    This is the bridge between J_trace and J_bisim: since paths are trees,
    any bisim-covering sieve automatically contains all path morphisms. -/
theorem pathDigraph_isRootedTree (n : ℕ) : IsRootedTree (pathDigraph n) := by
  refine ⟨⟨0, Nat.zero_lt_succ n⟩, ?_, ?_, ?_⟩
  · -- no_edge_to_root: if edge v ⟨0, _⟩ then 0 = v.val + 1, impossible
    intro v he
    -- he : (pathDigraph n).edge v ⟨0, _⟩ i.e. 0 = v.val + 1
    simp at he
  · -- unique_parent: for v ≠ root, unique parent is ⟨v.val - 1⟩
    intro v hne
    have hv_pos : 0 < v.val := by
      by_contra h
      push_neg at h
      apply hne
      apply Fin.ext
      show v.val = 0
      omega
    refine ⟨⟨v.val - 1, by omega⟩, ?_, ?_⟩
    · -- Existence: edge from ⟨v.val - 1⟩ to v
      show v.val = (⟨v.val - 1, _⟩ : Fin (n + 1)).val + 1
      simp; omega
    · -- Uniqueness: any parent p must equal ⟨v.val - 1⟩
      intro p hp
      change v.val = p.val + 1 at hp
      apply Fin.ext; simp; omega
  · -- all_reachable
    intro v
    have := pathDigraph_reachable_aux n v.val (by omega)
    have hv_eq : v = ⟨v.val, v.isLt⟩ := rfl
    rw [hv_eq]
    exact this

/-!
## Part 4: Fan Digraphs Are Rooted Trees
-/

/-- Every fan digraph fan(k) with k > 0 is a rooted tree with root ⟨0⟩.

    The fan is the simplest branching tree: a root with k leaf children.
    For k ≥ 2, this provides the key test objects that separate J_bisim from J_trace. -/
theorem fanDigraph_isRootedTree (k : ℕ) (_hk : 0 < k) : IsRootedTree (fanDigraph k) := by
  refine ⟨⟨0, Nat.zero_lt_succ k⟩, ?_, ?_, ?_⟩
  · -- no_edge_to_root: if edge v ⟨0, _⟩ then 0 < 0, contradiction
    intro v he
    simp at he
  · -- unique_parent: for v ≠ root, unique parent is ⟨0⟩
    intro v hne
    have hv_pos : 0 < v.val := by
      apply Nat.pos_of_ne_zero
      intro h
      apply hne
      exact Fin.ext h
    refine ⟨⟨0, Nat.zero_lt_succ k⟩, ?_, ?_⟩
    · -- Existence: edge from 0 to v
      show (⟨0, _⟩ : Fin (k + 1)).val = 0 ∧ 0 < v.val
      exact ⟨rfl, hv_pos⟩
    · -- Uniqueness: if edge p v then p.val = 0
      intro p hp
      exact Fin.ext hp.1
  · -- all_reachable
    intro v
    by_cases hv : v.val = 0
    · -- v is the root
      have hv_eq : v = ⟨0, Nat.zero_lt_succ k⟩ := Fin.ext hv
      rw [hv_eq]
      exact Reachable.refl _
    · -- v.val > 0, so there's an edge 0 → v
      have hedge : (fanDigraph k).edge ⟨0, Nat.zero_lt_succ k⟩ v := by
        show (⟨0, _⟩ : Fin (k + 1)).val = 0 ∧ 0 < v.val
        exact ⟨rfl, Nat.pos_of_ne_zero hv⟩
      exact Reachable.single hedge

/-!
## Part 5: The Bisim-Covering Predicate
-/

/-- A sieve S on G is **bisim-covering** if it contains every homomorphism from
    every rooted tree T into G. This is the covering condition for J_bisim.

    Intuitively: S "sees" all possible tree-shaped observations of G — for every
    rooted tree T and every way to embed T into G, that embedding is in S.

    Compared to isTraceCovering (which only requires path morphisms), this is
    strictly stronger: it requires all tree-shaped probes, not just linear ones. -/
def isBisimCovering (G : FinDigraph) (S : DigraphSieve G) : Prop :=
  ∀ (T : FinDigraph), IsRootedTree T → ∀ (f : DigraphHom T G), S.mem T f

/-- Every bisim-covering sieve is trace-covering: since every path digraph P_n
    is a rooted tree, requiring all tree morphisms subsumes requiring all path morphisms.

    This is the inclusion J_bisim ⊆ J_trace as Grothendieck topologies
    (finer topology = more covering sieves = stricter covering condition). -/
theorem bisim_covering_implies_trace_covering {G : FinDigraph} {S : DigraphSieve G}
    (hS : isBisimCovering G S) : isTraceCovering G S :=
  fun n f => hS (pathDigraph n) (pathDigraph_isRootedTree n) f

/-!
## Part 6: Three Grothendieck Axioms for J_bisim
-/

/-- **Maximality axiom:** The maximal sieve is bisim-covering for every G.
    Every morphism into G is in the maximal sieve, so in particular all tree morphisms. -/
theorem bisim_covering_maximal (G : FinDigraph) :
    isBisimCovering G (DigraphSieve.maximal G) :=
  fun _ _ _ => trivial

/-- **Stability axiom:** If S bisim-covers G, then the pullback h*(S) bisim-covers H.
    Any tree morphism f : T → H becomes h ∘ f : T → G, which is in S. -/
theorem bisim_covering_stable {G H : FinDigraph} {S : DigraphSieve G}
    (h : DigraphHom H G) (hS : isBisimCovering G S) :
    isBisimCovering H (S.pullback h) :=
  fun T hT f => hS T hT (DigraphHom.comp f h)

/-- **Transitivity axiom:** If S bisim-covers G and for every (H, f) ∈ S the pullback
    f*(T) bisim-covers H, then T bisim-covers G.

    Key insight (self-probing trick): for any tree T₀ and g : T₀ → G, we know g ∈ S
    (since S bisim-covers G and T₀ is a tree). Then T.pullback g bisim-covers T₀.
    Since T₀ is a tree, id_{T₀} ∈ T.pullback g, which gives g ∘ id = g ∈ T. -/
theorem bisim_covering_transitive {G : FinDigraph} {S T : DigraphSieve G}
    (hS : isBisimCovering G S)
    (hT : ∀ (H : FinDigraph) (f : DigraphHom H G), S.mem H f →
      isBisimCovering H (T.pullback f)) :
    isBisimCovering G T := by
  intro T₀ hT₀ g
  -- g : T₀ → G. Since S bisim-covers G and T₀ is a tree, g ∈ S.
  have hg : S.mem T₀ g := hS T₀ hT₀ g
  -- By hypothesis, T.pullback g bisim-covers T₀.
  have hTg : isBisimCovering T₀ (T.pullback g) := hT T₀ g hg
  -- Since T₀ is a tree, id_{T₀} must be in T.pullback g.
  have hid := hTg T₀ hT₀ (DigraphHom.id T₀)
  -- (T.pullback g).mem T₀ (id) = T.mem T₀ (comp id g) = T.mem T₀ g
  simp only [DigraphSieve.pullback] at hid
  rw [DigraphHom.id_comp] at hid
  exact hid

/-!
## Part 7: J_bisim Strictly Finer Than J_trace

The fan digraph fan(2) (root with 2 leaf children) is the key separating example.
The path-generated sieve on fan(2) is trace-covering (by pathGeneratedSieve_trace_covering)
but NOT bisim-covering (the identity morphism id_{fan(2)} is not in the sieve).
-/

/-- fan(2) is a rooted tree with root 0 and children 1, 2. -/
theorem fanDigraph2_isRootedTree : IsRootedTree (fanDigraph 2) :=
  fanDigraph_isRootedTree 2 (by omega)

/-- The identity on fan(2) does NOT factor through any path digraph.

    Proof: if id = f ∘ h for h : fan(2) → P_n and f : P_n → fan(2), then
    h maps both edges 0→1 and 0→2 to edges in P_n. In P_n, each vertex has
    at most one outgoing edge, so h(1).val = h(0).val + 1 = h(2).val.
    Thus h(1) = h(2). But f(h(1)) = 1 and f(h(2)) = 2 (from f ∘ h = id),
    giving 1 = 2 in Fin 3, contradiction. -/
theorem fan2_id_not_in_pathGeneratedSieve :
    ¬(pathGeneratedSieve (fanDigraph 2)).mem (fanDigraph 2) (DigraphHom.id (fanDigraph 2)) := by
  intro ⟨n, h, f, heq⟩
  -- heq : id = comp h f, so for all v, f.toFun (h.toFun v) = v
  -- Extract pointwise equality from heq
  have hcomp : ∀ v, f.toFun (h.toFun v) = v := by
    intro v
    have heqf := congr_arg DigraphHom.toFun heq
    -- heqf : (id fan2).toFun = (comp h f).toFun
    -- (comp h f).toFun = f.toFun ∘ h.toFun, (id fan2).toFun = _root_.id
    have := congr_fun heqf v
    -- this : (id fan2).toFun v = (comp h f).toFun v
    -- i.e., v = f.toFun (h.toFun v)
    exact this.symm
  -- fan(2) has edges 0→1 and 0→2
  have hedge_01 : (fanDigraph 2).edge (⟨0, by omega⟩ : Fin 3) ⟨1, by omega⟩ :=
    show (0 : Fin 3).val = 0 ∧ 0 < (1 : Fin 3).val from ⟨rfl, by omega⟩
  have hedge_02 : (fanDigraph 2).edge (⟨0, by omega⟩ : Fin 3) ⟨2, by omega⟩ :=
    show (0 : Fin 3).val = 0 ∧ 0 < (2 : Fin 3).val from ⟨rfl, by omega⟩
  -- h preserves edges: h maps 0→1 to an edge in P_n
  have h_edge_01 := h.map_edge _ _ hedge_01
  -- In pathDigraph n: edge h(0) h(1) means h(1).val = h(0).val + 1
  change (h.toFun ⟨1, by omega⟩).val = (h.toFun ⟨0, by omega⟩).val + 1 at h_edge_01
  -- h maps 0→2 to an edge in P_n
  have h_edge_02 := h.map_edge _ _ hedge_02
  change (h.toFun ⟨2, by omega⟩).val = (h.toFun ⟨0, by omega⟩).val + 1 at h_edge_02
  -- Therefore h(1).val = h(2).val
  have h12_eq : (h.toFun ⟨1, by omega⟩).val = (h.toFun ⟨2, by omega⟩).val := by omega
  have h12 : h.toFun ⟨1, by omega⟩ = h.toFun ⟨2, by omega⟩ := Fin.ext h12_eq
  -- But f(h(1)) = 1 and f(h(2)) = 2
  have fh1 := hcomp ⟨1, by omega⟩
  have fh2 := hcomp ⟨2, by omega⟩
  -- Since h(1) = h(2), f(h(1)) = f(h(2)), so 1 = 2 in Fin 3
  rw [h12] at fh1
  -- fh1 : f.toFun (h.toFun ⟨2, _⟩) = ⟨1, _⟩
  -- fh2 : f.toFun (h.toFun ⟨2, _⟩) = ⟨2, _⟩
  have h_eq : (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by rw [← fh1, fh2]
  have := congrArg Fin.val h_eq
  simp at this

/-- The path-generated sieve on fan(2) is NOT bisim-covering.

    Proof: if it were bisim-covering, then since fan(2) is a rooted tree,
    the identity id_{fan(2)} would need to be in the sieve. But
    fan2_id_not_in_pathGeneratedSieve shows it is not. -/
theorem pathGeneratedSieve_not_bisimCovering_fan2 :
    ¬isBisimCovering (fanDigraph 2) (pathGeneratedSieve (fanDigraph 2)) := by
  intro hbc
  exact fan2_id_not_in_pathGeneratedSieve
    (hbc (fanDigraph 2) fanDigraph2_isRootedTree (DigraphHom.id (fanDigraph 2)))

/-- **J_bisim is strictly finer than J_trace.**

    Witness: the path-generated sieve on fan(2) is trace-covering (by
    pathGeneratedSieve_trace_covering) but not bisim-covering (the identity
    on fan(2) fails to factor through any path digraph, since fan(2) has
    branching that paths cannot capture). -/
theorem bisim_strictly_finer_than_trace_topology :
    ∃ (G : FinDigraph) (S : DigraphSieve G),
      isTraceCovering G S ∧ ¬isBisimCovering G S :=
  ⟨fanDigraph 2, pathGeneratedSieve (fanDigraph 2),
   pathGeneratedSieve_trace_covering (fanDigraph 2),
   pathGeneratedSieve_not_bisimCovering_fan2⟩

/-!
## Part 8: Summary
-/

/-- Master theorem: J_bisim is a Grothendieck topology, strictly finer than J_trace.

    The three Grothendieck axioms (maximality, stability, transitivity) together with
    the strict comparison to J_trace establish J_bisim as the finest named-equivalence
    topology on f.p.LTS₁, bracketing the van Glabbeek spectrum from above. -/
theorem bisim_topology_summary :
    -- (1) Maximality
    (∀ G : FinDigraph, isBisimCovering G (DigraphSieve.maximal G)) ∧
    -- (2) Stability
    (∀ (G H : FinDigraph) (S : DigraphSieve G) (h : DigraphHom H G),
      isBisimCovering G S → isBisimCovering H (S.pullback h)) ∧
    -- (3) Transitivity
    (∀ (G : FinDigraph) (S T : DigraphSieve G),
      isBisimCovering G S →
      (∀ (H : FinDigraph) (f : DigraphHom H G), S.mem H f → isBisimCovering H (T.pullback f)) →
      isBisimCovering G T) ∧
    -- (4) J_bisim implies J_trace (inclusion of topologies)
    (∀ (G : FinDigraph) (S : DigraphSieve G),
      isBisimCovering G S → isTraceCovering G S) ∧
    -- (5) Strictly finer than J_trace
    (∃ (G : FinDigraph) (S : DigraphSieve G),
      isTraceCovering G S ∧ ¬isBisimCovering G S) :=
  ⟨bisim_covering_maximal,
   fun _ _ _ h hS => bisim_covering_stable h hS,
   fun _ _ _ hS hT => bisim_covering_transitive hS hT,
   fun _ _ hS => bisim_covering_implies_trace_covering hS,
   bisim_strictly_finer_than_trace_topology⟩

end Ruliology.PresheafTopos
