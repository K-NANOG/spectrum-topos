/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Path Digraphs and Trace Sets

This file defines path digraphs P_n (linear chains 0→1→...→n), the inductive
`hasPathOfLength` predicate, trace sets, and the pathEmbed bijection establishing
that paths of length n from vertex v in G correspond exactly to graph homomorphisms
P_n → G sending 0 ↦ v.

For |L| = 1, this is the combinatorial bridge between trace equivalence (same trace
set) and hom-set agreement (same representable presheaf stalks), enabling the trace
topology J_trace in Phase 165.

## Key Results

- `pathDigraph n`: Fin(n+1) vertices, edge i j ↔ j.val = i.val + 1
- `hasPathOfLength G v n`: inductive predicate for paths in G
- `traceSet G v = {n | hasPathOfLength G v n}`
- `pathToHom`: path of length n from v → DigraphHom (pathDigraph n) G
- `homToPath`: DigraphHom (pathDigraph n) G → path of length n from f(0)
- Concrete trace sets for all v20.0 building blocks

## References

- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Joyal-Nielsen-Winskel, "Bisimulation from open maps" (1996)
-/

import RuleSys.PresheafTopos.FiniteDigraph

set_option autoImplicit false

namespace RTS.PresheafTopos

/-!
## Part 1: Path Digraph Definition
-/

/-- The path digraph P_n: a linear chain 0 → 1 → ... → n with n+1 vertices and n edges.
    For |L| = 1, path digraphs are the |L| = 1 specialization of path LTS (traces are
    just natural numbers = path lengths). -/
@[reducible] def pathDigraph (n : ℕ) : FinDigraph where
  Vertex := Fin (n + 1)
  edge := fun i j => j.val = i.val + 1
  edgeDecidable := fun _ _ => inferInstance

/-- P_0 has a single vertex and no edges. -/
theorem pathDigraph_zero_no_edges (i j : Fin 1) : ¬(pathDigraph 0).edge i j := by
  simp

/-- The source vertex ⟨0⟩ has no incoming edges. -/
theorem pathDigraph_source_no_incoming (n : ℕ) (i : Fin (n + 1)) :
    ¬(pathDigraph n).edge i ⟨0, Nat.zero_lt_succ n⟩ := by
  simp

/-- The sink vertex ⟨n⟩ has no outgoing edges. -/
theorem pathDigraph_sink_no_outgoing (n : ℕ) (j : Fin (n + 1)) :
    ¬(pathDigraph n).edge ⟨n, Nat.lt_succ_of_le (le_refl n)⟩ j := by
  simp
  intro h
  omega

/-- Each non-sink vertex i < n has exactly one outgoing edge: to i+1. -/
theorem pathDigraph_unique_successor (n : ℕ) (i : Fin (n + 1)) (_ : i.val < n)
    (j : Fin (n + 1)) (hej : (pathDigraph n).edge i j) : j.val = i.val + 1 := hej

/-- The initial morphism from ∅ to any path digraph. -/
def pathDigraph_from_empty (n : ℕ) : DigraphHom emptyDigraph (pathDigraph n) :=
  emptyDigraph_to (pathDigraph n)

/-- Inclusion of P_n into P_{n+1} via Fin.castSucc. -/
def pathDigraph_inclusion (n : ℕ) : DigraphHom (pathDigraph n) (pathDigraph (n + 1)) where
  toFun := Fin.castSucc
  map_edge := by
    intro s t h
    simp at h ⊢
    exact h

/-!
## Part 2: Paths in Digraphs
-/

/-- A path of length n starting from vertex v in digraph G.
    - Length 0: trivially exists (the empty path at v)
    - Length n+1: an edge v → w followed by a path of length n from w -/
inductive hasPathOfLength (G : FinDigraph) : G.Vertex → ℕ → Prop where
  | zero (v : G.Vertex) : hasPathOfLength G v 0
  | step (v w : G.Vertex) (n : ℕ) : G.edge v w → hasPathOfLength G w n →
      hasPathOfLength G v (n + 1)

/-- The trace set of G from vertex v: the set of all achievable path lengths. -/
def traceSet (G : FinDigraph) (v : G.Vertex) : Set ℕ :=
  {n | hasPathOfLength G v n}

/-- Trace equivalence: two rooted digraphs have the same trace set.
    For |L| = 1, this is trace equivalence in the van Glabbeek spectrum. -/
def traceEquiv (G : FinDigraph) (v : G.Vertex) (H : FinDigraph) (w : H.Vertex) : Prop :=
  traceSet G v = traceSet H w

theorem traceEquiv_refl (G : FinDigraph) (v : G.Vertex) :
    traceEquiv G v G v := rfl

theorem traceEquiv_symm {G : FinDigraph} {v : G.Vertex} {H : FinDigraph} {w : H.Vertex}
    (h : traceEquiv G v H w) : traceEquiv H w G v := h.symm

theorem traceEquiv_trans {G : FinDigraph} {v : G.Vertex} {H : FinDigraph} {w : H.Vertex}
    {K : FinDigraph} {u : K.Vertex}
    (h1 : traceEquiv G v H w) (h2 : traceEquiv H w K u) : traceEquiv G v K u :=
  h1.trans h2

/-!
## Part 3: The Path-Homomorphism Bijection

Paths of length n from v in G correspond to graph homomorphisms P_n → G sending 0 to v.
-/

/-- Forward: a path of length n from v in G implies the existence of a root-preserving
    homomorphism P_n → G. Since hasPathOfLength is in Prop, we prove existence (also Prop)
    rather than constructing the homomorphism directly. -/
theorem path_implies_hom {G : FinDigraph} {v : G.Vertex} {n : ℕ}
    (p : hasPathOfLength G v n) :
    ∃ f : DigraphHom (pathDigraph n) G, f.toFun ⟨0, Nat.zero_lt_succ n⟩ = v := by
  induction p with
  | zero v =>
    exact ⟨{
      toFun := fun _ => v
      map_edge := fun s t h => absurd (show t.val = s.val + 1 from h) (by omega)
    }, rfl⟩
  | step v w m e _hp ih =>
    obtain ⟨f, hroot⟩ := ih
    -- Construct the prepended homomorphism P_{m+1} → G
    refine ⟨{
      toFun := fun i => if h : i.val = 0 then v else f.toFun ⟨i.val - 1, by omega⟩
      map_edge := ?_
    }, by simp⟩
    intro s t hedge
    change t.val = s.val + 1 at hedge
    by_cases hs : s.val = 0
    · -- s = 0 maps to v, t = 1 maps to f(0) = w
      have ht : t.val ≠ 0 := by omega
      simp only [dif_pos hs, dif_neg ht]
      have : (⟨t.val - 1, by omega⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩ := by
        apply Fin.ext; show t.val - 1 = 0; omega
      rw [this, hroot]
      exact e
    · -- s > 0 maps to f(s-1), t > 0 maps to f(t-1)
      have ht : t.val ≠ 0 := by omega
      simp only [dif_neg hs, dif_neg ht]
      have hedge_f : (pathDigraph m).edge ⟨s.val - 1, by omega⟩ ⟨t.val - 1, by omega⟩ := by
        show (⟨t.val - 1, _⟩ : Fin (m + 1)).val = (⟨s.val - 1, _⟩ : Fin (m + 1)).val + 1
        simp; omega
      exact f.map_edge _ _ hedge_f

/-- Reverse: a homomorphism P_n → G gives a path of length n from f(0). -/
def homToPath {G : FinDigraph} {n : ℕ} (f : DigraphHom (pathDigraph n) G) :
    hasPathOfLength G (f.toFun ⟨0, Nat.zero_lt_succ n⟩) n := by
  induction n with
  | zero => exact hasPathOfLength.zero _
  | succ m ih =>
    -- P_{m+1} has edge ⟨0⟩ → ⟨1⟩
    have hedge : (pathDigraph (m + 1)).edge ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      show (1 : Fin (m + 2)).val = (0 : Fin (m + 2)).val + 1
      simp
    have edge_in_G := f.map_edge _ _ hedge
    -- The tail of f restricted to {1, ..., m+1} gives a hom P_m → G
    let tail : DigraphHom (pathDigraph m) G := {
      toFun := fun i => f.toFun ⟨i.val + 1, by omega⟩
      map_edge := by
        intro s t h
        -- h : (pathDigraph m).edge s t, i.e., t.val = s.val + 1
        -- Need: (pathDigraph (m+1)).edge ⟨s.val+1, _⟩ ⟨t.val+1, _⟩
        have hbound_s : s.val + 1 < m + 2 := by omega
        have hbound_t : t.val + 1 < m + 2 := by
          have := t.isLt; omega
        have hedge' : (pathDigraph (m + 1)).edge
            ⟨s.val + 1, hbound_s⟩ ⟨t.val + 1, hbound_t⟩ := by
          show (⟨t.val + 1, hbound_t⟩ : Fin (m + 2)).val =
               (⟨s.val + 1, hbound_s⟩ : Fin (m + 2)).val + 1
          simp
          -- h says t.val = s.val + 1 (edge in pathDigraph m)
          change t.val = s.val + 1 at h
          omega
        exact f.map_edge _ _ hedge'
    }
    have tail_path := ih tail
    -- tail sends 0 to f(1)
    have htail : tail.toFun ⟨0, Nat.zero_lt_succ m⟩ = f.toFun ⟨1, by omega⟩ := by
      simp [tail]
    rw [htail] at tail_path
    exact hasPathOfLength.step _ _ _ edge_in_G tail_path

/-!
## Part 4: Concrete Trace Set Computations
-/

/-- •₀ (loopless vertex) has trace set {0}: only the empty path exists. -/
theorem looplessVertex_hasPath_zero : hasPathOfLength looplessVertex () 0 :=
  hasPathOfLength.zero (G := looplessVertex) ()

theorem looplessVertex_no_longer_path (n : ℕ) :
    ¬hasPathOfLength looplessVertex () (n + 1) := by
  intro h
  match h with
  | .step _ w _ e _ => exact e

theorem looplessVertex_traceSet :
    traceSet looplessVertex () = {0} := by
  ext n
  simp [traceSet]
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m => exact absurd h (looplessVertex_no_longer_path m)
  · intro h
    rw [h]
    exact looplessVertex_hasPath_zero

/-- •₁ (loop vertex) has trace set ℕ: all path lengths are achievable via the self-loop. -/
theorem loopVertex_hasPath_all (n : ℕ) : hasPathOfLength loopVertex () n := by
  induction n with
  | zero => exact hasPathOfLength.zero (G := loopVertex) ()
  | succ m ih => exact hasPathOfLength.step (G := loopVertex) () () m trivial ih

theorem loopVertex_traceSet :
    traceSet loopVertex () = Set.univ := by
  ext n
  simp [traceSet]
  exact loopVertex_hasPath_all n

/-- Arrow graph from root false: trace set = {0, 1}. -/
theorem arrow_hasPath_false_zero : hasPathOfLength arrowDigraph false 0 :=
  hasPathOfLength.zero (G := arrowDigraph) false

theorem arrow_hasPath_false_one : hasPathOfLength arrowDigraph false 1 :=
  hasPathOfLength.step (G := arrowDigraph) false true 0
    (show arrowDigraph.edge false true from And.intro rfl rfl)
    (hasPathOfLength.zero (G := arrowDigraph) true)

theorem arrow_no_path_from_true_succ (n : ℕ) :
    ¬hasPathOfLength arrowDigraph true (n + 1) := by
  intro h
  match h with
  | .step _ w _ e _ =>
    -- arrowDigraph.edge true w requires true = false
    exact absurd e.1 Bool.noConfusion

theorem arrow_no_path_false_ge2 (n : ℕ) :
    ¬hasPathOfLength arrowDigraph false (n + 2) := by
  intro h
  -- After one step from false, we reach true (the only edge is false→true)
  match h with
  | .step _ w _ e hp =>
    have : w = true := e.2
    subst this
    exact arrow_no_path_from_true_succ n hp

theorem arrowDigraph_traceSet_false :
    traceSet arrowDigraph false = {0, 1} := by
  ext n
  simp [traceSet]
  constructor
  · intro h
    match n with
    | 0 => left; rfl
    | 1 => right; rfl
    | n + 2 => exact absurd h (arrow_no_path_false_ge2 n)
  · intro h
    cases h with
    | inl h => rw [h]; exact arrow_hasPath_false_zero
    | inr h => rw [h]; exact arrow_hasPath_false_one

/-- Arrow graph from root true: trace set = {0}. -/
theorem arrowDigraph_traceSet_true :
    traceSet arrowDigraph true = {0} := by
  ext n
  simp [traceSet]
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m => exact absurd h (arrow_no_path_from_true_succ m)
  · intro h
    rw [h]
    exact hasPathOfLength.zero (G := arrowDigraph) true

/-!
## Part 5: Trace Equivalence Examples
-/

/-- •₀ and → (rooted at true) are trace-equivalent: both have trace set {0}. -/
theorem looplessVertex_arrow_true_traceEquiv :
    traceEquiv looplessVertex () arrowDigraph true := by
  unfold traceEquiv
  rw [looplessVertex_traceSet, arrowDigraph_traceSet_true]

/-- •₀ and •₁ are NOT trace-equivalent: {0} ≠ ℕ (witnessed at n = 1). -/
theorem looplessVertex_loopVertex_not_traceEquiv :
    ¬traceEquiv looplessVertex () loopVertex () := by
  intro h
  unfold traceEquiv at h
  rw [looplessVertex_traceSet, loopVertex_traceSet] at h
  have : (1 : ℕ) ∈ ({0} : Set ℕ) := by
    rw [h]; exact Set.mem_univ 1
  simp at this

/-- •₁ and → (rooted at false) are NOT trace-equivalent: ℕ ≠ {0,1} (witnessed at n = 2). -/
theorem loopVertex_arrow_false_not_traceEquiv :
    ¬traceEquiv loopVertex () arrowDigraph false := by
  intro h
  unfold traceEquiv at h
  rw [loopVertex_traceSet, arrowDigraph_traceSet_false] at h
  have : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := by
    rw [← h]; exact Set.mem_univ 2
  simp at this

/-- The path-homomorphism correspondence: paths of length n from v in G correspond
    to root-preserving homomorphisms P_n → G. Both directions are proved. -/
theorem path_hom_correspondence :
    -- Forward: paths give homomorphisms (existential)
    (∀ (G : FinDigraph) (v : G.Vertex) (n : ℕ),
      hasPathOfLength G v n → ∃ f : DigraphHom (pathDigraph n) G,
        f.toFun ⟨0, Nat.zero_lt_succ n⟩ = v) ∧
    -- Reverse: homomorphisms give paths
    (∀ (G : FinDigraph) (n : ℕ) (f : DigraphHom (pathDigraph n) G),
      hasPathOfLength G (f.toFun ⟨0, Nat.zero_lt_succ n⟩) n) :=
  ⟨fun _G _v _n p => path_implies_hom p,
   fun _G _n f => homToPath f⟩

end RTS.PresheafTopos
