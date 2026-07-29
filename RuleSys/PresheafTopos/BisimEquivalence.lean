/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Bisimulation Equivalence for Finite Directed Graphs

This file defines bisimulation for FinDigraph via the standard zig-zag condition,
proves it forms an equivalence relation, and establishes that bisimulation strictly
refines trace equivalence for |L| = 1.

## Key Results

- `isBisimulation`: forward + backward zig-zag condition on a relation R
- `bisimEquiv`: two rooted digraphs are bisimilar iff connected by a bisimulation
- `bisimEquiv_refl`, `bisimEquiv_symm`, `bisimEquiv_trans`: equivalence relation
- `bisim_implies_trace`: bisimulation equivalence implies trace equivalence
- `bisim_strictly_finer_than_trace`: trace-equivalent pair that is NOT bisimilar
- v20.0 bisimulation class computations for small objects

## Mathematical Significance

Bisimulation is the finest named behavioral equivalence in the van Glabbeek spectrum.
For |L| = 1, trace equivalence and bisimulation are the two endpoints that bracket
all 13 named equivalences. This file proves the separation is strict even for |L| = 1,
using the asymmetric-branch vs chain example.

## References

- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Park, "Concurrency and automata on infinite sequences" (1981)
- Milner, "Communication and Concurrency" (1989)
-/

import RuleSys.PresheafTopos.PathDigraph

set_option autoImplicit false

namespace RTS.PresheafTopos

/-!
## Part 1: Bisimulation Definition
-/

/-- A relation R : G.Vertex -> H.Vertex -> Prop is a bisimulation between digraphs G and H
    if it satisfies the zig-zag condition:
    - Forward (zig): if R v w and G has edge v -> v', then H has edge w -> w' with R v' w'
    - Backward (zag): if R v w and H has edge w -> w', then G has edge v -> v' with R v' w'

    This is the standard Park-Milner definition of bisimulation. -/
structure isBisimulation (G H : FinDigraph) (R : G.Vertex → H.Vertex → Prop) : Prop where
  /-- Forward condition (zig): G-edges can be matched by H-edges -/
  forward : ∀ (v : G.Vertex) (w : H.Vertex), R v w →
    ∀ (v' : G.Vertex), G.edge v v' → ∃ (w' : H.Vertex), H.edge w w' ∧ R v' w'
  /-- Backward condition (zag): H-edges can be matched by G-edges -/
  backward : ∀ (v : G.Vertex) (w : H.Vertex), R v w →
    ∀ (w' : H.Vertex), H.edge w w' → ∃ (v' : G.Vertex), G.edge v v' ∧ R v' w'

/-- Two rooted digraphs are bisimulation equivalent if there exists a bisimulation R
    relating their roots. -/
def bisimEquiv (G : FinDigraph) (v : G.Vertex) (H : FinDigraph) (w : H.Vertex) : Prop :=
  ∃ R : G.Vertex → H.Vertex → Prop, isBisimulation G H R ∧ R v w

/-!
## Part 2: Bisimulation is an Equivalence Relation
-/

/-- Bisimulation equivalence is reflexive: the identity relation is a bisimulation. -/
theorem bisimEquiv_refl (G : FinDigraph) (v : G.Vertex) :
    bisimEquiv G v G v := by
  refine ⟨fun a b => a = b, ?_, rfl⟩
  exact {
    forward := fun v w hvw v' hev => by
      subst hvw; exact ⟨v', hev, rfl⟩
    backward := fun v w hvw w' hew => by
      subst hvw; exact ⟨w', hew, rfl⟩
  }

/-- Bisimulation equivalence is symmetric: flipping the relation swaps forward and backward. -/
theorem bisimEquiv_symm {G : FinDigraph} {v : G.Vertex} {H : FinDigraph} {w : H.Vertex}
    (h : bisimEquiv G v H w) : bisimEquiv H w G v := by
  obtain ⟨R, hR, hRvw⟩ := h
  refine ⟨fun w' v' => R v' w', ?_, hRvw⟩
  exact {
    forward := fun w' v' hRvw' w'' hew => by
      obtain ⟨v'', hev, hRv'w''⟩ := hR.backward v' w' hRvw' w'' hew
      exact ⟨v'', hev, hRv'w''⟩
    backward := fun w' v' hRvw' v'' hev => by
      obtain ⟨w'', hew, hRv''w''⟩ := hR.forward v' w' hRvw' v'' hev
      exact ⟨w'', hew, hRv''w''⟩
  }

/-- Bisimulation equivalence is transitive: relational composition of bisimulations
    is again a bisimulation. -/
theorem bisimEquiv_trans {G : FinDigraph} {v : G.Vertex}
    {H : FinDigraph} {w : H.Vertex}
    {K : FinDigraph} {u : K.Vertex}
    (h1 : bisimEquiv G v H w) (h2 : bisimEquiv H w K u) :
    bisimEquiv G v K u := by
  obtain ⟨R₁, hR₁, hR₁vw⟩ := h1
  obtain ⟨R₂, hR₂, hR₂wu⟩ := h2
  refine ⟨fun v' u' => ∃ w' : H.Vertex, R₁ v' w' ∧ R₂ w' u', ?_, ⟨w, hR₁vw, hR₂wu⟩⟩
  exact {
    forward := fun v' u' ⟨w', hR₁vw', hR₂w'u'⟩ v'' hev => by
      obtain ⟨w'', hew, hR₁v''w''⟩ := hR₁.forward v' w' hR₁vw' v'' hev
      obtain ⟨u'', heu, hR₂w''u''⟩ := hR₂.forward w' u' hR₂w'u' w'' hew
      exact ⟨u'', heu, ⟨w'', hR₁v''w'', hR₂w''u''⟩⟩
    backward := fun v' u' ⟨w', hR₁vw', hR₂w'u'⟩ u'' heu => by
      obtain ⟨w'', hew, hR₂w''u''⟩ := hR₂.backward w' u' hR₂w'u' u'' heu
      obtain ⟨v'', hev, hR₁v''w''⟩ := hR₁.backward v' w' hR₁vw' w'' hew
      exact ⟨v'', hev, ⟨w'', hR₁v''w'', hR₂w''u''⟩⟩
  }

/-!
## Part 3: Bisimulation Implies Trace Equivalence
-/

/-- If R is a bisimulation with R v w, then paths from v in G can be matched by
    paths from w in H. -/
private theorem bisim_path_forward {G H : FinDigraph} {R : G.Vertex → H.Vertex → Prop}
    (hR : isBisimulation G H R) {v : G.Vertex} {w : H.Vertex} (hRvw : R v w)
    {n : ℕ} (hp : hasPathOfLength G v n) : hasPathOfLength H w n := by
  induction hp generalizing w with
  | zero _ => exact hasPathOfLength.zero w
  | step v v' m hev _hp' ih =>
    obtain ⟨w', hew, hRv'w'⟩ := hR.forward v w hRvw v' hev
    exact hasPathOfLength.step w w' m hew (ih hRv'w')

/-- Bisimulation equivalence implies trace equivalence: if two rooted digraphs are
    bisimilar, they have the same trace set (same set of achievable path lengths). -/
theorem bisim_implies_trace {G : FinDigraph} {v : G.Vertex}
    {H : FinDigraph} {w : H.Vertex}
    (h : bisimEquiv G v H w) : traceEquiv G v H w := by
  obtain ⟨R, hR, hRvw⟩ := h
  ext n
  simp only [traceSet, Set.mem_setOf_eq]
  constructor
  · exact bisim_path_forward hR hRvw
  · -- Backward: use the flipped relation
    have hR' : isBisimulation H G (fun w' v' => R v' w') := {
      forward := fun w' v' hR' w'' hew => by
        obtain ⟨v'', hev, hRv''w''⟩ := hR.backward v' w' hR' w'' hew
        exact ⟨v'', hev, hRv''w''⟩
      backward := fun w' v' hR' v'' hev => by
        obtain ⟨w'', hew, hRv''w''⟩ := hR.forward v' w' hR' v'' hev
        exact ⟨w'', hew, hRv''w''⟩
    }
    exact bisim_path_forward hR' hRvw

/-!
## Part 4: Bisim-Separating Example (trace != bisim for |L|=1)

We define two digraphs that are trace-equivalent but NOT bisimilar:
- asymBranchDigraph: root 0 with children 1, 2; child 1 has child 3; child 2 is a leaf
- chainDigraph2: root 0 with child 1, child 1 has child 2 (linear chain of length 2)

Both have trace set {0, 1, 2}, but they are not bisimilar because the asymmetric
branching structure at vertex 0 in asymBranch cannot be matched by chain's linear structure.
-/

/-- The asymmetric branch digraph: 4 vertices, edges 0->1, 0->2, 1->3.
    Root 0 has two children: child 1 (with successor 3) and child 2 (leaf). -/
@[reducible] def asymBranchDigraph : FinDigraph where
  Vertex := Fin 4
  edge := fun s t =>
    (s.val = 0 ∧ t.val = 1) ∨ (s.val = 0 ∧ t.val = 2) ∨ (s.val = 1 ∧ t.val = 3)
  edgeDecidable := fun _ _ => inferInstance

/-- The chain digraph of length 2: 3 vertices, edges 0->1, 1->2.
    A linear chain from root 0 to leaf 2. -/
@[reducible] def chainDigraph2 : FinDigraph where
  Vertex := Fin 3
  edge := fun s t =>
    (s.val = 0 ∧ t.val = 1) ∨ (s.val = 1 ∧ t.val = 2)
  edgeDecidable := fun _ _ => inferInstance

-- Helper: edge proofs for asymBranchDigraph
private theorem asymBranch_edge_01 :
    asymBranchDigraph.edge (⟨0, by omega⟩ : Fin 4) ⟨1, by omega⟩ := by
  show (0 = 0 ∧ 1 = 1) ∨ _; exact Or.inl ⟨rfl, rfl⟩

private theorem asymBranch_edge_13 :
    asymBranchDigraph.edge (⟨1, by omega⟩ : Fin 4) ⟨3, by omega⟩ := by
  show _ ∨ _ ∨ (1 = 1 ∧ 3 = 3); exact Or.inr (Or.inr ⟨rfl, rfl⟩)

-- Helper: edge proofs for chainDigraph2
private theorem chain2_edge_01 :
    chainDigraph2.edge (⟨0, by omega⟩ : Fin 3) ⟨1, by omega⟩ := by
  show (0 = 0 ∧ 1 = 1) ∨ _; exact Or.inl ⟨rfl, rfl⟩

private theorem chain2_edge_12 :
    chainDigraph2.edge (⟨1, by omega⟩ : Fin 3) ⟨2, by omega⟩ := by
  show _ ∨ (1 = 1 ∧ 2 = 2); exact Or.inr ⟨rfl, rfl⟩

/-- asymBranchDigraph has a path of length 0 from root 0. -/
private theorem asymBranch_path0 :
    hasPathOfLength asymBranchDigraph ⟨0, by omega⟩ 0 :=
  hasPathOfLength.zero _

/-- asymBranchDigraph has a path of length 1 from root 0 (via edge 0->1). -/
private theorem asymBranch_path1 :
    hasPathOfLength asymBranchDigraph ⟨0, by omega⟩ 1 :=
  hasPathOfLength.step _ _ 0 asymBranch_edge_01 (hasPathOfLength.zero _)

/-- asymBranchDigraph has a path of length 2 from root 0 (via 0->1->3). -/
private theorem asymBranch_path2 :
    hasPathOfLength asymBranchDigraph ⟨0, by omega⟩ 2 :=
  hasPathOfLength.step _ _ 1 asymBranch_edge_01
    (hasPathOfLength.step _ _ 0 asymBranch_edge_13 (hasPathOfLength.zero _))

/-- No vertex in asymBranchDigraph has outgoing edges from vertices 2 or 3. -/
private theorem asymBranch_no_edge_from_2 {t : Fin 4} :
    ¬asymBranchDigraph.edge ⟨2, by omega⟩ t := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all

private theorem asymBranch_no_edge_from_3 {t : Fin 4} :
    ¬asymBranchDigraph.edge ⟨3, by omega⟩ t := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all

/-- asymBranchDigraph has no path of length >= 3 from root 0. -/
private theorem asymBranch_no_path_ge3 (n : ℕ) :
    ¬hasPathOfLength asymBranchDigraph ⟨0, by omega⟩ (n + 3) := by
  intro h
  match h with
  | .step _ w _ e hp =>
    -- e : edge 0 w, w.val = 1 or w.val = 2
    rcases e with ⟨_, hw⟩ | ⟨_, hw⟩ | ⟨h0, _⟩
    · -- w.val = 1
      match hp with
      | .step _ w₂ _ e₂ hp₂ =>
        rcases e₂ with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, hw₂⟩
        · simp_all
        · simp_all
        · -- w₂.val = 3
          match hp₂ with
          | .step _ w₃ _ e₃ _ =>
            rcases e₃ with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all
    · -- w.val = 2
      match hp with
      | .step _ w₂ _ e₂ _ =>
        rcases e₂ with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all
    · simp_all

/-- chainDigraph2 has a path of length 0 from root 0. -/
private theorem chain2_path0 :
    hasPathOfLength chainDigraph2 ⟨0, by omega⟩ 0 :=
  hasPathOfLength.zero _

/-- chainDigraph2 has a path of length 1 from root 0 (via edge 0->1). -/
private theorem chain2_path1 :
    hasPathOfLength chainDigraph2 ⟨0, by omega⟩ 1 :=
  hasPathOfLength.step _ _ 0 chain2_edge_01 (hasPathOfLength.zero _)

/-- chainDigraph2 has a path of length 2 from root 0 (via 0->1->2). -/
private theorem chain2_path2 :
    hasPathOfLength chainDigraph2 ⟨0, by omega⟩ 2 :=
  hasPathOfLength.step _ _ 1 chain2_edge_01
    (hasPathOfLength.step _ _ 0 chain2_edge_12 (hasPathOfLength.zero _))

/-- No vertex in chainDigraph2 has outgoing edges from vertex 2. -/
private theorem chain2_no_edge_from_2 {t : Fin 3} :
    ¬chainDigraph2.edge ⟨2, by omega⟩ t := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all

/-- chainDigraph2 has no path of length >= 3 from root 0. -/
private theorem chain2_no_path_ge3 (n : ℕ) :
    ¬hasPathOfLength chainDigraph2 ⟨0, by omega⟩ (n + 3) := by
  intro h
  match h with
  | .step _ w _ e hp =>
    rcases e with ⟨_, hw⟩ | ⟨h0, _⟩
    · -- w.val = 1
      match hp with
      | .step _ w₂ _ e₂ hp₂ =>
        rcases e₂ with ⟨h1, _⟩ | ⟨_, hw₂⟩
        · simp_all
        · -- w₂.val = 2
          match hp₂ with
          | .step _ w₃ _ e₃ _ =>
            rcases e₃ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all
    · simp_all

/-- asymBranchDigraph rooted at 0 and chainDigraph2 rooted at 0 are trace-equivalent:
    both have trace set {0, 1, 2}. -/
theorem asymBranch_traceEquiv_chain2 :
    traceEquiv asymBranchDigraph ⟨0, by omega⟩ chainDigraph2 ⟨0, by omega⟩ := by
  ext n
  simp only [traceSet, Set.mem_setOf_eq]
  constructor
  · intro hp
    match n with
    | 0 => exact chain2_path0
    | 1 => exact chain2_path1
    | 2 => exact chain2_path2
    | n + 3 => exact absurd hp (asymBranch_no_path_ge3 n)
  · intro hp
    match n with
    | 0 => exact asymBranch_path0
    | 1 => exact asymBranch_path1
    | 2 => exact asymBranch_path2
    | n + 3 => exact absurd hp (chain2_no_path_ge3 n)

/-- asymBranchDigraph rooted at 0 and chainDigraph2 rooted at 0 are NOT bisimilar.

    Proof by contradiction: assume R is a bisimulation with R 0 0.
    - Forward on edge 0->2 in asymBranch: only successor of 0 in chain is 1, so R 2 1.
    - Backward on edge 1->2 in chain (using R 2 1): need edge from 2 in asymBranch.
      But vertex 2 in asymBranch has no outgoing edges. Contradiction. -/
theorem asymBranch_not_bisimEquiv_chain2 :
    ¬bisimEquiv asymBranchDigraph ⟨0, by omega⟩ chainDigraph2 ⟨0, by omega⟩ := by
  intro ⟨R, hR, hR00⟩
  -- Forward on asymBranch edge 0 -> 2
  have hedge_02 : asymBranchDigraph.edge (⟨0, by omega⟩ : Fin 4) ⟨2, by omega⟩ := by
    show _ ∨ (0 = 0 ∧ 2 = 2) ∨ _; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨w', hew', hR2w'⟩ := hR.forward _ _ hR00 ⟨2, by omega⟩ hedge_02
  -- chain.edge 0 w' means w'.val = 1
  have hw'_val : w'.val = 1 := by
    rcases hew' with ⟨_, hw⟩ | ⟨h0, _⟩
    · exact hw
    · exfalso; simp_all
  -- Backward on chain edge 1->2 using R 2 w' (where w'.val = 1)
  have hw'_eq : w' = ⟨1, by omega⟩ := Fin.ext hw'_val
  rw [hw'_eq] at hR2w'
  obtain ⟨v', hev', _⟩ := hR.backward ⟨2, by omega⟩ ⟨1, by omega⟩ hR2w' ⟨2, by omega⟩ chain2_edge_12
  exact asymBranch_no_edge_from_2 hev'

/-- Bisimulation is strictly finer than trace equivalence for |L| = 1:
    there exist rooted digraphs that are trace-equivalent but NOT bisimilar. -/
theorem bisim_strictly_finer_than_trace :
    ∃ (G : FinDigraph) (v : G.Vertex) (H : FinDigraph) (w : H.Vertex),
      traceEquiv G v H w ∧ ¬bisimEquiv G v H w :=
  ⟨asymBranchDigraph, ⟨0, by omega⟩, chainDigraph2, ⟨0, by omega⟩,
   asymBranch_traceEquiv_chain2, asymBranch_not_bisimEquiv_chain2⟩

/-!
## Part 5: v20.0 Bisimulation Class Computations

Bisimulation classes for the small building blocks from v20.0:
- looplessVertex (no edges), loopVertex (self-loop), arrowDigraph (false->true)
-/

/-- looplessVertex and arrowDigraph rooted at true are bisimilar: both are deadlocked
    (no outgoing edges from their roots). -/
theorem looplessVertex_bisimEquiv_arrow_true :
    bisimEquiv looplessVertex () arrowDigraph true := by
  refine ⟨fun _ w => w = true, ?_, rfl⟩
  exact {
    forward := fun _ _ _ _ he => absurd he id
    backward := fun _ w hw _ he => by
      subst hw; exact absurd he.1 Bool.noConfusion
  }

/-- looplessVertex and loopVertex are NOT bisimilar: the backward condition on the
    self-loop fails because looplessVertex has no edges. -/
theorem looplessVertex_not_bisimEquiv_loopVertex :
    ¬bisimEquiv looplessVertex () loopVertex () := by
  intro ⟨R, hR, hR_root⟩
  obtain ⟨v', hev', _⟩ := hR.backward () () hR_root () trivial
  exact hev'

/-- loopVertex and arrowDigraph rooted at false are NOT bisimilar.

    Proof: if R is a bisimulation with R () false, then:
    - Forward on self-loop: only successor of false is true. So R () true.
    - Forward on self-loop (using R () true): need arrow.edge true w'.
      But true has no outgoing edges. Contradiction. -/
theorem loopVertex_not_bisimEquiv_arrow_false :
    ¬bisimEquiv loopVertex () arrowDigraph false := by
  intro ⟨R, hR, hR_root⟩
  -- Forward on loopVertex self-loop: arrow.edge false w' and R () w'
  obtain ⟨w', hew', hRw'⟩ := hR.forward () false hR_root () trivial
  have : w' = true := hew'.2
  subst this
  -- Forward on loopVertex self-loop using R () true: arrow.edge true w''
  obtain ⟨w'', hew'', _⟩ := hR.forward () true hRw' () trivial
  exact absurd hew''.1 Bool.noConfusion

/-- Master theorem: bisimulation refines trace equivalence, and the refinement is strict.
    Combined with the v20.0 concrete class computations. -/
theorem bisim_refines_trace_summary :
    -- (1) Bisimulation implies trace equivalence
    (∀ (G : FinDigraph) (v : G.Vertex) (H : FinDigraph) (w : H.Vertex),
      bisimEquiv G v H w → traceEquiv G v H w) ∧
    -- (2) Strictly finer: trace-equivalent pair that is not bisimilar
    (∃ (G : FinDigraph) (v : G.Vertex) (H : FinDigraph) (w : H.Vertex),
      traceEquiv G v H w ∧ ¬bisimEquiv G v H w) ∧
    -- (3) v20.0 bisimulation class: deadlocked objects are bisimilar
    bisimEquiv looplessVertex () arrowDigraph true ∧
    -- (4) v20.0: loopless and loop are not bisimilar
    ¬bisimEquiv looplessVertex () loopVertex () ∧
    -- (5) v20.0: loop and arrow(false) are not bisimilar
    ¬bisimEquiv loopVertex () arrowDigraph false :=
  ⟨fun _ _ _ _ h => bisim_implies_trace h,
   bisim_strictly_finer_than_trace,
   looplessVertex_bisimEquiv_arrow_true,
   looplessVertex_not_bisimEquiv_loopVertex,
   loopVertex_not_bisimEquiv_arrow_false⟩

end RTS.PresheafTopos
