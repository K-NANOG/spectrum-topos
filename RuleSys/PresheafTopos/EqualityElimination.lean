/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Equality Elimination: Tree Structure and Atom Characterization

This file proves structural properties of `treeUnravelLTS` that enable
equality elimination and dependency analysis for the geometric van Benthem
theorem. The core insight: in the tree unraveling, ALL edges go from parent
to child (shorter path to longer path), there are no self-loops, and vertex
equality is path equality.

## Key Results

- `treeNoSelfLoop`: No self-loops in the tree unraveling
- `treeEdge_extends_path`: Tree edges extend the parent's path by one step
- `treeEdge_unique_child`: Same label + same endpoint from same parent = same child
- `treeEdge_unique_parent_label`: Each non-root vertex has unique (parent, label) pair
- `tree_step_depth_strict`: Step atoms strictly increase depth on trees
- `tree_step_equal_absurd`: Step + equality between source and target is absurd on trees

## References

- Otto, "Bisimulation-invariant PTIME" (2004), §3 (locally acyclic covers)
- Grädel-Thomas-Wilke, "Automata, Logics, and Infinite Games" (2002), §2
-/

import RuleSys.PresheafTopos.DepthPreservation

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Tree Edge Structural Lemmas
-/

/-- No self-loops in the tree unraveling: an edge strictly increases path length,
    so source and target are always distinct. -/
theorem treeNoSelfLoop (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (t : (treeUnravelLTS G v d).Vertex) :
    ¬(treeUnravelLTS G v d).edge a t t := by
  intro h
  have := treeEdge_succ_pathLength G v d a t t h
  omega

/-- Tree edges extend the parent's path by one step. This is the first component
    of treeEdgePred, extracted as a standalone lemma. -/
theorem treeEdge_extends_path (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    q.val = p.val ++ [(a, q.endpoint)] :=
  h.1

/-- Tree edges preserve the G-edge relation at endpoints. -/
theorem treeEdge_G_edge (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    G.edge a p.endpoint q.endpoint :=
  h.2

/-- If two children of the same parent have the same label and endpoint, they are equal.
    This follows because their paths are determined by the parent's path plus the extension. -/
theorem treeEdge_unique_child (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q₁ q₂ : (treeUnravelLTS G v d).Vertex)
    (h₁ : (treeUnravelLTS G v d).edge a p q₁)
    (h₂ : (treeUnravelLTS G v d).edge a p q₂)
    (hep : q₁.endpoint = q₂.endpoint) :
    q₁ = q₂ := by
  apply Subtype.ext
  rw [treeEdge_extends_path G v d a p q₁ h₁,
      treeEdge_extends_path G v d a p q₂ h₂, hep]

/-- Each non-root tree vertex has a unique parent vertex and incoming label.
    If `edge a₁ p₁ q` and `edge a₂ p₂ q`, then `p₁ = p₂` and `a₁ = a₂`. -/
theorem treeEdge_unique_parent_label (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a₁ a₂ : L) (p₁ p₂ q : (treeUnravelLTS G v d).Vertex)
    (h₁ : (treeUnravelLTS G v d).edge a₁ p₁ q)
    (h₂ : (treeUnravelLTS G v d).edge a₂ p₂ q) :
    p₁ = p₂ ∧ a₁ = a₂ := by
  have he₁ := treeEdge_extends_path G v d a₁ p₁ q h₁
  have he₂ := treeEdge_extends_path G v d a₂ p₂ q h₂
  -- q.val = p₁.val ++ [(a₁, q.endpoint)] = p₂.val ++ [(a₂, q.endpoint)]
  have hcat : p₁.val ++ [(a₁, q.endpoint)] = p₂.val ++ [(a₂, q.endpoint)] := by
    rw [← he₁, ← he₂]
  -- Use List.dropLast on both sides to get the prefixes
  have hpaths : p₁.val = p₂.val := by
    have h1 : (p₁.val ++ [(a₁, q.endpoint)]).dropLast = p₁.val := by
      simp [List.dropLast_append_of_ne_nil]
    have h2 : (p₂.val ++ [(a₂, q.endpoint)]).dropLast = p₂.val := by
      simp [List.dropLast_append_of_ne_nil]
    rw [← h1, hcat, h2]
  -- Substitute path equality into the concatenation to get label equality
  have hlabel : a₁ = a₂ := by
    rw [hpaths] at hcat
    have := List.append_cancel_left hcat
    exact (Prod.mk.inj (List.cons.inj this).1).1
  exact ⟨Subtype.ext hpaths, hlabel⟩

/-- Path equality implies vertex equality (Subtype extensionality wrapper). -/
theorem treeVertex_eq_of_val_eq (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (p q : (treeUnravelLTS G v d).Vertex) (h : p.val = q.val) :
    p = q :=
  Subtype.ext h

/-- Edges in treeUnravelLTS strictly increase path length. Corollary: the source
    vertex's path is a proper prefix of the target's path. -/
theorem treeEdge_strict_prefix (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    p.pathLength < q.pathLength := by
  rw [treeEdge_succ_pathLength G v d a p q h]
  omega

/-- The parent's path is a prefix of the child's path. -/
theorem treeEdge_path_prefix (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    p.val <+: q.val := by
  rw [treeEdge_extends_path G v d a p q h]
  exact List.prefix_append p.val [(a, q.endpoint)]

/-!
## Part 2: Step and Equality Characterization on Trees
-/

/-- On trees, step atoms strictly increase depth: if `edge a (σ i) (σ j)` holds
    then σ(j) is strictly deeper than σ(i). -/
theorem tree_step_depth_strict (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j : Fin n)
    (h : (treeUnravelLTS G v d).edge a (σ i) (σ j)) :
    (σ i).pathLength < (σ j).pathLength :=
  treeEdge_strict_prefix G v d a (σ i) (σ j) h

/-- On trees, step atoms from a variable to itself are impossible (no self-loops). -/
theorem tree_step_self_absurd (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i : Fin n)
    (h : (treeUnravelLTS G v d).edge a (σ i) (σ i)) : False :=
  treeNoSelfLoop G v d a (σ i) h

/-- On trees, a step atom combined with equality of source and target is absurd.
    This is the key lemma for eliminating `step_a(x,x)` patterns in geometric formulas. -/
theorem tree_step_equal_absurd (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j : Fin n)
    (hstep : (treeUnravelLTS G v d).edge a (σ i) (σ j))
    (heq : σ i = σ j) : False := by
  have := treeEdge_strict_prefix G v d a (σ i) (σ j) hstep
  rw [heq] at this
  omega

/-- On trees, if two step atoms point to the same target from the same source with
    the same label and same endpoint, their targets are equal. -/
theorem tree_step_same_target (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j₁ j₂ : Fin n)
    (h₁ : (treeUnravelLTS G v d).edge a (σ i) (σ j₁))
    (h₂ : (treeUnravelLTS G v d).edge a (σ i) (σ j₂))
    (hep : (σ j₁).endpoint = (σ j₂).endpoint) :
    σ j₁ = σ j₂ :=
  treeEdge_unique_child G v d a (σ i) (σ j₁) (σ j₂) h₁ h₂ hep

/-- On trees, if two step atoms with different labels/parents point to the same
    target, the parents and labels must be equal. -/
theorem tree_step_unique_incoming (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a₁ a₂ : L) (i₁ i₂ j : Fin n)
    (h₁ : (treeUnravelLTS G v d).edge a₁ (σ i₁) (σ j))
    (h₂ : (treeUnravelLTS G v d).edge a₂ (σ i₂) (σ j)) :
    σ i₁ = σ i₂ ∧ a₁ = a₂ :=
  treeEdge_unique_parent_label G v d a₁ a₂ (σ i₁) (σ i₂) (σ j) h₁ h₂

/-!
## Part 3: LTSGeoFormula Atoms on Trees — Semantic Characterization
-/

/-- On a tree unraveling, `step a (σ i) (σ j)` implies the target extends the
    source's computation path by exactly one step. -/
theorem tree_step_path_extension (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j : Fin n)
    (h : (treeUnravelLTS G v d).edge a (σ i) (σ j)) :
    (σ j).val = (σ i).val ++ [(a, (σ j).endpoint)] :=
  treeEdge_extends_path G v d a (σ i) (σ j) h

/-- On a tree, equal vertices have equal path lengths (contrapositive: different
    depths implies different vertices). -/
theorem tree_equal_depth (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (i j : Fin n) (h : σ i = σ j) :
    (σ i).pathLength = (σ j).pathLength := by
  rw [h]

/-- On a tree, if a step atom connects variables i→j, then j cannot also be an
    ancestor of i (no cycles). In fact, j has strictly greater depth. -/
theorem tree_step_no_back (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a b : L) (i j k : Fin n)
    (hij : (treeUnravelLTS G v d).edge a (σ i) (σ j))
    (hjk : (treeUnravelLTS G v d).edge b (σ j) (σ k))
    (hki : σ k = σ i) : False := by
  have h1 := treeEdge_strict_prefix G v d a (σ i) (σ j) hij
  have h2 := treeEdge_strict_prefix G v d b (σ j) (σ k) hjk
  rw [hki] at h2
  omega

/-- On a tree, a diamond property (two paths from i meeting at k) is impossible.
    If i→j₁ and i→j₂ via different children, and j₁→k and j₂→k, then the
    unique parent of k would need to be both j₁ and j₂, forcing j₁ = j₂. -/
theorem tree_diamond_forces_equal (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a₁ a₂ : L) (j₁ j₂ k : Fin n)
    (h₁ : (treeUnravelLTS G v d).edge a₁ (σ j₁) (σ k))
    (h₂ : (treeUnravelLTS G v d).edge a₂ (σ j₂) (σ k)) :
    σ j₁ = σ j₂ ∧ a₁ = a₂ :=
  treeEdge_unique_parent_label G v d a₁ a₂ (σ j₁) (σ j₂) (σ k) h₁ h₂

/-- Root has no incoming edges: no step atom can target the root. -/
theorem tree_root_no_incoming (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p : (treeUnravelLTS G v d).Vertex) :
    ¬(treeUnravelLTS G v d).edge a p (TreeVertex.rootPath G v d) :=
  treeUnravel_no_edge_to_root G v d a p

/-- On trees, the path length function is strictly monotone along edges:
    edge a p q → p.pathLength + 1 = q.pathLength. Combined with depth
    boundedness, this limits the possible "shapes" of satisfying assignments. -/
theorem tree_depth_monotone_edge (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (p q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a p q) :
    p.pathLength + 1 = q.pathLength :=
  (treeEdge_succ_pathLength G v d a p q h).symm

/-!
## Part 4: Semantic Step Characterization for LTSGeoFormula
-/

/-- On trees, `LTSGeoFormula.step a i j` under assignment σ implies σ(j) is an
    a-child of σ(i) in the tree. This relates the formula-level step atom to
    the tree-level edge structure. -/
theorem tree_geo_step_is_edge (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j : Fin n)
    (h : (LTSGeoFormula.step a i j).satisfies (treeUnravelLTS G v d) σ) :
    (treeUnravelLTS G v d).edge a (σ i) (σ j) :=
  h

/-- On trees, `LTSGeoFormula.step a i i` is always false (self-loop). -/
theorem tree_geo_step_self_false (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i : Fin n)
    (h : (LTSGeoFormula.step a i i).satisfies (treeUnravelLTS G v d) σ) :
    False :=
  treeNoSelfLoop G v d a (σ i) h

/-- On trees, `LTSGeoFormula.equal i j` combined with `LTSGeoFormula.step a i j`
    is always false. -/
theorem tree_geo_equal_step_false (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a : L) (i j : Fin n)
    (heq : (LTSGeoFormula.equal i j).satisfies (treeUnravelLTS G v d) σ)
    (hstep : (LTSGeoFormula.step a i j).satisfies (treeUnravelLTS G v d) σ) :
    False := by
  exact tree_step_equal_absurd G v d σ a i j hstep heq

/-- On trees, `LTSGeoFormula.step a i j` and `LTSGeoFormula.step b k j` together
    force σ(i) = σ(k) and a = b — the unique parent property at the formula level. -/
theorem tree_geo_step_confluence (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    {n : ℕ} (σ : Fin n → (treeUnravelLTS G v d).Vertex)
    (a b : L) (i k j : Fin n)
    (h₁ : (LTSGeoFormula.step a i j).satisfies (treeUnravelLTS G v d) σ)
    (h₂ : (LTSGeoFormula.step b k j).satisfies (treeUnravelLTS G v d) σ) :
    σ i = σ k ∧ a = b :=
  tree_step_unique_incoming G v d σ a b i k j h₁ h₂

end RTS.PresheafTopos
