/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Depth Preservation: Formula Types and Transfer Theorems

This file defines two formula types for labeled transition systems and proves the
depth preservation theorem: HML formulas of bounded depth have the same truth value
at a pointed FinLTS (G, v) and its bounded tree unraveling.

## Key Definitions

- `LabeledHML L`: Full positive HML with top, bot, conj, disj, diamond
- `LTSGeoFormula L n`: Geometric formulas over the LTS signature (step, equal, ∃)
- `LabeledHML.depth`: Diamond nesting depth
- `LTSGeoFormula.existDepth`: Existential nesting depth

## Key Results

- `LabeledHML.preserved_by_hom`: Forward preservation by LTS homomorphisms
- `LTSGeoFormula.preserved_by_hom`: Forward preservation for geometric formulas
- `hml_backward`: HML formulas lift backward from G to the tree (depth-bounded)
- `hml_depth_preservation`: Bidirectional transfer at the root

## References

- van Benthem, "Modal Logic and Classical Logic" (1983)
- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- Grädel-Thomas-Wilke, "Automata, Logics, and Infinite Games" (2002), §2
-/

import RuleSys.PresheafTopos.FreeExtension
import RuleSys.PresheafTopos.TreeUnraveling

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: LabeledHML — Full Positive HML
-/

/-- Full positive Hennessy-Milner Logic for labeled transition systems.
    Extends HMLPos with `bot` and `disj`, needed as the target fragment
    of the geometric van Benthem theorem. -/
inductive LabeledHML (L : Type) : Type where
  /-- The trivially true formula -/
  | top : LabeledHML L
  /-- The trivially false formula -/
  | bot : LabeledHML L
  /-- Conjunction of two formulas -/
  | conj : LabeledHML L → LabeledHML L → LabeledHML L
  /-- Disjunction of two formulas -/
  | disj : LabeledHML L → LabeledHML L → LabeledHML L
  /-- Diamond modality: there exists an a-successor satisfying φ -/
  | diamond : L → LabeledHML L → LabeledHML L
  deriving DecidableEq

/-- Satisfaction of a LabeledHML formula at a vertex v of a finite LTS G. -/
def LabeledHML.satisfies (G : FinLTS L) (v : G.Vertex) : LabeledHML L → Prop
  | .top => True
  | .bot => False
  | .conj φ ψ => satisfies G v φ ∧ satisfies G v ψ
  | .disj φ ψ => satisfies G v φ ∨ satisfies G v ψ
  | .diamond a φ => ∃ w : G.Vertex, G.edge a v w ∧ satisfies G w φ

/-- Diamond nesting depth of a LabeledHML formula. -/
def LabeledHML.depth : LabeledHML L → ℕ
  | .top => 0
  | .bot => 0
  | .conj φ ψ => max φ.depth ψ.depth
  | .disj φ ψ => max φ.depth ψ.depth
  | .diamond _ φ => φ.depth + 1

/-!
## Part 2: HMLPos to LabeledHML Conversion
-/

/-- Embed HMLPos into LabeledHML (structural inclusion: top↦top, conj↦conj, diamond↦diamond). -/
def HMLPos.toLabeledHML : HMLPos L → LabeledHML L
  | .top => .top
  | .conj φ ψ => .conj φ.toLabeledHML ψ.toLabeledHML
  | .diamond a φ => .diamond a φ.toLabeledHML

/-- Satisfaction is preserved by the HMLPos → LabeledHML embedding. -/
theorem HMLPos.toLabeledHML_satisfies_iff (G : FinLTS L) (v : G.Vertex)
    (φ : HMLPos L) :
    φ.toLabeledHML.satisfies G v ↔ φ.satisfies G v := by
  induction φ generalizing v with
  | top => simp [toLabeledHML, LabeledHML.satisfies, HMLPos.satisfies]
  | conj φ ψ ihφ ihψ =>
    simp only [toLabeledHML, LabeledHML.satisfies, HMLPos.satisfies]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(ihφ v).mp h1, (ihψ v).mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨(ihφ v).mpr h1, (ihψ v).mpr h2⟩⟩
  | diamond a φ ih =>
    simp only [toLabeledHML, LabeledHML.satisfies, HMLPos.satisfies]
    exact ⟨fun ⟨w, he, hs⟩ => ⟨w, he, (ih w).mp hs⟩,
           fun ⟨w, he, hs⟩ => ⟨w, he, (ih w).mpr hs⟩⟩

/-!
## Part 3: LTSGeoFormula — Geometric Formulas over the LTS Signature
-/

/-- Geometric formulas specialized to the LTS signature {step_a | a ∈ L}.
    Uses de Bruijn indices: `Fin n` for bound variables in context of size n.
    `exist φ` binds a fresh variable at index 0, shifting existing variables. -/
inductive LTSGeoFormula (L : Type) : ℕ → Type where
  /-- Truth -/
  | top {n} : LTSGeoFormula L n
  /-- Falsity -/
  | bot {n} : LTSGeoFormula L n
  /-- Equality between variables i and j -/
  | equal {n} (i j : Fin n) : LTSGeoFormula L n
  /-- Labeled transition step_a(i, j) -/
  | step {n} (a : L) (i j : Fin n) : LTSGeoFormula L n
  /-- Conjunction -/
  | conj {n} : LTSGeoFormula L n → LTSGeoFormula L n → LTSGeoFormula L n
  /-- Disjunction -/
  | disj {n} : LTSGeoFormula L n → LTSGeoFormula L n → LTSGeoFormula L n
  /-- Existential quantification: binds variable 0 in the body -/
  | exist {n} : LTSGeoFormula L (n + 1) → LTSGeoFormula L n

/-- Satisfaction of an LTSGeoFormula at an assignment σ : Fin n → G.Vertex.
    `exist φ` binds variable 0 via `Fin.cons`: `Fin.cons w σ` maps 0 ↦ w, (i+1) ↦ σ i. -/
def LTSGeoFormula.satisfies {n : ℕ} (G : FinLTS L) (σ : Fin n → G.Vertex) :
    LTSGeoFormula L n → Prop
  | .top => True
  | .bot => False
  | .equal i j => σ i = σ j
  | .step a i j => G.edge a (σ i) (σ j)
  | .conj φ ψ => satisfies G σ φ ∧ satisfies G σ ψ
  | .disj φ ψ => satisfies G σ φ ∨ satisfies G σ ψ
  | .exist φ => ∃ w : G.Vertex, satisfies G (Fin.cons w σ) φ

/-- Satisfaction of LTSGeoFormula on FinLTS is decidable. -/
def LTSGeoFormula.satisfies_decidable {n : ℕ} (G : FinLTS L) (σ : Fin n → G.Vertex) :
    (φ : LTSGeoFormula L n) → Decidable (φ.satisfies G σ)
  | .top => isTrue trivial
  | .bot => isFalse id
  | .equal i j => inferInstanceAs (Decidable (σ i = σ j))
  | .step a i j => G.edgeDecidable a (σ i) (σ j)
  | .conj φ ψ => @instDecidableAnd _ _ (satisfies_decidable G σ φ) (satisfies_decidable G σ ψ)
  | .disj φ ψ => @instDecidableOr _ _ (satisfies_decidable G σ φ) (satisfies_decidable G σ ψ)
  | .exist φ =>
    haveI : DecidablePred (fun w => φ.satisfies G (Fin.cons w σ)) :=
      fun w => satisfies_decidable G (Fin.cons w σ) φ
    Fintype.decidableExistsFintype

/-- Existential nesting depth of an LTSGeoFormula. -/
def LTSGeoFormula.existDepth {n : ℕ} : LTSGeoFormula L n → ℕ
  | .top => 0
  | .bot => 0
  | .equal _ _ => 0
  | .step _ _ _ => 0
  | .conj φ ψ => max φ.existDepth ψ.existDepth
  | .disj φ ψ => max φ.existDepth ψ.existDepth
  | .exist φ => φ.existDepth + 1

/-!
## Part 4: Forward Homomorphism Preservation
-/

/-- LabeledHML formulas are preserved by LTS homomorphisms.
    This extends the HMLPos version (FreeExtension.lean) to include bot and disj. -/
theorem LabeledHML.preserved_by_hom {G H : FinLTS L} (f : LTSHom G H)
    (v : G.Vertex) (φ : LabeledHML L) (h : φ.satisfies G v) :
    φ.satisfies H (f.toFun v) := by
  induction φ generalizing v with
  | top => trivial
  | bot => exact h.elim
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ v h.1, ihψ v h.2⟩
  | disj φ ψ ihφ ihψ =>
    exact h.elim (fun h => Or.inl (ihφ v h)) (fun h => Or.inr (ihψ v h))
  | diamond a φ ih =>
    obtain ⟨w, hedge, hsat⟩ := h
    exact ⟨f.toFun w, f.map_edge a v w hedge, ih w hsat⟩

/-- Composing a function with Fin.cons commutes:
    f ∘ (Fin.cons w σ) = Fin.cons (f w) (f ∘ σ). -/
private theorem comp_fin_cons {α β : Type} {n : ℕ} (f : α → β) (w : α)
    (σ : Fin n → α) : f ∘ (Fin.cons w σ) = Fin.cons (f w) (f ∘ σ) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Fin.cons]
  | succ i => simp [Fin.cons, Function.comp]

/-- Geometric LTS formulas are preserved by LTS homomorphisms applied pointwise.
    Since all constructors are positive-existential, homomorphisms map witnesses forward. -/
theorem LTSGeoFormula.preserved_by_hom {n : ℕ} {G H : FinLTS L} (f : LTSHom G H)
    (σ : Fin n → G.Vertex) (φ : LTSGeoFormula L n)
    (h : φ.satisfies G σ) : φ.satisfies H (f.toFun ∘ σ) := by
  induction φ with
  | top => trivial
  | bot => exact h.elim
  | equal i j =>
    show f.toFun (σ i) = f.toFun (σ j)
    exact congrArg f.toFun h
  | step a i j =>
    show H.edge a (f.toFun (σ i)) (f.toFun (σ j))
    exact f.map_edge a (σ i) (σ j) h
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ σ h.1, ihψ σ h.2⟩
  | disj φ ψ ihφ ihψ =>
    exact h.elim (fun h => Or.inl (ihφ σ h)) (fun h => Or.inr (ihψ σ h))
  | exist φ ih =>
    obtain ⟨w, hsat⟩ := h
    refine ⟨f.toFun w, ?_⟩
    have := ih (Fin.cons w σ) hsat
    rw [comp_fin_cons] at this
    exact this

/-!
## Part 5: Forward Transfer via Tree Projection
-/

/-- Forward transfer: geometric formulas satisfied in the tree transfer to G
    via the projection homomorphism. Specialized to the 1-variable (pointed) case. -/
theorem geo_forward_transfer (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (φ : LTSGeoFormula L 1)
    (h : φ.satisfies (treeUnravelLTS G v d)
           (fun _ => TreeVertex.rootPath G v d)) :
    φ.satisfies G (fun _ => v) :=
  LTSGeoFormula.preserved_by_hom (treeProjection G v d) _ φ h

/-!
## Part 6: HML Backward Transfer
-/

/-- Tree edges increase path length by exactly one. -/
theorem treeEdge_succ_pathLength (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (a : L) (t q : (treeUnravelLTS G v d).Vertex)
    (h : (treeUnravelLTS G v d).edge a t q) :
    q.pathLength = t.pathLength + 1 := by
  show q.val.length = t.val.length + 1
  have := h.1
  rw [this, List.length_append, List.length_singleton]

/-- HML formulas transfer backward from G to the tree unraveling, provided the
    tree vertex has enough remaining depth.

    Invariant: t.pathLength + φ.depth ≤ d ensures the back condition is available
    at every diamond step in the recursive descent. -/
theorem hml_backward (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex)
    (φ : LabeledHML L) (hd : t.pathLength + φ.depth ≤ d)
    (h : φ.satisfies G t.endpoint) :
    φ.satisfies (treeUnravelLTS G v d) t := by
  induction φ generalizing t with
  | top => trivial
  | bot => exact h.elim
  | conj φ ψ ihφ ihψ =>
    simp only [LabeledHML.depth] at hd
    have h_ml := Nat.le_max_left φ.depth ψ.depth
    have h_mr := Nat.le_max_right φ.depth ψ.depth
    exact ⟨ihφ t (by omega) h.1, ihψ t (by omega) h.2⟩
  | disj φ ψ ihφ ihψ =>
    simp only [LabeledHML.depth] at hd
    have h_ml := Nat.le_max_left φ.depth ψ.depth
    have h_mr := Nat.le_max_right φ.depth ψ.depth
    exact h.elim
      (fun h => Or.inl (ihφ t (by omega) h))
      (fun h => Or.inr (ihψ t (by omega) h))
  | diamond a φ ih =>
    obtain ⟨w, hedge, hsat⟩ := h
    -- From depth bound: t.pathLength + (φ.depth + 1) ≤ d
    simp only [LabeledHML.depth] at hd
    have hlen : t.pathLength < d := by omega
    -- Lift the G-edge to the tree using the back condition
    obtain ⟨q, htree_edge, hq_ep⟩ := treeProjection_back G v d t hlen a w hedge
    -- The witness q has endpoint w and pathLength = t.pathLength + 1
    have hq_depth : q.pathLength + φ.depth ≤ d := by
      rw [treeEdge_succ_pathLength G v d a t q htree_edge]; omega
    refine ⟨q, htree_edge, ih q hq_depth ?_⟩
    -- hq_ep : (treeProjection G v d).toFun q = w, which is q.endpoint = w
    have : q.endpoint = w := hq_ep
    rw [this]
    exact hsat

/-- HML formulas transfer forward from the tree to G via the projection. -/
theorem hml_forward (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (t : (treeUnravelLTS G v d).Vertex)
    (φ : LabeledHML L)
    (h : φ.satisfies (treeUnravelLTS G v d) t) :
    φ.satisfies G t.endpoint :=
  LabeledHML.preserved_by_hom (treeProjection G v d) t φ h

/-!
## Part 7: Root d-Bisimilarity Theorem
-/

/-- **Depth preservation theorem**: HML formulas of depth ≤ d have the same truth value
    at the original pointed LTS (G, v) and its bounded tree unraveling at depth d.

    This is the key transfer principle for the geometric van Benthem theorem:
    any bisimulation-invariant HML property can be checked on the tree instead. -/
theorem hml_depth_preservation (G : FinLTS L) (v : G.Vertex) (d : ℕ)
    (φ : LabeledHML L) (hd : φ.depth ≤ d) :
    φ.satisfies G v ↔
    φ.satisfies (treeUnravelLTS G v d) (TreeVertex.rootPath G v d) := by
  constructor
  · -- G → tree: backward transfer at root (pathLength = 0)
    intro h
    have hbd : (TreeVertex.rootPath G v d).pathLength + φ.depth ≤ d := by
      simp [TreeVertex.rootPath_pathLength]; exact hd
    have hep : (TreeVertex.rootPath G v d).endpoint = v :=
      TreeVertex.rootPath_endpoint G v d
    exact hml_backward G v d (TreeVertex.rootPath G v d) φ hbd (hep ▸ h)
  · -- Tree → G: forward transfer via projection
    intro h
    have hep : (TreeVertex.rootPath G v d).endpoint = v :=
      TreeVertex.rootPath_endpoint G v d
    exact hep ▸ hml_forward G v d (TreeVertex.rootPath G v d) φ h

end RTS.PresheafTopos
