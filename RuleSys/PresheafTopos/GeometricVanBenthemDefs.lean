/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric van Benthem Definitions

Core definitions for the geometric van Benthem theorem: bisimulation invariance,
depth-bounded bisimilarity, and their basic properties. Separated from the main
theorem file to break an import cycle (CharacteristicFormula → ... → AxiomElimination
needs these definitions, but the main theorem needs AxiomElimination).

## Key Definitions

- `FinLTSBisimInvariant`: Bisimulation invariance for geometric formulas on FinLTS
- `dBisimilar`: Depth-bounded bisimilarity (HML agreement up to depth d)
- `tree_dBisimilar`: Tree unraveling is d-bisimilar to original (constructive)

## References

- van Benthem, "Modal Logic and Classical Logic" (1976/1983)
- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
-/

import RuleSys.PresheafTopos.EqualityElimination

set_option autoImplicit false

namespace Ruliology.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Bisimulation Invariance for Geometric Formulas
-/

/-- A geometric formula φ : LTSGeoFormula L 1 (with one free variable) is
    bisimulation-invariant if it is preserved by labeled bisimulations:
    whenever R is a bisimulation between G and H with R v w, then
    φ(G, v) implies φ(H, w). -/
def FinLTSBisimInvariant (φ : LTSGeoFormula L 1) : Prop :=
  ∀ (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop),
    LabeledBisimulation G H R →
    ∀ (v : G.Vertex) (w : H.Vertex), R v w →
    φ.satisfies G (fun _ => v) → φ.satisfies H (fun _ => w)

/-- The inverse of a labeled bisimulation is a labeled bisimulation. -/
theorem LabeledBisimulation_inv {G H : FinLTS L}
    {R : G.Vertex → H.Vertex → Prop} (hR : LabeledBisimulation G H R) :
    LabeledBisimulation H G (fun h g => R g h) :=
  ⟨fun s t h => hR.2 t s h, fun s t h => hR.1 t s h⟩

/-- Bisimulation invariance is a bidirectional condition: φ has the same truth
    value at bisimulation-related states. -/
theorem FinLTSBisimInvariant_iff (φ : LTSGeoFormula L 1)
    (hbi : FinLTSBisimInvariant φ) (G H : FinLTS L)
    (R : G.Vertex → H.Vertex → Prop) (hR : LabeledBisimulation G H R)
    (v : G.Vertex) (w : H.Vertex) (hvw : R v w) :
    φ.satisfies G (fun _ => v) ↔ φ.satisfies H (fun _ => w) :=
  ⟨hbi G H R hR v w hvw,
   hbi H G (fun h g => R g h) (LabeledBisimulation_inv hR) w v hvw⟩

/-!
## Part 2: Depth-Bounded Bisimilarity
-/

/-- Two pointed FinLTS are d-bisimilar if they satisfy the same LabeledHML formulas
    of diamond depth at most d. This is the logical characterization of bounded
    bisimulation equivalence (the bounded Hennessy-Milner property). -/
def dBisimilar (G : FinLTS L) (v : G.Vertex) (H : FinLTS L)
    (w : H.Vertex) (d : ℕ) : Prop :=
  ∀ (ψ : LabeledHML L), ψ.depth ≤ d → (ψ.satisfies G v ↔ ψ.satisfies H w)

/-- d-bisimilarity is reflexive. -/
theorem dBisimilar_refl (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    dBisimilar G v G v d :=
  fun _ _ => Iff.rfl

/-- d-bisimilarity is symmetric. -/
theorem dBisimilar_symm {G H : FinLTS L} {v : G.Vertex} {w : H.Vertex} {d : ℕ}
    (h : dBisimilar G v H w d) :
    dBisimilar H w G v d :=
  fun ψ hd => (h ψ hd).symm

/-- d-bisimilarity is transitive. -/
theorem dBisimilar_trans {G H K : FinLTS L} {v : G.Vertex} {w : H.Vertex}
    {u : K.Vertex} {d : ℕ}
    (h1 : dBisimilar G v H w d) (h2 : dBisimilar H w K u d) :
    dBisimilar G v K u d :=
  fun ψ hd => (h1 ψ hd).trans (h2 ψ hd)

/-- Monotonicity: d-bisimilarity at depth d implies d'-bisimilarity for d' ≤ d. -/
theorem dBisimilar_mono {G H : FinLTS L} {v : G.Vertex} {w : H.Vertex}
    {d d' : ℕ} (h : dBisimilar G v H w d) (hle : d' ≤ d) :
    dBisimilar G v H w d' :=
  fun ψ hd' => h ψ (Nat.le_trans hd' hle)

/-!
## Part 3: Tree Unraveling and d-Bisimilarity
-/

/-- The tree unraveling at depth d is d-bisimilar to the original pointed LTS.
    This follows directly from the bidirectional HML depth preservation theorem
    (Phase 224). The forward direction uses the projection homomorphism; the
    backward direction uses the back condition at non-maximal-depth vertices. -/
theorem tree_dBisimilar (G : FinLTS L) (v : G.Vertex) (d : ℕ) :
    dBisimilar G v (treeUnravelLTS G v d) (TreeVertex.rootPath G v d) d :=
  fun ψ hd => hml_depth_preservation G v d ψ hd

end Ruliology.PresheafTopos
