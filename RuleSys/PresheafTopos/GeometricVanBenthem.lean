/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric van Benthem Theorem

The geometric analogue of van Benthem's 1976 characterization theorem:
bisimulation-invariant geometric sequents over labeled transition systems
are determined by bounded-depth HML equivalence.

## Key Results

- `geo_dBisim_invariant`: The model-theoretic core — bisim-inv geo formulas of
  bounded existential depth are d-bisim-invariant
- `geo_tree_equivalence`: Bisim-invariant formulas transfer to/from trees
- `geometric_van_benthem`: The main theorem (bidirectional)
- `geometric_van_benthem_nat`: Natural depth specialization

## Architecture

The proof decomposes into:
1. **Definitions** (GeometricVanBenthemDefs.lean): FinLTSBisimInvariant, dBisimilar
2. **Forward transfer** (DepthPreservation.lean): `geo_forward_transfer`
3. **HML transfer** (DepthPreservation.lean): `hml_depth_preservation`
4. **Backward transfer** (BackwardTransfer.lean): padded tree bisimulation
5. **Characteristic formula transfer** (AxiomElimination.lean): `geo_transfer_via_tree`
6. **Assembly** (this file): composing the above into the full characterization

The full proof chain: φ(G,v) →[backward_transfer via padded tree]→ φ(Tree_G, root)
→[characteristic formula + d-bisimilarity + preserved_by_hom]→ φ(H,w).

## References

- van Benthem, "Modal Logic and Classical Logic" (1976/1983)
- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- Otto, "Bisimulation-invariant PTIME" (2004)
- Rosen, "Modal logic over finite structures" (1997)
-/

import RuleSys.PresheafTopos.AxiomElimination

set_option autoImplicit false

namespace Ruliology.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

-- Definitions (FinLTSBisimInvariant, dBisimilar, etc.) are imported
-- transitively from GeometricVanBenthemDefs via the AxiomElimination chain.

/-!
## The Model-Theoretic Core

Bisimulation-invariant geometric formulas of bounded existential depth are
determined by bounded-depth HML equivalence.

This is the "hard direction" proved via:
1. Padded tree bisimulation (backward transfer)
2. Characteristic formula transfer (forward transfer)
See `geo_dBisim_invariant_proved` in AxiomElimination.lean.
-/

/-- **The geometric van Benthem core**: bisimulation-invariant geometric formulas
    of bounded existential depth are d-bisim-invariant.

    Given: φ is bisimulation-invariant and has existDepth ≤ d.
    Then: if two pointed FinLTS satisfy the same HML formulas of depth ≤ d,
    they also satisfy the same bisim-invariant geometric formulas of existDepth ≤ d.

    Proof: backward transfer (padded tree bisimulation) +
    characteristic formula transfer. See AxiomElimination.lean. -/
theorem geo_dBisim_invariant {L : Type} [Fintype L] [DecidableEq L]
    (φ : LTSGeoFormula L 1) (hbi : FinLTSBisimInvariant (L := L) φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d) :
    φ.satisfies G (fun _ => v) → φ.satisfies H (fun _ => w) :=
  geo_dBisim_invariant_proved φ hbi d hd G H v w hdb

/-!
## Tree Transfer and Main Theorem
-/

/-- Bisim-invariant geometric formulas have the same truth value at a pointed FinLTS
    and its bounded tree unraveling. The forward direction is the projection
    homomorphism (constructive). The backward direction uses d-bisimilarity
    of the tree to the original. -/
theorem geo_tree_equivalence (φ : LTSGeoFormula L 1) (hbi : FinLTSBisimInvariant φ)
    (d : ℕ) (hd : φ.existDepth ≤ d) (G : FinLTS L) (v : G.Vertex) :
    φ.satisfies G (fun _ => v) ↔
    φ.satisfies (treeUnravelLTS G v d) (fun _ => TreeVertex.rootPath G v d) :=
  ⟨geo_dBisim_invariant φ hbi d hd G (treeUnravelLTS G v d) v
     (TreeVertex.rootPath G v d) (tree_dBisimilar G v d),
   geo_forward_transfer G v d φ⟩

/-- **The Geometric van Benthem Theorem**: bisimulation-invariant geometric formulas
    of bounded existential depth are d-bisim-invariant.

    If φ is a bisimulation-invariant geometric formula with existDepth ≤ d, then
    d-bisimilar pointed FinLTS satisfy the same φ truth values.

    This is the geometric analogue of van Benthem's 1976 characterization theorem:
    just as bisimulation-invariant first-order formulas reduce to modal logic,
    bisimulation-invariant geometric formulas are determined by bounded-depth HML
    observations — the modal fragment with ⊤, ⊥, ∧, ∨, ⟨a⟩ but no negation.

    The theorem's content: among geometric formulas, the only obstructions to HML
    expressibility are equality atoms, confluence patterns, and self-loops — all
    of which are incompatible with bisimulation invariance. -/
theorem geometric_van_benthem (φ : LTSGeoFormula L 1) (hbi : FinLTSBisimInvariant φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d) :
    φ.satisfies G (fun _ => v) ↔ φ.satisfies H (fun _ => w) :=
  ⟨geo_dBisim_invariant φ hbi d hd G H v w hdb,
   geo_dBisim_invariant φ hbi d hd H G w v (dBisimilar_symm hdb)⟩

/-- Natural depth specialization: use the formula's own existDepth as the bound. -/
theorem geometric_van_benthem_nat (φ : LTSGeoFormula L 1)
    (hbi : FinLTSBisimInvariant φ)
    (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w φ.existDepth) :
    φ.satisfies G (fun _ => v) ↔ φ.satisfies H (fun _ => w) :=
  geometric_van_benthem φ hbi φ.existDepth (le_refl _) G H v w hdb

end Ruliology.PresheafTopos
