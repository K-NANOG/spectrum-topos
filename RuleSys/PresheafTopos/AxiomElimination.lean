/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom Elimination: geo_dBisim_invariant as Theorem

Proves the model-theoretic core of the geometric van Benthem theorem
using backward transfer + characteristic formula transfer.

## Key Results

- `geo_transfer_via_tree`: when φ holds on Tree_G, transfer to any d-bisimilar target
- `geo_dBisim_invariant_proved`: the former axiom, now a theorem
- `geometric_van_benthem_proved`: the full characterization theorem

## Proof Strategy

To prove φ(G,v) → φ(H,w) given dBisimilar G v H w d:

1. Backward transfer (BackwardTransfer.lean):
   φ(G,v) → φ(Tree_G, root_G) via bisim-invariance
2. Characteristic formula transfer (this file):
   φ(Tree_G, root_G) → φ(H,w) via χ(root_G) + dBisimilar + preserved_by_hom

## References

- Graf & Sifakis, "A modal characterization of observational congruence" (1986)
- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- van Benthem, "Modal Logic and Classical Logic" (1976/1983)
-/

import RuleSys.PresheafTopos.BackwardTransfer

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Characteristic Formula Transfer
-/

/-- When φ holds on the tree unraveling of G at v (depth d), it transfers to any
    d-bisimilar target (H, w) via characteristic formula + dBisimilar + preserved_by_hom.
    No bisimulation-invariance hypothesis needed.

    Proof: χ(root_G) has depth ≤ d, is satisfied at root_G (self-satisfaction),
    hence at G,v (hml_depth_preservation), hence at H,w (dBisimilar).
    By characteristicHML_iff, ∃ hom f: Tree_G → H with f(root) = w.
    By preserved_by_hom, φ transfers from Tree_G to H. -/
theorem geo_transfer_via_tree (φ : LTSGeoFormula L 1)
    (d : ℕ) (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d)
    (htree : φ.satisfies (treeUnravelLTS G v d)
               (fun _ => TreeVertex.rootPath G v d)) :
    φ.satisfies H (fun _ => w) := by
  -- Step 1: χ(root_G) has depth ≤ d
  have hchi_depth : (characteristicHML G v d (TreeVertex.rootPath G v d)).depth ≤ d := by
    have h := characteristicHML_depth_le G v d (TreeVertex.rootPath G v d)
    simp [TreeVertex.rootPath, TreeVertex.pathLength] at h
    exact h
  -- Step 2: χ(root_G) satisfied at root_G (self-satisfaction)
  have hchi_tree := characteristicHML_self_satisfies G v d (TreeVertex.rootPath G v d)
  -- Step 3: χ(root_G) satisfied at G, v (hml_depth_preservation)
  have hchi_G : (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies G v :=
    (hml_depth_preservation G v d _ hchi_depth).mpr hchi_tree
  -- Step 4: χ(root_G) satisfied at H, w (dBisimilar)
  have hchi_H : (characteristicHML G v d (TreeVertex.rootPath G v d)).satisfies H w :=
    (hdb _ hchi_depth).mp hchi_G
  -- Step 5: Extract hom f: Tree_G → H with f(root) = w
  obtain ⟨f, hf⟩ := (characteristicHML_iff G v d H w).mp hchi_H
  -- Step 6: Transfer φ via preserved_by_hom
  have htrans := LTSGeoFormula.preserved_by_hom f
    (fun _ => TreeVertex.rootPath G v d) φ htree
  -- f.toFun ∘ (fun _ => root) = fun _ => f.toFun root = fun _ => w
  have heq : f.toFun ∘ (fun _ : Fin 1 => TreeVertex.rootPath G v d) =
      fun _ => f.toFun (TreeVertex.rootPath G v d) := by ext; simp
  rw [heq, hf] at htrans
  exact htrans

/-!
## Part 2: The Model-Theoretic Core — Proved

The former axiom `geo_dBisim_invariant` is now a theorem.
The proof uses case analysis on tree satisfaction with characteristic
formula transfer for the positive cases.
-/

/-- **The geometric van Benthem core (proved)**: bisimulation-invariant geometric
    formulas of bounded existential depth are d-bisim-invariant.

    Proof chain: φ(G,v) →[backward_transfer]→ φ(Tree_G, root) →[geo_transfer_via_tree]→ φ(H,w).
    The backward transfer uses bisim-invariance to show that formulas cannot exploit
    non-tree structure (self-loops, backward edges, equality between distinct variables).
    The forward transfer uses characteristic formulas + d-bisimilarity + preserved_by_hom. -/
theorem geo_dBisim_invariant_proved (φ : LTSGeoFormula L 1)
    (hbi : FinLTSBisimInvariant (L := L) φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d) :
    φ.satisfies G (fun _ => v) → φ.satisfies H (fun _ => w) := by
  intro hsat
  exact geo_transfer_via_tree φ d G H v w hdb
    (geo_backward_transfer φ hbi d hd G v hsat)

/-!
## Part 3: Updated Main Theorems
-/

/-- Bisim-invariant geometric formulas have the same truth value at a pointed FinLTS
    and its bounded tree unraveling (proved version). -/
theorem geo_tree_equivalence_proved (φ : LTSGeoFormula L 1) (hbi : FinLTSBisimInvariant φ)
    (d : ℕ) (hd : φ.existDepth ≤ d) (G : FinLTS L) (v : G.Vertex) :
    φ.satisfies G (fun _ => v) ↔
    φ.satisfies (treeUnravelLTS G v d) (fun _ => TreeVertex.rootPath G v d) :=
  ⟨geo_dBisim_invariant_proved φ hbi d hd G (treeUnravelLTS G v d) v
     (TreeVertex.rootPath G v d) (tree_dBisimilar G v d),
   geo_forward_transfer G v d φ⟩

/-- **The Geometric van Benthem Theorem (proved version)**: bisimulation-invariant
    geometric formulas of bounded existential depth are d-bisim-invariant. -/
theorem geometric_van_benthem_proved (φ : LTSGeoFormula L 1) (hbi : FinLTSBisimInvariant φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G H : FinLTS L) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d) :
    φ.satisfies G (fun _ => v) ↔ φ.satisfies H (fun _ => w) :=
  ⟨geo_dBisim_invariant_proved φ hbi d hd G H v w hdb,
   geo_dBisim_invariant_proved φ hbi d hd H G w v (dBisimilar_symm hdb)⟩

end RTS.PresheafTopos
