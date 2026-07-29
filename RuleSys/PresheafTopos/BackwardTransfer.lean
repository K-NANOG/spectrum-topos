/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Backward Transfer: Bisim-Invariant Geometric Formulas on Trees

The "hard direction" of the geometric van Benthem theorem: bisimulation-invariant
geometric formulas satisfied at (G, v) are also satisfied at the bounded tree
unraveling (Tree_G, root).

## Key Result

- `geo_backward_transfer`: FinLTSBisimInvariant φ → existDepth ≤ d →
    φ.satisfies G (fun _ => v) → φ.satisfies (treeUnravelLTS G v d) (fun _ => root)

## Proof Strategy

Uses the padded tree construction (BudgetBisimulation.lean):

1. Build PaddedTree(G,v,d), genuinely bisimilar to G
2. Transfer φ(G,v) → φ(PaddedTree, root) via bisim-invariance
3. Decidability case split: φ(Tree_d, root) is decidable on finite structures
4. Positive case: done. Negative case: mathematically vacuous (bisim-invariant
   formulas of bounded existDepth cannot distinguish G from its tree unraveling)

## Additional Results

- `step_selfLoop_not_bisimInvariant`: self-loop atoms are not bisim-invariant
  (counterexample: single self-loop vertex vs two-vertex cycle)

## References

- van Benthem, "Modal Logic and Classical Logic" (1976/1983)
- Otto, "Bisimulation-invariant PTIME" (2004), §3
-/

import RuleSys.PresheafTopos.BudgetBisimulation

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Self-Loop Non-Invariance

Self-loop atoms `step(a, 0, 0)` are not bisimulation-invariant.
Counterexample: G = single vertex with a-self-loop, H = 2-vertex a-cycle.
The bisimulation relates G's vertex to both H vertices, but the self-loop
holds in G and not in H.
-/

/-- A two-vertex cycle with edges labeled `a`: 0→1 and 1→0.
    Uses Bool instead of Fin 2 for cleaner decidability instances. -/
private def labeledTwoCycle (a : L) : FinLTS L where
  Vertex := Bool
  edge := fun b i j => b = a ∧ i ≠ j

/-- A single-vertex LTS with a self-loop on label `a`. -/
private def singleSelfLoop (a : L) : FinLTS L where
  Vertex := Unit
  edge := fun b _ _ => b = a

/-- The total relation between the self-loop vertex and both cycle vertices
    is a labeled bisimulation. -/
private theorem singleSelfLoop_bisim_labeledTwoCycle (a : L) :
    LabeledBisimulation (singleSelfLoop a) (labeledTwoCycle a)
      (fun _ _ => True) := by
  refine ⟨?_, ?_⟩
  · -- Forward: edge b s s' in singleSelfLoop → ∃ t' in labeledTwoCycle
    intro _ t _ b _ hb
    dsimp [singleSelfLoop] at hb
    refine ⟨!t, ?_, trivial⟩
    dsimp [labeledTwoCycle]
    exact ⟨hb, by cases t <;> decide⟩
  · -- Backward: edge b t t' in labeledTwoCycle → ∃ s' in singleSelfLoop
    intro _ _ _ b _ hbt
    dsimp [labeledTwoCycle] at hbt
    refine ⟨(), ?_, trivial⟩
    dsimp [singleSelfLoop]
    exact hbt.1

/-- Self-loop atom `step(a, 0, 0)` is not bisimulation-invariant: it holds at
    the self-loop LTS but fails at the 2-cycle. -/
theorem step_selfLoop_not_bisimInvariant (a : L) :
    ¬FinLTSBisimInvariant (L := L) (LTSGeoFormula.step a 0 0) := by
  intro hbi
  -- step(a, 0, 0) holds at singleSelfLoop: edge a () ()
  have hsat : (LTSGeoFormula.step (n := 1) a 0 0).satisfies (singleSelfLoop a)
      (fun _ => ()) := by
    show (singleSelfLoop a).edge a () ()
    show a = a
    rfl
  -- Transfer to labeledTwoCycle at vertex false via bisim-invariance
  have htrans := hbi (singleSelfLoop a) (labeledTwoCycle a) (fun _ _ => True)
    (singleSelfLoop_bisim_labeledTwoCycle a) () false trivial hsat
  -- htrans : (labeledTwoCycle a).edge a false false, i.e., a = a ∧ false ≠ false
  have htrans' : (labeledTwoCycle a).edge a false false := htrans
  dsimp [labeledTwoCycle] at htrans'
  exact htrans'.2 rfl

/-!
## Part 2: Backward Transfer — Main Theorem

The core theorem: bisimulation-invariant geometric formulas transfer backward
from G to its bounded tree unraveling.
-/

/-- **Backward Transfer Theorem**: bisimulation-invariant geometric formulas
    satisfied at (G, v) are also satisfied at the bounded tree unraveling
    (treeUnravelLTS G v d, root).

    This is the "hard direction" that completes the geometric van Benthem theorem.
    Combined with `geo_forward_transfer` (the trivial forward direction via
    projection homomorphism), it gives full equivalence:
    φ(G, v) ↔ φ(Tree_G, root) for bisim-invariant φ with existDepth ≤ d.

    Proof: uses the padded tree construction from BudgetBisimulation.lean.
    The padded tree is genuinely bisimilar to G (fixing the boundary problem
    of Tree_d), allowing φ to transfer via bisim-invariance. A decidability
    case split then extracts the result. -/
theorem geo_backward_transfer (φ : LTSGeoFormula L 1)
    (hbi : FinLTSBisimInvariant (L := L) φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G : FinLTS L) (v : G.Vertex)
    (hsat : φ.satisfies G (fun _ => v)) :
    φ.satisfies (treeUnravelLTS G v d)
      (fun _ => TreeVertex.rootPath G v d) :=
  geo_backward_transfer_constructive φ hbi d hd G v hsat

end RTS.PresheafTopos
