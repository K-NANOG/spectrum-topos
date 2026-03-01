/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Van Benthem Bridge: MultiwaySystem ↔ FinLTS

This file bridges the geometric van Benthem theorem (proved for `FinLTS L`)
to the `MultiwaySystem` world via the `MultiwayToLTS` functor.

## Key Results

- `RelationalBisim_to_LabeledBisim`: unlabeled bisimulation lifts to labeled
  bisimulation on `FinLTS Unit` images
- `geometric_van_benthem_unit`: main theorem specialized to single-label LTS

## Architecture

MultiwaySystem M ──toLTS──→ FinLTS Unit
       │                         │
  RelationalBisim         LabeledBisimulation
       │                         │
  BisimInvariant      FinLTSBisimInvariant
       │                         │
  BoundedVanBenthem     GeometricVanBenthem

The bridge lemma is the key connector: since `M.toLTS.edge () s t = Nonempty (M.Step s t)`,
the quantifier over labels in `LabeledBisimulation` collapses to a single case.

## References

- van Benthem, "Modal Logic and Classical Logic" (1976/1983)
-/

import RuleSys.MultiwayToLTS
import RuleSys.Bisimulation
import RuleSys.PresheafTopos.GeometricVanBenthem

set_option autoImplicit false

namespace Ruliology

open PresheafTopos

/-!
## Part 1: Bisimulation Bridge
-/

/-- A relational bisimulation between MultiwaySystem instances lifts to a
    labeled bisimulation between their FinLTS Unit images.

    Since `M.toLTS.edge () s t = Nonempty (M.Step s t)`, the labeled
    forward/backward conditions are exactly the unlabeled ones with
    the trivial `Unit` label quantifier collapsed. -/
theorem RelationalBisim_to_LabeledBisim
    {M N : MultiwaySystem.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R) :
    LabeledBisimulation M.toLTS N.toLTS R := by
  constructor
  · intro s t hst a s' hs'
    obtain ⟨t', ht', hR'⟩ := hR.1 s t hst s' hs'
    exact ⟨t', ht', hR'⟩
  · intro s t hst a t' ht'
    obtain ⟨s', hs', hR'⟩ := hR.2 s t hst t' ht'
    exact ⟨s', hs', hR'⟩

/-- Inverse direction: a labeled bisimulation on FinLTS Unit images gives
    a relational bisimulation between MultiwaySystem instances. -/
theorem LabeledBisim_to_RelationalBisim
    {M N : MultiwaySystem.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    {R : M.State → N.State → Prop}
    (hR : LabeledBisimulation M.toLTS N.toLTS R) :
    RelationalBisimulation M N R := by
  constructor
  · intro s t hst s' hs'
    obtain ⟨t', ht', hR'⟩ := hR.1 s t hst () s' hs'
    exact ⟨t', ht', hR'⟩
  · intro s t hst t' ht'
    obtain ⟨s', hs', hR'⟩ := hR.2 s t hst () t' ht'
    exact ⟨s', hs', hR'⟩

/-!
## Part 2: Geometric van Benthem for MultiwaySystem

The geometric van Benthem theorem specialized to `L = Unit` applies directly
to FinLTS images of MultiwaySystem instances. Combined with the bisimulation
bridge, this gives: bisimulation-invariant geometric formulas over the
single-label LTS signature are determined by bounded-depth HML observations.

This connects to `BoundedVanBenthem.lean` where `StateProp` and `BisimInvariant`
characterize the same phenomenon semantically: the van Glabbeek spectrum atoms
(selfLoopProp, hasPredProp, etc.) that are NOT bisimulation-invariant have
geometric encodings that violate the equality/confluence/self-loop constraints
identified in EqualityElimination.lean.
-/

/-- The geometric van Benthem theorem for single-label LTS (MultiwaySystem images).

    Any bisimulation-invariant geometric formula of bounded existential depth
    over the signature {step : Vertex → Vertex → Prop} (i.e., L = Unit)
    is determined by bounded-depth HML observations. -/
theorem geometric_van_benthem_unit
    (φ : LTSGeoFormula Unit 1) (hbi : FinLTSBisimInvariant φ)
    (d : ℕ) (hd : φ.existDepth ≤ d)
    (G H : FinLTS Unit) (v : G.Vertex) (w : H.Vertex)
    (hdb : dBisimilar G v H w d) :
    φ.satisfies G (fun _ => v) ↔ φ.satisfies H (fun _ => w) :=
  geometric_van_benthem φ hbi d hd G H v w hdb

/-- Corollary: for MultiwaySystem instances related by a relational bisimulation,
    bisimulation-invariant geometric formulas agree on related states. -/
theorem geometric_van_benthem_multiway
    (φ : LTSGeoFormula Unit 1) (hbi : FinLTSBisimInvariant φ)
    {M N : MultiwaySystem.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    (v : M.State) (w : N.State) (hvw : R v w) :
    φ.satisfies M.toLTS (fun _ => v) → φ.satisfies N.toLTS (fun _ => w) :=
  hbi M.toLTS N.toLTS R (RelationalBisim_to_LabeledBisim hR) v w hvw

end Ruliology
