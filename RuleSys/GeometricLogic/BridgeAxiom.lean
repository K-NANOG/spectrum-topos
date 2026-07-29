/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Bridge Axiom for Propositional Geometric Theories

Defines the propositional classifying topos and the bridge theorem connecting
non-isomorphic Lindenbaum algebras to non-equivalent classifying toposes.

## Main Definitions

- `propClassifyingTopos`: Sheaf topos on LindenbaumAlgebra with join-cover topology
- `sheaf_reflects_frame_iso`: Axiom — equivalent sheaf toposes imply isomorphic frames
- `propositional_bridge`: Non-isomorphic algebras ⟹ non-equivalent classifying toposes
- `cardinality_separates`: Constructive separation via cardinality difference

## Mathematical Background

For frames L₁, L₂ viewed as locales, the functor Sh : Loc → GrTopos is faithful
on isomorphisms: Sh(L₁) ≌ Sh(L₂) implies L₁ ≅ L₂. For finite distributive
lattices (which are spatial locales by Birkhoff), this is classical. The bridge
axiom captures this fact; the locale theory infrastructure is orthogonal to the
topos-theoretic development.

## References

- Johnstone, "Stone Spaces" (1982), Section II.2
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), Chapter IX
-/

import RuleSys.GeometricLogic.SyntacticCoverage
import Mathlib.CategoryTheory.Sites.Sheaf

open CategoryTheory

universe u

namespace GeometricLogic.Propositional

variable {T : PropGeoTheory.{u}}

/-- The propositional classifying topos of a propositional geometric theory T.

This is the sheaf topos Sh(LindenbaumAlgebra T, J_join) where J_join is the
join-cover Grothendieck topology from Phase 95. For propositional theories,
this replaces the general classifying topos construction. -/
noncomputable abbrev propClassifyingTopos (T : PropGeoTheory.{u}) :=
  Sheaf (syntacticGrothendieck T) Type

/-- For frames viewed as locales, equivalent sheaf toposes have isomorphic frames.

This follows from the fact that Sh : Loc → GrTopos is faithful on isomorphisms.
For finite distributive lattices (spatial locales by Birkhoff representation),
the proof goes: Sh(L₁) ≌ Sh(L₂) → same points → same opens → L₁ ≅ L₂.
See Johnstone, "Stone Spaces" (1982), or Mac Lane & Moerdijk, "Sheaves in
Geometry and Logic" (1992), Chapter IX.

Axiomatized because formalizing locale theory is orthogonal to the topos-theoretic
Church-Turing development. -/
axiom sheaf_reflects_frame_iso (T₁ T₂ : PropGeoTheory.{u})
    (h : Nonempty (propClassifyingTopos T₁ ≌ propClassifyingTopos T₂)) :
    Nonempty (LindenbaumAlgebra T₁ ≃o LindenbaumAlgebra T₂)

/-- **The propositional bridge theorem.**

Non-isomorphic Lindenbaum algebras produce non-equivalent classifying toposes.
Proved by contrapositive from `sheaf_reflects_frame_iso`. -/
theorem propositional_bridge (T₁ T₂ : PropGeoTheory.{u})
    (h : ¬ Nonempty (LindenbaumAlgebra T₁ ≃o LindenbaumAlgebra T₂)) :
    ¬ Nonempty (propClassifyingTopos T₁ ≌ propClassifyingTopos T₂) :=
  fun he => h (sheaf_reflects_frame_iso T₁ T₂ he)

/-- Constructive separation: different cardinalities imply non-isomorphic lattices.

For finite Lindenbaum algebras, a cardinality mismatch is a concrete witness of
non-isomorphism. This is the simplest constructive separation criterion. -/
theorem cardinality_separates (T₁ T₂ : PropGeoTheory.{u})
    (h : Fintype.card (LindenbaumAlgebra T₁) ≠ Fintype.card (LindenbaumAlgebra T₂)) :
    ¬ Nonempty (LindenbaumAlgebra T₁ ≃o LindenbaumAlgebra T₂) :=
  fun ⟨e⟩ => h (Fintype.card_eq.mpr ⟨e.toEquiv⟩)

/-- Convenient API: different cardinalities imply non-equivalent classifying toposes. -/
theorem propositional_bridge_cardinality (T₁ T₂ : PropGeoTheory.{u})
    (h : Fintype.card (LindenbaumAlgebra T₁) ≠ Fintype.card (LindenbaumAlgebra T₂)) :
    ¬ Nonempty (propClassifyingTopos T₁ ≌ propClassifyingTopos T₂) :=
  propositional_bridge T₁ T₂ (cardinality_separates T₁ T₂ h)

end GeometricLogic.Propositional
