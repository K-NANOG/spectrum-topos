/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Syntactic Coverage on Lindenbaum Algebra

Defines the join-cover coverage on the Lindenbaum algebra of a propositional
geometric theory and generates the Grothendieck topology via `Coverage.toGrothendieck`.

## Main Definitions

- `presieveSupport`: The set of objects with a morphism in a presieve
- `joinCoverage`: Coverage where a presieve covers X iff join of support = X
- `syntacticGrothendieck`: Grothendieck topology via `Coverage.toGrothendieck`

## References

- Vickers, "Topology via Logic" (1989)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992)
-/

import RuleSys.GeometricLogic.PropositionalLindenbaum
import Mathlib.CategoryTheory.Sites.Coverage

open CategoryTheory

universe u

namespace GeometricLogic.Propositional

variable {T : PropGeoTheory.{u}}

/-- The support of a presieve: the set of objects having a morphism in the presieve.
In a thin category (preorder), this is the set of objects "in" the presieve. -/
def presieveSupport {X : LindenbaumAlgebra T} (S : Presieve X) :
    Set (LindenbaumAlgebra T) :=
  {Y | ∃ (f : Y ⟶ X), S f}

/-- The join-cover coverage on the Lindenbaum algebra. A presieve S on X is covering
iff `sSup (presieveSupport S) = X`. Pullback stability uses frame distributivity. -/
noncomputable def joinCoverage (T : PropGeoTheory.{u}) :
    Coverage (LindenbaumAlgebra T) where
  coverings X := {S | sSup (presieveSupport S) = X}
  pullback := by
    intro X Y f S hS
    -- f : Y ⟶ X (Y ≤ X), hS : sSup (presieveSupport S) = X
    -- Pullback presieve: include (Y ⊓ Z) → Y for each Z in support of S
    refine ⟨fun (A : LindenbaumAlgebra T) (_ : A ⟶ Y) =>
      ∃ (Z : LindenbaumAlgebra T) (h : Z ⟶ X), S h ∧ A = Y ⊓ Z, ?_, ?_⟩
    · -- Covering: sSup of pullback support = Y
      simp only [Set.mem_setOf_eq]
      apply le_antisymm
      · -- ≤ : all elements of support are ≤ Y
        apply sSup_le
        intro A hA
        exact leOfHom hA.choose
      · -- ≥ : Y ≤ sSup support, by frame distributivity
        have hle : Y ≤ X := leOfHom f
        calc Y = Y ⊓ X := (inf_eq_left.mpr hle).symm
          _ = Y ⊓ sSup (presieveSupport S) := by rw [hS]
          _ = ⨆ Z ∈ presieveSupport S, Y ⊓ Z := inf_sSup_eq
          _ ≤ sSup (presieveSupport fun (A : LindenbaumAlgebra T) (_ : A ⟶ Y) =>
              ∃ (Z : LindenbaumAlgebra T) (h : Z ⟶ X), S h ∧ A = Y ⊓ Z) := by
            apply iSup_le; intro Z; apply iSup_le; intro hZ
            apply le_sSup
            exact ⟨homOfLE inf_le_left, Z, hZ.choose, hZ.choose_spec, rfl⟩
    · -- FactorsThruAlong: trivial in thin category (Subsingleton morphisms)
      intro A g ⟨Z, h, hSh, hAeq⟩
      exact ⟨Z, homOfLE ((le_of_eq hAeq).trans inf_le_right), h, hSh, Subsingleton.elim _ _⟩

/-- The syntactic Grothendieck topology on the Lindenbaum algebra,
generated from the join-cover coverage via saturation. -/
noncomputable def syntacticGrothendieck (T : PropGeoTheory.{u}) :
    GrothendieckTopology (LindenbaumAlgebra T) :=
  (joinCoverage T).toGrothendieck

/-- A presieve S covers X in the join coverage iff the join of its support equals X. -/
theorem mem_joinCoverage_iff {X : LindenbaumAlgebra T} {S : Presieve X} :
    S ∈ (joinCoverage T).coverings X ↔ sSup (presieveSupport S) = X :=
  Iff.rfl

end GeometricLogic.Propositional
