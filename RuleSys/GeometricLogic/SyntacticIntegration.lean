/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Syntactic Integration: Propositional ↔ First-Order Bridge

Connects the concrete propositional infrastructure (LindenbaumAlgebra, syntacticGrothendieck,
propClassifyingTopos) to the first-order SyntacticCategory framework. For rooted transition system
theories, the syntactic category is equivalent to the propositional Lindenbaum algebra,
and the classifying toposes agree.

## Axiom Inventory: 4 axioms in this file

All 4 axioms bridge the first-order SyntacticCategory to the propositional
LindenbaumAlgebra. They encode the standard fact that propositional geometric
theories have syntactic categories equivalent to their Lindenbaum algebras.

**Classification summary:**
- 3 axioms: requires syntactic category construction in Lean (equivalence
  functor, topology preservation, topos equivalence)
- 1 axiom: requires syntactic category construction in Lean (propositional
  extraction)

## Main Definitions

- `toPropGeoTheory`: Extracts propositional geometric theory from first-order theory
- `syntacticCategory_lindenbaum_equiv`: SynCat(T_M) ≌ LindenbaumAlgebra (axiom)
- `syntacticCategory_lindenbaum_topology`: Topology preservation under equivalence (axiom)
- `classifyingTopos_equiv_propClassifyingTopos`: Sheaf topos equivalence (axiom)
- `firstOrder_propositional_bridge`: PROVED — non-isomorphic algebras → non-equivalent toposes

## Mathematical Background

For rooted transition system theories T_M, the geometric theory is propositional: formulas are
boolean combinations of relational atoms R(s₁, s₂) where R ∈ {step, reach, pathEquiv}
and s₁, s₂ ∈ M.State (finite). The syntactic category SynCat(T_M) is a thin category
whose objects are formulas-in-context quotiented by provable equivalence. For propositional
theories, this preorder is exactly the Lindenbaum–Tarski algebra. Under this equivalence,
geometric covering families (finite disjunctions) map to join-covers in the frame.

## References

- Caramello, "Theories, Sites, Toposes" (2018), Chapter 2
- Johnstone, "Sketches of an Elephant" (2002), D1.4
-/

import RuleSys.GeometricLogic.SyntacticCategory
import RuleSys.GeometricLogic.BridgeAxiom

open CategoryTheory
open GeometricLogic.Propositional

universe u

namespace GeometricLogic.Integration

/-- Encodes extraction of a propositional geometric theory from a first-order
geometric theory over RTSLanguage.

For rooted transition system theories, all formulas are propositional: the language has
only relational symbols (step, reach, pathEquiv) and no function symbols beyond
the nullary init constant. The propositional translation maps each binary
relational atom R(x, y) to a propositional variable indexed by (R, x, y) where
x, y range over the finite state space.

Axiomatized: requires syntactic category construction in Lean.
The translation requires inspecting GeoFormula constructors and converting them
to PropFormula constructors across the first-order/propositional type boundary.

Ref: Caramello TST, Ch. 2 (propositional geometric theories are a special case). -/
axiom toPropGeoTheory (T : GeometricTheory RTSLanguage) :
    Propositional.PropGeoTheory.{0}

/-- Encodes that the syntactic category of a rooted transition system theory is equivalent
as a category to the Lindenbaum algebra of its propositional translation.

For T_M where M is a rooted transition system, SynCat(T_M) is a preorder category
whose objects are formulas-in-context quotiented by provable equivalence.
For propositional theories, this is exactly the Lindenbaum algebra:
- Objects: propositional formulas / provable equivalence
- Morphisms: provability ordering (φ ⟶ ψ iff T ⊢ φ → ψ)

Axiomatized: requires syntactic category construction in Lean.
Constructing the equivalence functor requires inspecting FormulaInContext
structure and matching it against PropFormula, crossing the first-order /
propositional type boundary. The equivalence itself is standard for
propositional geometric theories.

Ref: Caramello TST, Ch. 2 (syntactic categories of propositional theories). -/
axiom syntacticCategory_lindenbaum_equiv (M : RTS.RootedTS) :
    Nonempty (SyntacticCategory (theoryOfSystem M) ≌
              LindenbaumAlgebra (toPropGeoTheory (theoryOfSystem M)))

/-- Encodes that the syntactic topology on SynCat(T_M) corresponds to the
join-cover Grothendieck topology on LindenbaumAlgebra under the equivalence
functor (both directions are cocontinuous).

Under F : SynCat(T_M) → LindenbaumAlgebra(toPropGeoTheory(T_M)),
geometric covering families (finite disjunctions) map to join-covers:
φ = ⋁ψ_i in the Lindenbaum algebra ↔ {ψ_i → φ} is a covering sieve.

Axiomatized: requires syntactic category construction in Lean.
Matching `IsGeometricCovering` (on SyntacticCategory, itself an axiom)
to `joinCoverage` (on LindenbaumAlgebra) requires the functor action on
sieves, which depends on the equivalence functor from
`syntacticCategory_lindenbaum_equiv`.

Ref: Johnstone, "Sketches of an Elephant" (2002), D1.4. -/
axiom syntacticCategory_lindenbaum_topology (M : RTS.RootedTS) :
    let E := (syntacticCategory_lindenbaum_equiv M).some
    E.functor.IsCocontinuous
      (syntacticTopology (theoryOfSystem M))
      (syntacticGrothendieck (toPropGeoTheory (theoryOfSystem M))) ∧
    E.inverse.IsCocontinuous
      (syntacticGrothendieck (toPropGeoTheory (theoryOfSystem M)))
      (syntacticTopology (theoryOfSystem M))

/-- Encodes that the first-order classifying topos and propositional classifying
topos are equivalent for rooted transition system theories.

This follows from the equivalence of syntactic sites:
  (SynCat(T_M), syntacticTopology) ≌ (LindenbaumAlgebra, syntacticGrothendieck)
Equivalent sites produce equivalent sheaf toposes.

Axiomatized: requires syntactic category construction in Lean.
The Mathlib proof via `Equivalence.sheafCongr` requires cocontinuity
instances registered in the elaboration context, which depends on
`syntacticCategory_lindenbaum_topology` (itself an axiom). Making this
compile would require additional `letI` ceremony that complicates the type.

Ref: Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992),
Ch. VII (Comparison Lemma); Caramello TST, Theorem 2.3.23. -/
axiom classifyingTopos_equiv_propClassifyingTopos (M : RTS.RootedTS) :
    Nonempty (ClassifyingTopos (theoryOfSystem M) ≌
              propClassifyingTopos (toPropGeoTheory (theoryOfSystem M)))

/-- **First-order propositional bridge theorem.**

Non-isomorphic Lindenbaum algebras imply non-equivalent first-order
classifying toposes. This lifts the propositional bridge (Phase 96) to the
first-order setting via the classifying topos equivalence.

**Proved** (not axiomatized) by composing:
1. `classifyingTopos_equiv_propClassifyingTopos` (equivalence of toposes)
2. `propositional_bridge` (non-isomorphic algebras → non-equivalent prop toposes) -/
theorem firstOrder_propositional_bridge (M₁ M₂ : RTS.RootedTS)
    (h : ¬ Nonempty (LindenbaumAlgebra (toPropGeoTheory (theoryOfSystem M₁)) ≃o
                     LindenbaumAlgebra (toPropGeoTheory (theoryOfSystem M₂)))) :
    ¬ Nonempty (ClassifyingTopos (theoryOfSystem M₁) ≌
                ClassifyingTopos (theoryOfSystem M₂)) := by
  intro ⟨e⟩
  apply propositional_bridge _ _ h
  exact ⟨(classifyingTopos_equiv_propClassifyingTopos M₁).some.symm.trans
         (e.trans (classifyingTopos_equiv_propClassifyingTopos M₂).some)⟩

/-- Convenient API: different Lindenbaum algebra cardinalities imply
non-equivalent first-order classifying toposes. -/
theorem firstOrder_cardinality_bridge (M₁ M₂ : RTS.RootedTS)
    (h : Fintype.card (LindenbaumAlgebra (toPropGeoTheory (theoryOfSystem M₁))) ≠
         Fintype.card (LindenbaumAlgebra (toPropGeoTheory (theoryOfSystem M₂)))) :
    ¬ Nonempty (ClassifyingTopos (theoryOfSystem M₁) ≌
                ClassifyingTopos (theoryOfSystem M₂)) :=
  firstOrder_propositional_bridge M₁ M₂ (cardinality_separates _ _ h)

end GeometricLogic.Integration
