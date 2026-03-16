/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bi-Heyting Operations and Structural Assessment for L₃₀

This file computes all bi-Heyting operations on the 30-element spectrum lattice L₃₀
using the Birkhoff downset representation: Heyting implication, pseudocomplement,
co-Heyting negation, boundary operators, double negation, and the Boolean core.

## Mathematical Content

For a finite distributive lattice L ≅ O(J), the Heyting implication is:
  a → b = largest z with z ∧ a ≤ b

Since L₃₀ is finite with decidable equality and ordering, we compute this directly:
  birkhoffHimp x y = ⊔{z ∈ L₃₀ : z ⊓ x ≤ y}

Derived operations:
- Pseudocomplement: ¬x = x → ⊥
- Co-Heyting negation: ~x = ⊤ \ x (using birkhoffSdiff)
- Heyting boundary: ∂x = x ∧ ¬x
- Double negation: ¬¬x

## Main Results

1. `birkhoffHimp` — Heyting implication with verified adjunction
2. Pseudocomplement, co-Heyting negation, boundary, double negation
3. Full catalogs: ¬x, ~x for all 13 named equivalences
4. Boundary analysis: nontrivial boundary count
5. Boolean core: regular elements = {⊥, ⊤}
6. Structural assessment: L₃₀ is maximally intuitionistic

## References

- Davey & Priestley, "Introduction to Lattices and Order" (2002)
- Birkhoff, "Lattice Theory" (1967)
-/

import RuleSys.SubtoposLattice.BirkhoffDownsets

set_option autoImplicit false

universe u

namespace RTS

namespace SpectrumElement

/-!
## Part 1: Heyting Implication via Direct Computation

For a finite lattice, the Heyting implication a → b is the largest element z
with z ∧ a ≤ b. We compute this as the join of all such z.
-/

/-- Heyting implication in L₃₀: birkhoffHimp x y = ⊔{z ∈ L₃₀ : z ⊓ x ≤ y}.
This is the largest z with z ∧ x ≤ y, computed by filtering all 30 elements
and taking their join. -/
def birkhoffHimp (x y : SpectrumElement) : SpectrumElement :=
  let candidates := allElements.filter (fun z => decide (z ⊓ x ≤ y))
  candidates.foldl (· ⊔ ·) ⊥

/-!
### Heyting Adjunction
-/

/-- The Heyting implication satisfies the left adjunction: (x → y) ∧ x ≤ y. -/
theorem birkhoffHimp_property :
    ∀ x y : SpectrumElement, birkhoffHimp x y ⊓ x ≤ y := by native_decide

/-- The Heyting implication is the LARGEST z with z ∧ x ≤ y. -/
theorem birkhoffHimp_largest :
    ∀ x y z : SpectrumElement, z ⊓ x ≤ y → z ≤ birkhoffHimp x y := by native_decide

/-!
## Part 2: Derived Operations
-/

/-- Pseudocomplement (Heyting negation): ¬x = x → ⊥.
The largest element z with z ∧ x = ⊥. -/
def pseudocomplement (x : SpectrumElement) : SpectrumElement := birkhoffHimp x ⊥

/-- Co-Heyting negation: ~x = ⊤ \ x (co-Heyting subtraction from top).
The smallest element z with z ∨ x = ⊤. -/
def coHeytingNeg (x : SpectrumElement) : SpectrumElement := birkhoffSdiff ⊤ x

/-- Heyting boundary: ∂x = x ∧ ¬x.
Measures the failure of excluded middle for x. ∂x = ⊥ iff x is complemented. -/
def heytingBoundary (x : SpectrumElement) : SpectrumElement := x ⊓ pseudocomplement x

/-- Double negation: ¬¬x.
The closure operator for the Boolean core. -/
def doubleNeg (x : SpectrumElement) : SpectrumElement := pseudocomplement (pseudocomplement x)

/-!
### Basic Properties
-/

/-- The pseudocomplement is disjoint from x: ¬x ∧ x = ⊥. -/
theorem pseudocomplement_property :
    ∀ x : SpectrumElement, pseudocomplement x ⊓ x = ⊥ := by native_decide

/-- The co-Heyting negation covers x: ~x ∨ x = ⊤. -/
theorem coHeytingNeg_property :
    ∀ x : SpectrumElement, coHeytingNeg x ⊔ x = ⊤ := by native_decide

/-- The Heyting boundary is below x. -/
theorem heytingBoundary_le :
    ∀ x : SpectrumElement, heytingBoundary x ≤ x := by native_decide

/-- Double negation is inflationary: x ≤ ¬¬x. -/
theorem doubleNeg_ge :
    ∀ x : SpectrumElement, x ≤ doubleNeg x := by native_decide

/-- Double negation is idempotent: ¬¬(¬¬x) = ¬¬x. -/
theorem doubleNeg_idempotent :
    ∀ x : SpectrumElement, doubleNeg (doubleNeg x) = doubleNeg x := by native_decide

/-!
## Part 3: Pseudocomplement Catalog

The pseudocomplement structure of L₃₀ is extreme: since J(L₃₀) is connected
(traces ≤ every join-irreducible), the only element with ¬x ≠ ⊥ is ⊥ itself.

For any non-⊥ element x, there exists a join-irreducible j ≤ x, and since
traces ≤ j for all j ∈ J, we get traces ≤ x for all non-⊥ x. Thus ¬x must
satisfy ¬x ∧ x = ⊥, meaning ¬x has no join-irreducibles in common with x.
But traces ≤ ¬x would also require traces ≤ ¬x, and traces ≤ x, contradicting
¬x ∧ x = ⊥ (since traces ≤ both). So ¬x = ⊥ for all non-⊥ x.
-/

/-- ¬⊥ = ⊤: the pseudocomplement of bottom is top. -/
theorem pseudocomplement_enabledness :
    pseudocomplement .enabledness = .bisimulation := by native_decide

/-- ¬T = ⊥: traces already covers all join-irreducibles via connectivity. -/
theorem pseudocomplement_traces :
    pseudocomplement .traces = .enabledness := by native_decide

/-- ¬F = ⊥. -/
theorem pseudocomplement_failures :
    pseudocomplement .failures = .enabledness := by native_decide

/-- ¬RV = ⊥. -/
theorem pseudocomplement_revivals :
    pseudocomplement .revivals = .enabledness := by native_decide

/-- ¬R = ⊥. -/
theorem pseudocomplement_readiness :
    pseudocomplement .readiness = .enabledness := by native_decide

/-- ¬IF = ⊥. -/
theorem pseudocomplement_impossibleFutures :
    pseudocomplement .impossibleFutures = .enabledness := by native_decide

/-- ¬S = ⊥. -/
theorem pseudocomplement_simulation :
    pseudocomplement .simulation = .enabledness := by native_decide

/-- ¬FT = ⊥. -/
theorem pseudocomplement_failureTraces :
    pseudocomplement .failureTraces = .enabledness := by native_decide

/-- ¬PF = ⊥. -/
theorem pseudocomplement_possibleFutures :
    pseudocomplement .possibleFutures = .enabledness := by native_decide

/-- ¬RT = ⊥. -/
theorem pseudocomplement_readyTraces :
    pseudocomplement .readyTraces = .enabledness := by native_decide

/-- ¬RS = ⊥. -/
theorem pseudocomplement_readySimulation :
    pseudocomplement .readySimulation = .enabledness := by native_decide

/-- ¬2S = ⊥. -/
theorem pseudocomplement_twoNestedSim :
    pseudocomplement .twoNestedSim = .enabledness := by native_decide

/-- ¬⊤ = ⊥: the pseudocomplement of top is bottom. -/
theorem pseudocomplement_bisimulation :
    pseudocomplement .bisimulation = .enabledness := by native_decide

/-- Summary: every non-⊥ element has trivial pseudocomplement.
This is a direct consequence of J being connected. -/
theorem pseudocomplement_trivial :
    ∀ x : SpectrumElement, x ≠ ⊥ → pseudocomplement x = ⊥ := by native_decide

/-!
## Part 4: Co-Heyting Negation Catalog

Dually, since J is connected, the co-Heyting negation ~x = ⊤ \ x equals ⊤
for all non-⊤ elements. The meet-irreducible structure is also connected
(by duality), so the only element with ~x ≠ ⊤ is ⊤ itself.
-/

/-- ~⊥ = ⊤: the co-Heyting negation of bottom is top. -/
theorem coHeytingNeg_enabledness :
    coHeytingNeg .enabledness = .bisimulation := by native_decide

/-- ~T = ⊤. -/
theorem coHeytingNeg_traces :
    coHeytingNeg .traces = .bisimulation := by native_decide

/-- ~F = ⊤. -/
theorem coHeytingNeg_failures :
    coHeytingNeg .failures = .bisimulation := by native_decide

/-- ~RV = ⊤. -/
theorem coHeytingNeg_revivals :
    coHeytingNeg .revivals = .bisimulation := by native_decide

/-- ~R = ⊤. -/
theorem coHeytingNeg_readiness :
    coHeytingNeg .readiness = .bisimulation := by native_decide

/-- ~IF = ⊤. -/
theorem coHeytingNeg_impossibleFutures :
    coHeytingNeg .impossibleFutures = .bisimulation := by native_decide

/-- ~S = ⊤. -/
theorem coHeytingNeg_simulation :
    coHeytingNeg .simulation = .bisimulation := by native_decide

/-- ~FT = ⊤. -/
theorem coHeytingNeg_failureTraces :
    coHeytingNeg .failureTraces = .bisimulation := by native_decide

/-- ~PF = ⊤. -/
theorem coHeytingNeg_possibleFutures :
    coHeytingNeg .possibleFutures = .bisimulation := by native_decide

/-- ~RT = ⊤. -/
theorem coHeytingNeg_readyTraces :
    coHeytingNeg .readyTraces = .bisimulation := by native_decide

/-- ~RS = ⊤. -/
theorem coHeytingNeg_readySimulation :
    coHeytingNeg .readySimulation = .bisimulation := by native_decide

/-- ~2S = ⊤. -/
theorem coHeytingNeg_twoNestedSim :
    coHeytingNeg .twoNestedSim = .bisimulation := by native_decide

/-- ~⊤ = ⊥: the co-Heyting negation of top is bottom. -/
theorem coHeytingNeg_bisimulation :
    coHeytingNeg .bisimulation = .enabledness := by native_decide

/-- Summary: every non-⊤ element has maximal co-Heyting negation.
This is the dual of pseudocomplement_trivial. -/
theorem coHeytingNeg_trivial :
    ∀ x : SpectrumElement, x ≠ ⊤ → coHeytingNeg x = ⊤ := by native_decide

/-!
## Part 5: Heyting Boundary Catalog

Since ¬x = ⊥ for all non-⊥ x, the Heyting boundary ∂x = x ∧ ¬x = x ∧ ⊥ = ⊥
for all x. This means EVERY element has trivial boundary.

This is a maximally degenerate situation: the Heyting negation collapses so
completely that the boundary operator carries no information.
-/

/-- All Heyting boundaries are trivial. -/
theorem heytingBoundary_trivial :
    ∀ x : SpectrumElement, heytingBoundary x = ⊥ := by native_decide

/-- Elements with nontrivial Heyting boundary. -/
def nontrivialBoundaryElements : List SpectrumElement :=
  allElements.filter (fun x => decide (heytingBoundary x ≠ ⊥))

/-- There are 0 elements with nontrivial Heyting boundary.
Since ¬x = ⊥ for all x ≠ ⊥, every boundary x ∧ ¬x = x ∧ ⊥ = ⊥. -/
theorem nontrivialBoundaryElements_count :
    nontrivialBoundaryElements.length = 0 := by native_decide

/-!
## Part 6: Double Negation and Boolean Core

Since ¬x = ⊥ for all x ≠ ⊥, we get ¬¬x = ¬⊥ = ⊤ for all x ≠ ⊥.
And ¬¬⊥ = ¬⊤ = ⊥. So ¬¬ maps everything to {⊥, ⊤}.

An element x is "regular" if ¬¬x = x. This means x = ⊥ or x = ⊤.
The Boolean core (regular elements) is exactly {⊥, ⊤}.
-/

/-- The regular elements: those fixed by double negation. -/
def regularElements : List SpectrumElement :=
  allElements.filter (fun x => decide (doubleNeg x = x))

/-- There are exactly 2 regular elements. -/
theorem regularElements_count :
    regularElements.length = 2 := by native_decide

/-- The regular elements are exactly ⊥ and ⊤. -/
theorem regularElements_eq :
    regularElements = [.enabledness, .bisimulation] := by native_decide

/-- Every regular element is complemented. -/
theorem regularElements_are_complemented :
    ∀ x : SpectrumElement, doubleNeg x = x → isComplemented x := by native_decide

/-- Double negation always produces a regular element. -/
theorem doubleNeg_maps_to_regular :
    ∀ x : SpectrumElement, doubleNeg x ∈ regularElements := by native_decide

/-- The double negation closure maps non-⊥ elements to ⊤.
This is the extreme case: the Boolean reflection L → L_¬¬ collapses
28 of 30 elements to ⊤. -/
theorem doubleNeg_collapses :
    ∀ x : SpectrumElement, x ≠ ⊥ → doubleNeg x = ⊤ := by native_decide

/-!
## Part 7: Key Named Heyting Implications

The Heyting implication a → b is more informative than ¬ or ~, because it
captures relative "information content" between specific elements.
-/

/-- F → S = S: failures implies simulation gives back simulation.
Since S is not below F (they are incomparable), but F → S captures the
largest z with z ∧ F ≤ S. That largest z is S itself. -/
theorem himp_failures_simulation :
    birkhoffHimp .failures .simulation = .simulation := by native_decide

/-- T → F = ⊤: traces implies failures is the whole lattice.
Since T ≤ F (traces is below failures in the spectrum), we have
x ∧ T ≤ T ≤ F for all x, so every element satisfies the condition. -/
theorem himp_traces_failures :
    birkhoffHimp .traces .failures = .bisimulation := by native_decide

/-- RS → S = S: ready simulation implies simulation gives S.
S ≤ RS, so the implication RS → S captures the elements z with z ∧ RS ≤ S.
The largest such z is S itself. -/
theorem himp_readySimulation_simulation :
    birkhoffHimp .readySimulation .simulation = .simulation := by native_decide

/-- PF → IF = IF: possible futures implies impossible futures gives IF.
Since IF ≤ PF, we have z ∧ PF ≤ IF iff z ≤ (PF → IF). The largest such z
is IF itself (since IF ∧ PF = IF ≤ IF). -/
theorem himp_possibleFutures_impossibleFutures :
    birkhoffHimp .possibleFutures .impossibleFutures = .impossibleFutures := by native_decide

/-- S → B = ⊤: simulation implies bisimulation is the whole lattice.
Since S ≤ B, every z satisfies z ∧ S ≤ S ≤ B. -/
theorem himp_simulation_bisimulation :
    birkhoffHimp .simulation .bisimulation = .bisimulation := by native_decide

/-- T → S = ⊤: traces implies simulation is the whole lattice.
Since T ≤ S, every z satisfies z ∧ T ≤ T ≤ S. -/
theorem himp_traces_simulation :
    birkhoffHimp .traces .simulation = .bisimulation := by native_decide

/-- Heyting implication of comparable elements: if x ≤ y then x → y = ⊤.
This is the deduction theorem: if x already implies y in the lattice order,
then x → y is trivially true (⊤). -/
theorem birkhoffHimp_of_le :
    ∀ x y : SpectrumElement, x ≤ y → birkhoffHimp x y = ⊤ := by native_decide

/-- Heyting self-implication: x → x = ⊤ for all x. -/
theorem birkhoffHimp_self :
    ∀ x : SpectrumElement, birkhoffHimp x x = ⊤ := by native_decide

/-!
## Part 8: Structural Assessment

The bi-Heyting algebra structure of L₃₀ reveals an extreme pattern:

1. **Collapsed negations**: ¬x = ⊥ for all x ≠ ⊥, and ~x = ⊤ for all x ≠ ⊤.
   This is a direct consequence of J(L₃₀) being connected.

2. **Trivial boundaries**: ∂x = ⊥ for ALL 30 elements.

3. **Minimal Boolean core**: Only {⊥, ⊤} are regular (¬¬-closed).
   The Boolean reflection L₃₀ → L₃₀_¬¬ collapses 28 elements to ⊤.

4. **Informative implications**: Despite collapsed negations, the Heyting
   implication a → b is non-trivial when a and b are incomparable.

This is the most extreme possible case for a connected J: the negation
operations degenerate completely, but the relative implication structure
preserves all the lattice-theoretic information.
-/

/-- The Boolean core has exactly 2 elements: L₃₀ is maximally non-Boolean.
Combined with J connected (1 component), this confirms the spectrum lattice
has the minimum possible number of complemented elements for any non-trivial
distributive lattice. -/
theorem boolean_core_minimal :
    regularElements.length = complementedElements.length := by native_decide

/-- Regular elements coincide with complemented elements.
In a finite distributive lattice, x is regular (¬¬x = x) iff x is complemented.
We verify this computationally. -/
theorem regular_eq_complemented :
    regularElements = complementedElements := by native_decide

/-- L₃₀ structural assessment: the lattice is maximally non-Boolean.
- Only 2 of 30 elements are regular/complemented (⊥ and ⊤)
- All 30 Heyting boundaries are trivial
- The pseudocomplement collapses: ¬x = ⊥ for all x ≠ ⊥
- The co-Heyting negation collapses: ~x = ⊤ for all x ≠ ⊤
This is the extreme consequence of J(L₃₀) having exactly 1 connected component. -/
theorem spectrum_structural_assessment :
    -- Boolean core size = 2
    regularElements.length = 2 ∧
    -- No nontrivial boundaries
    nontrivialBoundaryElements.length = 0 ∧
    -- Regular = complemented
    regularElements = complementedElements ∧
    -- Only ⊥ and ⊤ are regular
    regularElements = [.enabledness, .bisimulation] := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end SpectrumElement

end RTS
