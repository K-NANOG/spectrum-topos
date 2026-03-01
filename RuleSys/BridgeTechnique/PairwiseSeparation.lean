/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pairwise Separation and Invariant Transfer

The first application of Caramello's bridge technique to transition systems and
process equivalences. We demonstrate concrete separation of classifying toposes
for three small systems, and establish a framework for transferring invariants
across deductively equivalent quotient theories.

## Main Results

### Pairwise Non-Equivalence (all proved)
- `singleLoop_toggle_nonequiv`: Sh(singleLoop) ≇ Sh(toggle) via card 2 ≠ 4
- `singleLoop_chain3_nonequiv`: Sh(singleLoop) ≇ Sh(chain3) via card 2 ≠ 8
- `toggle_chain3_nonequiv`: Sh(toggle) ≇ Sh(chain3) via card 4 ≠ 8
- `all_pairs_nonequivalent`: Summary conjunction of all three

### Invariant Transfer Framework
- `IsMoritaInvariant`: A property P of quotient theories that transfers across
  deductively equivalent quotients
- `deductiveEquiv_preserves_card`: Deductive equivalence preserves Lindenbaum
  algebra cardinality (proved)
- `card_match_is_morita_invariant`: Cardinality matching is a Morita invariant (proved)
- `subtopos_count_invariant`: Grothendieck topology count transfers across
  deductive equivalence (axiomatized)

## Mathematical Background

Caramello's bridge technique (2018) uses classifying toposes as "bridges" to
transfer invariants between theories. A Morita invariant is a topos-theoretic
property that is preserved by equivalence of classifying toposes. The simplest
example is the cardinality of the Lindenbaum algebra: if two theories have
classifying toposes that are equivalent, their Lindenbaum algebras must be
isomorphic (by the sheaf-reflects-frame axiom), hence have the same cardinality.

This is the first formalization applying the bridge technique to transition
systems in the sense of process algebra. See also Hora (2024) for automata.

## References

- Caramello, "Theories, Sites, Toposes" (2018), Chapters 2-3
- Hora, "Toposes of Automata" (2024)
- van Glabbeek, "The Linear Time-Branching Time Spectrum" (1990, 2001)
-/

import RuleSys.SubtoposLattice.SpectrumEmbedding
import RuleSys.GeometricLogic.BridgeAxiom

set_option autoImplicit false

universe u

open CategoryTheory GeometricLogic.Propositional Ruliology

/-!
## Section 1: Pairwise Non-Equivalence

We prove that the three small systems (singleLoop, toggle, chain3) have
pairwise non-equivalent classifying toposes. Each proof uses the cardinality
bridge: different Lindenbaum algebra sizes imply non-isomorphic algebras,
which imply non-equivalent sheaf toposes.
-/

/-- singleLoop and toggle have non-equivalent classifying toposes.
Proof: Lindenbaum algebra cardinalities differ (2 ≠ 4). -/
theorem singleLoop_toggle_nonequiv :
    ¬ Nonempty (propClassifyingTopos singleLoopTheory ≌
                propClassifyingTopos toggleTheory) :=
  propositional_bridge_cardinality singleLoopTheory toggleTheory (by
    have h1 := singleLoop_algebra_card
    have h2 := toggle_algebra_card
    omega)

/-- singleLoop and chain3 have non-equivalent classifying toposes.
Proof: Lindenbaum algebra cardinalities differ (2 ≠ 8). -/
theorem singleLoop_chain3_nonequiv :
    ¬ Nonempty (propClassifyingTopos singleLoopTheory ≌
                propClassifyingTopos chain3Theory) :=
  propositional_bridge_cardinality singleLoopTheory chain3Theory (by
    have h1 := singleLoop_algebra_card
    have h2 := chain3_algebra_card
    omega)

/-- toggle and chain3 have non-equivalent classifying toposes.
Proof: Lindenbaum algebra cardinalities differ (4 ≠ 8). -/
theorem toggle_chain3_nonequiv :
    ¬ Nonempty (propClassifyingTopos toggleTheory ≌
                propClassifyingTopos chain3Theory) :=
  propositional_bridge_cardinality toggleTheory chain3Theory (by
    have h1 := toggle_algebra_card
    have h2 := chain3_algebra_card
    omega)

/-!
## Section 2: All-Pairs Summary

A single theorem collecting all three pairwise non-equivalences.
-/

/-- All three small systems have pairwise non-equivalent classifying toposes.

This is the concrete demonstration of the bridge technique: three systems
with different state-space sizes produce topos-theoretically distinct
classifying toposes, as witnessed by Lindenbaum algebra cardinality. -/
theorem all_pairs_nonequivalent :
    (¬ Nonempty (propClassifyingTopos singleLoopTheory ≌ propClassifyingTopos toggleTheory)) ∧
    (¬ Nonempty (propClassifyingTopos singleLoopTheory ≌ propClassifyingTopos chain3Theory)) ∧
    (¬ Nonempty (propClassifyingTopos toggleTheory ≌ propClassifyingTopos chain3Theory)) :=
  ⟨singleLoop_toggle_nonequiv, singleLoop_chain3_nonequiv, toggle_chain3_nonequiv⟩

/-!
## Section 3: Morita Invariant Framework

A Morita invariant for propositional geometric theories is a property of
quotient theories that transfers across deductive equivalence. This is the
analogue of Caramello's notion at the quotient theory level.
-/

/-- A Morita invariant for propositional geometric theories: a property P
of quotient theories that transfers across deductively equivalent quotients.

Concretely, P is a Morita invariant if whenever Q₁ and Q₂ have
order-isomorphic Lindenbaum algebras, then P Q₁ ↔ P Q₂. -/
def IsMoritaInvariant {T : PropGeoTheory.{u}}
    (P : PropQuotientTheory T → Prop) : Prop :=
  ∀ Q₁ Q₂ : PropQuotientTheory T, Q₁.DeductivelyEquiv Q₂ → (P Q₁ ↔ P Q₂)

/-!
## Section 4: Cardinality as Morita Invariant

The cardinality of the Lindenbaum algebra is a Morita invariant: deductive
equivalence (= order-isomorphism of Lindenbaum algebras) preserves the
number of elements. This is the simplest invariant and underlies the
pairwise separation theorems above.
-/

/-- Deductive equivalence preserves Lindenbaum algebra cardinality.

Proof: An order isomorphism has an underlying equivalence of types,
and `Fintype.card_congr` transports cardinality across equivalences. -/
theorem deductiveEquiv_preserves_card {T : PropGeoTheory.{u}}
    (Q₁ Q₂ : PropQuotientTheory T) (h : Q₁.DeductivelyEquiv Q₂) :
    Fintype.card (LindenbaumAlgebra Q₁.toTheory) =
    Fintype.card (LindenbaumAlgebra Q₂.toTheory) := by
  obtain ⟨e⟩ := h
  exact Fintype.card_congr e.toEquiv

/-- Cardinality matching is a Morita invariant: the property
"Lindenbaum algebra has exactly n elements" is preserved by deductive
equivalence.

Proof: By `deductiveEquiv_preserves_card`, the cardinality is equal
across deductively equivalent quotients, so matching a fixed n is
equivalent. -/
theorem card_match_is_morita_invariant {T : PropGeoTheory.{u}} (n : ℕ) :
    IsMoritaInvariant (fun (Q : PropQuotientTheory T) =>
      Fintype.card (LindenbaumAlgebra Q.toTheory) = n) := by
  intro Q₁ Q₂ h
  constructor
  · intro hq; rw [← hq]; exact (deductiveEquiv_preserves_card Q₁ Q₂ h).symm
  · intro hq; rw [← hq]; exact deductiveEquiv_preserves_card Q₁ Q₂ h

/-!
## Section 5: Subtopos Count Invariant

The number of Grothendieck topologies on a Lindenbaum algebra is a more
refined invariant than cardinality. It counts the number of distinct
subtoposes of the classifying topos, or equivalently the number of
deductive-equivalence classes of quotient theories (by Caramello duality).

This is axiomatized because the full proof requires:
1. Deductive equivalence gives an order isomorphism of Lindenbaum algebras
2. Order isomorphism induces a bijection on Grothendieck topologies
3. Bijection preserves finite cardinality

Step 2 follows from the fact that a Grothendieck topology J on C
transports along a categorical equivalence C ≌ D to a topology on D,
and this transport is bijective. For finite distributive lattices viewed
as categories, an order isomorphism is a categorical equivalence.
-/

/-- The number of Grothendieck topologies on a Lindenbaum algebra transfers
across deductive equivalence. This follows from the Duality Theorem: isomorphic
algebras have bijective sets of Grothendieck topologies. -/
axiom subtopos_count_invariant {T : PropGeoTheory.{u}}
    (Q₁ Q₂ : PropQuotientTheory T)
    (h : Q₁.DeductivelyEquiv Q₂) (n : ℕ)
    (h₁ : ∃ (S : Finset (GrothendieckTopology (LindenbaumAlgebra Q₁.toTheory))),
           S.card = n) :
    ∃ (S : Finset (GrothendieckTopology (LindenbaumAlgebra Q₂.toTheory))),
      S.card = n
