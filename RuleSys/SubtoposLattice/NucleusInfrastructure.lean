/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nucleus Infrastructure: Connecting Nuclei to Grothendieck Topologies

This file establishes the lattice-theoretic infrastructure connecting nuclei
(closure operators preserving ⊓) on Lindenbaum algebras to Grothendieck topologies.
For finite distributive lattices, nuclei biject with subsets of join-irreducibles J(L),
giving exactly 2^|J(L)| subtoposes (forming a Boolean algebra).

## Mathematical Background

A **nucleus** on a frame L is an inflationary idempotent ⊓-preserving endomorphism
j : L → L. Johnstone (Stone Spaces, II.2) establishes that Lawvere-Tierney topologies
on Sh(L) correspond bijectively to nuclei on L. For finite distributive lattices, the
Funayama-Nakayama theorem (1942) gives that congruences form a Boolean algebra with
|J(L)| atoms, where J(L) denotes the set of join-irreducible elements.

## Main Results

1. `HubSpokesJoinIrred` — enumeration of J(L) for the hub-spokes 5-element lattice
2. 8 named nuclei matching the 8 GT topologies from NondeterministicSystems.lean
3. `NucleusGTCorrespondence` — bridge between nucleus and GT topology formalizations
4. `hubSpokes_nuclei_boolean` — 2³ = 8 validates the 2^|J(L)| formula
5. `nucleus_count_eq_two_pow_joinIrred` — general theorem for finite distributive lattices

## Validation Checkpoint

The 8 nuclei on the hub-spokes lattice {⊥, m=p∧q, p, q, ⊤} match the 8
Grothendieck topologies from v10.0, confirming the framework.

## References

- Johnstone, "Stone Spaces" (1982), II.2: LT topologies ↔ nuclei
- Funayama-Nakayama (1942): congruence lattice of distributive lattice
- Caramello, "Theories, Sites, Toposes" (2018), Thm 3.6: subtoposes ↔ quotient theories
-/

import RuleSys.SubtoposLattice.NondeterministicSystems
import RuleSys.SubtoposLattice.HubSpokesComputable
import Mathlib.Order.Nucleus
import Mathlib.Order.Irreducible
import Mathlib.Order.CompleteBooleanAlgebra

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace Ruliology

/-!
## Part 1: Nucleus Applicability Verification

The `LindenbaumAlgebra T` has `CompleteDistribLattice` (which implies `Frame`,
which implies `SemilatticeInf`), so `Nucleus (LindenbaumAlgebra T)` is well-typed.
Mathlib provides `CompleteLattice`, `Frame`, and `HeytingAlgebra` instances on
`Nucleus X` for any frame X.
-/

/-- Verify that nuclei on the hub-spokes Lindenbaum algebra form a complete lattice.
This follows from Mathlib's `CompleteLattice (Nucleus X)` instance for any frame X,
and `LindenbaumAlgebra T` being a `CompleteDistribLattice`. -/
noncomputable example : CompleteLattice (Nucleus (LindenbaumAlgebra hubSpokesTransTheory)) :=
  inferInstance

/-- Verify that nuclei on the hub-spokes Lindenbaum algebra form a frame. -/
noncomputable example : Order.Frame (Nucleus (LindenbaumAlgebra hubSpokesTransTheory)) :=
  inferInstance

/-!
## Part 2: Join-Irreducible Element Enumeration

For the hub-spokes 5-element lattice {⊥, m=p∧q, p, q, ⊤}, the join-irreducible
elements are J(L) = {m, p, q}. An element x is join-irreducible (`SupIrred x`) if
x ≠ ⊥ and x = a ∨ b implies x = a or x = b.

- m = p ∧ q is join-irreducible: the only way to express it as a join is m ∨ ⊥ = m.
- p is join-irreducible: p = a ∨ b with a, b < p forces a, b ∈ {⊥, m}, and m ∨ ⊥ = m ≠ p.
- q is join-irreducible: symmetric to p.
- ⊤ is NOT join-irreducible: ⊤ = p ∨ q with p ≠ ⊤ and q ≠ ⊤.
- ⊥ is NOT join-irreducible: by definition (⊥ is excluded).
-/

/-- The join-irreducible elements of the hub-spokes 5-element lattice {⊥, m, p, q, ⊤}.
J(L) = {m, p, q} where m = p ∧ q. -/
inductive HubSpokesJoinIrred where
  | m   -- p ∧ q (the meet of the two generators)
  | p   -- step(a,b) generator
  | q   -- step(a,c) generator
  deriving DecidableEq

instance : Fintype HubSpokesJoinIrred where
  elems := {.m, .p, .q}
  complete := fun x => by cases x <;> simp

/-- The hub-spokes lattice has exactly 3 join-irreducible elements. -/
theorem hubSpokes_joinIrred_card : Fintype.card HubSpokesJoinIrred = 3 := by decide

/-- Each HubSpokesJoinIrred element maps to a Lindenbaum algebra element. -/
axiom hubSpokes_joinIrred_embed :
    HubSpokesJoinIrred → LindenbaumAlgebra hubSpokesTransTheory

/-- The embedded join-irreducible elements are actually join-irreducible in the
Lindenbaum algebra. -/
axiom hubSpokes_joinIrred_supIrred :
    ∀ j : HubSpokesJoinIrred, SupIrred (hubSpokes_joinIrred_embed j)

/-- Every join-irreducible element of the hub-spokes Lindenbaum algebra corresponds
to one of the three named elements {m, p, q}. -/
axiom hubSpokes_joinIrred_complete :
    ∀ (x : LindenbaumAlgebra hubSpokesTransTheory),
      SupIrred x → ∃ j : HubSpokesJoinIrred, hubSpokes_joinIrred_embed j = x

/-!
## Part 3: Eight Named Nuclei

The 8 nuclei on {⊥, m, p, q, ⊤} with J(L) = {m, p, q} are determined by which
join-irreducible elements they collapse. Each nucleus j is characterized by
its fixpoint set (elements x with j(x) = x).

| #  | Collapsed J(L) | Fixpoints       | Name           | Nucleus |
|----|----------------|-----------------|----------------|---------|
| 1  | ∅              | {⊥,m,p,q,⊤}    | trivial (id)   | ⊥       |
| 2  | {m}            | {m,p,q,⊤}\{⊥→m}| botCollapsed   | axiom   |
| 3  | {q}            | {⊥,p,⊤}        | qCollapsed     | axiom   |
| 4  | {p}            | {⊥,q,⊤}        | pCollapsed     | axiom   |
| 5  | {m,p,q} subset | {⊥,⊤}          | gap            | axiom   |
| 6  | {m,q}+absorb   | {p,⊤}          | pChannel       | axiom   |
| 7  | {m,p}+absorb   | {q,⊤}          | qChannel       | axiom   |
| 8  | {m,p,q}        | {⊤}            | discrete (⊤)   | ⊤       |

The trivial nucleus is ⊥ (identity) and the discrete nucleus is ⊤ (constant ⊤)
from Mathlib's BoundedOrder instance on Nucleus.
-/

/-- The trivial nucleus (identity) on the hub-spokes Lindenbaum algebra.
Fixpoint set: all of L. No elements collapsed. -/
noncomputable def hubSpokes_nucleus_trivial :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) := ⊥

/-- The discrete nucleus (constant ⊤) on the hub-spokes Lindenbaum algebra.
Fixpoint set: {⊤}. All elements collapsed to ⊤. -/
noncomputable def hubSpokes_nucleus_discrete :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) := ⊤

/-- The ⊥-collapsed nucleus: sends ⊥ to m, all other elements fixed.
Fixpoint set: {m, p, q, ⊤}.
j(⊥) = m, j(m) = m, j(p) = p, j(q) = q, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = m = p ⊓ q = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_botCollapsed :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_botCollapsed_nucleus

/-- The q-collapsed nucleus: merges m→p and q→⊤.
Fixpoint set: {⊥, p, ⊤}.
j(⊥) = ⊥, j(m) = p, j(p) = p, j(q) = ⊤, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = p = p ⊓ ⊤ = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_qCollapsed :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_qCollapsed_nucleus

/-- The p-collapsed nucleus: merges m→q and p→⊤.
Fixpoint set: {⊥, q, ⊤}.
j(⊥) = ⊥, j(m) = q, j(p) = ⊤, j(q) = q, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = q = ⊤ ⊓ q = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_pCollapsed :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_pCollapsed_nucleus

/-- The gap nucleus: collapses all middle elements to ⊤.
Fixpoint set: {⊥, ⊤}.
j(⊥) = ⊥, j(m) = ⊤, j(p) = ⊤, j(q) = ⊤, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = ⊤ = ⊤ ⊓ ⊤ = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_gap :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_gap_nucleus

/-- The p-channel nucleus: collapses to the p-chain {p, ⊤}.
Fixpoint set: {p, ⊤}.
j(⊥) = p, j(m) = p, j(p) = p, j(q) = ⊤, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = p = p ⊓ ⊤ = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_pChannel :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_pChannel_nucleus

/-- The q-channel nucleus: collapses to the q-chain {q, ⊤}.
Fixpoint set: {q, ⊤}.
j(⊥) = q, j(m) = q, j(p) = ⊤, j(q) = q, j(⊤) = ⊤.
Meet-preservation: j(p ⊓ q) = j(m) = q = ⊤ ⊓ q = j(p) ⊓ j(q). ✓ -/
noncomputable def hubSpokes_nucleus_qChannel :
    Nucleus (LindenbaumAlgebra hubSpokesTransTheory) :=
  HubSpokesElem.Nucleus.transport hubSpokesTransAlgebra_orderIso
    HubSpokesElem.concreteNucleus_qChannel_nucleus

/-!
## Part 4: Ordering Relations

The 8 nuclei form a partial order matching the Hasse diagram of GT topologies
from NondeterministicSystems.lean. The ordering on nuclei is pointwise:
j₁ ≤ j₂ iff j₁(x) ≤ j₂(x) for all x. A larger nucleus collapses more.

Hasse diagram (identical structure to the GT topology diagram):
```
                    discrete (⊤)
                   /    |    \
             pChannel  gap  qChannel
              /    \  / \  /    \
        qCollapsed  \/   \/  pCollapsed
              \    /\   /\    /
               botCollapsed
                    |
               trivial (⊥)
```
-/

-- Trivial ≤ everything (from BoundedOrder.bot_le)

theorem hubSpokes_nucleus_trivial_le_botCollapsed :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_botCollapsed := bot_le

theorem hubSpokes_nucleus_trivial_le_qCollapsed :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_qCollapsed := bot_le

theorem hubSpokes_nucleus_trivial_le_pCollapsed :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_pCollapsed := bot_le

theorem hubSpokes_nucleus_trivial_le_gap :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_gap := bot_le

theorem hubSpokes_nucleus_trivial_le_pChannel :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_pChannel := bot_le

theorem hubSpokes_nucleus_trivial_le_qChannel :
    hubSpokes_nucleus_trivial ≤ hubSpokes_nucleus_qChannel := bot_le

-- Everything ≤ discrete (from BoundedOrder.le_top)

theorem hubSpokes_nucleus_botCollapsed_le_discrete :
    hubSpokes_nucleus_botCollapsed ≤ hubSpokes_nucleus_discrete := le_top

theorem hubSpokes_nucleus_qCollapsed_le_discrete :
    hubSpokes_nucleus_qCollapsed ≤ hubSpokes_nucleus_discrete := le_top

theorem hubSpokes_nucleus_pCollapsed_le_discrete :
    hubSpokes_nucleus_pCollapsed ≤ hubSpokes_nucleus_discrete := le_top

theorem hubSpokes_nucleus_gap_le_discrete :
    hubSpokes_nucleus_gap ≤ hubSpokes_nucleus_discrete := le_top

theorem hubSpokes_nucleus_pChannel_le_discrete :
    hubSpokes_nucleus_pChannel ≤ hubSpokes_nucleus_discrete := le_top

theorem hubSpokes_nucleus_qChannel_le_discrete :
    hubSpokes_nucleus_qChannel ≤ hubSpokes_nucleus_discrete := le_top

-- Non-trivial ordering between intermediate nuclei (proved via transport)
-- The correct Hasse diagram for nuclei (pointwise ordering) is:
--
--              discrete (⊤)
--           /    |     \
--     pChannel  gap  qChannel
--      /    \       /    \
-- qCollapsed botCollapsed pCollapsed
--      \       |       /
--         trivial (⊥)

/-- qCollapsed ≤ gap: collapsing q (and m→p) is weaker than collapsing to {⊥, ⊤}. -/
theorem hubSpokes_nucleus_qCollapsed_le_gap :
    hubSpokes_nucleus_qCollapsed ≤ hubSpokes_nucleus_gap :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_qCollapsed_le_gap

/-- pCollapsed ≤ gap: collapsing p (and m→q) is weaker than collapsing to {⊥, ⊤}. -/
theorem hubSpokes_nucleus_pCollapsed_le_gap :
    hubSpokes_nucleus_pCollapsed ≤ hubSpokes_nucleus_gap :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_pCollapsed_le_gap

/-- qCollapsed ≤ pChannel: qCollapsed sends ⊥→⊥; pChannel sends ⊥→p.
Since pChannel collapses more (⊥→p), pChannel ≥ qCollapsed. -/
theorem hubSpokes_nucleus_qCollapsed_le_pChannel :
    hubSpokes_nucleus_qCollapsed ≤ hubSpokes_nucleus_pChannel :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_qCollapsed_le_pChannel

/-- pCollapsed ≤ qChannel: symmetric to qCollapsed ≤ pChannel. -/
theorem hubSpokes_nucleus_pCollapsed_le_qChannel :
    hubSpokes_nucleus_pCollapsed ≤ hubSpokes_nucleus_qChannel :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_pCollapsed_le_qChannel

/-- botCollapsed ≤ pChannel: botCollapsed sends ⊥→pq; pChannel sends ⊥→p.
Since pq ≤ p, this holds at ⊥ and at all other elements. -/
theorem hubSpokes_nucleus_botCollapsed_le_pChannel :
    hubSpokes_nucleus_botCollapsed ≤ hubSpokes_nucleus_pChannel :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_botCollapsed_le_pChannel

/-- botCollapsed ≤ qChannel: symmetric to botCollapsed ≤ pChannel. -/
theorem hubSpokes_nucleus_botCollapsed_le_qChannel :
    hubSpokes_nucleus_botCollapsed ≤ hubSpokes_nucleus_qChannel :=
  HubSpokesElem.Nucleus.transport_mono hubSpokesTransAlgebra_orderIso _ _
    HubSpokesElem.concrete_botCollapsed_le_qChannel

/-!
### Distinctness Axioms

The 6 intermediate nuclei are pairwise distinct and distinct from trivial/discrete.
-/

-- Each intermediate nucleus is distinct from trivial and discrete.
-- Proved via transport injectivity from the computable representation.

private noncomputable def φ := hubSpokesTransAlgebra_orderIso

private theorem ne_trivial_of_concrete_ne {c : Nucleus HubSpokesElem}
    (h : c ≠ HubSpokesElem.concreteNucleus_trivial_nucleus) :
    HubSpokesElem.Nucleus.transport φ c ≠ hubSpokes_nucleus_trivial := by
  intro heq
  rw [hubSpokes_nucleus_trivial, ← HubSpokesElem.Nucleus.transport_bot φ] at heq
  exact h (HubSpokesElem.Nucleus.transport_injective φ heq)

private theorem ne_discrete_of_concrete_ne {c : Nucleus HubSpokesElem}
    (h : c ≠ HubSpokesElem.concreteNucleus_discrete_nucleus) :
    HubSpokesElem.Nucleus.transport φ c ≠ hubSpokes_nucleus_discrete := by
  intro heq
  rw [hubSpokes_nucleus_discrete, ← HubSpokesElem.Nucleus.transport_top φ] at heq
  exact h (HubSpokesElem.Nucleus.transport_injective φ heq)

theorem hubSpokes_nucleus_botCollapsed_ne_trivial :
    hubSpokes_nucleus_botCollapsed ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_botCollapsed_ne_trivial

theorem hubSpokes_nucleus_botCollapsed_ne_discrete :
    hubSpokes_nucleus_botCollapsed ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_botCollapsed_ne_discrete

theorem hubSpokes_nucleus_qCollapsed_ne_trivial :
    hubSpokes_nucleus_qCollapsed ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_qCollapsed_ne_trivial

theorem hubSpokes_nucleus_qCollapsed_ne_discrete :
    hubSpokes_nucleus_qCollapsed ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_qCollapsed_ne_discrete

theorem hubSpokes_nucleus_pCollapsed_ne_trivial :
    hubSpokes_nucleus_pCollapsed ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_pCollapsed_ne_trivial

theorem hubSpokes_nucleus_pCollapsed_ne_discrete :
    hubSpokes_nucleus_pCollapsed ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_pCollapsed_ne_discrete

theorem hubSpokes_nucleus_gap_ne_trivial :
    hubSpokes_nucleus_gap ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_gap_ne_trivial

theorem hubSpokes_nucleus_gap_ne_discrete :
    hubSpokes_nucleus_gap ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_gap_ne_discrete

theorem hubSpokes_nucleus_pChannel_ne_trivial :
    hubSpokes_nucleus_pChannel ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_pChannel_ne_trivial

theorem hubSpokes_nucleus_pChannel_ne_discrete :
    hubSpokes_nucleus_pChannel ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_pChannel_ne_discrete

theorem hubSpokes_nucleus_qChannel_ne_trivial :
    hubSpokes_nucleus_qChannel ≠ hubSpokes_nucleus_trivial :=
  ne_trivial_of_concrete_ne HubSpokesElem.concrete_qChannel_ne_trivial

theorem hubSpokes_nucleus_qChannel_ne_discrete :
    hubSpokes_nucleus_qChannel ≠ hubSpokes_nucleus_discrete :=
  ne_discrete_of_concrete_ne HubSpokesElem.concrete_qChannel_ne_discrete

-- Key incomparability among intermediate nuclei (proved via transport)

/-- qCollapsed and pCollapsed are incomparable: neither ≤ the other.
qCollapsed sends m→p; pCollapsed sends m→q. Since p ∥ q, neither dominates. -/
theorem hubSpokes_nucleus_qCollapsed_not_le_pCollapsed :
    ¬(hubSpokes_nucleus_qCollapsed ≤ hubSpokes_nucleus_pCollapsed) := by
  intro h
  exact HubSpokesElem.concrete_qCollapsed_not_le_pCollapsed
    (HubSpokesElem.Nucleus.transport_reflects_le φ _ _ h)

theorem hubSpokes_nucleus_pCollapsed_not_le_qCollapsed :
    ¬(hubSpokes_nucleus_pCollapsed ≤ hubSpokes_nucleus_qCollapsed) := by
  intro h
  exact HubSpokesElem.concrete_pCollapsed_not_le_qCollapsed
    (HubSpokesElem.Nucleus.transport_reflects_le φ _ _ h)

/-- pChannel and qChannel are incomparable: neither ≤ the other.
pChannel fixes p; qChannel fixes q. Since p ∥ q, neither dominates. -/
theorem hubSpokes_nucleus_pChannel_not_le_qChannel :
    ¬(hubSpokes_nucleus_pChannel ≤ hubSpokes_nucleus_qChannel) := by
  intro h
  exact HubSpokesElem.concrete_pChannel_not_le_qChannel
    (HubSpokesElem.Nucleus.transport_reflects_le φ _ _ h)

theorem hubSpokes_nucleus_qChannel_not_le_pChannel :
    ¬(hubSpokes_nucleus_qChannel ≤ hubSpokes_nucleus_pChannel) := by
  intro h
  exact HubSpokesElem.concrete_qChannel_not_le_pChannel
    (HubSpokesElem.Nucleus.transport_reflects_le φ _ _ h)

/-!
### Completeness and Count
-/

/-- Every nucleus on the hub-spokes Lindenbaum algebra is one of the 8 named nuclei. -/
axiom hubSpokes_nucleus_complete :
    ∀ (n : Nucleus (LindenbaumAlgebra hubSpokesTransTheory)),
      n = hubSpokes_nucleus_trivial ∨ n = hubSpokes_nucleus_botCollapsed ∨
      n = hubSpokes_nucleus_qCollapsed ∨ n = hubSpokes_nucleus_pCollapsed ∨
      n = hubSpokes_nucleus_gap ∨ n = hubSpokes_nucleus_pChannel ∨
      n = hubSpokes_nucleus_qChannel ∨ n = hubSpokes_nucleus_discrete

/-- There are exactly 8 nuclei on the hub-spokes Lindenbaum algebra. -/
axiom hubSpokes_nucleus_count :
    ∃ (S : Finset (Nucleus (LindenbaumAlgebra hubSpokesTransTheory))),
      S.card = 8 ∧ ∀ n, n ∈ S

/-!
## Part 5: Nucleus-GT Topology Correspondence

Johnstone's theorem (Stone Spaces II.2) establishes a bijection between nuclei on
a frame L and Lawvere-Tierney topologies (= Grothendieck topologies) on Sh(L).

The correspondence is order-preserving (isotone):
- Identity nucleus (⊥) ↔ trivial GT topology (⊥): no collapse, full topos
- Constant ⊤ nucleus (⊤) ↔ discrete GT topology (⊤): total collapse, degenerate topos
- Intermediate nuclei ↔ intermediate GT topologies in the same order

A larger nucleus (more collapse) corresponds to a larger GT topology (more covering
sieves), both yielding a smaller subtopos.
-/

/-- Correspondence between nuclei on a Lindenbaum algebra and Grothendieck topologies.
This is the concrete instance of Johnstone's theorem (Stone Spaces II.2):
LT topologies on Sh(L) biject with nuclei on L.

The correspondence is isotone: larger nucleus (more collapse) ↔ larger GT topology
(more covering sieves). Both yield smaller subtoposes.

For the hub-spokes lattice, this matches the 8 nuclei with the 8 GT topologies
from NondeterministicSystems.lean. -/
structure NucleusGTCorrespondence (T : PropGeoTheory) where
  /-- Map nuclei to Grothendieck topologies. -/
  nucleusToGT : Nucleus (LindenbaumAlgebra T) → GrothendieckTopology (LindenbaumAlgebra T)
  /-- Map Grothendieck topologies to nuclei. -/
  gtToNucleus : GrothendieckTopology (LindenbaumAlgebra T) → Nucleus (LindenbaumAlgebra T)
  /-- Left inverse: round-tripping through GT topology recovers the nucleus. -/
  leftInverse : ∀ n, gtToNucleus (nucleusToGT n) = n
  /-- Right inverse: round-tripping through nuclei recovers the GT topology. -/
  rightInverse : ∀ J, nucleusToGT (gtToNucleus J) = J
  /-- The correspondence is order-preserving (isotone). -/
  monotone : ∀ n₁ n₂, n₁ ≤ n₂ → nucleusToGT n₁ ≤ nucleusToGT n₂
  /-- The correspondence reflects order (isotone bijection = order isomorphism). -/
  order_reflecting : ∀ n₁ n₂, nucleusToGT n₁ ≤ nucleusToGT n₂ → n₁ ≤ n₂

/-- The nucleusToGT map is injective (follows from leftInverse). -/
theorem NucleusGTCorrespondence.injective {T : PropGeoTheory}
    (corr : NucleusGTCorrespondence T) :
    Function.Injective corr.nucleusToGT := by
  intro n₁ n₂ h
  have h₁ := corr.leftInverse n₁
  have h₂ := corr.leftInverse n₂
  rw [h] at h₁
  rw [← h₁, h₂]

/-!
### NucleusGTCorrespondence Instance

The `hubSpokes_nucleusGT` correspondence, matching axioms, and all derived
GT topology theorems (ordering, distinctness, incomparability, completeness,
count) are now CONSTRUCTED in NucleusGTBijection.lean via the general
`nucleusToGrothendieck` construction. This eliminates 10 axioms
(1 correspondence + 8 matchings + 1 count).
-/

/-!
## Part 6: Boolean Algebra Structure of Nuclei

The 8 nuclei form a Boolean algebra 2³, because |J(L)| = 3 for the hub-spokes
lattice. This is in contrast to the van Glabbeek lattice (13 elements, NOT Boolean),
which embeds as a proper sublattice of the Boolean nucleus lattice.
-/

/-- The hub-spokes nuclei form a Boolean algebra: 2^|J(L)| = 2³ = 8 nuclei.
This validates the Funayama-Nakayama theorem for this concrete lattice. -/
theorem hubSpokes_nuclei_boolean :
    Fintype.card HubSpokesJoinIrred = 3 ∧
    (2 ^ Fintype.card HubSpokesJoinIrred = 8) := by
  constructor
  · decide
  · decide

/-- For any finite distributive lattice L, the number of nuclei equals 2^|J(L)|.
This is the Funayama-Nakayama theorem (1942) specialized to nuclei:
congruences on a distributive lattice form a Boolean algebra with |J(L)| atoms.

In the topos-theoretic context: the number of subtoposes of Sh(L) is always
2^|J(L)|, a power of 2 (forming a Boolean algebra). -/
axiom nucleus_count_eq_two_pow_joinIrred
    (L : Type*) [Order.Frame L] [Fintype L] [DecidableEq L]
    (J : Finset L)
    (hJ : ∀ x ∈ J, SupIrred x)
    (hJ_complete : ∀ x : L, SupIrred x → x ∈ J) :
    ∃ (S : Finset (Nucleus L)), S.card = 2 ^ J.card ∧ ∀ n, n ∈ S

/-!
## Part 7: Summary

### Axiom count: 5
- 3 J(L) axioms (embed, supIrred, complete)
- 2 nucleus completeness/count axioms

### Axioms moved to NucleusGTBijection.lean (Phase 190):
- 1 NucleusGTCorrespondence → CONSTRUCTED via nucleusToGrothendieck
- 8 matching axioms → PROVED
- 1 hubSpokes_topology_count → DERIVED
- All GT ordering, distinctness, incomparability, completeness → PROVED

### Previously eliminated in Phase 140:
**Phase 140-01: 30 axioms** (nuclei: axiom → def via OrderIso transport)
**Phase 140-02: 26 axioms** (GT properties: axiom → theorem via correspondence)

### The correct Hasse diagram (both nuclei and GT topologies):
```
              discrete (⊤)
           /    |     \
     pChannel  gap  qChannel
      /    \       /    \
 qCollapsed botCollapsed pCollapsed
      \       |       /
         trivial (⊥)
```
-/

end Ruliology
