/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coframe Structure: Subtopos Lattice as Dual of Nucleus Frame

The lattice of subtoposes of any Grothendieck topos is a coframe (dual of a frame).
This file establishes the coframe structure on the order-dual of the nucleus lattice
and shows that the energy-to-subtopos composition is monotone.

## Mathematical Content

For a frame L, Mathlib gives `Order.Frame (Nucleus L)`. The subtopos lattice reverses
the nucleus ordering (larger nucleus = more closure = smaller subtopos), so
`(Nucleus L)ᵒᵈ` captures the subtopos ordering. By general duality, the order-dual
of a frame is a coframe, giving us co-Heyting operations (sdiff, hnot) for free.

## Main Results

1. `subtopCoframe` — Coframe instance on `(Nucleus L)ᵒᵈ` (verified)
2. `subtopCoheytingAlgebra` — Co-Heyting algebra with sdiff on `(Nucleus L)ᵒᵈ` (verified)
3. `energy_to_subtopos_monotone` — Energy-to-subtopos is monotone (not antitone)
4. `bisimulation_is_full_topos` — Bisimulation maps to ⊤ (full topos)
5. `subtopSdiff_adjoint` — Co-Heyting adjoint characterization

## References

- Johnstone, "Stone Spaces" (1982), II.2: LT topologies ↔ nuclei
- Johnstone, "Sketches of an Elephant" (2002), A4.5: Coframe of subtoposes
-/

import RuleSys.SubtoposLattice.NucleusInfrastructure
import RuleSys.SubtoposLattice.EnergyNucleusMap

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace RTS

/-!
## Part 1: Coframe Instance on Subtopos Order

The subtopos ordering reverses the nucleus ordering: a larger nucleus (more closure)
corresponds to a smaller subtopos (fewer sheaves). Therefore the subtopos lattice
is `(Nucleus L)ᵒᵈ`, the order-dual of the nucleus frame.

Since Mathlib provides `Order.Frame (Nucleus L)` for any frame L, the dual
`(Nucleus L)ᵒᵈ` automatically gets `Order.Coframe` via Mathlib's order-dual instances.
-/

/-- The subtopos lattice of Sh(L) as a type: order-dual of the nucleus lattice.
A "subtopos" is represented by its corresponding nucleus, but with reversed ordering:
larger subtopos = smaller nucleus. -/
abbrev SubtoposOrder (L : Type*) [Order.Frame L] := (Nucleus L)ᵒᵈ

/-- The subtopos lattice is a coframe (dual of the nucleus frame).
This is the topos-theoretic statement that subtoposes form a co-Heyting algebra
with arbitrary meets distributing over binary joins. -/
noncomputable example (L : Type*) [Order.Frame L] :
    Order.Coframe (SubtoposOrder L) :=
  inferInstance

/-- The subtopos lattice is a co-Heyting algebra, providing the co-Heyting
subtraction `\` (sdiff) and co-complement `￢` (hnot).
The co-Heyting subtraction A \ B represents "what subtopos A distinguishes
beyond subtopos B" — the largest C with C ⊔ B ≥ A. -/
noncomputable example (L : Type*) [Order.Frame L] :
    CoheytingAlgebra (SubtoposOrder L) :=
  inferInstance

/-!
## Part 2: Co-Heyting Operations in Process-Theoretic Language
-/

/-- Co-Heyting subtraction on the subtopos lattice.
Given nuclei j₁, j₂ (representing subtoposes), `subtopSdiff j₁ j₂` is the
largest subtopos C such that C ∨ j₂ ≥ j₁ in the subtopos ordering.

Process-theoretic interpretation: the "differential content" that j₁ provides
beyond j₂ — what distinguishing power j₁ has that j₂ lacks. -/
noncomputable def subtopSdiff {L : Type*} [Order.Frame L]
    (j₁ j₂ : Nucleus L) : SubtoposOrder L :=
  (OrderDual.toDual j₁) \ (OrderDual.toDual j₂)

/-- The co-Heyting adjoint characterization:
  subtopSdiff j₁ j₂ ≤ j₃ ↔ toDual j₁ ≤ toDual j₂ ⊔ j₃
in the subtopos (order-dual) ordering. -/
theorem subtopSdiff_adjoint {L : Type*} [Order.Frame L]
    (j₁ j₂ : Nucleus L) (j₃ : SubtoposOrder L) :
    subtopSdiff j₁ j₂ ≤ j₃ ↔ OrderDual.toDual j₁ ≤ OrderDual.toDual j₂ ⊔ j₃ :=
  sdiff_le_iff

/-!
## Part 3: Energy-to-Subtopos Monotonicity

The energy-to-nucleus map is ANTITONE (order-reversing): larger energy budget →
finer equivalence → less closure → smaller nucleus. But the subtopos ordering
REVERSES the nucleus ordering, so the composition is MONOTONE:
  larger energy budget → larger subtopos

This is the key orientation fact: more expressive formulas → more distinctions →
larger subtopos (with more sheaves = more observable structure).
-/

/-- The composition energy → subtopos is monotone (order-preserving).
Given an energy-to-nucleus map E (antitone), the composition
  ē ↦ OrderDual.toDual (E.nucleusAt ē)
is monotone from NamedEquivalence to (Nucleus L)ᵒᵈ. -/
theorem energy_to_subtopos_monotone {L : Type*} [Order.Frame L] (E : EnergyNucleus L)
    (e₁ e₂ : NamedEquivalence) (h : e₁ ≤ e₂) :
    OrderDual.toDual (E.nucleusAt e₁) ≤ OrderDual.toDual (E.nucleusAt e₂) :=
  E.antitone e₁ e₂ h

/-- Bisimulation corresponds to the largest subtopos (= full topos Sh(L)).
Since bisimulation → identity nucleus (⊥ in nucleus lattice), it maps to ⊤
in the subtopos lattice (top in the dual = bottom in the original). -/
theorem bisimulation_is_full_topos {L : Type*} [Order.Frame L] (E : EnergyNucleus L) :
    OrderDual.toDual (E.nucleusAt .bisimulation) = ⊤ :=
  congrArg OrderDual.toDual E.bisim_is_bot

/-- Enabledness corresponds to the smallest nontrivial subtopos.
Enabledness has the largest nucleus (most closure), hence the smallest subtopos
in the dual ordering. -/
theorem enabledness_is_minimal_subtopos {L : Type*} [Order.Frame L] (E : EnergyNucleus L)
    (e : NamedEquivalence) :
    OrderDual.toDual (E.nucleusAt .enabledness) ≤ OrderDual.toDual (E.nucleusAt e) :=
  enabledness_nucleus_is_top E e

/-!
## Part 4: Hub-Spokes Concrete Instance

For the hub-spokes lattice with 8 nuclei, the 8 subtoposes form the order-dual
of the nucleus Hasse diagram:

```
             trivial (⊤ in SubtoposOrder = ⊥ in Nucleus)
          /       |      \
    pCollapsed  gap  qCollapsed
     /     \       /     \
qChannel botCollapsed pChannel
     \       |       /
        discrete (⊥ in SubtoposOrder = ⊤ in Nucleus)
```

Note the reversal: the trivial nucleus (identity, ⊥ in Nucleus) becomes
⊤ in SubtoposOrder (the full topos), while the discrete nucleus (constant ⊤
in Nucleus) becomes ⊥ in SubtoposOrder (the degenerate topos).
-/

/-- The hub-spokes subtopos lattice has 8 elements forming a coframe. -/
theorem hubSpokes_subtopos_count :
    ∃ (S : Finset (SubtoposOrder (LindenbaumAlgebra hubSpokesTransTheory))),
      S.card = 8 ∧ ∀ n, n ∈ S :=
  hubSpokes_nucleus_count

/-- Every subtopos of the hub-spokes system is one of the 8 named ones. -/
theorem hubSpokes_subtopos_complete :
    ∀ (s : SubtoposOrder (LindenbaumAlgebra hubSpokesTransTheory)),
      s = OrderDual.toDual hubSpokes_nucleus_trivial ∨
      s = OrderDual.toDual hubSpokes_nucleus_botCollapsed ∨
      s = OrderDual.toDual hubSpokes_nucleus_qCollapsed ∨
      s = OrderDual.toDual hubSpokes_nucleus_pCollapsed ∨
      s = OrderDual.toDual hubSpokes_nucleus_gap ∨
      s = OrderDual.toDual hubSpokes_nucleus_pChannel ∨
      s = OrderDual.toDual hubSpokes_nucleus_qChannel ∨
      s = OrderDual.toDual hubSpokes_nucleus_discrete :=
  hubSpokes_nucleus_complete

/-!
## Summary

The coframe structure on the subtopos lattice provides:
1. **Co-Heyting subtraction** (sdiff): "differential content" between equivalences
2. **Co-complement** (hnot): "everything not captured by" an equivalence
3. **Monotone energy-to-subtopos map**: larger budget → larger subtopos
4. **Hub-spokes instance**: 8-element coframe for concrete computation

### Axiom count: 0
### Theorem count: 7
-/

end RTS
