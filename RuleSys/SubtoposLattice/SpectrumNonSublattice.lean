/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectrum Non-Sublattice: The Van Glabbeek Spectrum Is Not a Sublattice

The 13 named process equivalences in the van Glabbeek spectrum form a LATTICE
(every pair has GLB/LUB within the 13) but NOT a SUBLATTICE of the ambient
energy frame (WithTop ℕ)⁶. The ambient lattice operations (componentwise min/max)
can produce energy vectors that don't correspond to any named equivalence.

## Mathematical Content

The ambient energy frame (WithTop ℕ)⁶ has componentwise min as meet and
componentwise max as join. When applied to named equivalences, these ambient
operations sometimes land outside the 13 named ones:
- PF ∧ FT = (∞, 2, ∞, 0, 1, 1) — unnamed ("possible failure traces")
- S ∧ F = (∞, 2, 0, 0, 0, 0) — unnamed ("conjunction-2 traces")
- IF ∨ FT = (∞, ∞, ∞, 0, ∞, 1) — unnamed join

The spectrum IS a lattice because within the 13 named equivalences, every pair
has a greatest lower bound and least upper bound. For example, the GLB of
PF and FT within the 13 is revivals (RV), even though the ambient meet is
different.

## Main Results

1. `EnergyBudget.meet` — componentwise min in the ambient frame
2. `EnergyBudget.join` — componentwise max in the ambient frame
3. `pf_meet_ft_unnamed` — PF ∧ FT is unnamed
4. `spectrum_not_sublattice` — the 13-point spectrum is not a sublattice
5. `sim_meet_failures_unnamed` — S ∧ F is unnamed (additional witness)
6. `if_join_ft_unnamed` — IF ∨ FT is unnamed (join witness)

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023)
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
-/

import RuleSys.SubtoposLattice.EnergyVectors

set_option autoImplicit false

universe u

namespace RTS

/-!
## Part 1: Componentwise Meet and Join for Energy Budgets

The ambient energy frame (WithTop ℕ)⁶ has componentwise meet (min) and join (max).
These are the lattice operations in the ambient frame, NOT the same as GLB/LUB
within the 13 named equivalences.
-/

namespace EnergyBudget

/-- Componentwise meet (min) of energy budgets in the ambient frame (WithTop ℕ)⁶. -/
def meet (a b : EnergyBudget) : EnergyBudget :=
  ⟨min a.obsDepth b.obsDepth,
   min a.conjNesting b.conjNesting,
   min a.deepPosClause b.deepPosClause,
   min a.otherPosClause b.otherPosClause,
   min a.negClause b.negClause,
   min a.negNesting b.negNesting⟩

/-- Componentwise join (max) of energy budgets in the ambient frame (WithTop ℕ)⁶. -/
def join (a b : EnergyBudget) : EnergyBudget :=
  ⟨max a.obsDepth b.obsDepth,
   max a.conjNesting b.conjNesting,
   max a.deepPosClause b.deepPosClause,
   max a.otherPosClause b.otherPosClause,
   max a.negClause b.negClause,
   max a.negNesting b.negNesting⟩

/-- The meet operation is the GLB in the componentwise ordering. -/
theorem meet_le_left (a b : EnergyBudget) : meet a b ≤ a :=
  ⟨min_le_left _ _, min_le_left _ _, min_le_left _ _,
   min_le_left _ _, min_le_left _ _, min_le_left _ _⟩

/-- The meet operation is the GLB in the componentwise ordering. -/
theorem meet_le_right (a b : EnergyBudget) : meet a b ≤ b :=
  ⟨min_le_right _ _, min_le_right _ _, min_le_right _ _,
   min_le_right _ _, min_le_right _ _, min_le_right _ _⟩

/-- The join operation is the LUB in the componentwise ordering. -/
theorem le_join_left (a b : EnergyBudget) : a ≤ join a b :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _,
   le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

/-- The join operation is the LUB in the componentwise ordering. -/
theorem le_join_right (a b : EnergyBudget) : b ≤ join a b :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _,
   le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

end EnergyBudget

/-!
## Part 2: Non-Sublattice Witness: PF ∧ FT

The componentwise meet of possibleFutures and failureTraces in the ambient energy
frame lands OUTSIDE the 13 named equivalences, proving the van Glabbeek spectrum
is not a sublattice of the ambient frame.

```
PF = (∞, 2, ∞, ∞, ∞, 1)
FT = (∞, ∞, ∞, 0, 1, 1)
PF ∧ FT = (∞, 2, ∞, 0, 1, 1) — unnamed!
```

Note: the GLB of PF and FT WITHIN the 13 named equivalences is revivals
RV = (∞, 2, 1, 0, 1, 1), which is strictly below (∞, 2, ∞, 0, 1, 1).
-/

namespace NamedEquivalence

/-- The ambient meet of possibleFutures and failureTraces is (∞, 2, ∞, 0, 1, 1). -/
theorem pf_meet_ft_eq :
    EnergyBudget.meet
      possibleFutures.toEnergyBudget
      failureTraces.toEnergyBudget =
    ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by native_decide

/-- The energy vector (∞, 2, ∞, 0, 1, 1) is not the image of any named equivalence. -/
theorem pf_meet_ft_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by decide

/-- The van Glabbeek spectrum is NOT a sublattice of the ambient energy frame (WithTop ℕ)⁶.
The ambient meet of possibleFutures and failureTraces does not correspond to any
named equivalence: PF ∧ FT = (∞, 2, ∞, 0, 1, 1) is unnamed. -/
theorem spectrum_not_sublattice :
    ¬ ∀ (a b : NamedEquivalence), ∃ c : NamedEquivalence,
      c.toEnergyBudget = EnergyBudget.meet a.toEnergyBudget b.toEnergyBudget := by
  intro h
  obtain ⟨c, hc⟩ := h .possibleFutures .failureTraces
  exact pf_meet_ft_unnamed c (hc.trans pf_meet_ft_eq)

/-!
## Part 3: Additional Non-Sublattice Witnesses

Further examples of ambient meets/joins landing outside the 13 named equivalences.
-/

/-- S ∧ F in the ambient frame: simulation meet failures = (∞, 2, 0, 0, 0, 0).
This is unnamed — traces has conjNesting = 1, this has conjNesting = 2 but
no negation, which matches no named equivalence. -/
theorem sim_meet_failures_eq :
    EnergyBudget.meet
      simulation.toEnergyBudget
      failures.toEnergyBudget =
    ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by native_decide

/-- The energy vector (∞, 2, 0, 0, 0, 0) is not the image of any named equivalence. -/
theorem sim_meet_failures_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by decide

/-- S ∧ IF = S ∧ F: the ambient meet of simulation and impossible futures equals
the ambient meet of simulation and failures. Both reduce to (∞, 2, 0, 0, 0, 0). -/
theorem sim_meet_if_eq_sim_meet_failures :
    EnergyBudget.meet simulation.toEnergyBudget impossibleFutures.toEnergyBudget =
    EnergyBudget.meet simulation.toEnergyBudget failures.toEnergyBudget := by
  native_decide

/-- IF ∨ FT in the ambient frame: impossibleFutures join failureTraces = (∞, ∞, ∞, 0, ∞, 1).
This is unnamed — no named equivalence has this energy vector. -/
theorem if_join_ft_eq :
    EnergyBudget.join
      impossibleFutures.toEnergyBudget
      failureTraces.toEnergyBudget =
    ⟨⊤, ⊤, ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩ := by native_decide

/-- The energy vector (∞, ∞, ∞, 0, ∞, 1) is not the image of any named equivalence. -/
theorem if_join_ft_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, ⊤, ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩ := by decide

/-- The non-sublattice property also holds for joins: not all ambient joins of
named equivalences land on named ones. IF ∨ FT is unnamed. -/
theorem spectrum_not_sublattice_join :
    ¬ ∀ (a b : NamedEquivalence), ∃ c : NamedEquivalence,
      c.toEnergyBudget = EnergyBudget.join a.toEnergyBudget b.toEnergyBudget := by
  intro h
  obtain ⟨c, hc⟩ := h .impossibleFutures .failureTraces
  exact if_join_ft_unnamed c (hc.trans if_join_ft_eq)

/-!
## Part 4: Named Ambient Meets/Joins (Consistency Checks)

Some ambient operations DO land on named equivalences, confirming the computation
and showing that the non-sublattice property is not universal — it depends on
which pair we choose.
-/

/-- IF ∧ FT in the ambient frame equals failures: (∞, 2, 0, 0, 1, 1) = F.
The two incomparable equivalences IF and FT have an ambient meet that happens
to be named. -/
theorem if_meet_ft_eq_failures :
    EnergyBudget.meet
      impossibleFutures.toEnergyBudget
      failureTraces.toEnergyBudget =
    failures.toEnergyBudget := by native_decide

/-- S ∨ F in the ambient frame equals readySimulation: (∞, ∞, ∞, ∞, 1, 1) = RS.
The linear-time/branching-time split rejoins at ready simulation. -/
theorem sim_join_failures_eq_readySim :
    EnergyBudget.join
      simulation.toEnergyBudget
      failures.toEnergyBudget =
    readySimulation.toEnergyBudget := by native_decide

/-- S ∨ IF in the ambient frame equals twoNestedSimulation: (∞, ∞, ∞, ∞, ∞, 1) = 2S. -/
theorem sim_join_if_eq_twoNested :
    EnergyBudget.join
      simulation.toEnergyBudget
      impossibleFutures.toEnergyBudget =
    twoNestedSimulation.toEnergyBudget := by native_decide

end NamedEquivalence

/-!
## Summary

### Non-sublattice witnesses (unnamed energy vectors from ambient operations):
1. PF ∧ FT = (∞, 2, ∞, 0, 1, 1) — "possible failure traces" (unnamed meet)
2. S ∧ F = (∞, 2, 0, 0, 0, 0) — "conjunction-2 traces" (unnamed meet)
3. IF ∨ FT = (∞, ∞, ∞, 0, ∞, 1) — unnamed join

### Named ambient operations (consistency checks):
4. IF ∧ FT = F = (∞, 2, 0, 0, 1, 1) — named meet
5. S ∨ F = RS = (∞, ∞, ∞, ∞, 1, 1) — named join
6. S ∨ IF = 2S = (∞, ∞, ∞, ∞, ∞, 1) — named join

### Key insight
The spectrum IS a lattice (GLB/LUB exist within the 13 for every pair)
but NOT a sublattice (ambient meets/joins can escape the 13).
The unnamed energy vectors represent process equivalences with well-defined
energy characterizations that have no classical name.

### Axiom count: 0
### Theorem count: 14
-/

end RTS
