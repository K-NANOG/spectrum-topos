/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Vectors: Full Van Glabbeek Spectrum via Bisping's 6D Characterization

This file extends the energy budget infrastructure from EnergySketch.lean with all 13
named equivalence vectors from Bisping's van Glabbeek spectrum characterization (CAV 2023,
PhD thesis 2025). The partial order on named equivalences is defined via componentwise
energy budget comparison, matching the van Glabbeek Hasse diagram exactly.

## Mathematical Content

Bisping characterizes each of the 13 named process equivalences in the van Glabbeek
linear-time/branching-time spectrum by a canonical 6-dimensional energy vector
ē ∈ (ℕ ∪ {∞})⁶. The componentwise ordering on these vectors exactly reproduces
the van Glabbeek lattice ordering: ē₁ ≤ ē₂ componentwise iff the equivalence
determined by ē₁ is coarser than that determined by ē₂.

## Main Results

1. `NamedEquivalence` — 13-element inductive type for the van Glabbeek spectrum
2. `toEnergyBudget` — canonical 6D energy vector for each named equivalence
3. `PartialOrder NamedEquivalence` — van Glabbeek lattice via energy budget lifting
4. 15 covering relation theorems (Hasse diagram edges)
5. 5 incomparability theorems (non-linear spectrum structure)
6. `SpectrumLevel.toNamedEquivalence` — order embedding from 4-level spectrum
7. Consistency with existing named budgets in EnergySketch.lean

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023, Figure 3)
- Bisping, "Generalized Equivalence Checking of Concurrent Programs" (PhD, TU Berlin, 2025)
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
-/

import RuleSys.SubtoposLattice.EnergySketch

set_option autoImplicit false

universe u

namespace RTS

/-!
## Part 1: Named Equivalence Inductive

The 13 named process equivalences from the van Glabbeek spectrum, ordered from
coarsest (enabledness) to finest (bisimulation).
-/

/-- The 13 named process equivalences in the van Glabbeek linear-time/branching-time
spectrum, as characterized by Bisping's energy game framework.

The ordering (coarsest to finest) follows the van Glabbeek Hasse diagram:
- Enabledness (E): can a single action be performed?
- Traces (T): what sequences of actions are possible?
- Failures (F): what actions can be refused after a trace?
- Revivals (RV): failures + one positive depth-1 observation
- Readiness (R): which actions are enabled/disabled after a trace?
- Impossible Futures (IF): what behaviors are impossible after a trace?
- Simulation (1S): positive HML — conjunction but no negation
- Failure Traces (FT): interleaved observation and refusal
- Possible Futures (PF): what future behaviors are possible?
- Ready Traces (RT): readiness checked along traces
- Ready Simulation (RS): simulation + flat negation
- 2-Nested Simulation (2S): Boolean combinations of positive HML
- Bisimulation (B): full HML, unbounded -/
inductive NamedEquivalence : Type
  | enabledness : NamedEquivalence
  | traces : NamedEquivalence
  | failures : NamedEquivalence
  | revivals : NamedEquivalence
  | readiness : NamedEquivalence
  | impossibleFutures : NamedEquivalence
  | simulation : NamedEquivalence
  | failureTraces : NamedEquivalence
  | possibleFutures : NamedEquivalence
  | readyTraces : NamedEquivalence
  | readySimulation : NamedEquivalence
  | twoNestedSimulation : NamedEquivalence
  | bisimulation : NamedEquivalence
  deriving DecidableEq, Repr

namespace NamedEquivalence

/-!
## Part 2: Energy Budget Mapping

Each named equivalence maps to its canonical 6D energy vector from Bisping's
CAV 2023 paper, Figure 3.
-/

/-- Map each named equivalence to its canonical 6-dimensional energy budget.

The dimensions are: (e₁ obsDepth, e₂ conjNesting, e₃ deepPosClause,
e₄ otherPosClause, e₅ negClause, e₆ negNesting). -/
def toEnergyBudget : NamedEquivalence → EnergyBudget
  | .enabledness       => ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .traces            => ⟨⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
  | .failures          => ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .revivals          => ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .readiness         => ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .impossibleFutures => ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), ⊤, (1 : ℕ)⟩
  | .simulation        => ⟨⊤, ⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩
  | .failureTraces     => ⟨⊤, ⊤, ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .possibleFutures   => ⟨⊤, (2 : ℕ), ⊤, ⊤, ⊤, (1 : ℕ)⟩
  | .readyTraces       => ⟨⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩
  | .readySimulation   => ⟨⊤, ⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩
  | .twoNestedSimulation => ⟨⊤, ⊤, ⊤, ⊤, ⊤, (1 : ℕ)⟩
  | .bisimulation      => ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩

/-!
## Part 3: Decidable Ordering for Energy Budgets

Add a DecidableRel instance for EnergyBudget ordering to enable `decide` proofs.
-/

/-- The componentwise ordering on energy budgets is decidable. -/
instance : DecidableRel (· ≤ · : EnergyBudget → EnergyBudget → Prop) := fun a b =>
  if h₁ : a.obsDepth ≤ b.obsDepth then
    if h₂ : a.conjNesting ≤ b.conjNesting then
      if h₃ : a.deepPosClause ≤ b.deepPosClause then
        if h₄ : a.otherPosClause ≤ b.otherPosClause then
          if h₅ : a.negClause ≤ b.negClause then
            if h₆ : a.negNesting ≤ b.negNesting then
              isTrue ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
            else isFalse fun h => h₆ h.2.2.2.2.2
          else isFalse fun h => h₅ h.2.2.2.2.1
        else isFalse fun h => h₄ h.2.2.2.1
      else isFalse fun h => h₃ h.2.2.1
    else isFalse fun h => h₂ h.2.1
  else isFalse fun h => h₁ h.1

/-!
## Part 4: Fintype and Cardinality
-/

/-- Manual Fintype instance for NamedEquivalence (13 elements). -/
instance : Fintype NamedEquivalence where
  elems := {.enabledness, .traces, .failures, .revivals, .readiness,
            .impossibleFutures, .simulation, .failureTraces, .possibleFutures,
            .readyTraces, .readySimulation, .twoNestedSimulation, .bisimulation}
  complete := fun x => by cases x <;> simp

/-- The van Glabbeek spectrum has exactly 13 named equivalences. -/
theorem card : Fintype.card NamedEquivalence = 13 := by decide

/-!
## Part 5: Injectivity and Partial Order
-/

/-- Distinct named equivalences have distinct energy vectors. -/
theorem toEnergyBudget_injective : Function.Injective toEnergyBudget := by
  intro a b h
  cases a <;> cases b <;> simp [toEnergyBudget] at h <;> rfl

/-- Ordering on named equivalences: a ≤ b iff a's energy budget is componentwise ≤ b's.
A larger energy budget allows more HML formulas, hence finer distinctions. -/
instance : LE NamedEquivalence where
  le a b := a.toEnergyBudget ≤ b.toEnergyBudget

/-- Strict ordering on named equivalences. -/
instance : LT NamedEquivalence where
  lt a b := a.toEnergyBudget < b.toEnergyBudget

/-- The van Glabbeek lattice as a partial order, lifted from the componentwise
energy budget ordering via the injective `toEnergyBudget` map. -/
instance : PartialOrder NamedEquivalence where
  le_refl a := _root_.le_refl a.toEnergyBudget
  le_trans a b c (hab : a.toEnergyBudget ≤ b.toEnergyBudget)
    (hbc : b.toEnergyBudget ≤ c.toEnergyBudget) := _root_.le_trans hab hbc
  le_antisymm a b (hab : a.toEnergyBudget ≤ b.toEnergyBudget)
    (hba : b.toEnergyBudget ≤ a.toEnergyBudget) :=
    toEnergyBudget_injective (_root_.le_antisymm hab hba)

/-- Decidable ordering on named equivalences. -/
instance : DecidableRel (· ≤ · : NamedEquivalence → NamedEquivalence → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.toEnergyBudget ≤ b.toEnergyBudget))

/-- Unfold LE on named equivalences to energy budget comparison. -/
theorem le_def (a b : NamedEquivalence) :
    a ≤ b ↔ a.toEnergyBudget ≤ b.toEnergyBudget := Iff.rfl

/-!
## Part 6: Bottom and Top Elements
-/

/-- Enabledness is the coarsest named equivalence (bottom element). -/
theorem enabledness_le (e : NamedEquivalence) : enabledness ≤ e := by
  cases e <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

/-- Bisimulation is the finest named equivalence (top element). -/
theorem le_bisimulation (e : NamedEquivalence) : e ≤ bisimulation := by
  cases e <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

/-!
## Part 7: Covering Relations (Hasse Diagram)

The 15 covering relations of the van Glabbeek lattice. Each `a_le_b` theorem
states that `a ≤ b` in the spectrum ordering.
-/

-- 1. E ⋖ T
theorem enabledness_le_traces : (enabledness : NamedEquivalence) ≤ traces := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 2. T ⋖ F
theorem traces_le_failures : (traces : NamedEquivalence) ≤ failures := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 3. T ⋖ S
theorem traces_le_simulation : (traces : NamedEquivalence) ≤ simulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 4. F ⋖ RV
theorem failures_le_revivals : (failures : NamedEquivalence) ≤ revivals := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 5. F ⋖ IF
theorem failures_le_impossibleFutures : (failures : NamedEquivalence) ≤ impossibleFutures := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 6. RV ⋖ R
theorem revivals_le_readiness : (revivals : NamedEquivalence) ≤ readiness := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 7. RV ⋖ FT
theorem revivals_le_failureTraces : (revivals : NamedEquivalence) ≤ failureTraces := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 8. R ⋖ RT
theorem readiness_le_readyTraces : (readiness : NamedEquivalence) ≤ readyTraces := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 9. IF ⋖ PF
theorem impossibleFutures_le_possibleFutures :
    (impossibleFutures : NamedEquivalence) ≤ possibleFutures := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 10. FT ⋖ RT
theorem failureTraces_le_readyTraces : (failureTraces : NamedEquivalence) ≤ readyTraces := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 11. RT ⋖ RS
theorem readyTraces_le_readySimulation :
    (readyTraces : NamedEquivalence) ≤ readySimulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 12. S ⋖ RS
theorem simulation_le_readySimulation :
    (simulation : NamedEquivalence) ≤ readySimulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 13. PF ⋖ 2S
theorem possibleFutures_le_twoNestedSimulation :
    (possibleFutures : NamedEquivalence) ≤ twoNestedSimulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 14. RS ⋖ 2S
theorem readySimulation_le_twoNestedSimulation :
    (readySimulation : NamedEquivalence) ≤ twoNestedSimulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

-- 15. 2S ⋖ B
theorem twoNestedSimulation_le_bisimulation :
    (twoNestedSimulation : NamedEquivalence) ≤ bisimulation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toEnergyBudget]

/-!
## Part 8: Incomparability Results

Key incomparabilities demonstrating the non-linear structure of the van Glabbeek
spectrum. The classic split is between the "linear-time" branch (traces → failures
→ ... → possible futures) and the "branching-time" branch (simulation → ready
simulation → 2-nested simulation).
-/

/-- Simulation and failures are incomparable: the classic linear/branching split.
Simulation allows conjunction (e₂ = ∞) but no negation (e₅ = e₆ = 0).
Failures allow negation (e₅ = e₆ = 1) but limited conjunction (e₂ = 2). -/
theorem simulation_incomp_failures :
    ¬((simulation : NamedEquivalence) ≤ failures) ∧ ¬(failures ≤ simulation) := by
  constructor
  · intro ⟨_, h, _⟩; simp [toEnergyBudget] at h
  · intro ⟨_, _, _, _, h, _⟩; simp [toEnergyBudget] at h

/-- Simulation and impossible futures are incomparable. -/
theorem simulation_incomp_impossibleFutures :
    ¬((simulation : NamedEquivalence) ≤ impossibleFutures) ∧
    ¬(impossibleFutures ≤ simulation) := by
  constructor
  · intro ⟨_, h, _⟩; simp [toEnergyBudget] at h
  · intro ⟨_, _, _, _, h, _⟩; simp [toEnergyBudget] at h

/-- Possible futures and ready traces are incomparable. -/
theorem possibleFutures_incomp_readyTraces :
    ¬((possibleFutures : NamedEquivalence) ≤ readyTraces) ∧
    ¬(readyTraces ≤ possibleFutures) := by
  constructor
  · intro ⟨_, _, _, _, h, _⟩; simp [toEnergyBudget] at h
  · intro ⟨_, h, _⟩; simp [toEnergyBudget] at h

/-- Possible futures and ready simulation are incomparable. -/
theorem possibleFutures_incomp_readySimulation :
    ¬((possibleFutures : NamedEquivalence) ≤ readySimulation) ∧
    ¬(readySimulation ≤ possibleFutures) := by
  constructor
  · intro ⟨_, _, _, _, h, _⟩; simp [toEnergyBudget] at h
  · intro ⟨_, h, _⟩; simp [toEnergyBudget] at h

/-- Impossible futures and failure traces are incomparable. -/
theorem impossibleFutures_incomp_failureTraces :
    ¬((impossibleFutures : NamedEquivalence) ≤ failureTraces) ∧
    ¬(failureTraces ≤ impossibleFutures) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- IF.negClause = ∞ > 1 = FT.negClause
    have := h.2.2.2.2.1
    simp [toEnergyBudget] at this
  · -- FT.conjNesting = ∞ > 2 = IF.conjNesting
    have := h.2.1
    simp [toEnergyBudget] at this

/-!
## Part 9: Connection to Existing Infrastructure
-/

end NamedEquivalence

/-- Embed the 4-level spectrum into the 13-element named equivalence lattice. -/
def SpectrumLevel.toNamedEquivalence : SpectrumLevel → NamedEquivalence
  | .trace => .traces
  | .simulation => .simulation
  | .readySimulation => .readySimulation
  | .bisimulation => .bisimulation

/-- The spectrum embedding is injective. -/
theorem SpectrumLevel.toNamedEquivalence_injective :
    Function.Injective SpectrumLevel.toNamedEquivalence := by
  intro a b h
  cases a <;> cases b <;> simp [toNamedEquivalence] at h <;> rfl

/-- The spectrum embedding is monotone: spectrum ordering matches named equivalence ordering. -/
theorem SpectrumLevel.toNamedEquivalence_monotone (ℓ₁ ℓ₂ : SpectrumLevel) (h : ℓ₁ ≤ ℓ₂) :
    ℓ₁.toNamedEquivalence ≤ ℓ₂.toNamedEquivalence := by
  match ℓ₁, ℓ₂ with
  | .trace, .trace =>
    show NamedEquivalence.traces.toEnergyBudget ≤ _; exact _root_.le_refl _
  | .trace, .simulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .trace, .readySimulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .trace, .bisimulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .simulation, .simulation =>
    show NamedEquivalence.simulation.toEnergyBudget ≤ _; exact _root_.le_refl _
  | .simulation, .readySimulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .simulation, .bisimulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .readySimulation, .readySimulation =>
    show NamedEquivalence.readySimulation.toEnergyBudget ≤ _; exact _root_.le_refl _
  | .readySimulation, .bisimulation =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NamedEquivalence.toEnergyBudget, toNamedEquivalence]
  | .bisimulation, .bisimulation =>
    show NamedEquivalence.bisimulation.toEnergyBudget ≤ _; exact _root_.le_refl _
  | .simulation, .trace => exact absurd h (by show ¬(1 ≤ 0); omega)
  | .readySimulation, .trace => exact absurd h (by show ¬(2 ≤ 0); omega)
  | .readySimulation, .simulation => exact absurd h (by show ¬(2 ≤ 1); omega)
  | .bisimulation, .trace => exact absurd h (by show ¬(3 ≤ 0); omega)
  | .bisimulation, .simulation => exact absurd h (by show ¬(3 ≤ 1); omega)
  | .bisimulation, .readySimulation => exact absurd h (by show ¬(3 ≤ 2); omega)

/-- Consistency: the spectrum-to-energy path through NamedEquivalence agrees with
the direct path through SpectrumLevel.toEnergyBudget. -/
theorem SpectrumLevel.toEnergyBudget_via_named (ℓ : SpectrumLevel) :
    ℓ.toNamedEquivalence.toEnergyBudget = ℓ.toEnergyBudget := by
  cases ℓ <;> rfl

/-!
## Part 10: Consistency with EnergySketch Named Budgets
-/

namespace NamedEquivalence

/-- The traces energy vector matches `EnergyBudget.traces` from EnergySketch. -/
theorem traces_budget_eq : toEnergyBudget .traces = EnergyBudget.traces := rfl

/-- The simulation energy vector matches `EnergyBudget.simulation` from EnergySketch. -/
theorem simulation_budget_eq : toEnergyBudget .simulation = EnergyBudget.simulation := rfl

/-- The ready simulation energy vector matches `EnergyBudget.readySimulation`. -/
theorem readySimulation_budget_eq :
    toEnergyBudget .readySimulation = EnergyBudget.readySimulation := rfl

/-- The bisimulation energy vector matches `EnergyBudget.bisimulation`. -/
theorem bisimulation_budget_eq :
    toEnergyBudget .bisimulation = EnergyBudget.bisimulation := rfl

/-- The `toEnergyBudget` map is monotone (order-preserving). -/
theorem toEnergyBudget_monotone (a b : NamedEquivalence) (h : a ≤ b) :
    a.toEnergyBudget ≤ b.toEnergyBudget := h

end NamedEquivalence

/-!
## Summary

The van Glabbeek linear-time/branching-time spectrum is formalized as a 13-element
partial order `NamedEquivalence`, with ordering derived from Bisping's 6-dimensional
energy budget characterization. The key structural features:

### Hasse diagram: 15 covering relations
E → T → {F, S}, F → {RV, IF}, RV → {R, FT}, R → RT, IF → PF,
FT → RT → RS, S → RS, {PF, RS} → 2S → B

### Non-linear structure: 5 proved incomparabilities
S ∦ F, S ∦ IF, PF ∦ RT, PF ∦ RS, IF ∦ FT

### Integration
- 4-level `SpectrumLevel` embeds monotonically via `toNamedEquivalence`
- Energy vectors match existing named budgets in EnergySketch.lean
- All ordering proofs go through componentwise energy comparison

### Axiom count: 0
### Theorem count: 30+
-/

end RTS
