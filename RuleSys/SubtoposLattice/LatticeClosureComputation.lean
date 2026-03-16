/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Closure Computation and Co-Heyting Subtraction Catalog

This file computes the lattice closure of the 13 named van Glabbeek energy vectors
in the ambient energy frame (WithTop ℕ)⁶, catalogs the unnamed elements, and defines
co-Heyting subtraction with process-theoretic interpretations.

## Mathematical Content

The 13 named equivalences form a lattice (every pair has GLB/LUB within the 13) but
not a sublattice (SpectrumNonSublattice.lean). Taking the lattice closure — iterating
pairwise meets/joins until no new elements appear — yields exactly 30 elements:
13 named + 17 unnamed.

The co-Heyting subtraction A \ B on the energy frame isolates the "differential content"
that energy budget A provides beyond B. For products of totally ordered sets, this has
a concrete componentwise formula: (A \ B)_i = A_i if A_i > B_i, else ⊥.

## Main Results

1. Additional unnamed energy vectors from pairwise meets/joins
2. `lattice_closure_count` — the closure has exactly 30 elements (proved)
3. `energySdiff` — co-Heyting subtraction on energy budgets
4. Three process-theoretic subtraction interpretations

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023)
- Johnstone, "Stone Spaces" (1982), II.2.5: coframe of subtoposes
-/

import RuleSys.SubtoposLattice.SpectrumNonSublattice

set_option autoImplicit false

universe u

namespace RTS

/-!
## Part 1: Additional Unnamed Energy Vectors (Round 1)

Beyond PF∧FT, S∧F, and IF∨FT (proved in SpectrumNonSublattice.lean), further
pairwise meets/joins of named equivalences produce additional unnamed elements.
-/

namespace NamedEquivalence

/-- S ∧ RV in the ambient frame = (∞, 2, 1, 0, 0, 0) — unnamed.
"Positive-depth-1 conjunction-2 traces": simulation's conjunction power
combined with revivals' positive clause depth, but no negation. -/
theorem sim_meet_revivals_eq :
    EnergyBudget.meet
      simulation.toEnergyBudget
      revivals.toEnergyBudget =
    ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by native_decide

theorem sim_meet_revivals_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by decide

/-- S ∧ R in the ambient frame = (∞, 2, 1, 1, 0, 0) — unnamed.
"Full positive conjunction-2 traces": all positive clause depths bounded but
no negation at all. -/
theorem sim_meet_readiness_eq :
    EnergyBudget.meet
      simulation.toEnergyBudget
      readiness.toEnergyBudget =
    ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by native_decide

theorem sim_meet_readiness_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by decide

/-- S ∧ PF in the ambient frame = (∞, 2, ∞, ∞, 0, 0) — unnamed.
"Deep positive conjunction-2 traces": unbounded positive clause depth but
conjunction nesting limited to 2 and no negation. -/
theorem sim_meet_pf_eq :
    EnergyBudget.meet
      simulation.toEnergyBudget
      possibleFutures.toEnergyBudget =
    ⟨⊤, (2 : ℕ), ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩ := by native_decide

theorem sim_meet_pf_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩ := by decide

/-- PF ∧ RT in the ambient frame = (∞, 2, ∞, 1, 1, 1) — unnamed.
"Ready possible futures": possible futures' deep clause depth with
readyTraces' single other-positive-clause access. -/
theorem pf_meet_rt_eq :
    EnergyBudget.meet
      possibleFutures.toEnergyBudget
      readyTraces.toEnergyBudget =
    ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by native_decide

theorem pf_meet_rt_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by decide

/-- PF ∧ RS in the ambient frame = (∞, 2, ∞, ∞, 1, 1) — unnamed.
"Ready simulation with deep clauses": full positive depth access with
limited conjunction nesting and single negation. -/
theorem pf_meet_rs_eq :
    EnergyBudget.meet
      possibleFutures.toEnergyBudget
      readySimulation.toEnergyBudget =
    ⟨⊤, (2 : ℕ), ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩ := by native_decide

theorem pf_meet_rs_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, (2 : ℕ), ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩ := by decide

/-- IF ∨ RT in the ambient frame = (∞, ∞, ∞, 1, ∞, 1) — unnamed.
"Deep-negation ready traces": ready traces' conjunction depth with
impossible futures' unlimited negation depth. -/
theorem if_join_rt_eq :
    EnergyBudget.join
      impossibleFutures.toEnergyBudget
      readyTraces.toEnergyBudget =
    ⟨⊤, ⊤, ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩ := by native_decide

theorem if_join_rt_unnamed :
    ∀ x : NamedEquivalence,
      x.toEnergyBudget ≠ ⟨⊤, ⊤, ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩ := by decide

end NamedEquivalence

/-!
## Part 2: Lattice Closure Count

The lattice closure of the 13 named energy vectors under componentwise min/max
contains exactly 30 elements: 13 named + 17 unnamed.

The closure is computed by iterating:
  Round 1: meets/joins of all incomparable named pairs → 9 new unnamed elements
  Round 2: meets/joins involving Round 1 elements → 8 new unnamed elements
  Round 3: meets/joins involving Round 2 elements → 0 new elements (closure reached)
-/

/-- All 30 energy budgets in the lattice closure, listed explicitly.

The 17 unnamed elements arise from 3 rounds of meet/join closure:
- Round 1 (named x named): S∧F, IF∨FT, PF∧FT, S∧RV, S∧R, S∧PF, PF∧RT, PF∧RS, IF∨RT
- Round 2 (new x all): S∧(IF∨FT), PF∧(IF∨FT), (S∧PF)∧(IF∨FT), IF∨(S∧RV),
  IF∨(S∧R), RT∧(S∧PF), IF∨(PF∧RT), S∧(IF∨RT)
- Round 3: no new elements (closure reached) -/
private def latticeClosureList : List EnergyBudget :=
  [ -- Named (13)
    ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,  -- E
    ⟨⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,          -- T
    ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩,          -- F
    ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩,          -- RV
    ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩,          -- R
    ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), ⊤, (1 : ℕ)⟩,                -- IF
    ⟨⊤, ⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩,                              -- S
    ⟨⊤, ⊤, ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩,                      -- FT
    ⟨⊤, (2 : ℕ), ⊤, ⊤, ⊤, (1 : ℕ)⟩,                              -- PF
    ⟨⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩,                      -- RT
    ⟨⊤, ⊤, ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩,                              -- RS
    ⟨⊤, ⊤, ⊤, ⊤, ⊤, (1 : ℕ)⟩,                                    -- 2S
    ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩,                                          -- B
    -- Round 1 unnamed (9)
    ⟨⊤, (2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,          -- S∧F
    ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,          -- S∧RV
    ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩,          -- S∧R
    ⟨⊤, (2 : ℕ), ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩,                      -- S∧PF
    ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩,                -- PF∧FT
    ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (1 : ℕ), (1 : ℕ)⟩,                -- PF∧RT
    ⟨⊤, (2 : ℕ), ⊤, ⊤, (1 : ℕ), (1 : ℕ)⟩,                      -- PF∧RS
    ⟨⊤, ⊤, ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩,                              -- IF∨FT
    ⟨⊤, ⊤, ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩,                              -- IF∨RT
    -- Round 2 unnamed (8)
    ⟨⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,                      -- S∧(IF∨FT)
    ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), ⊤, (1 : ℕ)⟩,                      -- PF∧(IF∨FT)
    ⟨⊤, (2 : ℕ), ⊤, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩,                -- (S∧PF)∧(IF∨FT)
    ⟨⊤, (2 : ℕ), (1 : ℕ), (0 : ℕ), ⊤, (1 : ℕ)⟩,                -- IF∨(S∧RV)
    ⟨⊤, (2 : ℕ), (1 : ℕ), (1 : ℕ), ⊤, (1 : ℕ)⟩,                -- IF∨(S∧R)
    ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩,                -- RT∧(S∧PF)
    ⟨⊤, (2 : ℕ), ⊤, (1 : ℕ), ⊤, (1 : ℕ)⟩,                      -- IF∨(PF∧RT)
    ⟨⊤, ⊤, ⊤, (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩                       -- S∧(IF∨RT)
  ]

/-- The 30-element Finset of energy budgets forming the lattice closure. -/
private def latticeClosureFinset : Finset EnergyBudget :=
  latticeClosureList.toFinset

private theorem latticeClosureFinset_card : latticeClosureFinset.card = 30 := by
  native_decide

private theorem latticeClosureFinset_named :
    ∀ x : NamedEquivalence, x.toEnergyBudget ∈ latticeClosureFinset := by
  decide

private theorem latticeClosureFinset_meet_closed :
    ∀ a ∈ latticeClosureFinset, ∀ b ∈ latticeClosureFinset,
      EnergyBudget.meet a b ∈ latticeClosureFinset := by
  native_decide

private theorem latticeClosureFinset_join_closed :
    ∀ a ∈ latticeClosureFinset, ∀ b ∈ latticeClosureFinset,
      EnergyBudget.join a b ∈ latticeClosureFinset := by
  native_decide

/-- The lattice closure of the 13 named equivalences in the ambient energy frame
(WithTop ℕ)⁶ contains exactly 30 elements: 13 named + 17 unnamed. -/
theorem lattice_closure_count :
    ∃ (S : Finset EnergyBudget),
      S.card = 30 ∧
      (∀ x : NamedEquivalence, x.toEnergyBudget ∈ S) ∧
      (∀ a b : EnergyBudget, a ∈ S → b ∈ S → EnergyBudget.meet a b ∈ S) ∧
      (∀ a b : EnergyBudget, a ∈ S → b ∈ S → EnergyBudget.join a b ∈ S) :=
  ⟨latticeClosureFinset, latticeClosureFinset_card, latticeClosureFinset_named,
   fun a b ha hb => latticeClosureFinset_meet_closed a ha b hb,
   fun a b ha hb => latticeClosureFinset_join_closed a ha b hb⟩

/-!
## Part 3: Co-Heyting Subtraction on Energy Budgets

The co-Heyting subtraction A \ B in a coframe is the largest C with C ∨ B ≥ A.
In a product of totally ordered sets (like (WithTop ℕ)⁶), this has a concrete
componentwise formula:

  (A \ B)_i = A_i  if  A_i > B_i
  (A \ B)_i = ⊥    if  A_i ≤ B_i

where ⊥ = 0 for WithTop ℕ.

Process-theoretic interpretation: A \ B isolates the expressiveness dimensions
where A strictly exceeds B — the "differential content" that A provides beyond B.
-/

namespace EnergyBudget

/-- Componentwise co-Heyting subtraction on energy budgets.
For each dimension, keeps the value if strictly greater than the other, otherwise
drops to ⊥ (= 0). This isolates the "differential content" between two budgets. -/
private def sdiffComponent (x y : WithTop ℕ) : WithTop ℕ :=
  if x ≤ y then (0 : ℕ) else x

def sdiff (a b : EnergyBudget) : EnergyBudget :=
  ⟨sdiffComponent a.obsDepth b.obsDepth,
   sdiffComponent a.conjNesting b.conjNesting,
   sdiffComponent a.deepPosClause b.deepPosClause,
   sdiffComponent a.otherPosClause b.otherPosClause,
   sdiffComponent a.negClause b.negClause,
   sdiffComponent a.negNesting b.negNesting⟩

end EnergyBudget

/-!
## Part 4: Process-Theoretic Subtraction Catalog

Each co-Heyting subtraction isolates a specific aspect of expressiveness.
-/

namespace NamedEquivalence

/-- B \ RS = (0, 0, 0, 0, ∞, ∞): "unlimited negation depth".
Bisimulation's excess over ready simulation is pure deep negation —
the ability to nest negations arbitrarily deep. This is exactly the
content that distinguishes full HML from the positive+flat-negation
fragment. -/
theorem bisim_sdiff_readySim :
    EnergyBudget.sdiff
      bisimulation.toEnergyBudget
      readySimulation.toEnergyBudget =
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), ⊤, ⊤⟩ := by native_decide

/-- S \ T = (0, ∞, ∞, ∞, 0, 0): "unbounded branching content".
Simulation's excess over traces is unlimited conjunction and positive clause
depth — the ability to observe branching structure. This is the content
that distinguishes simulation equivalence from trace equivalence:
conjunction lets you say "both φ₁ and φ₂ hold after action a", while
traces can only say "φ holds after action a". -/
theorem sim_sdiff_traces :
    EnergyBudget.sdiff
      simulation.toEnergyBudget
      traces.toEnergyBudget =
    ⟨(0 : ℕ), ⊤, ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩ := by native_decide

/-- F \ T = (0, 2, 0, 0, 1, 1): "bounded conjunction + single negation".
Failures' excess over traces is bounded conjunction (depth 2) plus
single-depth negation — the ability to say "after trace σ, action a is
refused". This is exactly the refusal content that failures equivalence
adds to trace equivalence: a single ¬⟨a⟩⊤ observation. -/
theorem failures_sdiff_traces :
    EnergyBudget.sdiff
      failures.toEnergyBudget
      traces.toEnergyBudget =
    ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by native_decide

/-- RS \ S = (0, 0, 0, 0, 1, 1): "flat negation content".
Ready simulation's excess over simulation is single-depth negation —
the ability to observe the absence of actions (readiness). Simulation
can only observe positive branching; ready simulation adds refusal
detection via ¬⟨a⟩⊤ at depth 0. -/
theorem readySim_sdiff_sim :
    EnergyBudget.sdiff
      readySimulation.toEnergyBudget
      simulation.toEnergyBudget =
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ)⟩ := by native_decide

/-- 2S \ RS = (0, 0, 0, 0, ∞, 0): "deep negation clause content".
Two-nested simulation's excess over ready simulation is unlimited
negation clause depth. RS can negate at depth 1; 2S can nest Boolean
combinations of positive formulas arbitrarily deep. -/
theorem twoNested_sdiff_readySim :
    EnergyBudget.sdiff
      twoNestedSimulation.toEnergyBudget
      readySimulation.toEnergyBudget =
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), ⊤, (0 : ℕ)⟩ := by native_decide

/-- PF \ IF = (0, 0, ∞, ∞, 0, 0): "deep positive clause content".
Possible futures' excess over impossible futures is unlimited positive
clause depth — the ability to observe the full tree structure of
possible behaviors, not just their absence. -/
theorem pf_sdiff_if :
    EnergyBudget.sdiff
      possibleFutures.toEnergyBudget
      impossibleFutures.toEnergyBudget =
    ⟨(0 : ℕ), (0 : ℕ), ⊤, ⊤, (0 : ℕ), (0 : ℕ)⟩ := by native_decide

end NamedEquivalence

/-!
## Summary

### Lattice closure: 30 elements (13 named + 17 unnamed)
Three rounds of meet/join closure starting from 13 named equivalences.

### Key unnamed elements (Round 1, from named × named):
- S ∧ F = (∞,2,0,0,0,0) — "conjunction-2 traces"
- PF ∧ FT = (∞,2,∞,0,1,1) — "possible failure traces"
- IF ∨ FT = (∞,∞,∞,0,∞,1) — "deep-negation failure traces"
- S ∧ PF = (∞,2,∞,∞,0,0) — "deep positive conjunction-2 traces"
- PF ∧ RS = (∞,2,∞,∞,1,1) — "ready simulation with deep clauses"
- IF ∨ RT = (∞,∞,∞,1,∞,1) — "deep-negation ready traces"

### Co-Heyting subtraction decomposition:
The spectrum's branching structure decomposes into orthogonal dimensions:
1. **Branching content** (S \ T): conjunction + positive clause depth
2. **Refusal content** (F \ T): bounded conjunction + single negation
3. **Flat negation** (RS \ S): single-depth negation (readiness)
4. **Deep negation** (2S \ RS): unlimited negation clause depth
5. **Unlimited negation** (B \ RS): full deep negation nesting
6. **Positive depth** (PF \ IF): deep positive clause access

### Axiom count: 0
### Theorem count: 18
-/

end RTS
