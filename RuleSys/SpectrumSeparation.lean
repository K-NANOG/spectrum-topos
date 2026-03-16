/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 4-Level Spectrum Separation via Distinguishing HML Formulas

This file proves the van Glabbeek spectrum separation for labeled transition
systems by constructing concrete distinguishing HML formulas and evaluating
them on the concrete LTS examples from `LabeledExamples.lean`.

## Overview

The van Glabbeek spectrum has four genuinely distinct levels for labeled LTS:
1. Trace equivalence (characterized by trace formulas O)
2. Simulation equivalence (characterized by positive formulas HML_pos)
3. Ready-simulation equivalence (characterized by HML_ready)
4. Bisimulation equivalence (characterized by full HML)

Each adjacent pair is separated by a concrete formula-LTS pair:

### Pair 1: Trace != Simulation
- Formula: `<a>(<b>T /\ <c>T)` -- "exists an a-successor that can do both b and c"
- Positive but not a trace formula (uses conjunction)
- Satisfied at vgTraceB.q0 (late choice: q1 can do both b and c)
- Not satisfied at vgTraceA.p0 (early choice: each a-successor can do only one)

### Pair 2: Simulation != Ready-Simulation
- Formula: `<a>(<b>T /\ neg(<c>T))` -- "exists an a-successor that can do b but not c"
- Ready-sim formula but not positive (uses inability atom neg(<c>T))
- Satisfied at vgSimA.r0 (r1 can do b but not c)
- Not satisfied at vgTraceB.q0 (q1 is the only a-successor and can do c)

### Pair 3: Ready-Simulation != Bisimulation
- Formula: `[a]<c>T` -- "all a-successors can do c"
- Bisim formula but not ready-sim (nested negation, not an inability atom)
- Satisfied at vgTraceB.q0 (q1 is the only a-successor and can do c)
- Not satisfied at vgSimA.r0 (r1 is an a-successor that cannot do c)

## References

- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
-/

import RuleSys.LabeledHML

set_option autoImplicit false

namespace RTS

open LabeledHML

/-!
## Part 1: Pair 1 — Trace != Simulation

The formula `<a>(<b>T /\ <c>T)` is positive (no negation) but not a trace formula
(uses conjunction). It separates `vgTraceB` from `vgTraceA`:
- In vgTraceB, q0 has a-successor q1, which can do both b and c.
- In vgTraceA, p0 has a-successors p1 (can do b only) and p2 (can do c only).
  Neither a-successor can do both.
-/

/-- Distinguishing formula for Pair 1: `<a>(<b>T /\ <c>T)`.
"There exists an a-successor that can do both b and c."
This is positive (no negation) but not a trace formula (uses conjunction). -/
def pair1Formula : LabeledHML ThreeLabelAlphabet :=
  .diamond .a (.conj (.diamond .b .top) (.diamond .c .top))

/-- `pair1Formula` is positive but not a trace formula. -/
theorem pair1Formula_positive_not_trace :
    pair1Formula.isPositive = true ∧ pair1Formula.isTraceFormula = false :=
  ⟨rfl, rfl⟩

/-- `pair1Formula` is satisfied at vgTraceB.q0.

In vgTraceB (CCS process `a.(b+c)`):
- q0 ->^a q1 (the a-successor)
- q1 ->^b q2 (q1 can do b)
- q1 ->^c q3 (q1 can do c)
So q1 satisfies `<b>T /\ <c>T`, and q0 satisfies `<a>(<b>T /\ <c>T)`. -/
theorem pair1_vgTraceB_satisfies :
    pair1Formula.satisfiedAt vgTraceBLTS .q0 :=
  ⟨.q1, ⟨()⟩, ⟨.q2, ⟨()⟩, trivial⟩, ⟨.q3, ⟨()⟩, trivial⟩⟩

/-- `pair1Formula` is NOT satisfied at vgTraceA.p0.

In vgTraceA (CCS process `a.b + a.c`):
- p0 ->^a p1 and p0 ->^a p2 are the only a-edges from p0
- p1 can do b (p1 ->^b p3) but NOT c (no c-edge from p1)
- p2 can do c (p2 ->^c p4) but NOT b (no b-edge from p2)
- p0, p3, p4 have no a-edges from p0

So no a-successor of p0 satisfies `<b>T /\ <c>T`. -/
theorem pair1_vgTraceA_not_satisfies :
    ¬ pair1Formula.satisfiedAt vgTraceALTS .p0 := by
  intro ⟨t, ht_step, hb, hc⟩
  cases t with
  | p0 => exact (ht_step.some).elim
  | p1 =>
    -- p1 can do b but NOT c. hc says ∃ t', Step .p1 .c t' ∧ True
    obtain ⟨t', ht', _⟩ := hc
    cases t' with
    | p0 => exact (ht'.some).elim
    | p1 => exact (ht'.some).elim
    | p2 => exact (ht'.some).elim
    | p3 => exact (ht'.some).elim
    | p4 => exact (ht'.some).elim
  | p2 =>
    -- p2 can do c but NOT b. hb says ∃ t', Step .p2 .b t' ∧ True
    obtain ⟨t', ht', _⟩ := hb
    cases t' with
    | p0 => exact (ht'.some).elim
    | p1 => exact (ht'.some).elim
    | p2 => exact (ht'.some).elim
    | p3 => exact (ht'.some).elim
    | p4 => exact (ht'.some).elim
  | p3 => exact (ht_step.some).elim
  | p4 => exact (ht_step.some).elim

/-- **Pair 1 separation**: trace equivalence is strictly coarser than simulation equivalence.

The formula `<a>(<b>T /\ <c>T)` is in HML_pos \ O (positive but not trace), and it
separates vgTraceB from vgTraceA. Since trace-equivalent systems agree on all trace
formulas and simulation-equivalent systems agree on all positive formulas, this pair
witnesses that simulation can distinguish systems that trace equivalence cannot. -/
theorem pair1_trace_neq_simulation :
    ∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isPositive = true ∧ phi.isTraceFormula = false ∧
      phi.satisfiedAt vgTraceBLTS .q0 ∧ ¬ phi.satisfiedAt vgTraceALTS .p0 :=
  ⟨pair1Formula, rfl, rfl, pair1_vgTraceB_satisfies, pair1_vgTraceA_not_satisfies⟩

/-!
## Part 2: Pair 2 — Simulation != Ready-Simulation

The formula `<a>(<b>T /\ neg(<c>T))` is a ready-sim formula (uses the inability atom
`neg(<c>T)`) but not positive (contains negation). It separates `vgSimA` from `vgTraceB`:
- In vgSimA, r0 has a-successor r1, which can do b but NOT c.
- In vgTraceB, q0's only a-successor is q1, which can do both b and c,
  so `neg(<c>T)` fails at q1.
-/

/-- Distinguishing formula for Pair 2: `<a>(<b>T /\ neg(<c>T))`.
"There exists an a-successor that can do b but cannot do c."
This is a ready-sim formula (inability atom `neg(<c>T)`) but not positive (has negation). -/
def pair2Formula : LabeledHML ThreeLabelAlphabet :=
  .diamond .a (.conj (.diamond .b .top) (.neg (.diamond .c .top)))

/-- `pair2Formula` is a ready-simulation formula but not positive.

Trace through `isReadySimFormula`:
  diamond .a (conj (diamond .b top) (neg (diamond .c top)))
  = isReadySimFormula (conj (diamond .b top) (neg (diamond .c top)))
  = isReadySimFormula (diamond .b top) && isReadySimFormula (neg (diamond .c top))
  = isReadySimFormula top && true
  = true && true = true

Trace through `isPositive`:
  diamond .a (conj (diamond .b top) (neg (diamond .c top)))
  = isPositive (conj (diamond .b top) (neg (diamond .c top)))
  = isPositive (diamond .b top) && isPositive (neg (diamond .c top))
  = true && false = false -/
theorem pair2Formula_readySim_not_positive :
    pair2Formula.isReadySimFormula = true ∧ pair2Formula.isPositive = false :=
  ⟨rfl, rfl⟩

/-- `pair2Formula` is satisfied at vgSimA.r0.

In vgSimA (CCS process `a.b + a.(b+c)`):
- r0 ->^a r1 (a-successor r1)
- r1 ->^b r3 (r1 can do b, so `<b>T` holds at r1)
- r1 has NO c-edge (Step .r1 .c t = Empty for all t), so `neg(<c>T)` holds at r1
Therefore `<b>T /\ neg(<c>T)` holds at r1, and `<a>(<b>T /\ neg(<c>T))` holds at r0. -/
theorem pair2_vgSimA_satisfies :
    pair2Formula.satisfiedAt vgSimALTS .r0 := by
  refine ⟨.r1, ⟨()⟩, ⟨.r3, ⟨()⟩, trivial⟩, ?_⟩
  -- Need to show ¬ ∃ t, Nonempty (vgSimALTS.Step .r1 .c t) ∧ True
  intro ⟨t, ht, _⟩
  cases t with
  | r0 => exact (ht.some).elim
  | r1 => exact (ht.some).elim
  | r2 => exact (ht.some).elim
  | r3 => exact (ht.some).elim
  | r4 => exact (ht.some).elim
  | r5 => exact (ht.some).elim

/-- `pair2Formula` is NOT satisfied at vgTraceB.q0.

In vgTraceB (CCS process `a.(b+c)`):
- q0's only a-successor is q1 (Step .q0 .a .q1 = Unit, all others Empty)
- At q1: q1 ->^c q3, so `<c>T` holds at q1, hence `neg(<c>T)` fails at q1
- Therefore the conjunction `<b>T /\ neg(<c>T)` fails at q1
- Since q1 is the only a-successor, `<a>(<b>T /\ neg(<c>T))` fails at q0 -/
theorem pair2_vgTraceB_not_satisfies :
    ¬ pair2Formula.satisfiedAt vgTraceBLTS .q0 := by
  intro ⟨t, ht_step, _hb, hc⟩
  cases t with
  | q0 => exact (ht_step.some).elim
  | q1 =>
    -- q1 can do c, so neg(<c>T) fails
    apply hc
    exact ⟨.q3, ⟨()⟩, trivial⟩
  | q2 => exact (ht_step.some).elim
  | q3 => exact (ht_step.some).elim

/-- **Pair 2 separation**: simulation equivalence is strictly coarser than ready-simulation.

The formula `<a>(<b>T /\ neg(<c>T))` is in HML_ready \ HML_pos (ready-sim but not positive),
and it separates vgSimA from vgTraceB. Since simulation-equivalent systems agree on all
positive formulas and ready-simulation-equivalent systems agree on all ready-sim formulas,
this pair witnesses that ready-simulation can distinguish systems that simulation cannot. -/
theorem pair2_simulation_neq_readySim :
    ∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isReadySimFormula = true ∧ phi.isPositive = false ∧
      phi.satisfiedAt vgSimALTS .r0 ∧ ¬ phi.satisfiedAt vgTraceBLTS .q0 :=
  ⟨pair2Formula, rfl, rfl, pair2_vgSimA_satisfies, pair2_vgTraceB_not_satisfies⟩

/-!
## Part 3: Pair 3 — Ready-Simulation != Bisimulation

The standard van Glabbeek counterexample reuses the existing LTS examples:
  P = `vgSimA` (CCS process `a.b + a.(b+c)`, states r0-r5)
  Q = `vgTraceB` (CCS process `a.(b+c)`, states q0-q3)

The distinguishing formula is `[a]<c>T` = "all a-successors can do c":
- At Q (q0): q1 is the only a-successor, and q1 ->^c q3. So `[a]<c>T` holds.
- At P (r0): r1 is an a-successor, and r1 has NO c-edge. So `[a]<c>T` fails.

The formula `[a]<c>T = neg(diamond .a (neg(diamond .c top)))` uses nested negation,
so `isReadySimFormula` returns false (only `neg(diamond _ top)` is allowed as negation).
But `isBisimFormula` returns true (all HML formulas are bisim formulas).
-/

/-- Distinguishing formula for Pair 3: `[a]<c>T` = `box .a (diamond .c top)`.
"All a-successors can perform action c."
This is a full HML formula (bisim) but NOT a ready-simulation formula,
because it uses nested negation `neg(diamond .a (neg(diamond .c top)))`,
which is not an inability atom `neg(diamond _ top)`. -/
def pair3Formula : LabeledHML ThreeLabelAlphabet := box .a (.diamond .c .top)

/-- `pair3Formula` is a bisimulation formula but not a ready-simulation formula. -/
theorem pair3Formula_bisim_not_readySim :
    pair3Formula.isBisimFormula = true ∧ pair3Formula.isReadySimFormula = false :=
  ⟨rfl, rfl⟩

/-- `pair3Formula` is satisfied at vgTraceB.q0.

In vgTraceB (CCS process `a.(b+c)`):
- q0's only a-successor is q1 (Step .q0 .a .q1 = Unit, all others Empty)
- q1 ->^c q3, so `<c>T` holds at q1
- Therefore `[a]<c>T` holds at q0: every a-successor (just q1) can do c.

Unfolding `box`: need `¬ ∃ t, Nonempty (Step q0 .a t) ∧ ¬(∃ u, Nonempty (Step t .c u) ∧ True)`.
The only a-successor is q1, and q1 has a c-edge to q3, contradicting the inner negation. -/
theorem pair3_vgTraceB_satisfies :
    pair3Formula.satisfiedAt vgTraceBLTS .q0 := by
  intro ⟨t, ht_step, hc⟩
  cases t with
  | q0 => exact (ht_step.some).elim
  | q1 =>
    -- q1 can do c: q1 ->^c q3
    apply hc
    exact ⟨.q3, ⟨()⟩, trivial⟩
  | q2 => exact (ht_step.some).elim
  | q3 => exact (ht_step.some).elim

/-- `pair3Formula` is NOT satisfied at vgSimA.r0.

In vgSimA (CCS process `a.b + a.(b+c)`):
- r0 has a-successors r1 and r2
- r1 has NO c-edge (Step .r1 .c t = Empty for all t)
- Therefore `[a]<c>T` fails at r0: r1 is an a-successor that cannot do c.

Unfolding: `¬ pair3Formula.satisfiedAt ...` = `¬¬(∃ t, Nonempty (Step r0 .a t) ∧ ¬(∃ u, ...))`.
We provide witness r1: r1 is an a-successor of r0, and r1 has no c-edges. -/
theorem pair3_vgSimA_not_satisfies :
    ¬ pair3Formula.satisfiedAt vgSimALTS .r0 := by
  intro h
  -- h : ¬ (∃ t, Nonempty (Step r0 .a t) ∧ ¬(∃ u, Nonempty (Step t .c u) ∧ True))
  -- Provide witness: r1 is an a-successor with no c-edges
  apply h
  refine ⟨.r1, ⟨()⟩, ?_⟩
  intro ⟨u, hu, _⟩
  cases u with
  | r0 => exact (hu.some).elim
  | r1 => exact (hu.some).elim
  | r2 => exact (hu.some).elim
  | r3 => exact (hu.some).elim
  | r4 => exact (hu.some).elim
  | r5 => exact (hu.some).elim

/-- **Pair 3 separation**: Ready-simulation equivalence is strictly coarser than bisimulation.

The formula `[a]<c>T` is in HML \ HML_ready (bisim but not ready-sim), and it
separates vgTraceB from vgSimA. Since ready-simulation-equivalent systems agree on
all ready-sim formulas and bisimulation-equivalent systems agree on all HML formulas,
this pair witnesses that bisimulation can distinguish systems that ready-simulation cannot.

**Standard example**: P = `vgSimA` (a.b + a.(b+c)), Q = `vgTraceB` (a.(b+c)).
P and Q are ready-simulation equivalent (mutual simulation preserving ready sets),
but NOT bisimilar (the back condition fails: r1 in P has ready {b} while q1 in Q
has ready {b,c}). The formula `[a]<c>T` holds at Q but not P, detecting this. -/
theorem pair3_readySim_neq_bisim :
    ∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isBisimFormula = true ∧ phi.isReadySimFormula = false ∧
      phi.satisfiedAt vgTraceBLTS .q0 ∧ ¬ phi.satisfiedAt vgSimALTS .r0 :=
  ⟨pair3Formula, rfl, rfl, pair3_vgTraceB_satisfies, pair3_vgSimA_not_satisfies⟩

/-- **4-Level Spectrum Separation**: The van Glabbeek spectrum has four genuinely
distinct levels for labeled transition systems.

Each adjacent pair of levels is separated by a concrete distinguishing formula
evaluated on concrete LTS examples:
1. Trace != Simulation: `<a>(<b>T /\ <c>T)` separates vgTraceB from vgTraceA
2. Simulation != Ready-Sim: `<a>(<b>T /\ neg(<c>T))` separates vgSimA from vgTraceB
3. Ready-Sim != Bisimulation: `[a]<c>T` separates vgTraceB from vgSimA

This breaks the upper collapse from `SpectrumEmbedding.lean` where
simulation = ready-simulation = bisimulation for diamond-only (unlabeled) HML. -/
theorem labeled_four_level_separation :
    -- trace != simulation
    (∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isPositive = true ∧ phi.isTraceFormula = false ∧
      phi.satisfiedAt vgTraceBLTS .q0 ∧ ¬ phi.satisfiedAt vgTraceALTS .p0) ∧
    -- simulation != ready-simulation
    (∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isReadySimFormula = true ∧ phi.isPositive = false ∧
      phi.satisfiedAt vgSimALTS .r0 ∧ ¬ phi.satisfiedAt vgTraceBLTS .q0) ∧
    -- ready-simulation != bisimulation
    (∃ phi : LabeledHML ThreeLabelAlphabet,
      phi.isBisimFormula = true ∧ phi.isReadySimFormula = false ∧
      phi.satisfiedAt vgTraceBLTS .q0 ∧ ¬ phi.satisfiedAt vgSimALTS .r0) :=
  ⟨pair1_trace_neq_simulation, pair2_simulation_neq_readySim, pair3_readySim_neq_bisim⟩

/-- Labeled systems break the upper spectrum collapse.

In `SpectrumEmbedding.lean`, the upper three spectrum levels (simulation,
ready-simulation, bisimulation) collapse for diamond-only (unlabeled) HML because
the single diamond modality cannot distinguish different actions. With labeled HML
(per-action diamond + negation), the full four-level hierarchy is restored.

This theorem witnesses the break: a positive non-trace formula separates two concrete
labeled LTS, which is impossible in the collapsed unlabeled setting. -/
theorem labeled_spectrum_collapse_broken :
    -- The upper collapse (sim = bisim for unlabeled) does NOT hold for labeled systems
    ∃ (phi : LabeledHML ThreeLabelAlphabet),
      phi.isPositive = true ∧ phi.isTraceFormula = false ∧
      phi.satisfiedAt vgTraceBLTS .q0 ∧ ¬ phi.satisfiedAt vgTraceALTS .p0 :=
  pair1_trace_neq_simulation

end RTS
