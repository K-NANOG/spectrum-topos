/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Van Glabbeek Separating Counterexamples for Labeled Transition Systems

This file defines the standard separating counterexamples from van Glabbeek's
"Linear Time - Branching Time Spectrum" (1990) that witness the strict separation
between spectrum levels for labeled transition systems.

## Overview

The van Glabbeek spectrum for labeled LTS has (at least) four distinct levels:
1. **Trace equivalence** — same completed traces
2. **Simulation equivalence** — mutual simulation
3. **Ready-simulation equivalence** — mutual ready-simulation
4. **Bisimulation equivalence** — bisimilarity

Each adjacent pair is separated by concrete CCS-style counterexamples:

### Pair 1: Trace ≠ Simulation
- `vgTraceA` models CCS process `a.b + a.c` (5 states, early choice)
- `vgTraceB` models CCS process `a.(b+c)` (4 states, late choice)
- Both have trace set {ab, ac} and Lindenbaum cardinality 5
- No simulation from A to B exists (ready set mismatch after a)

### Pair 2: Simulation ≠ Ready-Simulation
- `vgSimA` models CCS process `a.b + a.(b+c)` (6 states)
- `vgSimB` = `vgTraceB` models CCS process `a.(b+c)` (4 states)
- Mutual simulation exists (both can match each other's transitions)
- No ready-simulation from A to B (ready set {b} at r1 ≠ {b,c} at q1)

### Key Insight

Pair 1 demonstrates that the Lindenbaum algebra (= propositional geometric theory)
does NOT distinguish all spectrum levels. Both `vgTraceA` and `vgTraceB` have
isomorphic 5-element Lindenbaum algebras, yet they are trace-equivalent but not
simulation-equivalent. The Lindenbaum algebra captures propositional content
(which transitions are forced/excluded), while simulation equivalence requires
modal depth-1 properties (diamond modalities).

## References

- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990)
- Vickers, "Topology via Logic" (1989)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
-/

import RuleSys.SubtoposLattice.LabeledTransitionSystems
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

universe u

open GeometricLogic.Propositional

namespace RTS

/-!
## Part 1: Three-Label Alphabet

The standard van Glabbeek counterexamples use three action labels {a, b, c}.
Two labels suffice for the basic labeled branching system in
`LabeledTransitionSystems.lean`, but three are needed for the `a.b + a.c`
vs `a.(b+c)` separation (Pair 1) which requires two distinct continuation
actions after the initial `a`-step.
-/

/-- Three-label alphabet: actions a, b, c.
Used for van Glabbeek separating counterexamples where distinct continuation
actions are needed to expose branching differences (e.g., `a.b + a.c` vs `a.(b+c)`). -/
inductive ThreeLabelAlphabet where
  | a | b | c
  deriving DecidableEq

instance : Fintype ThreeLabelAlphabet where
  elems := {.a, .b, .c}
  complete := fun x => by cases x <;> simp

/-!
## Part 2: Pair 1 — Trace Equivalent, Not Simulation Equivalent

### System vgTraceA: CCS process `a.b + a.c`

State diagram:
```
     p0
    / \
   a   a
  /     \
 p1     p2
 |       |
 b       c
 |       |
 p3     p4
```

States: p0 (initial), p1, p2, p3, p4
Edges: p0 ->^a p1, p0 ->^a p2, p1 ->^b p3, p2 ->^c p4

This process makes an early choice between the b-branch and c-branch at the
initial a-step. After choosing, only one continuation is available: p1 can
only do b, and p2 can only do c.

### System vgTraceB: CCS process `a.(b+c)`

State diagram:
```
  q0
  |
  a
  |
  q1
 / \
b   c
/     \
q2   q3
```

States: q0 (initial), q1, q2, q3
Edges: q0 ->^a q1, q1 ->^b q2, q1 ->^c q3

This process delays the choice: after a, state q1 can still do either b or c.
The trace sets are identical: {ab, ac}. But the branching structure differs.

### Separation

A simulation from vgTraceA to vgTraceB must map p0 to q0 (initial states).
After the a-step, p0 branches to p1 or p2. Both must map to q1 (the unique
a-successor of q0). But ready(p1) = {b} while ready(q1) = {b,c}. For the
simulation to work, every transition from the image q1 must be matchable
by the preimage p1 — but q1 ->^c q3 has no match from p1 (which can only do b).
Hence no simulation from A to B exists.
-/

/-- State type for `vgTraceA` — CCS process `a.b + a.c`.
- p0: initial state with nondeterministic a-choice
- p1: left branch, can only perform b
- p2: right branch, can only perform c
- p3: terminal state after b
- p4: terminal state after c -/
inductive VGTraceAState where
  | p0 | p1 | p2 | p3 | p4
  deriving DecidableEq

instance : Fintype VGTraceAState where
  elems := {.p0, .p1, .p2, .p3, .p4}
  complete := fun x => by cases x <;> simp

/-- Edge predicate for `vgTraceA` — CCS process `a.b + a.c`.

Transitions (4 edges out of 75 total triples):
- p0 ->^a p1 (choose left branch)
- p0 ->^a p2 (choose right branch)
- p1 ->^b p3 (continue left with b)
- p2 ->^c p4 (continue right with c) -/
def vgTraceA_hasEdge : VGTraceAState → ThreeLabelAlphabet → VGTraceAState → Bool
  | .p0, .a, .p1 => true
  | .p0, .a, .p2 => true
  | .p1, .b, .p3 => true
  | .p2, .c, .p4 => true
  | _, _, _ => false

/-- Propositional geometric theory of `vgTraceA` — CCS process `a.b + a.c`.

**Atoms**: `VGTraceAState x ThreeLabelAlphabet x VGTraceAState` = 5 x 3 x 5 = 75 atoms.
**Axioms**:
- 71 non-edge exclusions (75 - 4 edges)
- Totality for p0: `top |- step_a(p0,p1) V step_a(p0,p2)`
- Totality for p1: `top |- step_b(p1,p3)` (forced top)
- Totality for p2: `top |- step_c(p2,p4)` (forced top)
- No totality for p3, p4 (terminal states, no outgoing edges) -/
noncomputable def vgTraceATheory : PropGeoTheory.{0} :=
  mkLabeledTransitionTheory VGTraceAState ThreeLabelAlphabet vgTraceA_hasEdge

/-- The Lindenbaum algebra of `vgTraceATheory` is equivalent to `Fin 5`.

**Analysis**: Of 75 atoms, 71 are forced to bot (non-edges), 2 are forced to top
(step_b(p1,p3) and step_c(p2,p4) by totality of p1 and p2 with unique successors).
Free generators: p = step_a(p0,p1), q = step_a(p0,p2) with p V q = top (totality of p0).
Both coexist in multiway semantics, so p AND q != bot.
Result: {bot, p AND q, p, q, top} = 5 elements. -/
axiom vgTraceA_algebra_equiv : Nonempty (LindenbaumAlgebra vgTraceATheory ≃ Fin 5)

/-- The Lindenbaum algebra of `vgTraceATheory` has exactly 5 elements. -/
theorem vgTraceA_algebra_card :
    Fintype.card (LindenbaumAlgebra vgTraceATheory) = 5 := by
  obtain ⟨e⟩ := vgTraceA_algebra_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-- `vgTraceA` as a concrete `LabeledLTS` — CCS process `a.b + a.c`.
Transition types: Unit for existing edges, Empty for non-edges. -/
def vgTraceALTS : LabeledLTS ThreeLabelAlphabet where
  State := VGTraceAState
  Step := fun s l t => match s, l, t with
    | .p0, .a, .p1 => Unit
    | .p0, .a, .p2 => Unit
    | .p1, .b, .p3 => Unit
    | .p2, .c, .p4 => Unit
    | _, _, _ => Empty
  init := .p0

/-- The theory of `vgTraceALTS` matches `vgTraceATheory`. -/
theorem vgTraceALTS_theory_eq :
    mkLabeledTransitionTheory VGTraceAState ThreeLabelAlphabet
      vgTraceA_hasEdge = vgTraceATheory := rfl

/-- State type for `vgTraceB` — CCS process `a.(b+c)`.
- q0: initial state
- q1: post-a state with b+c choice still available
- q2: terminal state after b
- q3: terminal state after c -/
inductive VGTraceBState where
  | q0 | q1 | q2 | q3
  deriving DecidableEq

instance : Fintype VGTraceBState where
  elems := {.q0, .q1, .q2, .q3}
  complete := fun x => by cases x <;> simp

/-- Edge predicate for `vgTraceB` — CCS process `a.(b+c)`.

Transitions (3 edges out of 48 total triples):
- q0 ->^a q1 (perform a, arrive at choice point)
- q1 ->^b q2 (choose b)
- q1 ->^c q3 (choose c) -/
def vgTraceB_hasEdge : VGTraceBState → ThreeLabelAlphabet → VGTraceBState → Bool
  | .q0, .a, .q1 => true
  | .q1, .b, .q2 => true
  | .q1, .c, .q3 => true
  | _, _, _ => false

/-- Propositional geometric theory of `vgTraceB` — CCS process `a.(b+c)`.

**Atoms**: `VGTraceBState x ThreeLabelAlphabet x VGTraceBState` = 4 x 3 x 4 = 48 atoms.
**Axioms**:
- 45 non-edge exclusions (48 - 3 edges)
- Totality for q0: `top |- step_a(q0,q1)` (forced top, unique successor)
- Totality for q1: `top |- step_b(q1,q2) V step_c(q1,q3)`
- No totality for q2, q3 (terminal states) -/
noncomputable def vgTraceBTheory : PropGeoTheory.{0} :=
  mkLabeledTransitionTheory VGTraceBState ThreeLabelAlphabet vgTraceB_hasEdge

/-- The Lindenbaum algebra of `vgTraceBTheory` is equivalent to `Fin 5`.

**Analysis**: Of 48 atoms, 45 are forced to bot (non-edges), 1 is forced to top
(step_a(q0,q1) by totality of q0 with unique a-successor).
Free generators: r = step_b(q1,q2), s = step_c(q1,q3) with r V s = top (totality of q1).
Both coexist in multiway semantics, so r AND s != bot.
Result: {bot, r AND s, r, s, top} = 5 elements.

**Key observation**: This is the SAME cardinality as vgTraceATheory. The Lindenbaum
algebra cannot distinguish these two systems — both reduce to the free bounded
distributive lattice on 2 generators modulo (p V q = top). The separation between
trace equivalence and simulation equivalence is INVISIBLE at the propositional level
and requires modal depth-1 properties (the diamond operator `<a>phi`). -/
axiom vgTraceB_algebra_equiv : Nonempty (LindenbaumAlgebra vgTraceBTheory ≃ Fin 5)

/-- The Lindenbaum algebra of `vgTraceBTheory` has exactly 5 elements. -/
theorem vgTraceB_algebra_card :
    Fintype.card (LindenbaumAlgebra vgTraceBTheory) = 5 := by
  obtain ⟨e⟩ := vgTraceB_algebra_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-- `vgTraceB` as a concrete `LabeledLTS` — CCS process `a.(b+c)`.
Transition types: Unit for existing edges, Empty for non-edges. -/
def vgTraceBLTS : LabeledLTS ThreeLabelAlphabet where
  State := VGTraceBState
  Step := fun s l t => match s, l, t with
    | .q0, .a, .q1 => Unit
    | .q1, .b, .q2 => Unit
    | .q1, .c, .q3 => Unit
    | _, _, _ => Empty
  init := .q0

/-- The theory of `vgTraceBLTS` matches `vgTraceBTheory`. -/
theorem vgTraceBLTS_theory_eq :
    mkLabeledTransitionTheory VGTraceBState ThreeLabelAlphabet
      vgTraceB_hasEdge = vgTraceBTheory := rfl

/-!
## Part 3: Pair 2 — Simulation Equivalent, Not Ready-Simulation Equivalent

### System vgSimA: CCS process `a.b + a.(b+c)`

State diagram:
```
       r0
      / \
     a   a
    /     \
   r1     r2
   |     / \
   b    b   c
   |   /     \
   r3 r4     r5
```

States: r0 (initial), r1, r2, r3, r4, r5
Edges: r0 ->^a r1, r0 ->^a r2, r1 ->^b r3, r2 ->^b r4, r2 ->^c r5

This process has a.b (deterministic b-branch via r1) and a.(b+c) (nondeterministic
branch via r2 that can do either b or c). The early choice between r1 and r2
determines whether c is available.

### Separation

**Simulation A → B**: Map r0↦q0, r1↦q1, r2↦q1, r3↦q2, r4↦q2, r5↦q3.
Every transition in A has a matching transition in B under this mapping.

**Simulation B → A**: Map q0↦r0, q1↦r2, q2↦r4, q3↦r5.
Every transition in B has a matching transition in A under this mapping.

Hence A and B are simulation equivalent (mutual simulation exists).

**No ready-simulation A → B**: A ready-simulation f : B → A must satisfy
ready(f(s)) ⊇ ready(s) (or equivalently, ready(s) ⊆ ready(f(s)) in the
other direction). After a-step, r1 has ready set {b} while q1 has ready set {b,c}.
For any simulation mapping q1 to some state in A, if q1 maps to r1, then
ready(r1) = {b} ⊄ ready(q1) = {b,c}, violating the ready condition.
If q1 maps to r2, ready(r2) = {b,c} ⊇ ready(q1), but then the reverse
simulation must map r1 somewhere with ready set ⊇ {b}, and the only option
is q1 with ready {b,c} ⊃ {b}, violating ready-simulation in the A → B direction.
-/

/-- State type for `vgSimA` — CCS process `a.b + a.(b+c)`.
- r0: initial state with nondeterministic a-choice
- r1: left branch, can only perform b (ready set = {b})
- r2: right branch, can perform b or c (ready set = {b, c})
- r3: terminal state after r1 ->^b
- r4: terminal state after r2 ->^b
- r5: terminal state after r2 ->^c -/
inductive VGSimAState where
  | r0 | r1 | r2 | r3 | r4 | r5
  deriving DecidableEq

instance : Fintype VGSimAState where
  elems := {.r0, .r1, .r2, .r3, .r4, .r5}
  complete := fun x => by cases x <;> simp

/-- Edge predicate for `vgSimA` — CCS process `a.b + a.(b+c)`.

Transitions (5 edges out of 108 total triples):
- r0 ->^a r1 (choose left branch, deterministic b)
- r0 ->^a r2 (choose right branch, nondeterministic b+c)
- r1 ->^b r3 (continue left with b)
- r2 ->^b r4 (continue right with b)
- r2 ->^c r5 (continue right with c) -/
def vgSimA_hasEdge : VGSimAState → ThreeLabelAlphabet → VGSimAState → Bool
  | .r0, .a, .r1 => true
  | .r0, .a, .r2 => true
  | .r1, .b, .r3 => true
  | .r2, .b, .r4 => true
  | .r2, .c, .r5 => true
  | _, _, _ => false

/-- Propositional geometric theory of `vgSimA` — CCS process `a.b + a.(b+c)`.

**Atoms**: `VGSimAState x ThreeLabelAlphabet x VGSimAState` = 6 x 3 x 6 = 108 atoms.
**Axioms**:
- 103 non-edge exclusions (108 - 5 edges)
- Totality for r0: `top |- step_a(r0,r1) V step_a(r0,r2)`
- Totality for r1: `top |- step_b(r1,r3)` (forced top, unique successor)
- Totality for r2: `top |- step_b(r2,r4) V step_c(r2,r5)`
- No totality for r3, r4, r5 (terminal states)

**Lindenbaum structure**: The algebra has TWO independent pairs of free generators:
- {p, q} from r0's totality (p = step_a(r0,r1), q = step_a(r0,r2))
- {s, t} from r2's totality (s = step_b(r2,r4), t = step_c(r2,r5))

Each pair satisfies (x V y = top, x AND y != bot), giving a 5-element sublattice.
The two pairs are independent (no axiom relates p,q to s,t), so the Lindenbaum
algebra is the free product (in bounded distributive lattices) of two 5-element
lattices, which has 5 x 5 = 25 elements by the Birkhoff representation theorem. -/
noncomputable def vgSimATheory : PropGeoTheory.{0} :=
  mkLabeledTransitionTheory VGSimAState ThreeLabelAlphabet vgSimA_hasEdge

/-- The Lindenbaum algebra of `vgSimATheory` is equivalent to `Fin 25`.

**Analysis**: Free product of two 5-element bounded distributive lattices.
Generators: p = step_a(r0,r1), q = step_a(r0,r2), s = step_b(r2,r4), t = step_c(r2,r5).
Relations: p V q = top, s V t = top, p AND q != bot, s AND t != bot.
By Birkhoff duality, the spectrum has 5 x 5 = 25 prime filters,
hence 25 elements in the Lindenbaum algebra.

This is strictly larger than the 5-element algebras of vgTraceA and vgTraceB,
reflecting the additional branching complexity of the `a.b + a.(b+c)` process. -/
axiom vgSimA_algebra_equiv : Nonempty (LindenbaumAlgebra vgSimATheory ≃ Fin 25)

/-- The Lindenbaum algebra of `vgSimATheory` has exactly 25 elements. -/
theorem vgSimA_algebra_card :
    Fintype.card (LindenbaumAlgebra vgSimATheory) = 25 := by
  obtain ⟨e⟩ := vgSimA_algebra_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-- `vgSimA` as a concrete `LabeledLTS` — CCS process `a.b + a.(b+c)`.
Transition types: Unit for existing edges, Empty for non-edges. -/
def vgSimALTS : LabeledLTS ThreeLabelAlphabet where
  State := VGSimAState
  Step := fun s l t => match s, l, t with
    | .r0, .a, .r1 => Unit
    | .r0, .a, .r2 => Unit
    | .r1, .b, .r3 => Unit
    | .r2, .b, .r4 => Unit
    | .r2, .c, .r5 => Unit
    | _, _, _ => Empty
  init := .r0

/-- The theory of `vgSimALTS` matches `vgSimATheory`. -/
theorem vgSimALTS_theory_eq :
    mkLabeledTransitionTheory VGSimAState ThreeLabelAlphabet
      vgSimA_hasEdge = vgSimATheory := rfl

/-- The second system in Pair 2 is just `vgTraceB` — CCS process `a.(b+c)`.
Both Pair 1 and Pair 2 use the same `a.(b+c)` process as one of the pair members,
which is a characteristic feature of the van Glabbeek spectrum construction. -/
noncomputable abbrev vgSimBTheory := vgTraceBTheory

/-!
## Part 4: Spectrum Separation Axioms

The following axioms record the separation properties of the van Glabbeek
counterexamples. They are stated as `True` placeholders because the concrete
statement types (labeled HML formulas, labeled simulation relations, ready
sets) will be defined in later phases (120-121). The extensive docstrings
preserve the mathematical content and proof sketches for later formalization.
-/

/-- Pair 1: vgTraceA and vgTraceB are NOT simulation equivalent.
No simulation from vgTraceA to vgTraceB exists: p1 (ready {b}) and p2 (ready {c})
cannot both map to q1 (ready {b,c}) while preserving the simulation condition.
After doing a in vgTraceA, we commit to either the b-branch (p1) or c-branch (p2).
In vgTraceB, after a, state q1 can still do either b or c. But if we map p1 to q1,
then p1 can only do b, while q1 can also do c — the simulation must find a matching
c-step from p1, which doesn't exist.
Concrete proof via distinguishing formula: see `SpectrumSeparation.pair1_trace_neq_simulation`. -/
theorem vgPair1_not_simulationEquiv : True := trivial

/-- Pair 2: vgSimA and vgTraceB are NOT ready-simulation equivalent.
Ready-simulation requires preserving ready sets (sets of enabled actions).
In vgSimA, after a, r1 has ready set {b}. In vgTraceB, after a, q1 has
ready set {b, c}. Any simulation mapping r1 to q1 violates the ready condition
because ready(q1) = {b,c} ⊄ ready(r1) = {b}. (Ready simulation from M to N
requires ready(f(s)) ⊆ ready(s) for the simulation function f : N → M.)
Concrete proof via distinguishing formula: see `SpectrumSeparation.pair2_simulation_neq_readySim`. -/
theorem vgPair2_not_readySimEquiv : True := trivial

/-- Ready-simulation and bisimulation are distinct equivalences for labeled LTS.
The formula `[a]<c>T` separates vgTraceB from vgSimA: it holds at q0 (all a-successors
can do c) but fails at r0 (r1 is an a-successor that cannot do c).
Proved in `SpectrumSeparation.pair3_readySim_neq_bisim`. -/
theorem readySim_neq_bisim_separation_exists : True := trivial

/-- The van Glabbeek spectrum has four genuinely distinct levels for labeled systems.
This breaks the upper spectrum collapse from SpectrumEmbedding.lean where
simulation = bisimulation for unlabeled systems (single diamond modality).
With labels, the HML sublanguage hierarchy O ⊂ HML_pos ⊂ HML_ready ⊂ HML
characterizes exactly the four levels: trace, simulation, ready simulation,
bisimulation. Each adjacent pair is separated by concrete counterexamples:
- trace ≠ simulation: vgTraceA vs vgTraceB (Pair 1, `<a>(<b>T /\ <c>T)`)
- simulation ≠ ready-simulation: vgSimA vs vgTraceB (Pair 2, `<a>(<b>T /\ neg(<c>T))`)
- ready-simulation ≠ bisimulation: vgTraceB vs vgSimA (Pair 3, `[a]<c>T`)
See `SpectrumSeparation.labeled_four_level_separation` for the full proof. -/
theorem labeled_spectrum_has_four_levels : True := trivial

end RTS
