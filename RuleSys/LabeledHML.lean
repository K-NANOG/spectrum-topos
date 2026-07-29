/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Labeled Hennessy-Milner Logic (Labeled HML)

This file defines Hennessy-Milner Logic with per-action diamond modalities and
classical negation, for labeled transition systems. Unlike the diamond-only HML
in `HML.lean` (which operates on unlabeled `RootedTS`), this version:

1. Parameterizes diamond by an action label: `<a>phi` checks for an a-labeled successor
2. Includes negation: `neg phi` gives classical negation
3. Operates on `LabeledLTS` (strong labeled transition systems)

## Sublanguage Hierarchy

With labels and negation, the van Glabbeek spectrum's four levels are genuinely
distinct (unlike the diamond-only collapse in `SpectrumEmbedding.lean`):

- **O (trace formulas)**: diamond + disjunction only (no conjunction, no negation)
- **HML_pos (positive formulas)**: all formulas without negation
- **HML_ready (ready-simulation formulas)**: positive + inability atoms `neg(<a>top)`
- **HML (full bisimulation formulas)**: all formulas including arbitrary negation

The strict inclusion chain `O < HML_pos < HML_ready < HML` is witnessed by
concrete separating formulas, breaking the upper collapse of diamond-only HML.

## Main Results

1. `LabeledHML` -- Labeled HML formulas with per-action diamond and negation
2. `LabeledHML.satisfiedAt` -- Kripke semantics over `LabeledLTS`
3. `LabeledRelationalBisimulation` -- Labeled bisimulation (forth/back per action)
4. `labeled_bisim_invariant` -- Bisimulation invariance (iff version, 0 axioms)
5. `isTraceFormula`, `isPositive`, `isReadySimFormula`, `isBisimFormula` -- Sublanguage predicates
6. `labeled_sublanguage_strict_chain` -- Strict inclusion with witnesses
7. `SpectrumLevel.labeledSublanguage` -- Connection to spectrum infrastructure

## References

- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
-/

import RuleSys.SubtoposLattice.LabeledExamples
import RuleSys.SubtoposLattice.SpectrumEmbedding

set_option autoImplicit false

namespace RTS

universe u v

/-!
## Part 1: LabeledHML Definition and Semantics
-/

/-- Labeled Hennessy-Milner Logic with per-action diamond and negation.

    Unlike diamond-only `HML` (which has a single unlabeled `diamond`), this
    version parameterizes diamond by an action label and includes negation.
    This is the full HML needed to characterize bisimulation for labeled LTS.

    - `top`: true (tautology)
    - `bot`: false (contradiction)
    - `conj phi psi`: phi AND psi
    - `disj phi psi`: phi OR psi
    - `diamond a phi`: <a>phi = "exists an a-successor satisfying phi"
    - `neg phi`: NOT phi (classical negation) -/
inductive LabeledHML (Label : Type u) : Type u
  | top : LabeledHML Label
  | bot : LabeledHML Label
  | conj : LabeledHML Label → LabeledHML Label → LabeledHML Label
  | disj : LabeledHML Label → LabeledHML Label → LabeledHML Label
  | diamond : Label → LabeledHML Label → LabeledHML Label
  | neg : LabeledHML Label → LabeledHML Label

namespace LabeledHML

variable {Label : Type*}

/-- Box modality: [a]phi := neg(<a>(neg phi)).
    "All a-successors satisfy phi." -/
abbrev box (a : Label) (phi : LabeledHML Label) : LabeledHML Label :=
  .neg (.diamond a (.neg phi))

/-- Action a is enabled: <a>top.
    "There exists some a-successor." -/
abbrev canDo (a : Label) : LabeledHML Label :=
  .diamond a .top

/-- Inability atom: neg(<a>top).
    "Action a is not enabled." This is the key formula that separates
    ready-simulation from simulation: it is in HML_ready but not HML_pos. -/
abbrev cannotDo (a : Label) : LabeledHML Label :=
  .neg (.diamond a .top)

/-- Kripke semantics over a labeled transition system.

    The diamond modality `<a>phi` checks for an a-labeled successor satisfying phi.
    Negation `neg phi` is classical (not intuitionistic): `neg phi` holds iff `phi`
    does not hold. This gives full classical HML semantics.

    Returns `Prop` (not `Bool`), so decidability is not required. -/
def satisfiedAt (M : LabeledLTS Label) (s : M.State)
    : LabeledHML Label → Prop
  | .top => True
  | .bot => False
  | .conj phi psi => phi.satisfiedAt M s ∧ psi.satisfiedAt M s
  | .disj phi psi => phi.satisfiedAt M s ∨ psi.satisfiedAt M s
  | .diamond a phi => ∃ t, Nonempty (M.Step s a t) ∧ phi.satisfiedAt M t
  | .neg phi => ¬ phi.satisfiedAt M s

/-- System-level validity: `phi` holds at every state of `M`. -/
def validIn (M : LabeledLTS Label) (phi : LabeledHML Label) : Prop :=
  ∀ s : M.State, phi.satisfiedAt M s

/-!
## Part 2: Sublanguage Predicates

Each spectrum level corresponds to a sublanguage of labeled HML. With labels
and negation, all four levels are genuinely distinct.
-/

/-- Trace sublanguage predicate: diamond and disjunction only.

    Trace formulas capture "possible future action sequences" but cannot express:
    - Conjunction (branching: "has both an a-successor and a b-successor")
    - Negation (refusal: "cannot do action a")

    This is the coarsest useful observation level.

    Matches the classical definition: O = {top, bot, disj, <a>} -/
def isTraceFormula : LabeledHML Label → Bool
  | .top => true
  | .bot => true
  | .conj _ _ => false
  | .disj phi psi => phi.isTraceFormula && psi.isTraceFormula
  | .diamond _ phi => phi.isTraceFormula
  | .neg _ => false

/-- Positive sublanguage predicate: no negation allowed.

    Positive formulas can express conjunction (branching) but not refusal.
    This characterizes simulation preorder: two states are simulation-equivalent
    iff they satisfy the same positive labeled HML formulas.

    Matches the classical definition: HML_pos = {top, bot, conj, disj, <a>} -/
def isPositive : LabeledHML Label → Bool
  | .top => true
  | .bot => true
  | .conj phi psi => phi.isPositive && psi.isPositive
  | .disj phi psi => phi.isPositive && psi.isPositive
  | .diamond _ phi => phi.isPositive
  | .neg _ => false

/-- Ready-simulation sublanguage predicate: positive + inability atoms.

    Ready-simulation formulas extend positive formulas with the ability to
    observe which actions are NOT enabled. The key addition is the inability
    atom `neg(<a>top)` ("action a is disabled"), which tests readiness.

    Arbitrary negation is still excluded -- only `neg(<a>top)` is allowed.
    This captures ready-simulation equivalence.

    Pattern matching on nested constructors:
    - `neg (diamond _ top)` => true (inability atom)
    - `neg _` => false (arbitrary negation excluded) -/
def isReadySimFormula : LabeledHML Label → Bool
  | .top => true
  | .bot => true
  | .conj phi psi => phi.isReadySimFormula && psi.isReadySimFormula
  | .disj phi psi => phi.isReadySimFormula && psi.isReadySimFormula
  | .diamond _ phi => phi.isReadySimFormula
  | .neg (.diamond _ .top) => true
  | .neg _ => false

/-- Bisimulation sublanguage predicate: all labeled HML formulas.

    The full HML characterizes bisimulation equivalence (Hennessy-Milner theorem).
    Every formula qualifies. -/
def isBisimFormula : LabeledHML Label → Bool := fun _ => true

end LabeledHML

/-!
## Part 3: Labeled Bisimulation and Invariance

A labeled relational bisimulation has forth and back conditions parameterized
by action label. The bisimulation invariance theorem is proved by structural
induction, with the negation case using `not_congr` (= `Iff.not` in Mathlib).
-/

/-- Labeled relational bisimulation: forth and back conditions parameterized by action label.

    This is the Park-Milner definition adapted to labeled transition systems.
    For each action `a`, related states must be able to match each other's
    a-transitions while maintaining the relation.

    Compare with `RelationalBisimulation` in `Bisimulation.lean` which uses
    unlabeled transitions. -/
def LabeledRelationalBisimulation {Label : Type*}
    (M N : LabeledLTS Label) (R : M.State → N.State → Prop) : Prop :=
  (∀ s t, R s t → ∀ (a : Label) s', Nonempty (M.Step s a s') →
    ∃ t', Nonempty (N.Step t a t') ∧ R s' t') ∧
  (∀ s t, R s t → ∀ (a : Label) t', Nonempty (N.Step t a t') →
    ∃ s', Nonempty (M.Step s a s') ∧ R s' t')

namespace LabeledHML

variable {Label : Type*}

/-- **Bisimulation Invariance of Labeled HML (iff version).**

    Labeled HML formulas are invariant under labeled relational bisimulation:
    if `R` is a labeled bisimulation and `R s t`, then `phi` holds at `s` iff at `t`.

    This is the labeled analogue of `HML.bisim_invariant` from `HML.lean`, extended
    with negation. The proof proceeds by structural induction. The negation case
    uses `not_congr` (Mathlib's `Iff.not`): from `phi(s) <-> phi(t)`, conclude
    `not phi(s) <-> not phi(t)`.

    **Axiom count: 0** -- fully constructive proof by structural induction. -/
theorem labeled_bisim_invariant
    {M N : LabeledLTS Label}
    {R : M.State → N.State → Prop}
    (hR : LabeledRelationalBisimulation M N R)
    (phi : LabeledHML Label) {s : M.State} {t : N.State} (hst : R s t) :
    phi.satisfiedAt M s ↔ phi.satisfiedAt N t := by
  induction phi generalizing s t with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | conj phi psi ih_phi ih_psi =>
    exact Iff.and (ih_phi hst) (ih_psi hst)
  | disj phi psi ih_phi ih_psi =>
    exact Iff.or (ih_phi hst) (ih_psi hst)
  | diamond a phi ih =>
    constructor
    · rintro ⟨s', hs', h_phi⟩
      obtain ⟨t', ht', hR'⟩ := hR.1 s t hst a s' hs'
      exact ⟨t', ht', (ih hR').mp h_phi⟩
    · rintro ⟨t', ht', h_phi⟩
      obtain ⟨s', hs', hR'⟩ := hR.2 s t hst a t' ht'
      exact ⟨s', hs', (ih hR').mpr h_phi⟩
  | neg phi ih =>
    exact not_congr (ih hst)

/-- Labeled HML is preserved forward by labeled bisimulation.

    If `(s, t) in R` and `phi` holds at `s`, then `phi` holds at `t`.
    Derived from the iff version `labeled_bisim_invariant`. -/
theorem labeled_bisim_invariant_forth
    {M N : LabeledLTS Label}
    {R : M.State → N.State → Prop}
    (hR : LabeledRelationalBisimulation M N R)
    (phi : LabeledHML Label) {s : M.State} {t : N.State} (hst : R s t) :
    phi.satisfiedAt M s → phi.satisfiedAt N t :=
  (labeled_bisim_invariant hR phi hst).mp

/-- Labeled HML is preserved backward by labeled bisimulation.

    If `(s, t) in R` and `phi` holds at `t`, then `phi` holds at `s`.
    Derived from the iff version `labeled_bisim_invariant`. -/
theorem labeled_bisim_invariant_back
    {M N : LabeledLTS Label}
    {R : M.State → N.State → Prop}
    (hR : LabeledRelationalBisimulation M N R)
    (phi : LabeledHML Label) {s : M.State} {t : N.State} (hst : R s t) :
    phi.satisfiedAt N t → phi.satisfiedAt M s :=
  (labeled_bisim_invariant hR phi hst).mpr

/-!
## Part 4: Sublanguage Inclusions
-/

/-- Trace formulas are positive: O subset HML_pos. -/
theorem trace_sub_positive :
    ∀ phi : LabeledHML Label,
    phi.isTraceFormula = true → phi.isPositive = true := by
  intro phi
  induction phi with
  | top => simp [isTraceFormula, isPositive]
  | bot => simp [isTraceFormula, isPositive]
  | conj _ _ _ _ => simp [isTraceFormula]
  | disj phi psi ih_phi ih_psi =>
    simp [isTraceFormula, isPositive, Bool.and_eq_true]
    exact fun h1 h2 => ⟨ih_phi h1, ih_psi h2⟩
  | diamond _ phi ih =>
    simp [isTraceFormula, isPositive]
    exact ih
  | neg _ _ => simp [isTraceFormula]

/-- Positive formulas are ready-simulation formulas: HML_pos subset HML_ready. -/
theorem positive_sub_readySim :
    ∀ phi : LabeledHML Label,
    phi.isPositive = true → phi.isReadySimFormula = true := by
  intro phi
  induction phi with
  | top => simp [isPositive, isReadySimFormula]
  | bot => simp [isPositive, isReadySimFormula]
  | conj phi psi ih_phi ih_psi =>
    simp [isPositive, isReadySimFormula, Bool.and_eq_true]
    exact fun h1 h2 => ⟨ih_phi h1, ih_psi h2⟩
  | disj phi psi ih_phi ih_psi =>
    simp [isPositive, isReadySimFormula, Bool.and_eq_true]
    exact fun h1 h2 => ⟨ih_phi h1, ih_psi h2⟩
  | diamond _ phi ih =>
    simp [isPositive, isReadySimFormula]
    exact ih
  | neg _ _ => simp [isPositive]

/-- Ready-simulation formulas are bisimulation formulas: HML_ready subset HML.

    Trivial: `isBisimFormula` returns `true` for all formulas. -/
theorem readySim_sub_bisim :
    ∀ phi : LabeledHML Label,
    phi.isReadySimFormula = true → phi.isBisimFormula = true :=
  fun _ _ => rfl

/-!
## Part 5: Strict Separation Witnesses
-/

/-- Witness: conjunction of diamonds is positive but not a trace formula.

    `<a>top AND <b>top` expresses "can do both a and b". This uses conjunction,
    which is excluded from trace formulas. -/
theorem conj_diamond_positive_not_trace (a b : Label) :
    (conj (diamond a top) (diamond b top) : LabeledHML Label).isPositive = true ∧
    (conj (diamond a top) (diamond b top) : LabeledHML Label).isTraceFormula = false :=
  ⟨rfl, rfl⟩

/-- Witness: inability atom is ready-sim but not positive.

    `neg(<a>top)` expresses "cannot do action a". This uses negation (specifically
    the inability pattern), which is excluded from positive formulas but allowed
    in ready-simulation formulas. -/
theorem inability_readySim_not_positive (a : Label) :
    (neg (diamond a top) : LabeledHML Label).isReadySimFormula = true ∧
    (neg (diamond a top) : LabeledHML Label).isPositive = false :=
  ⟨rfl, rfl⟩

/-- Witness: negation of conjunction is bisim but not ready-sim.

    `neg(<a>top AND <b>top)` is a full negation of a conjunction, which is NOT
    an inability atom. Ready-simulation formulas only allow `neg(<a>top)` as
    negation, not arbitrary `neg(...)`. -/
theorem neg_conj_bisim_not_readySim (a b : Label) :
    (neg (conj (diamond a top) (diamond b top)) : LabeledHML Label).isBisimFormula = true ∧
    (neg (conj (diamond a top) (diamond b top)) : LabeledHML Label).isReadySimFormula = false :=
  ⟨rfl, rfl⟩

/-- **Strict inclusion chain**: O < HML_pos < HML_ready < HML.

    Each level of the labeled HML sublanguage hierarchy is strictly contained
    in the next. This is witnessed by:
    - `<a>top AND <b>top` in HML_pos \ O (conjunction breaks trace)
    - `neg(<a>top)` in HML_ready \ HML_pos (inability breaks positive)
    - `neg(<a>top AND <b>top)` in HML \ HML_ready (full negation breaks ready-sim)

    This breaks the upper collapse from `SpectrumEmbedding.lean` where
    simulation = ready-simulation = bisimulation for diamond-only HML. -/
theorem labeled_sublanguage_strict_chain (a b : Label) :
    (∃ phi : LabeledHML Label, phi.isPositive = true ∧ phi.isTraceFormula = false) ∧
    (∃ phi : LabeledHML Label, phi.isReadySimFormula = true ∧ phi.isPositive = false) ∧
    (∃ phi : LabeledHML Label, phi.isBisimFormula = true ∧ phi.isReadySimFormula = false) :=
  ⟨⟨conj (diamond a top) (diamond b top), rfl, rfl⟩,
   ⟨neg (diamond a top), rfl, rfl⟩,
   ⟨neg (conj (diamond a top) (diamond b top)), rfl, rfl⟩⟩

/-!
## Part 6: Named Labeled HML Formulas
-/

/-- <a>top: "can perform action a" -/
def hasAction (a : Label) : LabeledHML Label := diamond a top

/-- <a><b>top: "can perform action a followed by action b" -/
def hasSequence (a b : Label) : LabeledHML Label :=
  diamond a (diamond b top)

/-- <a>phi AND <b>psi: "has an a-successor satisfying phi and a b-successor satisfying psi" -/
def diamondBothLabeled (a : Label) (phi : LabeledHML Label)
    (b : Label) (psi : LabeledHML Label) : LabeledHML Label :=
  conj (diamond a phi) (diamond b psi)

end LabeledHML

/-!
## Part 7: L-Equivalence and Spectrum Connection
-/

/-- Labeled L-equivalence: two states in a labeled LTS agree on all formulas
    in the sublanguage L. -/
def LabeledHMLEquiv {Label : Type*} (L : LabeledHML Label → Bool)
    (M : LabeledLTS Label) (s t : M.State) : Prop :=
  ∀ phi : LabeledHML Label, L phi = true →
    (phi.satisfiedAt M s ↔ phi.satisfiedAt M t)

/-- Map each spectrum level to its labeled HML sublanguage predicate.

    Unlike `SpectrumLevel.sublanguage` (for diamond-only HML, where the upper
    three levels collapse), the labeled version has four genuinely distinct
    sublanguages because labeled HML has per-action diamond and negation. -/
def SpectrumLevel.labeledSublanguage (Label : Type*) :
    SpectrumLevel → (LabeledHML Label → Bool)
  | .trace => LabeledHML.isTraceFormula
  | .simulation => LabeledHML.isPositive
  | .readySimulation => LabeledHML.isReadySimFormula
  | .bisimulation => LabeledHML.isBisimFormula

/-- Labeled sublanguage inclusion is monotone with respect to the spectrum ordering.

    If `l1 <= l2` in the spectrum, then every formula in `l1`'s sublanguage
    is also in `l2`'s sublanguage. This is the labeled analogue of
    `sublanguage_incl` from `SpectrumEmbedding.lean`. -/
theorem labeled_sublanguage_incl {Label : Type*}
    (l1 l2 : SpectrumLevel) (hle : l1 ≤ l2)
    (phi : LabeledHML Label) (h_phi : SpectrumLevel.labeledSublanguage Label l1 phi = true) :
    SpectrumLevel.labeledSublanguage Label l2 phi = true := by
  match l1, l2 with
  | .trace, .trace => exact h_phi
  | .trace, .simulation =>
    exact LabeledHML.trace_sub_positive phi h_phi
  | .trace, .readySimulation =>
    exact LabeledHML.positive_sub_readySim phi (LabeledHML.trace_sub_positive phi h_phi)
  | .trace, .bisimulation => rfl
  | .simulation, .simulation => exact h_phi
  | .simulation, .readySimulation =>
    exact LabeledHML.positive_sub_readySim phi h_phi
  | .simulation, .bisimulation => rfl
  | .readySimulation, .readySimulation => exact h_phi
  | .readySimulation, .bisimulation => rfl
  | .bisimulation, .bisimulation => rfl
  | .simulation, .trace => exact absurd hle (by show ¬(1 ≤ 0); omega)
  | .readySimulation, .trace => exact absurd hle (by show ¬(2 ≤ 0); omega)
  | .readySimulation, .simulation => exact absurd hle (by show ¬(2 ≤ 1); omega)
  | .bisimulation, .trace => exact absurd hle (by show ¬(3 ≤ 0); omega)
  | .bisimulation, .simulation => exact absurd hle (by show ¬(3 ≤ 1); omega)
  | .bisimulation, .readySimulation => exact absurd hle (by show ¬(3 ≤ 2); omega)

/-- Labeled spectrum monotonicity: a finer (larger) spectrum level induces a finer
    (more discriminating) equivalence. -/
theorem labeled_spectrum_monotone {Label : Type*}
    {l1 l2 : SpectrumLevel} (hle : l1 ≤ l2)
    {M : LabeledLTS Label} {s t : M.State}
    (heq : LabeledHMLEquiv (SpectrumLevel.labeledSublanguage Label l2) M s t) :
    LabeledHMLEquiv (SpectrumLevel.labeledSublanguage Label l1) M s t :=
  fun phi h_phi => heq phi (labeled_sublanguage_incl l1 l2 hle phi h_phi)

/-- Labeled bisimulation implies L-equivalence at every spectrum level. -/
theorem labeled_bisim_implies_all_spectrum_equiv {Label : Type*}
    {M N : LabeledLTS Label}
    {R : M.State → N.State → Prop}
    (hR : LabeledRelationalBisimulation M N R)
    {s : M.State} {t : N.State} (hst : R s t) :
    ∀ l : SpectrumLevel, ∀ phi : LabeledHML Label,
    SpectrumLevel.labeledSublanguage Label l phi = true →
    (phi.satisfiedAt M s ↔ phi.satisfiedAt N t) :=
  fun _ phi _ => LabeledHML.labeled_bisim_invariant hR phi hst

end RTS
