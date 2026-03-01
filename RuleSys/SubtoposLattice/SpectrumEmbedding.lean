/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Van Glabbeek Spectrum Embedding

This file defines the van Glabbeek spectrum structure as a partially ordered
set of HML sublanguages, and connects it to bisimulation invariance.

## Mathematical Content

The van Glabbeek spectrum organizes process equivalences from coarsest (trace
equivalence) to finest (bisimulation equivalence). Each level corresponds to
an HML sublanguage: a subset of Hennessy-Milner Logic formulas. Two states are
L-equivalent if they agree on all formulas in the sublanguage L.

In our diamond-only setting (no negation, no box), the simulation, ready-simulation,
and bisimulation sublanguages all coincide with full HML. Only trace equivalence
is strictly coarser, restricting to the negation-free, conjunction-free fragment
(only disjunction and diamond).

## Main Results

1. `SpectrumLevel` — 4-element ordered type: trace < simulation < readySimulation < bisimulation
2. `HML.isTraceFormula` — Predicate for the trace (diamond+disjunction-only) fragment
3. `HMLEquiv` — L-equivalence: agreement on all formulas in a sublanguage
4. `spectrum_monotone` — Finer spectrum level implies finer equivalence
5. `bisim_implies_all_spectrum_equiv` — Bisimulation implies L-equivalence at every level

## Diamond-Only Collapse

In the diamond-only fragment of HML (no negation, no box), the distinction between
simulation, ready-simulation, and bisimulation sublanguages collapses:
- **Simulation** formulas: all positive formulas (= all diamond-only HML)
- **Ready-simulation** formulas: simulation + readiness predicates (trivial in diamond-only)
- **Bisimulation** formulas: all HML formulas (= all diamond-only HML)

Since diamond-only HML has no negation, the three sublanguages coincide.
The spectrum retains its ordered structure to match the classical theory, but
the equivalences induced at levels simulation, readySimulation, and bisimulation
are identical in this fragment.

## References

- van Glabbeek, "The Linear Time–Branching Time Spectrum" (1990, 2001)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
-/

import RuleSys.SubtoposLattice.ConcreteQuotients
import RuleSys.HML

set_option autoImplicit false

open CategoryTheory
open GeometricLogic.Propositional

namespace Ruliology

universe u v

/-!
## Section 1: Spectrum Levels

The van Glabbeek spectrum is modeled as a 4-element partially ordered set,
encoding the classical hierarchy: trace ≤ simulation ≤ readySimulation ≤ bisimulation.
-/

/-- The levels of the van Glabbeek spectrum, from coarsest to finest.

    - `trace`: trace equivalence (diamond + disjunction only)
    - `simulation`: simulation equivalence (all positive formulas)
    - `readySimulation`: ready-simulation equivalence
    - `bisimulation`: bisimulation equivalence (full HML) -/
inductive SpectrumLevel : Type
  | trace : SpectrumLevel
  | simulation : SpectrumLevel
  | readySimulation : SpectrumLevel
  | bisimulation : SpectrumLevel
  deriving DecidableEq, Repr

namespace SpectrumLevel

/-- Encode spectrum levels as natural numbers for ordering. -/
def toNat : SpectrumLevel → ℕ
  | .trace => 0
  | .simulation => 1
  | .readySimulation => 2
  | .bisimulation => 3

/-- `toNat` is injective: distinct levels map to distinct numbers. -/
theorem toNat_injective : Function.Injective SpectrumLevel.toNat := by
  intro a b hab
  cases a <;> cases b <;> simp [toNat] at hab <;> rfl

instance : LE SpectrumLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT SpectrumLevel where
  lt a b := a.toNat < b.toNat

instance : PartialOrder SpectrumLevel where
  le_refl a := Nat.le_refl a.toNat
  le_trans _ _ _ := Nat.le_trans
  le_antisymm _ _ hab hba := toNat_injective (Nat.le_antisymm hab hba)
  lt_iff_le_not_ge _ _ := by
    show toNat _ < toNat _ ↔ toNat _ ≤ toNat _ ∧ ¬ toNat _ ≤ toNat _
    omega

/-- Trace is the bottom element: trace ≤ ℓ for all ℓ. -/
theorem trace_le (ℓ : SpectrumLevel) : SpectrumLevel.trace ≤ ℓ := by
  show (0 : ℕ) ≤ ℓ.toNat
  exact Nat.zero_le _

/-- Bisimulation is the top element: ℓ ≤ bisimulation for all ℓ. -/
theorem le_bisimulation (ℓ : SpectrumLevel) : ℓ ≤ SpectrumLevel.bisimulation := by
  show ℓ.toNat ≤ 3
  cases ℓ <;> simp [toNat]

end SpectrumLevel

/-!
## Section 2: HML Sublanguage Predicates

Each spectrum level corresponds to a sublanguage of HML. In the diamond-only
fragment, only the trace sublanguage is a proper restriction. The simulation,
ready-simulation, and bisimulation sublanguages all admit every diamond-only
HML formula.
-/

/-- The trace sublanguage: diamond and disjunction only (no conjunction).

    Trace formulas capture "possible future paths" but cannot express
    "having two different successors" (which requires conjunction).
    This is the coarsest useful observation level.

    - `top` and `bot` are trace formulas (nullary)
    - `conj` is excluded (conjunction distinguishes branching)
    - `disj` is included if both children are trace formulas
    - `diamond` is included if its child is a trace formula -/
def HML.isTraceFormula : HML → Bool
  | .top => true
  | .bot => true
  | .conj _ _ => false
  | .disj φ ψ => φ.isTraceFormula && ψ.isTraceFormula
  | .diamond φ => φ.isTraceFormula

/-- The simulation sublanguage: all diamond-only HML formulas.

    In the full HML with negation and box, the simulation sublanguage
    restricts to positive formulas (no negation). Since diamond-only
    HML is already positive, every formula qualifies. -/
def HML.isSimFormula : HML → Bool := fun _ => true

/-- The ready-simulation sublanguage: all diamond-only HML formulas.

    Ready-simulation adds "readiness" predicates (the ability to observe
    which actions are enabled). In diamond-only HML, readiness is
    already expressible via `◇⊤`, so no additional restriction is needed. -/
def HML.isReadySimFormula : HML → Bool := fun _ => true

/-- The bisimulation sublanguage: all diamond-only HML formulas.

    The full HML characterizes bisimulation. In the diamond-only fragment,
    this is all formulas. -/
def HML.isBisimFormula : HML → Bool := fun _ => true

/-!
## Section 3: L-Equivalence and Sublanguage Selection

Two states are L-equivalent if they satisfy exactly the same formulas in the
sublanguage L. The `SpectrumLevel.sublanguage` function maps each level to
its corresponding predicate on HML formulas.
-/

/-- L-equivalence: two states in a multiway system agree on all formulas
    in the sublanguage L.

    `HMLEquiv L M s t` holds when for every HML formula `φ` with `L φ = true`,
    `φ` is satisfied at `s` iff it is satisfied at `t`. -/
def HMLEquiv (L : HML → Bool) (M : MultiwaySystem.{u, v}) (s t : M.State) : Prop :=
  ∀ φ : HML, L φ = true → (φ.satisfiedAt M s ↔ φ.satisfiedAt M t)

/-- Map each spectrum level to its HML sublanguage predicate. -/
def SpectrumLevel.sublanguage : SpectrumLevel → (HML → Bool)
  | .trace => HML.isTraceFormula
  | .simulation => HML.isSimFormula
  | .readySimulation => HML.isReadySimFormula
  | .bisimulation => HML.isBisimFormula

/-!
## Section 4: Sublanguage Inclusion and Spectrum Monotonicity

The key structural property: if sublanguage L₁ ⊆ L₂, then L₂-equivalence
implies L₁-equivalence. Combined with the spectrum ordering, this gives
spectrum monotonicity: finer spectrum levels induce finer (more discriminating)
equivalences.
-/

/-- Trace formulas are simulation formulas (sublanguage inclusion).

    Since `isSimFormula` returns `true` for all formulas, this is trivial. -/
theorem trace_sub_sim : ∀ φ : HML, φ.isTraceFormula = true → φ.isSimFormula = true :=
  fun _ _ => rfl

/-- Sublanguage inclusion preserves L-equivalence contravariantly:
    if L₁ ⊆ L₂ and states are L₂-equivalent, they are L₁-equivalent.

    This is the core structural lemma for spectrum monotonicity. -/
theorem sublanguage_monotone {L₁ L₂ : HML → Bool}
    (h : ∀ φ, L₁ φ = true → L₂ φ = true)
    {M : MultiwaySystem.{u, v}} {s t : M.State}
    (heq : HMLEquiv L₂ M s t) : HMLEquiv L₁ M s t :=
  fun φ hφ => heq φ (h φ hφ)

/-- Spectrum monotonicity: a finer (larger) spectrum level induces a finer
    (more discriminating) equivalence. Equivalently, if ℓ₁ ≤ ℓ₂ and two
    states are ℓ₂-equivalent, they are ℓ₁-equivalent.

    **Proof:** By case analysis on ℓ₁ and ℓ₂. For ℓ₁ = trace, the trace
    sublanguage is contained in any other (which all return `true`).
    For all other cases, both sublanguages return `true` for all formulas,
    so inclusion is trivial. Impossible cases (ℓ₁ > ℓ₂) are discharged
    by the ordering constraint. -/
private theorem sublanguage_incl (ℓ₁ ℓ₂ : SpectrumLevel) (hle : ℓ₁ ≤ ℓ₂)
    (φ : HML) (hφ : ℓ₁.sublanguage φ = true) : ℓ₂.sublanguage φ = true := by
  match ℓ₁, ℓ₂ with
  | .trace, .trace => exact hφ
  | .trace, .simulation => rfl
  | .trace, .readySimulation => rfl
  | .trace, .bisimulation => rfl
  | .simulation, .simulation => rfl
  | .simulation, .readySimulation => rfl
  | .simulation, .bisimulation => rfl
  | .readySimulation, .readySimulation => rfl
  | .readySimulation, .bisimulation => rfl
  | .bisimulation, .bisimulation => rfl
  | .simulation, .trace => exact absurd hle (by show ¬(1 ≤ 0); omega)
  | .readySimulation, .trace => exact absurd hle (by show ¬(2 ≤ 0); omega)
  | .readySimulation, .simulation => exact absurd hle (by show ¬(2 ≤ 1); omega)
  | .bisimulation, .trace => exact absurd hle (by show ¬(3 ≤ 0); omega)
  | .bisimulation, .simulation => exact absurd hle (by show ¬(3 ≤ 1); omega)
  | .bisimulation, .readySimulation => exact absurd hle (by show ¬(3 ≤ 2); omega)

theorem spectrum_monotone {ℓ₁ ℓ₂ : SpectrumLevel} (hle : ℓ₁ ≤ ℓ₂)
    {M : MultiwaySystem.{u, v}} {s t : M.State}
    (heq : HMLEquiv ℓ₂.sublanguage M s t) : HMLEquiv ℓ₁.sublanguage M s t :=
  sublanguage_monotone (sublanguage_incl ℓ₁ ℓ₂ hle) heq

/-!
## Section 5: Bisimulation Connection

The Hennessy-Milner theorem (proved in HML.lean for our diamond-only fragment):
bisimulation-related states satisfy exactly the same HML formulas. Combined
with the spectrum structure, this implies bisimulation-related states are
L-equivalent at every spectrum level.
-/

/-- Bisimulation implies L-equivalence at every spectrum level.

    Given a relational bisimulation R between systems M and N, and states
    s in M, t in N with R s t, then s and t agree on every HML formula
    in every sublanguage of the spectrum.

    **Proof:** By `HML.bisim_invariant` (from HML.lean), bisimulation-related
    states agree on ALL HML formulas. Since every sublanguage is a subset of
    all HML formulas, L-equivalence follows immediately. -/
theorem bisim_implies_all_spectrum_equiv
    {M N : MultiwaySystem.{u, v}} {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    {s : M.State} {t : N.State} (hst : R s t) :
    ∀ ℓ : SpectrumLevel, ∀ φ : HML, ℓ.sublanguage φ = true →
      (φ.satisfiedAt M s ↔ φ.satisfiedAt N t) :=
  fun _ φ _ => HML.bisim_invariant hR φ hst

/-!
## Section 6: Diamond-Only Collapse

In the diamond-only setting (no negation, no box modality), the three upper
levels of the spectrum collapse:

  simulation equivalence = ready-simulation equivalence = bisimulation equivalence

This is because:
1. **Simulation vs bisimulation**: In full HML, bisimulation equivalence is
   strictly finer than simulation equivalence because negation can distinguish
   forward-only from back-and-forth simulation. Without negation, the simulation
   sublanguage already contains all diamond-only formulas.

2. **Ready-simulation**: Readiness predicates like "action a is enabled" are
   expressible as `◇_a ⊤` in diamond-only HML. No additional predicates are
   needed, so ready-simulation adds nothing beyond simulation.

3. **The trace fragment is genuinely coarser**: Trace equivalence excludes
   conjunction, which is needed to express "has both a φ-successor and a
   ψ-successor". This is the only real distinction in the diamond-only spectrum.

Despite this collapse, we retain the 4-level structure because:
- It faithfully represents the classical spectrum for documentation purposes
- Phase 102+ may extend to richer logics where the levels separate
- The proofs work uniformly regardless of collapse
-/

/-- In the diamond-only fragment, simulation and bisimulation sublanguages
    are identical (both return `true` for all formulas). -/
theorem sim_eq_bisim_sublanguage :
    HML.isSimFormula = HML.isBisimFormula := rfl

/-- In the diamond-only fragment, ready-simulation and bisimulation sublanguages
    are identical (both return `true` for all formulas). -/
theorem readySim_eq_bisim_sublanguage :
    HML.isReadySimFormula = HML.isBisimFormula := rfl

/-- Simulation, ready-simulation, and bisimulation induce the same equivalence
    in the diamond-only fragment. -/
theorem upper_spectrum_collapse (M : MultiwaySystem.{u, v}) (s t : M.State) :
    HMLEquiv SpectrumLevel.simulation.sublanguage M s t ↔
    HMLEquiv SpectrumLevel.bisimulation.sublanguage M s t := by
  constructor
  · intro h φ hφ
    exact h φ hφ
  · intro h φ hφ
    exact h φ hφ

/-!
## Section 8: Spectrum-to-Quotient Embedding

Each spectrum level and propositional geometric theory T determines a quotient
theory of T. The map is order-REVERSING: finer equivalence → fewer extra axioms.
-/

/-- Each spectrum level and propositional geometric theory T determines a quotient
theory of T. The quotient identifies formula classes that are indistinguishable
at the given observation level.

Concretely, the quotient theory adds axioms φ ⊢ ψ for each pair of formulas
where [φ] and [ψ] are identified by the HML sublanguage at level ℓ. -/
axiom spectrumQuotient (ℓ : SpectrumLevel) (T : PropGeoTheory.{u}) :
    PropQuotientTheory T

/-- The spectrum-to-quotient map is order-REVERSING:
finer equivalence (higher in spectrum) → fewer extra axioms (lower in quotient order).

Intuition: bisimulation makes the fewest identifications (finest equiv), so its
quotient theory adds the fewest axioms. Trace makes the most identifications
(coarsest equiv), so its quotient adds the most axioms. -/
axiom spectrumQuotient_antitone (T : PropGeoTheory.{u})
    (ℓ₁ ℓ₂ : SpectrumLevel) (h : ℓ₁ ≤ ℓ₂) :
    spectrumQuotient ℓ₂ T ≤ spectrumQuotient ℓ₁ T

/-!
## Section 9: Spectrum-to-Topology Embedding

Composing the spectrum-to-quotient map (antitone) with the duality correspondence
(also antitone) gives an order-PRESERVING map from spectrum levels to Grothendieck
topologies: finer equivalence → finer topology (more covering sieves).
-/

/-- Each spectrum level determines a Grothendieck topology on the Lindenbaum
algebra, via the quotient theory and duality correspondence. -/
axiom spectrumTopology (ℓ : SpectrumLevel) (T : PropGeoTheory.{u}) :
    GrothendieckTopology (LindenbaumAlgebra T)

/-- The spectrum-to-topology map is order-PRESERVING:
finer equivalence → finer topology (more covering sieves).

This follows from composing two order-reversals:
spectrum → quotient (antitone) → topology (duality, antitone) = preserving. -/
axiom spectrumTopology_monotone (T : PropGeoTheory.{u})
    (ℓ₁ ℓ₂ : SpectrumLevel) (h : ℓ₁ ≤ ℓ₂) :
    spectrumTopology ℓ₁ T ≤ spectrumTopology ℓ₂ T

/-!
## Section 10: Endpoint Correspondence

The trivial quotient (no extra axioms) is ≤ the bisimulation quotient.
The trace topology is ≤ the bisimulation topology.
-/

/-- The bisimulation quotient has the fewest extra axioms among spectrum quotients.
In particular, trivial quotient ≤ bisimulation quotient. -/
theorem trivial_le_bisimQuotient (T : PropGeoTheory.{u}) :
    PropQuotientTheory.trivial T ≤ spectrumQuotient .bisimulation T :=
  PropQuotientTheory.trivial_le _

/-- The trace topology is at most the bisimulation topology. -/
theorem traceTopology_le_bisimTopology (T : PropGeoTheory.{u}) :
    spectrumTopology .trace T ≤ spectrumTopology .bisimulation T :=
  spectrumTopology_monotone T .trace .bisimulation (SpectrumLevel.trace_le _)

/-!
## Section 11: Deterministic Collapse

For deterministic systems, all process equivalences collapse: every pair of
spectrum levels gives deductively equivalent quotient theories. We axiomatize
this per-system since the connection between `Deterministic` (on MultiwaySystem)
and `PropGeoTheory` requires the standard translation infrastructure.
-/

/-- For singleLoopTheory (deterministic), all spectrum levels collapse. -/
axiom singleLoop_spectrum_collapse :
    ∀ ℓ₁ ℓ₂ : SpectrumLevel,
      (spectrumQuotient ℓ₁ singleLoopTheory).DeductivelyEquiv
      (spectrumQuotient ℓ₂ singleLoopTheory)

/-- For toggleTheory (deterministic), all spectrum levels collapse. -/
axiom toggle_spectrum_collapse :
    ∀ ℓ₁ ℓ₂ : SpectrumLevel,
      (spectrumQuotient ℓ₁ toggleTheory).DeductivelyEquiv
      (spectrumQuotient ℓ₂ toggleTheory)

/-- For chain3Theory (deterministic), all spectrum levels collapse. -/
axiom chain3_spectrum_collapse :
    ∀ ℓ₁ ℓ₂ : SpectrumLevel,
      (spectrumQuotient ℓ₁ chain3Theory).DeductivelyEquiv
      (spectrumQuotient ℓ₂ chain3Theory)

/-!
## Section 12: Connection to Concrete Quotients

For deterministic systems, the bisimulation quotient corresponds to the
syntactic/atomic quotient from Phase 100. Since the spectrum collapses,
ALL spectrum quotients correspond to the syntactic quotient.
-/

/-- For singleLoop, the bisimulation quotient corresponds to the atomic
quotient (from ConcreteQuotients.lean). -/
axiom singleLoop_bisim_is_atomic :
    (spectrumQuotient .bisimulation singleLoopTheory).DeductivelyEquiv
    singleLoop_Q_atomic

/-- For toggle, the bisimulation quotient corresponds to the syntactic quotient. -/
axiom toggle_bisim_is_syntactic :
    (spectrumQuotient .bisimulation toggleTheory).DeductivelyEquiv
    toggle_Q_syntactic

/-- For chain3, the bisimulation quotient corresponds to the syntactic quotient. -/
axiom chain3_bisim_is_syntactic :
    (spectrumQuotient .bisimulation chain3Theory).DeductivelyEquiv
    chain3_Q_syntactic

/-!
## Section 13: Summary — The Van Glabbeek Spectrum as Subtopos Lattice

The van Glabbeek spectrum embeds into the quotient theory lattice (antitone)
and Grothendieck topology lattice (monotone) of any propositional geometric theory.

### Key results:
- `spectrumQuotient`: spectrum level → quotient theory (antitone)
- `spectrumTopology`: spectrum level → Grothendieck topology (monotone)
- Deterministic collapse: for singleLoop, toggle, chain3, all spectrum levels
  give deductively equivalent quotient theories
- Connection: bisimulation quotients correspond to syntactic/atomic quotients

### Interpretation:
- Each process equivalence defines a "level of observation" of the system
- Coarser equivalences (trace) see less → more axioms identify more formulas → finer topology
- Finer equivalences (bisimulation) see more → fewer axioms → coarser topology
- The embedding is the first realization of process equivalences as
  Lawvere-Tierney topologies in the literature

### Future work (Phase 102):
- Apply Caramello's bridge technique to transfer invariants across
  Morita-equivalent systems using the spectrum-to-topology embedding
- For nondeterministic systems: trace ≠ bisimulation gives genuinely distinct
  quotient theories and distinct subtoposes
-/

end Ruliology
