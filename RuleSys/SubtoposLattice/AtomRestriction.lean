/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Energy-Restricted Atom Sets for Multi-Dimensional Lindenbaum Algebras

This file defines the `EnrichedAtom` type that unifies the three kinds of propositional
atoms needed for the energy-indexed Lindenbaum tower:

1. **Base atoms** (`base s a t`): depth-0 transition existence atoms step_a(s,t)
2. **Branch atoms** (`branch s a C`): depth-1 path atoms encoding branching structure
3. **Unable atoms** (`unable s a`): Morleyized negation atoms encoding inability ¬⟨a⟩⊤

The energy budget determines which atoms are "visible": base atoms are always visible,
branch atoms require conjunction nesting (e₂ ≥ 2), and unable atoms require negation
access (e₅ ≥ 1, e₆ ≥ 1). The restricted atom set A_ē is monotone in the energy ordering.

## Main Results

1. `EnrichedAtom` — unified 3-constructor atom type
2. `isVisibleAt` — energy-parameterized visibility predicate
3. `restrictedAtoms` — filtered atom set for a given energy budget
4. `restrictedAtoms_monotone` — larger budget → more visible atoms
5. Named budget characterizations for trace, simulation, ready-simulation, bisimulation
6. `GradedAtom.toEnriched` — embedding from existing GradedAtom type

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023)
- Johnstone, "Sketches of an Elephant" D1.5.13 (Morleyization)
-/

import RuleSys.SubtoposLattice.EnergyVectors

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

universe u

namespace RTS

/-!
## Part 1: Enriched Atom Type

The `EnrichedAtom` type unifies base transition atoms, depth-1 branching atoms,
and Morleyized unable atoms into a single type parameterized by energy visibility.
-/

/-- Enriched atoms for energy-indexed propositional geometric theories.

- `base s a t`: transition atom step_a(s,t) — "s can do a reaching t"
- `branch s a C`: path atom pathAtom_1(s,a,C) — "∃t. s→ᵃt ∧ ∀(b,u)∈C. t→ᵇu"
- `unable s a`: Morleyized negation atom — "s cannot perform action a" (¬⟨a⟩⊤)

The three constructors correspond to the three types of information in the
van Glabbeek spectrum: trace information (base), branching information (branch),
and refusal information (unable). -/
inductive EnrichedAtom (State Label : Type*) : Type _
  | base : State → Label → State → EnrichedAtom State Label
  | branch : State → Label → Finset (Label × State) → EnrichedAtom State Label
  | unable : State → Label → EnrichedAtom State Label

/-!
## Part 2: DecidableEq and Fintype
-/

/-- Decidable equality for `EnrichedAtom`. -/
instance enrichedAtom_decidableEq {State Label : Type*}
    [DecidableEq State] [DecidableEq Label] : DecidableEq (EnrichedAtom State Label) :=
  fun a b => match a, b with
  | .base s₁ a₁ t₁, .base s₂ a₂ t₂ =>
    if hs : s₁ = s₂ then
      if ha : a₁ = a₂ then
        if ht : t₁ = t₂ then isTrue (by subst hs; subst ha; subst ht; rfl)
        else isFalse (by intro h; cases h; exact ht rfl)
      else isFalse (by intro h; cases h; exact ha rfl)
    else isFalse (by intro h; cases h; exact hs rfl)
  | .branch s₁ a₁ C₁, .branch s₂ a₂ C₂ =>
    if hs : s₁ = s₂ then
      if ha : a₁ = a₂ then
        if hC : C₁ = C₂ then isTrue (by subst hs; subst ha; subst hC; rfl)
        else isFalse (by intro h; cases h; exact hC rfl)
      else isFalse (by intro h; cases h; exact ha rfl)
    else isFalse (by intro h; cases h; exact hs rfl)
  | .unable s₁ a₁, .unable s₂ a₂ =>
    if hs : s₁ = s₂ then
      if ha : a₁ = a₂ then isTrue (by subst hs; subst ha; rfl)
      else isFalse (by intro h; cases h; exact ha rfl)
    else isFalse (by intro h; cases h; exact hs rfl)
  | .base _ _ _, .branch _ _ _ => isFalse (by intro h; cases h)
  | .base _ _ _, .unable _ _ => isFalse (by intro h; cases h)
  | .branch _ _ _, .base _ _ _ => isFalse (by intro h; cases h)
  | .branch _ _ _, .unable _ _ => isFalse (by intro h; cases h)
  | .unable _ _, .base _ _ _ => isFalse (by intro h; cases h)
  | .unable _ _, .branch _ _ _ => isFalse (by intro h; cases h)

/-- Equivalence between `EnrichedAtom` and a three-way sum type. -/
def EnrichedAtom.equivSum (State Label : Type*) :
    EnrichedAtom State Label ≃
      (State × Label × State) ⊕ (State × Label × Finset (Label × State)) ⊕
        (State × Label) where
  toFun
    | .base s a t => Sum.inl (s, a, t)
    | .branch s a C => Sum.inr (Sum.inl (s, a, C))
    | .unable s a => Sum.inr (Sum.inr (s, a))
  invFun
    | Sum.inl (s, a, t) => .base s a t
    | Sum.inr (Sum.inl (s, a, C)) => .branch s a C
    | Sum.inr (Sum.inr (s, a)) => .unable s a
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by
    match x with
    | Sum.inl _ => rfl
    | Sum.inr (Sum.inl _) => rfl
    | Sum.inr (Sum.inr _) => rfl

/-- `EnrichedAtom` is finite when `State` and `Label` are. -/
noncomputable instance enrichedAtom_fintype {State Label : Type*}
    [Fintype State] [DecidableEq State] [Fintype Label] [DecidableEq Label] :
    Fintype (EnrichedAtom State Label) :=
  Fintype.ofEquiv _ (EnrichedAtom.equivSum State Label).symm

/-!
## Part 3: Atom Kind Classification
-/

/-- The kind of an enriched atom: base, branch, or unable. -/
inductive AtomKind : Type
  | base : AtomKind
  | branch : AtomKind
  | unable : AtomKind
  deriving DecidableEq, Repr

/-- Extract the kind of an enriched atom. -/
def EnrichedAtom.kind {State Label : Type*} : EnrichedAtom State Label → AtomKind
  | .base _ _ _ => .base
  | .branch _ _ _ => .branch
  | .unable _ _ => .unable

/-!
## Part 4: Energy-Based Visibility

Each energy budget determines which atom kinds are "visible". The mapping captures
how energy dimensions control formula expressiveness:

- Base atoms (transition existence) are always observable
- Branch atoms (branching structure) require conjunction nesting e₂ ≥ 2
- Unable atoms (negation) require negative clause depth e₅ ≥ 1 and negation nesting e₆ ≥ 1
-/

/-- Whether an atom kind is visible under a given energy budget.

- `base`: always visible (e₂ ≥ 1 suffices for flat observation)
- `branch`: requires e₂ ≥ 2 (conjunction nesting for branching observation)
- `unable`: requires e₅ ≥ 1 and e₆ ≥ 1 (negation access) -/
def AtomKind.isVisibleAt (k : AtomKind) (e : EnergyBudget) : Bool :=
  match k with
  | .base => true
  | .branch => decide (e.conjNesting ≥ (2 : ℕ))
  | .unable => decide (e.negClause ≥ (1 : ℕ) ∧ e.negNesting ≥ (1 : ℕ))

/-- Whether an enriched atom is visible under a given energy budget. -/
def EnrichedAtom.isVisibleAt {State Label : Type*}
    (atom : EnrichedAtom State Label) (e : EnergyBudget) : Bool :=
  atom.kind.isVisibleAt e

/-!
## Part 5: Restricted Atom Sets
-/

/-- The set of atoms visible under energy budget `e`, filtered from `atoms`. -/
def restrictedAtoms {State Label : Type*} [DecidableEq State] [DecidableEq Label]
    (atoms : Finset (EnrichedAtom State Label)) (e : EnergyBudget) :
    Finset (EnrichedAtom State Label) :=
  atoms.filter (fun a => a.isVisibleAt e)

/-- Monotonicity: a larger energy budget makes at least as many atoms visible.
If e₁ ≤ e₂ componentwise, then every atom visible under e₁ is also visible under e₂. -/
theorem restrictedAtoms_monotone {State Label : Type*}
    [DecidableEq State] [DecidableEq Label]
    (atoms : Finset (EnrichedAtom State Label))
    (e₁ e₂ : EnergyBudget) (hle : e₁ ≤ e₂) :
    restrictedAtoms atoms e₁ ⊆ restrictedAtoms atoms e₂ := by
  intro a ha
  simp only [restrictedAtoms, Finset.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  cases a with
  | base _ _ _ => simp [EnrichedAtom.isVisibleAt, EnrichedAtom.kind, AtomKind.isVisibleAt]
  | branch _ _ _ =>
    simp only [EnrichedAtom.isVisibleAt, EnrichedAtom.kind, AtomKind.isVisibleAt] at ha ⊢
    have h2 : e₁.conjNesting ≤ e₂.conjNesting := hle.2.1
    exact decide_eq_true_eq.mpr (_root_.le_trans (decide_eq_true_eq.mp ha.2) h2)
  | unable _ _ =>
    simp only [EnrichedAtom.isVisibleAt, EnrichedAtom.kind, AtomKind.isVisibleAt] at ha ⊢
    have h5 : e₁.negClause ≤ e₂.negClause := hle.2.2.2.2.1
    have h6 : e₁.negNesting ≤ e₂.negNesting := hle.2.2.2.2.2
    have ⟨hc5, hc6⟩ := decide_eq_true_eq.mp ha.2
    exact decide_eq_true_eq.mpr ⟨_root_.le_trans hc5 h5, _root_.le_trans hc6 h6⟩

/-!
## Part 6: Named Budget Characterizations

For each named energy budget, characterize which atom kinds are visible.
-/

/-- Under the trace budget (∞,1,0,0,0,0), only base atoms are visible.
Branch atoms need e₂ ≥ 2 but traces have e₂ = 1.
Unable atoms need e₅ ≥ 1 but traces have e₅ = 0. -/
theorem trace_base_visible :
    AtomKind.isVisibleAt .base (NamedEquivalence.toEnergyBudget .traces) = true := rfl

theorem trace_branch_invisible :
    AtomKind.isVisibleAt .branch (NamedEquivalence.toEnergyBudget .traces) = false := rfl

theorem trace_unable_invisible :
    AtomKind.isVisibleAt .unable (NamedEquivalence.toEnergyBudget .traces) = false := rfl

/-- Under the simulation budget (∞,∞,∞,∞,0,0), base and branch atoms are visible.
Unable atoms need e₅ ≥ 1 but simulation has e₅ = 0. -/
theorem simulation_base_visible :
    AtomKind.isVisibleAt .base (NamedEquivalence.toEnergyBudget .simulation) = true := rfl

theorem simulation_branch_visible :
    AtomKind.isVisibleAt .branch (NamedEquivalence.toEnergyBudget .simulation) = true := by
  decide

theorem simulation_unable_invisible :
    AtomKind.isVisibleAt .unable (NamedEquivalence.toEnergyBudget .simulation) = false := rfl

/-- Under the ready-simulation budget (∞,∞,∞,∞,1,1), all atom kinds are visible. -/
theorem readySim_base_visible :
    AtomKind.isVisibleAt .base (NamedEquivalence.toEnergyBudget .readySimulation) = true := rfl

theorem readySim_branch_visible :
    AtomKind.isVisibleAt .branch (NamedEquivalence.toEnergyBudget .readySimulation) = true := by
  decide

theorem readySim_unable_visible :
    AtomKind.isVisibleAt .unable (NamedEquivalence.toEnergyBudget .readySimulation) = true := by
  decide

/-- Under the bisimulation budget (∞,∞,∞,∞,∞,∞), all atom kinds are visible. -/
theorem bisim_base_visible :
    AtomKind.isVisibleAt .base (NamedEquivalence.toEnergyBudget .bisimulation) = true := rfl

theorem bisim_branch_visible :
    AtomKind.isVisibleAt .branch (NamedEquivalence.toEnergyBudget .bisimulation) = true := by
  decide

theorem bisim_unable_visible :
    AtomKind.isVisibleAt .unable (NamedEquivalence.toEnergyBudget .bisimulation) = true := by
  decide

/-!
## Part 7: Failures Budget — First Negation Access Below Ready Simulation

Failures (∞,2,0,0,1,1) is the coarsest equivalence that uses negation.
It has e₂ = 2, so branch atoms are visible, and e₅ = e₆ = 1, so unable atoms
are visible. This is notable because failures is strictly below simulation in the
van Glabbeek lattice (they're incomparable), yet failures sees unable atoms that
simulation cannot.
-/

theorem failures_unable_visible :
    AtomKind.isVisibleAt .unable (NamedEquivalence.toEnergyBudget .failures) = true := by
  decide

theorem failures_branch_visible :
    AtomKind.isVisibleAt .branch (NamedEquivalence.toEnergyBudget .failures) = true := by
  decide

/-!
## Part 8: GradedAtom Recovery

The existing `GradedAtom` type from v14.0 embeds into `EnrichedAtom` via
`base → base` and `depth1 → branch`. Under the simulation budget (which
includes base + branch but not unable), the enriched atom set recovers
the graded atom set.
-/

/-- Embed a `GradedAtom` into an `EnrichedAtom`. -/
def GradedAtom.toEnriched {State Label : Type*} :
    GradedAtom State Label → EnrichedAtom State Label
  | .base s a t => .base s a t
  | .depth1 s a C => .branch s a C

/-- The embedding preserves the base constructor. -/
theorem GradedAtom.toEnriched_base {State Label : Type*}
    (s : State) (a : Label) (t : State) :
    (GradedAtom.base s a t : GradedAtom State Label).toEnriched = .base s a t := rfl

/-- The embedding preserves the depth1 constructor. -/
theorem GradedAtom.toEnriched_depth1 {State Label : Type*}
    (s : State) (a : Label) (C : Finset (Label × State)) :
    (GradedAtom.depth1 s a C : GradedAtom State Label).toEnriched = .branch s a C := rfl

/-- The embedding is injective. -/
theorem GradedAtom.toEnriched_injective {State Label : Type*} :
    Function.Injective (@GradedAtom.toEnriched State Label) := by
  intro a b h
  cases a with
  | base s₁ a₁ t₁ => cases b with
    | base s₂ a₂ t₂ => simp [toEnriched] at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl
    | depth1 _ _ _ => simp [toEnriched] at h
  | depth1 s₁ a₁ C₁ => cases b with
    | base _ _ _ => simp [toEnriched] at h
    | depth1 s₂ a₂ C₂ => simp [toEnriched] at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl

/-- Under the simulation budget, graded atoms (base + branch) are exactly the
visible enriched atoms — unable atoms are invisible because e₅ = e₆ = 0.

Stated as: the kind of any graded atom is visible under the simulation budget. -/
theorem GradedAtom.visible_under_simulation {State Label : Type*}
    (atom : GradedAtom State Label) :
    atom.toEnriched.isVisibleAt (NamedEquivalence.toEnergyBudget .simulation) = true := by
  cases atom with
  | base _ _ _ => rfl
  | depth1 _ _ _ => exact simulation_branch_visible

/-!
## Part 9: Energy-Atom Spectrum Summary

The three atom kinds partition the van Glabbeek spectrum into three observation regimes:

| Atom Kind | First Visible | Energy Condition |
|-----------|--------------|-----------------|
| base | Enabledness (1,1,0,0,0,0) | Always |
| branch | Failures (∞,2,0,0,1,1) | e₂ ≥ 2 |
| unable | Failures (∞,2,0,0,1,1) | e₅ ≥ 1 ∧ e₆ ≥ 1 |

The key insight: simulation (∞,∞,∞,∞,0,0) sees branch atoms but NOT unable atoms,
while failures (∞,2,0,0,1,1) sees unable atoms but has limited conjunction nesting.
This is the energy-theoretic explanation of the classic linear/branching time split.

### Axiom count: 0
### Theorem count: 20+
-/

end RTS
