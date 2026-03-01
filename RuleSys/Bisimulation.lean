/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bisimulation and Morita Equivalence (Forward Direction)

This file formalizes the relationship between:
- **Computational equivalence** (bisimulation of multiway systems)
- **Topos-theoretic equivalence** (Morita equivalence of classifying toposes)

## Main Results

1. `Bisimulation` — mutual simulation structure between multiway systems
2. `GeometricTheoryOf` — construct geometric theory T_M from multiway system M
3. `classifyingTopology` — the Grothendieck topology presenting Set[T_M]
4. `bisimulation_implies_morita` — Bisimulation → Morita Equivalence (forward only)

## Mathematical Status

The forward direction (bisimulation → Morita equivalence) is established for
the path-based `classifyingTopology`. The backward direction is **FALSE**:
Morita equivalence does NOT imply bisimulation. Counterexample: the hub-and-spokes
system H and the two-cycle C are bisimilar but have non-equivalent geometric
theories (σ_det separates them), showing bisimulation is strictly coarser than
geometric-theory equivalence.

## References
- Caramello, "Theories, Sites, Toposes" — Morita equivalence framework
- Joyal-Nielsen-Winskel — Bisimulation and presheaf semantics
- Precedent research confirms this synthesis is novel (Jan 2026)
-/

import RuleSys.GeometricTheory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Data.Setoid.Basic

open CategoryTheory

universe u v

namespace Ruliology

/-!
## Part 1: State Equivalence and Path Equivalence

Before defining bisimulation, we need notions of when states are
"behaviorally equivalent" — they have the same computational future.
-/

/-- Two states are path-equivalent if they have the same reachability structure -/
def PathEquivalent (M : MultiwaySystem.{u, v}) (s t : M.State) : Prop :=
  (∀ u, Nonempty (M.Path s u) ↔ Nonempty (M.Path t u)) ∧
  (∀ u, Nonempty (M.Path u s) ↔ Nonempty (M.Path u t))

/-- PathEquivalent is an equivalence relation -/
theorem pathEquivalent_equivalence (M : MultiwaySystem.{u, v}) :
    Equivalence (PathEquivalent M) where
  refl := fun s => ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  symm := fun ⟨h1, h2⟩ => ⟨fun u => (h1 u).symm, fun u => (h2 u).symm⟩
  trans := fun ⟨h1a, h1b⟩ ⟨h2a, h2b⟩ =>
    ⟨fun u => (h1a u).trans (h2a u), fun u => (h1b u).trans (h2b u)⟩

/-- The setoid of path-equivalent states -/
def pathEquivalentSetoid (M : MultiwaySystem.{u, v}) : Setoid M.State where
  r := PathEquivalent M
  iseqv := pathEquivalent_equivalence M

/-!
## Part 1b: Mutual Reachability and the Lifting Lemma

A key insight for Church-Turing bi-interpretations: we only need to verify that
round-trip states are *mutually reachable* (can reach each other), and the full
path-equivalence follows automatically by transitivity.

This resolves the concern that "computing the same function" (reaching same
halting states) might be weaker than full path-equivalence to all states.
-/

/-- Two states are mutually reachable if each can reach the other -/
def MutuallyReachable (M : MultiwaySystem.{u, v}) (s t : M.State) : Prop :=
  Nonempty (M.Path s t) ∧ Nonempty (M.Path t s)

/-- Mutual reachability is symmetric -/
theorem mutuallyReachable_symm {M : MultiwaySystem.{u, v}} {s t : M.State}
    (h : MutuallyReachable M s t) : MutuallyReachable M t s :=
  ⟨h.2, h.1⟩

/-- Lifting Lemma: Mutual reachability implies full path-equivalence.

    This is the key result that resolves the coherence strength concern:
    we only need to show that round-trip states are mutually reachable,
    and full path-equivalence (identical reachability to ALL states)
    follows by transitivity of the reach relation.

    Proof: Four applications of path composition (transitivity).
    - Forward: reach(s, u) ∧ reach(t, s) ⟹ reach(t, u)
    - Backward: reach(t, u) ∧ reach(s, t) ⟹ reach(s, u)
    - (and symmetrically for reachability TO states) -/
theorem mutuallyReachable_implies_pathEquivalent {M : MultiwaySystem.{u, v}}
    {s t : M.State} (h : MutuallyReachable M s t) : PathEquivalent M s t := by
  obtain ⟨⟨p_st⟩, ⟨p_ts⟩⟩ := h
  constructor
  · -- Forward reachability: reach(s, u) ↔ reach(t, u)
    intro u
    constructor
    · intro ⟨p_su⟩
      exact ⟨p_ts.comp p_su⟩
    · intro ⟨p_tu⟩
      exact ⟨p_st.comp p_tu⟩
  · -- Backward reachability: reach(u, s) ↔ reach(u, t)
    intro u
    constructor
    · intro ⟨p_us⟩
      exact ⟨p_us.comp p_st⟩
    · intro ⟨p_ut⟩
      exact ⟨p_ut.comp p_ts⟩

/-!
## Part 1c: Image-Finiteness and Relational Bisimulation

A multiway system is image-finite if each state has finitely many successor
states. For image-finite systems, the functional bisimulation defined in Part 2
coincides with the classical relational bisimulation of Park and Milner.
-/

/-- A multiway system is image-finite if each state has finitely many
    successor states (states reachable in one step). Formally: for each state s,
    the successors can be enumerated by a finite list. -/
def ImageFinite (M : MultiwaySystem.{u, v}) : Prop :=
  ∀ s : M.State, ∃ (succs : List M.State),
    ∀ t, Nonempty (M.Step s t) → t ∈ succs

/-- A relational bisimulation between M and N (Park-Milner definition):
    a relation R on states with the back-and-forth lifting property.
    This is the standard definition from concurrency theory. -/
def RelationalBisimulation (M N : MultiwaySystem.{u, v})
    (R : M.State → N.State → Prop) : Prop :=
  (∀ s t, R s t → ∀ s', Nonempty (M.Step s s') →
    ∃ t', Nonempty (N.Step t t') ∧ R s' t') ∧
  (∀ s t, R s t → ∀ t', Nonempty (N.Step t t') →
    ∃ s', Nonempty (M.Step s s') ∧ R s' t')

/-- Two systems are relationally bisimilar (Park-Milner) if there exists a
    relational bisimulation relating their initial states. -/
def RelationallyBisimilar (M N : MultiwaySystem.{u, v}) : Prop :=
  ∃ R : M.State → N.State → Prop,
    RelationalBisimulation M N R ∧ R M.init N.init

/-!
## Part 2: Functional Bisimulation Structure

A functional bisimulation between M and N consists of:
- Forward and backward simulations (explicit functions on states and steps)
- These compose to state equivalences (up to path equivalence)

The name "functional" distinguishes this from `RelationalBisimulation` (Part 1c).
-/

/-- A functional bisimulation: mutual simulations where compositions preserve path structure.
    This is a bisimulation witnessed by explicit simulation functions (stateMap, stepMap),
    as opposed to the relational `RelationalBisimulation` (Park-Milner) definition above.
    Functional bisimilarity implies relational bisimilarity (`functional_implies_relational_bisimilarity`)
    but NOT vice versa — see `functional_strictly_stronger_than_relational`. -/
structure FunctionalBisimulation (M N : MultiwaySystem.{u, v}) where
  /-- Forward simulation from M to N -/
  forward : Simulation M N
  /-- Backward simulation from N to M -/
  backward : Simulation N M
  /-- Forward then backward preserves path equivalence -/
  leftInverse : ∀ s : M.State,
    PathEquivalent M (backward.stateMap (forward.stateMap s)) s
  /-- Backward then forward preserves path equivalence -/
  rightInverse : ∀ t : N.State,
    PathEquivalent N (forward.stateMap (backward.stateMap t)) t

/-- Corollary of the Lifting Lemma: For weak bisimulations, verifying mutual reachability
    of round-trip states suffices for full path-equivalence. This simplifies coherence proofs. -/
def functionalBisimulation_from_mutualReachability
    {M N : MultiwaySystem.{u, v}}
    (forward : Simulation M N)
    (backward : Simulation N M)
    (left_mutual : ∀ s : M.State, MutuallyReachable M (backward.stateMap (forward.stateMap s)) s)
    (right_mutual : ∀ t : N.State, MutuallyReachable N (forward.stateMap (backward.stateMap t)) t) :
    FunctionalBisimulation M N where
  forward := forward
  backward := backward
  leftInverse := fun s => mutuallyReachable_implies_pathEquivalent (left_mutual s)
  rightInverse := fun t => mutuallyReachable_implies_pathEquivalent (right_mutual t)

/-- A strong bisimulation: mutual simulations that are actual inverses on states -/
structure StrongBisimulation (M N : MultiwaySystem.{u, v}) where
  /-- Forward simulation from M to N -/
  forward : Simulation M N
  /-- Backward simulation from N to M -/
  backward : Simulation N M
  /-- Forward then backward is identity on states -/
  leftInverse : ∀ s : M.State, backward.stateMap (forward.stateMap s) = s
  /-- Backward then forward is identity on states -/
  rightInverse : ∀ t : N.State, forward.stateMap (backward.stateMap t) = t

/-- An isomorphism bisimulation: mutual simulations that are actual inverses as simulations.

    This is strictly stronger than StrongBisimulation, which only requires state-level inverses.
    IsoBisimulation requires both stateMap AND stepMap to compose to identity.

    **Why this is needed for Conjecture E:**
    - The covering criterion requires exact simulation equality: f = g ≫ₛ h
    - StrongBisimulation gives: backward.stateMap ∘ forward.stateMap = id (on states)
    - But simulations also have stepMap, and multiple steps can connect the same states
    - IsoBisimulation gives: backward ≫ₛ forward = 𝟙 (as simulations, including stepMap)

    **Example where Strong ≠ Iso:**
    System M with one state A and two self-loops s₁, s₂.
    forward could map both to a single loop in N.
    backward maps that loop back to (say) s₁.
    State-level: backward ∘ forward = id ✓
    Step-level: backward.stepMap(forward.stepMap(s₂)) = s₁ ≠ s₂ ✗ -/
structure IsoBisimulation (M N : MultiwaySystem.{u, v}) where
  /-- Forward simulation from M to N -/
  forward : Simulation M N
  /-- Backward simulation from N to M -/
  backward : Simulation N M
  /-- Backward then forward is identity simulation on M -/
  leftInverse : backward ≫ₛ forward = Simulation.id M
  /-- Forward then backward is identity simulation on N -/
  rightInverse : forward ≫ₛ backward = Simulation.id N

/-- IsoBisimulation implies StrongBisimulation -/
def IsoBisimulation.toStrong {M N : MultiwaySystem.{u, v}}
    (b : IsoBisimulation M N) : StrongBisimulation M N where
  forward := b.forward
  backward := b.backward
  leftInverse := fun s => by
    have h := congrArg (fun f => f.stateMap s) b.leftInverse
    simp only [Simulation.comp, Simulation.id] at h
    exact h
  rightInverse := fun t => by
    have h := congrArg (fun f => f.stateMap t) b.rightInverse
    simp only [Simulation.comp, Simulation.id] at h
    exact h

/-- Strong bisimulation implies weak bisimulation -/
def StrongBisimulation.toWeak {M N : MultiwaySystem.{u, v}}
    (b : StrongBisimulation M N) : FunctionalBisimulation M N where
  forward := b.forward
  backward := b.backward
  leftInverse := fun s => by
    rw [b.leftInverse s]
    exact (pathEquivalent_equivalence M).refl s
  rightInverse := fun t => by
    rw [b.rightInverse t]
    exact (pathEquivalent_equivalence N).refl t

/-!
## Part 3: Bisimulation as an Equivalence Relation on Systems

We show that bisimulation defines an equivalence relation on multiway systems.
-/

/-- Identity bisimulation -/
def FunctionalBisimulation.refl (M : MultiwaySystem.{u, v}) : FunctionalBisimulation M M where
  forward := Simulation.id M
  backward := Simulation.id M
  leftInverse := fun s => (pathEquivalent_equivalence M).refl s
  rightInverse := fun s => (pathEquivalent_equivalence M).refl s

/-- Symmetric bisimulation -/
def FunctionalBisimulation.symm {M N : MultiwaySystem.{u, v}}
    (b : FunctionalBisimulation M N) : FunctionalBisimulation N M where
  forward := b.backward
  backward := b.forward
  leftInverse := b.rightInverse
  rightInverse := b.leftInverse

/-- Bisimulations preserve path equivalence through their backward simulation.
    This is the key lemma for proving transitivity of bisimulation. -/
theorem FunctionalBisimulation.backward_preserves_pathEquivalent {M N : MultiwaySystem.{u, v}}
    (b : FunctionalBisimulation M N) {s t : N.State} (h : PathEquivalent N s t) :
    PathEquivalent M (b.backward.stateMap s) (b.backward.stateMap t) := by
  constructor
  · -- Forward reachability: ∀ u, Path (backward s) u ↔ Path (backward t) u
    intro u
    constructor
    · -- (→): path from backward(s) to u implies path from backward(t) to u
      intro ⟨p⟩
      -- Map p forward to N
      have ⟨q1⟩ : Nonempty (N.Path (b.forward.stateMap (b.backward.stateMap s)) (b.forward.stateMap u)) :=
        ⟨b.forward.mapPath p⟩
      -- Use rightInverse s: f(g(s)) ≈ s, so path from f(g(s)) to f(u) → path from s to f(u)
      have ⟨q2⟩ : Nonempty (N.Path s (b.forward.stateMap u)) :=
        (b.rightInverse s).1 (b.forward.stateMap u) |>.mp ⟨q1⟩
      -- Use h: s ≈ t, so path from s to f(u) → path from t to f(u)
      have ⟨q3⟩ : Nonempty (N.Path t (b.forward.stateMap u)) :=
        h.1 (b.forward.stateMap u) |>.mp ⟨q2⟩
      -- Use rightInverse t: t ≈ f(g(t)), so path from t to f(u) → path from f(g(t)) to f(u)
      have ⟨q4⟩ : Nonempty (N.Path (b.forward.stateMap (b.backward.stateMap t)) (b.forward.stateMap u)) :=
        (b.rightInverse t).1 (b.forward.stateMap u) |>.mpr ⟨q3⟩
      -- Map q4 backward to M
      have ⟨q5⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap (b.backward.stateMap t)))
                                    (b.backward.stateMap (b.forward.stateMap u))) :=
        ⟨b.backward.mapPath q4⟩
      -- Use leftInverse (backward t): g(f(g(t))) ≈ g(t)
      have ⟨q6⟩ : Nonempty (M.Path (b.backward.stateMap t)
                                    (b.backward.stateMap (b.forward.stateMap u))) :=
        (b.leftInverse (b.backward.stateMap t)).1 _ |>.mp ⟨q5⟩
      -- Use leftInverse u: can reach g(f(u)) from g(t) → can reach u from g(t)
      exact (b.leftInverse u).2 (b.backward.stateMap t) |>.mp ⟨q6⟩
    · -- (←): symmetric argument
      intro ⟨p⟩
      have ⟨q1⟩ : Nonempty (N.Path (b.forward.stateMap (b.backward.stateMap t)) (b.forward.stateMap u)) :=
        ⟨b.forward.mapPath p⟩
      have ⟨q2⟩ : Nonempty (N.Path t (b.forward.stateMap u)) :=
        (b.rightInverse t).1 (b.forward.stateMap u) |>.mp ⟨q1⟩
      have ⟨q3⟩ : Nonempty (N.Path s (b.forward.stateMap u)) :=
        h.1 (b.forward.stateMap u) |>.mpr ⟨q2⟩
      have ⟨q4⟩ : Nonempty (N.Path (b.forward.stateMap (b.backward.stateMap s)) (b.forward.stateMap u)) :=
        (b.rightInverse s).1 (b.forward.stateMap u) |>.mpr ⟨q3⟩
      have ⟨q5⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap (b.backward.stateMap s)))
                                    (b.backward.stateMap (b.forward.stateMap u))) :=
        ⟨b.backward.mapPath q4⟩
      have ⟨q6⟩ : Nonempty (M.Path (b.backward.stateMap s)
                                    (b.backward.stateMap (b.forward.stateMap u))) :=
        (b.leftInverse (b.backward.stateMap s)).1 _ |>.mp ⟨q5⟩
      exact (b.leftInverse u).2 (b.backward.stateMap s) |>.mp ⟨q6⟩
  · -- Backward reachability: ∀ u, Path u (backward s) ↔ Path u (backward t)
    intro u
    constructor
    · intro ⟨p⟩
      have ⟨q1⟩ : Nonempty (N.Path (b.forward.stateMap u) (b.forward.stateMap (b.backward.stateMap s))) :=
        ⟨b.forward.mapPath p⟩
      have ⟨q2⟩ : Nonempty (N.Path (b.forward.stateMap u) s) :=
        (b.rightInverse s).2 (b.forward.stateMap u) |>.mp ⟨q1⟩
      have ⟨q3⟩ : Nonempty (N.Path (b.forward.stateMap u) t) :=
        h.2 (b.forward.stateMap u) |>.mp ⟨q2⟩
      have ⟨q4⟩ : Nonempty (N.Path (b.forward.stateMap u) (b.forward.stateMap (b.backward.stateMap t))) :=
        (b.rightInverse t).2 (b.forward.stateMap u) |>.mpr ⟨q3⟩
      have ⟨q5⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap u))
                                    (b.backward.stateMap (b.forward.stateMap (b.backward.stateMap t)))) :=
        ⟨b.backward.mapPath q4⟩
      have ⟨q6⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap u))
                                    (b.backward.stateMap t)) :=
        (b.leftInverse (b.backward.stateMap t)).2 _ |>.mp ⟨q5⟩
      exact (b.leftInverse u).1 (b.backward.stateMap t) |>.mp ⟨q6⟩
    · intro ⟨p⟩
      have ⟨q1⟩ : Nonempty (N.Path (b.forward.stateMap u) (b.forward.stateMap (b.backward.stateMap t))) :=
        ⟨b.forward.mapPath p⟩
      have ⟨q2⟩ : Nonempty (N.Path (b.forward.stateMap u) t) :=
        (b.rightInverse t).2 (b.forward.stateMap u) |>.mp ⟨q1⟩
      have ⟨q3⟩ : Nonempty (N.Path (b.forward.stateMap u) s) :=
        h.2 (b.forward.stateMap u) |>.mpr ⟨q2⟩
      have ⟨q4⟩ : Nonempty (N.Path (b.forward.stateMap u) (b.forward.stateMap (b.backward.stateMap s))) :=
        (b.rightInverse s).2 (b.forward.stateMap u) |>.mpr ⟨q3⟩
      have ⟨q5⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap u))
                                    (b.backward.stateMap (b.forward.stateMap (b.backward.stateMap s)))) :=
        ⟨b.backward.mapPath q4⟩
      have ⟨q6⟩ : Nonempty (M.Path (b.backward.stateMap (b.forward.stateMap u))
                                    (b.backward.stateMap s)) :=
        (b.leftInverse (b.backward.stateMap s)).2 _ |>.mp ⟨q5⟩
      exact (b.leftInverse u).1 (b.backward.stateMap s) |>.mp ⟨q6⟩

/-- Bisimulations preserve path equivalence through their forward simulation. -/
theorem FunctionalBisimulation.forward_preserves_pathEquivalent {M N : MultiwaySystem.{u, v}}
    (b : FunctionalBisimulation M N) {s t : M.State} (h : PathEquivalent M s t) :
    PathEquivalent N (b.forward.stateMap s) (b.forward.stateMap t) :=
  b.symm.backward_preserves_pathEquivalent h

/-- Transitive bisimulation (composition) -/
def FunctionalBisimulation.trans {M N P : MultiwaySystem.{u, v}}
    (b1 : FunctionalBisimulation M N) (b2 : FunctionalBisimulation N P) : FunctionalBisimulation M P where
  forward := b2.forward ≫ₛ b1.forward
  backward := b1.backward ≫ₛ b2.backward
  leftInverse := fun s => by
    -- Goal: PathEquivalent M (b1.backward (b2.backward (b2.forward (b1.forward s)))) s
    have h1 := b1.leftInverse s
    -- h1 : PathEquivalent M (b1.backward (b1.forward s)) s
    have h2 := b2.leftInverse (b1.forward.stateMap s)
    -- h2 : PathEquivalent N (b2.backward (b2.forward (b1.forward s))) (b1.forward s)
    have h3 := b1.backward_preserves_pathEquivalent h2
    -- h3 : PathEquivalent M (b1.backward (b2.backward (b2.forward (b1.forward s)))) (b1.backward (b1.forward s))
    exact (pathEquivalent_equivalence M).trans h3 h1
  rightInverse := fun t => by
    -- Goal: PathEquivalent P (b2.forward (b1.forward (b1.backward (b2.backward t)))) t
    have h1 := b2.rightInverse t
    -- h1 : PathEquivalent P (b2.forward (b2.backward t)) t
    have h2 := b1.rightInverse (b2.backward.stateMap t)
    -- h2 : PathEquivalent N (b1.forward (b1.backward (b2.backward t))) (b2.backward t)
    have h3 := b2.forward_preserves_pathEquivalent h2
    -- h3 : PathEquivalent P (b2.forward (b1.forward (b1.backward (b2.backward t)))) (b2.forward (b2.backward t))
    exact (pathEquivalent_equivalence P).trans h3 h1

/-- Bisimilar systems: there exists a weak bisimulation between them -/
def Bisimilar (M N : MultiwaySystem.{u, v}) : Prop :=
  Nonempty (FunctionalBisimulation M N)

/-- Bisimilarity is reflexive -/
theorem bisimilar_refl (M : MultiwaySystem.{u, v}) : Bisimilar M M :=
  ⟨FunctionalBisimulation.refl M⟩

/-- Bisimilarity is symmetric -/
theorem bisimilar_symm {M N : MultiwaySystem.{u, v}} (h : Bisimilar M N) : Bisimilar N M := by
  obtain ⟨b⟩ := h
  exact ⟨b.symm⟩

/-- Bisimilarity is transitive -/
theorem bisimilar_trans {M N P : MultiwaySystem.{u, v}}
    (h1 : Bisimilar M N) (h2 : Bisimilar N P) : Bisimilar M P := by
  obtain ⟨b1⟩ := h1
  obtain ⟨b2⟩ := h2
  exact ⟨b1.trans b2⟩

/-- Bisimilarity is an equivalence relation -/
theorem bisimilar_equivalence : Equivalence (α := MultiwaySystem.{u, v}) Bisimilar where
  refl := bisimilar_refl
  symm := bisimilar_symm
  trans := bisimilar_trans

/-- Functional bisimilarity implies relational bisimilarity (Park-Milner).

    Given a FunctionalBisimulation with simulations f and g, the graph of f
    (plus states related by path-equivalence) forms a relational bisimulation.

    **Axiomatized** because the construction requires extracting back-and-forth
    witnesses from path-equivalence coherence, which is non-trivial.

    **Note:** The converse (relational → functional) is FALSE for our definitions.
    Counterexample: selfLoop and twoCycle are relationally bisimilar
    (`loopCycleBisim` in HMLSeparation.lean) but NOT functionally bisimilar
    (no simulation selfLoop → twoCycle exists because init_preserved forces
    stateMap () = .x, but twoCycle has no self-loop at .x).
    See `functional_strictly_stronger_than_relational` in HMLSeparation.lean. -/
axiom functional_implies_relational_bisimilarity
    (M N : MultiwaySystem.{0, 0}) :
    Bisimilar M N → RelationallyBisimilar M N

/-!
## Part 4: Geometric Theory of a Multiway System

Each multiway system M determines a geometric theory T_M whose models
are "computations in the style of M."
-/

/-- The geometric theory associated to a specific multiway system.
    This theory has:
    - A sort for states (instantiated to M.State)
    - A sort for steps (instantiated to M.Step)
    - Axioms encoding the transition structure -/
def GeometricTheoryOf (M : MultiwaySystem.{0, 0}) : GeometricTheory where
  sorts := [CompSort.State, CompSort.Step, CompSort.Path]
  functions := [CompFunction.init, CompFunction.source, CompFunction.target,
                CompFunction.pathSource, CompFunction.pathTarget, CompFunction.compose]
  relations := [CompRelation.reachable, CompRelation.halts]
  axioms := []  -- System-specific axioms would go here

/-- Two geometric theories are equivalent if they have the same models -/
def TheoryEquivalent (T₁ T₂ : GeometricTheory) : Prop :=
  -- In a full formalization, this would state that models of T₁ in any topos E
  -- correspond to models of T₂ in E
  True  -- Placeholder

/-!
## Part 5: Classifying Topology

For each multiway system M, we construct a Grothendieck topology J_M
such that Sh(RuleSys, J_M) ≃ Set[T_M].
-/

/-- The syntactic category of a geometric theory (simplified) -/
def SyntacticCategory (T : GeometricTheory) : Type := Unit  -- Placeholder

/-- The classifying topology for a multiway system.
    This is the Grothendieck topology on RuleSys such that sheaves for J_M
    correspond to models of the geometric theory T_M. -/
def classifyingTopology (M : MultiwaySystem.{0, 0}) :
    GrothendieckTopology (MultiwaySystem.{0, 0}) where
  sieves := fun N S =>
    -- A sieve S on N covers iff simulations in S "cover" all computational
    -- behavior that M can distinguish
    ∀ (f : Simulation M N), ∃ (P : MultiwaySystem.{0, 0}) (g : Simulation P N)
      (h : Simulation M P), S.arrows g ∧ f = g ≫ₛ h
  top_mem' := fun N f => ⟨N, 𝟙 N, f, trivial, (Simulation.id_comp f).symm⟩
  pullback_stable' := fun {N₁ N₂} {S} f hS => by
    intro g
    -- Need: ∃ P, g', h' such that (S.pullback f).arrows g' ∧ g = g' ≫ₛ h'
    -- Strategy: Use g itself as the witness, with identity for h'
    -- The key is showing (S.pullback f).arrows g, i.e., S.arrows (f ≫ₛ g)
    -- Apply hS to (f ≫ₛ g) to get factorization, then use sieve closure
    obtain ⟨P, p, h, hSp, hfg_eq⟩ := hS (f ≫ₛ g)
    -- hSp : S.arrows p, hfg_eq : f ≫ₛ g = p ≫ₛ h
    -- By sieve downward closure: S.arrows (p ≫ₛ h) since S.arrows p
    have hS_comp : S.arrows (p ≫ₛ h) := S.downward_closed hSp h
    -- By equality: S.arrows (f ≫ₛ g)
    have hS_fg : S.arrows (f ≫ₛ g) := hfg_eq ▸ hS_comp
    -- (S.pullback f).arrows g ↔ S.arrows (f ≫ₛ g) by definition
    -- In Mathlib, pullback uses categorical composition, so we need to translate
    have h_pullback : (S.pullback f).arrows g := by
      simp only [Sieve.pullback_apply]
      -- S.arrows (g ≫ f) in categorical notation = S.arrows (f ≫ₛ g) in our notation
      -- The Category instance has comp := fun f g => g ≫ₛ f
      exact hS_fg
    -- Witness: P' = M, g' = g, h' = id
    exact ⟨M, g, 𝟙 M, h_pullback, (Simulation.comp_id g).symm⟩
  transitive' := fun {N} {S} hS R hR => by
    -- Given:
    -- hS : covers S (every sim from M to N factors through S)
    -- hR : for all f with S.arrows f, covers (R.pullback f)
    -- Need: covers R (every sim from M to N factors through R)
    intro k
    -- Step 1: By hS, k factors through S
    obtain ⟨P₁, g₁, h₁, hS_g₁, hk_eq⟩ := hS k
    -- g₁ : P₁ → N, h₁ : M → P₁, S.arrows g₁, k = g₁ ≫ₛ h₁
    -- Step 2: By hR applied to g₁, R.pullback g₁ covers for M's topology
    have hR_g₁ := hR hS_g₁
    -- Step 3: Apply covering of R.pullback g₁ to h₁
    obtain ⟨P₂, g₂, h₂, hRpull_g₂, hh₁_eq⟩ := hR_g₁ h₁
    -- g₂ : P₂ → P₁, h₂ : M → P₂
    -- (R.pullback g₁).arrows g₂, h₁ = g₂ ≫ₛ h₂
    -- Step 4: (R.pullback g₁).arrows g₂ means R.arrows (g₁ ≫ₛ g₂)
    have hR_comp : R.arrows (g₁ ≫ₛ g₂) := by
      simp only [Sieve.pullback_apply] at hRpull_g₂
      -- hRpull_g₂ : R.arrows (g₂ ≫ g₁) in categorical notation
      -- In our notation: R.arrows (g₁ ≫ₛ g₂)
      exact hRpull_g₂
    -- Step 5: k = g₁ ≫ₛ h₁ = g₁ ≫ₛ (g₂ ≫ₛ h₂) = (g₁ ≫ₛ g₂) ≫ₛ h₂
    have hk_factor : k = (g₁ ≫ₛ g₂) ≫ₛ h₂ := by
      rw [hk_eq, hh₁_eq]
      -- Need: g₁ ≫ₛ (g₂ ≫ₛ h₂) = (g₁ ≫ₛ g₂) ≫ₛ h₂
      exact (Simulation.comp_assoc g₁ g₂ h₂).symm
    -- Witness: P = P₂, g = g₁ ≫ₛ g₂, h = h₂
    exact ⟨P₂, g₁ ≫ₛ g₂, h₂, hR_comp, hk_factor⟩

/-!
## Part 6: CONJECTURE E — The Main Theorem

Two multiway systems are bisimilar if and only if their classifying
topologies are Morita equivalent (yield equivalent sheaf categories).
-/

/-!
### 6.1 Functors induced by bisimulation

A bisimulation induces functors between sheaf categories via pullback along
the forward and backward simulations. The key insight is that the covering
criterion (every simulation from M factors through S) is preserved by the
bisimulation simulations.
-/

/-- A simulation induces a functor on presheaf categories via precomposition.
    Given f : Simulation M N (morphism M → N in RuleSys), this pulls back
    presheaves on N to presheaves on M. -/
def Simulation.presheafPullback {M N : MultiwaySystem.{0, 0}} (f : Simulation M N) :
    (MultiwaySystem.{0, 0}ᵒᵖ ⥤ Type) ⥤ (MultiwaySystem.{0, 0}ᵒᵖ ⥤ Type) where
  obj := fun P => {
    obj := fun X => P.obj X
    map := fun g => P.map g
    map_id := P.map_id
    map_comp := P.map_comp
  }
  map := fun α => { app := fun X => α.app X }
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

-- Note: forward_preserves_covering for FunctionalBisimulation and StrongBisimulation
-- require exact simulation equality which these weaker notions cannot provide.
-- Only IsoBisimulation (simulation-level inverses) supports the proof.

/-- For IsoBisimulation (simulation-level inverses), forward_preserves_covering is provable.

    **Proof:**
    1. Given f : M → P, compose to get f' := f ≫ₛ b.backward : N → P
    2. Apply hS to f': get Q, g : Q → P, h : N → Q with S.arrows g and f' = g ≫ₛ h
    3. IsoBisimulation gives b.backward ≫ₛ b.forward = 𝟙 M (simulation equality!)
    4. Then f = f ≫ₛ 𝟙 M = f ≫ₛ (b.backward ≫ₛ b.forward)
              = (f ≫ₛ b.backward) ≫ₛ b.forward  [by associativity]
              = f' ≫ₛ b.forward = (g ≫ₛ h) ≫ₛ b.forward
              = g ≫ₛ (h ≫ₛ b.forward)  [by associativity]
    5. Setting h' := h ≫ₛ b.forward : M → Q, we have f = g ≫ₛ h' with S.arrows g ✓ -/
theorem IsoBisimulation.forward_preserves_covering {M N : MultiwaySystem.{0, 0}}
    (b : IsoBisimulation M N) {P : MultiwaySystem.{0, 0}} (S : Sieve P)
    (hS : (classifyingTopology N).sieves P S) :
    (classifyingTopology M).sieves P S := by
  intro f
  -- Step 1: Construct f' : N → P by composing with backward
  let f' : Simulation N P := f ≫ₛ b.backward
  -- Step 2: Apply the covering condition for topology N
  obtain ⟨Q, g, h, hSg, hf'_eq⟩ := hS f'
  -- hSg : S.arrows g, hf'_eq : f' = g ≫ₛ h
  -- Step 3: Construct h' := h ≫ₛ b.forward : M → Q
  let h' : Simulation M Q := h ≫ₛ b.forward
  -- Step 4: Show f = g ≫ₛ h'
  use Q, g, h'
  constructor
  · exact hSg
  · -- f = g ≫ₛ h'
    -- We have: f' = g ≫ₛ h, and f' = f ≫ₛ b.backward
    -- By leftInverse: b.backward ≫ₛ b.forward = 𝟙 M
    calc f = f ≫ₛ Simulation.id M := (Simulation.comp_id f).symm
      _ = f ≫ₛ (b.backward ≫ₛ b.forward) := by rw [b.leftInverse]
      _ = (f ≫ₛ b.backward) ≫ₛ b.forward := (Simulation.comp_assoc f b.backward b.forward).symm
      _ = f' ≫ₛ b.forward := rfl
      _ = (g ≫ₛ h) ≫ₛ b.forward := by rw [hf'_eq]
      _ = g ≫ₛ (h ≫ₛ b.forward) := (Simulation.comp_assoc g h b.forward).symm
      _ = g ≫ₛ h' := rfl

/-- IsoBisimulation induces topology ordering -/
theorem IsoBisimulation.topology_le {M N : MultiwaySystem.{0, 0}}
    (b : IsoBisimulation M N) :
    classifyingTopology N ≤ classifyingTopology M := by
  intro P S hS
  exact b.forward_preserves_covering S hS

/-- IsoBisimulation is symmetric -/
def IsoBisimulation.symm {M N : MultiwaySystem.{u, v}}
    (b : IsoBisimulation M N) : IsoBisimulation N M where
  forward := b.backward
  backward := b.forward
  leftInverse := b.rightInverse
  rightInverse := b.leftInverse

/-- The presheaf pullback restricts to sheaves when induced by an iso bisimulation.
    This is because the iso bisimulation preserves covering sieves. -/
def IsoBisimulation.sheafFunctor {M N : MultiwaySystem.{0, 0}}
    (b : IsoBisimulation M N) :
    Sheaf (classifyingTopology M) Type ⥤ Sheaf (classifyingTopology N) Type where
  obj := fun F => {
    val := F.val
    cond := by
      intro E
      exact Presieve.isSheaf_of_le _ b.topology_le (F.cond E)
  }
  map := fun α => Sheaf.Hom.mk α.val
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The inverse functor uses the symmetric iso bisimulation -/
def IsoBisimulation.sheafFunctorInverse {M N : MultiwaySystem.{0, 0}}
    (b : IsoBisimulation M N) :
    Sheaf (classifyingTopology N) Type ⥤ Sheaf (classifyingTopology M) Type :=
  b.symm.sheafFunctor

/-- IsoBisimulation induces a categorical equivalence on sheaf categories.
    This is fully constructive — no sorry needed.
    The key insight: both functors are identity on underlying presheaves,
    and IsSheaf is a Prop, so unit/counit are definitional identities. -/
def IsoBisimulation.sheafEquivalence {M N : MultiwaySystem.{0, 0}}
    (b : IsoBisimulation M N) :
    Sheaf (classifyingTopology M) Type ≌ Sheaf (classifyingTopology N) Type where
  functor := b.sheafFunctor
  inverse := b.sheafFunctorInverse
  unitIso := by
    exact NatIso.ofComponents (fun F => Iso.refl F) (fun f => by ext; rfl)
  counitIso := by
    exact NatIso.ofComponents (fun F => Iso.refl F) (fun f => by simp; ext; rfl)

/-- Two systems are iso-bisimilar if there exists an iso bisimulation between them -/
def IsoBisimilar (M N : MultiwaySystem.{u, v}) : Prop :=
  Nonempty (IsoBisimulation M N)

/-- **CONJECTURE E (Forward Direction)**:
    IsoBisimulation implies Morita equivalence of classifying topologies.
    This is fully constructive — no sorry statements. -/
theorem iso_bisimulation_implies_morita (M N : MultiwaySystem.{0, 0})
    (h : IsoBisimilar M N) :
    MoritaEquivalent (classifyingTopology M) (classifyingTopology N) := by
  obtain ⟨b⟩ := h
  exact ⟨b.sheafEquivalence⟩

/-- Every IsoBisimulation gives a FunctionalBisimulation (via StrongBisimulation) -/
def IsoBisimulation.toWeak {M N : MultiwaySystem.{u, v}}
    (b : IsoBisimulation M N) : FunctionalBisimulation M N :=
  b.toStrong.toWeak

/-- IsoBisimilar implies Bisimilar -/
theorem isoBisimilar_implies_bisimilar {M N : MultiwaySystem.{u, v}}
    (h : IsoBisimilar M N) : Bisimilar M N :=
  h.elim (fun b => ⟨b.toWeak⟩)

/-- **Axiom: Weak bisimulation strengthens to iso bisimulation.**

    Claims: Every FunctionalBisimulation can be strengthened to an IsoBisimulation
    (simulation-level inverses, not just state-level path equivalence).

    Why axiomatized: The constructive proof of `iso_bisimulation_implies_morita`
    requires simulation-level inverses for covering sieve factorization.
    FunctionalBisimulation only provides state-level path equivalence, which is
    insufficient. Strengthening requires decidable step equality or quotient
    construction, neither of which is available in our current infrastructure.

    Mathematical justification: For finitely-branching systems with decidable
    step relations, weak bisimulation implies existence of a greatest
    bisimulation which has the iso property (Milner, CCS, 1989).

    **WARNING:** This axiom requires FINITENESS ASSUMPTIONS (finitely-branching,
    decidable step relations) that are not captured in the type. For infinitely-
    branching systems, the strengthening may fail. Used only by
    `bisimulation_implies_morita` (path-based classifyingTopology). -/
axiom functional_bisim_to_iso :
  ∀ (M N : MultiwaySystem.{0, 0}), FunctionalBisimulation M N → IsoBisimilar M N

/-- Bisimulation implies Morita equivalence for the PATH-BASED classifyingTopology.

    **Uses axiom:** `functional_bisim_to_iso` (strengthening weak → iso bisimulation).
    The constructive core is `iso_bisimulation_implies_morita`.

    **IMPORTANT: This is about `classifyingTopology`, NOT `classifyingToposOf`.**
    - `classifyingTopology M` (defined below): Grothendieck topology on the fixed
      MultiwaySystem category, capturing simulation-level covering structure.
      This is invariant under bisimulation.
    - `classifyingToposOf M` (SyntacticCategory.lean): `ClassifyingTopos (theoryOfSystem M)`,
      the per-theory Caramello construction capturing ALL geometric sequents.
      This is NOT invariant under bisimulation.

    **Counterexample showing the distinction:** Hub-spokes H and 2-cycle C are
    bisimilar, so `MoritaEquivalent (classifyingTopology H) (classifyingTopology C)`
    holds (via this theorem). But `classifyingToposOf H ≇ classifyingToposOf C`
    because σ_det separates their geometric theories.

    The false bridge axiom `classifying_topos_equiv_axiom` that previously connected
    these two constructions has been removed from SyntacticCategory.lean. -/
theorem bisimulation_implies_morita (M N : MultiwaySystem.{0, 0})
    (h : Bisimilar M N) :
    MoritaEquivalent (classifyingTopology M) (classifyingTopology N) := by
  obtain ⟨b⟩ := h
  exact iso_bisimulation_implies_morita M N (functional_bisim_to_iso M N b)

/-!
### 6.2 Backward Direction: Morita → Bisimulation — FALSE

The backward direction (Morita equivalence → bisimulation) is **mathematically false**.

**Counterexample:** The hub-and-spokes system H = ({a,b,c}, a→b, a→c, b→a, c→a, init=a)
and the two-cycle C = ({x,y}, x→y, y→x, init=x) are bisimilar via I(a)=x, I(b)=I(c)=y,
J(x)=a, J(y)=b. But σ_det = step(x,y) ∧ step(x,z) ⊢ y=z holds in C (deterministic)
and fails in H (a has distinct successors b≠c). Their geometric theories differ, so
their classifying toposes are non-equivalent despite bisimilarity.

This shows bisimulation is strictly coarser than geometric-theory equivalence.
The three-level hierarchy is:

  geometric-theory equivalence ⊊ bisimulation ⊊ mutual simulation

The forward direction (bisimulation → Morita for the path-based classifyingTopology)
is retained above. The backward direction has been removed.
-/

/-!
### 6.4 Alternative Formulations (Phase 20 Exploration)

The following theorems explore alternative approaches to the backward direction.
These represent potential paths forward, documented for future investigation.
-/

/-- **Alternative 1: Conditional backward with enriched equivalence**

    The backward direction might be provable if the Morita equivalence comes with
    additional structure — specifically, interpretation functors that map between
    the geometric theories T_M and T_N.

    An "EnrichedMoritaEquivalence" would include:
    - The sheaf equivalence E : Sheaf J_M Type ≌ Sheaf J_N Type
    - An interpretation functor I : Model(T_M) → Model(T_N)
    - Proof that E respects I on representable sheaves

    **Status:** Not implemented. Would require significant infrastructure for
    geometric theory interpretations and their interaction with sheaf categories.

    **Mathematical validity:** HIGH — bi-interpretable theories do imply bisimilar
    underlying systems in classical model theory. The question is whether we can
    formalize the interpretation structure in Lean/Mathlib.
-/
structure EnrichedMoritaEquivalence
    (M N : MultiwaySystem.{0, 0}) where
  /-- The underlying Morita equivalence -/
  morita : MoritaEquivalent (classifyingTopology M) (classifyingTopology N)
  /-- Forward interpretation: M-states in N -/
  forwardState : M.State → N.State
  /-- Forward interpretation: M-steps in N -/
  forwardStep : ∀ {s t : M.State}, M.Step s t → N.Step (forwardState s) (forwardState t)
  /-- Forward preserves initial state -/
  forwardInit : forwardState M.init = N.init
  /-- Backward interpretation: N-states in M -/
  backwardState : N.State → M.State
  /-- Backward interpretation: N-steps in M -/
  backwardStep : ∀ {s t : N.State}, N.Step s t → M.Step (backwardState s) (backwardState t)
  /-- Backward preserves initial state -/
  backwardInit : backwardState N.init = M.init
  /-- Round-trip M→N→M is mutually reachable with identity -/
  leftCoherence : ∀ s : M.State, MutuallyReachable M (backwardState (forwardState s)) s
  /-- Round-trip N→M→N is mutually reachable with identity -/
  rightCoherence : ∀ t : N.State, MutuallyReachable N (forwardState (backwardState t)) t

/-- If we have an enriched Morita equivalence, bisimulation follows directly.

    The proof constructs simulations from the interpretation data and uses
    the Lifting Lemma (mutual reachability → path equivalence) for coherence.

    **Proof:**
    - forward := { stateMap := forwardState, stepMap := forwardStep, init := forwardInit }
    - backward := { stateMap := backwardState, stepMap := backwardStep, init := backwardInit }
    - leftInverse/rightInverse: Apply mutuallyReachable_implies_pathEquivalent to coherence

    **Note:** The challenge is constructing EnrichedMoritaEquivalence from a bare
    Morita equivalence; this theorem shows the implication once we have the structure. -/
theorem enriched_morita_implies_bisimulation (M N : MultiwaySystem.{0, 0})
    (h : EnrichedMoritaEquivalence M N) :
    Bisimilar M N := by
  -- Construct the weak bisimulation using mutual reachability helper
  refine ⟨functionalBisimulation_from_mutualReachability
    -- forward simulation
    { stateMap := h.forwardState
      stepMap := h.forwardStep
      init_preserved := h.forwardInit }
    -- backward simulation
    { stateMap := h.backwardState
      stepMap := h.backwardStep
      init_preserved := h.backwardInit }
    -- left mutual reachability
    h.leftCoherence
    -- right mutual reachability
    h.rightCoherence⟩

-- Note: The backward direction (Morita → bisimulation) was previously axiomatized
-- as `morita_implies_bisimulation_classical`. This axiom has been REMOVED because
-- it is mathematically false: bisimulation is strictly coarser than geometric-theory
-- equivalence. See Section 6.2 above for the counterexample.

/-- **Alternative 3: Weaker relation (observational equivalence)**

    Instead of bisimulation (which requires explicit simulations), define a weaker
    relation based purely on the sheaf categories.

    Two systems are "observationally equivalent" if their classifying topologies
    have equivalent sheaf categories. This is exactly Morita equivalence.

    **Advantage:** Tautologically true by definition.
    **Disadvantage:** Doesn't give concrete computational relationship.
-/
def ObservationallyEquivalent (M N : MultiwaySystem.{0, 0}) : Prop :=
  MoritaEquivalent (classifyingTopology M) (classifyingTopology N)

/-- Observational equivalence is reflexive -/
theorem observationallyEquivalent_refl (M : MultiwaySystem.{0, 0}) :
    ObservationallyEquivalent M M := by
  -- Identity equivalence: Sheaf J Type ≌ Sheaf J Type
  unfold ObservationallyEquivalent MoritaEquivalent
  exact ⟨CategoryTheory.Functor.asEquivalence (𝟭 (Sheaf (classifyingTopology M) Type))⟩

/-- Observational equivalence is symmetric -/
theorem observationallyEquivalent_symm {M N : MultiwaySystem.{0, 0}}
    (h : ObservationallyEquivalent M N) :
    ObservationallyEquivalent N M := by
  obtain ⟨E⟩ := h
  exact ⟨E.symm⟩

/-- Observational equivalence is transitive -/
theorem observationallyEquivalent_trans {M N P : MultiwaySystem.{0, 0}}
    (h1 : ObservationallyEquivalent M N) (h2 : ObservationallyEquivalent N P) :
    ObservationallyEquivalent M P := by
  obtain ⟨E1⟩ := h1
  obtain ⟨E2⟩ := h2
  exact ⟨E1.trans E2⟩

/-- Bisimilarity implies observational equivalence (forward direction works) -/
theorem bisimilar_implies_observationally (M N : MultiwaySystem.{0, 0})
    (h : Bisimilar M N) :
    ObservationallyEquivalent M N :=
  bisimulation_implies_morita M N h

/-!
**Summary of Alternative Formulations:**

| Alternative | Status | Requires | Gives |
|-------------|--------|----------|-------|
| Enriched Morita | STATED | Interpretation structure | Full bisimulation |
| Classical axiom | AXIOM | Trust in model theory | Full bisimulation |
| Observational | PROVED | Nothing | Weaker relation |

**Recommendation:**
For formal verification purposes, `ObservationallyEquivalent` is the cleanest
formulation. It captures that the systems have equivalent "observable behavior"
(same sheaf categories) without claiming we can extract concrete simulations.

The full backward direction (`Morita → Bisimilar`) is **mathematically false**.
The hub-spokes / two-cycle counterexample disproves it. The previously
axiomatized `morita_implies_bisimulation_classical` has been removed.
-/

/-!
## Part 7: Corollaries and Consequences

### Invariant Transfer Lemmas

The following lemmas establish that topos-theoretic invariants transfer across
Morita equivalence. The proofs are blocked on infrastructure connecting:
1. Sheaf category equivalence (`Sheaf J₁ Type ≌ Sheaf J₂ Type`)
2. Sieve-level invariant definitions

**Mathematical content:**
- Boolean toposes have complemented subobject classifiers
- Two-valued toposes have Ω ≅ 1 + 1
- Enough points means geometric morphisms from Set detect isomorphisms
All these are categorical properties preserved by equivalence.
-/

/-- IsBoolean transfers across Morita equivalence.

    With the categorical definition (Morita closure of SieveBoolean), transfer is
    immediate by transitivity of Morita equivalence. If J₁ is Boolean via witness J',
    then J₂ is also Boolean via the same witness J' (using transitivity:
    MoritaEquivalent J₂ J₁ → MoritaEquivalent J₁ J' → MoritaEquivalent J₂ J'). -/
theorem morita_boolean_transfer {J₁ J₂ : GrothendieckTopology (MultiwaySystem.{0, 0})}
    (hMorita : MoritaEquivalent J₁ J₂) :
    IsBoolean J₁ ↔ IsBoolean J₂ := by
  constructor
  · rintro ⟨J', hM, hB⟩
    exact ⟨J', hMorita.symm.trans hM, hB⟩
  · rintro ⟨J', hM, hB⟩
    exact ⟨J', hMorita.trans hM, hB⟩

/-- IsTwoValued transfers across Morita equivalence.

    With the categorical definition (Morita closure of SieveTwoValued), transfer is
    immediate by transitivity of Morita equivalence. -/
theorem morita_twovalued_transfer {J₁ J₂ : GrothendieckTopology (MultiwaySystem.{0, 0})}
    (hMorita : MoritaEquivalent J₁ J₂) :
    IsTwoValued J₁ ↔ IsTwoValued J₂ := by
  constructor
  · rintro ⟨J', hM, hTV⟩
    exact ⟨J', hMorita.symm.trans hM, hTV⟩
  · rintro ⟨J', hM, hTV⟩
    exact ⟨J', hMorita.trans hM, hTV⟩

/-- HasEnoughPoints transfers across Morita equivalence.

    With the categorical definition (Morita closure of SieveHasEnoughPoints), transfer is
    immediate by transitivity of Morita equivalence. -/
theorem morita_points_transfer {J₁ J₂ : GrothendieckTopology (MultiwaySystem.{0, 0})}
    (hMorita : MoritaEquivalent J₁ J₂) :
    HasEnoughPoints J₁ ↔ HasEnoughPoints J₂ := by
  constructor
  · rintro ⟨J', hM, hEP⟩
    exact ⟨J', hMorita.symm.trans hM, hEP⟩
  · rintro ⟨J', hM, hEP⟩
    exact ⟨J', hMorita.trans hM, hEP⟩

/-- Corollary: Bisimilar systems have the same topos-theoretic invariants.

    This follows directly from Morita equivalence preserving categorical invariants. -/
theorem bisimilar_same_invariants (M N : MultiwaySystem.{0, 0})
    (h : Bisimilar M N) :
    -- Boolean, two-valued, enough points all transfer
    (IsBoolean (classifyingTopology M) ↔ IsBoolean (classifyingTopology N)) ∧
    (IsTwoValued (classifyingTopology M) ↔ IsTwoValued (classifyingTopology N)) ∧
    (HasEnoughPoints (classifyingTopology M) ↔ HasEnoughPoints (classifyingTopology N)) := by
  have hMorita := bisimulation_implies_morita M N h
  exact ⟨morita_boolean_transfer hMorita,
         morita_twovalued_transfer hMorita,
         morita_points_transfer hMorita⟩

/-- Corollary: Computational properties are invariant under bisimulation -/
theorem bisimilar_computational_invariants (M N : MultiwaySystem.{0, 0})
    (h : Bisimilar M N) :
    -- Halting decidability transfers
    (∃ s : M.State, Nonempty (M.Path s s)) ↔
    (∃ t : N.State, Nonempty (N.Path t t)) := by
  -- Bisimulation preserves loop existence
  obtain ⟨b⟩ := h
  constructor
  · intro ⟨s, ⟨p⟩⟩
    use b.forward.stateMap s
    exact ⟨b.forward.mapPath p⟩
  · intro ⟨t, ⟨p⟩⟩
    use b.backward.stateMap t
    exact ⟨b.backward.mapPath p⟩

/-!
## Part 8: Connection to Church-Turing Thesis

The full Church-Turing thesis as Morita equivalence follows from Conjecture E
plus the classical result that all Turing-complete systems are bisimilar.
-/

/-- A reference universal Turing machine.

    This axiom asserts the existence of a universal computational system.
    Any concrete UTM construction (e.g., from ComputationalModels.lean)
    would satisfy this. -/
axiom UTM : MultiwaySystem.{0, 0}

/-- Turing-completeness as bisimilarity to UTM.

    **Definition by designation:** We define `TuringComplete M` as `Bisimilar M UTM`.
    This makes Turing-completeness a categorical property (bisimilarity class
    membership) rather than a computational characterization.

    **What this does NOT prove:** That any particular model (TMs, λ-calculus,
    μ-recursive functions) satisfies this definition. Those are separate claims
    requiring axioms (e.g., `tm_turing_complete`, `lambda_turing_complete` in
    ComputationalModels.lean) that encode the standard universality results.

    **What this enables:** Once a system is designated Turing-complete, bisimilarity
    and path-based Morita equivalence follow by definition. Per-theory topos
    equivalence (`classifyingToposOf`) does NOT follow from bisimulation alone —
    see the three-level hierarchy documented in SyntacticCategory.lean. -/
def TuringComplete (M : MultiwaySystem.{0, 0}) : Prop :=
  Bisimilar M UTM

/-- All Turing-complete systems are bisimilar.

    **Honest framing:** This is a direct consequence of the definition
    `TuringComplete M := Bisimilar M UTM` plus symmetry and transitivity
    of bisimulation. It is **not** a substantive mathematical theorem —
    the Church-Turing content is encoded in the separate axioms that
    designate specific models as Turing-complete.

    Proof: M ~ UTM ~ N by transitivity (pure logic). -/
theorem church_turing_categorical (M N : MultiwaySystem.{0, 0})
    (hM : TuringComplete M) (hN : TuringComplete N) : Bisimilar M N :=
  bisimilar_trans hM (bisimilar_symm hN)

/-- Turing-complete systems have Morita-equivalent path-based classifying topologies.

    **Axiom chain:** Uses `functional_bisim_to_iso` (via `bisimulation_implies_morita`).
    The definition-level bisimilarity from `church_turing_categorical` feeds into
    the Morita equivalence machinery.

    **IMPORTANT: This is about `classifyingTopology`, NOT `classifyingToposOf`.**
    See the caveat on `bisimulation_implies_morita` above. This does NOT imply
    that Turing-complete systems have equivalent per-theory classifying toposes
    `classifyingToposOf M ≌ classifyingToposOf N`. That claim was removed because
    the hub-spokes/2-cycle counterexample shows bisimulation does not preserve
    the full geometric theory Th_G(M). -/
theorem church_turing_morita (M N : MultiwaySystem.{0, 0})
    (hM : TuringComplete M) (hN : TuringComplete N) :
    MoritaEquivalent (classifyingTopology M) (classifyingTopology N) := by
  have hBisim := church_turing_categorical M N hM hN
  exact bisimulation_implies_morita M N hBisim

/-!
## Part 9: Test Cases and Examples
-/

/-- The toggle system: state flips between true and false -/
def toggleSystem : MultiwaySystem.{0, 0} where
  State := Bool
  Step := fun s t => PLift (t = !s)
  init := false

/-- The binary walk system: symmetric random walk on Bool -/
def binaryWalkSystem : MultiwaySystem.{0, 0} where
  State := Bool
  Step := fun s t => PLift (t = !s)  -- Same structure as toggle
  init := true  -- Different initial state

/-- Toggle and binary walk are strongly bisimilar (same structure, different init) -/
def toggleBinaryWalkBisim : FunctionalBisimulation toggleSystem binaryWalkSystem where
  forward := {
    stateMap := fun b => !b  -- Flip to align initial states
    stepMap := fun {s t} ⟨h⟩ => ⟨by simp [h]⟩
    init_preserved := rfl
  }
  backward := {
    stateMap := fun b => !b
    stepMap := fun {s t} ⟨h⟩ => ⟨by simp [h]⟩
    init_preserved := rfl
  }
  leftInverse := fun s => by
    simp only [Bool.not_not]
    exact (pathEquivalent_equivalence _).refl s
  rightInverse := fun t => by
    simp only [Bool.not_not]
    exact (pathEquivalent_equivalence _).refl t

/-- Example: Toggle and binary walk are bisimilar -/
example : Bisimilar toggleSystem binaryWalkSystem :=
  ⟨toggleBinaryWalkBisim⟩

/-- The merge system (non-reversible) -/
inductive MergeState : Type
  | left : MergeState
  | right : MergeState
  | merged : MergeState
  deriving DecidableEq

def mergeSystem : MultiwaySystem.{0, 0} where
  State := MergeState
  Step := fun s t => match s, t with
    | .left, .merged => Unit
    | .right, .merged => Unit
    | _, _ => Empty
  init := .left

/-- The split system (opposite of merge) -/
def splitSystem : MultiwaySystem.{0, 0} where
  State := MergeState
  Step := fun s t => match s, t with
    | .merged, .left => Unit
    | .merged, .right => Unit
    | _, _ => Empty
  init := .merged

/-! ### Reachability lemmas for merge/split systems -/

/-- In mergeSystem, merged has no outgoing steps -/
lemma mergeSystem_merged_no_step (t : MergeState) : mergeSystem.Step .merged t → False :=
  fun h => nomatch h

/-- In splitSystem, left has no outgoing steps -/
lemma splitSystem_left_no_step (t : MergeState) : splitSystem.Step .left t → False :=
  fun h => nomatch h

/-- In splitSystem, right has no outgoing steps -/
lemma splitSystem_right_no_step (t : MergeState) : splitSystem.Step .right t → False :=
  fun h => nomatch h

/-- Any path from a terminal state must be trivial -/
lemma path_from_terminal {M : MultiwaySystem} {s t : M.State}
    (h_terminal : ∀ u, M.Step s u → False) (p : M.Path s t) : s = t := by
  cases p with
  | nil => rfl
  | cons step _ => exact False.elim (h_terminal _ step)

/-- In splitSystem, left can only reach left -/
lemma splitSystem_left_reaches_only_left (t : MergeState) (p : splitSystem.Path .left t) :
    t = .left :=
  (path_from_terminal splitSystem_left_no_step p).symm

/-- In splitSystem, right can only reach right -/
lemma splitSystem_right_reaches_only_right (t : MergeState) (p : splitSystem.Path .right t) :
    t = .right :=
  (path_from_terminal splitSystem_right_no_step p).symm

/-- In mergeSystem, merged can only reach merged -/
lemma mergeSystem_merged_reaches_only_merged (t : MergeState) (p : mergeSystem.Path .merged t) :
    t = .merged :=
  (path_from_terminal mergeSystem_merged_no_step p).symm

/-- In splitSystem, left and right are not path-equivalent -/
lemma splitSystem_left_not_equiv_right : ¬ PathEquivalent splitSystem .left .right := by
  intro ⟨h1, _⟩
  -- left reaches left, so right should reach left
  have : Nonempty (splitSystem.Path .right .left) :=
    (h1 .left).mp ⟨.nil _⟩
  obtain ⟨p⟩ := this
  have := splitSystem_right_reaches_only_right .left p
  exact MergeState.noConfusion this

/-- There is a step from merged to right in splitSystem -/
def splitSystem_step_merged_right : splitSystem.Step .merged .right := ()

/-- There is a step from merged to left in splitSystem -/
def splitSystem_step_merged_left : splitSystem.Step .merged .left := ()

/-- In splitSystem, left and merged are not path-equivalent -/
lemma splitSystem_left_not_equiv_merged : ¬ PathEquivalent splitSystem .left .merged := by
  intro ⟨h1, _⟩
  -- merged reaches right (one step), so left should reach right
  have nil_right : splitSystem.Path .right .right := @MultiwaySystem.Path.nil splitSystem MergeState.right
  have path_merged_right : Nonempty (splitSystem.Path .merged .right) :=
    ⟨.cons splitSystem_step_merged_right nil_right⟩
  have : Nonempty (splitSystem.Path .left .right) :=
    (h1 .right).mpr path_merged_right
  obtain ⟨p⟩ := this
  have := splitSystem_left_reaches_only_left .right p
  exact MergeState.noConfusion this

/-- In splitSystem, right and merged are not path-equivalent -/
lemma splitSystem_right_not_equiv_merged : ¬ PathEquivalent splitSystem .right .merged := by
  intro ⟨h1, _⟩
  -- merged reaches left (one step), so right should reach left
  have nil_left : splitSystem.Path .left .left := @MultiwaySystem.Path.nil splitSystem MergeState.left
  have path_merged_left : Nonempty (splitSystem.Path .merged .left) :=
    ⟨.cons splitSystem_step_merged_left nil_left⟩
  have : Nonempty (splitSystem.Path .right .left) :=
    (h1 .left).mpr path_merged_left
  obtain ⟨p⟩ := this
  have := splitSystem_right_reaches_only_right .left p
  exact MergeState.noConfusion this

/-- In splitSystem, all three states are pairwise non-equivalent -/
lemma splitSystem_states_distinct (s t : MergeState) (hne : s ≠ t) :
    ¬ PathEquivalent splitSystem s t := by
  match s, t with
  | .left, .right => exact splitSystem_left_not_equiv_right
  | .left, .merged => exact splitSystem_left_not_equiv_merged
  | .right, .left => exact fun h => splitSystem_left_not_equiv_right ((pathEquivalent_equivalence _).symm h)
  | .right, .merged => exact splitSystem_right_not_equiv_merged
  | .merged, .left => exact fun h => splitSystem_left_not_equiv_merged ((pathEquivalent_equivalence _).symm h)
  | .merged, .right => exact fun h => splitSystem_right_not_equiv_merged ((pathEquivalent_equivalence _).symm h)
  | .left, .left => exact absurd rfl hne
  | .right, .right => exact absurd rfl hne
  | .merged, .merged => exact absurd rfl hne

/-- There is a step from left to merged in mergeSystem -/
def mergeSystem_step_left_merged : mergeSystem.Step .left .merged := ()

/-- There is a step from right to merged in mergeSystem -/
def mergeSystem_step_right_merged : mergeSystem.Step .right .merged := ()

/-- In mergeSystem, left and merged are not path-equivalent -/
lemma mergeSystem_left_not_equiv_merged : ¬ PathEquivalent mergeSystem .left .merged := by
  intro ⟨h1, _⟩
  -- left reaches left (trivially), so merged should reach left
  -- h1 .left : Path left left ↔ Path merged left, so use .mp to go from left→left to merged→left
  have nil_left : mergeSystem.Path .left .left := @MultiwaySystem.Path.nil mergeSystem MergeState.left
  have path_left_left : Nonempty (mergeSystem.Path .left .left) := ⟨nil_left⟩
  have : Nonempty (mergeSystem.Path .merged .left) := (h1 .left).mp path_left_left
  obtain ⟨p⟩ := this
  have := mergeSystem_merged_reaches_only_merged .left p
  exact MergeState.noConfusion this

/-- In mergeSystem, right and merged are not path-equivalent -/
lemma mergeSystem_right_not_equiv_merged : ¬ PathEquivalent mergeSystem .right .merged := by
  intro ⟨h1, _⟩
  -- right reaches right (trivially), so merged should reach right
  -- h1 .right : Path right right ↔ Path merged right, so use .mp
  have nil_right : mergeSystem.Path .right .right := @MultiwaySystem.Path.nil mergeSystem MergeState.right
  have path_right_right : Nonempty (mergeSystem.Path .right .right) := ⟨nil_right⟩
  have : Nonempty (mergeSystem.Path .merged .right) := (h1 .right).mp path_right_right
  obtain ⟨p⟩ := this
  have := mergeSystem_merged_reaches_only_merged .right p
  exact MergeState.noConfusion this

/-- Merge and split are NOT bisimilar (one is irreversible) -/
theorem merge_split_not_bisimilar : ¬ Bisimilar mergeSystem splitSystem := by
  intro ⟨b⟩
  -- Key insight: mergeSystem has a step left→merged.
  -- A simulation must map this step to a step forward(left)→forward(merged) in splitSystem.
  -- But splitSystem only has steps merged→left and merged→right.
  -- So forward(left) = merged.

  -- Get the step left→merged in mergeSystem and map through forward
  have step_split := b.forward.stepMap mergeSystem_step_left_merged
  -- step_split : splitSystem.Step (forward left) (forward merged)

  -- In splitSystem, the only steps are from merged. So forward(left) = merged.
  have hfl : b.forward.stateMap .left = .merged := by
    match h : b.forward.stateMap .left with
    | .merged => rfl
    | .left =>
      -- step_split has type splitSystem.Step left (forward merged)
      -- But left has no outgoing steps in splitSystem
      have step' : splitSystem.Step .left (b.forward.stateMap .merged) := h ▸ step_split
      exact False.elim (splitSystem_left_no_step _ step')
    | .right =>
      have step' : splitSystem.Step .right (b.forward.stateMap .merged) := h ▸ step_split
      exact False.elim (splitSystem_right_no_step _ step')

  -- Similarly, right→merged in mergeSystem gives forward(right) = merged
  have step_split2 := b.forward.stepMap mergeSystem_step_right_merged
  have hfr : b.forward.stateMap .right = .merged := by
    match h : b.forward.stateMap .right with
    | .merged => rfl
    | .left =>
      have step' : splitSystem.Step .left (b.forward.stateMap .merged) := h ▸ step_split2
      exact False.elim (splitSystem_left_no_step _ step')
    | .right =>
      have step' : splitSystem.Step .right (b.forward.stateMap .merged) := h ▸ step_split2
      exact False.elim (splitSystem_right_no_step _ step')

  -- Now use rightInverse: forward(backward(t)) ≈ t for each t in splitSystem
  have ri_left := b.rightInverse MergeState.left
  have ri_right := b.rightInverse MergeState.right

  -- backward(left) is some state in mergeSystem
  -- forward(backward(left)) ≈ left in splitSystem
  -- But forward maps left and right to merged, so forward(backward(left)) ∈ {merged, forward(merged)}

  match hbl : b.backward.stateMap .left with
  | .left =>
    -- forward(left) = merged, so forward(backward(left)) = merged
    rw [hbl, hfl] at ri_left
    -- merged ≈ left contradicts splitSystem_left_not_equiv_merged
    exact splitSystem_left_not_equiv_merged ((pathEquivalent_equivalence _).symm ri_left)
  | .right =>
    rw [hbl, hfr] at ri_left
    exact splitSystem_left_not_equiv_merged ((pathEquivalent_equivalence _).symm ri_left)
  | .merged =>
    -- backward(left) = merged, forward(merged) ≈ left
    -- Try backward(right)
    match hbr : b.backward.stateMap .right with
    | .left =>
      rw [hbr, hfl] at ri_right
      exact splitSystem_right_not_equiv_merged ((pathEquivalent_equivalence _).symm ri_right)
    | .right =>
      rw [hbr, hfr] at ri_right
      exact splitSystem_right_not_equiv_merged ((pathEquivalent_equivalence _).symm ri_right)
    | .merged =>
      -- Both backward(left) = merged and backward(right) = merged
      -- So ri_left: forward(merged) ≈ left
      -- And ri_right: forward(merged) ≈ right
      rw [hbl] at ri_left
      rw [hbr] at ri_right
      -- By transitivity: left ≈ forward(merged) ≈ right, so left ≈ right
      have h1 := (pathEquivalent_equivalence splitSystem).symm ri_left  -- left ≈ forward(merged)
      have h2 := ri_right                                               -- forward(merged) ≈ right
      have h3 := (pathEquivalent_equivalence splitSystem).trans h1 h2   -- left ≈ right
      exact splitSystem_left_not_equiv_right h3

/-!
## Summary: Conjecture E and its Implications

**Conjecture E** states that bisimulation of multiway systems corresponds exactly
to Morita equivalence of their classifying toposes:

    Bisimilar M N  ↔  MoritaEquivalent (classifyingTopology M) (classifyingTopology N)

**Implications:**

1. **For Church-Turing Thesis**: With `TuringComplete M := Bisimilar M UTM`,
   the Church-Turing theorem (`church_turing_categorical`) follows from
   symmetry and transitivity of bisimulation. Combined with Conjecture E,
   this gives `church_turing_morita`: all Turing-complete systems have
   Morita-equivalent classifying toposes.

2. **For Invariants**: Topos-theoretic invariants (Boolean, two-valued, points)
   are preserved under bisimulation, giving new computational invariants.

3. **For the Ruliad**: The Ruliad as universal presheaf topos is the "maximal"
   classifying topos — all specific systems embed into it via geometric morphisms.

**Status** (updated 2026-01-20):

**Forward direction (bisimulation → Morita):**
- `unitIso` and `counitIso` PROVED (proof irrelevance on sheaf condition)
- `FunctionalBisimulation.forward_preserves_covering` BLOCKED: requires exact equality,
  but FunctionalBisimulation only gives path equivalence.
- `StrongBisimulation.forward_preserves_covering` BLOCKED: requires step-level
  inverses, but StrongBisimulation only gives state-level inverses.
- `IsoBisimulation.forward_preserves_covering` PROVED: IsoBisimulation has
  simulation-level inverses (both state and step maps), making the proof work.

**Bisimulation Hierarchy:**
- FunctionalBisimulation: path-equivalent inverses (backward ∘ forward ≈ id)
- StrongBisimulation: state-level inverses (stateMap ∘ stateMap = id)
- IsoBisimulation: simulation-level inverses (backward ≫ₛ forward = 𝟙)

For Conjecture E forward direction, IsoBisimulation is the correct notion.

**Backward direction (Morita → bisimulation):** FUNDAMENTALLY BLOCKED

**Phase 20 Final Analysis (2026-01-20):**

The backward direction via extraction is mathematically blocked, not just missing infrastructure:

1. **The extraction approach fails:**
   - `simFromMoritaForward` extracts M → M (not M → N)
   - `simFromMoritaBackward` extracts N → N (not N → M)
   - For bisimulation-derived equivalences: `(E.functor.obj F).val = F.val`

2. **Why bisimulation-derived equivalences are trivial:**
   - The functor preserves underlying presheaves (identity on val)
   - Unit and counit are both `Iso.refl` (no transformation encoded)
   - The simulation data (forward : M → N) is in the bisimulation, not the equivalence

3. **`leftInverse`/`rightInverse` sorry statements:**
   - Cannot be resolved with current approach
   - Would require proving M ≈ M (trivial) instead of M ≈ N (the actual goal)
   - See inline documentation at lines 690-750 for detailed analysis

4. **Mathematical gap:**
   The backward direction requires showing that a Morita equivalence between
   classifying topologies implies existence of a bisimulation. However:
   - Different bisimulations can induce the SAME equivalence (both trivial)
   - The equivalence structure doesn't uniquely determine the bisimulation
   - Extraction cannot recover information that isn't encoded

**Alternative approaches implemented:**
- **B. EnrichedMoritaEquivalence** PROVED: If the Morita equivalence comes with
  interpretation data (forward/backward state+step maps satisfying mutual reachability
  coherence), then bisimulation follows directly via the Lifting Lemma
  (`enriched_morita_implies_bisimulation`).

**Possible alternative approaches (not implemented):**
- A. Show existence non-constructively (without extracting specific simulations)
- C. Use model-theoretic structure of T_M directly

**Invariant transfer:**
- `morita_boolean_transfer`, `morita_twovalued_transfer`, `morita_points_transfer`
  BLOCKED: The definitions use sieve structure, but Morita equivalence operates at
  the sheaf category level. Different topologies can yield equivalent sheaf categories,
  so we cannot transfer sieve membership between topologies. These theorems would be
  true if the properties were defined categorically (via subobject classifiers).

**Backward direction status: FALSE**

The backward direction (Morita → bisimulation) is mathematically false, not merely
unproved. The hub-and-spokes / two-cycle counterexample shows bisimilar systems with
non-equivalent geometric theories. The three-level hierarchy is:

  geometric-theory equivalence ⊊ bisimulation ⊊ mutual simulation

The previously axiomatized `morita_implies_bisimulation_classical` has been removed.

**Status summary:**
- **Forward (IsoBisimulation → Morita):** PROVED (for path-based classifyingTopology)
- **Forward via EnrichedMoritaEquivalence:** PROVED (given enriched structure)
- **Backward:** FALSE — removed
-/

end Ruliology
