/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Second Separation Theorem: Bisimulation ⊋ Geometric-Theory Equivalence

Proves: ∃ M N, Bisimilar M N ∧ ¬(classifyingToposOf M ≌ classifyingToposOf N)

This separates bisimulation from classifying topos equivalence, establishing
the second level of the three-level hierarchy:

  geometric-theory equivalence ⊊ bisimulation ⊊ mutual simulation

## Systems

- **HubSpokes**: State = {a, b, c}, transitions a→b, a→c, b→a, c→a, init = a.
  Hub-and-spokes graph with hub a and spokes b, c.
- **TwoCycle**: State = {x, y}, transitions x→y, y→x, init = x.
  Simple two-cycle.

## Main Results

- `hubSpokes_twoCycle_bisimilar`: Bisimilar hubSpokes twoCycle (PROVED)
- `hubSpokes_twoCycle_topos_nonequiv`: ¬ topos equivalent (1 axiom, σ_det)
- `second_separation_theorem`: the full theorem (PROVED, 1 axiom)

The hub-spokes system is non-deterministic (a has two successors b ≠ c),
while the two-cycle is deterministic. The determinism sequent σ_det separates
their geometric theories despite bisimilarity.

## References

- NonEquivalence.lean — First separation (mutual simulation ⊋ bisimulation)
- Bisimulation.lean — Bisimulation definitions and path equivalence
-/

import RuleSys.Bisimulation
import RuleSys.GeometricLogic.SyntacticCategory
import RuleSys.GeometricLogic.Soundness

open CategoryTheory

namespace RTS

/-!
## Part 1: State Types
-/

/-- States of the hub-and-spokes system -/
inductive HubSpokeState : Type
  | a : HubSpokeState
  | b : HubSpokeState
  | c : HubSpokeState
  deriving DecidableEq

/-- States of the two-cycle system -/
inductive TwoCycleState : Type
  | x : TwoCycleState
  | y : TwoCycleState
  deriving DecidableEq

/-!
## Part 2: System Definitions
-/

/-- Hub-and-spokes system: a is the hub, b and c are spokes.
    Transitions: a→b, a→c, b→a, c→a. Initial state: a.
    This system is non-deterministic: a has two distinct successors b and c. -/
def hubSpokes : RootedTS.{0, 0} where
  State := HubSpokeState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .a, .c => Unit
    | .b, .a => Unit
    | .c, .a => Unit
    | _, _ => Empty
  init := .a

/-- Two-cycle system: x and y alternate.
    Transitions: x→y, y→x. Initial state: x.
    This system is deterministic: each state has exactly one successor. -/
def twoCycle : RootedTS.{0, 0} where
  State := TwoCycleState
  Step := fun s t => match s, t with
    | .x, .y => Unit
    | .y, .x => Unit
    | _, _ => Empty
  init := .x

/-!
## Part 2b: Image-Finiteness
-/

/-- hubSpokes is image-finite: each state has finitely many successors. -/
theorem hubSpokes_imageFinite : ImageFinite hubSpokes := by
  intro s
  match s with
  | .a =>
    exact ⟨[.b, .c], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => exact nomatch step
      | .b => simp
      | .c => simp⟩
  | .b =>
    exact ⟨[.a], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => simp
      | .b => exact nomatch step
      | .c => exact nomatch step⟩
  | .c =>
    exact ⟨[.a], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => simp
      | .b => exact nomatch step
      | .c => exact nomatch step⟩

/-- twoCycle is image-finite: each state has finitely many successors. -/
theorem twoCycle_imageFinite : ImageFinite twoCycle := by
  intro s
  match s with
  | .x =>
    exact ⟨[.y], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .x => exact nomatch step
      | .y => simp⟩
  | .y =>
    exact ⟨[.x], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .x => simp
      | .y => exact nomatch step⟩

/-!
## Part 3: Simulations (Fully Constructive)
-/

/-- Forward simulation: hubSpokes → twoCycle via I(a)=x, I(b)=y, I(c)=y.
    Steps: a→b maps to x→y, a→c maps to x→y, b→a maps to y→x, c→a maps to y→x. -/
def hubSpokes_to_twoCycle : Simulation hubSpokes twoCycle where
  stateMap := fun s => match s with
    | .a => .x
    | .b => .y
    | .c => .y
  stepMap := fun {s t} step => by
    match s, t with
    | .a, .b => exact ()
    | .a, .c => exact ()
    | .b, .a => exact ()
    | .c, .a => exact ()
    | .a, .a => exact step.elim
    | .b, .b => exact step.elim
    | .b, .c => exact step.elim
    | .c, .b => exact step.elim
    | .c, .c => exact step.elim
  init_preserved := rfl

/-- Backward simulation: twoCycle → hubSpokes via J(x)=a, J(y)=b.
    Steps: x→y maps to a→b, y→x maps to b→a. -/
def twoCycle_to_hubSpokes : Simulation twoCycle hubSpokes where
  stateMap := fun s => match s with
    | .x => .a
    | .y => .b
  stepMap := fun {s t} step => by
    match s, t with
    | .x, .y => exact ()
    | .y, .x => exact ()
    | .x, .x => exact step.elim
    | .y, .y => exact step.elim
  init_preserved := rfl

/-!
## Part 4: Explicit Paths and Path Equivalence
-/

/-- Step from b to a in hubSpokes -/
def hubSpokes_step_b_a : hubSpokes.Step HubSpokeState.b HubSpokeState.a := ()

/-- Step from a to b in hubSpokes -/
def hubSpokes_step_a_b : hubSpokes.Step HubSpokeState.a HubSpokeState.b := ()

/-- Step from c to a in hubSpokes -/
def hubSpokes_step_c_a : hubSpokes.Step HubSpokeState.c HubSpokeState.a := ()

/-- Step from a to c in hubSpokes -/
def hubSpokes_step_a_c : hubSpokes.Step HubSpokeState.a HubSpokeState.c := ()

/-- Path from b to a in hubSpokes (one step: b→a) -/
def hubSpokes_path_b_a : hubSpokes.Path HubSpokeState.b HubSpokeState.a :=
  .cons hubSpokes_step_b_a (@RootedTS.Path.nil hubSpokes HubSpokeState.a)

/-- Path from a to b in hubSpokes (one step: a→b) -/
def hubSpokes_path_a_b : hubSpokes.Path HubSpokeState.a HubSpokeState.b :=
  .cons hubSpokes_step_a_b (@RootedTS.Path.nil hubSpokes HubSpokeState.b)

/-- Path from c to a in hubSpokes (one step: c→a) -/
def hubSpokes_path_c_a : hubSpokes.Path HubSpokeState.c HubSpokeState.a :=
  .cons hubSpokes_step_c_a (@RootedTS.Path.nil hubSpokes HubSpokeState.a)

/-- Path from a to c in hubSpokes (one step: a→c) -/
def hubSpokes_path_a_c : hubSpokes.Path HubSpokeState.a HubSpokeState.c :=
  .cons hubSpokes_step_a_c (@RootedTS.Path.nil hubSpokes HubSpokeState.c)

/-- Path from b to c in hubSpokes (two steps: b→a→c) -/
def hubSpokes_path_b_c : hubSpokes.Path HubSpokeState.b HubSpokeState.c :=
  hubSpokes_path_b_a.comp hubSpokes_path_a_c

/-- Path from c to b in hubSpokes (two steps: c→a→b) -/
def hubSpokes_path_c_b : hubSpokes.Path HubSpokeState.c HubSpokeState.b :=
  hubSpokes_path_c_a.comp hubSpokes_path_a_b

/-- b and c are mutually reachable in hubSpokes -/
theorem hubSpokes_b_c_mutuallyReachable : MutuallyReachable hubSpokes HubSpokeState.b HubSpokeState.c :=
  ⟨⟨hubSpokes_path_b_c⟩, ⟨hubSpokes_path_c_b⟩⟩

/-- b and c are path-equivalent in hubSpokes -/
theorem hubSpokes_b_c_pathEquivalent : PathEquivalent hubSpokes HubSpokeState.b HubSpokeState.c :=
  mutuallyReachable_implies_pathEquivalent hubSpokes_b_c_mutuallyReachable

/-!
## Part 5: Bisimulation (Fully Constructive)

The round-trip maps are:
- J(I(a)) = J(x) = a  (identity)
- J(I(b)) = J(y) = b  (identity)
- J(I(c)) = J(y) = b  (not identity! but b ≈ c by path equivalence)
- I(J(x)) = I(a) = x  (identity)
- I(J(y)) = I(b) = y  (identity)

The left inverse needs MutuallyReachable for c (since J(I(c)) = b ≠ c),
which we proved above. The right inverse is reflexive.
-/

/-- The weak bisimulation between hubSpokes and twoCycle -/
def hubSpokes_twoCycle_bisim : FunctionalBisimulation hubSpokes twoCycle :=
  functionalBisimulation_from_mutualReachability
    hubSpokes_to_twoCycle
    twoCycle_to_hubSpokes
    -- leftInverse: J(I(s)) mutually reachable with s
    (fun s => match s with
      | HubSpokeState.a =>
        ⟨⟨@RootedTS.Path.nil hubSpokes HubSpokeState.a⟩,
         ⟨@RootedTS.Path.nil hubSpokes HubSpokeState.a⟩⟩
      | HubSpokeState.b =>
        ⟨⟨@RootedTS.Path.nil hubSpokes HubSpokeState.b⟩,
         ⟨@RootedTS.Path.nil hubSpokes HubSpokeState.b⟩⟩
      | HubSpokeState.c => -- J(I(c)) = J(y) = b, need MutuallyReachable b c
        ⟨⟨hubSpokes_path_b_c⟩, ⟨hubSpokes_path_c_b⟩⟩)
    -- rightInverse: I(J(t)) mutually reachable with t
    (fun t => match t with
      | TwoCycleState.x =>
        ⟨⟨@RootedTS.Path.nil twoCycle TwoCycleState.x⟩,
         ⟨@RootedTS.Path.nil twoCycle TwoCycleState.x⟩⟩
      | TwoCycleState.y =>
        ⟨⟨@RootedTS.Path.nil twoCycle TwoCycleState.y⟩,
         ⟨@RootedTS.Path.nil twoCycle TwoCycleState.y⟩⟩)

/-- hubSpokes and twoCycle are bisimilar -/
theorem hubSpokes_twoCycle_bisimilar : Bisimilar hubSpokes twoCycle :=
  ⟨hubSpokes_twoCycle_bisim⟩

/-!
## Part 6: Topos Non-Equivalence
-/

/-- T_twoCycle proves σ_det.
    Proof: the canonical model of twoCycle satisfies σ_det (each state has
    exactly one successor: x→y and y→x), so by completeness the theory proves it. -/
theorem twoCycle_proves_sigma_det :
    GeometricLogic.Provable (GeometricLogic.theoryOfSystem twoCycle) GeometricLogic.sigma_det :=
  GeometricLogic.theoryOfSystem_complete_canonical twoCycle _ <|
    (GeometricLogic.satisfiesSequent'_sigma_det_iff _).mpr fun x y z ⟨s1⟩ ⟨s2⟩ =>
      match x, y, s1, z, s2 with
      | .x, .y, _, .y, _ => rfl
      | .y, .x, _, .x, _ => rfl

/-- hubSpokes' canonical model does not satisfy σ_det (state a has successors b ≠ c). -/
private theorem hubSpokes_not_satisfies_sigma_det :
    ¬ GeometricLogic.satisfiesSequent' (RootedTS.canonicalModel hubSpokes)
      GeometricLogic.sigma_det := by
  rw [GeometricLogic.satisfiesSequent'_sigma_det_iff]
  push_neg
  exact ⟨.a, .b, .c, ⟨()⟩, ⟨()⟩, HubSpokeState.noConfusion⟩

/-- T_hubSpokes does not prove σ_det. -/
private theorem hubSpokes_not_proves_sigma_det :
    ¬ GeometricLogic.Provable (GeometricLogic.theoryOfSystem hubSpokes) GeometricLogic.sigma_det := by
  intro h
  have hsound := GeometricLogic.Provable.sound h _
    (GeometricLogic.canonicalModel_satisfies_theorySeq hubSpokes)
  exact hubSpokes_not_satisfies_sigma_det hsound

/-- **Provability separation: hubSpokes and twoCycle have non-equivalent
    classifying toposes.**

    The determinism sequent σ_det := step(x,y) ∧ step(x,z) ⊢ y = z is provable
    in Th_G(twoCycle) (each state has exactly one successor: x→y only, y→x only)
    but not in Th_G(hubSpokes) (state a has distinct successors b and c).

    Previously axiomatized; now PROVED using generic soundness + semantic
    separation + the universal property of classifying toposes. -/
theorem hubSpokes_twoCycle_topos_nonequiv :
    ¬ Nonempty (GeometricLogic.classifyingToposOf hubSpokes ≌
                GeometricLogic.classifyingToposOf twoCycle) := by
  intro ⟨e⟩
  exact GeometricLogic.provability_separation_implies_topos_nonequiv
    twoCycle_proves_sigma_det hubSpokes_not_proves_sigma_det ⟨e.symm⟩

/-- **Second Separation Theorem**

    There exist rooted transition systems M, N such that:
    1. M and N are bisimilar (Bisimilar M N)
    2. Their classifying toposes are NOT equivalent

    This establishes: bisimulation ⊋ geometric-theory equivalence.

    Combined with the first separation theorem (mutual simulation ⊋ bisimulation),
    this gives the three-level hierarchy:

      geometric-theory equivalence ⊊ bisimulation ⊊ mutual simulation

    Parts:
    - Bisimilarity is fully proved (constructive, no axioms)
    - Topos non-equivalence uses provability separation via σ_det (1 axiom) -/
theorem second_separation_theorem :
    ∃ (M N : RootedTS.{0, 0}),
      Bisimilar M N ∧
      ¬ Nonempty (GeometricLogic.classifyingToposOf M ≌
                  GeometricLogic.classifyingToposOf N) := by
  refine ⟨hubSpokes, twoCycle, ?_, ?_⟩
  · exact hubSpokes_twoCycle_bisimilar
  · exact hubSpokes_twoCycle_topos_nonequiv

/-!
## Part 7: Section 3.3 — System Bi-Interpretation ≠ Theory Equivalence

A direct corollary of the Second Separation: system-level bi-interpretation
(≡ functional bisimulation, by Conjecture E in Interpretation.lean) does NOT
imply theory-level equivalence (classifying topos equivalence).

The hubSpokes and twoCycle systems are bisimilar (and hence bi-interpretable),
but σ_det separates their geometric theories, so their classifying toposes
are non-equivalent. This justifies the paper's claim that the functor
E[-] : Theory → Topos is NOT conservative on bi-interpretations.
-/

/-- **Section 3.3 (paper)**: System-level bi-interpretation does not imply
    classifying topos equivalence.

    Since `Bisimilar ↔ BiInterpretable` (Conjecture E, Interpretation.lean),
    this is a restatement of `second_separation_theorem` making the
    bi-interpretation connection explicit. -/
theorem biInterpretation_not_implies_topos_equiv :
    ∃ (M N : RootedTS.{0, 0}),
      -- Mutual simulation (both directions)
      (Nonempty (Simulation M N) ∧ Nonempty (Simulation N M)) ∧
      -- Functional bisimulation (≡ system bi-interpretation)
      Bisimilar M N ∧
      -- Yet classifying toposes are NOT equivalent
      ¬ Nonempty (GeometricLogic.classifyingToposOf M ≌
                  GeometricLogic.classifyingToposOf N) := by
  refine ⟨hubSpokes, twoCycle, ?_, ?_, ?_⟩
  · exact ⟨⟨hubSpokes_to_twoCycle⟩, ⟨twoCycle_to_hubSpokes⟩⟩
  · exact hubSpokes_twoCycle_bisimilar
  · exact hubSpokes_twoCycle_topos_nonequiv

end RTS
