/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quotient Bridge Theorem

Proves: Bisimilar M N → classifyingToposOf (quotientSystem M) ≌ classifyingToposOf (quotientSystem N)

Bisimulation does not preserve the raw geometric theory Th_G(M) (the Second
Separation Theorem shows hubSpokes ≈ twoCycle yet Th_G(H) ≠ Th_G(C)). However,
bisimulation DOES preserve the quotient theory: passing to the path-equivalence
quotient M/∼ collapses the branching structure that σ_det detects.

## Construction

1. `quotientSystem M`: the path-equivalence quotient of M
2. `quotientProjection M`: canonical simulation M → M/∼
3. Bisimilar systems have isomorphic quotients (strong bisimulation on quotients)
4. Strong bisimulation of quotients implies topos equivalence

## Main Results

- `quotientSystem`: construct the quotient rooted transition system
- `quotientProjection`: simulation M → quotientSystem M
- `bisimilar_implies_quotient_strongBisim`: bisimulation lifts to strong bisim on quotients
- `quotient_bridge`: bisimilar → quotient toposes equivalent

## References

- Bisimulation.lean — PathEquivalent, pathEquivalentSetoid, forward_preserves_pathEquivalent
- SecondSeparation.lean — motivating counterexample
-/

import RuleSys.Bisimulation
import RuleSys.GeometricLogic.SyntacticCategory

open CategoryTheory

namespace RTS

/-!
## Part 1: Quotient System Construction

The quotient system M/∼ collapses path-equivalent states. States are equivalence
classes [s] under PathEquivalent, and there is a step [s₁] → [s₂] iff there
exist representatives s₁' ∈ [s₁], s₂' ∈ [s₂] with a step s₁' → s₂' in M.
-/

/-- The quotient rooted transition system M/∼ where ∼ is path equivalence.

    - State: `Quotient (pathEquivalentSetoid M)` — equivalence classes of states
    - Step: `[s₁] → [s₂]` iff ∃ representatives with a step between them
    - init: `⟦M.init⟧` — the equivalence class of the initial state -/
def quotientSystem (M : RootedTS.{0, 0}) : RootedTS.{0, 0} where
  State := Quotient (pathEquivalentSetoid M)
  Step := fun q₁ q₂ =>
    PLift (∃ s₁ s₂ : M.State, ⟦s₁⟧ = q₁ ∧ ⟦s₂⟧ = q₂ ∧ Nonempty (M.Step s₁ s₂))
  init := ⟦M.init⟧

/-- The canonical projection M → M/∼ is a simulation.
    Maps each state to its equivalence class, and each step to
    the existential witness in the quotient. -/
def quotientProjection (M : RootedTS.{0, 0}) :
    Simulation M (quotientSystem M) where
  stateMap := fun s => ⟦s⟧
  stepMap := fun {s t} step => ⟨⟨s, t, rfl, rfl, ⟨step⟩⟩⟩
  init_preserved := rfl

/-!
## Part 2: Quotient Maps from Bisimulation

A weak bisimulation M ≈ N induces maps between the quotient systems M/∼ and N/∼.
The key is that simulations in a bisimulation preserve path equivalence
(proved in Bisimulation.lean as `forward_preserves_pathEquivalent`), so
the forward map descends to quotients.
-/

/-- A bisimulation's forward simulation descends to quotients.

    Given b : FunctionalBisimulation M N, the forward stateMap preserves path equivalence
    (by `forward_preserves_pathEquivalent`), so it descends to a function on quotients. -/
def bisim_quotient_map {M N : RootedTS.{0, 0}} (b : FunctionalBisimulation M N) :
    Quotient (pathEquivalentSetoid M) → Quotient (pathEquivalentSetoid N) :=
  Quotient.map b.forward.stateMap (fun _ _ h => b.forward_preserves_pathEquivalent h)

/-- A bisimulation's backward simulation descends to quotients. -/
def bisim_quotient_map_back {M N : RootedTS.{0, 0}} (b : FunctionalBisimulation M N) :
    Quotient (pathEquivalentSetoid N) → Quotient (pathEquivalentSetoid M) :=
  Quotient.map b.backward.stateMap (fun _ _ h => b.backward_preserves_pathEquivalent h)

/-- The quotient maps compose to the identity on M's quotient.

    For any s : M.State, bisim_quotient_map_back (bisim_quotient_map ⟦s⟧) = ⟦s⟧
    because b.backward(b.forward(s)) is path-equivalent to s (by leftInverse). -/
theorem bisim_quotient_left_inverse {M N : RootedTS.{0, 0}}
    (b : FunctionalBisimulation M N) (q : Quotient (pathEquivalentSetoid M)) :
    bisim_quotient_map_back b (bisim_quotient_map b q) = q := by
  induction q using Quotient.ind with
  | _ s =>
    show Quotient.mk (pathEquivalentSetoid M) (b.backward.stateMap (b.forward.stateMap s)) =
         Quotient.mk (pathEquivalentSetoid M) s
    exact Quotient.sound (b.leftInverse s)

/-- The quotient maps compose to the identity on N's quotient. -/
theorem bisim_quotient_right_inverse {M N : RootedTS.{0, 0}}
    (b : FunctionalBisimulation M N) (q : Quotient (pathEquivalentSetoid N)) :
    bisim_quotient_map b (bisim_quotient_map_back b q) = q := by
  induction q using Quotient.ind with
  | _ t =>
    show Quotient.mk (pathEquivalentSetoid N) (b.forward.stateMap (b.backward.stateMap t)) =
         Quotient.mk (pathEquivalentSetoid N) t
    exact Quotient.sound (b.rightInverse t)

/-!
## Part 3: Step Maps on Quotients

The quotient map preserves steps: if there is a step between equivalence
classes in M/∼, the forward map carries it to a step between the corresponding
classes in N/∼.
-/

/-- The quotient forward map preserves steps.

    Given a step [s₁] → [s₂] in M/∼ (witnessed by representatives s₁', s₂'
    with s₁' → s₂' in M), we apply b.forward to get
    b.forward(s₁') → b.forward(s₂') in N, which witnesses
    [b.forward(s₁')] → [b.forward(s₂')] in N/∼. -/
def bisim_quotient_stepMap {M N : RootedTS.{0, 0}} (b : FunctionalBisimulation M N)
    {q₁ q₂ : (quotientSystem M).State}
    (step : (quotientSystem M).Step q₁ q₂) :
    (quotientSystem N).Step (bisim_quotient_map b q₁) (bisim_quotient_map b q₂) := by
  constructor
  obtain ⟨s₁, s₂, hs₁, hs₂, ⟨st⟩⟩ := step.down
  subst hs₁; subst hs₂
  exact ⟨b.forward.stateMap s₁, b.forward.stateMap s₂, rfl, rfl, ⟨b.forward.stepMap st⟩⟩

/-- The quotient backward map preserves steps. -/
def bisim_quotient_stepMap_back {M N : RootedTS.{0, 0}} (b : FunctionalBisimulation M N)
    {q₁ q₂ : (quotientSystem N).State}
    (step : (quotientSystem N).Step q₁ q₂) :
    (quotientSystem M).Step (bisim_quotient_map_back b q₁) (bisim_quotient_map_back b q₂) := by
  constructor
  obtain ⟨t₁, t₂, ht₁, ht₂, ⟨st⟩⟩ := step.down
  subst ht₁; subst ht₂
  exact ⟨b.backward.stateMap t₁, b.backward.stateMap t₂, rfl, rfl, ⟨b.backward.stepMap st⟩⟩

/-!
## Part 4: Strong Bisimulation of Quotients

The quotient maps form a StrongBisimulation (state-level inverses, not just
path-equivalence). This is because the quotient maps are actual inverses on
the quotient state types (proved in Part 2).
-/

/-- A weak bisimulation induces a strong bisimulation on quotient systems.

    The forward and backward quotient maps are actual inverses on states
    (not just path-equivalent), so the quotient bisimulation is strong. -/
def bisimilar_implies_quotient_strongBisim {M N : RootedTS.{0, 0}}
    (b : FunctionalBisimulation M N) :
    StrongBisimulation (quotientSystem M) (quotientSystem N) where
  forward := {
    stateMap := bisim_quotient_map b
    stepMap := bisim_quotient_stepMap b
    init_preserved := by
      show bisim_quotient_map b (⟦M.init⟧ : Quotient (pathEquivalentSetoid M)) =
           (⟦N.init⟧ : Quotient (pathEquivalentSetoid N))
      simp only [bisim_quotient_map, Quotient.map_mk, b.forward.init_preserved]
  }
  backward := {
    stateMap := bisim_quotient_map_back b
    stepMap := bisim_quotient_stepMap_back b
    init_preserved := by
      show bisim_quotient_map_back b (⟦N.init⟧ : Quotient (pathEquivalentSetoid N)) =
           (⟦M.init⟧ : Quotient (pathEquivalentSetoid M))
      simp only [bisim_quotient_map_back, Quotient.map_mk, b.backward.init_preserved]
  }
  leftInverse := bisim_quotient_left_inverse b
  rightInverse := bisim_quotient_right_inverse b

/-!
## Part 5: Topos Equivalence from Strong Bisimulation

A strong bisimulation (state-level bijection preserving all structure) between
quotient systems lifts to an equivalence of classifying toposes. The state-level
bijection induces a syntactic category equivalence because the bijection preserves
all transition structure, hence all provable geometric sequents.
-/

/-- **Axiom: Strong bisimulation of quotient systems implies topos equivalence.**

    A StrongBisimulation between quotient systems M/∼ and N/∼ gives:
    - A state-level bijection preserving all transitions
    - Hence identical geometric theories (same provable sequents)
    - Hence equivalent classifying toposes

    **Why axiomatized:** The full proof requires showing that the state bijection
    lifts to a syntactic category equivalence preserving the topology. This needs
    the formula manipulation infrastructure that is currently axiomatized in
    SyntacticCategory.lean. The mathematical content is standard:
    isomorphic models have identical theories, hence equivalent classifying toposes.

    **Mathematical justification:** Two systems with state-level bijection
    preserving all transitions are isomorphic as rooted transition systems. Isomorphic
    systems have identical geometric theories Th_G(M) = Th_G(N) (literally
    the same provable sequents), hence identical classifying toposes. -/
axiom strongBisim_implies_topos_equiv
    (M N : RootedTS.{0, 0}) :
    StrongBisimulation M N →
    Nonempty (GeometricLogic.classifyingToposOf M ≌
              GeometricLogic.classifyingToposOf N)

/-!
## Part 6: The Quotient Bridge Theorem
-/

/-- **Quotient Bridge Theorem**

    Bisimilar rooted transition systems have equivalent quotient classifying toposes:
    if M ≈ N, then E[Th_G(M/∼)] ≃ E[Th_G(N/∼)].

    The proof proceeds:
    1. Extract the weak bisimulation from Bisimilar M N
    2. Construct the strong bisimulation on quotient systems
    3. Apply strongBisim_implies_topos_equiv

    This completes the picture: bisimulation does NOT preserve the raw
    classifying topos (Second Separation Theorem), but it DOES preserve
    the quotient classifying topos. The quotient collapses exactly the
    branching structure that σ_det detects.

    **Axiom count: 1** (strongBisim_implies_topos_equiv) -/
theorem quotient_bridge (M N : RootedTS.{0, 0}) (h : Bisimilar M N) :
    Nonempty (GeometricLogic.classifyingToposOf (quotientSystem M) ≌
              GeometricLogic.classifyingToposOf (quotientSystem N)) := by
  obtain ⟨b⟩ := h
  exact strongBisim_implies_topos_equiv
    (quotientSystem M) (quotientSystem N)
    (bisimilar_implies_quotient_strongBisim b)

end RTS
