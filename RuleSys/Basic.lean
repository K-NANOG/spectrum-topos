/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RuleSys: Category of Rooted Transition Systems

This file defines:
1. RootedTS - objects of RuleSys (state type, rewrite relation, initial state)
2. Simulation - morphisms preserving initial state and rewrite paths
3. Category instance for RuleSys with composition and identities

This forms the foundation for constructing the classifying presheaf topos.

## References
- Caramello's Relative Topos Theory
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Logic.Relation

open CategoryTheory

universe u v

namespace RTS

/-!
## Task 1 & 2: Rooted Transition System Structure

A rooted transition system is a computational structure consisting of:
- A type of states `State`
- A typed rewrite relation `Step : State → State → Type*` representing computation paths
- An initial state `init : State`

The rewrite relation is typed (not Prop-valued) to track different computational paths
between the same states, capturing the multiway nature of computation.
-/

/-- A RootedTS is the basic object of RuleSys.
    It consists of states, typed transition/rewrite relations, and an initial state.
    The typed step relation allows multiple distinct paths between states. -/
structure RootedTS where
  /-- The type of states in the system -/
  State : Type u
  /-- Typed rewrite/transition relation: `Step s t` is the type of rewrites from s to t -/
  Step : State → State → Type v
  /-- The initial/starting state -/
  init : State

namespace RootedTS

variable (M : RootedTS.{u, v})

/-- Rewrite paths in a rooted transition system: sequences of rewrites -/
inductive Path : M.State → M.State → Type (max u v)
  | nil : (s : M.State) → Path s s
  | cons : {s t u : M.State} → M.Step s t → Path t u → Path s u

/-- Composition of paths -/
def Path.comp {M : RootedTS.{u, v}} {s t u : M.State} :
    M.Path s t → M.Path t u → M.Path s u
  | .nil _, p => p
  | .cons step p₁, p₂ => .cons step (p₁.comp p₂)

/-- Path composition is associative -/
theorem Path.comp_assoc {M : RootedTS.{u, v}} {s t u v : M.State}
    (p₁ : M.Path s t) (p₂ : M.Path t u) (p₃ : M.Path u v) :
    (p₁.comp p₂).comp p₃ = p₁.comp (p₂.comp p₃) := by
  induction p₁ with
  | nil _ => rfl
  | cons step p ih => simp only [Path.comp, ih]

/-- nil is left identity for path composition -/
theorem Path.nil_comp {M : RootedTS.{u, v}} {s t : M.State}
    (p : M.Path s t) : (Path.nil s).comp p = p := rfl

/-- nil is right identity for path composition -/
theorem Path.comp_nil {M : RootedTS.{u, v}} {s t : M.State}
    (p : M.Path s t) : p.comp (Path.nil t) = p := by
  induction p with
  | nil _ => rfl
  | cons step p ih => simp only [Path.comp, ih]

end RootedTS

/-!
## Task 3: Simulation Morphisms

A simulation from M to N is a structure-preserving map consisting of:
- A function on states `stateMap : M.State → N.State`
- A function on steps that preserves source/target
- Preservation of the initial state

This captures the notion of one computational system simulating another.
-/

/-- A Simulation is a morphism in RuleSys: a structure-preserving map between rooted transition systems.
    It maps states to states, steps to steps (preserving endpoints), and initial to initial. -/
structure Simulation (M N : RootedTS.{u, v}) where
  /-- The map on states -/
  stateMap : M.State → N.State
  /-- The map on steps, preserving source and target -/
  stepMap : {s t : M.State} → M.Step s t → N.Step (stateMap s) (stateMap t)
  /-- The initial state is preserved -/
  init_preserved : stateMap M.init = N.init

namespace Simulation

variable {M N P Q : RootedTS.{u, v}}

/-- Simulations extend to paths: a simulation maps paths to paths -/
def mapPath (f : Simulation M N) {s t : M.State} :
    M.Path s t → N.Path (f.stateMap s) (f.stateMap t)
  | .nil _ => .nil (f.stateMap _)
  | .cons step p => .cons (f.stepMap step) (f.mapPath p)

/-- mapPath preserves path composition -/
theorem mapPath_comp (f : Simulation M N) {s t u : M.State}
    (p₁ : M.Path s t) (p₂ : M.Path t u) :
    f.mapPath (p₁.comp p₂) = (f.mapPath p₁).comp (f.mapPath p₂) := by
  induction p₁ with
  | nil _ => rfl
  | cons step p ih => simp only [RootedTS.Path.comp, mapPath, ih]

/-- mapPath preserves identity paths -/
theorem mapPath_nil (f : Simulation M N) (s : M.State) :
    f.mapPath (RootedTS.Path.nil s) = RootedTS.Path.nil (f.stateMap s) := rfl

/-- Two simulations are equal if their stateMap and stepMap agree.
    This is the extensionality principle for simulations. -/
@[ext]
theorem ext {f g : Simulation M N}
    (h_state : f.stateMap = g.stateMap)
    (h_step : ∀ s t (step : M.Step s t),
      HEq (f.stepMap step) (g.stepMap step)) :
    f = g := by
  cases f with | mk fstate fstep finit =>
  cases g with | mk gstate gstep ginit =>
  simp only [mk.injEq] at h_state ⊢
  subst h_state
  simp only [heq_eq_eq, true_and]
  funext s t step
  exact eq_of_heq (h_step s t step)

/-!
## Task 4: Category Structure

We prove that RootedTS with Simulation morphisms forms a category:
- Identity: the identity simulation on any system
- Composition: composition of simulations
- Associativity and unit laws
-/

/-- Identity simulation: maps everything to itself -/
def id (M : RootedTS.{u, v}) : Simulation M M where
  stateMap := _root_.id
  stepMap := _root_.id
  init_preserved := rfl

/-- Composition of simulations -/
def comp (g : Simulation N P) (f : Simulation M N) : Simulation M P where
  stateMap := g.stateMap ∘ f.stateMap
  stepMap := g.stepMap ∘ f.stepMap
  init_preserved := by simp only [Function.comp_apply, f.init_preserved, g.init_preserved]

/-- Notation for simulation composition -/
infixr:80 " ≫ₛ " => Simulation.comp

/-- Composition is associative -/
theorem comp_assoc (h : Simulation P Q) (g : Simulation N P) (f : Simulation M N) :
    (h ≫ₛ g) ≫ₛ f = h ≫ₛ (g ≫ₛ f) := by
  cases h; cases g; cases f
  rfl

/-- Left identity law -/
theorem id_comp (f : Simulation M N) : (Simulation.id N) ≫ₛ f = f := by
  cases f
  rfl

/-- Right identity law -/
theorem comp_id (f : Simulation M N) : f ≫ₛ (Simulation.id M) = f := by
  cases f
  rfl

end Simulation

/-!
## Reachability Simulations (Primary Notion)

A reachability simulation maps paths to paths. This is the PRIMARY notion of
simulation for the Church-Turing bi-interpretation framework, as it naturally
handles cases where a single computation step maps to a multi-step sequence.

**Key insight (v5.0):** Making reachability simulation the primary notion
eliminates the need for a separate "weak simulation" patch. Step-preserving
simulations embed as the special case where paths map to singleton paths.
-/

/-- A ReachabilitySimulation is the PRIMARY morphism type for labeled transition systems.

    It maps states to states and PATHS to PATHS (not just steps to steps).
    This naturally handles:
    - Church encoding: TM step → β-reduction sequence
    - UTM simulation: β-reduction → TM computation sequence

    Step-preserving simulations (the old `Simulation`) embed as the special case
    where path maps factor through single steps.

    **Key property:** Reachability is preserved. If s →* t in M, then f(s) →* f(t) in N. -/
structure ReachabilitySimulation (M N : RootedTS.{u, v}) where
  /-- The map on states -/
  stateMap : M.State → N.State
  /-- The reachability map: paths map to paths -/
  reachMap : {s t : M.State} → M.Path s t → N.Path (stateMap s) (stateMap t)
  /-- The initial state is preserved -/
  init_preserved : stateMap M.init = N.init
  /-- reachMap preserves path composition -/
  reachMap_comp : ∀ {s t u : M.State} (p₁ : M.Path s t) (p₂ : M.Path t u),
    reachMap (p₁.comp p₂) = (reachMap p₁).comp (reachMap p₂)

namespace ReachabilitySimulation

variable {M N P : RootedTS.{u, v}}

/-- Every step-preserving Simulation embeds as a ReachabilitySimulation.
    Single steps become singleton paths. -/
def ofSimulation (f : Simulation M N) : ReachabilitySimulation M N where
  stateMap := f.stateMap
  reachMap := f.mapPath  -- mapPath already exists on Simulation
  init_preserved := f.init_preserved
  reachMap_comp := f.mapPath_comp

/-- Composition of reachability simulations -/
def comp (g : ReachabilitySimulation N P) (f : ReachabilitySimulation M N) :
    ReachabilitySimulation M P where
  stateMap := g.stateMap ∘ f.stateMap
  reachMap := fun path => g.reachMap (f.reachMap path)
  init_preserved := by simp [Function.comp_apply, f.init_preserved, g.init_preserved]
  reachMap_comp := by
    intro s t u p₁ p₂
    simp only [f.reachMap_comp, g.reachMap_comp]

/-- Identity reachability simulation -/
def id (M : RootedTS.{u, v}) : ReachabilitySimulation M M where
  stateMap := _root_.id
  reachMap := _root_.id
  init_preserved := rfl
  reachMap_comp := by intros; rfl

end ReachabilitySimulation

/-- Lift a step-to-path map to a path-to-path map -/
private def liftStepToPath {M N : RootedTS.{u, v}}
    {f : M.State → N.State}
    (stepToPath : {s t : M.State} → M.Step s t → N.Path (f s) (f t))
    {s t : M.State} : M.Path s t → N.Path (f s) (f t)
  | .nil _ => .nil _
  | .cons step rest => (stepToPath step).comp (liftStepToPath stepToPath rest)

/-- The lifted step-to-path map preserves path composition -/
private theorem liftStepToPath_comp {M N : RootedTS.{u, v}}
    {f : M.State → N.State}
    (stepToPath : {s t : M.State} → M.Step s t → N.Path (f s) (f t))
    {s t u : M.State} (p₁ : M.Path s t) (p₂ : M.Path t u) :
    liftStepToPath stepToPath (p₁.comp p₂) =
      (liftStepToPath stepToPath p₁).comp (liftStepToPath stepToPath p₂) := by
  induction p₁ with
  | nil _ => simp [liftStepToPath, RootedTS.Path.nil_comp]
  | cons step p ih =>
    simp only [RootedTS.Path.comp, liftStepToPath]
    rw [ih, RootedTS.Path.comp_assoc]

namespace ReachabilitySimulation

variable {M N P : RootedTS.{u, v}}

/-- Construct a ReachabilitySimulation from a step-to-path map.

    This is the appropriate constructor for Church-Turing encodings where
    a single computational step in M corresponds to a multi-step path in N
    (e.g., one TM step → a sequence of β-reductions). The path-to-path map
    is derived by inductively composing step-to-path maps. -/
def ofStepToPath
    (stateMap : M.State → N.State)
    (stepToPath : {s t : M.State} → M.Step s t → N.Path (stateMap s) (stateMap t))
    (init_preserved : stateMap M.init = N.init) :
    ReachabilitySimulation M N where
  stateMap := stateMap
  reachMap := liftStepToPath stepToPath
  init_preserved := init_preserved
  reachMap_comp := liftStepToPath_comp stepToPath

end ReachabilitySimulation

/-!
## Category Instance

We now package everything into a Category instance for RootedTS,
making it usable with mathlib's category theory library.
-/

/-- RuleSys: The category of rooted transition systems and simulations.
    This is the foundational category for constructing the classifying presheaf topos. -/
instance : Category RootedTS.{u, v} where
  Hom := Simulation
  id := Simulation.id
  comp := fun f g => g ≫ₛ f  -- Note: mathlib uses f ≫ g = g ∘ f convention
  id_comp := fun f => Simulation.comp_id f
  comp_id := fun f => Simulation.id_comp f
  assoc := fun f g h => (Simulation.comp_assoc h g f).symm

/-- RuleSys: the category of rooted transition systems (rooted transition systems) -/
abbrev RuleSys := RootedTS.{u, v}

namespace RuleSys

/-- The objects of RuleSys are rooted transition systems -/
example : Type (u + 1) := RuleSys.{u, 0}

/-- Morphisms in RuleSys are simulations -/
example (M N : RuleSys.{u, v}) : Type (max u v) := M ⟶ N

/-- RuleSys has identity morphisms -/
example (M : RuleSys.{u, v}) : M ⟶ M := 𝟙 M

/-- RuleSys has composition of morphisms -/
example {M N P : RuleSys.{u, v}} (f : M ⟶ N) (g : N ⟶ P) : M ⟶ P := f ≫ g

end RuleSys

/-!
## Examples

Some basic examples of rooted transition systems to demonstrate the definitions.
-/

/-- The trivial rooted transition system with one state and no non-identity steps -/
def trivialSystem : RootedTS where
  State := Unit
  Step := fun _ _ => Empty
  init := ()

/-- A simple binary counter system -/
def binaryCounter : RootedTS where
  State := Nat
  Step := fun n m => PLift (m = n + 1)  -- Can only increment
  init := 0

/-- The identity simulation on the trivial system -/
example : trivialSystem ⟶ trivialSystem := 𝟙 trivialSystem

/-- Simulation from trivial to any system (maps to initial state) -/
def fromTrivial (M : RootedTS.{0, 0}) : Simulation trivialSystem M :=
  { stateMap := fun _ => M.init
    stepMap := fun e => e.elim
    init_preserved := rfl }

/-!
## Halting and Reachability

Basic definitions for halting states and reachable halting in rooted transition systems.
These are placed here (rather than in Irreducibility) so that TuringMachine.lean
can use them without circular imports.
-/

/-- A halting state in a rooted transition system: a state with no outgoing steps -/
def isHalting (M : RootedTS.{u, v}) (s : M.State) : Prop :=
  ∀ t : M.State, IsEmpty (M.Step s t)

/-- A rooted transition system reaches a halting configuration: there exists a reachable
    state from init that has no outgoing transitions. -/
def ReachesHalt (M : RootedTS.{0, 0}) : Prop :=
  ∃ (s : M.State), (∃ _ : M.Path M.init s, True) ∧ isHalting M s

end RTS
