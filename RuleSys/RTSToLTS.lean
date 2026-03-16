/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# MultiwayToLTS: Bridge between RootedTS and FinLTS

This file bridges the two core formalisms in the project:
- **RootedTS** (Basic.lean): objects of RuleSys, with typed step relation `Step : State → State → Type v`
- **FinLTS** (PresheafTopos/LabeledLTS.lean): finite labeled transition systems with `edge : L → Vertex → Vertex → Prop`

The bridge embeds finite RootedTS instances into `FinLTS Unit` (single-label LTS)
by collapsing the typed step relation to a propositional edge predicate via `Nonempty`.

## Main Definitions

- `RootedTS.toLTS`: Convert a finite RootedTS to `FinLTS Unit`
- `Simulation.toLTSHom`: Lift simulation morphisms to LTS homomorphisms
- `toLTSHom_id`: Identity preservation (functoriality)
- `toLTSHom_comp`: Composition preservation (functoriality)

## Design Notes

- Restricted to `RootedTS.{0, 0}` since `FinLTS` requires `Type` (not `Type u`)
- Requires `Fintype`, `DecidableEq` on State and `Decidable (Nonempty (M.Step s t))`
- The single label `Unit` reflects that RootedTS is unlabeled

## References

- Caramello, "Theories, Sites, Toposes"
- Sobocinski, "Relational presheaves, change of base and weak simulation" (JCSS 2015)
-/

import RuleSys.Basic
import RuleSys.PresheafTopos.LabeledLTS

set_option autoImplicit false

namespace RTS

open PresheafTopos

/-!
## Part 1: Object Map — RootedTS to FinLTS Unit

A `RootedTS.{0, 0}` with finite decidable state and decidable step existence
maps to a `FinLTS Unit` where the single `()` label carries all transitions.

The edge predicate is `fun () s t => Nonempty (M.Step s t)`, collapsing the
potentially multi-valued typed step relation to a propositional assertion of
step existence.
-/

/-- Convert a finite RootedTS with decidable step existence to a single-label FinLTS.

    The typed step relation `Step : State → State → Type` is collapsed to the propositional
    edge predicate `Nonempty (M.Step s t)`. This forgets *which* rewrite rule applies but
    preserves *whether* a transition exists, which suffices for process-algebraic properties
    (trace equivalence, bisimulation, etc.). -/
def RootedTS.toLTS (M : RootedTS.{0, 0})
    [Fintype M.State] [DecidableEq M.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))] : FinLTS Unit where
  Vertex := M.State
  edge := fun () s t => Nonempty (M.Step s t)
  edgeDecidable := fun () => inferInstance

/-!
## Part 2: Morphism Map — Simulation to LTSHom

A `Simulation M N` maps to `LTSHom M.toLTS N.toLTS`: the state map becomes the
vertex map, and the step map witnesses edge preservation.
-/

/-- Lift a simulation between RootedTS instances to an LTS homomorphism between
    their FinLTS images.

    Given `f : Simulation M N` with `f.stepMap : M.Step s t → N.Step (f.stateMap s) (f.stateMap t)`,
    the edge preservation follows: if `Nonempty (M.Step s t)` then
    `Nonempty (N.Step (f.stateMap s) (f.stateMap t))` by applying `f.stepMap`. -/
def Simulation.toLTSHom {M N : RootedTS.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    (f : Simulation M N) : LTSHom M.toLTS N.toLTS where
  toFun := f.stateMap
  map_edge := fun () _ _ ⟨step⟩ => ⟨f.stepMap step⟩

/-!
## Part 3: Functoriality Properties

The assignment `M ↦ M.toLTS`, `f ↦ f.toLTSHom` respects identity and composition,
making it a functor from the subcategory of finite decidable RootedTS to
the category of `FinLTS Unit`.
-/

/-- The vertex type of the converted LTS is definitionally equal to the state type. -/
theorem RootedTS.toLTS_vertex (M : RootedTS.{0, 0})
    [Fintype M.State] [DecidableEq M.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))] :
    M.toLTS.Vertex = M.State := rfl

/-- Identity preservation: the identity simulation maps to the identity LTS homomorphism. -/
theorem Simulation.toLTSHom_id (M : RootedTS.{0, 0})
    [Fintype M.State] [DecidableEq M.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))] :
    (Simulation.id M).toLTSHom = LTSHom.id M.toLTS := by
  apply LTSHom.ext
  intro v
  rfl

/-- Composition preservation: composing simulations then converting equals converting
    then composing LTS homomorphisms.

    Note on argument order: `Simulation.comp g f` = g ∘ f (g after f), while
    `LTSHom.comp f' g'` = g' ∘ f' (g' after f'). -/
theorem Simulation.toLTSHom_comp {M N P : RootedTS.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [Fintype P.State] [DecidableEq P.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    [∀ s t, Decidable (Nonempty (P.Step s t))]
    (g : Simulation N P) (f : Simulation M N) :
    (g.comp f).toLTSHom = LTSHom.comp f.toLTSHom g.toLTSHom := by
  apply LTSHom.ext
  intro v
  rfl

/-- The init state is preserved as a vertex: `f.stateMap M.init = N.init` in the
    LTS image, directly inherited from `f.init_preserved`. -/
theorem Simulation.toLTSHom_init {M N : RootedTS.{0, 0}}
    [Fintype M.State] [DecidableEq M.State]
    [Fintype N.State] [DecidableEq N.State]
    [∀ s t, Decidable (Nonempty (M.Step s t))]
    [∀ s t, Decidable (Nonempty (N.Step s t))]
    (f : Simulation M N) :
    f.toLTSHom.toFun M.init = N.init :=
  f.init_preserved

end RTS
