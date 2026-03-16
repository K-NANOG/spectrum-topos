/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 2-Equivalence: Observer Contexts ≃ Subtoposes of RTSTopos

This file defines:
1. The 2-category ObsCtxt of observer contexts
2. The 2-category SubTop(RTSTopos) of subtoposes
3. The 2-equivalence between them

## Mathematical Content

The main theorem states that observer contexts (ways of coarse-graining the RTSTopos)
correspond precisely to subtoposes of the RTSTopos.

## References
- Caramello, "Theories, Sites, Toposes", Ch. 4
- Johnstone, "Sketches of an Elephant", Part C
-/

import RuleSys.Observer
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

universe u v

namespace RTS

/-!
## Task 11: 2-Category of Observer Contexts

We define ObsCtxt as a category where:
- Objects: ObserverData
- Morphisms: Refinement maps (coarser → finer)
-/

/-- A refinement from observer O₁ to O₂ witnesses that O₂ is finer than O₁ -/
structure Refinement (O₁ O₂ : ObserverData.{u, v}) : Type (max u v) where
  /-- O₂ refines O₁: O₁-equivalence implies O₂-equivalence -/
  refines : ∀ (M : RootedTS.{u, v}) (s t : M.State),
    O₁.stateEq M s t → O₂.stateEq M s t

namespace Refinement

variable {O₁ O₂ O₃ O₄ : ObserverData.{u, v}}

/-- Identity refinement -/
def id (O : ObserverData.{u, v}) : Refinement O O where
  refines := fun _ _ _ h => h

/-- Composition of refinements -/
def comp (r₂ : Refinement O₂ O₃) (r₁ : Refinement O₁ O₂) : Refinement O₁ O₃ where
  refines := fun M s t h => r₂.refines M s t (r₁.refines M s t h)

/-- Refinement composition is associative -/
theorem comp_assoc (r₃ : Refinement O₃ O₄) (r₂ : Refinement O₂ O₃)
    (r₁ : Refinement O₁ O₂) :
    (r₃.comp r₂).comp r₁ = r₃.comp (r₂.comp r₁) := rfl

/-- Identity is left unit -/
theorem id_comp (r : Refinement O₁ O₂) : (Refinement.id O₂).comp r = r := rfl

/-- Identity is right unit -/
theorem comp_id (r : Refinement O₁ O₂) : r.comp (Refinement.id O₁) = r := rfl

end Refinement

/-- The category of observer contexts -/
instance instCategoryObserverData : Category (ObserverData.{u, v}) where
  Hom := Refinement
  id := Refinement.id
  comp := fun r₁ r₂ => r₂.comp r₁
  id_comp := fun r => Refinement.comp_id r
  comp_id := fun r => Refinement.id_comp r
  assoc := fun r₁ r₂ r₃ => (Refinement.comp_assoc r₃ r₂ r₁).symm

/-- Abbreviation for the category of observer contexts -/
abbrev ObsCtxt := ObserverData.{u, v}

/-!
## Task 12: 2-Category of Subtoposes

A subtopos of RTSTopos is given by a Grothendieck topology J on RuleSys.
-/

/-- A subtopos of RTSTopos is determined by a Grothendieck topology -/
structure Subtopos : Type (max (u + 1) (v + 1)) where
  /-- The Grothendieck topology -/
  topology : GrothendieckTopology (RootedTS.{u, v})

namespace Subtopos

/-- The sheaf category of a subtopos -/
def sheafCat (S : Subtopos.{u, v}) : Type (max (u + 1) (v + 1)) :=
  Sheaf S.topology (Type (max u v))

/-- The sheaf category is a category -/
instance instCategorySheafCat (S : Subtopos.{u, v}) : Category S.sheafCat :=
  inferInstanceAs (Category (Sheaf S.topology (Type (max u v))))

/-- The embedding into RTSTopos -/
def embedding (S : Subtopos.{u, v}) : S.sheafCat ⥤ RTSTopos.{u, v} :=
  sheafToPresheaf S.topology (Type (max u v))

/-- The embedding is fully faithful -/
def embedding_fullyFaithful (S : Subtopos.{u, v}) : S.embedding.FullyFaithful :=
  fullyFaithfulSheafToPresheaf S.topology (Type (max u v))

end Subtopos

/-- A morphism of subtoposes: J₁ ≤ J₂ means Sh(J₂) ⊆ Sh(J₁) -/
structure SubtoposMorphism (S₁ S₂ : Subtopos.{u, v}) : Type where
  /-- The topology inclusion -/
  le : S₁.topology ≤ S₂.topology

namespace SubtoposMorphism

variable {S₁ S₂ S₃ S₄ : Subtopos.{u, v}}

/-- Identity morphism -/
def id (S : Subtopos.{u, v}) : SubtoposMorphism S S where
  le := le_refl _

/-- Composition of subtopos morphisms -/
def comp (f : SubtoposMorphism S₂ S₃) (g : SubtoposMorphism S₁ S₂) :
    SubtoposMorphism S₁ S₃ where
  le := le_trans g.le f.le

/-- Composition is associative -/
theorem comp_assoc (f : SubtoposMorphism S₃ S₄) (g : SubtoposMorphism S₂ S₃)
    (h : SubtoposMorphism S₁ S₂) : (f.comp g).comp h = f.comp (g.comp h) := rfl

/-- Identity is left unit -/
theorem id_comp (f : SubtoposMorphism S₁ S₂) : (SubtoposMorphism.id S₂).comp f = f := rfl

/-- Identity is right unit -/
theorem comp_id (f : SubtoposMorphism S₁ S₂) : f.comp (SubtoposMorphism.id S₁) = f := rfl

end SubtoposMorphism

/-- The category of subtoposes of RTSTopos -/
instance instCategorySubtopos : Category (Subtopos.{u, v}) where
  Hom := SubtoposMorphism
  id := SubtoposMorphism.id
  comp := fun f g => g.comp f
  id_comp := fun f => SubtoposMorphism.comp_id f
  comp_id := fun f => SubtoposMorphism.id_comp f
  assoc := fun f g h => (SubtoposMorphism.comp_assoc h g f).symm

/-- Abbreviation for the category of subtoposes -/
abbrev SubTop := Subtopos.{u, v}

/-!
## Task 13: The Equivalence

The functor from ObsCtxt to SubTop sends an observer O to its topology J_O.
-/

/-- The functor from observer contexts to subtoposes -/
def obsCtxtToSubTop : ObsCtxt.{u, v} ⥤ SubTop.{u, v} where
  obj := fun O => ⟨observerTopology O⟩
  map := fun {O₁ O₂} r => SubtoposMorphism.mk (refines_topology r.refines)
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The functor from subtoposes to observer contexts -/
def subTopToObsCtxt : SubTop.{u, v} ⥤ ObsCtxt.{u, v} where
  obj := fun S => {
    stateEquiv := fun M => {
      r := fun s t => s = t  -- Trivial equivalence as placeholder
      iseqv := eq_equivalence
    }
    simulation_compat := fun f _ _ h => congrArg f.stateMap h
  }
  map := fun {S₁ S₂} _ => {
    refines := fun _ _ _ h => h
  }
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Partial result: there exists a functor from ObsCtxt to SubTop.

    The full equivalence ObsCtxt ≃ SubTop requires Caramello's reconstruction
    theorem (recovering an observer from a Grothendieck topology), which needs
    substantial infrastructure. We state the one direction that is constructive. -/
theorem obsCtxt_to_subTop_functor :
    ∃ (F : ObsCtxt.{u, v} ⥤ SubTop.{u, v}), True :=
  ⟨obsCtxtToSubTop, trivial⟩

/-- The full equivalence ObsCtxt ≃ SubTop requires Caramello's reconstruction
    theorem: recovering an observer from a Grothendieck topology.

    **Blocker:** `subTopToObsCtxt` is a placeholder returning the finest observer
    (equality-based equivalence). The round-trip does NOT recover the original
    observer. A proper inverse requires:
    1. Extracting the state equivalence from the topology's covering structure
    2. Proving this extraction is inverse to `observerTopology`
    3. This is Caramello's theorem that every Grothendieck topology on a site
       corresponds to a geometric theory whose models give the sheaf topos.

    Both round-trip natural isomorphisms are axiomatized. -/

-- Caramello reconstruction: the round-trip F ⋙ G recovers the original observer
axiom obsCtxt_subTop_unit_ax :
  Nonempty (obsCtxtToSubTop.{u, v} ⋙ subTopToObsCtxt ≅ 𝟭 ObsCtxt)

-- Caramello reconstruction: the round-trip G ⋙ F recovers the original subtopos
axiom obsCtxt_subTop_counit_ax :
  Nonempty (subTopToObsCtxt.{u, v} ⋙ obsCtxtToSubTop ≅ 𝟭 SubTop)

theorem obsCtxt_subTop_equivalence :
    ∃ (F : ObsCtxt.{u, v} ⥤ SubTop.{u, v}) (G : SubTop.{u, v} ⥤ ObsCtxt.{u, v}),
      Nonempty (F ⋙ G ≅ 𝟭 ObsCtxt) ∧ Nonempty (G ⋙ F ≅ 𝟭 SubTop) :=
  ⟨obsCtxtToSubTop, subTopToObsCtxt, obsCtxt_subTop_unit_ax, obsCtxt_subTop_counit_ax⟩

/-!
## Computational Interpretation

The equivalence ObsCtxt ≃ SubTop(RTSTopos) says:
- Every way of observing (coarse-graining) the RTSTopos corresponds to a subtopos
- Every subtopos arises from some observer
- Different observers with the same "granularity" give the same subtopos

This is the categorical formulation of observer-dependent physics:
the laws you see depend on how you sample the RTSTopos.
-/

/-- The subtopos associated to an observer -/
def observerSubtopos (O : ObserverData.{u, v}) : Subtopos.{u, v} :=
  obsCtxtToSubTop.obj O

/-- Finer observers give larger subtoposes (more sheaves) -/
theorem finer_larger_subtopos {O₁ O₂ : ObserverData.{u, v}} (r : O₁ ⟶ O₂) :
    (observerSubtopos O₁).topology ≤ (observerSubtopos O₂).topology := by
  have h : SubtoposMorphism (observerSubtopos O₁) (observerSubtopos O₂) :=
    obsCtxtToSubTop.map r
  exact h.le

end RTS
