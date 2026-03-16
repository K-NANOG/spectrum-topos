/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fiber Products (Pullbacks) of Rooted Transition Systems

This file defines:
1. FiberProduct - the pullback of two simulations with common target
2. Projection simulations fst and snd
3. Universal property (lift) and HasPullback instance

## Mathematical Content

Given simulations f : M ⟶ N and g : P ⟶ N, the fiber product M ×_N P is the
rooted transition system whose:
- States are pairs (m, p) where f.stateMap m = g.stateMap p
- Steps are compatible pairs of steps
- Initial state is (M.init, P.init)

This provides the categorical pullback structure needed for Grothendieck topology
proofs, particularly observerCovering_pullback.

## References
- Mac Lane, "Categories for the Working Mathematician", Ch. III
- Mathlib CategoryTheory.Limits.Shapes.Pullback
-/

import RuleSys.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace RTS

/-- Helper: HEq of products from HEq of components (same universe for simplicity) -/
theorem Prod.ext_heq {α₁ α₂ : Type u} {β₁ β₂ : Type v} {a₁ : α₁} {a₂ : α₂} {b₁ : β₁} {b₂ : β₂}
    (ha : HEq a₁ a₂) (hb : HEq b₁ b₂) : HEq (a₁, b₁) (a₂, b₂) := by
  cases ha; cases hb; rfl

variable {M N P : RootedTS.{u, v}} (f : M ⟶ N) (g : P ⟶ N)

/-!
## Fiber Product Structure

The fiber product M ×_N P consists of compatible pairs of states and steps.
-/

/-- The fiber product of two simulations with common target.
    States are pairs (m, p) with f(m) = g(p).
    Steps are pairs of steps whose images are equal (via HEq due to dependent types). -/
def FiberProduct : RootedTS.{u, v} where
  State := { pair : M.State × P.State // f.stateMap pair.1 = g.stateMap pair.2 }
  Step := fun s t =>
    { stepPair : M.Step s.val.1 t.val.1 × P.Step s.val.2 t.val.2 //
      HEq (f.stepMap stepPair.1) (g.stepMap stepPair.2) }
  init := ⟨(M.init, P.init), by
    rw [f.init_preserved, g.init_preserved]⟩

namespace FiberProduct

/-- First projection: FiberProduct f g → M -/
def fst : FiberProduct f g ⟶ M where
  stateMap := fun s => s.val.1
  stepMap := fun step => step.val.1
  init_preserved := rfl

/-- Second projection: FiberProduct f g → P -/
def snd : FiberProduct f g ⟶ P where
  stateMap := fun s => s.val.2
  stepMap := fun step => step.val.2
  init_preserved := rfl

/-- The pullback condition: fst ≫ f = snd ≫ g
    In Mathlib's convention, h ≫ k means k ∘ h (diagrammatic order) -/
theorem condition : fst f g ≫ f = snd f g ≫ g := by
  apply Simulation.ext
  · -- stateMap equality: f.stateMap (s.val.1) = g.stateMap (s.val.2)
    funext s
    exact s.property
  · -- stepMap equality: f.stepMap step.val.1 and g.stepMap step.val.2 are HEq
    intro s t step
    -- step.property gives us the HEq we need
    simp only [CategoryStruct.comp, Simulation.comp]
    exact step.property

/-- Lift morphism: given h : W → M and k : W → P with h ≫ f = k ≫ g,
    there exists a unique morphism W → FiberProduct f g -/
def lift {W : RootedTS.{u, v}} (h : W ⟶ M) (k : W ⟶ P)
    (w : h ≫ f = k ≫ g) : W ⟶ FiberProduct f g where
  stateMap := fun s => ⟨(h.stateMap s, k.stateMap s), by
    -- Need: f.stateMap (h.stateMap s) = g.stateMap (k.stateMap s)
    -- This follows from w : h ≫ f = k ≫ g
    have hw : (h ≫ f).stateMap = (k ≫ g).stateMap := congrArg Simulation.stateMap w
    exact congrFun hw s⟩
  stepMap := fun {s t} step => ⟨(h.stepMap step, k.stepMap step), by
    -- Need: HEq (f.stepMap (h.stepMap step)) (g.stepMap (k.stepMap step))
    -- w : h ≫ f = k ≫ g, and composition is (h ≫ f).stepMap = f.stepMap ∘ h.stepMap
    -- So this reduces to showing the composed simulations have equal stepMap images
    have heq : HEq ((h ≫ f).stepMap (s := s) (t := t) step)
                   ((k ≫ g).stepMap (s := s) (t := t) step) := by
      rw [w]
    simp only [CategoryStruct.comp, Simulation.comp] at heq
    exact heq⟩
  init_preserved := by
    simp only [FiberProduct]
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    exact ⟨h.init_preserved, k.init_preserved⟩

/-- lift composed with fst gives back h -/
theorem lift_fst {W : RootedTS.{u, v}} (h : W ⟶ M) (k : W ⟶ P)
    (w : h ≫ f = k ≫ g) : lift f g h k w ≫ fst f g = h := by
  apply Simulation.ext
  · -- stateMap: (lift ≫ fst).stateMap s = h.stateMap s
    funext s
    rfl
  · -- stepMap: both give h.stepMap step
    intro s t step
    apply HEq.rfl

/-- lift composed with snd gives back k -/
theorem lift_snd {W : RootedTS.{u, v}} (h : W ⟶ M) (k : W ⟶ P)
    (w : h ≫ f = k ≫ g) : lift f g h k w ≫ snd f g = k := by
  apply Simulation.ext
  · funext s; rfl
  · intro s t step; apply HEq.rfl

/- Uniqueness: any morphism agreeing with lift on projections equals lift.

    Mathematical content: Two morphisms into a fiber product are equal iff their
    projections are equal. This follows from the universal property of pullbacks.

    Proof outline:
    1. Extract stateMap component equalities from h_fst and h_snd
    2. Combine via Prod.ext and Subtype.ext to get φ.stateMap = ψ.stateMap
    3. After substitution, extract stepMap component equalities similarly
    4. Conclude φ.stepMap = ψ.stepMap by the same method

    Technical blocker: Extracting stepMap equality from composed simulation equality
    requires careful handling of dependent types. The simulation composition
    creates types that depend on stateMap, and Lean 4's dependent elimination
    doesn't automatically simplify simulation equality into component equalities.

    Potential fix: Define a custom injectivity lemma for simulation composition
    that properly handles the dependent stepMap type. -/
/-- **Axiomatized**: The stepMap component equality requires extracting dependent type
    equalities from composed simulation equalities (h_fst, h_snd). The stateMap equality
    is proven constructively via Subtype.ext and Prod.ext. The stepMap equality follows
    mathematically because FiberProduct steps are determined by their first and second
    projections (which are equal by h_fst and h_snd), but Lean 4's dependent type
    elimination does not automatically simplify the HEq goals that arise.

    A full proof would require custom injectivity lemmas for simulation composition
    that properly handle the dependent stepMap types. -/
theorem hom_ext {W : RootedTS.{u, v}} (φ ψ : W ⟶ FiberProduct f g)
    (h_fst : φ ≫ fst f g = ψ ≫ fst f g)
    (h_snd : φ ≫ snd f g = ψ ≫ snd f g) : φ = ψ := by
  -- Extract stateMap equalities from projection equalities
  have h_sm_fst : ∀ s, (φ.stateMap s).val.1 = (ψ.stateMap s).val.1 :=
    fun s => congrFun (congrArg Simulation.stateMap h_fst) s
  have h_sm_snd : ∀ s, (φ.stateMap s).val.2 = (ψ.stateMap s).val.2 :=
    fun s => congrFun (congrArg Simulation.stateMap h_snd) s
  -- Combine into stateMap equality
  have h_sm : φ.stateMap = ψ.stateMap := by
    funext s
    exact Subtype.ext (Prod.ext (h_sm_fst s) (h_sm_snd s))
  -- Case split on simulation structures and substitute stateMap equality
  cases φ with | mk φs φst φi =>
  cases ψ with | mk ψs ψst ψi =>
  simp only [Simulation.stateMap] at h_sm
  subst h_sm
  -- After substituting stateMap equality, stepMap types now agree
  -- We need to show the full simulations are equal
  -- Since stateMap is the same, it suffices to show stepMap agrees
  congr 1
  · -- stepMap equality
    funext s t step
    apply Subtype.ext
    apply Prod.ext
    · -- First component: extract from h_fst
      have : (⟨φs, φst, φi⟩ : Simulation W (FiberProduct f g)) ≫ fst f g =
             (⟨φs, ψst, ψi⟩ : Simulation W (FiberProduct f g)) ≫ fst f g := h_fst
      have h_step : ∀ (s t : W.State) (step : W.Step s t),
          HEq (((⟨φs, φst, φi⟩ : Simulation W (FiberProduct f g)) ≫ fst f g).stepMap step)
               (((⟨φs, ψst, ψi⟩ : Simulation W (FiberProduct f g)) ≫ fst f g).stepMap step) := by
        intro s t step; rw [this]
      exact eq_of_heq (h_step s t step)
    · -- Second component: extract from h_snd
      have : (⟨φs, φst, φi⟩ : Simulation W (FiberProduct f g)) ≫ snd f g =
             (⟨φs, ψst, ψi⟩ : Simulation W (FiberProduct f g)) ≫ snd f g := h_snd
      have h_step : ∀ (s t : W.State) (step : W.Step s t),
          HEq (((⟨φs, φst, φi⟩ : Simulation W (FiberProduct f g)) ≫ snd f g).stepMap step)
               (((⟨φs, ψst, ψi⟩ : Simulation W (FiberProduct f g)) ≫ snd f g).stepMap step) := by
        intro s t step; rw [this]
      exact eq_of_heq (h_step s t step)

/-!
## Pullback Cone and Universal Property
-/

/-- The pullback cone for f and g -/
def cone : PullbackCone f g :=
  PullbackCone.mk (fst f g) (snd f g) (condition f g)

/-- The pullback cone is a limit -/
def isLimit : IsLimit (cone f g) := by
  apply PullbackCone.isLimitAux'
  intro s
  refine ⟨lift f g s.fst s.snd s.condition, ?_, ?_, ?_⟩
  · -- fst property
    exact lift_fst f g s.fst s.snd s.condition
  · -- snd property
    exact lift_snd f g s.fst s.snd s.condition
  · -- uniqueness
    intro m hm_fst hm_snd
    apply hom_ext
    · -- Need: m ≫ fst f g = lift ... ≫ fst f g
      -- hm_fst : m ≫ (cone f g).fst = s.fst
      -- (cone f g).fst = fst f g by definition
      rw [lift_fst]
      exact hm_fst
    · rw [lift_snd]
      exact hm_snd

end FiberProduct

/-!
## HasPullback Instance
-/

/-- RuleSys has pullbacks for any pair of morphisms with common target -/
instance hasPullback : HasPullback f g :=
  ⟨⟨FiberProduct.cone f g, FiberProduct.isLimit f g⟩⟩

/-- RuleSys has all pullbacks -/
instance hasPullbacks : HasPullbacks RootedTS.{u, v} :=
  @hasPullbacks_of_hasLimit_cospan _ _ (fun {X Y Z} {f} {g} => hasPullback f g)

end RTS
