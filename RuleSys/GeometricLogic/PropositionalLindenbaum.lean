/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Propositional Lindenbaum Algebra

This file defines propositional geometric theories, their provability calculus,
semantic evaluation, and soundness. The Lindenbaum algebra (quotient by provable
equivalence) with full lattice structure is built in the second section.

## Main Definitions (Foundation)

- `PropFormula α`: Propositional geometric formulas over atoms α
- `PropSequent α`: Sequents φ ⊢ ψ of propositional formulas
- `PropGeoTheory`: Propositional geometric theory (finite atoms, finite axiom set)
- `PropProvable T s`: Provability relation (14 constructors)
- `PropFormula.eval`: Boolean evaluation under a valuation
- `PropGeoTheory.IsModel`: Model predicate (decidable)
- `PropProvable.sound`: Soundness theorem

## Main Definitions (Lindenbaum Algebra)

- `LindenbaumAlgebra T`: Quotient of PropFormula by provable equivalence
- Instances: `DistribLattice`, `BoundedOrder`, `Fintype`, `DecidableEq`,
  `CompleteDistribLattice` (hence `Frame`), `SmallCategory`
- `PropProvable.complete`: Completeness axiom (semantically valid ⟹ provable)
- `LindenbaumAlgebra.le_iff_provable`: ⟦φ⟧ ≤ ⟦ψ⟧ ↔ T ⊢ φ → ψ

## Implementation Notes

This is a self-contained propositional fragment, independent of the first-order
`GeoFormula` infrastructure. The connection to `SyntacticCategory` is deferred
to Phase 97 (integration).

Propositional geometric logic uses only ⊤, ⊥, ∧, ∨ (no negation, implication,
equality, or quantifiers).

## References

- Vickers, "Topology via Logic" (1989)
- Johnstone, "Stone Spaces" (1982)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Finset.Basic
import Mathlib.CategoryTheory.Category.Preorder

universe u

namespace GeometricLogic

namespace Propositional

/-!
## Propositional Formulas and Sequents
-/

/-- Propositional geometric formulas: the fragment with ⊤, ⊥, ∧, ∨.

Unlike `GeoFormula`, this has no quantifiers, equality, or relation symbols.
Atoms are propositional variables of type α. -/
inductive PropFormula (α : Type u) where
  | atom (a : α)
  | top
  | bot
  | conj (φ ψ : PropFormula α)
  | disj (φ ψ : PropFormula α)
  deriving DecidableEq

/-- A propositional geometric sequent: φ ⊢ ψ. -/
structure PropSequent (α : Type u) where
  antecedent : PropFormula α
  consequent : PropFormula α
  deriving DecidableEq

/-- A propositional geometric theory with finite atoms and finite axiom set.

The `Fintype` and `DecidableEq` constraints on `Atoms` enable:
- Computable model checking (enumerate all valuations)
- Decidable semantic entailment
- Fintype on the Lindenbaum algebra (via completeness) -/
structure PropGeoTheory where
  Atoms : Type u
  [fintypeAtoms : Fintype Atoms]
  [decidableEqAtoms : DecidableEq Atoms]
  axioms : Finset (PropSequent Atoms)

attribute [instance] PropGeoTheory.fintypeAtoms PropGeoTheory.decidableEqAtoms

variable {T : PropGeoTheory.{u}}

/-!
## Provability Calculus
-/

/-- Provability for propositional geometric theories.

The 14 constructors correspond to the structural rules of propositional geometric logic:
- `ax`: theory axioms
- `identity`, `cut`: structural rules (reflexivity, transitivity)
- `conj_intro`, `conj_elim_left`, `conj_elim_right`: conjunction rules
- `disj_intro_left`, `disj_intro_right`, `disj_elim`: disjunction rules
- `top_intro`, `bot_elim`: truth/falsity rules
- `weaken`, `weaken_right`: weakening rules
- `distrib`: frame distributivity (φ ∧ (ψ ∨ χ) ⊢ (φ ∧ ψ) ∨ (φ ∧ χ)) -/
inductive PropProvable (T : PropGeoTheory.{u}) : PropSequent T.Atoms → Prop where
  | ax {s : PropSequent T.Atoms} (h : s ∈ T.axioms) : PropProvable T s
  | identity (φ : PropFormula T.Atoms) : PropProvable T ⟨φ, φ⟩
  | cut {φ ψ χ : PropFormula T.Atoms}
      (h₁ : PropProvable T ⟨φ, ψ⟩) (h₂ : PropProvable T ⟨ψ, χ⟩) : PropProvable T ⟨φ, χ⟩
  | conj_intro {φ ψ χ : PropFormula T.Atoms}
      (h₁ : PropProvable T ⟨φ, ψ⟩) (h₂ : PropProvable T ⟨φ, χ⟩) :
      PropProvable T ⟨φ, .conj ψ χ⟩
  | conj_elim_left {φ ψ : PropFormula T.Atoms} :
      PropProvable T ⟨.conj φ ψ, φ⟩
  | conj_elim_right {φ ψ : PropFormula T.Atoms} :
      PropProvable T ⟨.conj φ ψ, ψ⟩
  | disj_intro_left {φ ψ : PropFormula T.Atoms} :
      PropProvable T ⟨φ, .disj φ ψ⟩
  | disj_intro_right {φ ψ : PropFormula T.Atoms} :
      PropProvable T ⟨ψ, .disj φ ψ⟩
  | disj_elim {φ ψ χ : PropFormula T.Atoms}
      (h₁ : PropProvable T ⟨φ, χ⟩) (h₂ : PropProvable T ⟨ψ, χ⟩) :
      PropProvable T ⟨.disj φ ψ, χ⟩
  | top_intro {φ : PropFormula T.Atoms} :
      PropProvable T ⟨φ, .top⟩
  | bot_elim {φ : PropFormula T.Atoms} :
      PropProvable T ⟨.bot, φ⟩
  | weaken {φ ψ χ : PropFormula T.Atoms}
      (h : PropProvable T ⟨φ, χ⟩) : PropProvable T ⟨.conj φ ψ, χ⟩
  | weaken_right {φ ψ χ : PropFormula T.Atoms}
      (h : PropProvable T ⟨ψ, χ⟩) : PropProvable T ⟨.conj φ ψ, χ⟩
  | distrib {φ ψ χ : PropFormula T.Atoms} :
      PropProvable T ⟨.conj φ (.disj ψ χ), .disj (.conj φ ψ) (.conj φ χ)⟩

scoped notation:25 T " ⊢ₚ " s => PropProvable T s

/-!
## Semantic Evaluation
-/

variable {α : Type u}

/-- Boolean evaluation of a propositional formula under a valuation. -/
def PropFormula.eval (v : α → Bool) : PropFormula α → Bool
  | .atom a => v a
  | .top => true
  | .bot => false
  | .conj φ ψ => φ.eval v && ψ.eval v
  | .disj φ ψ => φ.eval v || ψ.eval v

/-- A valuation v is a T-model if it satisfies all axioms of T:
for each axiom φ ⊢ ψ, whenever φ evaluates to true, so does ψ. -/
def PropGeoTheory.IsModel (T : PropGeoTheory.{u}) (v : T.Atoms → Bool) : Prop :=
  ∀ s ∈ T.axioms, s.antecedent.eval v = true → s.consequent.eval v = true

instance PropGeoTheory.decidableIsModel (T : PropGeoTheory.{u}) (v : T.Atoms → Bool) :
    Decidable (T.IsModel v) :=
  show Decidable (∀ s ∈ T.axioms, s.antecedent.eval v = true → s.consequent.eval v = true) from
    inferInstance

/-- The finite set of all T-models. -/
def PropGeoTheory.Models (T : PropGeoTheory.{u}) : Finset (T.Atoms → Bool) :=
  Finset.univ.filter T.IsModel

/-- Semantic entailment: a sequent is semantically valid in T if every T-model
satisfying the antecedent also satisfies the consequent. -/
def PropGeoTheory.semanticallyEntails (T : PropGeoTheory.{u}) (s : PropSequent T.Atoms) : Prop :=
  ∀ v : T.Atoms → Bool, T.IsModel v → s.antecedent.eval v = true → s.consequent.eval v = true

noncomputable instance PropGeoTheory.decidableSemanticallyEntails
    (T : PropGeoTheory.{u}) (s : PropSequent T.Atoms) :
    Decidable (T.semanticallyEntails s) :=
  show Decidable (∀ v : T.Atoms → Bool, T.IsModel v →
    s.antecedent.eval v = true → s.consequent.eval v = true) from
    Fintype.decidableForallFintype

/-!
## Soundness
-/

/-- Soundness: provable sequents are semantically valid.

Every constructor of `PropProvable` preserves truth under all T-models.
Proved by induction on the derivation. -/
theorem PropProvable.sound {T : PropGeoTheory.{u}} {s : PropSequent T.Atoms}
    (h : T ⊢ₚ s) :
    ∀ (v : T.Atoms → Bool), T.IsModel v →
      s.antecedent.eval v = true → s.consequent.eval v = true := by
  induction h with
  | ax hmem => exact fun _ hv ha => hv _ hmem ha
  | identity _ => exact fun _ _ ha => ha
  | cut _ _ ih₁ ih₂ => exact fun v hv ha => ih₂ v hv (ih₁ v hv ha)
  | conj_intro _ _ ih₁ ih₂ =>
    intro v hv ha
    simp only [PropFormula.eval, Bool.and_eq_true]
    exact ⟨ih₁ v hv ha, ih₂ v hv ha⟩
  | conj_elim_left =>
    intro v _ ha
    simp only [PropFormula.eval, Bool.and_eq_true] at ha
    exact ha.1
  | conj_elim_right =>
    intro v _ ha
    simp only [PropFormula.eval, Bool.and_eq_true] at ha
    exact ha.2
  | disj_intro_left =>
    intro v _ ha
    simp only [PropFormula.eval, Bool.or_eq_true]
    exact Or.inl ha
  | disj_intro_right =>
    intro v _ ha
    simp only [PropFormula.eval, Bool.or_eq_true]
    exact Or.inr ha
  | disj_elim _ _ ih₁ ih₂ =>
    intro v hv ha
    simp only [PropFormula.eval, Bool.or_eq_true] at ha
    rcases ha with h | h
    · exact ih₁ v hv h
    · exact ih₂ v hv h
  | top_intro => exact fun _ _ _ => rfl
  | bot_elim =>
    intro _ _ ha
    exact Bool.noConfusion ha
  | weaken _ ih =>
    intro v hv ha
    simp only [PropFormula.eval, Bool.and_eq_true] at ha
    exact ih v hv ha.1
  | weaken_right _ ih =>
    intro v hv ha
    simp only [PropFormula.eval, Bool.and_eq_true] at ha
    exact ih v hv ha.2
  | distrib =>
    intro v _ ha
    simp only [PropFormula.eval, Bool.and_eq_true, Bool.or_eq_true] at ha ⊢
    rcases ha with ⟨hφ, hψ | hχ⟩
    · exact Or.inl ⟨hφ, hψ⟩
    · exact Or.inr ⟨hφ, hχ⟩

/-- Soundness corollary: provable sequents are semantically entailed. -/
theorem PropProvable.sound' {T : PropGeoTheory.{u}} {s : PropSequent T.Atoms}
    (h : T ⊢ₚ s) : T.semanticallyEntails s :=
  h.sound

/-!
## Lindenbaum Algebra
-/

/-- Two formulas are provably equivalent in T if each entails the other. -/
def provableEquiv (T : PropGeoTheory.{u}) (φ ψ : PropFormula T.Atoms) : Prop :=
  PropProvable T ⟨φ, ψ⟩ ∧ PropProvable T ⟨ψ, φ⟩

/-- Provable equivalence is an equivalence relation. -/
def provableEquivSetoid (T : PropGeoTheory.{u}) : Setoid (PropFormula T.Atoms) where
  r := provableEquiv T
  iseqv := {
    refl := fun φ => ⟨.identity φ, .identity φ⟩
    symm := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
    trans := fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨.cut h₁ h₃, .cut h₄ h₂⟩
  }

/-- The Lindenbaum algebra of a propositional geometric theory T:
the quotient of formulas by provable equivalence. -/
def LindenbaumAlgebra (T : PropGeoTheory.{u}) :=
  Quotient (provableEquivSetoid T)

namespace LindenbaumAlgebra

variable {T : PropGeoTheory.{u}}

/-- Quotient map from formulas to Lindenbaum algebra elements. -/
def mk (φ : PropFormula T.Atoms) : LindenbaumAlgebra T :=
  Quotient.mk (provableEquivSetoid T) φ

/-- The ordering on the Lindenbaum algebra: ⟦φ⟧ ≤ ⟦ψ⟧ iff T proves φ ⊢ ψ. -/
instance : LE (LindenbaumAlgebra T) where
  le := Quotient.lift₂ (fun φ ψ => PropProvable T ⟨φ, ψ⟩)
    (fun _ _ _ _ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ => propext ⟨fun h => .cut ha₂ (.cut h hb₁),
      fun h => .cut ha₁ (.cut h hb₂)⟩)

theorem le_def (φ ψ : PropFormula T.Atoms) :
    (mk φ : LindenbaumAlgebra T) ≤ mk ψ ↔ PropProvable T ⟨φ, ψ⟩ :=
  Iff.rfl

instance : Preorder (LindenbaumAlgebra T) where
  le_refl := Quotient.ind (fun φ => (.identity φ : PropProvable T ⟨φ, φ⟩))
  le_trans a b c h₁ h₂ :=
    Quotient.inductionOn₃ a b c (fun _ _ _ (h₁ : PropProvable T _) (h₂ : PropProvable T _) =>
      .cut h₁ h₂) h₁ h₂

instance : PartialOrder (LindenbaumAlgebra T) where
  le_antisymm := Quotient.ind₂ (fun _ _ h₁ h₂ => Quotient.sound ⟨h₁, h₂⟩)

instance : DistribLattice (LindenbaumAlgebra T) where
  sup := Quotient.lift₂ (fun φ ψ => mk (.disj φ ψ))
    (fun _ _ _ _ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ => Quotient.sound
      ⟨.disj_elim (.cut ha₁ .disj_intro_left) (.cut hb₁ .disj_intro_right),
       .disj_elim (.cut ha₂ .disj_intro_left) (.cut hb₂ .disj_intro_right)⟩)
  inf := Quotient.lift₂ (fun φ ψ => mk (.conj φ ψ))
    (fun _ _ _ _ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ => Quotient.sound
      ⟨.conj_intro (.cut .conj_elim_left ha₁) (.cut .conj_elim_right hb₁),
       .conj_intro (.cut .conj_elim_left ha₂) (.cut .conj_elim_right hb₂)⟩)
  le_sup_left := Quotient.ind₂ (fun _ _ => (PropProvable.disj_intro_left : PropProvable T _))
  le_sup_right := Quotient.ind₂ (fun _ _ => (PropProvable.disj_intro_right : PropProvable T _))
  sup_le a b c h₁ h₂ :=
    Quotient.inductionOn₃ a b c (fun _ _ _ (h₁ : PropProvable T _) (h₂ : PropProvable T _) =>
      .disj_elim h₁ h₂) h₁ h₂
  inf_le_left := Quotient.ind₂ (fun _ _ => (PropProvable.conj_elim_left : PropProvable T _))
  inf_le_right := Quotient.ind₂ (fun _ _ => (PropProvable.conj_elim_right : PropProvable T _))
  le_inf a b c h₁ h₂ :=
    Quotient.inductionOn₃ a b c (fun _ _ _ (h₁ : PropProvable T _) (h₂ : PropProvable T _) =>
      .conj_intro h₁ h₂) h₁ h₂
  le_sup_inf a b c :=
    Quotient.inductionOn₃ a b c (fun φ ψ χ =>
      show PropProvable T ⟨.conj (.disj φ ψ) (.disj φ χ), .disj φ (.conj ψ χ)⟩ from
      .cut .distrib (.disj_elim
        (.cut .conj_elim_right .disj_intro_left)
        (.cut (.conj_intro .conj_elim_right .conj_elim_left)
          (.cut .distrib (.disj_elim
            (.cut .conj_elim_right .disj_intro_left)
            (.cut (.conj_intro .conj_elim_right .conj_elim_left) .disj_intro_right))))))

instance : OrderTop (LindenbaumAlgebra T) where
  top := mk .top
  le_top := Quotient.ind (fun _ => (PropProvable.top_intro : PropProvable T _))

instance : OrderBot (LindenbaumAlgebra T) where
  bot := mk .bot
  bot_le := Quotient.ind (fun _ => (PropProvable.bot_elim : PropProvable T _))

instance : BoundedOrder (LindenbaumAlgebra T) where
  __ := inferInstanceAs (OrderTop (LindenbaumAlgebra T))
  __ := inferInstanceAs (OrderBot (LindenbaumAlgebra T))

/-! ### API lemma -/

theorem le_iff_provable {φ ψ : PropFormula T.Atoms} :
    (mk φ : LindenbaumAlgebra T) ≤ mk ψ ↔ PropProvable T ⟨φ, ψ⟩ :=
  Iff.rfl

end LindenbaumAlgebra

/-!
## Completeness and Fintype
-/

/-- Completeness for propositional geometric logic: semantically entailed sequents are provable.

This is a standard result for finite propositional geometric logic (follows from
Birkhoff's representation theorem for finite distributive lattices, or directly
from the fact that propositional geometric logic has a finite model property).
Axiomatized here because the constructive proof requires a DNF construction
that is orthogonal to the topos-theoretic development. -/
axiom PropProvable.complete {T : PropGeoTheory.{u}} {s : PropSequent T.Atoms}
    (h : T.semanticallyEntails s) : PropProvable T s

namespace LindenbaumAlgebra

variable {T : PropGeoTheory.{u}}

/-- The model-behavior map: sends each equivalence class to its truth-table
restricted to T-models. Well-defined by soundness. -/
noncomputable def modelBehavior :
    LindenbaumAlgebra T → ({v : T.Atoms → Bool // T.IsModel v} → Bool) :=
  Quotient.lift (fun φ ⟨v, _⟩ => φ.eval v)
    (fun φ ψ ⟨h₁, h₂⟩ => funext fun ⟨v, hv⟩ => by
      simp only
      cases hφ : φ.eval v
      · cases hψ : ψ.eval v
        · rfl
        · exact absurd (h₂.sound v hv hψ) (by rw [hφ]; exact Bool.noConfusion)
      · cases hψ : ψ.eval v
        · exact absurd (h₁.sound v hv hφ) (by rw [hψ]; exact Bool.noConfusion)
        · rfl)

/-- The model-behavior map is injective (by completeness). -/
theorem modelBehavior_injective : Function.Injective (modelBehavior : LindenbaumAlgebra T → _) := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  apply Quotient.sound
  constructor
  · exact PropProvable.complete (fun v hv ha => by
      have := congr_fun hab ⟨v, hv⟩
      simp only [modelBehavior, Quotient.lift_mk] at this
      rw [ha] at this; exact this.symm)
  · exact PropProvable.complete (fun v hv hb => by
      have := congr_fun hab ⟨v, hv⟩
      simp only [modelBehavior, Quotient.lift_mk] at this
      rw [hb] at this; exact this)

/-- The Lindenbaum algebra is finite (injection into finite truth-table space). -/
noncomputable instance : Fintype (LindenbaumAlgebra T) :=
  Fintype.ofInjective modelBehavior modelBehavior_injective

/-- Decidable equality on the Lindenbaum algebra (from injection into finite type). -/
noncomputable instance : DecidableEq (LindenbaumAlgebra T) :=
  modelBehavior_injective.decidableEq

/-- The Lindenbaum algebra is a complete distributive lattice (hence a Frame).
Follows from `Fintype + DistribLattice + BoundedOrder`. -/
noncomputable instance : CompleteDistribLattice (LindenbaumAlgebra T) :=
  Fintype.toCompleteDistribLattice _

/-- The Lindenbaum algebra as a thin category (at most one morphism between objects).
Morphisms are `ULift (PLift (a ≤ b))`. -/
noncomputable instance : CategoryTheory.SmallCategory (LindenbaumAlgebra T) :=
  Preorder.smallCategory _

end LindenbaumAlgebra

end Propositional

end GeometricLogic
