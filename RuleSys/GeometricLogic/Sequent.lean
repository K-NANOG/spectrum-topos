/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Geometric Sequents and Theories

This file defines geometric sequents and geometric theories, building on
the geometric formula infrastructure.

## Main Definitions

- `GeoSequent L α`: A geometric sequent φ ⊢ ψ in context α
- `GeometricTheory L`: A set of geometric sequents (a geometric theory)
- `GeometricTheory.empty`, `GeometricTheory.single`, `GeometricTheory.union`

## Implementation Notes

A geometric sequent `φ ⊢_ctx ψ` consists of an antecedent and consequent
formula, both in the same context α. The context type α indexes the free
variables available in both formulas.

A geometric theory is a set of sequents, potentially with different context
types. We use a Sigma type to package sequents with their contexts.

## References

- Caramello, "Theories, Sites, Toposes" (2017), Ch. 1-2
- Makkai & Reyes, "First Order Categorical Logic" (1977)
-/

import RuleSys.GeometricLogic.Formula

open FirstOrder Language

universe u v u'

namespace GeometricLogic

variable (L : Language.{u, v})

/-- A geometric sequent: φ ⊢_{ctx} ψ where ctx is the type α of free variables.

Both antecedent and consequent are sentences in context α (i.e., formulas with
no additional bound variables beyond those in α). -/
structure GeoSequent (α : Type u') where
  /-- The hypothesis formula (left side of ⊢) -/
  antecedent : GeoFormula L α 0
  /-- The conclusion formula (right side of ⊢) -/
  consequent : GeoFormula L α 0

namespace GeoSequent

variable {L} {α : Type u'}

/-- Create a sequent from ⊤ (true) to a formula: ⊤ ⊢ φ
    This represents "φ is provable" (an axiom with no hypothesis). -/
def axiom' (φ : GeoFormula L α 0) : GeoSequent L α :=
  { antecedent := .top, consequent := φ }

/-- The trivial sequent: ⊤ ⊢ ⊤ -/
def trivial : GeoSequent L α :=
  { antecedent := .top, consequent := .top }

/-- The identity sequent: φ ⊢ φ -/
def identity (φ : GeoFormula L α 0) : GeoSequent L α :=
  { antecedent := φ, consequent := φ }

/-- Map free variables through a function -/
def relabelFree {β : Type u'} (f : α → β) (s : GeoSequent L α) : GeoSequent L β :=
  { antecedent := s.antecedent.relabelFree f
    consequent := s.consequent.relabelFree f }

end GeoSequent

/-- A packaged sequent with its context type.
    This allows collecting sequents with different context types. -/
abbrev PackagedSequent (L : Language.{u, v}) := Σ α : Type u', GeoSequent L α

/-- A geometric theory is a collection of sequents over a common language.
    Different sequents may have different context types. -/
def GeometricTheory (L : Language.{u, v}) := Set (PackagedSequent L)

namespace GeometricTheory

variable {L : Language.{u, v}}

/-- The empty theory (no axioms) -/
def empty : GeometricTheory L := (∅ : Set (PackagedSequent L))

/-- Package a sequent with its context type -/
def package {α : Type u'} (s : GeoSequent L α) : PackagedSequent L := ⟨α, s⟩

/-- A theory with a single sequent -/
def single {α : Type u'} (s : GeoSequent L α) : GeometricTheory L :=
  ({package s} : Set (PackagedSequent L))

/-- Union of two theories -/
def union (T₁ T₂ : GeometricTheory L) : GeometricTheory L :=
  (T₁ ∪ T₂ : Set (PackagedSequent L))

/-- Add a sequent to a theory -/
def addSequent {α : Type u'} (T : GeometricTheory L) (s : GeoSequent L α) : GeometricTheory L :=
  (T ∪ single s : Set (PackagedSequent L))

/-- Check if a sequent is in the theory -/
def contains {α : Type u'} (T : GeometricTheory L) (s : GeoSequent L α) : Prop :=
  T (package s)

/-- Collect all sequents with a specific context type -/
def sequentsInContext (T : GeometricTheory L) (α : Type u') : Set (GeoSequent L α) :=
  { s | T (package s) }

end GeometricTheory

/-!
## Provability Relation

Provability for geometric theories, defined as an inductive type whose
constructors correspond to the structural rules of geometric logic.
The key properties are: axioms are provable, identity holds, cut is
admissible, and interpretations preserve provability.
-/

/-- A sequent is provable from a geometric theory if it can be derived
    using the structural rules of geometric logic.

    The constructors correspond to:
    - `ax`: axioms of the theory are provable
    - `identity`: reflexivity (φ ⊢ φ)
    - `trivial`: ⊤ ⊢ ⊤
    - `cut`: transitivity (φ ⊢ ψ and ψ ⊢ χ imply φ ⊢ χ)
    - `conj_intro`, `conj_elim_left`, `conj_elim_right`: conjunction rules
    - `weaken`: weakening (φ ⊢ χ implies φ ∧ ψ ⊢ χ)
    - `top_intro`: top introduction (φ ⊢ ⊤)
    - `bot_elim`: bottom elimination (⊥ ⊢ φ)
    - `disj_intro_left`, `disj_intro_right`, `disj_elim`: disjunction rules
    - `exist_intro`, `exist_elim`: existential quantification rules (Frobenius)

    **Paper reference:** Definition 2.14 of the paper requires provability preservation
    for interpretations: if T ⊢ φ ⊢_x ψ, then T' ⊢ I(φ) ⊢_x I(ψ). -/
inductive Provable {L : Language.{u, v}} (T : GeometricTheory L) {α : Type u'} :
    GeoSequent L α → Prop where
  /-- Axioms of a theory are provable -/
  | ax {s : GeoSequent L α} (h : T.contains s) : Provable T s
  /-- The identity sequent φ ⊢ φ is provable in any theory -/
  | identity (φ : GeoFormula L α 0) : Provable T (GeoSequent.identity φ)
  /-- The trivial sequent ⊤ ⊢ ⊤ is provable in any theory -/
  | trivial : Provable T (GeoSequent.trivial : GeoSequent L α)
  /-- Cut rule: if T ⊢ φ ⊢ ψ and T ⊢ ψ ⊢ χ, then T ⊢ φ ⊢ χ.
      This is the structural rule enabling composition of derivations. -/
  | cut {φ ψ χ : GeoFormula L α 0}
      (h₁ : Provable T ⟨φ, ψ⟩) (h₂ : Provable T ⟨ψ, χ⟩) : Provable T ⟨φ, χ⟩
  /-- Conjunction introduction: from φ ⊢ ψ and φ ⊢ χ, derive φ ⊢ ψ ∧ χ -/
  | conj_intro {φ ψ χ : GeoFormula L α 0}
      (h₁ : Provable T ⟨φ, ψ⟩) (h₂ : Provable T ⟨φ, χ⟩) : Provable T ⟨φ, .conj ψ χ⟩
  /-- Left conjunction elimination: φ ∧ ψ ⊢ φ -/
  | conj_elim_left {φ ψ : GeoFormula L α 0} : Provable T ⟨.conj φ ψ, φ⟩
  /-- Right conjunction elimination: φ ∧ ψ ⊢ ψ -/
  | conj_elim_right {φ ψ : GeoFormula L α 0} : Provable T ⟨.conj φ ψ, ψ⟩
  /-- Weakening: from φ ⊢ χ, derive φ ∧ ψ ⊢ χ -/
  | weaken {φ ψ χ : GeoFormula L α 0}
      (h : Provable T ⟨φ, χ⟩) : Provable T ⟨.conj φ ψ, χ⟩
  /-- Top introduction: φ ⊢ ⊤ for any formula φ -/
  | top_intro {φ : GeoFormula L α 0} : Provable T ⟨φ, .top⟩
  /-- Bottom elimination: ⊥ ⊢ φ for any formula φ (ex falso quodlibet) -/
  | bot_elim {φ : GeoFormula L α 0} : Provable T ⟨.bot, φ⟩
  /-- Left disjunction introduction: φ ⊢ φ ∨ ψ -/
  | disj_intro_left {φ ψ : GeoFormula L α 0} :
      Provable T ⟨φ, .disj φ ψ⟩
  /-- Right disjunction introduction: ψ ⊢ φ ∨ ψ -/
  | disj_intro_right {φ ψ : GeoFormula L α 0} :
      Provable T ⟨ψ, .disj φ ψ⟩
  /-- Disjunction elimination (Frobenius for ∨):
      if χ ∧ φ ⊢ ξ and χ ∧ ψ ⊢ ξ, then χ ∧ (φ ∨ ψ) ⊢ ξ.
      This is the context-preserving elimination rule for geometric logic. -/
  | disj_elim {φ ψ χ ξ : GeoFormula L α 0}
      (h₁ : Provable T ⟨.conj χ φ, ξ⟩)
      (h₂ : Provable T ⟨.conj χ ψ, ξ⟩) :
      Provable T ⟨.conj χ (.disj φ ψ), ξ⟩
  /-- Existential introduction: φ ⊢ ∃x.φ̂ where φ̂ is φ cast to include
      an unused bound variable. If φ holds, then ∃x.φ̂ holds trivially
      (pick any witness; x is unused in φ̂). -/
  | exist_intro {φ : GeoFormula L α 0} :
      Provable T ⟨φ, .exist (GeoFormula.castLE (by omega) φ)⟩
  /-- Existential elimination (Frobenius for ∃):
      φ ∧ (∃x.χ) ⊢ ∃x.(φ̂ ∧ χ) where φ̂ = castLE φ.
      The context formula φ distributes into the existential scope.
      This is the Frobenius reciprocity characterizing geometric ∃. -/
  | exist_elim {φ : GeoFormula L α 0} {χ : GeoFormula L α 1} :
      Provable T ⟨.conj φ (.exist χ), .exist (.conj (GeoFormula.castLE (by omega) φ) χ)⟩

/-!
## Notation

Scoped notation for constructing sequents and provability.
-/

scoped notation:25 φ " ⊢ₛ " ψ => GeoSequent.mk φ ψ

/-- Notation for provability: T ⊢ s means s is provable from theory T -/
scoped notation:25 T " ⊢ " s => Provable T s

end GeometricLogic
