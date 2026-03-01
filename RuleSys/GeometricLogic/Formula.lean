/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Formulas

This file defines geometric formulas, the fragment of first-order logic
used in topos-theoretic characterizations. Geometric logic uses only:
- ⊤ (truth)
- ⊥ (falsity)
- ∧ (conjunction)
- ⋁ (disjunction - binary, with finitary extension)
- ∃ (existential quantification)
- = (equality)

Notably absent: ¬, ⇒, ∀

## Main Definitions

- `GeoFormula L α n`: geometric formulas over language L with free variables α
  and n bound variables
- `GeoFormula.subst`: substitution of variables
- `GeoFormula.disjFin`: finitary disjunction

## Implementation Notes

We follow Mathlib's `BoundedFormula` pattern: the number of bound variables
is a ℕ parameter, and bound variables are indexed by `Fin n`. This avoids
universe issues with nested inductives.

## References

- Caramello, "Theories, Sites, Toposes" (2017)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992)
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language

universe u v u'

namespace GeometricLogic

variable (L : Language.{u, v}) (α : Type u')

/-- Geometric formulas: the fragment of FOL with ⊤, ⊥, ∧, ⋁, ∃, =.

Following Mathlib's `BoundedFormula` pattern:
- `α` indexes the free variables
- `n` is the number of bound variables in scope
- Bound variables are indexed by `Fin n`

The existential `exist φ` binds one new variable, so `φ : GeoFormula L α (n+1)`. -/
inductive GeoFormula : ℕ → Type max u v u'
  | top {n} : GeoFormula n
  | bot {n} : GeoFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : GeoFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : GeoFormula n
  | conj {n} (φ ψ : GeoFormula n) : GeoFormula n
  | disj {n} (φ ψ : GeoFormula n) : GeoFormula n
  | exist {n} (φ : GeoFormula (n + 1)) : GeoFormula n

/-- A geometric formula with no bound variables -/
abbrev GeoSentence := GeoFormula L α 0

namespace GeoFormula

variable {L} {α}
variable {n : ℕ}

/-- Finitary disjunction (left-associative) -/
def disjList : List (GeoFormula L α n) → GeoFormula L α n
  | [] => .bot
  | [φ] => φ
  | φ :: φs => .disj φ (disjList φs)

/-- Finitary disjunction over Fin m -/
def disjFin {m : ℕ} (φs : Fin m → GeoFormula L α n) : GeoFormula L α n :=
  disjList (List.ofFn φs)

/-- Finitary conjunction (left-associative) -/
def conjList : List (GeoFormula L α n) → GeoFormula L α n
  | [] => .top
  | [φ] => φ
  | φ :: φs => .conj φ (conjList φs)

/-- Cast to more bound variables -/
def castLE : ∀ {n m : ℕ}, n ≤ m → GeoFormula L α n → GeoFormula L α m
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, h, .equal t₁ t₂ =>
    .equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, .conj φ ψ => .conj (castLE h φ) (castLE h ψ)
  | _, _, h, .disj φ ψ => .disj (castLE h φ) (castLE h ψ)
  | _, _, h, .exist φ => .exist (castLE (Nat.succ_le_succ h) φ)

variable {β : Type u'} {γ : Type u'}

/-- Relabel free variables in a formula -/
def relabelFree : ∀ {n : ℕ}, (α → β) → GeoFormula L α n → GeoFormula L β n
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, g, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map g id)) (t₂.relabel (Sum.map g id))
  | _, g, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map g id))
  | _, g, .conj φ ψ => .conj (relabelFree g φ) (relabelFree g ψ)
  | _, g, .disj φ ψ => .disj (relabelFree g φ) (relabelFree g ψ)
  | _, g, .exist φ => .exist (relabelFree g φ)

/-- Substitution of free variables with terms -/
def subst : ∀ {n : ℕ}, GeoFormula L α n → (α → L.Term β) → GeoFormula L β n
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .equal t₁ t₂, σ =>
    .equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr)))
           (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr)))
  | _, .rel R ts, σ =>
    .rel R (fun i => (ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr)))
  | _, .conj φ ψ, σ => .conj (subst φ σ) (subst ψ σ)
  | _, .disj φ ψ, σ => .disj (subst φ σ) (subst ψ σ)
  | _, .exist φ, σ => .exist (subst φ σ)

/-- Lift free variables to include one additional bound variable (context extension) -/
def liftAt (k : ℕ) : ∀ {n : ℕ}, GeoFormula L α n → GeoFormula L α (n + 1)
  | _, .top => .top
  | _, .bot => .bot
  | _, .equal t₁ t₂ =>
    let lift_fn := fun x : α ⊕ Fin _ => match x with
      | Sum.inl a => Sum.inl a
      | Sum.inr i => Sum.inr (if i.val < k then i.castSucc else i.succ)
    .equal (t₁.relabel lift_fn) (t₂.relabel lift_fn)
  | n, .rel R ts =>
    let lift_fn := fun x : α ⊕ Fin n => match x with
      | Sum.inl a => Sum.inl a
      | Sum.inr i => Sum.inr (if i.val < k then i.castSucc else i.succ)
    .rel R (fun i => (ts i).relabel lift_fn)
  | _, .conj φ ψ => .conj (liftAt k φ) (liftAt k ψ)
  | _, .disj φ ψ => .disj (liftAt k φ) (liftAt k ψ)
  | _, .exist φ => .exist (liftAt (k + 1) φ)

-- Basic substitution lemmas

@[simp]
theorem subst_top' (σ : α → L.Term β) : subst (GeoFormula.top (L := L) (α := α) (n := n)) σ = .top := rfl

@[simp]
theorem subst_bot' (σ : α → L.Term β) : subst (GeoFormula.bot (L := L) (α := α) (n := n)) σ = .bot := rfl

@[simp]
theorem subst_conj' (φ ψ : GeoFormula L α n) (σ : α → L.Term β) :
    subst (φ.conj ψ) σ = (subst φ σ).conj (subst ψ σ) := rfl

@[simp]
theorem subst_disj' (φ ψ : GeoFormula L α n) (σ : α → L.Term β) :
    subst (φ.disj ψ) σ = (subst φ σ).disj (subst ψ σ) := rfl

-- Relabeling lemmas

theorem relabelFree_id' (φ : GeoFormula L α n) : relabelFree id φ = φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | equal t₁ t₂ =>
    simp only [relabelFree]
    congr 1 <;> rw [Sum.map_id_id, Term.relabel_id]
  | rel R ts =>
    simp only [relabelFree]
    congr 1
    funext i
    rw [Sum.map_id_id, Term.relabel_id]
  | conj φ ψ ihφ ihψ =>
    simp only [relabelFree]
    rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [relabelFree]
    rw [ihφ, ihψ]
  | exist φ ih =>
    simp only [relabelFree]
    rw [ih]

theorem relabelFree_comp' (f : α → β) (g : β → γ) (φ : GeoFormula L α n) :
    relabelFree g (relabelFree f φ) = relabelFree (g ∘ f) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | equal t₁ t₂ =>
    simp only [relabelFree]
    congr 1 <;> (rw [Term.relabel_relabel, Sum.map_comp_map]; simp only [Function.comp_id])
  | rel R ts =>
    simp only [relabelFree]
    congr 1
    funext i
    rw [Term.relabel_relabel, Sum.map_comp_map]
    simp only [Function.comp_id]
  | conj φ ψ ihφ ihψ =>
    simp only [relabelFree]
    rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [relabelFree]
    rw [ihφ, ihψ]
  | exist φ ih =>
    simp only [relabelFree]
    rw [ih]

/-!
## Notation and Aliases

Convenience aliases for formula construction. Note that geometric logic does NOT
include implication (⇒) or negation (¬) as primitives. In sequent calculus,
implication is represented at the sequent level: `φ ⊢ ψ` rather than `φ ⇒ ψ`.
-/

/-- Alias for conjunction (for notation compatibility) -/
abbrev and' (φ ψ : GeoFormula L α n) : GeoFormula L α n := φ.conj ψ

/-- Alias for disjunction (for notation compatibility) -/
abbrev or' (φ ψ : GeoFormula L α n) : GeoFormula L α n := φ.disj ψ

/-- Finitary conjunction over Fin m -/
def conjFin {m : ℕ} (φs : Fin m → GeoFormula L α n) : GeoFormula L α n :=
  conjList (List.ofFn φs)

/-!
## Formula Infrastructure for Syntactic Categories

These definitions support concrete construction of identity and composition
relations in the syntactic category (SyntacticCategory.lean).
-/

/-- Iterated existential quantification: ∃x₁...∃xₙ. φ

    Wraps a formula with n bound variables in n existential quantifiers,
    producing a sentence (0 bound variables). -/
def iteratedExist : ∀ {n : ℕ}, GeoFormula L α n → GeoFormula L α 0
  | 0, φ => φ
  | _ + 1, φ => iteratedExist (.exist φ)

/-- General substitution: maps free variables to terms that may reference
    both free variables and bound variables.

    Unlike `subst` (which maps α → L.Term β, keeping free vars as free vars),
    this maps α → L.Term (β ⊕ Fin n), allowing free variables to be replaced
    with bound variable references. This is essential for `captureFreeVars`.

    Under existential quantifiers, bound variable references in the
    substitution are shifted by `Fin.succ` to account for the new binding. -/
def substGeneral : ∀ {n : ℕ},
    GeoFormula L α n → (α → L.Term (β ⊕ Fin n)) → GeoFormula L β n
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .equal t₁ t₂, σ =>
    .equal (t₁.subst (Sum.elim σ (Term.var ∘ Sum.inr)))
           (t₂.subst (Sum.elim σ (Term.var ∘ Sum.inr)))
  | _, .rel R ts, σ =>
    .rel R (fun i => (ts i).subst (Sum.elim σ (Term.var ∘ Sum.inr)))
  | _, .conj φ ψ, σ => .conj (substGeneral φ σ) (substGeneral ψ σ)
  | _, .disj φ ψ, σ => .disj (substGeneral φ σ) (substGeneral ψ σ)
  | _, .exist φ, σ => .exist (substGeneral φ
      (fun a => (σ a).relabel (Sum.map id Fin.succ)))

/-- Convert free variables of type β into bound variables.

    Given a formula with free vars (α ⊕ β) and 0 bound vars, produces a
    formula with free vars α and |β| bound vars, where each β-element is
    mapped to a unique Fin index via `Fintype.equivFin`.

    Combined with `iteratedExist`, this enables existential quantification
    over a finite set of free variables — the key operation for defining
    composition in the syntactic category. -/
noncomputable def captureFreeVars [Fintype β] :
    GeoFormula L (α ⊕ β) 0 → GeoFormula L α (Fintype.card β) :=
  fun φ =>
    let φ' := φ.castLE (Nat.zero_le _)
    substGeneral φ' (fun v => match v with
      | Sum.inl a => Term.var (Sum.inl a)
      | Sum.inr b => Term.var (Sum.inr ((Fintype.equivFin β) b)))

/-- Conjunction of equalities between left and right copies of context variables:
    ⋀_{a ∈ α} (inl a = inr a).

    In the context (α ⊕ α), asserts that every variable in the left copy (domain)
    equals the corresponding variable in the right copy (codomain). This is the
    building block for the diagonal/identity relation in the syntactic category. -/
noncomputable def equalityConjunction (L : Language.{u, v}) (α : Type u') [Fintype α] :
    GeoFormula L (α ⊕ α) 0 :=
  GeoFormula.conjList (Finset.univ.toList.map fun a =>
    GeoFormula.equal
      (Term.var (Sum.inl (Sum.inl a)))
      (Term.var (Sum.inl (Sum.inr a))))

end GeoFormula

end GeometricLogic
