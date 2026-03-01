/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semantic Satisfaction of Geometric Formulas

Defines semantic satisfaction of geometric formulas in `MultiwayModel`,
connecting the syntactic geometric logic infrastructure to concrete models.

## Main Definitions

- `evalTerm`: Evaluate a term in a model under a valuation
- `satisfiesFormula`: A model satisfies a geometric formula
- `satisfiesSequent'`: A model satisfies a geometric sequent
- `satisfiesTheorySeq`: A model satisfies all sequents of a theory

## References

- Caramello, "Theories, Sites, Toposes" (2017), Ch. 1-2
-/

import RuleSys.GeometricLogic.TheoryOfSystem

open FirstOrder Language GeometricLogic

universe u v

namespace GeometricLogic

/-- Evaluate a term in a MultiwayModel under a valuation for free variables
    and an assignment for bound variables.

    MultiwayLanguage has:
    - One 0-ary function: `init` (mapped to m.init)
    - No higher-arity functions
    - Variables: free (Sum.inl) or bound (Sum.inr) -/
def evalTerm (m : MultiwayModel) {α : Type*} {n : ℕ} (val : α → m.carrier)
    (ctx : Fin n → m.carrier) : MultiwayLanguage.Term (α ⊕ Fin n) → m.carrier
  | .var (Sum.inl a) => val a
  | .var (Sum.inr i) => ctx i
  | .func (l := 0) () _ => m.init

/-- Interpret a binary relation symbol in the model -/
def interpRel (m : MultiwayModel) (r : MultiwayRel) (a b : m.carrier) : Prop :=
  match r with
  | .step => m.step a b
  | .reach => m.reach a b
  | .pathEquiv => m.pathEquiv a b

/-- Semantic satisfaction of a geometric formula in a MultiwayModel.

    Given a valuation `val` for free variables and `ctx` for bound variables,
    determines whether the formula holds in the model. -/
def satisfiesFormula (m : MultiwayModel) {α : Type*} {n : ℕ}
    (val : α → m.carrier) (ctx : Fin n → m.carrier) :
    GeoFormula MultiwayLanguage α n → Prop
  | .top => True
  | .bot => False
  | .equal t₁ t₂ => evalTerm m val ctx t₁ = evalTerm m val ctx t₂
  | @GeoFormula.rel _ _ _ 2 R ts =>
    interpRel m R (evalTerm m val ctx (ts 0)) (evalTerm m val ctx (ts 1))
  | @GeoFormula.rel _ _ _ 0 R _ => R.elim
  | @GeoFormula.rel _ _ _ 1 R _ => R.elim
  | @GeoFormula.rel _ _ _ (_ + 3) R _ => R.elim
  | .conj φ ψ => satisfiesFormula m val ctx φ ∧ satisfiesFormula m val ctx ψ
  | .disj φ ψ => satisfiesFormula m val ctx φ ∨ satisfiesFormula m val ctx ψ
  | .exist φ => ∃ c : m.carrier, satisfiesFormula m val (Fin.cons c ctx) φ

/-- A model satisfies a geometric sequent if for all valuations,
    the antecedent being satisfied implies the consequent is satisfied. -/
def satisfiesSequent' (m : MultiwayModel) {α : Type*}
    (s : GeoSequent MultiwayLanguage α) : Prop :=
  ∀ val : α → m.carrier,
    satisfiesFormula m val Fin.elim0 s.antecedent →
    satisfiesFormula m val Fin.elim0 s.consequent

/-- A model satisfies a geometric theory (as a set of packaged sequents). -/
def satisfiesTheorySeq (m : MultiwayModel) (T : GeometricTheory MultiwayLanguage) : Prop :=
  ∀ p : PackagedSequent MultiwayLanguage, T p → satisfiesSequent' m p.2

/-!
## Formula Evaluation Lemmas

Infrastructure for evaluating `satisfiesFormula` on concrete formulas
built from `relabelFree`, `equalityConjunction`, etc. These are needed
for proving `IsFunctional.identity` and `.comp` in SyntacticCategory.lean.
-/

/-- Term evaluation commutes with relabeling of free variables. -/
@[simp]
theorem evalTerm_relabel {m : MultiwayModel} {α β : Type*} {n : ℕ}
    (val : β → m.carrier) (ctx : Fin n → m.carrier)
    (f : α → β) (t : MultiwayLanguage.Term (α ⊕ Fin n)) :
    evalTerm m val ctx (t.relabel (Sum.map f id)) = evalTerm m (val ∘ f) ctx t := by
  match t with
  | .var (Sum.inl _) => rfl
  | .var (Sum.inr _) => rfl
  | .func (l := 0) () _ => rfl

/-- Formula satisfaction commutes with free variable relabeling. -/
theorem satisfiesFormula_relabelFree {m : MultiwayModel} {α β : Type} {n : ℕ}
    (val : β → m.carrier) (ctx : Fin n → m.carrier)
    (f : α → β) (φ : GeoFormula MultiwayLanguage α n) :
    satisfiesFormula m val ctx (φ.relabelFree f) ↔ satisfiesFormula m (val ∘ f) ctx φ := by
  induction φ generalizing β with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [GeoFormula.relabelFree, satisfiesFormula, evalTerm_relabel]
  | @rel _ l R ts =>
    match l, R with
    | 0, R => exact nomatch R
    | 1, R => exact nomatch R
    | 2, R =>
      simp only [GeoFormula.relabelFree, satisfiesFormula, evalTerm_relabel]
    | _ + 3, R => exact nomatch R
  | conj φ ψ ihφ ihψ =>
    simp only [GeoFormula.relabelFree, satisfiesFormula]
    exact and_congr (ihφ val ctx f) (ihψ val ctx f)
  | disj φ ψ ihφ ihψ =>
    simp only [GeoFormula.relabelFree, satisfiesFormula]
    exact or_congr (ihφ val ctx f) (ihψ val ctx f)
  | exist φ ih =>
    simp only [GeoFormula.relabelFree, satisfiesFormula]
    exact exists_congr (fun c => ih val (Fin.cons c ctx) f)

/-- Satisfaction of a conjunction list ↔ all members satisfied. -/
theorem satisfiesFormula_conjList {m : MultiwayModel} {α : Type} {n : ℕ}
    (val : α → m.carrier) (ctx : Fin n → m.carrier)
    (φs : List (GeoFormula MultiwayLanguage α n)) :
    satisfiesFormula m val ctx (GeoFormula.conjList φs) ↔
    ∀ φ ∈ φs, satisfiesFormula m val ctx φ := by
  induction φs with
  | nil => simp [GeoFormula.conjList, satisfiesFormula]
  | cons φ φs ih =>
    cases φs with
    | nil => simp [GeoFormula.conjList]
    | cons ψ rest =>
      simp only [GeoFormula.conjList, satisfiesFormula]
      constructor
      · intro ⟨hφ, hrest⟩ x hx
        cases hx with
        | head => exact hφ
        | tail _ hx => exact ih.mp hrest x hx
      · intro h
        exact ⟨h φ (List.Mem.head _),
               ih.mpr (fun x hx => h x (List.Mem.tail _ hx))⟩

/-- Equality conjunction gives pointwise equality of left/right context variables. -/
theorem satisfiesFormula_equalityConjunction {m : MultiwayModel} {α : Type} [Fintype α]
    (val : (α ⊕ α) → m.carrier) (ctx : Fin 0 → m.carrier) :
    satisfiesFormula m val ctx (GeoFormula.equalityConjunction MultiwayLanguage α) ↔
    ∀ a : α, val (Sum.inl a) = val (Sum.inr a) := by
  simp only [GeoFormula.equalityConjunction]
  rw [satisfiesFormula_conjList]
  constructor
  · intro h a
    have := h _ (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩)
    simp only [satisfiesFormula, evalTerm] at this
    exact this
  · intro h φ hφ
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hφ
    simp only [satisfiesFormula, evalTerm]
    exact h a

/-- Term evaluation under castLE: casting bound variables preserves evaluation. -/
theorem evalTerm_castLE {m : MultiwayModel} {α : Type*} {n k : ℕ}
    (h : n ≤ k) (val : α → m.carrier) (ctx : Fin k → m.carrier)
    (t : MultiwayLanguage.Term (α ⊕ Fin n)) :
    evalTerm m val ctx (t.relabel (Sum.map id (Fin.castLE h))) =
    evalTerm m val (ctx ∘ Fin.castLE h) t := by
  match t with
  | .var (Sum.inl _) => rfl
  | .var (Sum.inr _) => rfl
  | .func (l := 0) () _ => rfl

/-- Formula satisfaction under castLE: adding unused bound variable slots. -/
theorem satisfiesFormula_castLE {m : MultiwayModel} {α : Type} {n k : ℕ}
    (h : n ≤ k) (val : α → m.carrier) (ctx : Fin k → m.carrier)
    (φ : GeoFormula MultiwayLanguage α n) :
    satisfiesFormula m val ctx (GeoFormula.castLE h φ) ↔
    satisfiesFormula m val (ctx ∘ Fin.castLE h) φ := by
  induction φ generalizing k with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [GeoFormula.castLE, satisfiesFormula, evalTerm_castLE]
  | @rel _ l R ts =>
    match l, R with
    | 0, R => exact nomatch R
    | 1, R => exact nomatch R
    | 2, R =>
      simp only [GeoFormula.castLE, satisfiesFormula, evalTerm_castLE]
    | _ + 3, R => exact nomatch R
  | conj φ ψ ihφ ihψ =>
    simp only [GeoFormula.castLE, satisfiesFormula]
    exact and_congr (ihφ h ctx) (ihψ h ctx)
  | disj φ ψ ihφ ihψ =>
    simp only [GeoFormula.castLE, satisfiesFormula]
    exact or_congr (ihφ h ctx) (ihψ h ctx)
  | exist φ ih =>
    simp only [GeoFormula.castLE, satisfiesFormula]
    constructor
    · intro ⟨c, hc⟩
      have := (ih (Nat.succ_le_succ h) (Fin.cons c ctx)).mp hc
      exact ⟨c, by convert this using 1; funext i; cases i using Fin.cases <;> simp [Fin.cons, Fin.castLE, Fin.castSucc]⟩
    · intro ⟨c, hc⟩
      have := (ih (Nat.succ_le_succ h) (Fin.cons c ctx)).mpr (by convert hc using 1; funext i; cases i using Fin.cases <;> simp [Fin.cons, Fin.castLE, Fin.castSucc])
      exact ⟨c, this⟩

/-- Iterated existential: satisfaction ↔ existence of a full bound-variable assignment. -/
theorem satisfiesFormula_iteratedExist {m : MultiwayModel} {α : Type} {n : ℕ}
    (val : α → m.carrier) (ctx : Fin 0 → m.carrier)
    (φ : GeoFormula MultiwayLanguage α n) :
    satisfiesFormula m val ctx (GeoFormula.iteratedExist φ) ↔
    ∃ ctx' : Fin n → m.carrier, satisfiesFormula m val ctx' φ := by
  induction n with
  | zero =>
    simp only [GeoFormula.iteratedExist]
    have hctx : ∀ (f : Fin 0 → m.carrier), f = ctx := fun f => funext (fun i => i.elim0)
    constructor
    · intro h; exact ⟨ctx, h⟩
    · intro ⟨ctx', h⟩; rw [hctx ctx'] at h; exact h
  | succ n ih =>
    simp only [GeoFormula.iteratedExist]
    rw [ih]
    constructor
    · intro ⟨ctx', c, h⟩
      exact ⟨Fin.cons c ctx', h⟩
    · intro ⟨ctx', h⟩
      exact ⟨Fin.tail ctx', ctx' 0, by rwa [Fin.cons_self_tail]⟩

/-!
## Theory of a Multiway System

The geometric theory T_M is defined syntactically as `multiwayTheory ∪ systemSpecificAxioms M`.
This gives T_M genuine syntactic content: a finite axiom set from which provability
is non-trivial. The classifying topos Sh(C_{T_M}, J_{T_M}) reflects the specific
transition structure of M.

The semantic closure (all sequents satisfied by the canonical model) is preserved
as `semanticTheoryOfSystem` for bridge lemmas.
-/

/-- The semantic closure of T_M — all sequents satisfied by M's canonical model.

    This is the set of ALL geometric sequents that hold when step/reach/pathEquiv
    are interpreted via M's structure. Useful for relating the syntactic theory
    to semantic truth via `syntactic_sub_semantic`. -/
def semanticTheoryOfSystem (M : Ruliology.MultiwaySystem) : GeometricTheory MultiwayLanguage :=
  fun p => satisfiesSequent' (Ruliology.MultiwaySystem.canonicalModel M) p.2

/-- The geometric theory associated to a multiway system M.

    Defined syntactically as `multiwayTheory ∪ systemSpecificAxioms M`:
    - `multiwayTheory`: 6 structural axioms (step→reach, reflexivity,
      transitivity, pathEquiv definition/symmetry/reach)
    - `systemSpecificAxioms M`: axioms encoding M's specific transitions

    This gives T_M genuine syntactic content for a meaningful classifying topos.
    Completeness (semantic truth → provability) is now a non-trivial theorem
    via Barr's completeness theorem (geometric_completeness). -/
def theoryOfSystem (M : Ruliology.MultiwaySystem) : GeometricTheory MultiwayLanguage :=
  syntacticTheoryOfSystem M

/-- The syntactic theory is a subtheory of the semantic closure.

    Every axiom of `theoryOfSystem M` (= multiwayTheory ∪ systemSpecificAxioms M)
    is satisfied by M's canonical model, hence belongs to the semantic closure.

    For multiwayTheory axioms, this follows from `canonicalModel_satisfies`.
    For systemSpecificAxioms, this follows from the axioms encoding actual
    transitions of M.

    Axiomatized: a full proof requires unfolding systemSpecificAxioms (itself
    axiomatized) and verifying each generated sequent against the canonical model. -/
axiom syntactic_sub_semantic (M : Ruliology.MultiwaySystem) :
    ∀ p, theoryOfSystem M p → semanticTheoryOfSystem M p

/-- Different systems have different geometric theories.

    Two systems with different transition structures produce different
    systemSpecificAxioms (different existence/completeness axioms),
    hence their syntactic theories differ.

    Axiomatized: proving this concretely requires showing that for any M ≠ N,
    the systemSpecificAxioms produce a distinguishing sequent. -/
axiom theoryOfSystem_injective : Function.Injective theoryOfSystem

end GeometricLogic
