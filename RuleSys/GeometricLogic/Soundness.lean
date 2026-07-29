/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Soundness Theorem and Bridge Lemmas

This file proves soundness of geometric logic by structural induction
on the `Provable` derivation, and establishes bridge lemmas relating
formula satisfaction to semantic properties.

## Theorems

- `Provable.sound`: Generic soundness — provable sequents hold in all models (PROVED)

## Axioms (2, retained — see elimination analysis in docstrings)

- `theoryOfSystem_complete_canonical`: Canonical model completeness bridge
  Obstruction: requires unfolding `systemSpecificAxioms` (itself axiomatized) +
  `geometric_completeness` (Barr's theorem, also axiomatized)
- `provability_separation_implies_topos_nonequiv`: Provability separation implies topos non-equivalence
  Obstruction: requires universal property of classifying toposes + Deligne's theorem

## Proved / Axiomatized

- `theoryOfSystem_complete`: Completeness via Barr's theorem (all models → provability)
- `canonicalModel_satisfies_theorySeq`: Canonical models satisfy their theories (via syntactic_sub_semantic)

## Bridge Lemmas

- `satisfiesSequent'_sigma_tot_iff`: σ_tot ↔ totality
- `satisfiesSequent'_sigma_det_iff`: σ_det ↔ determinism
- `satisfiesSequent'_sigma_conf_iff`: σ_conf ↔ weak confluence
- `satisfiesSequent'_sigma_loop_iff`: σ_loop ↔ universal self-loop

Note: System-specific provability axioms (pathSys_proves_sigma_tot,
twoCycle_proves_sigma_det) are in their respective separation files
to avoid circular imports.

## References

- Caramello, "Theories, Sites, Toposes" (2017), Corollary 2.1.12
-/

import RuleSys.GeometricLogic.Satisfaction
import RuleSys.GeometricLogic.SeparatingSequents
import RuleSys.GeometricLogic.SyntacticCategory

open FirstOrder Language GeometricLogic CategoryTheory

namespace GeometricLogic

/-!
## Soundness Theorem

Proved by structural induction on the `Provable` derivation.
-/

/-- **Generic soundness of geometric logic.**

    If a geometric sequent s is provable from theory T, then every
    RTSModel that satisfies T (as a set of sequents) also satisfies s.

    Proof: structural induction on the derivation.
    - `ax`: the model satisfies all axioms of T by hypothesis
    - `identity`: φ ⊢ φ holds trivially
    - `trivial`: ⊤ ⊢ ⊤ holds trivially
    - `cut`: compose the two induction hypotheses
    - `top_intro`: φ ⊢ ⊤ holds trivially
    - `bot_elim`: ⊥ ⊢ φ holds vacuously (False.elim)
    - `disj_intro_left/right`: Or.inl / Or.inr
    - `disj_elim`: case split on the disjunction
    - `exist_intro`: pick any witness (bound var unused via castLE)
    - `exist_elim`: Frobenius — distribute context into ∃ scope -/
theorem Provable.sound {α : Type} {s : GeoSequent RTSLanguage α}
    {T : GeometricTheory RTSLanguage} :
    Provable T s → ∀ m : RTSModel, satisfiesTheorySeq m T → satisfiesSequent' m s := by
  intro h
  induction h with
  | ax hmem => intro m hT; exact hT _ hmem
  | identity _ => intro _ _ _ hant; exact hant
  | trivial => intro _ _ _ _; trivial
  | cut _ _ ih₁ ih₂ =>
    intro m hT val hφ
    exact ih₂ m hT val (ih₁ m hT val hφ)
  | conj_intro _ _ ih₁ ih₂ =>
    intro m hT val hφ
    exact ⟨ih₁ m hT val hφ, ih₂ m hT val hφ⟩
  | conj_elim_left => intro _ _ val ⟨h, _⟩; exact h
  | conj_elim_right => intro _ _ val ⟨_, h⟩; exact h
  | weaken _ ih => intro m hT val ⟨hφ, _⟩; exact ih m hT val hφ
  | top_intro => intro _ _ _ _; trivial
  | bot_elim => intro _ _ _ h; exact h.elim
  | disj_intro_left => intro _ _ val hφ; exact Or.inl hφ
  | disj_intro_right => intro _ _ val hψ; exact Or.inr hψ
  | disj_elim _ _ ih₁ ih₂ =>
    intro m hT val ⟨hχ, hφψ⟩
    cases hφψ with
    | inl hφ => exact ih₁ m hT val ⟨hχ, hφ⟩
    | inr hψ => exact ih₂ m hT val ⟨hχ, hψ⟩
  | exist_intro =>
    intro m hT val hφ
    exact ⟨m.init, (satisfiesFormula_castLE (by omega) val _ _).mpr
      (by convert hφ)⟩
  | exist_elim =>
    intro m hT val ⟨hφ, c, hχ⟩
    exact ⟨c, (satisfiesFormula_castLE (by omega) val _ _).mpr
      (by convert hφ), hχ⟩

/-- **Completeness for the syntactic theory of M.**

    Every sequent satisfied by all models of T_M is provable from T_M.
    This is an instance of Barr's completeness theorem for geometric theories.

    With the syntactic definition of `theoryOfSystem`, completeness is a genuine
    theorem — it uses Barr's deep result (Caramello TST, Corollary 2.1.12),
    not the trivial `Provable.ax` that the previous semantic definition allowed.

    The hypothesis is strengthened: we require the sequent to hold in ALL models
    of T_M, not just the canonical model. This is the standard formulation. -/
theorem theoryOfSystem_complete (M : RTS.RootedTS) {α : Type}
    {s : GeoSequent RTSLanguage α}
    (h : ∀ m : RTSModel.{0}, satisfiesTheorySeq m (theoryOfSystem M) → satisfiesSequent' m s) :
    Provable (theoryOfSystem M) s :=
  FunctionalFormula.geometric_completeness h

/-- **Completeness via canonical model.**

    If the canonical model of M satisfies a geometric sequent s, then
    s is provable from T_M. This is a convenience corollary of
    `theoryOfSystem_complete` that preserves the old canonical-model-based API.

    The intended proof goes: canonical model satisfies s → every model of T_M
    satisfies s → (by `geometric_completeness` / Barr) → Provable T_M s.

    **Elimination analysis** (Phase 250-01):
    This axiom cannot be eliminated without first eliminating its two
    nested axiom dependencies:

    1. **`systemSpecificAxioms` (TheoryOfSystem.lean:239)**: The theory
       `theoryOfSystem M = rtsTheory ∪ systemSpecificAxioms M` includes
       system-specific axioms that are themselves axiomatized. The bridge from
       "canonical model satisfies s" to "all models of T_M satisfy s" requires
       knowing that `systemSpecificAxioms M` completely determines the step
       relation (existence + completeness axioms for each state). Without
       unfolding `systemSpecificAxioms`, we cannot show that an arbitrary
       model of T_M agrees with the canonical model.

    2. **`geometric_completeness` (SyntacticCategory.lean:482)**: Even if we
       could bridge to "all models satisfy s", the final step uses Barr's
       completeness theorem which is itself axiomatized.

    **Strategies attempted:**
    - Factor through `theoryOfSystem_complete`: blocked by (1) — cannot show
      arbitrary models agree with canonical model without `systemSpecificAxioms`
    - Instance-specific `Provable` proof terms: blocked by (1) — `Provable.ax`
      requires membership in `theoryOfSystem M`, which is opaque
    - Concrete axiom sets for pathSys/twoCycle/detCounter: blocked by (1)
    - Existing `syntactic_sub_semantic` bridge: goes wrong direction
      (theoryOfSystem → semanticTheoryOfSystem, not reverse)

    **Downstream uses** (3 sites):
    - `FirstSeparation.lean:300`: pathSys_proves_sigma_tot
    - `SecondSeparation.lean:274`: twoCycle_proves_sigma_det
    - `NonEquivalence.lean:241`: detCounter_proves_sigma_det -/
axiom theoryOfSystem_complete_canonical (M : RTS.RootedTS) {α : Type}
    (s : GeoSequent RTSLanguage α) :
    satisfiesSequent' (RTS.RootedTS.canonicalModel M) s →
    Provable (theoryOfSystem M) s

/-!
## Bridge Lemmas

These relate `satisfiesSequent'` on concrete sequents to semantic properties,
bridging the formula-level evaluation to direct semantic predicates.
-/

/-- σ_tot satisfaction ↔ totality (every state has a successor). -/
theorem satisfiesSequent'_sigma_tot_iff (m : RTSModel) :
    satisfiesSequent' m sigma_tot ↔ ∀ x : m.carrier, ∃ y : m.carrier, m.step x y := by
  constructor
  · intro h x
    have := h (fun _ => x) trivial
    simp only [sigma_tot, satisfiesFormula, stepRel, interpRel,
               evalTerm, varTerm, boundTerm] at this
    exact this
  · intro h val _
    obtain ⟨y, hy⟩ := h (val 0)
    exact ⟨y, hy⟩

/-- σ_det satisfaction ↔ determinism (functional step relation). -/
theorem satisfiesSequent'_sigma_det_iff (m : RTSModel) :
    satisfiesSequent' m sigma_det ↔
    ∀ x y z : m.carrier, m.step x y → m.step x z → y = z := by
  constructor
  · intro h x y z h1 h2
    have := h (![x, y, z]) ⟨h1, h2⟩
    simp only [sigma_det, satisfiesFormula, eqTerms, evalTerm, varTerm] at this
    exact this
  · intro h val ⟨h1, h2⟩
    exact h (val 0) (val 1) (val 2) h1 h2

/-- σ_conf satisfaction ↔ weak confluence. -/
theorem satisfiesSequent'_sigma_conf_iff (m : RTSModel) :
    satisfiesSequent' m sigma_conf ↔
    ∀ x y z : m.carrier, m.step x y → m.step x z →
      ∃ w : m.carrier, m.step y w ∧ m.step z w := by
  constructor
  · intro h x y z h1 h2
    have := h (![x, y, z]) ⟨h1, h2⟩
    simp only [sigma_conf, satisfiesFormula, stepRel, interpRel, evalTerm,
               varTerm, boundTerm] at this
    exact this
  · intro h val ⟨h1, h2⟩
    obtain ⟨w, hw1, hw2⟩ := h (val 0) (val 1) (val 2) h1 h2
    exact ⟨w, hw1, hw2⟩

/-- σ_loop satisfaction ↔ universal self-loop. -/
theorem satisfiesSequent'_sigma_loop_iff (m : RTSModel) :
    satisfiesSequent' m sigma_loop ↔ ∀ x : m.carrier, m.step x x := by
  constructor
  · intro h x
    have := h (fun _ => x) trivial
    simp only [sigma_loop, satisfiesFormula, stepVars, stepRel, interpRel,
               evalTerm, varTerm] at this
    exact this
  · intro h val _
    exact h (val 0)

/-- The canonical model of M satisfies theoryOfSystem M.

    With the syntactic definition, this follows from `syntactic_sub_semantic`:
    every axiom of T_M (= rtsTheory ∪ systemSpecificAxioms M) is satisfied
    by the canonical model, because the syntactic theory is a subtheory of the
    semantic closure. -/
theorem canonicalModel_satisfies_theorySeq (M : RTS.RootedTS) :
    satisfiesTheorySeq (RTS.RootedTS.canonicalModel M) (theoryOfSystem M) :=
  fun p hp => syntactic_sub_semantic M p hp

/-!
## Provability Separation Implies Topos Non-Equivalence

This is the universal property of classifying toposes: equivalent toposes
have the same provable sequents. Moved here from BranchingTopology.lean
to be available to all separation files without circular imports.
-/

/-- Provability separation implies topos non-equivalence.

    For geometric theories T₁, T₂ over the same language, if T₁ proves
    a sequent s that T₂ does not prove, then their classifying toposes
    are not equivalent.

    **Mathematical justification** (Caramello TST, §2.1):
    Equivalent classifying toposes have equivalent categories of models
    in every Grothendieck topos E. In particular, for E = Set, they have
    the same Set-models. By soundness + completeness of geometric logic
    (Caramello TST, Corollary 2.1.12), same models implies same provable
    sequents. Contrapositively, different provable sequents implies
    non-equivalent toposes.

    **Elimination analysis** (Phase 249-01):
    This axiom cannot be eliminated without introducing new axioms because
    its proof requires two ingredients that are both beyond current reach:

    1. **Universal property of classifying toposes**: The key missing link is
       showing that `Sheaf J₁ Type ≌ Sheaf J₂ Type` implies an equivalence
       of T-model categories `Mod(T₁, Set) ≃ Mod(T₂, Set)`. This requires
       formalizing the correspondence between geometric morphisms `Set → Sh(C,J)`
       and J-continuous flat functors `C → Set` (Caramello TST, Theorem 2.1.14),
       which constitutes a substantial amount of topos theory not in Mathlib.

    2. **Language generality**: The axiom is stated for arbitrary first-order
       languages L, but `geometric_completeness` (Barr's theorem) is only
       axiomatized for `RTSLanguage`. Even restricting to `RTSLanguage`
       would still require ingredient (1).

    3. **Deligne's theorem / enough points**: The "inverse" direction (topos
       equivalence → model equivalence) ultimately relies on coherent toposes
       having enough points (Deligne's theorem), which is deep topos theory
       not formalized in Mathlib.

    **Downstream uses** (4 sites, all with RTSLanguage theories):
    - `FirstSeparation.lean`: fork/pathSys via σ_tot
    - `SecondSeparation.lean`: hubSpokes/twoCycle via σ_det
    - `NonEquivalence.lean`: detCounter/binarySplit via σ_det
    - `BranchingTopology.lean`: detCounter/binarySplit via determinismSequent -/
axiom provability_separation_implies_topos_nonequiv
    {L : FirstOrder.Language.{0, 0}} {T₁ T₂ : GeometricTheory L}
    [Category (SyntacticCategory T₁)] [Category (SyntacticCategory T₂)]
    {α : Type} {s : GeoSequent L α}
    (h₁ : Provable T₁ s) (h₂ : ¬Provable T₂ s) :
    ¬Nonempty (ClassifyingTopos T₁ ≌ ClassifyingTopos T₂)

end GeometricLogic
