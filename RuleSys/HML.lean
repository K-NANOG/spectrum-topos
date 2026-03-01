/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Diamond-Only Hennessy-Milner Logic (HML)

This file defines the diamond-only fragment of Hennessy-Milner logic and proves
it is bisimulation-invariant. This characterizes the fragment of geometric logic
preserved by bisimulation.

## Geometric van Benthem Conjecture

A geometric sequent is bisimulation-invariant iff its consequent is equivalent
to the standard translation of a diamond-only HML formula. The forward direction
(HML → bisimulation-invariant) is proved here. The backward direction is conjectured.

## Main Results

1. `HML` — Diamond-only modal formulas: {⊤, ⊥, ∧, ∨, ◇}
2. `HML.satisfiedAt` — Kripke semantics over multiway systems
3. `HML.bisim_invariant` — HML is bisimulation-invariant (forward direction)

## Three Separating Mechanisms

Geometric logic extends HML via three mechanisms, each breaking bisimulation
invariance by imposing implicit identification constraints:

1. **Consequent equality**: `step(x,y) ∧ step(x,z) ⊢ y=z` (σ_det)
2. **Cyclic variable sharing**: `step(x,y) ∧ step(x,z) ⊢ ∃w.step(y,w) ∧ step(z,w)` (σ_conf)
3. **Repeated variables in atoms**: `⊤ ⊢ step(x,x)` (σ_loop)

All three assert that two "positions" are filled by the same state.
Bisimulation can split any state into copies, breaking all three.

The standard translation of diamond-only HML avoids all three:
- Each `∃y.(step(x,y) ∧ ...)` introduces a fresh variable
- No variable appears in two argument positions of any atom
- No cyclic sharing between existential witnesses

Witnesses are in HMLSeparation.lean.

## References

- van Benthem, "Modal Correspondence Theory" (1976)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
-/

import RuleSys.Bisimulation

namespace Ruliology

universe u v

/-!
## Part 1: HML Definition and Semantics
-/

/-- Diamond-only Hennessy-Milner Logic.

    The fragment of modal logic with only ◇ (diamond), no □ (box) or ¬ (negation).
    Under the standard translation, this maps to tree-shaped equality-free
    positive existential first-order formulas — a strict subfragment of
    geometric logic.

    - `top`: ⊤ (tautology)
    - `bot`: ⊥ (contradiction)
    - `conj φ ψ`: φ ∧ ψ
    - `disj φ ψ`: φ ∨ ψ
    - `diamond φ`: ◇φ = ∃y.(step(x, y) ∧ φ(y)) -/
inductive HML : Type
  | top     : HML
  | bot     : HML
  | conj    : HML → HML → HML
  | disj    : HML → HML → HML
  | diamond : HML → HML

namespace HML

/-- Kripke semantics: `φ.satisfiedAt M s` holds when state `s` in system `M`
    satisfies the HML formula `φ`.

    The diamond modality uses the step relation of the multiway system:
    `◇φ` holds at `s` iff there exists `t` with `step(s, t)` and `φ` holds at `t`. -/
def satisfiedAt (M : MultiwaySystem.{u, v}) (s : M.State) : HML → Prop
  | .top => True
  | .bot => False
  | .conj φ ψ => φ.satisfiedAt M s ∧ ψ.satisfiedAt M s
  | .disj φ ψ => φ.satisfiedAt M s ∨ ψ.satisfiedAt M s
  | .diamond φ => ∃ t, Nonempty (M.Step s t) ∧ φ.satisfiedAt M t

/-- System-level validity: `φ` holds at every state of `M`. -/
def validIn (M : MultiwaySystem.{u, v}) (φ : HML) : Prop :=
  ∀ s : M.State, φ.satisfiedAt M s

/-!
## Part 2: Bisimulation Invariance

The main theorem: HML formulas are invariant under relational bisimulation.
The proof is structural induction on the formula. The diamond case uses
the forth/back conditions of the bisimulation to lift witnesses.
-/

/-- HML is preserved forward: if `(s, t) ∈ R` and `φ` holds at `s`, then `φ` holds at `t`.

    **Proof:** Structural induction on `φ`.
    - `diamond φ`: From `∃s'. step(s,s') ∧ φ(s')` and the forth condition of `R`,
      obtain `t'` with `step(t,t')` and `(s',t') ∈ R`. By IH, `φ(t')`. -/
theorem bisim_invariant_forth
    {M N : MultiwaySystem.{u, v}} {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    (φ : HML) : ∀ {s : M.State} {t : N.State}, R s t →
    φ.satisfiedAt M s → φ.satisfiedAt N t := by
  induction φ with
  | top => intros; trivial
  | bot => intro _ _ _ h; exact h.elim
  | conj φ ψ ihφ ihψ =>
    intro s t hst ⟨h1, h2⟩
    exact ⟨ihφ hst h1, ihψ hst h2⟩
  | disj φ ψ ihφ ihψ =>
    intro s t hst h
    exact h.elim (fun h1 => Or.inl (ihφ hst h1)) (fun h2 => Or.inr (ihψ hst h2))
  | diamond φ ih =>
    intro s t hst ⟨s', hs', hφ⟩
    obtain ⟨t', ht', hR'⟩ := hR.1 s t hst s' hs'
    exact ⟨t', ht', ih hR' hφ⟩

/-- HML is preserved backward: if `(s, t) ∈ R` and `φ` holds at `t`, then `φ` holds at `s`.

    **Proof:** Same argument using the back condition. -/
theorem bisim_invariant_back
    {M N : MultiwaySystem.{u, v}} {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    (φ : HML) : ∀ {s : M.State} {t : N.State}, R s t →
    φ.satisfiedAt N t → φ.satisfiedAt M s := by
  induction φ with
  | top => intros; trivial
  | bot => intro _ _ _ h; exact h.elim
  | conj φ ψ ihφ ihψ =>
    intro s t hst ⟨h1, h2⟩
    exact ⟨ihφ hst h1, ihψ hst h2⟩
  | disj φ ψ ihφ ihψ =>
    intro s t hst h
    exact h.elim (fun h1 => Or.inl (ihφ hst h1)) (fun h2 => Or.inr (ihψ hst h2))
  | diamond φ ih =>
    intro s t hst ⟨t', ht', hφ⟩
    obtain ⟨s', hs', hR'⟩ := hR.2 s t hst t' ht'
    exact ⟨s', hs', ih hR' hφ⟩

/-- **Bisimulation Invariance of HML.**

    HML formulas are invariant under relational bisimulation:
    if `R` is a bisimulation and `(s, t) ∈ R`, then `φ` holds at `s` iff at `t`.

    This is the forward direction of the geometric van Benthem conjecture. -/
theorem bisim_invariant
    {M N : MultiwaySystem.{u, v}} {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    (φ : HML) {s : M.State} {t : N.State} (hst : R s t) :
    φ.satisfiedAt M s ↔ φ.satisfiedAt N t :=
  ⟨bisim_invariant_forth hR φ hst, bisim_invariant_back hR φ hst⟩

/-- System-level invariance for total bisimulations.

    If `R` is a bisimulation where every state in `N` is related to some state
    in `M`, and `φ.validIn M`, then `φ.validIn N`. -/
theorem bisim_system_invariant
    {M N : MultiwaySystem.{u, v}} {R : M.State → N.State → Prop}
    (hR : RelationalBisimulation M N R)
    (hTotal : ∀ t : N.State, ∃ s : M.State, R s t)
    (φ : HML) (hvalid : φ.validIn M) : φ.validIn N := by
  intro t
  obtain ⟨s, hst⟩ := hTotal t
  exact (bisim_invariant hR φ hst).mp (hvalid s)

/-!
## Part 3: Standard HML Formulas

Named formulas corresponding to common modal properties.
-/

/-- ◇⊤: "has at least one successor" -/
def hasSuc : HML := .diamond .top

/-- ◇◇⊤: "has a successor that has a successor" -/
def hasSucSuc : HML := .diamond (.diamond .top)

/-- ◇φ ∧ ◇ψ: "has a successor satisfying φ and a (possibly different) successor satisfying ψ" -/
def diamondBoth (φ ψ : HML) : HML := .conj (.diamond φ) (.diamond ψ)

end HML

end Ruliology
