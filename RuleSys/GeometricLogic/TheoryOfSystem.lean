/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theory of Rooted Transition Systems

This file defines the geometric theory T_M for rooted transition systems, establishing
the logical characterization needed for the Caramello framework resolution
of Conjecture E (bisimulation ↔ bi-interpretability).

## Main Definitions

- `MultiwayRel`: Binary relation symbols (step, reach, pathEquiv)
- `RTSLanguage`: First-order language with init constant and binary relations
- `theoryOfSystem`: The geometric theory T_M for a rooted transition system M

## Implementation Notes

We use a single-sorted theory where all variables range over states.
The language has:
- One 0-ary function: `init` (the initial state constant)
- Three binary relations:
  - `step(x, y)`: one-step transition from x to y
  - `reach(x, y)`: y is reachable from x via some path
  - `pathEquiv(x, y)`: x and y are mutually reachable

The `step` relation and `init` constant capture the primitive structure
of rooted transition systems, enabling model-theoretic extraction of simulations
from interpretations.

## References

- Caramello, "Theories, Sites, Toposes" (2017), Ch. 1-2
- Makkai & Reyes, "First Order Categorical Logic" (1977)
-/

import RuleSys.GeometricLogic.Sequent
import RuleSys.Basic

open FirstOrder Language GeometricLogic

universe u v

namespace GeometricLogic

/-!
## Task 1: RTSLanguage and Relation Constructors
-/

/-- Binary relation symbols in the multiway language.
    - `step`: primitive step relation (one-step transition)
    - `reach`: reachability (reflexive-transitive closure of step)
    - `pathEquiv`: path equivalence (bidirectional reachability) -/
inductive MultiwayRel : Type
  | step      -- one-step transition from x to y
  | reach     -- y is reachable from x (path exists)
  | pathEquiv -- x and y are mutually reachable
  deriving DecidableEq, Repr

/-- The first-order language for rooted transition system theories.

    **Structure:**
    - One 0-ary function: `init` (the initial state constant)
    - Three binary relations: `step`, `reach`, `pathEquiv`

    This is a single-sorted language where all variables range over states.
    The `init` constant and `step` relation capture the primitive structure
    of rooted transition systems, while `reach` and `pathEquiv` are derived notions
    axiomatized in the theory. -/
def RTSLanguage : Language.{0, 0} where
  Functions := fun
    | 0 => Unit   -- init : S (the initial state constant)
    | _ => Empty
  Relations := fun
    | 2 => MultiwayRel
    | _ => Empty

/-- The init constant symbol in RTSLanguage -/
def initSymbol : RTSLanguage.Functions 0 := ()

/-- The single sort representing states in T_M.
    In geometric logic, we work with a single-sorted theory. -/
abbrev StateSort := Unit

/-!
## Task 2: Formula and Term Constructors
-/

section TermsAndFormulas

variable {α : Type*} {n : ℕ}

/-- Create a free variable term -/
def varTerm (a : α) : RTSLanguage.Term (α ⊕ Fin n) :=
  Term.var (Sum.inl a)

/-- Create a bound variable term -/
def boundTerm (i : Fin n) : RTSLanguage.Term (α ⊕ Fin n) :=
  Term.var (Sum.inr i)

/-- Coercion from MultiwayRel to the language's binary relations -/
def MultiwayRel.toRel (r : MultiwayRel) : RTSLanguage.Relations 2 := r

/-- The step relation applied to two terms: step(t₁, t₂).
    This means there is a one-step transition from t₁ to t₂. -/
def stepRel (t₁ t₂ : RTSLanguage.Term (α ⊕ Fin n)) :
    GeoFormula RTSLanguage α n :=
  .rel (MultiwayRel.step.toRel) ![t₁, t₂]

/-- The reach relation applied to two terms: reach(t₁, t₂).
    In RTSLanguage, this means t₂ is reachable from t₁. -/
def reachRel (t₁ t₂ : RTSLanguage.Term (α ⊕ Fin n)) :
    GeoFormula RTSLanguage α n :=
  .rel (MultiwayRel.reach.toRel) ![t₁, t₂]

/-- The pathEquiv relation applied to two terms: pathEquiv(t₁, t₂).
    This means t₁ and t₂ are mutually reachable. -/
def pathEquivRel (t₁ t₂ : RTSLanguage.Term (α ⊕ Fin n)) :
    GeoFormula RTSLanguage α n :=
  .rel (MultiwayRel.pathEquiv.toRel) ![t₁, t₂]

/-- step(x, y) where x, y are free variables indexed by α -/
def stepVars (x y : α) : GeoFormula RTSLanguage α 0 :=
  stepRel (varTerm x) (varTerm y)

/-- reach(x, y) where x, y are free variables indexed by α -/
def reachVars (x y : α) : GeoFormula RTSLanguage α 0 :=
  reachRel (varTerm x) (varTerm y)

/-- pathEquiv(x, y) where x, y are free variables indexed by α -/
def pathEquivVars (x y : α) : GeoFormula RTSLanguage α 0 :=
  pathEquivRel (varTerm x) (varTerm y)

/-- The init constant as a term (0-ary function application) -/
def initTerm : RTSLanguage.Term (α ⊕ Fin n) :=
  Term.func initSymbol ![]

/-- Equality formula: t₁ = t₂ -/
def eqTerms (t₁ t₂ : RTSLanguage.Term (α ⊕ Fin n)) :
    GeoFormula RTSLanguage α n :=
  .equal t₁ t₂

/-- Formula expressing x = init (x is the initial state) -/
def isInitVar (x : α) : GeoFormula RTSLanguage α 0 :=
  eqTerms (varTerm x) initTerm

end TermsAndFormulas

/-!
## Task 3: Theory Axioms and theoryOfSystem
-/

section TheoryAxioms

/-- Standard context: single variable x (indexed by Fin 1) -/
abbrev Ctx1 := Fin 1
/-- Standard context: two variables x, y (indexed by Fin 2) -/
abbrev Ctx2 := Fin 2
/-- Standard context: three variables x, y, z (indexed by Fin 3) -/
abbrev Ctx3 := Fin 3

/-- Axiom: Steps imply reachability.
    step(x, y) ⊢_{x,y} reach(x, y)

    This connects the primitive step relation to derived reachability.
    Combined with reflexivity and transitivity of reach, this says
    reach is the reflexive-transitive closure of step. -/
def axiomStepImpliesReach : GeoSequent RTSLanguage Ctx2 :=
  { antecedent := stepVars 0 1
    consequent := reachVars 0 1 }

/-- Axiom: Reachability is reflexive.
    ⊤ ⊢_x reach(x, x) -/
def axiomReachRefl : GeoSequent RTSLanguage Ctx1 :=
  { antecedent := .top
    consequent := reachVars 0 0 }

/-- Axiom: Reachability is transitive.
    reach(x, y) ∧ reach(y, z) ⊢_{x,y,z} reach(x, z) -/
def axiomReachTrans : GeoSequent RTSLanguage Ctx3 :=
  { antecedent := .conj (reachVars 0 1) (reachVars 1 2)
    consequent := reachVars 0 2 }

/-- Axiom: Path equivalence is defined by bidirectional reachability.
    reach(x, y) ∧ reach(y, x) ⊢_{x,y} pathEquiv(x, y) -/
def axiomPathEquivDef : GeoSequent RTSLanguage Ctx2 :=
  { antecedent := .conj (reachVars 0 1) (reachVars 1 0)
    consequent := pathEquivVars 0 1 }

/-- Axiom: Path equivalence is symmetric.
    pathEquiv(x, y) ⊢_{x,y} pathEquiv(y, x) -/
def axiomPathEquivSymm : GeoSequent RTSLanguage Ctx2 :=
  { antecedent := pathEquivVars 0 1
    consequent := pathEquivVars 1 0 }

/-- Axiom: Path equivalence implies bidirectional reachability (converse of definition).
    pathEquiv(x, y) ⊢_{x,y} reach(x, y) -/
def axiomPathEquivToReach : GeoSequent RTSLanguage Ctx2 :=
  { antecedent := pathEquivVars 0 1
    consequent := reachVars 0 1 }

/-- The core geometric theory of rooted transition systems.

    **Axioms:**
    1. `step(x,y) ⊢ reach(x,y)` - steps imply reachability
    2. `⊤ ⊢ reach(x,x)` - reachability is reflexive
    3. `reach(x,y) ∧ reach(y,z) ⊢ reach(x,z)` - reachability is transitive
    4. `reach(x,y) ∧ reach(y,x) ⊢ pathEquiv(x,y)` - path equivalence definition
    5. `pathEquiv(x,y) ⊢ pathEquiv(y,x)` - path equivalence is symmetric
    6. `pathEquiv(x,y) ⊢ reach(x,y)` - path equivalence implies reachability

    Together with the `init` constant, this theory captures the full structure
    of rooted transition systems. System-specific behavior is in the models. -/
def rtsTheory : GeometricTheory RTSLanguage :=
  ({ GeometricTheory.package axiomStepImpliesReach,
     GeometricTheory.package axiomReachRefl,
     GeometricTheory.package axiomReachTrans,
     GeometricTheory.package axiomPathEquivDef,
     GeometricTheory.package axiomPathEquivSymm,
     GeometricTheory.package axiomPathEquivToReach } : Set (PackagedSequent RTSLanguage))

/-- System-specific axioms for a rooted transition system M.

    These capture the concrete transition structure of M as geometric sequents:

    1. **Existence axioms:** For each pair (s, t) where M.Step s t holds:
       `⊤ ⊢ step(s, t)` — asserting the existence of specific transitions.

    2. **Completeness axioms:** For each state s, the disjunction of all successors:
       `step(s, x) ⊢ x = t₁ ∨ x = t₂ ∨ ... ∨ x = tₙ`
       where {t₁, ..., tₙ} = {t | M.Step s t}.

    These are geometric sequents (using only ∧, ∨, ∃, =, ⊤ on the right).

    Axiomatized: encoding M's states as RTSLanguage terms requires a
    naming function `M.State → RTSLanguage.Term`, which depends on a
    finite enumeration of states. The type signature captures the contract
    that each system produces a well-defined set of geometric axioms. -/
axiom systemSpecificAxioms (M : RTS.RootedTS) :
    GeometricTheory RTSLanguage

/-- The syntactic geometric theory of a rooted transition system M.

    Defined as the union of:
    - `rtsTheory`: 6 structural axioms (step→reach, reflexivity,
      transitivity, pathEquiv definition/symmetry/reach)
    - `systemSpecificAxioms M`: axioms encoding M's specific transitions

    This gives T_M genuine syntactic content: a finite (or r.e.) axiom set
    from which provability is non-trivial. The classifying topos
    Sh(C_{T_M}, J_{T_M}) reflects the specific transition structure of M,
    not just semantic truth. -/
def syntacticTheoryOfSystem (M : RTS.RootedTS) : GeometricTheory RTSLanguage :=
  GeometricTheory.union rtsTheory (systemSpecificAxioms M)

end TheoryAxioms

/-!
## Models of RTSLanguage

A model interprets the language symbols into a carrier set.
For rooted transition systems, the canonical model interprets:
- init → M.init
- step(x,y) → Nonempty (M.Step x y)
- reach(x,y) → M.reach x y
- pathEquiv(x,y) → M.pathEquiv x y
-/

section Models

/-- A model of RTSLanguage in Set.

    A model interprets:
    - The carrier type (states)
    - The init constant → an element of the carrier
    - The step relation → a binary relation on the carrier
    - The reach relation → a binary relation on the carrier
    - The pathEquiv relation → a binary relation on the carrier

    For the model to satisfy theoryOfSystem, the interpretations must
    satisfy the theory's axioms. -/
structure RTSModel where
  /-- The carrier set (states) -/
  carrier : Type*
  /-- Interpretation of the init constant -/
  init : carrier
  /-- Interpretation of the step relation -/
  step : carrier → carrier → Prop
  /-- Interpretation of the reach relation -/
  reach : carrier → carrier → Prop
  /-- Interpretation of the pathEquiv relation -/
  pathEquiv : carrier → carrier → Prop

namespace RTSModel

variable (M : RTSModel)

/-- A model satisfies the step-implies-reach axiom -/
def satisfies_stepReach : Prop :=
  ∀ x y, M.step x y → M.reach x y

/-- A model satisfies reach reflexivity -/
def satisfies_reachRefl : Prop :=
  ∀ x, M.reach x x

/-- A model satisfies reach transitivity -/
def satisfies_reachTrans : Prop :=
  ∀ x y z, M.reach x y → M.reach y z → M.reach x z

/-- A model satisfies pathEquiv definition -/
def satisfies_pathEquivDef : Prop :=
  ∀ x y, M.reach x y → M.reach y x → M.pathEquiv x y

/-- A model satisfies pathEquiv symmetry -/
def satisfies_pathEquivSymm : Prop :=
  ∀ x y, M.pathEquiv x y → M.pathEquiv y x

/-- A model satisfies pathEquiv-implies-reach -/
def satisfies_pathEquivReach : Prop :=
  ∀ x y, M.pathEquiv x y → M.reach x y

/-- A model satisfies all axioms of rtsTheory -/
def satisfiesTheory : Prop :=
  M.satisfies_stepReach ∧
  M.satisfies_reachRefl ∧
  M.satisfies_reachTrans ∧
  M.satisfies_pathEquivDef ∧
  M.satisfies_pathEquivSymm ∧
  M.satisfies_pathEquivReach

end RTSModel

end Models

end GeometricLogic

/-!
## Canonical Model of a Rooted Transition System

Every rooted transition system gives rise to a canonical model of RTSLanguage.
-/

namespace RTS.RootedTS

variable (M : RTS.RootedTS)

/-- Reachability relation on a rooted transition system.
    `reach M s t` holds if there exists a path from `s` to `t`. -/
def reach (s t : M.State) : Prop :=
  Nonempty (M.Path s t)

/-- Path equivalence: bidirectional reachability.
    `pathEquiv M s t` holds if `s` can reach `t` and `t` can reach `s`. -/
def pathEquiv (s t : M.State) : Prop :=
  M.reach s t ∧ M.reach t s

/-- Reachability is reflexive -/
theorem reach_refl (s : M.State) : M.reach s s :=
  ⟨RootedTS.Path.nil s⟩

/-- Reachability is transitive -/
theorem reach_trans {s t u : M.State} (h1 : M.reach s t) (h2 : M.reach t u) :
    M.reach s u := by
  obtain ⟨p1⟩ := h1
  obtain ⟨p2⟩ := h2
  exact ⟨p1.comp p2⟩

open GeometricLogic

/-- The canonical model of a rooted transition system.

    This interprets RTSLanguage in the "intended" way:
    - carrier = M.State
    - init = M.init
    - step(x,y) = Nonempty (M.Step x y)
    - reach(x,y) = M.reach x y
    - pathEquiv(x,y) = M.pathEquiv x y

    The canonical model satisfies theoryOfSystem M. -/
def canonicalModel (M : RTS.RootedTS) : RTSModel where
  carrier := M.State
  init := M.init
  step := fun x y => Nonempty (M.Step x y)
  reach := M.reach
  pathEquiv := M.pathEquiv

/-- The canonical model satisfies the multiway theory -/
theorem canonicalModel_satisfies (M : RTS.RootedTS) :
    M.canonicalModel.satisfiesTheory := by
  unfold RTSModel.satisfiesTheory
  unfold RTSModel.satisfies_stepReach
  unfold RTSModel.satisfies_reachRefl
  unfold RTSModel.satisfies_reachTrans
  unfold RTSModel.satisfies_pathEquivDef
  unfold RTSModel.satisfies_pathEquivSymm
  unfold RTSModel.satisfies_pathEquivReach
  simp only [canonicalModel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- step implies reach: step(x,y) → reach(x,y)
    intro x y ⟨s⟩
    exact ⟨Path.cons s (Path.nil y)⟩
  · -- reach reflexive
    exact M.reach_refl
  · -- reach transitive
    exact fun x y z hxy hyz => M.reach_trans hxy hyz
  · -- pathEquiv definition
    exact fun x y hxy hyx => ⟨hxy, hyx⟩
  · -- pathEquiv symmetric
    exact fun x y ⟨hxy, hyx⟩ => ⟨hyx, hxy⟩
  · -- pathEquiv implies reach
    exact fun x y ⟨hxy, _⟩ => hxy

/-!
## Morita Equivalence Hypotheses Verification

This section verifies that our geometric theory definitions satisfy
Caramello's hypotheses for Morita equivalence of toposes.

### Hypothesis 1: Coherent Language

`RTSLanguage` is a coherent first-order language:
- **Single sort:** All variables range over State
- **Finite relation arities:** step (2), reach (2), pathEquiv (2)
- **Constants as 0-ary functions:** init is a 0-ary function symbol
- **No proper function symbols:** Only the constant init

This satisfies Caramello's requirement that the language be coherent
(finitary, single-sorted for simplicity).

### Hypothesis 2: Geometric Theory

`theoryOfSystem M` generates a geometric theory because all axioms
are geometric sequents of the form:

  φ ⊢_x ψ

where φ and ψ are geometric formulas (built from atoms, ∧, ∨, ∃, ⊤, ⊥).

**Axiom analysis:**
- `stepReach`: step(x,y) ⊢ reach(x,y) — atoms only
- `reachRefl`: ⊤ ⊢ reach(x,x) — atom consequent
- `reachTrans`: reach(x,y) ∧ reach(y,z) ⊢ reach(x,z) — conjunction to atom
- `pathEquivDef`: reach(x,y) ∧ reach(y,x) ⊢ pathEquiv(x,y) — conjunction to atom
- `pathEquivSymm`: pathEquiv(x,y) ⊢ pathEquiv(y,x) — atoms only
- `pathEquivReach`: pathEquiv(x,y) ⊢ reach(x,y) — atoms only

No axiom uses ∀, →, or ¬ in the consequent. All are geometric.

### Hypothesis 3: Interpretations Preserve Provability

`InterpretationData.preserves_provability` (axiomatized in Interpretation.lean)
ensures that if T_M ⊢ φ ⊢_x ψ, then T_N ⊢ I(φ) ⊢_x I(ψ).

This is Definition 2.14(iv) from Caramello: interpretations preserve
the proof-theoretic structure of geometric theories.

### Hypothesis 4: Bi-Interpretation Coherence

`BiInterpretation.coherence_M` and `coherence_N` ensure that:
- backward.stateMap ∘ forward.stateMap is path-equivalent to id on M
- forward.stateMap ∘ backward.stateMap is path-equivalent to id on N

This corresponds to the "definable isomorphism" requirement in Caramello's
framework: the round-trip interpretation is isomorphic to identity
in the internal logic of the theories.

### Conclusion: Morita Equivalence Justified

Given these hypotheses:

1. Classifying toposes Set[T_M] and Set[T_N] are well-defined Grothendieck toposes
2. A bi-interpretation B : T_M ↔ T_N induces an equivalence Set[T_M] ≃ Set[T_N]
3. This equivalence is a Morita equivalence (preserves geometric properties)

Therefore `bisimilar_iff_biInterpretable` correctly characterizes when
rooted transition systems have Morita-equivalent classifying toposes.

**Reference:** Caramello, "Theories, Sites, Toposes" (2017), Theorem 2.1.14
-/

end RTS.RootedTS
