/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Separating Sequents for the Three-Level Hierarchy

Defines the four separating geometric sequents as concrete `GeoSequent` objects:
- σ_tot: totality (⊤ ⊢_x ∃y. step(x,y))
- σ_det: determinism (step(x,y) ∧ step(x,z) ⊢ y=z) — reuses BranchingTopology
- σ_conf: weak confluence (step(x,y) ∧ step(x,z) ⊢ ∃w. step(y,w) ∧ step(z,w))
- σ_loop: universal self-loop (⊤ ⊢_x step(x,x))

## References

- Paper §4: Separation theorems
- BranchingTopology.lean — determinismSequent (σ_det)
-/

import RuleSys.GeometricLogic.TheoryOfSystem

open FirstOrder Language GeometricLogic

namespace GeometricLogic

/-!
## σ_tot: Totality sequent

⊤ ⊢_x ∃y. step(x, y)

Every state has at least one successor. Separates pathSys (total) from fork (c halts).
-/

/-- The totality sequent: ⊤ ⊢_x ∃y. step(x, y).
    Context: one free variable x : Ctx1 (= Fin 1).
    The consequent ∃y. step(x, y) has:
    - x as the free variable (varTerm 0 in Ctx1)
    - y as the bound variable (boundTerm 0 in context with 1 bound var) -/
def sigma_tot : GeoSequent MultiwayLanguage Ctx1 :=
  { antecedent := .top
    consequent := .exist (stepRel (varTerm (0 : Fin 1)) (boundTerm 0)) }

/-!
## σ_det: Determinism sequent

step(x,y) ∧ step(x,z) ⊢_{x,y,z} y = z

Reuse from BranchingTopology (determinismSequent).
-/

-- σ_det is `determinismSequent` defined in BranchingTopology.lean.
-- We define it here independently for use in the Soundness module.

/-- The determinism sequent: step(x,y) ∧ step(x,z) ⊢_{x,y,z} y = z.
    Context: three free variables (Ctx3 = Fin 3). -/
def sigma_det : GeoSequent MultiwayLanguage Ctx3 :=
  { antecedent := .conj (stepVars 0 1) (stepVars 0 2)
    consequent := eqTerms (varTerm 1) (varTerm 2) }

/-!
## σ_conf: Weak confluence sequent

step(x,y) ∧ step(x,z) ⊢_{x,y,z} ∃w. step(y,w) ∧ step(z,w)

Every pair of successors can reach a common successor.
-/

/-- The weak confluence sequent:
    step(x,y) ∧ step(x,z) ⊢_{x,y,z} ∃w. step(y,w) ∧ step(z,w).
    Context: three free variables (Ctx3).
    The consequent uses one bound variable w (index 0 in Fin 1). -/
def sigma_conf : GeoSequent MultiwayLanguage Ctx3 :=
  { antecedent := .conj (stepVars 0 1) (stepVars 0 2)
    consequent := .exist (.conj
      (stepRel (varTerm (1 : Fin 3)) (boundTerm 0))
      (stepRel (varTerm (2 : Fin 3)) (boundTerm 0))) }

/-!
## σ_loop: Universal self-loop sequent

⊤ ⊢_x step(x, x)

Every state has a self-loop.
-/

/-- The universal self-loop sequent: ⊤ ⊢_x step(x, x).
    Context: one free variable x (Ctx1 = Fin 1). -/
def sigma_loop : GeoSequent MultiwayLanguage Ctx1 :=
  { antecedent := .top
    consequent := stepVars 0 0 }

end GeometricLogic
