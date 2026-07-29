/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Semantic Separation: Validity and Invalidity of Separating Sequents

Proves semantic validity/invalidity for each separating sequent in each
witness system. All proofs are constructive finite case analysis — zero axioms.

Also derives non-provability results from generic soundness + semantic separation.

## Main Results (semantic, 0 axioms)

- σ_tot: pathSys satisfies it, fork does not
- σ_det: twoCycle satisfies it, hubSpokes does not
- σ_conf: diamondGraph satisfies it, confTree does not
- σ_loop: selfLoop satisfies it, twoCycle does not

## Derived Non-Provability (from Provable.sound axiom)

- `fork_not_proves_sigma_tot`
- `hubSpokes_not_proves_sigma_det`
- `confTree_not_proves_sigma_conf`
- `twoCycle_not_proves_sigma_loop`

## References

- Paper §4: Separation theorems
-/

import RuleSys.GeometricLogic.Soundness
import RuleSys.FirstSeparation
import RuleSys.SecondSeparation
import RuleSys.HMLSeparation

open FirstOrder Language GeometricLogic

namespace GeometricLogic

-- Abbreviation for canonical model
private abbrev cm (M : RTS.RootedTS) := RTS.RootedTS.canonicalModel M

/-!
## σ_tot: Totality — pathSys vs fork
-/

/-- pathSys satisfies σ_tot: every state has a successor. -/
theorem pathSys_satisfies_sigma_tot : satisfiesSequent' (cm RTS.pathSys) sigma_tot := by
  rw [satisfiesSequent'_sigma_tot_iff]
  intro x
  match x with
  | .x => exact ⟨.y, ⟨()⟩⟩
  | .y => exact ⟨.y, ⟨()⟩⟩

/-- fork does NOT satisfy σ_tot: state c has no successor. -/
theorem fork_not_satisfies_sigma_tot : ¬ satisfiesSequent' (cm RTS.fork) sigma_tot := by
  rw [satisfiesSequent'_sigma_tot_iff]
  push_neg
  exact ⟨.c, fun t ht => RTS.fork_c_halting t ht⟩

/-- T_fork does not prove σ_tot. -/
theorem fork_not_proves_sigma_tot :
    ¬ Provable (theoryOfSystem RTS.fork) sigma_tot := by
  intro h
  have hsound := Provable.sound h _ (canonicalModel_satisfies_theorySeq RTS.fork)
  exact fork_not_satisfies_sigma_tot hsound

/-!
## σ_det: Determinism — twoCycle vs hubSpokes
-/

/-- twoCycle satisfies σ_det: each state has exactly one successor. -/
theorem twoCycle_satisfies_sigma_det : satisfiesSequent' (cm RTS.twoCycle) sigma_det := by
  rw [satisfiesSequent'_sigma_det_iff]
  intro x y z ⟨s1⟩ ⟨s2⟩
  match x, y, s1, z, s2 with
  | .x, .y, (), .y, () => rfl
  | .y, .x, (), .x, () => rfl

/-- hubSpokes does NOT satisfy σ_det: state a has distinct successors b and c. -/
theorem hubSpokes_not_satisfies_sigma_det :
    ¬ satisfiesSequent' (cm RTS.hubSpokes) sigma_det := by
  rw [satisfiesSequent'_sigma_det_iff]
  push_neg
  exact ⟨.a, .b, .c, ⟨()⟩, ⟨()⟩, RTS.HubSpokeState.noConfusion⟩

/-- T_hubSpokes does not prove σ_det. -/
theorem hubSpokes_not_proves_sigma_det :
    ¬ Provable (theoryOfSystem RTS.hubSpokes) sigma_det := by
  intro h
  have hsound := Provable.sound h _ (canonicalModel_satisfies_theorySeq RTS.hubSpokes)
  exact hubSpokes_not_satisfies_sigma_det hsound

/-!
## σ_conf: Weak confluence — diamondGraph vs confTree
-/

/-- diamondGraph satisfies σ_conf. -/
theorem diamondGraph_satisfies_sigma_conf :
    satisfiesSequent' (cm RTS.diamondGraph) sigma_conf := by
  rw [satisfiesSequent'_sigma_conf_iff]
  intro x y z ⟨s1⟩ ⟨s2⟩
  match x, y, s1, z, s2 with
  | .a, .b, (), .b, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .b, (), .c, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .c, (), .b, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .c, (), .c, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .b, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .c, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .d, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩

/-- confTree does NOT satisfy σ_conf: b and c have no common successor. -/
theorem confTree_not_satisfies_sigma_conf :
    ¬ satisfiesSequent' (cm RTS.confTree) sigma_conf := by
  rw [satisfiesSequent'_sigma_conf_iff]
  push_neg
  refine ⟨.a, .b, .c, ⟨()⟩, ⟨()⟩, ?_⟩
  intro w ⟨hw1⟩ ⟨hw2⟩
  match w, hw1 with
  | .dL, () => exact nomatch hw2

/-- T_confTree does not prove σ_conf. -/
theorem confTree_not_proves_sigma_conf :
    ¬ Provable (theoryOfSystem RTS.confTree) sigma_conf := by
  intro h
  have hsound := Provable.sound h _ (canonicalModel_satisfies_theorySeq RTS.confTree)
  exact confTree_not_satisfies_sigma_conf hsound

/-!
## σ_loop: Universal self-loop — selfLoop vs twoCycle
-/

/-- selfLoop satisfies σ_loop. -/
theorem selfLoop_satisfies_sigma_loop :
    satisfiesSequent' (cm RTS.selfLoop) sigma_loop := by
  rw [satisfiesSequent'_sigma_loop_iff]
  intro x
  match x with
  | () => exact ⟨()⟩

/-- twoCycle does NOT satisfy σ_loop: x has no self-loop. -/
theorem twoCycle_not_satisfies_sigma_loop :
    ¬ satisfiesSequent' (cm RTS.twoCycle) sigma_loop := by
  rw [satisfiesSequent'_sigma_loop_iff]
  push_neg
  exact ⟨.x, fun h => h.elim fun s => nomatch s⟩

/-- T_twoCycle does not prove σ_loop. -/
theorem twoCycle_not_proves_sigma_loop :
    ¬ Provable (theoryOfSystem RTS.twoCycle) sigma_loop := by
  intro h
  have hsound := Provable.sound h _ (canonicalModel_satisfies_theorySeq RTS.twoCycle)
  exact twoCycle_not_satisfies_sigma_loop hsound

end GeometricLogic
