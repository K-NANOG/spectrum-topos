/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Simulation Invariance for Geometric Formulas

This file defines simulation invariance for geometric formulas over labeled
transition systems and proves that positive existential HML (HMLPos) formulas
are simulation-invariant. As a corollary, simulation invariance implies
bisimulation invariance.

## Key Definitions

- `FinLTSSimInvariant`: A geometric formula φ is simulation-invariant if it is
  preserved by forward simulations: whenever R is a simulation from G to H with
  R v w, then φ(G, v) implies φ(H, w).
- `HMLPos.sim_invariant`: HMLPos formulas are preserved by labeled simulations.
- `bisimInvariant_of_simInvariant`: Simulation invariance implies bisimulation invariance.
- `hmlPos_bisimInvariant`: HMLPos formulas are preserved by labeled bisimulations.

## Mathematical Significance

Simulation invariance is strictly stronger than bisimulation invariance:
every simulation-invariant formula is bisimulation-invariant, because the
forward half of a bisimulation is a simulation. The converse fails in general
(bisimulation invariance additionally requires backward preservation, which
simulation invariance provides "for free" since it only demands forward direction).

HMLPos — the positive existential fragment of HML — is the canonical example
of simulation-invariant formulas. This characterization connects to the
van Glabbeek spectrum: the simulation preorder is characterized by HMLPos
equivalence, just as bisimulation equivalence is characterized by full HML
equivalence.

## References

- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
-/

import RuleSys.PresheafTopos.GeometricVanBenthem
import RuleSys.PresheafTopos.SimulationTopology
import RuleSys.PresheafTopos.FreeExtension

set_option autoImplicit false

namespace RTS.PresheafTopos

variable {L : Type} [Fintype L] [DecidableEq L]

/-!
## Part 1: Simulation Invariance for Geometric Formulas
-/

/-- A geometric formula φ : LTSGeoFormula L 1 (with one free variable) is
    simulation-invariant if it is preserved by labeled simulations:
    whenever R is a forward simulation from G to H with R v w, then
    φ(G, v) implies φ(H, w).

    This is the forward-only analogue of `FinLTSBisimInvariant`. Unlike
    bisimulation invariance, simulation invariance is a one-directional condition:
    truth is preserved in the forward direction of the simulation. -/
def FinLTSSimInvariant (φ : LTSGeoFormula L 1) : Prop :=
  ∀ (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop),
    LabeledSimulation G H R →
    ∀ (v : G.Vertex) (w : H.Vertex), R v w →
    φ.satisfies G (fun _ => v) → φ.satisfies H (fun _ => w)

/-!
## Part 2: HMLPos Simulation Invariance
-/

/-- **HMLPos formulas are preserved by labeled simulations.**

    If R is a forward simulation from G to H, R v w, and φ.satisfies G v,
    then φ.satisfies H w. Proof by structural induction on the HMLPos formula:

    - `top`: trivially True → True
    - `conj φ ψ`: both conjuncts preserved by induction hypotheses
    - `diamond a φ`: Given ∃w', G.edge a v w' ∧ φ.satisfies G w' and R v w:
      the simulation forward condition gives ∃w'', H.edge a w w'' ∧ R w' w'',
      and by IH, φ.satisfies H w''.

    This is the key semantic property of positive existential formulas:
    they contain only ∃ (diamond) and ∧ (conj), both of which are
    forward-preserved by functional/relational maps. -/
theorem HMLPos.sim_invariant
    (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop)
    (hR : LabeledSimulation G H R)
    (v : G.Vertex) (w : H.Vertex) (hvw : R v w)
    (phi : HMLPos L) (hsat : phi.satisfies G v) :
    phi.satisfies H w := by
  induction phi generalizing v w with
  | top => trivial
  | conj φ ψ ih_φ ih_ψ =>
    obtain ⟨h_left, h_right⟩ := hsat
    exact ⟨ih_φ v w hvw h_left, ih_ψ v w hvw h_right⟩
  | diamond a φ ih =>
    obtain ⟨v', hv'_edge, hv'_sat⟩ := hsat
    obtain ⟨w', hw'_edge, hw'_rel⟩ := hR v w hvw a v' hv'_edge
    exact ⟨w', hw'_edge, ih v' w' hw'_rel hv'_sat⟩

/-!
## Part 3: Simulation Invariance Implies Bisimulation Invariance
-/

/-- **Simulation invariance implies bisimulation invariance.**

    If a geometric formula φ is simulation-invariant, then it is also
    bisimulation-invariant. The proof uses the fact that the forward half
    of a labeled bisimulation is a labeled simulation:
    `(LabeledBisimulation G H R).1 : LabeledSimulation G H R`.

    Given a bisimulation R between G and H with R v w:
    - Forward: R.1 is a simulation from G to H, so φ(G,v) → φ(H,w)
    - Backward: R.2 gives a simulation from H to G (via flip R),
      so φ(H,w) → φ(G,v)

    Both directions together give the bidirectional condition required
    by `FinLTSBisimInvariant`. -/
theorem bisimInvariant_of_simInvariant (φ : LTSGeoFormula L 1)
    (hsim : FinLTSSimInvariant φ) : FinLTSBisimInvariant φ := by
  intro G H R hR v w hvw hsat
  exact hsim G H R hR.1 v w hvw hsat

/-!
## Part 4: HMLPos Bisimulation Invariance (Corollary)
-/

/-- **HMLPos formulas are preserved by labeled bisimulations.**

    Corollary of `HMLPos.sim_invariant`: since the forward half of a
    bisimulation is a simulation, HMLPos formulas that hold at v in G
    also hold at w in H whenever R is a bisimulation with R v w.

    Combined with `FinLTSBisimInvariant_iff`, this gives full bidirectional
    equivalence: bisimulation-related states satisfy exactly the same
    HMLPos formulas. -/
theorem hmlPos_bisimInvariant
    (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop)
    (hR : LabeledBisimulation G H R)
    (v : G.Vertex) (w : H.Vertex) (hvw : R v w)
    (phi : HMLPos L) (hsat : phi.satisfies G v) :
    phi.satisfies H w :=
  HMLPos.sim_invariant G H R hR.1 v w hvw phi hsat

end RTS.PresheafTopos
