/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Separation Witnesses: Geometric Logic Extends HML

Exhibits three bisimilar system pairs where a geometric property holds in one
system but not the other. Each property is expressible as a geometric sequent
but lies outside diamond-only HML.

## Three Mechanisms

1. **Consequent equality** (σ_det): hubSpokes ~ twoCycle (SecondSeparation.lean)
2. **Cyclic variable sharing** (σ_conf): diamondGraph ~ confTree (this file)
3. **Repeated variables** (σ_loop): selfLoop ~ twoCycle (this file)

## References

- HML.lean — Bisimulation invariance of the diamond-only fragment
- SecondSeparation.lean — First witness pair (σ_det)
-/

import RuleSys.HML
import RuleSys.SecondSeparation

open CategoryTheory

namespace RTS

universe u v

/-!
## Part 1: Semantic Formulations
-/

/-- Weak confluence: every pair of successors has a common successor.
    Geometric sequent: `step(x,y) ∧ step(x,z) ⊢ ∃w. step(y,w) ∧ step(z,w)`.
    Breaks bisimulation-invariance via cyclic variable sharing. -/
def WeakConfluence (M : RootedTS.{u, v}) : Prop :=
  ∀ (s t₁ t₂ : M.State), Nonempty (M.Step s t₁) → Nonempty (M.Step s t₂) →
    ∃ w : M.State, Nonempty (M.Step t₁ w) ∧ Nonempty (M.Step t₂ w)

/-- Universal self-loop: every state has a self-loop.
    Geometric sequent: `⊤ ⊢_x step(x, x)`.
    Breaks bisimulation-invariance via repeated variables. -/
def UniversalSelfLoop (M : RootedTS.{u, v}) : Prop :=
  ∀ s : M.State, Nonempty (M.Step s s)

/-- Determinism: each state has at most one successor.
    Geometric sequent: `step(x,y) ∧ step(x,z) ⊢ y=z`.
    Breaks bisimulation-invariance via consequent equality. -/
def Deterministic (M : RootedTS.{u, v}) : Prop :=
  ∀ (s t₁ t₂ : M.State), Nonempty (M.Step s t₁) → Nonempty (M.Step s t₂) → t₁ = t₂

/-!
## Part 2: σ_loop — Repeated Variable Separation

selfLoop (one state, self-loop) ~ twoCycle (two states, no self-loops)
-/

/-- Single state with self-loop. -/
def selfLoop : RootedTS.{0, 0} where
  State := Unit
  Step := fun _ _ => Unit
  init := ()

/-- R relates the single state to every state of twoCycle. -/
def loopCycleBisimR : Unit → TwoCycleState → Prop := fun _ _ => True

/-- loopCycleBisimR is a relational bisimulation. -/
theorem loopCycleBisim : RelationalBisimulation selfLoop twoCycle loopCycleBisimR := by
  constructor
  · -- Forth
    intro s t _ s' _
    match t with
    | .x => exact ⟨.y, ⟨()⟩, trivial⟩
    | .y => exact ⟨.x, ⟨()⟩, trivial⟩
  · -- Back
    intro s t _ t' _
    exact ⟨(), ⟨()⟩, trivial⟩

/-- selfLoop satisfies UniversalSelfLoop. -/
theorem selfLoop_has_selfLoop : UniversalSelfLoop selfLoop :=
  fun _ => ⟨()⟩

/-- twoCycle does NOT satisfy UniversalSelfLoop. -/
theorem twoCycle_no_selfLoop : ¬ UniversalSelfLoop twoCycle := by
  intro h
  exact (h .x).elim fun step => nomatch step

/-- **σ_loop separation.** -/
theorem selfLoop_separation :
    RelationalBisimulation selfLoop twoCycle loopCycleBisimR ∧
    UniversalSelfLoop selfLoop ∧
    ¬ UniversalSelfLoop twoCycle :=
  ⟨loopCycleBisim, selfLoop_has_selfLoop, twoCycle_no_selfLoop⟩

/-!
## Part 2b: Remark 3.5 — Functional Bisimulation is Strictly Stronger

selfLoop and twoCycle are relationally bisimilar (loopCycleBisim above),
but NOT functionally bisimilar: no simulation selfLoop → twoCycle exists
because init_preserved forces stateMap () = .x, and twoCycle has no self-loop
at .x (nor at .y), so the self-loop () → () cannot be mapped.
-/

/-- **No simulation selfLoop → twoCycle exists.** init_preserved forces
    stateMap () = .x, but the self-loop () → () would need
    twoCycle.Step .x .x, which is Empty. -/
theorem no_sim_selfLoop_twoCycle : IsEmpty (Simulation selfLoop twoCycle) := by
  constructor
  intro f
  have step := f.stepMap (show selfLoop.Step () () from ())
  match f.stateMap (), step with
  | .x, step => exact nomatch step
  | .y, step => exact nomatch step

/-- selfLoop and twoCycle are NOT functionally bisimilar (no simulation
    in the forward direction exists at all). -/
theorem selfLoop_twoCycle_not_bisimilar : ¬ Bisimilar selfLoop twoCycle := by
  intro ⟨b⟩
  exact no_sim_selfLoop_twoCycle.false b.forward

/-- **Remark 3.5 (paper)**: Functional bisimulation (Definition 3.4) is strictly
    stronger than relational bisimulation (Definition 3.3).

    Witness: selfLoop and twoCycle are relationally bisimilar via loopCycleBisimR,
    but NOT functionally bisimilar (no simulation selfLoop → twoCycle exists).
    This demonstrates that the three-level hierarchy is genuine:
      geometric-theory equivalence ⊊ functional bisimulation ⊊ relational bisimulation ⊊ mutual simulation -/
theorem functional_strictly_stronger_than_relational :
    RelationallyBisimilar selfLoop twoCycle ∧ ¬ Bisimilar selfLoop twoCycle :=
  ⟨⟨loopCycleBisimR, loopCycleBisim, trivial⟩, selfLoop_twoCycle_not_bisimilar⟩

/-!
## Part 3: σ_conf — Cyclic Variable Sharing Separation

diamondGraph (a→b, a→c, b→d, c→d, d→d) ~ confTree (a→b, a→c, b→dL, c→dR, dL→dL, dR→dR)

The diamond has a join at d (b and c share successor d).
The tree has no join (b reaches dL, c reaches dR, no common successor).
Terminal states have self-loops so weak confluence is well-defined.
-/

/-- States of the diamond graph. -/
inductive DiamondState : Type
  | a : DiamondState
  | b : DiamondState
  | c : DiamondState
  | d : DiamondState
  deriving DecidableEq

/-- States of the confluence tree. -/
inductive ConfTreeState : Type
  | a : ConfTreeState
  | b : ConfTreeState
  | c : ConfTreeState
  | dL : ConfTreeState
  | dR : ConfTreeState
  deriving DecidableEq

/-- Diamond graph with self-loop at terminal: a→b, a→c, b→d, c→d, d→d. -/
def diamondGraph : RootedTS.{0, 0} where
  State := DiamondState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .a, .c => Unit
    | .b, .d => Unit
    | .c, .d => Unit
    | .d, .d => Unit
    | _, _ => Empty
  init := .a

/-- Confluence tree with self-loops at leaves: a→b, a→c, b→dL, c→dR, dL→dL, dR→dR. -/
def confTree : RootedTS.{0, 0} where
  State := ConfTreeState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .a, .c => Unit
    | .b, .dL => Unit
    | .c, .dR => Unit
    | .dL, .dL => Unit
    | .dR, .dR => Unit
    | _, _ => Empty
  init := .a

/-- Bisimulation relation: a↔a, b↔b, c↔c, d↔dL, d↔dR. -/
def confBisimR : DiamondState → ConfTreeState → Prop := fun s t =>
  match s, t with
  | .a, .a => True
  | .b, .b => True
  | .c, .c => True
  | .d, .dL => True
  | .d, .dR => True
  | _, _ => False

/-- confBisimR is a relational bisimulation between diamondGraph and confTree. -/
theorem confBisim : RelationalBisimulation diamondGraph confTree confBisimR := by
  constructor
  · -- Forth: given R(s,t) and step(s,s'), find t' with step(t,t') and R(s',t')
    intro s t hR s' hs'
    obtain ⟨step⟩ := hs'
    match s, s', step with
    | .a, .b, () =>
      match t with | .a => exact ⟨.b, ⟨()⟩, trivial⟩ | .b => exact hR.elim
                   | .c => exact hR.elim | .dL => exact hR.elim | .dR => exact hR.elim
    | .a, .c, () =>
      match t with | .a => exact ⟨.c, ⟨()⟩, trivial⟩ | .b => exact hR.elim
                   | .c => exact hR.elim | .dL => exact hR.elim | .dR => exact hR.elim
    | .b, .d, () =>
      match t with | .b => exact ⟨.dL, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .c => exact hR.elim | .dL => exact hR.elim | .dR => exact hR.elim
    | .c, .d, () =>
      match t with | .c => exact ⟨.dR, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .b => exact hR.elim | .dL => exact hR.elim | .dR => exact hR.elim
    | .d, .d, () =>
      match t with | .dL => exact ⟨.dL, ⟨()⟩, trivial⟩
                   | .dR => exact ⟨.dR, ⟨()⟩, trivial⟩
                   | .a => exact hR.elim | .b => exact hR.elim | .c => exact hR.elim
  · -- Back: given R(s,t) and step(t,t'), find s' with step(s,s') and R(s',t')
    intro s t hR t' ht'
    obtain ⟨step⟩ := ht'
    match t, t', step with
    | .a, .b, () =>
      match s with | .a => exact ⟨.b, ⟨()⟩, trivial⟩ | .b => exact hR.elim
                   | .c => exact hR.elim | .d => exact hR.elim
    | .a, .c, () =>
      match s with | .a => exact ⟨.c, ⟨()⟩, trivial⟩ | .b => exact hR.elim
                   | .c => exact hR.elim | .d => exact hR.elim
    | .b, .dL, () =>
      match s with | .b => exact ⟨.d, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .c => exact hR.elim | .d => exact hR.elim
    | .c, .dR, () =>
      match s with | .c => exact ⟨.d, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .b => exact hR.elim | .d => exact hR.elim
    | .dL, .dL, () =>
      match s with | .d => exact ⟨.d, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .b => exact hR.elim | .c => exact hR.elim
    | .dR, .dR, () =>
      match s with | .d => exact ⟨.d, ⟨()⟩, trivial⟩ | .a => exact hR.elim
                   | .b => exact hR.elim | .c => exact hR.elim

/-- diamondGraph satisfies WeakConfluence: all successors can reach d. -/
theorem diamondGraph_weakConfluent : WeakConfluence diamondGraph := by
  intro s t₁ t₂ ⟨step₁⟩ ⟨step₂⟩
  -- Every successor can step to d, so w = d always works
  match s, t₁, step₁, t₂, step₂ with
  | .a, .b, (), .b, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .b, (), .c, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .c, (), .b, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .a, .c, (), .c, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .b, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .c, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩
  | .d, .d, (), .d, () => exact ⟨.d, ⟨()⟩, ⟨()⟩⟩

/-- confTree does NOT satisfy WeakConfluence: b and c have no common successor.
    b→dL and c→dR, but step(c, dL) and step(b, dR) are both Empty. -/
theorem confTree_not_weakConfluent : ¬ WeakConfluence confTree := by
  intro h
  -- Instantiate at a, b, c (a has successors b and c)
  obtain ⟨w, ⟨step_bw⟩, ⟨step_cw⟩⟩ := h .a .b .c ⟨()⟩ ⟨()⟩
  -- b's only successor is dL, so w = dL
  match w, step_bw with
  | .dL, () =>
    -- But step(c, dL) is Empty
    exact nomatch step_cw

/-- **σ_conf separation.** -/
theorem confluence_separation :
    RelationalBisimulation diamondGraph confTree confBisimR ∧
    WeakConfluence diamondGraph ∧
    ¬ WeakConfluence confTree :=
  ⟨confBisim, diamondGraph_weakConfluent, confTree_not_weakConfluent⟩

/-!
## Part 4: σ_det — Consequent Equality (from SecondSeparation.lean)
-/

/-- twoCycle is deterministic. -/
theorem twoCycle_deterministic : Deterministic twoCycle := by
  intro s t₁ t₂ ⟨step₁⟩ ⟨step₂⟩
  match s, t₁, step₁, t₂, step₂ with
  | .x, .y, (), .y, () => rfl
  | .y, .x, (), .x, () => rfl

/-- hubSpokes is NOT deterministic: a has distinct successors b and c. -/
theorem hubSpokes_not_deterministic : ¬ Deterministic hubSpokes := by
  intro h
  have : HubSpokeState.b = HubSpokeState.c := h .a .b .c ⟨()⟩ ⟨()⟩
  exact HubSpokeState.noConfusion this

/-!
## Part 5: Summary
-/

/-- **Three-mechanism separation theorem.**

    Geometric logic extends diamond-only HML via three independent mechanisms.
    Each breaks bisimulation-invariance by imposing implicit identification
    constraints that bisimulation can split by duplicating states. -/
theorem three_mechanism_separation :
    -- (1) Equality: hubSpokes ~ twoCycle
    (Bisimilar hubSpokes twoCycle ∧ Deterministic twoCycle ∧ ¬ Deterministic hubSpokes) ∧
    -- (2) Cyclic sharing: diamondGraph ~ confTree via R
    (RelationalBisimulation diamondGraph confTree confBisimR ∧
     WeakConfluence diamondGraph ∧ ¬ WeakConfluence confTree) ∧
    -- (3) Repeated vars: selfLoop ~ twoCycle via R
    (RelationalBisimulation selfLoop twoCycle loopCycleBisimR ∧
     UniversalSelfLoop selfLoop ∧ ¬ UniversalSelfLoop twoCycle) :=
  ⟨⟨hubSpokes_twoCycle_bisimilar, twoCycle_deterministic, hubSpokes_not_deterministic⟩,
   confluence_separation,
   selfLoop_separation⟩

end RTS
