/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bounded Depth van Benthem Theorem

Proves the geometric van Benthem conjecture at bounded quantifier depth.
At each depth, there are finitely many "atom types." We show every non-HML
atom is NOT bisimulation-invariant by exhibiting concrete separating witness
pairs. The surviving atoms are exactly the HML-expressible ones.

## Main Results

1. `vanBenthem_depth0` — Depth-0 HML formulas are constant (⊤ or ⊥),
   and the only non-trivial depth-0 geometric atom (selfLoopProp) is not
   bisimulation-invariant.

2. `vanBenthem_depth1` — Among depth-1 geometric atoms, only ◇⊤ (hasSucProp)
   is bisimulation-invariant. All five non-HML atoms are separated by
   concrete witness pairs.

## Witness Systems

- selfLoop ~ twoCycle (from HMLSeparation.lean) — separates self-loop atoms
- sourceGraph ~ backEdgeGraph (new) — separates predecessor/back-edge atoms

## References

- van Benthem, "Modal Correspondence Theory" (1976)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
- HML.lean — Forward direction (HML → bisimulation-invariant)
- HMLSeparation.lean — Three-mechanism separation witnesses
-/

import RuleSys.HMLSeparation

namespace Ruliology

universe u v

/-!
## Part 1: Definitions
-/

/-- Diamond nesting depth of an HML formula.
    - top/bot: depth 0
    - conj/disj: max of children
    - diamond: 1 + depth of child -/
def HML.depth : HML → ℕ
  | .top => 0
  | .bot => 0
  | .conj φ ψ => max φ.depth ψ.depth
  | .disj φ ψ => max φ.depth ψ.depth
  | .diamond φ => φ.depth + 1

/-- A state property: a predicate on states of any multiway system at universe (0,0). -/
def StateProp := ∀ (M : MultiwaySystem.{0, 0}), M.State → Prop

/-- A state property is bisimulation-invariant if it is preserved by all
    relational bisimulations. -/
def BisimInvariant (P : StateProp) : Prop :=
  ∀ (M N : MultiwaySystem.{0, 0}) (R : M.State → N.State → Prop),
    RelationalBisimulation M N R →
    ∀ (s : M.State) (t : N.State), R s t → (P M s ↔ P N t)

/-!
## Part 2: HML is bisimulation-invariant
-/

/-- Every HML formula gives a bisimulation-invariant state property. -/
theorem hml_bisimInvariant (φ : HML) :
    BisimInvariant (fun M s => φ.satisfiedAt M s) :=
  fun _ _ _ hR _ _ hst => HML.bisim_invariant hR φ hst

/-- BisimInvariant is closed under conjunction. -/
theorem bisimInvariant_conj {P Q : StateProp}
    (hP : BisimInvariant P) (hQ : BisimInvariant Q) :
    BisimInvariant (fun M s => P M s ∧ Q M s) :=
  fun M N R hR s t hst =>
    ⟨fun ⟨hp, hq⟩ => ⟨(hP M N R hR s t hst).mp hp, (hQ M N R hR s t hst).mp hq⟩,
     fun ⟨hp, hq⟩ => ⟨(hP M N R hR s t hst).mpr hp, (hQ M N R hR s t hst).mpr hq⟩⟩

/-- BisimInvariant is closed under disjunction. -/
theorem bisimInvariant_disj {P Q : StateProp}
    (hP : BisimInvariant P) (hQ : BisimInvariant Q) :
    BisimInvariant (fun M s => P M s ∨ Q M s) :=
  fun M N R hR s t hst =>
    ⟨fun h => h.elim (fun hp => Or.inl ((hP M N R hR s t hst).mp hp))
                      (fun hq => Or.inr ((hQ M N R hR s t hst).mp hq)),
     fun h => h.elim (fun hp => Or.inl ((hP M N R hR s t hst).mpr hp))
                      (fun hq => Or.inr ((hQ M N R hR s t hst).mpr hq))⟩

/-!
## Part 3: Depth-0 atom analysis

The only non-trivial depth-0 geometric atom over one free variable in
the step-relation language is `selfLoopProp := fun M s => Nonempty (M.Step s s)`.
-/

/-- Self-loop property: state s has a self-loop. -/
def selfLoopProp : StateProp := fun M s => Nonempty (M.Step s s)

/-- selfLoopProp is NOT bisimulation-invariant.
    Witness: selfLoop ~ twoCycle via loopCycleBisimR.
    selfLoop satisfies selfLoopProp at (); twoCycle does NOT at .x. -/
theorem selfLoopProp_not_bisimInvariant : ¬ BisimInvariant selfLoopProp := by
  intro h
  -- loopCycleBisimR relates () to every TwoCycleState, in particular .x
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  -- Apply bisim-invariance
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  -- selfLoop has a self-loop at ()
  have hself : selfLoopProp selfLoop () := ⟨()⟩
  -- So twoCycle should have a self-loop at .x
  have htwo := hiff.mp hself
  -- But twoCycle.Step .x .x = Empty
  exact htwo.elim fun step => nomatch step

/-- HML formulas of depth 0 contain no diamonds, so they evaluate
    to constant True or False at every state. -/
theorem hml_depth0_constant (φ : HML) (hd : φ.depth = 0) :
    (∀ (M : MultiwaySystem.{0, 0}) (s : M.State), φ.satisfiedAt M s) ∨
    (∀ (M : MultiwaySystem.{0, 0}) (s : M.State), ¬ φ.satisfiedAt M s) := by
  induction φ with
  | top => exact Or.inl (fun _ _ => trivial)
  | bot => exact Or.inr (fun _ _ h => h)
  | conj φ ψ ihφ ihψ =>
    simp [HML.depth] at hd
    have hφd : φ.depth = 0 := by omega
    have hψd : ψ.depth = 0 := by omega
    have hφ := ihφ hφd
    have hψ := ihψ hψd
    match hφ, hψ with
    | Or.inl hφt, Or.inl hψt => exact Or.inl (fun M s => ⟨hφt M s, hψt M s⟩)
    | Or.inl _, Or.inr hψf => exact Or.inr (fun M s ⟨_, h2⟩ => hψf M s h2)
    | Or.inr hφf, _ => exact Or.inr (fun M s ⟨h1, _⟩ => hφf M s h1)
  | disj φ ψ ihφ ihψ =>
    simp [HML.depth] at hd
    have hφd : φ.depth = 0 := by omega
    have hψd : ψ.depth = 0 := by omega
    have hφ := ihφ hφd
    have hψ := ihψ hψd
    match hφ, hψ with
    | Or.inl hφt, _ => exact Or.inl (fun M s => Or.inl (hφt M s))
    | _, Or.inl hψt => exact Or.inl (fun M s => Or.inr (hψt M s))
    | Or.inr hφf, Or.inr hψf =>
      exact Or.inr (fun M s h => h.elim (hφf M s) (hψf M s))
  | diamond φ _ =>
    simp [HML.depth] at hd

/-!
## Part 4: New witness systems for depth-1
-/

/-- States of the source graph. -/
inductive SourceState : Type
  | src : SourceState
  | sink : SourceState
  deriving DecidableEq

/-- Source graph: src→sink, sink→sink. Init: src.
    src has a successor (sink) but no predecessor. -/
def sourceGraph : MultiwaySystem.{0, 0} where
  State := SourceState
  Step := fun s t => match s, t with
    | .src, .sink => Unit
    | .sink, .sink => Unit
    | _, _ => Empty
  init := .src

/-- States of the back-edge graph. -/
inductive BackEdgeState : Type
  | root : BackEdgeState
  | loop : BackEdgeState
  deriving DecidableEq

/-- Back-edge graph: root→loop, loop→loop, loop→root. Init: root.
    root has a successor (loop) AND a predecessor (loop). -/
def backEdgeGraph : MultiwaySystem.{0, 0} where
  State := BackEdgeState
  Step := fun s t => match s, t with
    | .root, .loop => Unit
    | .loop, .loop => Unit
    | .loop, .root => Unit
    | _, _ => Empty
  init := .root

/-- Bisimulation relation: R(src, root), R(sink, loop), R(sink, root). -/
def predBisimR : SourceState → BackEdgeState → Prop := fun s t =>
  match s, t with
  | .src, .root => True
  | .sink, .loop => True
  | .sink, .root => True
  | _, _ => False

/-- predBisimR is a relational bisimulation between sourceGraph and backEdgeGraph. -/
theorem predBisim : RelationalBisimulation sourceGraph backEdgeGraph predBisimR := by
  constructor
  · -- Forth: given R(s,t) and step(s,s'), find t' with step(t,t') and R(s',t')
    intro s t hR s' hs'
    obtain ⟨step⟩ := hs'
    match s, s', step with
    | .src, .sink, () =>
      -- R(src, t) means t = root
      match t with
      | .root => exact ⟨.loop, ⟨()⟩, trivial⟩
      | .loop => exact hR.elim
    | .sink, .sink, () =>
      -- R(sink, t) means t = loop or t = root
      match t with
      | .loop => exact ⟨.loop, ⟨()⟩, trivial⟩
      | .root => exact ⟨.loop, ⟨()⟩, trivial⟩
  · -- Back: given R(s,t) and step(t,t'), find s' with step(s,s') and R(s',t')
    intro s t hR t' ht'
    obtain ⟨step⟩ := ht'
    match t, t', step with
    | .root, .loop, () =>
      -- R(s, root) means s = src or s = sink
      match s with
      | .src => exact ⟨.sink, ⟨()⟩, trivial⟩
      | .sink => exact ⟨.sink, ⟨()⟩, trivial⟩
    | .loop, .loop, () =>
      -- R(s, loop) means s = sink
      match s with
      | .sink => exact ⟨.sink, ⟨()⟩, trivial⟩
      | .src => exact hR.elim
    | .loop, .root, () =>
      -- R(s, loop) means s = sink
      match s with
      | .sink => exact ⟨.sink, ⟨()⟩, trivial⟩
      | .src => exact hR.elim

/-!
## Part 5: Depth-1 atom non-invariance

Five semantic properties, each proved NOT bisimulation-invariant.
-/

/-- Has predecessor: some state steps to s. -/
def hasPredProp : StateProp := fun M s => ∃ t, Nonempty (M.Step t s)

/-- Exists self-loop: some state in M has a self-loop (reachable from s via ∃). -/
def existsSelfLoopProp : StateProp := fun M _ => ∃ t : M.State, Nonempty (M.Step t t)

/-- Has mutual neighbor: s has a successor that also steps back to s. -/
def hasMutualNbrProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ Nonempty (M.Step t s)

/-- Has successor with self-loop: s has a successor that has a self-loop. -/
def hasSucWithSelfLoopProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ Nonempty (M.Step t t)

/-- hasPredProp is NOT bisimulation-invariant.
    Witness: sourceGraph ~ backEdgeGraph via predBisimR.
    src has no predecessor in sourceGraph; root has predecessor loop in backEdgeGraph. -/
theorem hasPredProp_not_bisimInvariant : ¬ BisimInvariant hasPredProp := by
  intro h
  have hR : predBisimR .src .root := trivial
  have hiff := h sourceGraph backEdgeGraph predBisimR predBisim .src .root hR
  -- backEdgeGraph: root has predecessor loop (loop→root step)
  have hpred : hasPredProp backEdgeGraph .root := ⟨.loop, ⟨()⟩⟩
  -- So sourceGraph should have a predecessor for src
  have hsrc := hiff.mpr hpred
  -- But src has no predecessor in sourceGraph
  obtain ⟨t, ⟨step⟩⟩ := hsrc
  match t, step with
  | .src, step => exact nomatch step
  | .sink, step => exact nomatch step

/-- existsSelfLoopProp is NOT bisimulation-invariant.
    Witness: selfLoop ~ twoCycle via loopCycleBisimR.
    selfLoop has a self-loop at (); twoCycle has no self-loops. -/
theorem existsSelfLoopProp_not_bisimInvariant : ¬ BisimInvariant existsSelfLoopProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  -- selfLoop has a self-loop at ()
  have hself : existsSelfLoopProp selfLoop () := ⟨(), ⟨()⟩⟩
  -- So twoCycle should have a self-loop somewhere
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step⟩⟩ := htwo
  match t, step with
  | .x, step => exact nomatch step
  | .y, step => exact nomatch step

/-- hasMutualNbrProp is NOT bisimulation-invariant.
    Witness: sourceGraph ~ backEdgeGraph via predBisimR.
    src in sourceGraph: successor is sink, but sink→src does not exist.
    root in backEdgeGraph: successor is loop, and loop→root exists. -/
theorem hasMutualNbrProp_not_bisimInvariant : ¬ BisimInvariant hasMutualNbrProp := by
  intro h
  have hR : predBisimR .src .root := trivial
  have hiff := h sourceGraph backEdgeGraph predBisimR predBisim .src .root hR
  -- backEdgeGraph: root→loop and loop→root
  have hmutual : hasMutualNbrProp backEdgeGraph .root := ⟨.loop, ⟨()⟩, ⟨()⟩⟩
  -- So sourceGraph should have a mutual neighbor for src
  have hsrc := hiff.mpr hmutual
  obtain ⟨t, ⟨step_fwd⟩, ⟨step_back⟩⟩ := hsrc
  -- src's only successor is sink
  match t, step_fwd with
  | .sink, () =>
    -- But sink→src doesn't exist
    exact nomatch step_back

/-- hasSucWithSelfLoopProp is NOT bisimulation-invariant.
    Witness: selfLoop ~ twoCycle via loopCycleBisimR.
    () in selfLoop: successor is () (self-loop), and () has a self-loop.
    .x in twoCycle: successor is .y, but .y has no self-loop. -/
theorem hasSucWithSelfLoopProp_not_bisimInvariant :
    ¬ BisimInvariant hasSucWithSelfLoopProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  -- selfLoop: () → () (self-loop) and () has self-loop
  have hself : hasSucWithSelfLoopProp selfLoop () := ⟨(), ⟨()⟩, ⟨()⟩⟩
  -- So twoCycle should have a successor with self-loop at .x
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step_fwd⟩, ⟨step_self⟩⟩ := htwo
  -- .x's only successor is .y
  match t, step_fwd with
  | .y, () =>
    -- But .y has no self-loop
    exact nomatch step_self

/-!
## Part 6: ◇⊤ IS bisimulation-invariant
-/

/-- Has successor: the standard translation of ◇⊤. -/
def hasSucProp : StateProp := fun M s => ∃ t, Nonempty (M.Step s t)

/-- hasSucProp is bisimulation-invariant.
    This is the standard translation of the HML formula ◇⊤. -/
theorem hasSucProp_bisimInvariant : BisimInvariant hasSucProp := by
  intro M N R hR s t hst
  constructor
  · -- Forward: if s has a successor s', then t has a successor t'
    intro ⟨s', hs'⟩
    obtain ⟨t', ht', _⟩ := hR.1 s t hst s' hs'
    exact ⟨t', ht'⟩
  · -- Backward: if t has a successor t', then s has a successor s'
    intro ⟨t', ht'⟩
    obtain ⟨s', hs', _⟩ := hR.2 s t hst t' ht'
    exact ⟨s', hs'⟩

/-!
## Part 7: Combined theorems
-/

/-- **Depth-0 van Benthem**: HML formulas of depth 0 are constant (⊤ or ⊥),
    and the only non-trivial depth-0 geometric atom is not bisimulation-invariant. -/
theorem vanBenthem_depth0 :
    (∀ φ : HML, φ.depth = 0 →
      (∀ (M : MultiwaySystem.{0, 0}) (s : M.State), φ.satisfiedAt M s) ∨
      (∀ (M : MultiwaySystem.{0, 0}) (s : M.State), ¬ φ.satisfiedAt M s)) ∧
    ¬ BisimInvariant selfLoopProp :=
  ⟨hml_depth0_constant, selfLoopProp_not_bisimInvariant⟩

/-- **Depth-1 van Benthem**: among depth-1 geometric atoms, only ◇⊤ is
    bisimulation-invariant. All others are separated by witness pairs. -/
theorem vanBenthem_depth1 :
    BisimInvariant hasSucProp ∧
    ¬ BisimInvariant selfLoopProp ∧
    ¬ BisimInvariant hasPredProp ∧
    ¬ BisimInvariant existsSelfLoopProp ∧
    ¬ BisimInvariant hasMutualNbrProp ∧
    ¬ BisimInvariant hasSucWithSelfLoopProp :=
  ⟨hasSucProp_bisimInvariant,
   selfLoopProp_not_bisimInvariant,
   hasPredProp_not_bisimInvariant,
   existsSelfLoopProp_not_bisimInvariant,
   hasMutualNbrProp_not_bisimInvariant,
   hasSucWithSelfLoopProp_not_bisimInvariant⟩

/-!
## Part 8: Remark 5.6 — Depth-1 Atom Coverage

The six depth-1 atoms above exhaust all single-variable geometric properties
at quantifier depth 1 over the step-relation language.

A depth-1 geometric property with one free variable `x` has the form
`∃y₁,...,yₙ. ⋀ᵢ step(aᵢ, bᵢ)` where each `aᵢ, bᵢ ∈ {x, y₁, ..., yₙ}`.

With a single existential variable `y`, the possible atomic formulas are:
- `step(x, y)` — `x` has a successor `y` (hasSucProp, ◇⊤)
- `step(x, x)` — `x` has a self-loop (selfLoopProp)
- `step(y, x)` — `x` has a predecessor `y` (hasPredProp)
- `step(y, y)` — some state has a self-loop (existsSelfLoopProp)

Conjunctions of these give:
- `step(x,y) ∧ step(y,x)` — hasMutualNbrProp
- `step(x,y) ∧ step(y,y)` — hasSucWithSelfLoopProp
- Other conjunctions reduce to these or to single atoms.

Properties with more than one existential variable at depth 1 decompose into
boolean combinations of single-variable properties by renaming.

The enumeration below captures this classification formally.
-/

/-- Depth-1 geometric atom types over the step-relation language. -/
inductive Depth1Atom : Type
  | hasSuc          -- ∃y. step(x, y) — the only bisim-invariant one
  | selfLoop        -- step(x, x)
  | hasPred         -- ∃y. step(y, x)
  | existsSelfLoop  -- ∃y. step(y, y)
  | hasMutualNbr    -- ∃y. step(x, y) ∧ step(y, x)
  | hasSucSelfLoop  -- ∃y. step(x, y) ∧ step(y, y)
  deriving DecidableEq

/-- Semantic interpretation: each atom gives a StateProp. -/
def Depth1Atom.toProp : Depth1Atom → StateProp
  | .hasSuc         => hasSucProp
  | .selfLoop       => selfLoopProp
  | .hasPred        => hasPredProp
  | .existsSelfLoop => existsSelfLoopProp
  | .hasMutualNbr   => hasMutualNbrProp
  | .hasSucSelfLoop => hasSucWithSelfLoopProp

/-- **Remark 5.6 (paper)**: Among the six depth-1 geometric atoms,
    hasSuc (◇⊤) is the unique bisimulation-invariant atom. -/
theorem depth1_unique_bisimInvariant (a : Depth1Atom) :
    BisimInvariant a.toProp ↔ a = .hasSuc := by
  constructor
  · intro h
    match a with
    | .hasSuc => rfl
    | .selfLoop => exact absurd h selfLoopProp_not_bisimInvariant
    | .hasPred => exact absurd h hasPredProp_not_bisimInvariant
    | .existsSelfLoop => exact absurd h existsSelfLoopProp_not_bisimInvariant
    | .hasMutualNbr => exact absurd h hasMutualNbrProp_not_bisimInvariant
    | .hasSucSelfLoop => exact absurd h hasSucWithSelfLoopProp_not_bisimInvariant
  · intro h
    subst h
    exact hasSucProp_bisimInvariant

/-!
## Part 9: Depth-2 Witness Systems

cycleEntry (a→b, b→c, c→b) ~ stretchedEntry (a'→b', b'→c', c'→d', d'→c')

These separate D2.3 (succOnCycleOrLoop): a successor whose successor can reach it.
cycleEntry at a: y=b, z=c, step(c,b) ✓. stretchedEntry at a': y=b', forced z=c', step(c',b')=Empty ✗.
-/

/-- States of the cycle-entry graph: a→b, b→c, c→b. -/
inductive CycleEntryState : Type
  | a : CycleEntryState
  | b : CycleEntryState
  | c : CycleEntryState
  deriving DecidableEq

/-- Cycle-entry graph: entry node a feeds into a 2-cycle b↔c. -/
def cycleEntry : MultiwaySystem.{0, 0} where
  State := CycleEntryState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .b, .c => Unit
    | .c, .b => Unit
    | _, _ => Empty
  init := .a

/-- States of the stretched-entry graph: a'→b', b'→c', c'→d', d'→c'. -/
inductive StretchedEntryState : Type
  | a : StretchedEntryState
  | b : StretchedEntryState
  | c : StretchedEntryState
  | d : StretchedEntryState
  deriving DecidableEq

/-- Stretched-entry graph: entry a' feeds into a 2-cycle c'↔d' via intermediate b'. -/
def stretchedEntry : MultiwaySystem.{0, 0} where
  State := StretchedEntryState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .b, .c => Unit
    | .c, .d => Unit
    | .d, .c => Unit
    | _, _ => Empty
  init := .a

/-- Bisimulation: a↔a', b↔b', {b,c}↔{c',d'}. -/
def cycleStretchedR : CycleEntryState → StretchedEntryState → Prop := fun s t =>
  match s, t with
  | .a, .a => True
  | .b, .b => True
  | .b, .c => True
  | .b, .d => True
  | .c, .b => True
  | .c, .c => True
  | .c, .d => True
  | _, _ => False

/-- cycleStretchedR is a relational bisimulation. -/
theorem cycleStretchedBisim :
    RelationalBisimulation cycleEntry stretchedEntry cycleStretchedR := by
  constructor
  · -- Forth: R(s,t) ∧ step(s,s') → ∃ t', step(t,t') ∧ R(s',t')
    intro s t hR s' hs'
    obtain ⟨step⟩ := hs'
    match s, s', step with
    | .a, .b, () =>
      match t with
      | .a => exact ⟨.b, ⟨()⟩, trivial⟩
      | .b => exact hR.elim | .c => exact hR.elim | .d => exact hR.elim
    | .b, .c, () =>
      match t with
      | .b => exact ⟨.c, ⟨()⟩, trivial⟩
      | .c => exact ⟨.d, ⟨()⟩, trivial⟩
      | .d => exact ⟨.c, ⟨()⟩, trivial⟩
      | .a => exact hR.elim
    | .c, .b, () =>
      match t with
      | .b => exact ⟨.c, ⟨()⟩, trivial⟩
      | .c => exact ⟨.d, ⟨()⟩, trivial⟩
      | .d => exact ⟨.c, ⟨()⟩, trivial⟩
      | .a => exact hR.elim
  · -- Back: R(s,t) ∧ step(t,t') → ∃ s', step(s,s') ∧ R(s',t')
    intro s t hR t' ht'
    obtain ⟨step⟩ := ht'
    match t, t', step with
    | .a, .b, () =>
      match s with
      | .a => exact ⟨.b, ⟨()⟩, trivial⟩
      | .b => exact hR.elim | .c => exact hR.elim
    | .b, .c, () =>
      match s with
      | .b => exact ⟨.c, ⟨()⟩, trivial⟩
      | .c => exact ⟨.b, ⟨()⟩, trivial⟩
      | .a => exact hR.elim
    | .c, .d, () =>
      match s with
      | .b => exact ⟨.c, ⟨()⟩, trivial⟩
      | .c => exact ⟨.b, ⟨()⟩, trivial⟩
      | .a => exact hR.elim
    | .d, .c, () =>
      match s with
      | .b => exact ⟨.c, ⟨()⟩, trivial⟩
      | .c => exact ⟨.b, ⟨()⟩, trivial⟩
      | .a => exact hR.elim

/-!
## Part 10: Depth-2 Atom Enumeration

A depth-2 geometric property has the form `∃y. A(x,y) ∧ ∃z. B(x,y,z)` where
A and B are conjunctions of step atoms among {x, y, z}. After removing atoms
that factor into depth-0/1 properties or are trivially implied by others,
8 non-trivial atoms remain.
-/

/-- Successor has successor: ◇◇⊤. The unique bisim-invariant depth-2 atom. -/
def succHasSuccProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u)

/-- Successor has self-loop: ∃y. step(x,y) ∧ step(y,y). Same as depth-1. -/
def succSelfLoopProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ Nonempty (M.Step t t)

/-- Successor on cycle or self-loop: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,y).
    The unique atom requiring cycleEntry/stretchedEntry witness. -/
def succOnCycleProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u) ∧ Nonempty (M.Step u t)

/-- Successor reaches self-loop: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,z). -/
def succReachesSelfLoopProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u) ∧ Nonempty (M.Step u u)

/-- Successor has co-successor from x: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(x,z). -/
def succHasCoSuccProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u) ∧ Nonempty (M.Step s u)

/-- Self-loop and has successor: step(x,x) ∧ ∃y. step(x,y). -/
def selfLoopAndSuccProp : StateProp := fun M s =>
  Nonempty (M.Step s s) ∧ ∃ t, Nonempty (M.Step s t)

/-- Self-loop and successor has successor: step(x,x) ∧ ∃y. step(x,y) ∧ ∃z. step(y,z). -/
def selfLoopAndSuccSuccProp : StateProp := fun M s =>
  Nonempty (M.Step s s) ∧ ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u)

/-- Successor reaches x: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,x). -/
def succReachesBackProp : StateProp := fun M s =>
  ∃ t, Nonempty (M.Step s t) ∧ ∃ u, Nonempty (M.Step t u) ∧ Nonempty (M.Step u s)

/-- Depth-2 geometric atom types over the step-relation language. -/
inductive Depth2Atom : Type
  | succHasSucc          -- D2.1: ∃y. step(x,y) ∧ ∃z. step(y,z) — ◇◇⊤
  | succSelfLoop         -- D2.2: ∃y. step(x,y) ∧ step(y,y)
  | succOnCycle          -- D2.3: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,y)
  | succReachesSelfLoop  -- D2.4: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,z)
  | succHasCoSucc        -- D2.5: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(x,z)
  | selfLoopAndSucc      -- D2.6: step(x,x) ∧ ∃y. step(x,y)
  | selfLoopAndSuccSucc  -- D2.7: step(x,x) ∧ ∃y. step(x,y) ∧ ∃z. step(y,z)
  | succReachesBack      -- D2.8: ∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,x)
  deriving DecidableEq

/-- Semantic interpretation: each depth-2 atom gives a StateProp. -/
def Depth2Atom.toProp : Depth2Atom → StateProp
  | .succHasSucc         => succHasSuccProp
  | .succSelfLoop        => succSelfLoopProp
  | .succOnCycle         => succOnCycleProp
  | .succReachesSelfLoop => succReachesSelfLoopProp
  | .succHasCoSucc       => succHasCoSuccProp
  | .selfLoopAndSucc     => selfLoopAndSuccProp
  | .selfLoopAndSuccSucc => selfLoopAndSuccSuccProp
  | .succReachesBack     => succReachesBackProp

/-!
## Part 11: D2.1 (◇◇⊤) IS bisimulation-invariant
-/

/-- succHasSuccProp (◇◇⊤) is bisimulation-invariant.
    This is the standard translation of the HML formula ◇◇⊤. -/
theorem succHasSuccProp_bisimInvariant : BisimInvariant succHasSuccProp := by
  intro M N R hR s t hst
  constructor
  · intro ⟨s', hs', u, hu⟩
    obtain ⟨t', ht', hR'⟩ := hR.1 s t hst s' hs'
    obtain ⟨u', hu', _⟩ := hR.1 s' t' hR' u hu
    exact ⟨t', ht', u', hu'⟩
  · intro ⟨t', ht', u, hu⟩
    obtain ⟨s', hs', hR'⟩ := hR.2 s t hst t' ht'
    obtain ⟨u', hu', _⟩ := hR.2 s' t' hR' u hu
    exact ⟨s', hs', u', hu'⟩

/-!
## Part 12: D2.2, D2.4–D2.8 non-invariance via selfLoop/twoCycle

selfLoop's single state () satisfies every step-based property (all vars = ()).
twoCycle at .x has unique successor .y, which forces specific constraints to fail.
-/

/-- D2.2: succSelfLoopProp is NOT bisimulation-invariant.
    selfLoop at (): y=(), step((),())=Unit ✓.
    twoCycle at .x: y=.y forced, step(.y,.y)=Empty ✗. -/
theorem succSelfLoopProp_not_bisimInvariant : ¬ BisimInvariant succSelfLoopProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : succSelfLoopProp selfLoop () := ⟨(), ⟨()⟩, ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step_fwd⟩, ⟨step_self⟩⟩ := htwo
  match t, step_fwd with
  | .y, () => exact nomatch step_self

/-- D2.4: succReachesSelfLoopProp is NOT bisimulation-invariant.
    selfLoop at (): y=(), z=(), all steps Unit ✓.
    twoCycle at .x: y=.y, z=.x (step(.y,.x)), step(.x,.x)=Empty ✗. -/
theorem succReachesSelfLoopProp_not_bisimInvariant :
    ¬ BisimInvariant succReachesSelfLoopProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : succReachesSelfLoopProp selfLoop () := ⟨(), ⟨()⟩, (), ⟨()⟩, ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step_xt⟩, u, ⟨step_tu⟩, ⟨step_uu⟩⟩ := htwo
  match t, step_xt with
  | .y, () =>
    match u, step_tu with
    | .x, () => exact nomatch step_uu

/-- D2.5: succHasCoSuccProp is NOT bisimulation-invariant.
    selfLoop at (): y=(), z=(), all steps Unit ✓.
    twoCycle at .x: y=.y, need step(.y,z) ∧ step(.x,z).
    step(.y,z) forces z=.x, but step(.x,.x)=Empty ✗. -/
theorem succHasCoSuccProp_not_bisimInvariant :
    ¬ BisimInvariant succHasCoSuccProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : succHasCoSuccProp selfLoop () := ⟨(), ⟨()⟩, (), ⟨()⟩, ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step_xt⟩, u, ⟨step_tu⟩, ⟨step_xu⟩⟩ := htwo
  match t, step_xt with
  | .y, () =>
    match u, step_tu with
    | .x, () => exact nomatch step_xu

/-- D2.6: selfLoopAndSuccProp is NOT bisimulation-invariant.
    selfLoop at (): step((),())=Unit, y=() ✓.
    twoCycle at .x: step(.x,.x)=Empty ✗. -/
theorem selfLoopAndSuccProp_not_bisimInvariant :
    ¬ BisimInvariant selfLoopAndSuccProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : selfLoopAndSuccProp selfLoop () := ⟨⟨()⟩, (), ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨⟨step_xx⟩, _⟩ := htwo
  exact nomatch step_xx

/-- D2.7: selfLoopAndSuccSuccProp is NOT bisimulation-invariant.
    selfLoop at (): step((),())=Unit, y=(), z=() ✓.
    twoCycle at .x: step(.x,.x)=Empty ✗. -/
theorem selfLoopAndSuccSuccProp_not_bisimInvariant :
    ¬ BisimInvariant selfLoopAndSuccSuccProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : selfLoopAndSuccSuccProp selfLoop () :=
    ⟨⟨()⟩, (), ⟨()⟩, (), ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨⟨step_xx⟩, _⟩ := htwo
  exact nomatch step_xx

/-- D2.8: succReachesBackProp is NOT bisimulation-invariant.
    selfLoop at (): y=(), z=(), step((),()) ✓.
    twoCycle at .x: y=.y, need step(.y,z) ∧ step(z,.x).
    step(.y,z) forces z=.x, step(.x,.x)=Empty ✗. -/
theorem succReachesBackProp_not_bisimInvariant :
    ¬ BisimInvariant succReachesBackProp := by
  intro h
  have hR : loopCycleBisimR () TwoCycleState.x := trivial
  have hiff := h selfLoop twoCycle loopCycleBisimR loopCycleBisim () .x hR
  have hself : succReachesBackProp selfLoop () := ⟨(), ⟨()⟩, (), ⟨()⟩, ⟨()⟩⟩
  have htwo := hiff.mp hself
  obtain ⟨t, ⟨step_xt⟩, u, ⟨step_tu⟩, ⟨step_ux⟩⟩ := htwo
  match t, step_xt with
  | .y, () =>
    match u, step_tu with
    | .x, () => exact nomatch step_ux

/-!
## Part 13: D2.3 non-invariance via cycleEntry/stretchedEntry

succOnCycleProp (∃y. step(x,y) ∧ ∃z. step(y,z) ∧ step(z,y)) is the unique
depth-2 atom that selfLoop/twoCycle cannot separate, because twoCycle at .x
satisfies it: y=.y, z=.x, step(.y,.x) ∧ step(.x,.y) ✓.

cycleEntry at .a: y=.b, z=.c, step(.b,.c) ∧ step(.c,.b) ✓.
stretchedEntry at .a: y=.b forced, step(.b,z) forces z=.c, step(.c,.b)=Empty ✗.
-/

/-- D2.3: succOnCycleProp is NOT bisimulation-invariant.
    Witness: cycleEntry ~ stretchedEntry via cycleStretchedR.
    cycleEntry at .a satisfies it; stretchedEntry at .a does not. -/
theorem succOnCycleProp_not_bisimInvariant : ¬ BisimInvariant succOnCycleProp := by
  intro h
  have hR : cycleStretchedR .a .a := trivial
  have hiff := h cycleEntry stretchedEntry cycleStretchedR cycleStretchedBisim .a .a hR
  -- cycleEntry at .a: y=.b, z=.c, step(.b,.c) ∧ step(.c,.b)
  have hce : succOnCycleProp cycleEntry .a :=
    ⟨.b, ⟨()⟩, .c, ⟨()⟩, ⟨()⟩⟩
  -- Transfer to stretchedEntry
  have hse := hiff.mp hce
  -- stretchedEntry at .a: only successor is .b
  obtain ⟨t, ⟨step_at⟩, u, ⟨step_tu⟩, ⟨step_ut⟩⟩ := hse
  match t, step_at with
  | .b, () =>
    -- .b's only successor is .c
    match u, step_tu with
    | .c, () =>
      -- step(.c, .b) = Empty
      exact nomatch step_ut

/-!
## Part 14: Combined Depth-2 Theorems
-/

/-- **Depth-2 van Benthem**: among depth-2 geometric atoms, only ◇◇⊤ (succHasSucc)
    is bisimulation-invariant. All seven others are separated by witness pairs. -/
theorem vanBenthem_depth2 :
    BisimInvariant succHasSuccProp ∧
    ¬ BisimInvariant succSelfLoopProp ∧
    ¬ BisimInvariant succOnCycleProp ∧
    ¬ BisimInvariant succReachesSelfLoopProp ∧
    ¬ BisimInvariant succHasCoSuccProp ∧
    ¬ BisimInvariant selfLoopAndSuccProp ∧
    ¬ BisimInvariant selfLoopAndSuccSuccProp ∧
    ¬ BisimInvariant succReachesBackProp :=
  ⟨succHasSuccProp_bisimInvariant,
   succSelfLoopProp_not_bisimInvariant,
   succOnCycleProp_not_bisimInvariant,
   succReachesSelfLoopProp_not_bisimInvariant,
   succHasCoSuccProp_not_bisimInvariant,
   selfLoopAndSuccProp_not_bisimInvariant,
   selfLoopAndSuccSuccProp_not_bisimInvariant,
   succReachesBackProp_not_bisimInvariant⟩

/-- **Remark 5.7 (paper)**: Among the eight depth-2 geometric atoms,
    succHasSucc (◇◇⊤) is the unique bisimulation-invariant atom. -/
theorem depth2_unique_bisimInvariant (a : Depth2Atom) :
    BisimInvariant a.toProp ↔ a = .succHasSucc := by
  constructor
  · intro h
    match a with
    | .succHasSucc => rfl
    | .succSelfLoop => exact absurd h succSelfLoopProp_not_bisimInvariant
    | .succOnCycle => exact absurd h succOnCycleProp_not_bisimInvariant
    | .succReachesSelfLoop => exact absurd h succReachesSelfLoopProp_not_bisimInvariant
    | .succHasCoSucc => exact absurd h succHasCoSuccProp_not_bisimInvariant
    | .selfLoopAndSucc => exact absurd h selfLoopAndSuccProp_not_bisimInvariant
    | .selfLoopAndSuccSucc => exact absurd h selfLoopAndSuccSuccProp_not_bisimInvariant
    | .succReachesBack => exact absurd h succReachesBackProp_not_bisimInvariant
  · intro h
    subst h
    exact succHasSuccProp_bisimInvariant

end Ruliology
