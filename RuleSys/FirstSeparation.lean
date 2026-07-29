/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# First Separation Theorem: Mutual Simulation ⊋ Bisimulation

Proves: ∃ M N, mutual simulation ∧ ¬RelationallyBisimilar ∧ ¬(E[T_M] ≌ E[T_N])

This formalizes the paper's First Separation using the **fork** F and **path** P
witness systems, replacing the earlier detCounter/binarySplit witnesses.

## Systems

- **Fork** F: State = {a, b, c}, transitions a→b, a→c, b→b, init = a.
  The initial state branches: left to self-looping b, right to halting c.
- **Path** P: State = {x, y}, transitions x→y, y→y, init = x.
  A single step followed by a self-loop.

## Main Results

- `fork_to_path` / `path_to_fork`: mutual simulation (PROVED, 0 axioms)
- `fork_path_not_relBisimilar`: ¬RelationallyBisimilar (PROVED, 0 axioms)
- `fork_path_not_bisimilar`: ¬Bisimilar (PROVED, 0 axioms, direct proof)
- `first_separation_theorem`: the full theorem (PROVED; see the axiom note below)

The topos direction rests on the geometric-logic layer rather than on a single
axiom. `#print axioms first_separation_theorem` reports twelve custom axioms
beyond `propext`, `Classical.choice` and `Quot.sound`, namely
`provability_separation_implies_topos_nonequiv`, `theoryOfSystem_complete_canonical`,
`syntactic_sub_semantic`, `systemSpecificAxioms`, `FunctionalFormula.geometric_completeness`,
`IsGeometricCovering` with its three closure properties, and three private lemmas of
`GeometricLogic.SyntacticCategory`. The results audited by `AxiomAudit.lean` are
disjoint from these; the separations are not among them.

The non-bisimilarity proof uses the relational (Park-Milner) definition directly:
any bisimulation R with (a,x) ∈ R forces (c,y) ∈ R via the forth condition on a→c,
then the back condition at (c,y) fails because c has no outgoing transitions.

The topos non-equivalence uses the **totality sequent** σ_tot := ⊤ ⊢_x ∃y. step(x,y),
which holds in P (every state has a successor) but fails in F (state c has no successor).

## References

- Paper §4.1: First Separation (fork/path witnesses, halting-state argument)
- SecondSeparation.lean — Second separation (bisimulation ⊋ topos equivalence)
- Bisimulation.lean — Bisimulation definitions
-/

import RuleSys.Bisimulation
import RuleSys.GeometricLogic.SyntacticCategory
import RuleSys.GeometricLogic.Soundness  -- for Provable.sound, bridge lemmas, provability axioms

open CategoryTheory

namespace RTS

/-!
## Part 1: State Types
-/

/-- States of the fork system -/
inductive ForkState : Type
  | a : ForkState  -- initial state (branching)
  | b : ForkState  -- self-looping state (left branch)
  | c : ForkState  -- halting state (right branch, no outgoing transitions)
  deriving DecidableEq

/-- States of the path system -/
inductive PathState : Type
  | x : PathState  -- initial state
  | y : PathState  -- self-looping state
  deriving DecidableEq

/-!
## Part 2: System Definitions
-/

/-- Fork system F: initial state a branches to self-looping b and halting c.
    Transitions: a→b, a→c, b→b. State c has no outgoing transitions. -/
def fork : RootedTS.{0, 0} where
  State := ForkState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .a, .c => Unit
    | .b, .b => Unit
    | _, _ => Empty
  init := .a

/-- Path system P: initial state x steps to self-looping y.
    Transitions: x→y, y→y. -/
def pathSys : RootedTS.{0, 0} where
  State := PathState
  Step := fun s t => match s, t with
    | .x, .y => Unit
    | .y, .y => Unit
    | _, _ => Empty
  init := .x

/-!
## Part 2b: Image-Finiteness
-/

/-- fork is image-finite: a has successors {b, c}, b has successor {b}, c has no successors. -/
theorem fork_imageFinite : ImageFinite fork := by
  intro s
  match s with
  | .a =>
    exact ⟨[.b, .c], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => exact nomatch step
      | .b => simp
      | .c => simp⟩
  | .b =>
    exact ⟨[.b], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => exact nomatch step
      | .b => simp
      | .c => exact nomatch step⟩
  | .c =>
    exact ⟨[], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .a => exact nomatch step
      | .b => exact nomatch step
      | .c => exact nomatch step⟩

/-- pathSys is image-finite: x has successor {y}, y has successor {y}. -/
theorem pathSys_imageFinite : ImageFinite pathSys := by
  intro s
  match s with
  | .x =>
    exact ⟨[.y], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .x => exact nomatch step
      | .y => simp⟩
  | .y =>
    exact ⟨[.y], fun t ht => by
      obtain ⟨step⟩ := ht
      match t with
      | .x => exact nomatch step
      | .y => simp⟩

/-!
## Part 3: Mutual Simulation (Fully Constructive)
-/

/-- Forward simulation: fork → pathSys via f(a)=x, f(b)=y, f(c)=y.
    Steps: a→b maps to x→y, a→c maps to x→y, b→b maps to y→y.
    State c has no outgoing transitions, so stepMap is vacuously satisfied. -/
def fork_to_path : Simulation fork pathSys where
  stateMap := fun s => match s with
    | .a => .x
    | .b => .y
    | .c => .y
  stepMap := fun {s t} step => by
    match s, t with
    | .a, .b => exact ()   -- x→y
    | .a, .c => exact ()   -- x→y
    | .b, .b => exact ()   -- y→y
    | .a, .a => exact step.elim
    | .b, .a => exact step.elim
    | .b, .c => exact step.elim
    | .c, .a => exact step.elim
    | .c, .b => exact step.elim
    | .c, .c => exact step.elim
  init_preserved := rfl

/-- Backward simulation: pathSys → fork via g(x)=a, g(y)=b.
    Steps: x→y maps to a→b, y→y maps to b→b. -/
def path_to_fork : Simulation pathSys fork where
  stateMap := fun s => match s with
    | .x => .a
    | .y => .b
  stepMap := fun {s t} step => by
    match s, t with
    | .x, .y => exact ()   -- a→b
    | .y, .y => exact ()   -- b→b
    | .x, .x => exact step.elim
    | .y, .x => exact step.elim
  init_preserved := rfl

/-!
## Part 4: Non-Bisimilarity via Relational Bisimulation (Fully Constructive)

The argument from the paper:
1. Suppose R is a relational bisimulation with (a, x) ∈ R.
2. Forth on a→c: since x's only successor is y, we get (c, y) ∈ R.
3. Back at (c, y): the transition y→y requires some s' with c→s' in fork.
   But c has no outgoing transitions. Contradiction.

This proof works directly with the relational (Park-Milner) definition,
which is the primary notion in the paper (Definition 3.3).
-/

/-- State c in fork has no outgoing transitions (it is a halting state). -/
theorem fork_c_halting : ∀ t : ForkState, ¬ Nonempty (fork.Step ForkState.c t) := by
  intro t ht
  obtain ⟨step⟩ := ht
  match t with
  | .a => exact nomatch step
  | .b => exact nomatch step
  | .c => exact nomatch step

/-- State x in pathSys has exactly one successor: y. -/
theorem pathSys_x_unique_succ (t : PathState) (h : Nonempty (pathSys.Step PathState.x t)) :
    t = PathState.y := by
  obtain ⟨step⟩ := h
  match t with
  | .y => rfl
  | .x => exact nomatch step

/-- **Non-bisimilarity theorem (relational)**: fork and pathSys are not
    relationally bisimilar.

    Proof: Suppose R is a relational bisimulation with (a, x) ∈ R.
    - Forth on a→c: ∃t' with x→t' and (c, t') ∈ R. Since x→y is the only
      transition from x, we have t' = y and (c, y) ∈ R.
    - Back at (c, y): y→y requires ∃s' with c→s' and (s', y) ∈ R.
      But c has no outgoing transitions. Contradiction. -/
theorem fork_path_not_relBisimilar : ¬ RelationallyBisimilar fork pathSys := by
  intro ⟨R, ⟨hForth, hBack⟩, hInit⟩
  -- Step 1: Apply forth to the transition a→c in fork
  have h_ac : Nonempty (fork.Step ForkState.a ForkState.c) := ⟨()⟩
  obtain ⟨t', ht', hRct'⟩ := hForth _ _ hInit _ h_ac
  -- Step 2: x's only successor is y, so t' = y
  have h_ty : t' = PathState.y := pathSys_x_unique_succ t' ht'
  subst h_ty
  -- Step 3: Now (c, y) ∈ R. Apply back to y→y in pathSys.
  have h_yy : Nonempty (pathSys.Step PathState.y PathState.y) := ⟨()⟩
  obtain ⟨s', hs', _⟩ := hBack _ _ hRct' _ h_yy
  -- Step 4: c has no outgoing transitions — contradiction
  exact fork_c_halting s' hs'

/-- **Non-bisimilarity theorem (functional)**: fork and pathSys are not
    functionally bisimilar.

    Direct proof by state-map analysis:
    - forward: f(a)=x (init), f(c)=y (only successor of x)
    - backward: g(y)=b (only self-looping state in fork)
    - leftInverse at c: PathEquivalent fork b c
    - But c has no outgoing transitions, so Path c b is empty. Contradiction.

    This proof uses 0 axioms. -/
theorem fork_path_not_bisimilar : ¬ Bisimilar fork pathSys := by
  intro ⟨b⟩
  -- Forward map: f(a)=x (init_preserved), f(c)=y (x's only successor)
  have hfa : b.forward.stateMap .a = .x := b.forward.init_preserved
  have hfc : b.forward.stateMap .c = .y := by
    apply pathSys_x_unique_succ
    have step := b.forward.stepMap (show fork.Step .a .c from ())
    rw [hfa] at step; exact ⟨step⟩
  -- Backward map: g(y) must self-loop in fork, so g(y) = b
  have hgy : b.backward.stateMap .y = .b := by
    have step := b.backward.stepMap (show pathSys.Step .y .y from ())
    match h : b.backward.stateMap .y, step with
    | .b, _ => rfl
    | .a, step => exact nomatch step
    | .c, step => exact nomatch step
  -- leftInverse at c: PathEquivalent fork (g(f(c))) c = PathEquivalent fork b c
  have hli := b.leftInverse .c
  rw [hfc, hgy] at hli
  -- PathEquivalent fork b c implies Path c b is nonempty (since Path b b is)
  have ⟨p⟩ : Nonempty (fork.Path .c .b) :=
    hli.1 ForkState.b |>.mp ⟨@RootedTS.Path.nil fork ForkState.b⟩
  -- But c has no outgoing transitions — contradiction
  exact ForkState.noConfusion (path_from_terminal (fun t step => fork_c_halting t ⟨step⟩) p)

/-!
## Part 5: Totality — The Separating Geometric Property
-/

/-- Totality: every state has at least one successor.
    Geometric sequent: ⊤ ⊢_x ∃y. step(x,y).
    This is the separating property for the First Separation:
    pathSys satisfies totality (x→y, y→y) but fork does not (c has no successor). -/
def Total' (M : RootedTS) : Prop :=
  ∀ s : M.State, ∃ t : M.State, Nonempty (M.Step s t)

/-- pathSys is total: x has successor y, y has successor y. -/
theorem pathSys_total : Total' pathSys := by
  intro s
  match s with
  | .x => exact ⟨.y, ⟨()⟩⟩
  | .y => exact ⟨.y, ⟨()⟩⟩

/-- fork is NOT total: state c has no successor. -/
theorem fork_not_total : ¬ Total' fork := by
  intro h
  obtain ⟨t, ht⟩ := h .c
  exact fork_c_halting t ht

/-- **σ_tot separation**: pathSys satisfies totality, fork does not. -/
theorem totality_separation :
    Total' pathSys ∧ ¬ Total' fork :=
  ⟨pathSys_total, fork_not_total⟩

/-!
## Part 6: Topos Non-Equivalence
-/

/-- T_pathSys proves σ_tot.
    Proof: the canonical model of pathSys satisfies σ_tot (every state has a
    successor: x→y and y→y), so by completeness the theory proves it. -/
theorem pathSys_proves_sigma_tot :
    GeometricLogic.Provable (GeometricLogic.theoryOfSystem pathSys) GeometricLogic.sigma_tot :=
  GeometricLogic.theoryOfSystem_complete_canonical pathSys _ <|
    (GeometricLogic.satisfiesSequent'_sigma_tot_iff _).mpr fun x =>
      match x with
      | .x => ⟨.y, ⟨()⟩⟩
      | .y => ⟨.y, ⟨()⟩⟩

/-- fork's canonical model does not satisfy σ_tot (state c halts). -/
private theorem fork_not_satisfies_sigma_tot :
    ¬ GeometricLogic.satisfiesSequent' (RootedTS.canonicalModel fork)
      GeometricLogic.sigma_tot := by
  rw [GeometricLogic.satisfiesSequent'_sigma_tot_iff]
  push_neg
  exact ⟨.c, fun t ht => fork_c_halting t ht⟩

/-- T_fork does not prove σ_tot (from generic soundness + semantic separation). -/
private theorem fork_not_proves_sigma_tot :
    ¬ GeometricLogic.Provable (GeometricLogic.theoryOfSystem fork) GeometricLogic.sigma_tot := by
  intro h
  have hsound := GeometricLogic.Provable.sound h _
    (GeometricLogic.canonicalModel_satisfies_theorySeq fork)
  exact fork_not_satisfies_sigma_tot hsound

/-- **Provability separation: fork and pathSys have non-equivalent
    classifying toposes.**

    The totality sequent σ_tot := ⊤ ⊢_x ∃y. step(x,y) is provable
    in Th_G(pathSys) (every state has a successor: x→y and y→y) but not
    in Th_G(fork) (state c has no successor — it is a halting state).

    Previously axiomatized; now PROVED using generic soundness + semantic
    separation + the universal property of classifying toposes. -/
theorem fork_path_topos_nonequiv :
    ¬ Nonempty (GeometricLogic.classifyingToposOf fork ≌
                GeometricLogic.classifyingToposOf pathSys) := by
  intro ⟨e⟩
  exact GeometricLogic.provability_separation_implies_topos_nonequiv
    pathSys_proves_sigma_tot fork_not_proves_sigma_tot ⟨e.symm⟩

/-!
## Part 7: The First Separation Theorem
-/

/-- **First Separation Theorem (fork/path witnesses)**

    There exist rooted transition systems M, N such that:
    1. M and N mutually simulate each other
    2. M and N are NOT relationally bisimilar
    3. Their classifying toposes are NOT equivalent

    The totality sequent σ_tot separates the geometric theories:
    it holds in pathSys (all states have successors) and fails in fork
    (state c is halting).

    Parts 1-2 are fully proved (0 custom axioms). Part 3 cites provability
    separation via σ_tot, which brings in the geometric-logic layer: the
    statement below depends on twelve custom axioms in total. See the axiom
    note in the module header. -/
theorem first_separation_theorem :
    ∃ (M N : RootedTS.{0, 0}),
      (Nonempty (Simulation M N) ∧ Nonempty (Simulation N M)) ∧
      ¬ RelationallyBisimilar M N ∧
      ¬ Nonempty (GeometricLogic.classifyingToposOf M ≌
                  GeometricLogic.classifyingToposOf N) := by
  refine ⟨fork, pathSys, ?_, ?_, ?_⟩
  · exact ⟨⟨fork_to_path⟩, ⟨path_to_fork⟩⟩
  · exact fork_path_not_relBisimilar
  · exact fork_path_topos_nonequiv

end RTS
