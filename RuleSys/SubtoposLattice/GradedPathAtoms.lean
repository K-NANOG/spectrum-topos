/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Graded Path Atoms for Depth-Bounded Observation Trees

This file introduces *graded path atoms* that solve the branching blindness problem
in propositional geometric theories of labeled transition systems.

## The Branching Blindness Problem

The base propositional geometric theory (from `LabeledTransitionSystems.lean`) uses
atoms `step_a(s,t)` encoding transition existence. This captures *which transitions
exist* but not *how transitions are distributed across intermediate states*. As a
result, the Lindenbaum algebras of `a.b + a.c` and `a.(b+c)` are both 5-element
lattices — the base theory cannot distinguish early choice from late choice.

Concretely, both systems have 2 free generators constrained by a single totality
relation `p ∨ q = ⊤`, yielding the same 5-element bounded distributive lattice
`{⊥, p ∧ q, p, q, ⊤}` regardless of whether the branching happens before or after
the initial `a`-step.

## The Depth-1 Path Atom Cure

We enrich the atom type with *depth-1 path atoms* `pathAtom_1(s, a, C)` encoding:
"there exists an intermediate state t such that s →^a t and t enables all transitions
in C". This captures branching structure because the set C of continuations must all
be reachable from a *single* intermediate state.

For `a.b + a.c` (vgTraceA): pathAtom_1(p0, a, {(b,p3),(c,p4)}) is ⊥ because no
single intermediate state after p0's a-step enables both b→p3 and c→p4. State p1
enables only b→p3, and p2 enables only c→p4.

For `a.(b+c)` (vgTraceB): pathAtom_1(q0, a, {(b,q2),(c,q3)}) is satisfiable because
q1 (the unique a-successor of q0) enables both b→q2 and c→q3.

This breaks the Lindenbaum isomorphism between the two systems.

## General PathAtom Concept (Documentation Only)

The graded path atom hierarchy generalizes to arbitrary depth:
- **depth 0**: atoms are `State × Label × State` (base transition atoms)
- **depth 1**: atoms are `State × Label × Finset(Label × State)` (this file)
- **depth d+1**: recursive — the continuation set C contains depth-d path atoms
  rather than flat `(Label × State)` pairs (deferred to Phase 127)

At each depth level, the path atoms encode properties visible to the corresponding
fragment of Hennessy-Milner Logic (HML). Depth 0 corresponds to O (trace formulas),
depth 1 to HML_pos (positive formulas with one level of diamond), and so on.

## References

- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990)
- Hennessy & Milner, "Algebraic Laws for Nondeterminism and Concurrency" (1985)
- Vickers, "Topology via Logic" (1989) — propositional geometric theories
-/

import RuleSys.SubtoposLattice.LabeledTransitionSystems
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

universe u

open GeometricLogic.Propositional

namespace RTS

/-!
## Part 1: Graded Atom Type

The `GradedAtom` inductive has two constructors:
- `base s a t`: the existing depth-0 labeled transition atom step_a(s,t)
- `depth1 s a C`: the depth-1 path atom pathAtom_1(s, a, C) encoding
  "∃t with s →^a t enabling all continuations in C"
-/

/-- Graded atoms for depth-bounded observation trees.

- `base s a t` represents the base labeled transition atom step_a(s,t):
  "the transition s →^a t exists"
- `depth1 s a C` represents the depth-1 path atom pathAtom_1(s, a, C):
  "there exists an intermediate state t such that s →^a t and for every
  (b, u) ∈ C, the transition t →^b u exists"

The depth-1 constructor encodes branching structure: which sets of continuations
are jointly reachable from a single intermediate state after an a-step from s. -/
inductive GradedAtom (State Label : Type*) : Type _
  | base : State → Label → State → GradedAtom State Label
  | depth1 : State → Label → Finset (Label × State) → GradedAtom State Label

/-!
## Part 2: DecidableEq and Fintype Instances
-/

/-- Decidable equality for `GradedAtom`, derived from decidable equality on
the component types. `Finset` has `DecidableEq` when the element type does. -/
instance gradedAtom_decidableEq {State Label : Type*}
    [DecidableEq State] [DecidableEq Label] : DecidableEq (GradedAtom State Label) :=
  fun a b => match a, b with
  | .base s₁ a₁ t₁, .base s₂ a₂ t₂ =>
    if hs : s₁ = s₂ then
      if ha : a₁ = a₂ then
        if ht : t₁ = t₂ then isTrue (by subst hs; subst ha; subst ht; rfl)
        else isFalse (by intro h; cases h; exact ht rfl)
      else isFalse (by intro h; cases h; exact ha rfl)
    else isFalse (by intro h; cases h; exact hs rfl)
  | .base _ _ _, .depth1 _ _ _ => isFalse (by intro h; cases h)
  | .depth1 _ _ _, .base _ _ _ => isFalse (by intro h; cases h)
  | .depth1 s₁ a₁ C₁, .depth1 s₂ a₂ C₂ =>
    if hs : s₁ = s₂ then
      if ha : a₁ = a₂ then
        if hC : C₁ = C₂ then isTrue (by subst hs; subst ha; subst hC; rfl)
        else isFalse (by intro h; cases h; exact hC rfl)
      else isFalse (by intro h; cases h; exact ha rfl)
    else isFalse (by intro h; cases h; exact hs rfl)

/-- Equivalence between `GradedAtom State Label` and the sum type
`(State × Label × State) ⊕ (State × Label × Finset (Label × State))`.
Used to derive `Fintype` for `GradedAtom`. -/
def GradedAtom.equivSum (State Label : Type*) :
    GradedAtom State Label ≃
      (State × Label × State) ⊕ (State × Label × Finset (Label × State)) where
  toFun
    | .base s a t => Sum.inl (s, a, t)
    | .depth1 s a C => Sum.inr (s, a, C)
  invFun
    | Sum.inl (s, a, t) => .base s a t
    | Sum.inr (s, a, C) => .depth1 s a C
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by cases x <;> simp

/-- `GradedAtom State Label` is finite when `State` and `Label` are finite.
The proof uses the equivalence to
`(State × Label × State) ⊕ (State × Label × Finset (Label × State))`
and the fact that `Finset` of a finite type is finite. -/
noncomputable instance gradedAtom_fintype {State Label : Type*}
    [Fintype State] [DecidableEq State] [Fintype Label] [DecidableEq Label] :
    Fintype (GradedAtom State Label) :=
  Fintype.ofEquiv _ (GradedAtom.equivSum State Label).symm

/-!
## Part 3: Valid Path Predicate

A depth-1 path atom `pathAtom_1(s, a, C)` is *valid* (satisfiable) if there exists
an intermediate state `t` such that `s →^a t` and for every `(b, u) ∈ C`, `t →^b u`.
This is the decidable predicate that determines which depth-1 atoms appear in the theory.
-/

/-- Check whether a depth-1 path atom `pathAtom_1(s, a, C)` is valid:
does there exist an intermediate state `t` such that `hasEdge s a t = true`
and for every `(b, u) ∈ C`, `hasEdge t b u = true`?

This is a decidable (Bool-valued) predicate that enumerates all possible
intermediate states `t` and checks the conjunction of edge conditions.

Marked `noncomputable` because `Multiset.toList` (used by Finset enumeration)
has no executable code in Lean 4. This is acceptable because the entire
`mkDepth1Theory` constructor is also noncomputable. -/
noncomputable def hasValidPath {State Label : Type*}
    [Fintype State] [DecidableEq State] [Fintype Label] [DecidableEq Label]
    (hasEdge : State → Label → State → Bool)
    (s : State) (a : Label) (C : Finset (Label × State)) : Bool :=
  Finset.univ.val.toList.any fun t =>
    hasEdge s a t && C.val.toList.all fun ⟨b, u⟩ => hasEdge t b u

/-!
## Part 4: Graded Theory Constructor

`mkDepth1Theory` extends the `mkLabeledTransitionTheory` pattern by adding depth-1
path atoms alongside the existing base transition atoms. The axiom groups are:

1. **Base non-edge exclusions**: `.base s a t ⊢ ⊥` for each non-edge (s, a, t)
2. **Base totality**: `⊤ ⊢ ∨_{(a,t)} .base s a t` for states with successors
3. **Depth-1 impossibility**: `.depth1 s a C ⊢ ⊥` for invalid path atoms
4. **Depth-1 totality**: `⊤ ⊢ ∨_{(a,C) valid} .depth1 s a C` for states with
   at least one valid depth-1 path atom

### Critical Test: Branching Blindness Broken

For vgTraceA (`a.b + a.c`):
- pathAtom_1(p0, a, {(b,p3),(c,p4)}) is INVALID (no single intermediate state
  after p0's a-step enables both b→p3 and c→p4)
- So `.depth1 p0 a {(b,p3),(c,p4)} ⊢ ⊥` is an axiom

For vgTraceB (`a.(b+c)`):
- pathAtom_1(q0, a, {(b,q2),(c,q3)}) is VALID (q1 enables both b→q2 and c→q3)
- So `.depth1 q0 a {(b,q2),(c,q3)}` is NOT forced to ⊥

This asymmetry creates different Lindenbaum algebras, breaking the isomorphism
that existed at the base (depth-0) level.
-/

/-- Build a `PropGeoTheory` with graded atoms (base + depth-1 path atoms)
from a finite state type, a finite label type, and a decidable edge predicate.

The atom type is `GradedAtom State Label`, combining:
- depth-0 atoms `.base s a t` (labeled transitions)
- depth-1 atoms `.depth1 s a C` (path atoms encoding branching structure)

Axiom groups:
1. Base non-edge exclusions: `.base s a t ⊢ ⊥` for non-edges
2. Base totality: `⊤ ⊢ ∨_{(a,t)} .base s a t` for states with successors
3. Depth-1 impossibility: `.depth1 s a C ⊢ ⊥` for invalid path atoms
4. Depth-1 totality: `⊤ ⊢ ∨_{(a,C) valid} .depth1 s a C` for states
   with at least one valid depth-1 path atom -/
noncomputable def mkDepth1Theory (State : Type) [Fintype State] [DecidableEq State]
    (Label : Type) [Fintype Label] [DecidableEq Label]
    (hasEdge : State → Label → State → Bool) : PropGeoTheory.{0} where
  Atoms := GradedAtom State Label
  axioms :=
    -- Group 1: Base non-edge exclusions: .base s a t ⊢ ⊥ for non-edges
    let baseNonEdgeAxioms : Finset (PropSequent (GradedAtom State Label)) :=
      Finset.univ.filter (fun (p : State × Label × State) =>
        hasEdge p.1 p.2.1 p.2.2 = false)
      |>.image (fun p => ⟨.atom (.base p.1 p.2.1 p.2.2), .bot⟩)
    -- Group 2: Base totality: ⊤ ⊢ ∨_{(a,t)} .base s a t for states with successors
    let baseTotalityAxioms : Finset (PropSequent (GradedAtom State Label)) :=
      (Finset.univ.filter (fun (s : State) =>
        (Finset.univ.filter (fun (at_ : Label × State) =>
          hasEdge s at_.1 at_.2 = true)).Nonempty)).image
        (fun s =>
          let successors := (Finset.univ.filter (fun (at_ : Label × State) =>
            hasEdge s at_.1 at_.2 = true)).val.toList
          let disjunction := mkDisj (successors.map
            (fun at_ => PropFormula.atom (GradedAtom.base s at_.1 at_.2)))
          ⟨.top, disjunction⟩)
    -- Group 3: Depth-1 impossibility: .depth1 s a C ⊢ ⊥ for invalid path atoms
    let depth1ImpossibilityAxioms : Finset (PropSequent (GradedAtom State Label)) :=
      Finset.univ.filter (fun (p : State × Label × Finset (Label × State)) =>
        hasValidPath hasEdge p.1 p.2.1 p.2.2 = false)
      |>.image (fun p => ⟨.atom (.depth1 p.1 p.2.1 p.2.2), .bot⟩)
    -- Group 4: Depth-1 totality: ⊤ ⊢ ∨_{(a,C) valid} .depth1 s a C
    -- for states with at least one valid depth-1 path atom
    let depth1TotalityAxioms : Finset (PropSequent (GradedAtom State Label)) :=
      (Finset.univ.filter (fun (s : State) =>
        (Finset.univ.filter (fun (p : Label × Finset (Label × State)) =>
          hasValidPath hasEdge s p.1 p.2 = true)).Nonempty)).image
        (fun s =>
          let validPaths := (Finset.univ.filter (fun (p : Label × Finset (Label × State)) =>
            hasValidPath hasEdge s p.1 p.2 = true)).val.toList
          let disjunction := mkDisj (validPaths.map
            (fun p => PropFormula.atom (GradedAtom.depth1 s p.1 p.2)))
          ⟨.top, disjunction⟩)
    baseNonEdgeAxioms ∪ baseTotalityAxioms ∪ depth1ImpossibilityAxioms ∪ depth1TotalityAxioms

end RTS
