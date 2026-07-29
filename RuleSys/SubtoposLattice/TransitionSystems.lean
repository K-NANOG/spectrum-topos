/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Transition-Enriched Propositional Geometric Theories

This file defines propositional geometric theories where atoms represent
*transition pairs* step(s,t) rather than state occupancy propositions.

## Motivation

The state-atom theories in `SmallSystems.lean` encode "being in state s" as atoms.
This makes transitions invisible: systems with the same number of states get
identical Lindenbaum algebras regardless of transition structure (e.g., toggle and
chain3 both have 2-atom / 3-atom theories). Transition-enriched theories make the
step structure visible by using `State × State` as the atom type.

## Construction

For a finite state type with a decidable edge predicate `hasEdge : State → State → Bool`:

- **Atoms**: `State × State` — atom `(s,t)` represents "transition s → t fires"
- **Non-edge exclusions**: `step(s,t) ⊢ ⊥` for each pair where `hasEdge s t = false`
- **Totality per state**: `⊤ ⊢ ∨_{t} step(s,t)` for states with at least one successor

## Deterministic Collapse

For deterministic systems (each state has exactly one successor), every transition
atom is forced: the unique outgoing edge atom is forced to ⊤ by totality, and all
non-edge atoms are forced to ⊥ by exclusion. With no free generators, the
Lindenbaum algebra collapses to `{⊥, ⊤} ≅ Bool` (cardinality 2).

This contrasts with state-atom theories: singleLoop=2, toggle=4, chain3=8.
Transition atoms discriminate by *branching structure* rather than state count.
The enrichment becomes meaningful for nondeterministic systems (Phase 105).

## References

- Vickers, "Topology via Logic" (1989) — propositional geometric theories
- Johnstone, "Stone Spaces" (1982) — Lindenbaum algebras
-/

import RuleSys.GeometricLogic.PropositionalLindenbaum
import RuleSys.GeometricLogic.SyntacticCoverage
import RuleSys.SubtoposLattice.SmallSystems
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

universe u

open GeometricLogic.Propositional

namespace RTS

/-!
## Part 1: Generic Transition Theory Construction

We define a generic helper `mkDisj` to build left-associated disjunctions from
a list of formulas, and `mkTransitionTheory` to build a `PropGeoTheory` from a
decidable edge predicate on a finite state type.
-/

/-- Build a left-associated disjunction from a list of formulas.

Returns `⊥` for the empty list, the single formula for a singleton list,
and left-associates for longer lists: `((a ∨ b) ∨ c)`. -/
def mkDisj {α : Type u} : List (PropFormula α) → PropFormula α
  | [] => .bot
  | φ :: rest => rest.foldl (fun acc ψ => .disj acc ψ) φ

/-- Build a `PropGeoTheory` from a finite state type and a decidable edge predicate.

Atoms are `State × State` pairs. The axioms encode:
1. **Non-edge exclusions**: `step(s,t) ⊢ ⊥` for each `(s,t)` where `hasEdge s t = false`
2. **Totality per state**: `⊤ ⊢ ∨_{t : hasEdge s t} step(s,t)` for each state `s`
   that has at least one successor -/
noncomputable def mkTransitionTheory (State : Type) [Fintype State] [DecidableEq State]
    (hasEdge : State → State → Bool) : PropGeoTheory.{0} where
  Atoms := State × State
  axioms :=
    -- Non-edge exclusions: step(s,t) ⊢ ⊥ for non-edges
    let nonEdgeAxioms : Finset (PropSequent (State × State)) :=
      Finset.univ.filter (fun (p : State × State) => hasEdge p.1 p.2 = false)
      |>.image (fun p => ⟨.atom p, .bot⟩)
    -- Totality axioms: ⊤ ⊢ ∨_t step(s,t) for states with successors
    let totalityAxioms : Finset (PropSequent (State × State)) :=
      (Finset.univ.filter (fun (s : State) =>
        (Finset.univ.filter (fun t => hasEdge s t = true)).Nonempty)).image
        (fun s =>
          let successors := (Finset.univ.filter (fun t => hasEdge s t = true)).val.toList
          let disjunction := mkDisj (successors.map (fun t => PropFormula.atom (s, t)))
          ⟨.top, disjunction⟩)
    nonEdgeAxioms ∪ totalityAxioms

/-!
## Part 2: Concrete Edge Predicates

Edge predicates for the three existing deterministic systems from SmallSystems.lean.
-/

/-- Edge predicate for singleLoop: s → s (self-loop). -/
def singleLoop_hasEdge : SingleLoopState → SingleLoopState → Bool
  | .s, .s => true

/-- Edge predicate for toggle: a ↔ b (bidirectional). -/
def toggle_hasEdge : ToggleState → ToggleState → Bool
  | .a, .b => true
  | .b, .a => true
  | _, _ => false

/-- Edge predicate for chain3: a → b → c (linear chain). -/
def chain3_hasEdge : Chain3State → Chain3State → Bool
  | .a, .b => true
  | .b, .c => true
  | _, _ => false

/-!
## Part 3: Concrete Transition-Enriched Theories

Each theory uses `State × State` as atoms, with non-edge exclusions and totality axioms.
We define these using the generic `mkTransitionTheory` construction.
-/

/-- Transition-enriched propositional geometric theory of the singleLoop system.

**Atoms**: `SingleLoopState × SingleLoopState` = 1 atom: step(s,s).
**Axioms**:
- ⊤ ⊢ step(s,s) — totality: s has successor s
No non-edge axioms since the only pair (s,s) is an edge. -/
noncomputable def singleLoopTransTheory : PropGeoTheory.{0} :=
  mkTransitionTheory SingleLoopState singleLoop_hasEdge

/-- Transition-enriched propositional geometric theory of the toggle system.

**Atoms**: `ToggleState × ToggleState` = 4 atoms: step(a,a), step(a,b), step(b,a), step(b,b).
**Axioms**:
- step(a,a) ⊢ ⊥ — non-edge: a does not self-loop
- step(b,b) ⊢ ⊥ — non-edge: b does not self-loop
- ⊤ ⊢ step(a,b) — totality: a's unique successor is b
- ⊤ ⊢ step(b,a) — totality: b's unique successor is a -/
noncomputable def toggleTransTheory : PropGeoTheory.{0} :=
  mkTransitionTheory ToggleState toggle_hasEdge

/-- Transition-enriched propositional geometric theory of the chain3 system.

**Atoms**: `Chain3State × Chain3State` = 9 atoms.
**Axioms**:
- 7 non-edge exclusions: step(a,a), step(a,c), step(b,a), step(b,b), step(c,a), step(c,b), step(c,c) ⊢ ⊥
- ⊤ ⊢ step(a,b) — totality: a's unique successor is b
- ⊤ ⊢ step(b,c) — totality: b's unique successor is c
Note: state c has no successors, so there is no totality axiom for c. -/
noncomputable def chain3TransTheory : PropGeoTheory.{0} :=
  mkTransitionTheory Chain3State chain3_hasEdge

/-!
## Part 4: Axiomatized Lindenbaum Algebra Structure

### The Deterministic Collapse Phenomenon

For a deterministic system where each state has at most one successor, every
transition atom is either:
- **Forced to ⊤**: the unique outgoing edge from a state with a successor
  (by the totality axiom `⊤ ⊢ step(s, successor(s))`)
- **Forced to ⊥**: a non-edge pair (by the exclusion axiom `step(s,t) ⊢ ⊥`)

Since every atom is determined (no free generators remain), the Lindenbaum algebra
degenerates to `{⊥, ⊤} ≅ Bool`, with cardinality 2.

This is the expected behavior: transition-enriched theories carry no extra
information for deterministic systems. The enrichment becomes meaningful only
for nondeterministic systems where a state has multiple successors — the
disjunction `⊤ ⊢ step(s,t₁) ∨ step(s,t₂)` leaves the individual atoms
undetermined, creating free generators in the Lindenbaum algebra.

**Contrast with state-atom theories** (SmallSystems.lean):
- singleLoopTheory: card = 2 (1 atom)
- toggleTheory: card = 4 (2 atoms)
- chain3Theory: card = 8 (3 atoms)

State-atom cardinality scales with state count. Transition-atom cardinality
for deterministic systems is uniformly 2, regardless of state count.
Phase 105's nondeterministic systems will break this uniformity.
-/

/-- The Lindenbaum algebra of singleLoopTransTheory is order-isomorphic to Bool.

**Mathematical justification**: The single atom step(s,s) is forced to ⊤
by the totality axiom `⊤ ⊢ step(s,s)`. With no free generators,
every formula is provably equivalent to ⊤ or ⊥. The algebra has
exactly 2 elements: [⊥] < [⊤] ≅ Bool. -/
axiom singleLoopTrans_algebra_iso :
    Nonempty (LindenbaumAlgebra singleLoopTransTheory ≃o Bool)

/-- The Lindenbaum algebra of toggleTransTheory is order-isomorphic to Bool.

**Mathematical justification**: Of the 4 atoms (a,a), (a,b), (b,a), (b,b):
- step(a,a) and step(b,b) are forced to ⊥ by non-edge exclusion
- step(a,b) is forced to ⊤ by totality for state a (unique successor b)
- step(b,a) is forced to ⊤ by totality for state b (unique successor a)
All atoms determined, no free generators → Lindenbaum = {⊥, ⊤} ≅ Bool. -/
axiom toggleTrans_algebra_iso :
    Nonempty (LindenbaumAlgebra toggleTransTheory ≃o Bool)

/-- The Lindenbaum algebra of chain3TransTheory is order-isomorphic to Bool.

**Mathematical justification**: Of the 9 atoms:
- 7 non-edges forced to ⊥: (a,a), (a,c), (b,a), (b,b), (c,a), (c,b), (c,c)
- step(a,b) forced to ⊤ by totality for state a (unique successor b)
- step(b,c) forced to ⊤ by totality for state b (unique successor c)
State c has no successors (no totality axiom), but all step(c,*) are non-edges.
All atoms determined → Lindenbaum = {⊥, ⊤} ≅ Bool. -/
axiom chain3Trans_algebra_iso :
    Nonempty (LindenbaumAlgebra chain3TransTheory ≃o Bool)

/-!
## Part 5: Cardinality Theorems

Derived from the axiomatized isomorphisms: the underlying `Equiv` gives
`Fintype.card` equalities. Each transition-enriched deterministic theory
has Lindenbaum algebra of cardinality 2.
-/

/-- The Lindenbaum algebra of singleLoopTransTheory has exactly 2 elements. -/
theorem singleLoopTrans_algebra_card :
    Fintype.card (LindenbaumAlgebra singleLoopTransTheory) = 2 := by
  obtain ⟨e⟩ := singleLoopTrans_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

/-- The Lindenbaum algebra of toggleTransTheory has exactly 2 elements. -/
theorem toggleTrans_algebra_card :
    Fintype.card (LindenbaumAlgebra toggleTransTheory) = 2 := by
  obtain ⟨e⟩ := toggleTrans_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

/-- The Lindenbaum algebra of chain3TransTheory has exactly 2 elements. -/
theorem chain3Trans_algebra_card :
    Fintype.card (LindenbaumAlgebra chain3TransTheory) = 2 := by
  obtain ⟨e⟩ := chain3Trans_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

/-- All three deterministic transition-enriched theories have the same Lindenbaum
cardinality (= 2). This validates the deterministic collapse phenomenon:
transition enrichment carries no information for deterministic systems.

This uniformity is expected to break when nondeterministic systems are introduced
in Phase 105 (hub-spokes and two-cycle), where branching creates free generators
in the Lindenbaum algebra, yielding cardinality > 2. -/
theorem deterministic_transition_uniformity :
    Fintype.card (LindenbaumAlgebra singleLoopTransTheory) =
    Fintype.card (LindenbaumAlgebra toggleTransTheory) ∧
    Fintype.card (LindenbaumAlgebra toggleTransTheory) =
    Fintype.card (LindenbaumAlgebra chain3TransTheory) :=
  ⟨by rw [singleLoopTrans_algebra_card, toggleTrans_algebra_card],
   by rw [toggleTrans_algebra_card, chain3Trans_algebra_card]⟩

end RTS
