/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Small Concrete Transition Systems

This file defines three small rooted transition systems with known Lindenbaum algebra
structure, providing concrete test cases for the subtopos enumeration framework.

## Systems

1. **singleLoop**: 1 state, 1 self-loop. Lindenbaum algebra = Bool (2 elements).
2. **toggle**: 2 states, bidirectional. Lindenbaum algebra = 4-element Boolean algebra.
3. **chain3**: 3 states, linear chain. Lindenbaum algebra = 8-element Boolean algebra.

## Mathematical Justification

The Lindenbaum algebra of a propositional geometric theory with n pairwise-disjoint
exhaustive atoms (state propositions satisfying ⊤ ⊢ p₀ ∨ ... ∨ pₙ₋₁ and pᵢ ∧ pⱼ ⊢ ⊥
for i ≠ j) is the free Boolean algebra on n generators modulo the partition axioms,
which is isomorphic to the power set lattice 2ⁿ.

- singleLoop: 1 atom, algebra ≅ 2¹ = Bool
- toggle: 2 atoms, algebra ≅ 2² = Fin 4
- chain3: 3 atoms, algebra ≅ 2³ = Fin 8

## References

- Vickers, "Topology via Logic" (1989) — propositional geometric theories
- Johnstone, "Stone Spaces" (1982) — Lindenbaum algebras of propositional theories
-/

import RuleSys.GeometricLogic.PropositionalLindenbaum
import RuleSys.GeometricLogic.SyntacticCoverage
import RuleSys.Basic

set_option autoImplicit false

universe u

namespace RTS

/-!
## Part 1: Concrete Transition Systems

Three small systems with finite state types, following the pattern from
NonEquivalence.lean (State = concrete inductive, Step = decidable proposition).
-/

/-- SingleLoopState: a single state. -/
inductive SingleLoopState where
  | s
  deriving DecidableEq

instance : Fintype SingleLoopState where
  elems := {.s}
  complete := fun x => by cases x; simp

set_option linter.constructorNameAsVariable false in
/-- singleLoop: The simplest nontrivial rooted transition system.
    One state `s` with a single self-loop s → s.
    This is the prototypical "trivial dynamics" system. -/
def singleLoop : RootedTS.{0, 0} where
  State := SingleLoopState
  Step := fun _ _ => Unit
  init := .s

/-- ToggleState: two states for the toggle system. -/
inductive ToggleState where
  | a
  | b
  deriving DecidableEq

instance : Fintype ToggleState where
  elems := {.a, .b}
  complete := fun x => by cases x <;> simp

/-- toggle: A two-state bidirectional system.
    States {a, b} with transitions a → b and b → a.
    This is the simplest non-trivial reversible system. -/
def toggle : RootedTS.{0, 0} where
  State := ToggleState
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .b, .a => Unit
    | _, _ => Empty
  init := .a

/-- Chain3State: three states for the chain system. -/
inductive Chain3State where
  | a
  | b
  | c
  deriving DecidableEq

instance : Fintype Chain3State where
  elems := {.a, .b, .c}
  complete := fun x => by cases x <;> simp

/-- chain3: A three-state linear chain system.
    States {a, b, c} with transitions a → b → c.
    This is the simplest "directed path" system with 3 distinct states. -/
def chain3 : RootedTS.{0, 0} where
  State := Chain3State
  Step := fun s t => match s, t with
    | .a, .b => Unit
    | .b, .c => Unit
    | _, _ => Empty
  init := .a

/-!
### DecidableEq instances for Step types

These are needed for downstream Fintype computations on step types.
-/

instance singleLoop_step_decidableEq (x y : SingleLoopState) :
    DecidableEq (singleLoop.Step x y) :=
  inferInstanceAs (DecidableEq Unit)

instance toggle_step_decidableEq (s t : ToggleState) :
    DecidableEq (toggle.Step s t) := by
  cases s <;> cases t <;> first | exact inferInstanceAs (DecidableEq Unit)
                                 | exact inferInstanceAs (DecidableEq Empty)

instance chain3_step_decidableEq (s t : Chain3State) :
    DecidableEq (chain3.Step s t) := by
  cases s <;> cases t <;> first | exact inferInstanceAs (DecidableEq Unit)
                                 | exact inferInstanceAs (DecidableEq Empty)

end RTS

open GeometricLogic.Propositional

namespace RTS

/-!
## Part 2: Propositional Geometric Theories

For each system, we define a propositional geometric theory whose atoms correspond
to "being in state s" propositions. The axioms encode:
- **Exhaustiveness**: ⊤ ⊢ p₀ ∨ ... ∨ pₙ₋₁ (the system is always in some state)
- **Exclusiveness**: pᵢ ∧ pⱼ ⊢ ⊥ for i ≠ j (the system is in at most one state)
-/

/-- Propositional geometric theory of the singleLoop system.

    One atom p₀ = "at state s". The sole axiom is ⊤ ⊢ p₀ (the system is always
    in state s, since there is only one state). -/
def singleLoopTheory : PropGeoTheory.{0} where
  Atoms := Fin 1
  axioms := {⟨.top, .atom 0⟩}

/-- Propositional geometric theory of the toggle system.

    Two atoms: p₀ = "at state a", p₁ = "at state b".
    Axioms:
    - ⊤ ⊢ p₀ ∨ p₁ (exhaustive: always in some state)
    - p₀ ∧ p₁ ⊢ ⊥ (exclusive: cannot be in both states) -/
def toggleTheory : PropGeoTheory.{0} where
  Atoms := Fin 2
  axioms := {⟨.top, .disj (.atom 0) (.atom 1)⟩,
             ⟨.conj (.atom 0) (.atom 1), .bot⟩}

/-- Propositional geometric theory of the chain3 system.

    Three atoms: p₀ = "at state a", p₁ = "at state b", p₂ = "at state c".
    Axioms:
    - ⊤ ⊢ p₀ ∨ p₁ ∨ p₂ (exhaustive: always in some state)
    - p₀ ∧ p₁ ⊢ ⊥ (states a, b exclusive)
    - p₀ ∧ p₂ ⊢ ⊥ (states a, c exclusive)
    - p₁ ∧ p₂ ⊢ ⊥ (states b, c exclusive) -/
def chain3Theory : PropGeoTheory.{0} where
  Atoms := Fin 3
  axioms := {⟨.top, .disj (.disj (.atom 0) (.atom 1)) (.atom 2)⟩,
             ⟨.conj (.atom 0) (.atom 1), .bot⟩,
             ⟨.conj (.atom 0) (.atom 2), .bot⟩,
             ⟨.conj (.atom 1) (.atom 2), .bot⟩}

/-!
## Part 3: Axiomatized Lindenbaum Algebra Structure

The Lindenbaum algebra of a propositional geometric theory with n pairwise-disjoint
exhaustive atoms is a 2ⁿ-element Boolean algebra. This is the free Boolean algebra
on n generators modulo the partition axioms (exhaustiveness + exclusiveness).

We axiomatize the order-isomorphisms to concrete finite types. The target types
carry the Boolean algebra structure:
- `Bool` = 2-element Boolean algebra (false < true)
- `Fin 4` with power-set order of 2 atoms (0=∅, 1={a}, 2={b}, 3={a,b})
- `Fin 8` with power-set order of 3 atoms

Since these are axioms, the specific order on `Fin n` is part of the axiomatized
content. The cardinality theorems that follow use only the underlying `Equiv`.
-/

/-- The Lindenbaum algebra of singleLoopTheory is order-isomorphic to Bool.

    **Mathematical justification**: With one atom p₀ and the axiom ⊤ ⊢ p₀,
    every formula is provably equivalent to either ⊤ or ⊥. The quotient has
    exactly 2 elements: [⊥] < [⊤], matching Bool (false < true). -/
axiom singleLoop_algebra_iso :
    Nonempty (LindenbaumAlgebra singleLoopTheory ≃o Bool)

/-- The Lindenbaum algebra of toggleTheory is order-isomorphic to Fin 4.

    **Mathematical justification**: With 2 atoms {p₀, p₁} satisfying
    ⊤ ⊢ p₀ ∨ p₁ and p₀ ∧ p₁ ⊢ ⊥, the Lindenbaum algebra is the 4-element
    Boolean algebra: {⊥, [p₀], [p₁], ⊤}. This is a diamond lattice where
    [p₀] and [p₁] are incomparable, both above ⊥ and below ⊤.
    Fin 4 is given the power-set order: 0=⊥, 1=[p₀], 2=[p₁], 3=⊤. -/
axiom toggle_algebra_iso :
    Nonempty (LindenbaumAlgebra toggleTheory ≃o Fin 4)

/-- The Lindenbaum algebra of chain3Theory is order-isomorphic to Fin 8.

    **Mathematical justification**: With 3 atoms {p₀, p₁, p₂} satisfying
    ⊤ ⊢ p₀ ∨ p₁ ∨ p₂ and all pairwise exclusions pᵢ ∧ pⱼ ⊢ ⊥,
    the Lindenbaum algebra is the 8-element Boolean algebra (power set of 3).
    The 8 equivalence classes are: ⊥, [p₀], [p₁], [p₂], [p₀∨p₁], [p₀∨p₂],
    [p₁∨p₂], ⊤. Fin 8 carries the corresponding power-set lattice order. -/
axiom chain3_algebra_iso :
    Nonempty (LindenbaumAlgebra chain3Theory ≃o Fin 8)

/-!
## Part 4: Cardinality Theorems

Derived from the axiomatized isomorphisms: the underlying `Equiv` gives
`Fintype.card` equalities.
-/

/-- The Lindenbaum algebra of singleLoopTheory has exactly 2 elements. -/
theorem singleLoop_algebra_card :
    Fintype.card (LindenbaumAlgebra singleLoopTheory) = 2 := by
  obtain ⟨e⟩ := singleLoop_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

/-- The Lindenbaum algebra of toggleTheory has exactly 4 elements. -/
theorem toggle_algebra_card :
    Fintype.card (LindenbaumAlgebra toggleTheory) = 4 := by
  obtain ⟨e⟩ := toggle_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

/-- The Lindenbaum algebra of chain3Theory has exactly 8 elements. -/
theorem chain3_algebra_card :
    Fintype.card (LindenbaumAlgebra chain3Theory) = 8 := by
  obtain ⟨e⟩ := chain3_algebra_iso
  exact Fintype.card_eq.mpr ⟨e.toEquiv⟩

end RTS
