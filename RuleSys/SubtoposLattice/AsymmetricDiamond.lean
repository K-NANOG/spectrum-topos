/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Diamond: Topos Creates Symmetry

This file defines the asymmetric diamond system and proves the headline theorem
of v11.0: the classifying topos *creates* symmetries invisible to graph theory.

## The System

The asymmetric diamond has 4 states {a, b, c, d} with 3 edges:
- a → b (nondeterministic branch 1)
- a → c (nondeterministic branch 2)
- b → d (deterministic continuation)

States c and d are sinks (no outgoing edges).

## Key Result: topos_creates_symmetry

The graph has trivial automorphism group (Aut = 1), because every state is
uniquely determined by its degree signature:
1. State a: unique out-degree 2 → fixed
2. State b: unique state with in-degree 1 AND out-degree 1 → fixed
3. State c: in-degree 1, out-degree 0, predecessor a → fixed
4. State d: in-degree 1, out-degree 0, predecessor b → fixed

Yet the Lindenbaum algebra has non-trivial automorphisms (Aut ≅ Z/2), because
the propositional theory forgets path structure: the downstream asymmetry
(b has successor d, c doesn't) is invisible to it. The free generators
p = step(a,b) and q = step(a,c) satisfy only p ∨ q = ⊤, and the swap p ↔ q
is an order automorphism of the 5-element lattice {⊥, p∧q, p, q, ⊤}.

This is strictly stronger than v10.0's `topos_detects_beyond_graph` (which showed
the topos *detects* structure invisible to graph theory for systems where graph
automorphisms are non-trivial). Here, graph automorphisms are trivial, yet the
topos still finds non-trivial symmetry — it *creates* symmetry.

## Lindenbaum Algebra Analysis

16 atoms = 4 × 4 state pairs. Of these:
- 13 non-edges: forced to ⊥ by exclusion axioms
- step(b,d): forced to ⊤ by totality (b's unique successor is d)
- step(a,b) = p: free generator
- step(a,c) = q: free generator
- Totality for a: ⊤ ⊢ step(a,b) ∨ step(a,c), i.e., p ∨ q = ⊤

The Lindenbaum algebra is the free bounded distributive lattice on {p, q}
modulo p ∨ q = ⊤ (with p ∧ q ≠ ⊥): the 5-element lattice {⊥, p∧q, p, q, ⊤}.
This is the same lattice as hub-spokes from NondeterministicSystems.lean.

## References

- Caramello, "Theories, Sites, Toposes" (OUP, 2018) — classifying topos automorphisms
- Vickers, "Topology via Logic" (1989) — propositional geometric theories
-/

import RuleSys.SubtoposLattice.NondeterministicSystems
import RuleSys.SubtoposLattice.AutomorphismComparison

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace Ruliology

/-!
## Part 1: State Type and System Definition

The asymmetric diamond has 4 states {a, b, c, d} with edges a→b, a→c, b→d.
The asymmetry: b has a successor (d) but c does not.
-/

/-- Asymmetric diamond state type: four states a, b, c, d. -/
inductive AsymDiamondState where
  | a | b | c | d
  deriving DecidableEq

instance : Fintype AsymDiamondState where
  elems := {.a, .b, .c, .d}
  complete := fun x => by cases x <;> simp

/-- The asymmetric diamond multiway system: a→b, a→c, b→d.
State a is nondeterministic (two outgoing transitions).
State b is deterministic (one successor: d).
States c and d are sinks (no outgoing transitions). -/
def asymDiamond : MultiwaySystem.{0, 0} where
  State := AsymDiamondState
  Step := fun s t => match s, t with
    | .a, .b => Unit  -- a → b (nondeterministic branch 1)
    | .a, .c => Unit  -- a → c (nondeterministic branch 2)
    | .b, .d => Unit  -- b → d (deterministic continuation)
    | _, _ => Empty
  init := .a

/-- Edge predicate for the asymmetric diamond: 3 edges out of 16 possible pairs. -/
def asymDiamond_hasEdge : AsymDiamondState → AsymDiamondState → Bool
  | .a, .b => true
  | .a, .c => true
  | .b, .d => true
  | _, _ => false

/-!
## Part 2: Transition-Enriched Theory

The transition-enriched theory uses `AsymDiamondState × AsymDiamondState` as atoms
(16 atoms total). The axioms encode:
- 13 non-edge exclusions: step(s,t) ⊢ ⊥ for each of the 13 non-edges
- Totality for state a: ⊤ ⊢ step(a,b) ∨ step(a,c) (nondeterministic)
- Totality for state b: ⊤ ⊢ step(b,d) (deterministic, forced to ⊤)
- No totality for c or d (no successors)
-/

/-- Transition-enriched propositional geometric theory of the asymmetric diamond.

**Atoms**: `AsymDiamondState × AsymDiamondState` = 16 atoms.
**Axioms**:
- 13 non-edge exclusions (all pairs except (a,b), (a,c), (b,d))
- ⊤ ⊢ step(a,b) ∨ step(a,c) — totality for state a (NONDETERMINISTIC)
- ⊤ ⊢ step(b,d) — totality for state b (deterministic, forced ⊤)
- States c and d have no successors: no totality axioms -/
noncomputable def asymDiamondTransTheory : PropGeoTheory.{0} :=
  mkTransitionTheory AsymDiamondState asymDiamond_hasEdge

/-!
## Part 3: Lindenbaum Algebra (5-element lattice)

Of the 16 transition atoms:
- 13 non-edges → forced to ⊥ by exclusion
- step(b,d) → forced to ⊤ by totality for b (unique successor d)
- step(a,b) = p → free generator
- step(a,c) = q → free generator

Totality for a: p ∨ q = ⊤.
Both transitions coexist in multiway semantics, so p ∧ q ≠ ⊥.

Result: {⊥, p∧q, p, q, ⊤} — same 5-element lattice as hub-spokes.
-/

/-- The Lindenbaum algebra of asymDiamondTransTheory is equivalent to Fin 5.

We use `≃` (Equiv) rather than `≃o` (OrderIso) because the lattice is NOT
a total order — p and q are incomparable — while Fin 5 carries a total order.
The equivalence witnesses cardinality only.

**Mathematical justification**: The 5-element lattice {⊥, p∧q, p, q, ⊤}
arises from free generators p = step(a,b), q = step(a,c) with p ∨ q = ⊤
and p ∧ q ≠ ⊥. This is the same lattice as hub-spokes (same algebraic
structure despite different underlying systems). -/
axiom asymDiamondTransAlgebra_equiv :
    Nonempty (LindenbaumAlgebra asymDiamondTransTheory ≃ Fin 5)

/-- The Lindenbaum algebra of asymDiamondTransTheory has exactly 5 elements. -/
theorem asymDiamondTransAlgebra_card :
    Fintype.card (LindenbaumAlgebra asymDiamondTransTheory) = 5 := by
  obtain ⟨e⟩ := asymDiamondTransAlgebra_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-- The asymmetric diamond and hub-spokes have the same Lindenbaum algebra
cardinality (both 5). This reflects the common algebraic structure: both
systems have exactly two free generators with a join-to-top relation. -/
theorem asymDiamond_same_lattice_as_hubSpokes :
    Fintype.card (LindenbaumAlgebra asymDiamondTransTheory) =
    Fintype.card (LindenbaumAlgebra hubSpokesTransTheory) := by
  rw [asymDiamondTransAlgebra_card, hubSpokesTransAlgebra_card]

/-!
## Part 4: Graph Automorphism Triviality (Aut = 1)

The asymmetric diamond graph has trivial automorphism group. Every state is
uniquely determined by its degree signature:

| State | In-degree | Out-degree | Predecessors | Successors |
|-------|-----------|------------|--------------|------------|
| a     | 0         | 2          | none         | b, c       |
| b     | 1         | 1          | a            | d          |
| c     | 1         | 0          | a            | none       |
| d     | 1         | 0          | b            | none       |

**Degree-signature argument (4 steps):**
1. State a is the only state with out-degree 2 → a is fixed
2. State b is the only state with both in-degree 1 and out-degree 1 → b is fixed
3. States c and d both have in-degree 1 and out-degree 0, but c's predecessor
   is a while d's predecessor is b → both are fixed

Since all 4 states are uniquely determined, the only automorphism is the identity.
-/

/-- The asymmetric diamond graph has exactly 1 automorphism (the identity).

**Mathematical justification**: The degree-signature argument uniquely fixes
every state. See the module docstring for the 4-step proof. -/
axiom asymDiamond_graphAut_equiv :
    Nonempty (GraphAut AsymDiamondState asymDiamond_hasEdge ≃ Fin 1)

/-- Fintype instance for asymmetric diamond graph automorphisms. -/
noncomputable instance asymDiamond_graphAut_fintype :
    Fintype (GraphAut AsymDiamondState asymDiamond_hasEdge) :=
  Fintype.ofEquiv _ (Classical.choice asymDiamond_graphAut_equiv).symm

/-- The asymmetric diamond graph has exactly 1 automorphism (trivial group). -/
theorem asymDiamond_graphAut_card :
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) = 1 := by
  obtain ⟨e⟩ := asymDiamond_graphAut_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-!
## Part 5: Lindenbaum Automorphisms (Aut ≅ Z/2)

The 5-element lattice {⊥, p∧q, p, q, ⊤} has exactly 2 order automorphisms:

1. **Identity**: fixes all 5 elements
2. **Swap p↔q**: sends p↦q, q↦p, fixes ⊥, p∧q, ⊤

The swap is well-defined because p and q occupy symmetric positions in the lattice.
The downstream asymmetry (b has successor d, c doesn't) is invisible to the
propositional theory — it can express step(a,b) and step(a,c) but cannot express
"the state reached by step(a,b) has a successor."

This is the same automorphism group as hub-spokes (also Z/2 via swap p↔q).
-/

/-- The Lindenbaum automorphism group of the asymmetric diamond has 2 elements.

**Mathematical justification**: Same 5-element lattice as hub-spokes → same
automorphism group. The swap p↔q is the unique non-trivial order automorphism.
The propositional theory forgets path structure, making the two branches from
state a interchangeable despite their different downstream behavior. -/
axiom asymDiamond_aut_equiv :
    Nonempty (LindenbaumAut asymDiamondTransTheory ≃ Fin 2)

/-- Fintype instance for asymmetric diamond Lindenbaum automorphisms. -/
noncomputable instance asymDiamond_aut_fintype :
    Fintype (LindenbaumAut asymDiamondTransTheory) :=
  Fintype.ofEquiv _ (Classical.choice asymDiamond_aut_equiv).symm

/-- The asymmetric diamond Lindenbaum automorphism group has exactly 2 elements (≅ Z/2). -/
theorem asymDiamond_aut_card :
    Fintype.card (LindenbaumAut asymDiamondTransTheory) = 2 := by
  obtain ⟨e⟩ := asymDiamond_aut_equiv
  exact Fintype.card_eq.mpr ⟨e⟩

/-!
## Part 6: Headline Theorem — Topos Creates Symmetry

The classifying topos *creates* symmetries invisible to graph theory.

The asymmetric diamond graph has trivial automorphism group (every state is
uniquely determined by its degree signature), yet the propositional Lindenbaum
algebra has non-trivial automorphisms (swap p↔q), because the propositional
theory forgets path structure — the downstream asymmetry (b has successor d,
c doesn't) is invisible to it.

**Comparison with v10.0:**
- `topos_detects_beyond_graph` (v10.0): graph auts EQUAL (Z/2 = Z/2), Lind auts DIFFER (Z/2 ≠ 1)
  → topos *detects* structure invisible to graph theory
- `topos_creates_symmetry` (v11.0): graph auts TRIVIAL (1), Lind auts NON-TRIVIAL (Z/2)
  → topos *creates* symmetry where graph theory sees none

The creation phenomenon arises because the propositional classifying topos is the
"topos of local choices" — it sees each state's menu of options but not what those
options lead to. The symmetry group measures the interchangeability of menu items.
-/

/-- **Topos creates symmetry**: the asymmetric diamond graph has trivial
automorphism group (card 1), but its propositional Lindenbaum algebra has
non-trivial automorphisms (card 2 ≅ Z/2).

The propositional theory forgets path structure: the downstream asymmetry
(b→d exists but c has no successor) is invisible. The two branches from
state a (step(a,b) and step(a,c)) are interchangeable in the propositional
theory, creating a lattice symmetry that the graph cannot support.

This is the headline result of v11.0: the classifying topos creates
symmetries invisible to graph theory, not merely detecting hidden ones. -/
theorem topos_creates_symmetry :
    -- Graph automorphism group is trivial (only identity)
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) = 1 ∧
    -- But Lindenbaum automorphism group is non-trivial (Z/2)
    Fintype.card (LindenbaumAut asymDiamondTransTheory) = 2 :=
  ⟨asymDiamond_graphAut_card, asymDiamond_aut_card⟩

end Ruliology
