/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Non-Monotonicity of Automorphism Count

This file proves the non-monotonicity theorem: for the asymmetric diamond system,
the number of automorphisms is non-monotone in the "strength" of the description.

## The Three-Level Symmetry Hierarchy

The asymmetric diamond system {a, b, c, d} with edges a→b, a→c, b→d exhibits
a striking three-level symmetry hierarchy:

1. **Graph level** (Aut = 1): The graph sees full global structure including
   path continuations. Every state is uniquely determined by its degree
   signature, so the only automorphism is the identity.

2. **Propositional topos level** (Aut = Z/2 = 2): The propositional theory
   sees branching at each state but not what happens after branching.
   The two branches from state a (step(a,b) and step(a,c)) are
   interchangeable, giving the swap p↔q as a non-trivial automorphism.

3. **First-order topos level** (Aut = 1, conjectured): The full geometric
   theory with sorted variables over states can express "the state reached
   by step(a,b) has a successor" vs "the state reached by step(a,c) doesn't",
   breaking the p↔q symmetry. (Not formalized in v11.0.)

## Non-Monotonicity: 1 < 2 > 1

The automorphism count follows the pattern 1 → 2 → 1 as the description
becomes richer: graph → propositional → first-order. This is non-monotone.

The propositional theory sits at a **Goldilocks resolution**: rich enough to
see branching structure (which the graph automorphism group, being purely
combinatorial, doesn't encode as a symmetry), but not rich enough to see
continuation structure (which would break the branching symmetry).

## What Is Formalized

- `asymDiamond_nonmonotonicity`: |Aut(graph)| < |Aut(Lind_prop)| (1 < 2)
- `hubSpokes_monotone`: |Aut(graph)| = |Aut(Lind_prop)| (2 = 2) — no non-monotonicity
- `goldilocks_resolution`: combined headline (non-monotonicity + Galois + triviality)

## What Is Conjectured (v12.0)

The first-order direction |Aut(Lind_prop)| > |Aut(Lind_FO)| (2 > 1) requires
formalizing the first-order Lindenbaum algebra, which is deferred to v12.0.

## References

- Caramello, "Theories, Sites, Toposes" (OUP, 2018) — classifying topos automorphisms
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990) — resolution levels
-/

import RuleSys.SubtoposLattice.ToposPoints

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace RTS

/-!
## Part 1: The Non-Monotonicity Theorem

For the asymmetric diamond, the graph automorphism group is strictly smaller
than the Lindenbaum automorphism group: |Aut(graph)| = 1 < 2 = |Aut(Lind)|.

This is a direct arithmetic consequence of the cardinalities computed in
Phase 109 (AsymmetricDiamond.lean).
-/

/-- **Non-monotonicity of automorphism count**: the asymmetric diamond graph has
strictly fewer automorphisms than its propositional Lindenbaum algebra.

The graph sees full global structure (degree signatures uniquely fix all states),
while the propositional theory forgets path continuations (making the two branches
from state a interchangeable). The propositional description creates symmetries
that the more detailed graph description breaks.

This is the 1 < 2 half of the full 1 < 2 > 1 non-monotonicity chain. -/
theorem asymDiamond_nonmonotonicity :
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) <
    Fintype.card (LindenbaumAut asymDiamondTransTheory) := by
  rw [asymDiamond_graphAut_card, asymDiamond_aut_card]
  omega

/-!
## Part 2: Comparative Non-Monotonicity

The non-monotonicity phenomenon is specific to systems where the graph
asymmetry is "downstream" (invisible to the propositional theory).

For hub-spokes, graph and Lindenbaum automorphism counts are equal (both 2):
the graph symmetry (swap b↔c) and the lattice symmetry (swap p↔q) are
"aligned" — both reflect the interchangeability of the two branches from a.

For the asymmetric diamond, the graph has no symmetry (because b→d breaks
the b/c symmetry at the graph level), but the lattice symmetry persists
(because the propositional theory cannot see that b has a successor and c doesn't).
-/

/-- Hub-spokes has equal graph and Lindenbaum automorphism counts (both Z/2).

The graph symmetry (swap b↔c) and lattice symmetry (swap p↔q) are aligned:
both reflect the interchangeability of the two branches from state a.
No non-monotonicity occurs because the graph asymmetry between b and c is
absent (both are sinks with the same degree signature). -/
theorem hubSpokes_monotone :
    Fintype.card (GraphAut HubSpokesState hubSpokes_hasEdge) =
    Fintype.card (LindenbaumAut hubSpokesTransTheory) := by
  rw [hubSpokes_graphAut_card, hubSpokes_aut_card]

/-- Two-cycle also has equal counts (both trivial: graph Aut=2, Lind Aut=1).

Actually, for two-cycle the graph has MORE automorphisms than the Lindenbaum
algebra — the opposite direction. This is because the graph swap a↔b preserves
edges, but the Bool lattice {⊥, ⊤} has only the identity order automorphism. -/
theorem twoCycle_reverse_monotone :
    Fintype.card (GraphAut ToggleState toggle_hasEdge) >
    Fintype.card (LindenbaumAut twoCycleTransTheory) := by
  rw [twoCycle_graphAut_card, twoCycle_aut_card]
  omega

/-- The three systems exhibit three different monotonicity behaviors:
- Hub-spokes: graph Aut = Lind Aut (2 = 2, aligned)
- Two-cycle: graph Aut > Lind Aut (2 > 1, determinism kills lattice symmetry)
- Asymmetric diamond: graph Aut < Lind Aut (1 < 2, propositional theory creates symmetry)

This trichotomy shows that the relationship between graph and topos symmetries
is genuinely non-monotone — neither direction is universally true. -/
theorem symmetry_trichotomy :
    -- Hub-spokes: equal (aligned symmetries)
    Fintype.card (GraphAut HubSpokesState hubSpokes_hasEdge) =
    Fintype.card (LindenbaumAut hubSpokesTransTheory) ∧
    -- Two-cycle: graph > lattice (determinism kills lattice symmetry)
    Fintype.card (GraphAut ToggleState toggle_hasEdge) >
    Fintype.card (LindenbaumAut twoCycleTransTheory) ∧
    -- Asymmetric diamond: graph < lattice (propositional theory creates symmetry)
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) <
    Fintype.card (LindenbaumAut asymDiamondTransTheory) :=
  ⟨hubSpokes_monotone, twoCycle_reverse_monotone, asymDiamond_nonmonotonicity⟩

/-!
## Part 3: Goldilocks Theorem

The asymmetric diamond sits at a unique position: it has the most symmetry
at the intermediate (propositional) level, while having no symmetry at the
more detailed (graph) level and more models than orbits at the topos level.
-/

/-- **Goldilocks resolution**: the asymmetric diamond propositional theory
sits at a resolution that maximizes symmetry.

Three simultaneous properties:
1. The propositional theory has MORE automorphisms than the graph (1 < 2)
2. The Galois action is non-trivial (2 orbits < 3 points)
3. The graph itself has NO symmetries at all (card 1)

The propositional classifying topos is the "topos of local choices": it sees
each state's menu of options but not what those options lead to. The symmetry
group measures the interchangeability of menu items. This is the Goldilocks
resolution — rich enough to see branching (unlike graph theory) but not rich
enough to see continuation structure (which would break the symmetry). -/
theorem goldilocks_resolution :
    -- More propositional symmetries than graph symmetries
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) <
    Fintype.card (LindenbaumAut asymDiamondTransTheory) ∧
    -- Non-trivial Galois action on topos points
    orbitCount asymDiamondTransTheory < pointCount asymDiamondTransTheory ∧
    -- Graph has NO symmetries at all
    Fintype.card (GraphAut AsymDiamondState asymDiamond_hasEdge) = 1 := by
  refine ⟨asymDiamond_nonmonotonicity, ?_, asymDiamond_graphAut_card⟩
  show Fintype.card (Quotient (toposOrbitSetoid asymDiamondTransTheory)) <
       Fintype.card (ToposPoint asymDiamondTransTheory)
  rw [asymDiamond_orbits_card, asymDiamond_points_card]
  omega

/-!
## Part 4: First-Order Conjecture (Documented Remark)

The full non-monotonicity chain is conjectured to be:

  |Aut(graph)| = 1 < |Aut(Lind_prop)| = 2 > |Aut(Lind_FO)| = 1

The first-order direction (2 > 1) would follow from:

1. The first-order geometric theory T_M of the asymmetric diamond has
   sorted variables ranging over states and can express:
   - ∃y. step(x,y) ∧ ∃z. step(y,z) — "state x reaches a state with a successor"
   - ∃y. step(x,y) ∧ ¬∃z. step(y,z) — "state x reaches a sink"

2. In the first-order Lindenbaum algebra, step(a,b) and step(a,c) are
   distinguished by their downstream behavior:
   - step(a,b) leads to state b which has successor d
   - step(a,c) leads to state c which is a sink

3. Therefore the swap p↔q is NOT an automorphism of the first-order
   Lindenbaum algebra: it would need to preserve the truth value of
   "the target state has a successor", which differs for b and c.

4. The only automorphism is the identity, giving |Aut(Lind_FO)| = 1.

**Status**: This direction is OUT of scope for v11.0. Formalizing the
first-order Lindenbaum algebra requires:
- A first-order version of PropGeoTheory with sorted variables
- Quantifier elimination or direct lattice computation
- This is deferred to v12.0

The 1 < 2 direction (formalized above as `asymDiamond_nonmonotonicity`)
already captures the key insight: the propositional theory creates symmetries
invisible to graph theory.
-/

end RTS
