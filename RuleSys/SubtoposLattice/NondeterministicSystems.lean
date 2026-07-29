/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nondeterministic Transition Systems

This file defines the first nondeterministic system (hub-spokes) and establishes
that nondeterminism breaks the deterministic uniformity from TransitionSystems.lean.

## Contrast with Deterministic Systems

In `TransitionSystems.lean`, all three deterministic systems (singleLoop, toggle, chain3)
have transition-enriched Lindenbaum algebras of cardinality 2 (= Bool). This is the
"deterministic collapse": each state has at most one successor, so every transition
atom is forced (to ⊤ by totality or to ⊥ by exclusion), leaving no free generators.

The hub-spokes system breaks this pattern: state `a` has TWO successors (b and c),
creating a nondeterministic branch. The totality axiom ⊤ ⊢ step(a,b) ∨ step(a,c)
leaves both atoms undetermined, producing a 5-element Lindenbaum algebra — the first
non-power-of-2 cardinality in the project.

## Systems

1. **Hub-spokes**: States {a, b, c}, edges a→b, a→c, b→a, c→a.
   State a is nondeterministic (two outgoing transitions).
   Lindenbaum algebra = 5-element lattice {⊥, p∧q, p, q, ⊤}.

2. **Two-cycle**: States {a, b}, edges a→b, b→a.
   Both states deterministic. Identical to toggle.
   Lindenbaum algebra = Bool (cardinality 2).

## References

- Vickers, "Topology via Logic" (1989) — propositional geometric theories
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990)
-/

import RuleSys.SubtoposLattice.TransitionSystems
import RuleSys.SubtoposLattice.SmallSystems
import RuleSys.SubtoposLattice.TopologyEnumeration
import RuleSys.SubtoposLattice.HubSpokesComputable
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace RTS

/-!
## Part 1: Hub-Spokes System

The hub-spokes system has 3 states {a, b, c} with 4 edges:
- a → b (nondeterministic branch 1)
- a → c (nondeterministic branch 2)
- b → a (deterministic return)
- c → a (deterministic return)

State a is the "hub" with nondeterministic branching; states b, c are "spokes"
with deterministic returns to the hub.
-/

/-- Hub-spokes state type: three states a, b, c. -/
inductive HubSpokesState where
  | a | b | c
  deriving DecidableEq

instance : Fintype HubSpokesState where
  elems := {.a, .b, .c}
  complete := fun x => by cases x <;> simp

/-- Hub-spokes rooted transition system: a→b, a→c, b→a, c→a.
State a is nondeterministic (two outgoing transitions). -/
def hubSpokesND : RootedTS.{0, 0} where
  State := HubSpokesState
  Step := fun s t => match s, t with
    | .a, .b => Unit  -- a → b
    | .a, .c => Unit  -- a → c (nondeterministic!)
    | .b, .a => Unit  -- b → a
    | .c, .a => Unit  -- c → a
    | _, _ => Empty
  init := .a

/-- Edge predicate for hub-spokes: 4 edges out of 9 possible pairs. -/
def hubSpokes_hasEdge : HubSpokesState → HubSpokesState → Bool
  | .a, .b => true
  | .a, .c => true
  | .b, .a => true
  | .c, .a => true
  | _, _ => false

/-- Transition-enriched propositional geometric theory of the hub-spokes system.

**Atoms**: `HubSpokesState × HubSpokesState` = 9 atoms.
**Axioms**:
- 5 non-edge exclusions: step(a,a), step(b,b), step(b,c), step(c,b), step(c,c) ⊢ ⊥
- ⊤ ⊢ step(a,b) ∨ step(a,c) — totality for state a (NONDETERMINISTIC)
- ⊤ ⊢ step(b,a) — totality for state b (deterministic, forced ⊤)
- ⊤ ⊢ step(c,a) — totality for state c (deterministic, forced ⊤) -/
noncomputable def hubSpokesTransTheory : PropGeoTheory.{0} :=
  mkTransitionTheory HubSpokesState hubSpokes_hasEdge

/-!
## Part 2: Two-Cycle System

The two-cycle system has states {a, b} with edges a→b, b→a — identical
to the toggle system from SmallSystems.lean. Both states are deterministic
(unique successors), so the transition-enriched Lindenbaum algebra is Bool.
-/

/-- The two-cycle rooted transition system is the toggle system under a different name.
Both have states {a, b} with bidirectional transitions a ↔ b. -/
def twoCycleND : RootedTS.{0, 0} := toggle

/-- The two-cycle transition-enriched theory is identical to toggleTransTheory.
Both have states {a, b} with bidirectional transitions a ↔ b.
The transition-enriched theory is identical because they share the same
state type (ToggleState) and edge predicate (toggle_hasEdge). -/
noncomputable def twoCycleTransTheory : PropGeoTheory.{0} := toggleTransTheory

/-!
## Part 3: Axiomatized Lindenbaum Algebra Structure

### Hub-spokes: 5-element Lindenbaum algebra

Of the 9 transition atoms (HubSpokesState × HubSpokesState):
- **5 non-edges forced ⊥**: step(a,a), step(b,b), step(b,c), step(c,b), step(c,c)
- **step(b,a) forced ⊤**: by totality for state b (unique successor a)
- **step(c,a) forced ⊤**: by totality for state c (unique successor a)
- **Remaining free generators**: p = step(a,b), q = step(a,c)

The totality axiom for state a gives: p ∨ q = ⊤.
Since both transitions coexist in the multiway semantics, p ∧ q is satisfiable
(both a→b and a→c fire simultaneously), so p ∧ q ≠ ⊥.

The free bounded distributive lattice on {p, q} modulo (p ∨ q = ⊤) has 5 elements:
  {⊥, p∧q, p, q, ⊤}
with ordering: ⊥ < p∧q < p < ⊤, ⊥ < p∧q < q < ⊤, p ∥ q (incomparable).

This is the first non-power-of-2 Lindenbaum cardinality in the project.

### Two-cycle: Bool (cardinality 2)

Since twoCycleTransTheory = toggleTransTheory definitionally, the Lindenbaum
algebra is identical: Bool with cardinality 2 (from TransitionSystems.lean).
-/

/-- The Lindenbaum algebra of hubSpokesTransTheory is order-isomorphic to HubSpokesElem.

**Mathematical justification**: The 5-element lattice {⊥, p∧q, p, q, ⊤}
arises from the free bounded distributive lattice on 2 generators {p, q}
modulo the single relation p ∨ q = ⊤ (with p ∧ q ≠ ⊥). This is exactly
the HubSpokesElem type defined in HubSpokesComputable.lean.

This is a stronger axiom than the previous `hubSpokesTransAlgebra_equiv`
(OrderIso vs bare Equiv), but it enables deriving all nucleus properties
from the computable HubSpokesElem representation. -/
axiom hubSpokesTransAlgebra_orderIso :
    LindenbaumAlgebra hubSpokesTransTheory ≃o HubSpokesElem

/-- The Lindenbaum algebra of hubSpokesTransTheory has exactly 5 elements.

This is the first non-power-of-2 cardinality in the project, breaking the
deterministic uniformity where all transition-enriched algebras have card 2. -/
theorem hubSpokesTransAlgebra_card :
    Fintype.card (LindenbaumAlgebra hubSpokesTransTheory) = 5 := by
  exact Fintype.card_eq.mpr ⟨hubSpokesTransAlgebra_orderIso.toEquiv⟩

/-- The Lindenbaum algebra of twoCycleTransTheory has exactly 2 elements.

Since twoCycleTransTheory = toggleTransTheory, this follows directly
from toggleTrans_algebra_card. -/
theorem twoCycleTransAlgebra_card :
    Fintype.card (LindenbaumAlgebra twoCycleTransTheory) = 2 :=
  toggleTrans_algebra_card

/-- Nondeterminism breaks the deterministic uniformity: the hub-spokes system
(with nondeterministic state a) has a strictly different Lindenbaum cardinality
than the two-cycle system (fully deterministic).

This is the first result in the project where two systems have genuinely
different transition-enriched Lindenbaum algebras (5 vs 2). All three
deterministic systems from TransitionSystems.lean had identical cardinality 2. -/
theorem nondeterministic_breaks_uniformity :
    Fintype.card (LindenbaumAlgebra hubSpokesTransTheory) ≠
    Fintype.card (LindenbaumAlgebra twoCycleTransTheory) := by
  rw [hubSpokesTransAlgebra_card, twoCycleTransAlgebra_card]
  omega

/-!
## Part 4: Grothendieck Topology Enumeration on Hub-Spokes Lattice

The hub-spokes Lindenbaum algebra is a 5-element lattice {⊥, m=p∧q, p, q, ⊤}
where p ∥ q (incomparable). This lattice admits exactly 8 Grothendieck topologies,
enumerated by classifying all nuclei (closure operators preserving ∧).

A nucleus j on the lattice is determined by its fixpoint set S (which must be
closed under ∧ and contain ⊤). The valid fixpoint sets are:

| #  | Fixpoint set   | Description     |
|----|---------------|-----------------|
| 1  | {⊥,m,p,q,⊤}  | trivial         |
| 2  | {m,p,q,⊤}    | ⊥-collapsed     |
| 3  | {⊥,p,⊤}      | q-collapsed     |
| 4  | {⊥,q,⊤}      | p-collapsed     |
| 5  | {⊥,⊤}        | gap             |
| 6  | {p,⊤}        | p-channel       |
| 7  | {q,⊤}        | q-channel       |
| 8  | {⊤}          | discrete        |

Compare: Bool (2-element) has 4 topologies. The doubling from 4 to 8
demonstrates that nondeterminism enriches the subtopos lattice.

### Invalid candidates (meet-preservation fails):
- {m,⊤}: j(p∧q)=j(m)=m but j(p)∧j(q)=⊤∧⊤=⊤ ≠ m
- {m,p,⊤}: j(p∧q)=j(m)=m but j(p)∧j(q)=p∧⊤=p ≠ m
- {m,q,⊤}: symmetric
- {⊥,m,⊤}: j(p∧q)=j(m)=m but j(p)∧j(q)=⊤∧⊤=⊤ ≠ m
- {⊥,m,p,⊤}: j(p∧q)=j(m)=m but j(p)∧j(q)=p∧⊤=p ≠ m
- {⊥,m,q,⊤}: symmetric
- {p,q,⊤}: not ∧-closed (p∧q=m ∉ set)
- {⊥,p,q,⊤}: not ∧-closed
-/

/-- The trivial Grothendieck topology on the hub-spokes Lindenbaum algebra.
Only the maximal sieve covers at each object. Fixpoint set: {⊥,m,p,q,⊤} (all). -/
noncomputable def hubSpokes_trivial :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) := ⊥

/-- The discrete Grothendieck topology on the hub-spokes Lindenbaum algebra.
Every sieve covers at every object. Fixpoint set: {⊤}. -/
noncomputable def hubSpokes_discrete :
    GrothendieckTopology (LindenbaumAlgebra hubSpokesTransTheory) := ⊤

/-!
### Intermediate GT Topologies

The 6 intermediate GT topologies (botCollapsed, qCollapsed, pCollapsed, gap,
pChannel, qChannel) are now CONSTRUCTED in NucleusGTBijection.lean via
`nucleusToGrothendieck` applied to the corresponding nuclei from
NucleusInfrastructure.lean. This eliminates 6 axioms.

All ordering, distinctness, incomparability, completeness and count theorems
are also in NucleusGTBijection.lean, derived from nucleus properties.
-/

/-!
## Part 5: Contrast with Deterministic Topology Counts

The two-cycle system has the same transition-enriched Lindenbaum algebra as toggle
(both = Bool), so its GT topology count is 4 (from TopologyEnumeration.lean,
via singleLoop_topology_count — both have Bool algebras with 4 topologies).

Hub-spokes has 8 topologies vs 4 for any deterministic system with Bool algebra.
This demonstrates that nondeterminism enriches the subtopos lattice, providing
more refined levels of process observation.
-/

end RTS
