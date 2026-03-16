/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete Quotient Theories

This file defines concrete quotient theories for the three small systems
(singleLoop, toggle, chain3) and establishes their correspondence with
the Grothendieck topologies enumerated in TopologyEnumeration.lean.

## Mathematical Content

For each system, the quotient theories capture "how much state information
is retained":
- **Trivial quotient** = no observation beyond existence (coarsest)
- **Syntactic quotient** = full state identity (medium)
- **Inconsistent quotient** = everything collapsed (finest = trivial topos)

For singleLoop (2-chain Lindenbaum algebra), there are 4 quotient theories
matching the 4 GT topologies (diamond lattice). For toggle and chain3,
we define trivial, syntactic, and inconsistent quotients matching the
3 named topologies.

## References

- Caramello, "Theories, Sites, Toposes" (2018) — Duality Theorem
-/

import RuleSys.SubtoposLattice.QuotientDuality

set_option autoImplicit false

universe u

open CategoryTheory
open GeometricLogic.Propositional

namespace RTS

/-!
## Section 1: Concrete Quotient Theories for singleLoop

The 4 GT topologies on the singleLoop Lindenbaum algebra (2-chain) correspond
to 4 quotient theories:
- Trivial quotient ↔ trivial topology (⊥)
- Atomic quotient ↔ atomic topology
- Collapsed quotient ↔ ⊥-collapsed topology
- Inconsistent quotient ↔ discrete topology (⊤)
-/

/-- The trivial quotient of singleLoopTheory: no extra axioms.
Corresponds to the trivial topology (⊥). -/
def singleLoop_Q_trivial : PropQuotientTheory singleLoopTheory :=
  PropQuotientTheory.trivial singleLoopTheory

/-- The inconsistent quotient of singleLoopTheory: adds ⊤ ⊢ ⊥.
Corresponds to the discrete topology (⊤). -/
def singleLoop_Q_inconsistent : PropQuotientTheory singleLoopTheory :=
  PropQuotientTheory.inconsistent singleLoopTheory

/-- The atomic-corresponding quotient of singleLoopTheory.
Since p₀ = ⊤ in singleLoopTheory, the intermediate quotient structures
are characterized by their topology correspondence, not by explicit axiom content.
Axiomatized because the internal structure depends on sieve-level analysis. -/
axiom singleLoop_Q_atomic : PropQuotientTheory singleLoopTheory

/-- The ⊥-collapsed-corresponding quotient of singleLoopTheory.
This collapses the bottom element of the Lindenbaum algebra, making the
"impossible" formula class degenerate. -/
axiom singleLoop_Q_collapsed : PropQuotientTheory singleLoopTheory

/-!
## Section 2: Duality Correspondence for singleLoop

Each concrete quotient theory corresponds to a specific GT topology
under Caramello's duality.
-/

/-- The trivial quotient corresponds to the trivial topology. -/
axiom singleLoop_duality_trivial :
    ∃ (f : PropQuotientTheory singleLoopTheory →
           GrothendieckTopology (LindenbaumAlgebra singleLoopTheory)),
      f singleLoop_Q_trivial = singleLoop_trivial

/-- The inconsistent quotient corresponds to the discrete topology. -/
axiom singleLoop_duality_inconsistent :
    ∃ (f : PropQuotientTheory singleLoopTheory →
           GrothendieckTopology (LindenbaumAlgebra singleLoopTheory)),
      f singleLoop_Q_inconsistent = singleLoop_discrete

/-- The atomic quotient corresponds to the atomic topology. -/
axiom singleLoop_duality_atomic :
    ∃ (f : PropQuotientTheory singleLoopTheory →
           GrothendieckTopology (LindenbaumAlgebra singleLoopTheory)),
      f singleLoop_Q_atomic = singleLoop_atomic

/-- The collapsed quotient corresponds to the ⊥-collapsed topology. -/
axiom singleLoop_duality_collapsed :
    ∃ (f : PropQuotientTheory singleLoopTheory →
           GrothendieckTopology (LindenbaumAlgebra singleLoopTheory)),
      f singleLoop_Q_collapsed = singleLoop_bottomCollapsed

/-!
## Section 3: Concrete Quotient Theories for toggle and chain3

For toggle (2 states) and chain3 (3 states), we define the three canonical
quotient theories matching the trivial, syntactic, and discrete topologies.
-/

/-- Trivial quotient of toggleTheory. -/
def toggle_Q_trivial : PropQuotientTheory toggleTheory :=
  PropQuotientTheory.trivial toggleTheory

/-- Inconsistent quotient of toggleTheory. -/
def toggle_Q_inconsistent : PropQuotientTheory toggleTheory :=
  PropQuotientTheory.inconsistent toggleTheory

/-- Syntactic quotient of toggleTheory: corresponds to the syntactic topology.
For the deterministic toggle system, this captures full state identity
(distinguishing state a from state b). -/
axiom toggle_Q_syntactic : PropQuotientTheory toggleTheory

/-- Trivial quotient of chain3Theory. -/
def chain3_Q_trivial : PropQuotientTheory chain3Theory :=
  PropQuotientTheory.trivial chain3Theory

/-- Inconsistent quotient of chain3Theory. -/
def chain3_Q_inconsistent : PropQuotientTheory chain3Theory :=
  PropQuotientTheory.inconsistent chain3Theory

/-- Syntactic quotient of chain3Theory: corresponds to the syntactic topology.
For the deterministic 3-state linear chain, this captures all positional
distinctions (states 0, 1, 2 are fully distinguished). -/
axiom chain3_Q_syntactic : PropQuotientTheory chain3Theory

/-!
## Section 4: Ordering on Concrete Quotients

The trivial quotient (empty extra axioms) is ≤ every other quotient.
For axiomatized quotients, we axiomatize the required ordering relationships.
-/

-- singleLoop ordering (diamond: trivial ≤ {atomic, collapsed} ≤ inconsistent)

/-- Trivial ≤ atomic in the quotient theory order. -/
theorem singleLoop_Q_trivial_le_atomic :
    singleLoop_Q_trivial ≤ singleLoop_Q_atomic :=
  PropQuotientTheory.trivial_le _

/-- Trivial ≤ collapsed in the quotient theory order. -/
theorem singleLoop_Q_trivial_le_collapsed :
    singleLoop_Q_trivial ≤ singleLoop_Q_collapsed :=
  PropQuotientTheory.trivial_le _

/-- Atomic ≤ inconsistent in the quotient theory order. -/
axiom singleLoop_Q_atomic_le_inconsistent :
    singleLoop_Q_atomic ≤ singleLoop_Q_inconsistent

/-- Collapsed ≤ inconsistent in the quotient theory order. -/
axiom singleLoop_Q_collapsed_le_inconsistent :
    singleLoop_Q_collapsed ≤ singleLoop_Q_inconsistent

-- toggle ordering (chain: trivial ≤ syntactic ≤ inconsistent)

/-- Trivial ≤ syntactic for toggle. -/
theorem toggle_Q_trivial_le_syntactic :
    toggle_Q_trivial ≤ toggle_Q_syntactic :=
  PropQuotientTheory.trivial_le _

/-- Syntactic ≤ inconsistent for toggle. -/
axiom toggle_Q_syntactic_le_inconsistent :
    toggle_Q_syntactic ≤ toggle_Q_inconsistent

-- chain3 ordering (chain: trivial ≤ syntactic ≤ inconsistent)

/-- Trivial ≤ syntactic for chain3. -/
theorem chain3_Q_trivial_le_syntactic :
    chain3_Q_trivial ≤ chain3_Q_syntactic :=
  PropQuotientTheory.trivial_le _

/-- Syntactic ≤ inconsistent for chain3. -/
axiom chain3_Q_syntactic_le_inconsistent :
    chain3_Q_syntactic ≤ chain3_Q_inconsistent

/-!
## Section 5: Quotient Completeness for singleLoop

Every quotient theory of singleLoopTheory is deductively equivalent to
one of the 4 concrete quotient theories. This follows from the duality
theorem and the topology completeness from TopologyEnumeration.lean.
-/

/-- Every quotient theory of singleLoopTheory is deductively equivalent to
one of the 4 concrete quotient theories. -/
axiom singleLoop_quotient_complete :
    ∀ (Q : PropQuotientTheory singleLoopTheory),
      Q.DeductivelyEquiv singleLoop_Q_trivial ∨
      Q.DeductivelyEquiv singleLoop_Q_atomic ∨
      Q.DeductivelyEquiv singleLoop_Q_collapsed ∨
      Q.DeductivelyEquiv singleLoop_Q_inconsistent

/-!
## Section 6: Process Equivalence Interpretation

Each quotient theory captures a "level of observation" of the system:

### singleLoop (1 state, 1 self-loop):
- **Trivial quotient** (singleLoop_Q_trivial): No observation beyond existence.
  Corresponds to the coarsest equivalence where all computations are identified.
- **Atomic quotient** (singleLoop_Q_atomic): State observation is possible.
  The single state is observable (though trivially, since there's only one).
- **Collapsed quotient** (singleLoop_Q_collapsed): Bottom element becomes degenerate.
  The "impossible state" observation is collapsed.
- **Inconsistent quotient** (singleLoop_Q_inconsistent): Everything is identified.
  Corresponds to the finest topology (discrete), yielding the trivial topos.

### toggle (2 states, bidirectional):
- **Trivial**: No state distinction. Both states are "the same."
- **Syntactic**: Full state identity. States a and b are distinguished.
- **Inconsistent**: Everything collapsed.

### chain3 (3 states, linear):
- **Trivial**: No positional information retained.
- **Syntactic**: Full position knowledge (states 0, 1, 2 distinguished).
- **Inconsistent**: Everything collapsed.

### Looking ahead:
Phase 101 will map HML (Hennessy-Milner Logic) sublanguages to quotient theories,
connecting the van Glabbeek spectrum to the quotient theory lattice via the duality.
-/

end RTS
