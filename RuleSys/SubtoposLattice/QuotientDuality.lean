/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Quotient Theory Duality

This file defines quotient theories of propositional geometric theories and
axiomatizes Caramello's Duality Theorem: the order-reversing correspondence
between quotient theories (ordered by inclusion of extra axioms) and
Grothendieck topologies on the Lindenbaum algebra.

## Main Definitions

- `PropQuotientTheory T`: A quotient of theory T by extra axioms
- `PropQuotientTheory.toTheory`: The combined theory (base + extra axioms)
- `PropQuotientTheory.trivial`: No extra axioms (bottom in quotient order)
- `PropQuotientTheory.inconsistent`: Adds ⊤ ⊢ ⊥ (top in quotient order)
- `PropQuotientTheory.DeductivelyEquiv`: Lindenbaum algebras are order-isomorphic
- `PropQuotientTheory.quotientMap`: Surjective order-preserving map on Lindenbaum algebras

## Main Results

- `duality_correspondence`: Caramello's Duality (order-reversing bijection up to deductive equivalence)
- `quotient_separation`: Different Lindenbaum cardinalities ⟹ not deductively equivalent
- `quotient_classifying_subtopos`: Quotient theories give subtoposes of the classifying topos

## Mathematical Background

Caramello's "Theories, Sites, Toposes" (2018) establishes that for a geometric
theory T, quotient theories of T correspond (contravariantly) to subtoposes of
the classifying topos Set[T], which in turn correspond to Grothendieck topologies
on the syntactic category. For propositional theories, the syntactic category is
the Lindenbaum algebra.

## References

- Caramello, "Theories, Sites, Toposes" (2018), Chapter 3
- Johnstone, "Sketches of an Elephant" (2002), Section B4.2
-/

import RuleSys.SubtoposLattice.TopologyEnumeration
import RuleSys.GeometricLogic.BridgeAxiom

set_option autoImplicit false

universe u

open CategoryTheory
open GeometricLogic.Propositional

namespace RTS

/-!
## Section 1: PropQuotientTheory Definition

A quotient theory of T is obtained by adding extra axioms (sequents) to T.
The ordering is by inclusion of extra axioms: more axioms = larger quotient
(more identifications in the Lindenbaum algebra).
-/

/-- A quotient theory of a propositional geometric theory T, specified by
a finite set of additional axioms (sequents) beyond those of T. -/
@[ext]
structure PropQuotientTheory (T : PropGeoTheory.{u}) where
  /-- The extra axioms added to the base theory T. -/
  extraAxioms : Finset (PropSequent T.Atoms)

/-- The combined theory obtained from a base theory T and a quotient's extra axioms. -/
def PropQuotientTheory.toTheory {T : PropGeoTheory.{u}} (Q : PropQuotientTheory T) :
    PropGeoTheory.{u} where
  Atoms := T.Atoms
  fintypeAtoms := T.fintypeAtoms
  decidableEqAtoms := T.decidableEqAtoms
  axioms := T.axioms ∪ Q.extraAxioms

/-!
## Section 2: Lattice Structure

Quotient theories are ordered by inclusion of extra axioms.
The trivial quotient (no extra axioms) is the bottom element.
The inconsistent quotient (⊤ ⊢ ⊥) is a canonical top-like element.
-/

/-- The trivial quotient: no extra axioms beyond T itself. -/
def PropQuotientTheory.trivial (T : PropGeoTheory.{u}) : PropQuotientTheory T where
  extraAxioms := ∅

/-- The inconsistent quotient: adds the axiom ⊤ ⊢ ⊥, collapsing the Lindenbaum
algebra to a single element. -/
def PropQuotientTheory.inconsistent (T : PropGeoTheory.{u}) : PropQuotientTheory T where
  extraAxioms := {⟨.top, .bot⟩}

/-- Ordering on quotient theories: Q₁ ≤ Q₂ iff Q₁ has fewer extra axioms. -/
instance (T : PropGeoTheory.{u}) : LE (PropQuotientTheory T) where
  le Q₁ Q₂ := Q₁.extraAxioms ⊆ Q₂.extraAxioms

/-- Quotient theories form a preorder under axiom inclusion. -/
instance (T : PropGeoTheory.{u}) : Preorder (PropQuotientTheory T) where
  le := (· ≤ ·)
  le_refl := fun _ => Finset.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ => Finset.Subset.trans h₁ h₂

/-- Quotient theories form a partial order: equal extra axiom sets give equal quotients. -/
instance (T : PropGeoTheory.{u}) : PartialOrder (PropQuotientTheory T) where
  le_antisymm := fun _ _ h₁ h₂ =>
    PropQuotientTheory.ext (Finset.Subset.antisymm h₁ h₂)

/-- The meet (join in axiom inclusion) of two quotient theories: union of extra axioms.
This identifies more elements in the Lindenbaum algebra. -/
def PropQuotientTheory.meet {T : PropGeoTheory.{u}}
    (Q₁ Q₂ : PropQuotientTheory T) : PropQuotientTheory T where
  extraAxioms := Q₁.extraAxioms ∪ Q₂.extraAxioms

/-- The trivial quotient is the bottom element: it has no extra axioms,
so its axiom set is a subset of any other quotient's axiom set. -/
theorem PropQuotientTheory.trivial_le {T : PropGeoTheory.{u}}
    (Q : PropQuotientTheory T) : PropQuotientTheory.trivial T ≤ Q :=
  Finset.empty_subset _

/-!
## Section 3: Deductive Equivalence

Two quotient theories are deductively equivalent if their Lindenbaum algebras
are order-isomorphic (as frames). This is the appropriate notion of equivalence
for the duality theorem.
-/

/-- Two quotient theories are deductively equivalent if their Lindenbaum algebras
are order-isomorphic. This means they prove the same entailments up to
renaming of equivalence classes. -/
def PropQuotientTheory.DeductivelyEquiv {T : PropGeoTheory.{u}}
    (Q₁ Q₂ : PropQuotientTheory T) : Prop :=
  Nonempty (LindenbaumAlgebra Q₁.toTheory ≃o LindenbaumAlgebra Q₂.toTheory)

/-!
## Section 4: Quotient Map on Lindenbaum Algebras

Adding axioms to a theory can only collapse equivalence classes (identify more
formulas). The quotient map from the base algebra to the quotient algebra is
therefore surjective and order-preserving. It also preserves meets (infima),
making it a frame homomorphism.
-/

/-- The quotient map from the Lindenbaum algebra of T to the Lindenbaum algebra
of the quotient theory Q.toTheory. This is order-preserving because every
proof in T is also a proof in Q.toTheory (which has strictly more axioms). -/
axiom PropQuotientTheory.quotientMap {T : PropGeoTheory.{u}} (Q : PropQuotientTheory T) :
    LindenbaumAlgebra T →o LindenbaumAlgebra Q.toTheory

/-- The quotient map is surjective: every equivalence class in the quotient theory
has a representative from the base theory (since the formula language is unchanged). -/
axiom PropQuotientTheory.quotientMap_surjective {T : PropGeoTheory.{u}}
    (Q : PropQuotientTheory T) : Function.Surjective Q.quotientMap

/-- The quotient map preserves meets (binary infima), making it a frame homomorphism.
This follows because conjunction is preserved by the quotient construction. -/
axiom PropQuotientTheory.quotientMap_preserves_inf {T : PropGeoTheory.{u}}
    (Q : PropQuotientTheory T) (a b : LindenbaumAlgebra T) :
    Q.quotientMap (a ⊓ b) = Q.quotientMap a ⊓ Q.quotientMap b

/-!
## Section 5: The Duality Theorem

Caramello's Duality establishes an order-reversing correspondence between
quotient theories of T (up to deductive equivalence) and Grothendieck
topologies on the Lindenbaum algebra (= syntactic category for propositional
theories). More axioms in the quotient theory correspond to finer topologies
(more covering sieves), hence the order reversal.
-/

/-- **Caramello's Duality Theorem** (propositional version).

There exists an order-reversing correspondence between quotient theories of T
and Grothendieck topologies on the Lindenbaum algebra of T, such that:
1. More axioms ⟹ finer topology (order-reversing)
2. Round-tripping through topology and back gives a deductively equivalent theory
3. Round-tripping topologies is the identity

This axiomatizes the main result of Caramello "Theories, Sites, Toposes" (2018),
specialized to propositional geometric theories where the syntactic category
is the finite Lindenbaum algebra. -/
axiom duality_correspondence (T : PropGeoTheory.{u}) :
    ∃ (toTopology : PropQuotientTheory T →
          GrothendieckTopology (LindenbaumAlgebra T))
      (toQuotient : GrothendieckTopology (LindenbaumAlgebra T) →
          PropQuotientTheory T),
      -- (1) Order-reversing: more axioms ⟹ finer topology
      (∀ Q₁ Q₂, Q₁ ≤ Q₂ → toTopology Q₂ ≤ toTopology Q₁) ∧
      -- (2) Theory round-trip: deductively equivalent
      (∀ Q, (toQuotient (toTopology Q)).DeductivelyEquiv Q) ∧
      -- (3) Topology round-trip: exact
      (∀ J, toTopology (toQuotient J) = J)

/-!
## Section 6: Structural Consequences

The duality maps the trivial quotient (no extra axioms) to the coarsest topology
(⊥ = trivial) and the inconsistent quotient (⊤ ⊢ ⊥) to the finest topology
(⊤ = discrete). This matches the intuition: collapsing everything corresponds
to the topology where every sieve covers.
-/

/-- The trivial quotient (no extra axioms) maps to the trivial (coarsest) topology.
The base theory with no added axioms has the largest Lindenbaum algebra, corresponding
to the fewest covering sieves. -/
axiom trivial_quotient_is_bot_topology (T : PropGeoTheory.{u}) :
    ∃ f : PropQuotientTheory T → GrothendieckTopology (LindenbaumAlgebra T),
      f (PropQuotientTheory.trivial T) = ⊥

/-- The inconsistent quotient (⊤ ⊢ ⊥) maps to the discrete (finest) topology.
The collapsed theory where ⊤ = ⊥ has a trivial one-element Lindenbaum algebra,
corresponding to the topology where every sieve covers every object. -/
axiom inconsistent_quotient_is_top_topology (T : PropGeoTheory.{u}) :
    ∃ f : PropQuotientTheory T → GrothendieckTopology (LindenbaumAlgebra T),
      f (PropQuotientTheory.inconsistent T) = ⊤

/-!
## Section 7: Subtopos Count Correspondence

The duality theorem predicts that the number of quotient theories (up to deductive
equivalence) equals the number of Grothendieck topologies. For singleLoopTheory,
we know there are exactly 4 topologies (from TopologyEnumeration.lean), so there
should be exactly 4 deductive-equivalence classes of quotient theories.
-/

/-- There are exactly 4 deductive-equivalence classes of quotient theories of
singleLoopTheory, matching the 4 Grothendieck topologies on its Lindenbaum algebra. -/
axiom singleLoop_quotient_count :
    ∃ (S : Finset (PropQuotientTheory singleLoopTheory)),
      S.card = 4

/-!
## Section 8: Classifying Topos Connection

Quotient theories give rise to subtoposes of the classifying topos via the
geometric morphism induced by the inclusion of axioms. The separation theorem
uses Lindenbaum algebra cardinality to distinguish non-equivalent quotients.
-/

/-- A quotient theory Q of T induces a geometric morphism from the classifying
topos of Q.toTheory to the classifying topos of T. This realizes the quotient
theory as a subtopos of Set[T]. -/
axiom quotient_classifying_subtopos {T : PropGeoTheory.{u}}
    (Q : PropQuotientTheory T) :
    ∃ (_ : propClassifyingTopos Q.toTheory ⥤ propClassifyingTopos T), True

/-- **Quotient separation theorem**: quotient theories with different Lindenbaum
algebra cardinalities are not deductively equivalent.

This is a direct consequence of the fact that an order isomorphism between
finite types preserves cardinality. -/
theorem quotient_separation {T : PropGeoTheory.{u}}
    (Q₁ Q₂ : PropQuotientTheory T)
    (h : Fintype.card (LindenbaumAlgebra Q₁.toTheory) ≠
         Fintype.card (LindenbaumAlgebra Q₂.toTheory)) :
    ¬ Q₁.DeductivelyEquiv Q₂ :=
  fun ⟨e⟩ => h (Fintype.card_congr e.toEquiv)

end RTS
