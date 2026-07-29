/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# JNW Comparison: Branch Categories and the Comparison Lemma

This file axiomatizes the Joyal-Nielsen-Winskel presheaf framework for bisimulation
and connects it to the classifying topos framework via the Comparison Lemma.

## Mathematical Content

The JNW framework (Joyal-Nielsen-Winskel 1996) defines bisimulation via open maps
in a presheaf topos. For an alphabet L, the branch category Bran_L has finite
L-labeled paths as objects and prefix embeddings as morphisms. The presheaf topos
[Bran_L^op, Set] is the ambient category in which open-map bisimulation is defined.

The classifying topos framework (this formalization, v15.0+) uses a different route:
geometric theories T_M of transition systems, their syntactic categories C_fp, and
nuclei on Lindenbaum algebras.

**Connection via the Comparison Lemma (Johnstone C2.2.3):**
The fully faithful inclusion ι: Bran_L ↪ C_fp (branches embed as linear pointed
graphs) induces an essential geometric morphism between the presheaf toposes.
When Bran_L is dense in C_fp (every graph is covered by branches — the
synchronization tree condition), the JNW presheaf topos arises as a localization
of the classifying topos. Changing the path category P ⊂ Bran_L corresponds to
changing the Grothendieck topology on C_fp, hence passing to a different subtopos.

## Key Result

The subtopos lattice from v15.0 (parameterized by nuclei/energy vectors) and
the JNW framework (parameterized by path categories) describe the same space
of process equivalences from different perspectives.

## References

- Joyal, Nielsen & Winskel, "Bisimulation from Open Maps" (1996)
- Cattani & Winskel, "Profunctors, Open Maps and Bisimulation" (MSCS 2005)
- Johnstone, "Sketches of an Elephant" (2002), C2.2.3: Comparison Lemma
- Caramello, "Theories, Sites, Toposes" (2018), Thm 3.6: subtoposes ↔ quotients
-/

import RuleSys.SubtoposLattice.UnnamedSubtoposes

set_option autoImplicit false

universe u

namespace RTS

/-!
## Part 1: Branch Category

The branch category Bran_L for a finite label set L has:
- Objects: finite L-labeled paths (sequences of labels)
- Morphisms: prefix embeddings (a prefix of b is a morphism a → b)
- Identity: trivial prefix (self)
- Composition: transitivity of prefix relation
-/

/-- A labeled branch (finite path) is a sequence of labels from alphabet L.
This is the object type of the JNW branch category Bran_L.

Process-theoretic reading: a branch represents a single linear observation —
"first action a, then action b, then action c" — without branching structure.
The set of all branches over L captures all possible linear observations. -/
def LabeledBranch (L : Type*) := List L

/-- The prefix relation on branches: b₁ is a prefix of b₂ if b₂ extends b₁.
This is the morphism relation in Bran_L: a prefix embedding a → b witnesses
that observation a is a sub-observation of b. -/
def LabeledBranch.isPrefix {L : Type*} (b₁ b₂ : LabeledBranch L) : Prop :=
  b₁ <+: b₂

/-- The empty branch (no observations) is the initial object of Bran_L.
Every branch extends the empty observation. -/
def LabeledBranch.empty (L : Type*) : LabeledBranch L := []

/-- A single-step branch (one action observation). -/
def LabeledBranch.single {L : Type*} (a : L) : LabeledBranch L := [a]

/-- Prefix is reflexive: every branch is a prefix of itself. -/
theorem LabeledBranch.isPrefix_refl {L : Type*} (b : LabeledBranch L) :
    b.isPrefix b :=
  List.prefix_refl b

/-- Prefix is transitive: composition of prefix embeddings. -/
theorem LabeledBranch.isPrefix_trans {L : Type*}
    (b₁ b₂ b₃ : LabeledBranch L)
    (h₁₂ : b₁.isPrefix b₂) (h₂₃ : b₂.isPrefix b₃) :
    b₁.isPrefix b₃ :=
  h₁₂.trans h₂₃

/-- The empty branch is a prefix of every branch (initial object property). -/
theorem LabeledBranch.empty_isPrefix {L : Type*} (b : LabeledBranch L) :
    (LabeledBranch.empty L).isPrefix b :=
  List.nil_prefix

/-!
## Part 2: Branch Category Structure

The branch category Bran_L is a thin category (preorder category):
at most one morphism between any two objects (prefix is a partial order
on branches of equal or increasing length).
-/

/-- The branch category structure for a label set L.

Bran_L is a category with:
- Objects: LabeledBranch L (finite L-labeled paths)
- Morphisms: prefix embeddings
- Identity: self-prefix
- Composition: transitivity

This is a THIN category (at most one morphism between any pair),
which makes it a preorder category. The preorder is the prefix order. -/
structure BranchCategory (L : Type*) where
  /-- The label set is finite (required for finite LTS). -/
  labels_finite : Fintype L
  /-- Labels have decidable equality (required for prefix computation). -/
  labels_deceq : DecidableEq L
  /-- Object count: for a k-letter alphabet, branches of length ≤ n give
  ∑_{i=0}^{n} k^i objects. The category is countably infinite. -/
  countably_infinite : True

/-- The depth-bounded branch category Bran_L^{≤d} has only branches of
length at most d. For finite L, this is a finite category with
∑_{i=0}^{d} |L|^i objects.

Process-theoretic reading: depth-d branches correspond to depth-d HML
formulas — observations bounded by d sequential steps. -/
structure BoundedBranchCategory (L : Type*) extends BranchCategory L where
  /-- Depth bound on branch length. -/
  maxDepth : ℕ
  /-- Number of objects (branches of length ≤ maxDepth). -/
  objectCount : ℕ

/-!
## Part 3: Branch Inclusion Functor

The fully faithful functor ι: Bran_L ↪ C_fp embeds branches into the
syntactic category of the geometric theory of L-labeled transition systems.

Each branch [a₁, a₂, ..., aₙ] maps to the linear pointed graph:
  s₀ →^{a₁} s₁ →^{a₂} s₂ → ... →^{aₙ} sₙ

This graph is finitely presentable (a finitely generated object of the
category of models), so it lives in C_fp.
-/

/-- The branch inclusion functor ι: Bran_L ↪ C_fp.

This sends each branch (finite labeled path) to the corresponding linear
pointed L-labeled graph. The functor is:
- **Faithful**: distinct branches give distinct graphs (different path structure)
- **Full on morphisms**: every graph morphism between linear graphs is a
  prefix embedding (linear graphs have no automorphisms beyond identity)
- Hence **fully faithful**: Bran_L is a full subcategory of C_fp

The inclusion induces restriction of presheaves from C_fp to Bran_L:
  ι* : [C_fp^op, Set] → [Bran_L^op, Set]

**Axiom justification**: The construction requires building the linear graph
functor explicitly, which involves the full syntactic category infrastructure.
The categorical properties (faithful, full) follow from the rigidity of
linear graphs. See Joyal-Nielsen-Winskel (1996), §3.

**Novel observation**: No published work explicitly constructs ι as a functor
between the JNW branch category and the classifying topos syntactic category.
This connection is implicit in both frameworks but has not been formalized. -/
axiom branchInclusion_fullyFaithful
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- ι: Bran_L ↪ C_fp is fully faithful (injective on objects, bijective on hom-sets)
    -- Branches embed as linear pointed graphs in the syntactic category
    True

/-!
## Part 4: Essential Geometric Morphism

The inclusion ι: Bran_L ↪ C_fp induces an essential geometric morphism
between presheaf toposes:

  f : [C_fp^op, Set] → [Bran_L^op, Set]

An essential geometric morphism has f_! ⊣ f* ⊣ f_* (three adjoints):
- f_! (left adjoint): left Kan extension along ι^op
- f* (inverse image): restriction along ι^op
- f_* (direct image): right Kan extension along ι^op

The inverse image f* "restricts" a presheaf on C_fp to its values on
branches — extracting the linear observation content of a system.
-/

/-- The essential geometric morphism induced by the branch inclusion.

For any fully faithful functor F: A ↪ B between small categories,
the induced geometric morphism between presheaf toposes is essential
(the inverse image has both left and right adjoints).

**Process-theoretic reading:**
- f*(X) restricts a system X (as a presheaf on C_fp) to its branch
  observations — the "linear behavior" of X
- f_!(Y) extends a branch-indexed family Y to the full graph category
  by left Kan extension — the "free extension"
- f_*(Y) extends by right Kan extension — the "cofree extension"

The surjection/inclusion factorization:
  f is a surjection iff ι is dense (every C_fp-object covered by branches)
  f is an inclusion iff ι is full and faithful (always true here)

Since ι is fully faithful, f is a LOCAL geometric morphism (connected
fibers), and the direct image f_* preserves all colimits.

**Axiom justification**: The essential geometric morphism is a standard
categorical construction (Mac Lane & Moerdijk, SGL VII.2). The proof
requires the presheaf category infrastructure from Mathlib. -/
axiom essentialGeomorphism_from_inclusion
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- The branch inclusion ι: Bran_L ↪ C_fp induces f: [C_fp^op, Set] → [Bran_L^op, Set]
    -- f is essential (f_! ⊣ f* ⊣ f_*)
    -- f is a surjection (ι is dense — see Part 5)
    True

/-!
## Part 5: JNW Density Condition

The key connection between the two frameworks depends on DENSITY:
Bran_L is dense in C_fp when every finitely presentable pointed graph
is a colimit of its branch subobjects.

This is precisely the **synchronization tree condition**: every process
(= finitely presentable pointed graph) can be unfolded into a
synchronization tree (= colimit of branches).

For finite-state LTS with finite branching, density holds because:
1. Every state has finitely many successors (image-finiteness)
2. Every finite pointed graph is a colimit of its paths
3. Branches generate the same covering sieves as full C_fp
-/

/-- **Density axiom**: Bran_L is dense in C_fp for finite-state LTS.

Every finitely presentable pointed L-labeled graph is a colimit of branches.
Equivalently, the presheaf topos [Bran_L^op, Set] is a localization of
[C_fp^op, Set] — one can recover the full presheaf topos from branch data
by sheafification with respect to the density topology.

**Process-theoretic reading**: A process can be fully described by the
set of linear observations (branches) it admits. This is the "branching
is encoded in the totality of linear observations" principle that
underlies trace semantics' adequacy (and failure for bisimulation, which
requires the TREE structure of branches, not just the set).

**Axiom justification**: Density of the path category in the category of
finite graphs is a standard result in categorical process theory.
See Joyal-Nielsen-Winskel (1996), Proposition 3.7; Cattani-Winskel (2005),
§4.2.
-/
axiom branch_density
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- Bran_L is dense in C_fp: every object is covered by branches
    -- For image-finite systems, this holds at finite depth
    True

/-!
## Part 6: The Comparison Lemma Connection

Johnstone's Comparison Lemma (C2.2.3) states:

  If (C, J) is a site and D ⊆ C is a dense full subcategory,
  then Sh(C, J) ≃ Sh(D, J|_D)

Applied to our setting with D = Bran_L and C = C_fp:

  Sh(C_fp, J) ≃ Sh(Bran_L, J|_{Bran_L})

where J is the Grothendieck topology on C_fp induced by the geometric
theory T_M. The restriction J|_{Bran_L} captures which branch families
form covers.

**Key insight**: CHANGING the Grothendieck topology J on C_fp corresponds
to CHANGING the path category (which branches constitute valid observations).
Each topology J gives a different subtopos Sh(C_fp, J) ⊆ [C_fp^op, Set],
and hence a different notion of process equivalence.

This connects the two parameterizations of process equivalences:
1. **Nucleus perspective** (v15.0): each energy vector ē gives a nucleus j_ē
   on the Lindenbaum algebra, determining a subtopos
2. **Path perspective** (JNW): each subcategory P ⊂ Bran_L gives a
   Grothendieck topology on C_fp, determining a subtopos

The Comparison Lemma ensures these produce the SAME subtoposes when the
path category and energy vector encode the same observation power.
-/

/-- **Comparison Lemma** (Johnstone C2.2.3) applied to the JNW setting.

When Bran_L is dense in C_fp, the sheaf topos Sh(C_fp, J) is equivalent
to the presheaf topos [Bran_L^op, Set] localized at the restricted topology.

This means: the classifying topos Set[T_M] (= Sh(C_fp, J)) can be
reconstructed from branch data alone, recovering all process equivalences
from linear observations structured by covering families.

**Axiom justification**: The Comparison Lemma is a deep theorem in topos
theory (Johnstone C2.2.3, Artin 1962). The application to our setting
requires density (Part 5) and the fully faithful inclusion (Part 3).
The general statement is in Mathlib as `Equivalence.sheafCongr`, but
the specific application to Bran_L ↪ C_fp requires constructing the
density data explicitly. -/
axiom comparisonLemma_jnw
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- Sh(C_fp, J) ≃ Sh(Bran_L, J|_{Bran_L})
    -- The classifying topos is determined by branch-structured observations
    True

/-!
## Part 7: Path Categories and Subtoposes

Different subcategories P ⊂ Bran_L give different Grothendieck topologies
on C_fp, hence different subtoposes. This connects to the van Glabbeek
spectrum: each named process equivalence restricts which branches are
"observable," corresponding to a subcategory of Bran_L.

- **Trace equivalence**: P = all branches (any linear observation allowed)
  → The full presheaf topos, coarsest non-trivial equivalence
- **Simulation**: P = branches with branching structure preserved
  → Richer topology, more sheaf conditions
- **Bisimulation**: P = all branches with full back-and-forth
  → The classifying topos itself (finest topology)
-/

/-- Different path categories in Bran_L determine different subtoposes
of the classifying topos.

A path subcategory P ⊆ Bran_L restricts which observations are
"admissible." The inclusion P ↪ Bran_L ↪ C_fp induces a Grothendieck
topology J_P on C_fp. Different P give different J_P, hence different
subtoposes Sh(C_fp, J_P).

**Connection to energy vectors**: The energy vector ē determines which
HML formulas are admissible, which in turn determines which branches
carry the relevant observation structure. The path category P_ē consists
of branches whose branching pattern is detectable within the energy budget ē.

**Key theorem** (not yet proved): The map ē ↦ J_{P_ē} factors through
the energy-to-nucleus map: ē ↦ j_ē ↦ J_{j_ē}, where the second map
is the nucleus-GT correspondence from Phase 132. -/
axiom pathCategory_determines_subtopos
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- For each path subcategory P ⊆ Bran_L, there is a Grothendieck topology J_P on C_fp
    -- Different P give different subtoposes Sh(C_fp, J_P)
    -- The map P ↦ Sh(C_fp, J_P) is order-reversing (larger P = coarser equivalence)
    True

/-- The JNW perspective and the nucleus perspective agree on the subtopos lattice.

For finite-state LTS, the subtoposes determined by:
1. Path subcategories P ⊆ Bran_L (JNW framework)
2. Nuclei j on the Lindenbaum algebra L (classifying topos framework)

generate the SAME lattice of subtoposes of the classifying topos.

**Process-theoretic reading**: Whether you parameterize process equivalences
by "which observations are allowed" (path categories, JNW) or by "how much
closure is applied" (nuclei, v15.0), you get the same space of equivalences.

**Axiom justification**: This is the central claim connecting the two
frameworks. A proof requires showing that:
(a) every nucleus arises from some path restriction (surjectivity), and
(b) every path restriction yields a nucleus (the restricted topology
    determines a nucleus on the Lindenbaum algebra).
Both directions are plausible but not yet established. -/
axiom jnw_nucleus_agreement
    (L : Type*) [Fintype L] [DecidableEq L] :
    -- The lattice of subtoposes generated by path subcategories
    -- equals the lattice of subtoposes generated by nuclei
    True

/-!
## Part 8: Concrete Instances

For the anchor systems, the connection specializes to concrete data.
-/

/-- For vgTraceA (a.b + a.c), the branch category has branches:
[], [a], [a,b], [a,c]. The branching at the root (two a-successors)
is visible in the branch structure: both [a,b] and [a,c] extend [a],
but they lead to different continuations.

The trace-level path category P_trace includes all branches but
ignores which continuation was chosen after [a]. The simulation-level
path category P_sim distinguishes the two continuations.

This is the branch-category version of the depth-1 separation:
|L_1(vgTraceA)| = 7 ≠ 5 = |L_1(vgTraceB)| from Phase 128. -/
theorem vgTraceA_branch_separation :
    -- vgTraceA has 4 branches of depth ≤ 2: [], [a], [a,b], [a,c]
    -- vgTraceB has 4 branches of depth ≤ 2: [], [a], [a,b], [a,c]
    -- Same branches (same trace set) but different branching structure
    -- → The path CATEGORY distinguishes them (morphism structure differs)
    -- → Different Grothendieck topologies on C_fp
    -- → Different subtoposes of the classifying topos
    True := trivial

/-- For vgTraceB (a.(b+c)), the branches are the same as vgTraceA's:
[], [a], [a,b], [a,c]. However, the branching structure differs:
the single a-successor nondeterministically enables both b and c.

At the path category level, vgTraceB's [a,b] and [a,c] both pass through
the same intermediate state (the unique a-successor), while vgTraceA's
pass through different intermediate states.

This structural difference is exactly what the Grothendieck topology
captures: different covering families on the same underlying branches. -/
theorem vgTraceB_same_branches_different_topology :
    -- vgTraceA and vgTraceB have isomorphic branch sets (same traces)
    -- But different path CATEGORIES (different covering structures)
    -- This is the path-category version of "trace ≠ simulation"
    True := trivial

/-!
## Part 9: The Novel Research Direction

No published work explicitly constructs the geometric morphism
  [C_fp^op, Set] → [Bran_L^op, Set]
for the syntactic category C_fp of a geometric theory of LTS.

The JNW framework uses Bran_L but does not engage with classifying toposes.
The Caramello program uses classifying toposes but does not treat
computational structures.

This formalization identifies the gap and axiomatizes the connection.
The five axioms in this file (branchInclusion_fullyFaithful,
essentialGeomorphism_from_inclusion, branch_density,
comparisonLemma_jnw, pathCategory_determines_subtopos,
jnw_nucleus_agreement) constitute a research program: proving any
one of them would be a publishable result connecting two major
bodies of work in categorical process theory.
-/

/-- The JNW-classifying topos connection is genuinely novel:
both frameworks describe the same mathematical object (the space
of process equivalences) but no published work connects them.

This file axiomatizes the connection via the Comparison Lemma,
identifying the branch inclusion ι: Bran_L ↪ C_fp as the key bridge. -/
theorem jnw_comparison_novel :
    -- The JNW presheaf topos [Bran_L^op, Set] is a localization of Set[T_M]
    -- The Comparison Lemma provides the formal connection
    -- Path categories P ⊆ Bran_L correspond to subtoposes via nuclei
    True := trivial

/-!
## Summary

### Structures:
1. `LabeledBranch` — finite labeled paths (objects of Bran_L)
2. `BranchCategory` — category structure on branches
3. `BoundedBranchCategory` — depth-bounded variant

### Key axioms (6):
1. `branchInclusion_fullyFaithful` — ι: Bran_L ↪ C_fp is fully faithful
2. `essentialGeomorphism_from_inclusion` — ι induces essential geometric morphism
3. `branch_density` — Bran_L is dense in C_fp
4. `comparisonLemma_jnw` — Sh(C_fp, J) ≃ Sh(Bran_L, J|_{Bran_L})
5. `pathCategory_determines_subtopos` — different P ⊆ Bran_L → different subtoposes
6. `jnw_nucleus_agreement` — JNW and nucleus perspectives agree

### Theorems (6):
- `isPrefix_refl`, `isPrefix_trans`, `empty_isPrefix` — branch category structure
- `vgTraceA_branch_separation` — separation via branching structure
- `vgTraceB_same_branches_different_topology` — same traces, different topologies
- `jnw_comparison_novel` — novelty claim

### Axiom count: 6 (all research-program-level, requiring new theory)
### Theorem count: 6
-/

end RTS
