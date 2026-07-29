/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Modal Logic Connection: Geometric Formulas ↔ HML

This file connects the subobject structure of Set[T_LTS] = [f.p.LTS₁^op, Set] to
Hennessy-Milner Logic (HML), establishing the correspondence between geometric formulas
over the theory T_LTS and modal formulas in the process-algebraic tradition.

## The Standard Translation

The diamond modality ⟨a⟩φ in HML translates to ∃y. T_a(x,y) ∧ φ(y) in first-order
logic. When φ is itself a positive existential formula (built from ∧, ∨, ∃, ⊤, ⊥),
the result is geometric. This gives a precise correspondence:

  **Geometric formulas over T_LTS ↔ Positive existential fragment of HML**

The positive existential fragment consists of formulas built from:
  ⊤, ⊥, ∧, ∨, ⟨a⟩ (diamond modality)
without negation, implication, or box modality.

## Definable Subfunctors

In the presheaf topos [f.p.LTS₁^op, Set], a definable subfunctor of the universal sort
assigns to each finite digraph G a subset of its vertices, functorially in G (preserved
by homomorphisms). Each geometric formula φ(x) with one free variable defines such a
subfunctor: the set of vertices satisfying φ in each graph G.

For |L| = 1 (single transition relation), the basic definable subfunctors include:
  - ⟨⟩⊤ = "has an outgoing edge" = {v ∈ G | ∃ w, edge(v, w)}
  - ⟨⟩⟨⟩⊤ = "has a 2-step path" = {v ∈ G | ∃ w u, edge(v, w) ∧ edge(w, u)}
  - ⟨⟩⊥ = ∅ (no vertex satisfies ∃y. T(x,y) ∧ ⊥)

## The Heyting Gap

The Heyting algebra Ω(G) of sieves provides intuitionistic implication (S₁ → S₂),
which has no classical HML counterpart. The internal Heyting implication of the topos
could distinguish processes indistinguishable by classical HML — a genuinely topos-
theoretic phenomenon with no process-algebraic precedent.

## The Non-Geometric Boundary

The box modality [a]φ = ¬⟨a⟩¬φ requires universal quantification ∀y. T_a(x,y) → φ(y),
which is NOT geometric. Full HML (with negation) therefore goes beyond the geometric
fragment. The precise boundary:
  - Geometric ↔ positive existential HML (⟨a⟩, ∧, ∨, ⊤, ⊥)
  - Non-geometric: negation (¬), box ([a]), implication (→)

This is consistent with v14.0's finding that HML sublanguages stratify the spectrum:
trace formulas (O) ⊂ positive (HML_pos) ⊂ ready-sim (HML_ready) ⊂ full HML. The
geometric fragment corresponds to HML_pos — the positive existential part.

## References

- Hennessy & Milner, "Algebraic laws for nondeterminism and concurrency" (1985)
- Abramsky, "Domain theory in logical form" (1991)
- Ghilardi & Meloni, "Relational and topological semantics for modal logic" (1990)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), §VI.6
-/

import RuleSys.PresheafTopos.FiniteDigraph

set_option autoImplicit false

universe u

namespace RTS.PresheafTopos

/-!
## Part 1: The Diamond Subfunctor

For |L| = 1, the diamond modality ⟨⟩⊤ corresponds to the predicate "has at least one
outgoing edge." This is a definable subfunctor of the universal sort: for each graph G,
it selects the vertices with outgoing edges, and this selection is preserved by
graph homomorphisms.
-/

/-- The diamond predicate: vertex v in graph G has at least one outgoing edge.
    This corresponds to ⟨⟩⊤ in HML (with a single label). -/
def hasDiamondTrue (G : FinDigraph) (v : G.Vertex) : Prop :=
  ∃ w : G.Vertex, G.edge v w

/-- The diamond predicate is preserved by graph homomorphisms (forward).

    If v has an outgoing edge in G and f: G → H is a homomorphism, then f(v)
    has an outgoing edge in H.

    This is the key property making ⟨⟩⊤ a legitimate subobject of the universal
    sort in [f.p.LTS₁^op, Set]. -/
theorem diamond_preserved_by_hom {G H : FinDigraph} (f : DigraphHom G H)
    (v : G.Vertex) (hv : hasDiamondTrue G v) : hasDiamondTrue H (f.toFun v) := by
  obtain ⟨w, hw⟩ := hv
  exact ⟨f.toFun w, f.map_edge v w hw⟩

/-- The double diamond predicate: vertex v has a 2-step path.
    Corresponds to ⟨⟩⟨⟩⊤ in HML. -/
def hasDoubleDiamond (G : FinDigraph) (v : G.Vertex) : Prop :=
  ∃ w : G.Vertex, G.edge v w ∧ ∃ u : G.Vertex, G.edge w u

/-- Double diamond is preserved by homomorphisms.
    This generalizes to ⟨⟩ⁿ⊤ for any depth n. -/
theorem double_diamond_preserved_by_hom {G H : FinDigraph} (f : DigraphHom G H)
    (v : G.Vertex) (hv : hasDoubleDiamond G v) :
    hasDoubleDiamond H (f.toFun v) := by
  obtain ⟨w, hw, u, hu⟩ := hv
  exact ⟨f.toFun w, f.map_edge v w hw, f.toFun u, f.map_edge w u hu⟩

/-!
## Part 2: Concrete Diamond Evaluation at Small Objects

We compute which vertices satisfy ⟨⟩⊤ in each of the small objects.
-/

/-- In the empty graph ∅, no vertex satisfies ⟨⟩⊤ (vacuously). -/
theorem diamond_empty : ∀ (v : emptyDigraph.Vertex), ¬hasDiamondTrue emptyDigraph v :=
  fun v => isEmptyElim v

/-- In •₀ (loopless vertex), the unique vertex does NOT satisfy ⟨⟩⊤. -/
theorem diamond_loopless : ¬hasDiamondTrue looplessVertex () := by
  intro ⟨w, hw⟩
  exact hw

/-- In •₁ (loop vertex), the unique vertex DOES satisfy ⟨⟩⊤. -/
theorem diamond_loop : hasDiamondTrue loopVertex () :=
  ⟨(), trivial⟩

/-- In the arrow graph (→), vertex false (= 0) satisfies ⟨⟩⊤ but vertex true (= 1) does not. -/
theorem diamond_arrow_source : hasDiamondTrue arrowDigraph false :=
  ⟨true, ⟨rfl, rfl⟩⟩

theorem diamond_arrow_target : ¬hasDiamondTrue arrowDigraph true := by
  intro ⟨w, hw⟩
  exact absurd hw.1 Bool.noConfusion

/-!
## Part 3: Homomorphism-Preservation Demonstrates Subfunctor Structure

The fact that homomorphisms preserve ⟨⟩⊤ means: the assignment
  G ↦ {v ∈ G.Vertex | hasDiamondTrue G v}
defines a subfunctor of the forgetful functor U: FinDigraph → Set that sends G to G.Vertex.

In the presheaf topos [f.p.LTS₁^op, Set], this subfunctor corresponds to a subobject
of the generic LTS. The geometric formula ∃y. T(x,y) defines this subobject.

Homomorphisms preserve the subfunctor in the forward direction:
  f: G → H homomorphism, v ∈ diamond(G) ⟹ f(v) ∈ diamond(H)

This is the content of diamond_preserved_by_hom above. The reverse direction does NOT
hold in general: f(v) ∈ diamond(H) does NOT imply v ∈ diamond(G). This asymmetry
reflects the distinction between homomorphisms and bisimulation morphisms.
-/

/-- Concrete verification: the arrow → •₁ homomorphism maps the non-diamond vertex
    true to the diamond vertex () in •₁. This shows backward preservation fails:
    f(true) = () satisfies ⟨⟩⊤ in •₁, but true does NOT satisfy ⟨⟩⊤ in →. -/
theorem diamond_backward_fails :
    hasDiamondTrue loopVertex (arrow_to_loop.toFun true) ∧
    ¬hasDiamondTrue arrowDigraph true :=
  ⟨diamond_loop, diamond_arrow_target⟩

/-!
## Part 4: The Standard Translation (Documentation)

The standard translation from HML to first-order logic over T_LTS:

  ST_x(⊤) = ⊤
  ST_x(⊥) = ⊥
  ST_x(φ ∧ ψ) = ST_x(φ) ∧ ST_x(ψ)
  ST_x(φ ∨ ψ) = ST_x(φ) ∨ ST_x(ψ)
  ST_x(⟨a⟩φ) = ∃y. T_a(x,y) ∧ ST_y(φ)
  ST_x(¬φ) = ¬ST_x(φ)                     — NOT geometric
  ST_x([a]φ) = ∀y. T_a(x,y) → ST_y(φ)    — NOT geometric

The positive existential fragment (no ¬, no [a]) produces geometric formulas.
Full HML with negation produces classical first-order formulas.

### The Precise Boundary

| HML Fragment | First-Order Logic | Geometric? |
|-------------|-------------------|------------|
| ⊤, ⊥ | ⊤, ⊥ | Yes |
| φ ∧ ψ | φ ∧ ψ | Yes |
| φ ∨ ψ | φ ∨ ψ | Yes |
| ⟨a⟩φ | ∃y. T_a(x,y) ∧ φ(y) | Yes (if φ geometric) |
| ¬φ | ¬φ | NO |
| [a]φ | ∀y. T_a(x,y) → φ(y) | NO |

Therefore: **Geometric formulas over T_LTS = Positive existential HML (= HML_pos)**.

This matches v13.0's spectrum stratification:
  Trace (O) ⊊ Positive (HML_pos) ⊊ Ready-Sim (HML_ready) ⊊ Full HML

The geometric fragment captures the first two levels. Ready-sim adds inability
atoms ¬⟨a⟩⊤ (negated diamonds at ground level), and full HML adds arbitrary negation.
-/

/-!
## Part 5: The Heyting Gap — Intuitionistic Logic Beyond HML

The subobject classifier Ω of [f.p.LTS₁^op, Set] is a Heyting algebra, providing
an intuitionistic implication → that has no counterpart in classical HML.

For two subfunctors S₁, S₂ of the universal sort:
  (S₁ → S₂)(G) = {v ∈ G | ∀ f: H → G, ∀ w, f(w) = v ∧ w ∈ S₁(H) → w ∈ S₂(H)}

This is a "for all tests that witness S₁ at v, S₂ also holds" — a universally
quantified condition that goes beyond positive existential logic.

### Process-Theoretic Interpretation

The Heyting implication S₁ → S₂ in Ω has a process-theoretic reading:
  "Any observation that witnesses property S₁ also witnesses property S₂"

This is an intuitionistic conditional that could distinguish processes
indistinguishable by classical HML. Whether this actually occurs (i.e., whether
the Heyting structure of Ω adds genuine discriminating power beyond HML) is an
open question — one of the motivations for studying Ω process-theoretically.

### Connection to Negation Collapse (Phase 161)

The unique atom theorem (Phase 161) showed that ¬S = ∅ for all non-empty sieves S.
This means Heyting negation ¬S in Ω is maximally degenerate — collapsing to the
bottom sieve for any non-trivial S. However, Heyting IMPLICATION S₁ → S₂ (for
non-comparable S₁, S₂) can still be informative, exactly as in the L₃₀ case where
¬x = ⊥ but S → F = IF (v18.0 discovery).
-/

/-- Summary: the modal-geometric correspondence for Set[T_LTS]. -/
structure ModalGeometricCorrespondence where
  /-- Diamond preservation: ⟨⟩⊤ is a definable subfunctor -/
  diamond_is_subfunctor :
    ∀ {G H : FinDigraph} (f : DigraphHom G H) (v : G.Vertex),
      hasDiamondTrue G v → hasDiamondTrue H (f.toFun v)
  /-- Backward preservation fails (homomorphisms ≠ bisimulations) -/
  backward_fails :
    ∃ (G H : FinDigraph) (f : DigraphHom G H) (v : G.Vertex),
      hasDiamondTrue H (f.toFun v) ∧ ¬hasDiamondTrue G v
  /-- Diamond evaluation at small objects -/
  diamond_loop_true : hasDiamondTrue loopVertex ()
  diamond_loopless_false : ¬hasDiamondTrue looplessVertex ()

/-- The modal-geometric correspondence holds for f.p.LTS₁. -/
def modalGeometric : ModalGeometricCorrespondence where
  diamond_is_subfunctor := fun f v hv => diamond_preserved_by_hom f v hv
  backward_fails := ⟨arrowDigraph, loopVertex, arrow_to_loop, true,
    diamond_loop, diamond_arrow_target⟩
  diamond_loop_true := diamond_loop
  diamond_loopless_false := diamond_loopless

end RTS.PresheafTopos
