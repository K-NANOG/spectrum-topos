/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Directed Graphs: The Category f.p.LTS₁

This file defines the category of finite directed graphs with graph homomorphisms,
which is the category f.p.LTS_L of finitely presentable models of the Horn theory
T_LTS for |L| = 1 (a single sort S and one binary relation T).

## Key Distinction: Homomorphisms vs Bisimulation Morphisms

For a Horn theory with relational symbols (no function symbols, no axioms), the
finitely presentable models are precisely the finite models, and the morphisms are
**homomorphisms** — functions that preserve relations in the forward direction only.
This is strictly weaker than bisimulation morphisms, which additionally require
a backward lifting condition (the "zig-zag" property).

Reference: Sobociński (JCSS 2015) — morphisms in the model category of a Horn theory
are transition-preserving functions, not bisimulations.

## Mathematical Content

The presheaf topos [f.p.LTS_L^op, Set] is the classifying topos Set[T_LTS] of the
geometric theory of L-labeled transition systems. Its properties (De Morgan, non-Boolean,
etc.) are determined by the structure of the base category f.p.LTS_L.

For |L| = 1, f.p.LTS₁ is the category **FinDiGraph** of finite directed graphs
(finite sets equipped with a binary relation) and graph homomorphisms (functions
preserving the relation forward).

### Small Objects

- **0 vertices**: ∅ (the empty graph) — initial object
- **1 vertex**: •₀ (no self-loop), •₁ (self-loop) — 2 non-isomorphic objects
- **2 vertices**: 10 non-isomorphic digraphs (OEIS A000595)
  By Burnside: |{0,1}×{0,1} → Bool| = 2⁴ = 16 edge configs, S₂ acts,
  (16 + #{fixed by swap})/2 = (16 + 4)/2 = 10

### Key Properties

- ∅ is initial (unique empty function to any graph)
- •₁ is terminal (unique function to singleton, self-loop always preserved)
- •₀ → •₁ exists but •₁ → •₀ does not (not a groupoid ⟹ not Boolean)
- The arrow graph → admits a homomorphism to •₁ that is NOT a bisimulation morphism

## References

- Sobociński, "Relational presheaves, change of base and weak simulation" (JCSS 2015)
- OEIS A000595: Number of binary relations on an n-element set up to permutation
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992) — presheaf toposes
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

universe u

namespace Ruliology.PresheafTopos

/-!
## Part 1: Finite Directed Graphs and Graph Homomorphisms
-/

/-- A finite directed graph: a finite set of vertices with a decidable binary edge relation.
    For |L| = 1, this is exactly a finitely presentable model of the Horn theory T_LTS. -/
structure FinDigraph where
  /-- The vertex type -/
  Vertex : Type
  /-- Finiteness of vertices -/
  [vertexFintype : Fintype Vertex]
  /-- Decidable equality on vertices -/
  [vertexDecEq : DecidableEq Vertex]
  /-- The edge relation -/
  edge : Vertex → Vertex → Prop
  /-- Decidability of edges -/
  [edgeDecidable : DecidableRel edge]

attribute [instance] FinDigraph.vertexFintype FinDigraph.vertexDecEq FinDigraph.edgeDecidable

/-- A graph homomorphism: a function on vertices that preserves edges in the forward
    direction. This is the correct notion of morphism for the category f.p.LTS_L —
    it preserves the binary relation T forward but does NOT require the backward
    lifting condition that bisimulation morphisms demand. -/
structure DigraphHom (G H : FinDigraph) where
  /-- The underlying function on vertices -/
  toFun : G.Vertex → H.Vertex
  /-- Forward edge preservation: if s →_G t then f(s) →_H f(t) -/
  map_edge : ∀ (s t : G.Vertex), G.edge s t → H.edge (toFun s) (toFun t)

namespace DigraphHom

/-- Extensionality for graph homomorphisms -/
theorem ext {G H : FinDigraph} {f g : DigraphHom G H}
    (h : ∀ v, f.toFun v = g.toFun v) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  funext v
  exact h v

/-- Identity homomorphism -/
def id (G : FinDigraph) : DigraphHom G G where
  toFun := _root_.id
  map_edge := fun _ _ h => h

/-- Composition of homomorphisms -/
def comp {G H K : FinDigraph} (f : DigraphHom G H) (g : DigraphHom H K) :
    DigraphHom G K where
  toFun := g.toFun ∘ f.toFun
  map_edge := fun s t h => g.map_edge _ _ (f.map_edge s t h)

theorem comp_assoc {G H K L : FinDigraph}
    (f : DigraphHom G H) (g : DigraphHom H K) (h : DigraphHom K L) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext; intro v; rfl

theorem id_comp {G H : FinDigraph} (f : DigraphHom G H) :
    comp (id G) f = f := by
  apply ext; intro v; rfl

theorem comp_id {G H : FinDigraph} (f : DigraphHom G H) :
    comp f (id H) = f := by
  apply ext; intro v; rfl

end DigraphHom

/-!
## Part 2: Category Instance

We define a Mathlib Category instance on FinDigraph using DigraphHom as morphisms.
-/

instance : CategoryTheory.CategoryStruct FinDigraph where
  Hom := DigraphHom
  id := DigraphHom.id
  comp := fun f g => DigraphHom.comp f g

instance : CategoryTheory.Category FinDigraph where
  id_comp := fun f => DigraphHom.id_comp f
  comp_id := fun f => DigraphHom.comp_id f
  assoc := fun f g h => DigraphHom.comp_assoc f g h

/-!
## Part 3: Small Objects (0 and 1 vertex)
-/

/-- The empty graph (0 vertices). Initial object in f.p.LTS₁. -/
@[reducible] def emptyDigraph : FinDigraph where
  Vertex := Empty
  edge := fun _ _ => False
  edgeDecidable := fun _ _ => isFalse id

/-- A single vertex with no self-loop (•₀). -/
@[reducible] def looplessVertex : FinDigraph where
  Vertex := Unit
  edge := fun _ _ => False

/-- A single vertex with a self-loop (•₁). Terminal object in f.p.LTS₁.
    The self-loop means •₁ has edge ((), ()) = True. -/
@[reducible] def loopVertex : FinDigraph where
  Vertex := Unit
  edge := fun _ _ => True

/-!
## Part 4: Initial and Terminal Objects
-/

/-- The empty graph is initial: there exists a unique homomorphism ∅ → G for any G. -/
def emptyDigraph_to (G : FinDigraph) : DigraphHom emptyDigraph G where
  toFun v := isEmptyElim v
  map_edge s _ _ := isEmptyElim s

/-- The homomorphism from ∅ is unique (by extensionality on the empty type). -/
theorem emptyDigraph_hom_unique (G : FinDigraph) (f g : DigraphHom emptyDigraph G) :
    f = g := by
  apply DigraphHom.ext
  intro v
  exact isEmptyElim v

/-- The loop vertex •₁ is terminal: there exists a homomorphism G → •₁ for any G. -/
def to_loopVertex (G : FinDigraph) : DigraphHom G loopVertex where
  toFun := fun _ => ()
  map_edge := fun _ _ _ => trivial

-- With @[reducible], Lean can see emptyDigraph.Vertex = Empty, loopVertex.Vertex = Unit
-- so IsEmpty, Subsingleton, Unique instances are inferred automatically.

/-- The homomorphism to •₁ is unique (the target has only one vertex). -/
theorem loopVertex_hom_unique (G : FinDigraph) (f g : DigraphHom G loopVertex) :
    f = g := by
  apply DigraphHom.ext
  intro v
  exact Subsingleton.elim _ _

/-!
## Part 5: Not a Groupoid

The morphism •₀ → •₁ exists but •₁ → •₀ does not, proving f.p.LTS₁ is not a groupoid.
This is the key reason Set[T_LTS] is non-Boolean (Mac Lane-Moerdijk V.8).
-/

/-- The unique homomorphism •₀ → •₁ (the unique function Unit → Unit trivially
    preserves edges since •₀ has no edges). -/
def noloop_to_loop : DigraphHom looplessVertex loopVertex where
  toFun := fun _ => ()
  map_edge := fun _ _ h => False.elim h

/-- There is NO homomorphism •₁ → •₀: the self-loop on •₁ would need to map to
    an edge in •₀, but •₀ has no edges. -/
theorem loop_to_noloop_impossible (f : DigraphHom loopVertex looplessVertex) : False :=
  f.map_edge () () trivial

/-- f.p.LTS₁ is not a groupoid: the morphism •₀ → •₁ has no inverse. -/
theorem not_groupoid :
    ∃ (G H : FinDigraph) (_ : DigraphHom G H),
      IsEmpty (DigraphHom H G) :=
  ⟨looplessVertex, loopVertex, noloop_to_loop,
    ⟨fun f => loop_to_noloop_impossible f⟩⟩

/-!
## Part 6: The Arrow Graph and Non-Bisimulation Verification

The arrow graph → = ({0, 1}, {(0,1)}) admits a homomorphism to •₁ that is
a valid graph homomorphism but NOT a bisimulation morphism. This verifies that
the category f.p.LTS_L uses homomorphisms (forward preservation only), not
bisimulation morphisms (forward + backward).
-/

/-- The arrow graph: two vertices with a single directed edge 0 → 1. -/
def arrowDigraph : FinDigraph where
  Vertex := Bool
  edge := fun s t => s = false ∧ t = true

/-- Homomorphism from the arrow graph to the loop vertex: send both vertices
    to the unique vertex. Edge (0,1) maps to ((),()) which is the self-loop. -/
def arrow_to_loop : DigraphHom arrowDigraph loopVertex where
  toFun := fun _ => ()
  map_edge := fun _ _ _ => trivial

/-- A bisimulation morphism: a graph homomorphism with the additional backward
    lifting condition. If f(s) has an outgoing edge to u in the codomain, then
    s must have an outgoing edge to some t with f(t) = u in the domain.

    This is strictly stronger than a plain homomorphism. Bisimulation morphisms
    are the "correct" morphisms for bisimulation equivalence, but they are NOT
    the morphisms of f.p.LTS_L (which is a model category of a Horn theory). -/
structure BisimHom (G H : FinDigraph) extends DigraphHom G H where
  /-- Backward lifting: if f(s) →_H u then ∃ t, s →_G t ∧ f(t) = u -/
  back_edge : ∀ (s : G.Vertex) (u : H.Vertex),
    H.edge (toFun s) u → ∃ t, G.edge s t ∧ toFun t = u

/-- The homomorphism arrow → •₁ is NOT a bisimulation morphism.

    Proof: In the arrow graph, vertex 1 (= true) has no outgoing edges.
    In •₁, the image of vertex 1 (= ()) has a self-loop () → ().
    The backward condition requires: ∃ t, arrowDigraph.edge true t.
    But no such t exists (the only edge is false → true, and true has
    no outgoing edges). Contradiction. -/
theorem arrow_to_loop_not_bisim :
    ¬∃ (b : BisimHom arrowDigraph loopVertex),
      b.toDigraphHom = arrow_to_loop := by
  intro ⟨b, _⟩
  -- The backward condition at vertex `true` (= 1) and target `()`:
  -- b.back_edge true () trivial gives ∃ t, arrowDigraph.edge true t ∧ ...
  obtain ⟨t, ht, _⟩ := b.back_edge true () trivial
  -- arrowDigraph.edge true t requires true = false, contradiction
  exact absurd ht.1 Bool.noConfusion

/-!
## Part 7: 2-Vertex Enumeration (Documentation)

For |L| = 1, the objects of f.p.LTS₁ on 2 vertices are non-isomorphic directed
graphs on {0, 1}. There are 2⁴ = 16 possible edge configurations (each of the
4 ordered pairs can be present or absent). The symmetric group S₂ acts by
swapping 0 and 1. By Burnside's lemma:

  |orbits| = (|Fix(id)| + |Fix(swap)|) / |S₂|
           = (16 + |Fix(swap)|) / 2

The swap fixes a configuration iff edges are invariant under 0↔1:
  - (0,0) ↔ (1,1): self-loops must match
  - (0,1) ↔ (1,0): cross-edges must match
So fixed configurations have 2 independent choices: {self-loops on/off} × {cross-edges on/off}
  |Fix(swap)| = 2² = 4

  |orbits| = (16 + 4) / 2 = 10

The 10 non-isomorphic digraphs on 2 vertices:
  (1) No edges
  (2) One cross-edge (0→1, symmetric to 1→0)
  (3) Both cross-edges (0↔1, no self-loops)
  (4) One self-loop only (on vertex 0, symmetric to vertex 1)
  (5) Both self-loops only
  (6) One self-loop + one cross-edge (same source)
  (7) One self-loop + one cross-edge (different sources)
  (8) Both self-loops + one cross-edge
  (9) One self-loop + both cross-edges
  (10) Complete graph (all 4 edges)

This matches OEIS A000595 at n=2.
-/

/-- Summary of categorical properties of f.p.LTS₁ established in this file. -/
theorem fpLTS1_has_initial : ∀ G : FinDigraph, ∃! (_ : DigraphHom emptyDigraph G), True :=
  fun G => ⟨emptyDigraph_to G, trivial, fun _ _ => emptyDigraph_hom_unique G _ _⟩

theorem fpLTS1_has_terminal : ∀ G : FinDigraph, ∃! (_ : DigraphHom G loopVertex), True :=
  fun G => ⟨to_loopVertex G, trivial, fun _ _ => loopVertex_hom_unique G _ _⟩

theorem fpLTS1_not_groupoid :
    ∃ (G H : FinDigraph) (_ : DigraphHom G H), IsEmpty (DigraphHom H G) :=
  not_groupoid

theorem fpLTS1_hom_not_bisim :
    ∃ (G H : FinDigraph) (f : DigraphHom G H),
      ¬∃ (b : BisimHom G H), b.toDigraphHom = f :=
  ⟨arrowDigraph, loopVertex, arrow_to_loop, arrow_to_loop_not_bisim⟩

end Ruliology.PresheafTopos
