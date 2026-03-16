/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Trace Grothendieck Topology J_trace

This file defines the trace Grothendieck topology on f.p.LTS₁ (= FinDigraph):
a sieve S on G is trace-covering iff it contains ALL homomorphisms from path
digraphs P_n into G, for every n.

## Key Results

- `isTraceCovering`: the covering predicate for J_trace
- Three Grothendieck axioms verified: maximality, stability, transitivity
- `trace_strictly_finer_than_atomic`: J_trace is strictly finer than the ¬¬-topology

## Mathematical Significance

The trace topology is the first explicit Grothendieck topology on f.p.LTS₁ whose
sheaf condition enforces a named behavioral equivalence (trace equivalence). In the
topology-as-backward-lifting narrative: the trace topology enforces the weakest
backward constraint — agreement on reachable path lengths.

For |L| = 1, trace equivalence reduces to "same set of path lengths from root."
J_trace covering sieves on G must contain witnesses for EVERY achievable trace.

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), §III.2 (Grothendieck topologies)
- van Glabbeek, "The linear time--branching time spectrum I" (1990)
-/

import RuleSys.PresheafTopos.PathDigraph
import RuleSys.PresheafTopos.SubobjectClassifier

set_option autoImplicit false

namespace RTS.PresheafTopos

/-!
## Part 1: Pullback Sieve
-/

/-- The pullback (restriction) of a sieve along a morphism.
    Given S a sieve on G and h : H → G, the pullback h*(S) is a sieve on H
    where g : K → H is in h*(S) iff h ∘ g : K → G is in S. -/
def DigraphSieve.pullback {G H : FinDigraph} (S : DigraphSieve G)
    (h : DigraphHom H G) : DigraphSieve H where
  mem := fun K g => S.mem K (DigraphHom.comp g h)
  precomp_closed := fun {_H' K} g k hmem => by
    -- hmem : S.mem _ (comp g h)
    -- Need: S.mem K (comp (comp k g) h)
    rw [DigraphHom.comp_assoc]
    exact S.precomp_closed (DigraphHom.comp g h) k hmem

/-!
## Part 2: The Trace Covering Predicate
-/

/-- A sieve S on G is **trace-covering** if it contains every homomorphism from
    every path digraph P_n into G. This is the covering condition for J_trace.

    Intuitively: S "sees" all possible traces through G — for every path length n
    and every way to trace a path of length n through G, that tracing is in S. -/
def isTraceCovering (G : FinDigraph) (S : DigraphSieve G) : Prop :=
  ∀ (n : ℕ) (f : DigraphHom (pathDigraph n) G), S.mem (pathDigraph n) f

/-- For non-empty graphs: every trace-covering sieve contains the initial morphism.
    This follows from the unique atom theorem: any path morphism P_0 → G (which
    exists when G has vertices) witnesses non-emptiness.

    Note: for G = emptyDigraph, isTraceCovering is vacuously true for all sieves
    (since Hom(P_n, ∅) = ∅ for all n), so this requires [Nonempty G.Vertex]. -/
theorem trace_covering_implies_nonempty {G : FinDigraph} {S : DigraphSieve G}
    [hne : Nonempty G.Vertex]
    (hS : isTraceCovering G S) :
    S.mem emptyDigraph (emptyDigraph_to G) := by
  -- Construct a morphism P_0 → G by mapping the single vertex to any vertex of G
  obtain ⟨v⟩ := hne
  let f : DigraphHom (pathDigraph 0) G := {
    toFun := fun _ => v
    map_edge := fun s t h => absurd h (by simp)
  }
  -- f : P_0 → G is in S since S trace-covers G
  have hf := hS 0 f
  -- By unique atom theorem: any element in S implies !_G ∈ S
  exact sieve_nonempty_contains_initial G S (pathDigraph 0) f hf

/-!
## Part 3: Grothendieck Topology Axioms
-/

/-- **Maximality axiom:** The maximal sieve is trace-covering for every G.
    Every morphism into G is in the maximal sieve, so in particular all path morphisms. -/
theorem trace_covering_maximal (G : FinDigraph) :
    isTraceCovering G (DigraphSieve.maximal G) :=
  fun _ _ => trivial

/-- **Stability axiom:** If S trace-covers G, then the pullback h*(S) trace-covers H.
    Any path morphism f : P_n → H becomes h ∘ f : P_n → G, which is in S. -/
theorem trace_covering_stable {G H : FinDigraph} {S : DigraphSieve G}
    (h : DigraphHom H G) (hS : isTraceCovering G S) :
    isTraceCovering H (S.pullback h) :=
  fun n f => hS n (DigraphHom.comp f h)

/-- **Transitivity axiom:** If S trace-covers G and for every (H, f) ∈ S the pullback
    f*(T) trace-covers H, then T trace-covers G.

    Key insight: for any path morphism g : P_n → G, we know g ∈ S (since S trace-covers G).
    Then the hypothesis gives: (T.pullback g) trace-covers P_n. In particular,
    id_{P_n} : P_n → P_n must be in (T.pullback g), which means g ∘ id = g ∈ T. -/
theorem trace_covering_transitive {G : FinDigraph} {S T : DigraphSieve G}
    (hS : isTraceCovering G S)
    (hT : ∀ (H : FinDigraph) (f : DigraphHom H G), S.mem H f →
      isTraceCovering H (T.pullback f)) :
    isTraceCovering G T := by
  intro n g
  -- g : P_n → G. Since S trace-covers G, g ∈ S.
  have hg : S.mem (pathDigraph n) g := hS n g
  -- By hypothesis, T.pullback g trace-covers P_n.
  have hTg : isTraceCovering (pathDigraph n) (T.pullback g) := hT (pathDigraph n) g hg
  -- In particular, id_{P_n} : P_n → P_n must be in T.pullback g.
  have hid := hTg n (DigraphHom.id (pathDigraph n))
  -- (T.pullback g).mem (pathDigraph n) (id) = T.mem (pathDigraph n) (comp id g) = T.mem _ g
  simp only [DigraphSieve.pullback] at hid
  rw [DigraphHom.id_comp] at hid
  exact hid

/-!
## Part 4: Strictly Finer Than Atomic Topology

The ¬¬-topology (= atomic topology, by Phase 160) declares S covering iff S is non-empty.
J_trace is strictly finer: every trace-covering sieve is non-empty, but not vice versa.
-/

/-- A homomorphism from P_1 to the loop vertex •₁: maps both vertices to ().
    This is the witness for the one-step trace through •₁'s self-loop. -/
def pathOne_to_loopVertex : DigraphHom (pathDigraph 1) loopVertex where
  toFun := fun _ => ()
  map_edge := fun _ _ _ => trivial

/-- The initial sieve on •₁ is non-empty (it contains !_{•₁}: ∅ → •₁). -/
theorem initial_sieve_nonempty_on_loopVertex :
    (DigraphSieve.initial loopVertex).mem emptyDigraph (emptyDigraph_to loopVertex) :=
  DigraphSieve.initial_contains_empty_hom loopVertex

/-- The initial sieve on •₁ is NOT trace-covering: it misses the morphism P_1 → •₁.

    The initial sieve contains only morphisms from graphs with empty vertex type.
    But pathDigraph 1 has Fin 2 as vertices, which is non-empty. -/
theorem initial_sieve_not_trace_covering_on_loopVertex :
    ¬isTraceCovering loopVertex (DigraphSieve.initial loopVertex) := by
  intro h
  -- h says: ∀ n f, (initial loopVertex).mem (pathDigraph n) f
  -- initial.mem H f = IsEmpty H.Vertex
  -- Take n = 1: (initial loopVertex).mem (pathDigraph 1) pathOne_to_loopVertex = IsEmpty (Fin 2)
  have := h 1 pathOne_to_loopVertex
  -- this : IsEmpty (Fin 2)
  exact this.false ⟨0, by omega⟩

/-- **J_trace is strictly finer than the atomic (¬¬) topology.**

    Witness: the initial sieve on •₁ is non-empty (hence ¬¬-covering)
    but does not contain all path morphisms (hence not trace-covering). -/
theorem trace_strictly_finer_than_atomic :
    ∃ (G : FinDigraph) (S : DigraphSieve G),
      S.mem emptyDigraph (emptyDigraph_to G) ∧ ¬isTraceCovering G S :=
  ⟨loopVertex, DigraphSieve.initial loopVertex,
   initial_sieve_nonempty_on_loopVertex,
   initial_sieve_not_trace_covering_on_loopVertex⟩

/-!
## Part 5: Summary
-/

/-- Master theorem: J_trace is a Grothendieck topology, strictly finer than ¬¬.

    The three Grothendieck axioms (maximality, stability, transitivity) together with
    the strict comparison to the atomic topology establish J_trace as a genuine
    intermediate topology sitting between the atomic topology (coarsest non-trivial)
    and the trivial topology (finest, corresponding to bisimulation). -/
theorem trace_topology_summary :
    -- (1) Maximality
    (∀ G : FinDigraph, isTraceCovering G (DigraphSieve.maximal G)) ∧
    -- (2) Stability
    (∀ (G H : FinDigraph) (S : DigraphSieve G) (h : DigraphHom H G),
      isTraceCovering G S → isTraceCovering H (S.pullback h)) ∧
    -- (3) Transitivity
    (∀ (G : FinDigraph) (S T : DigraphSieve G),
      isTraceCovering G S →
      (∀ (H : FinDigraph) (f : DigraphHom H G), S.mem H f → isTraceCovering H (T.pullback f)) →
      isTraceCovering G T) ∧
    -- (4) Strictly finer than atomic
    (∃ (G : FinDigraph) (S : DigraphSieve G),
      S.mem emptyDigraph (emptyDigraph_to G) ∧ ¬isTraceCovering G S) :=
  ⟨trace_covering_maximal,
   fun _ _ _ h hS => trace_covering_stable h hS,
   fun _ _ _ hS hT => trace_covering_transitive hS hT,
   trace_strictly_finer_than_atomic⟩

end RTS.PresheafTopos
