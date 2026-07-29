/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Simulation Topology: The Three-Point Chain J_bisim < J_sim < J_trace

This file defines the simulation Grothendieck topology J_sim on the category of
finite L-labeled transition systems, strictly between J_bisim and J_trace. It includes:
- Forward simulation definition and mutual simulation equivalence
- Bisimulation implies simulation; simulation implies trace inclusion
- Tree-hom / simulation correspondence
- Simulation composition and transitivity
- Concrete van Glabbeek proofs: B simulates A, A does NOT simulate B
- Mutual simulation of B and C, non-bisimilarity of B and C
- Naive sim-covering and stability failure counterexample
- Simulation topology axioms (opaque) with Grothendieck properties
- Three-point strict chain: J_bisim < J_sim < J_trace

## Axiom Census

**Total axioms in this file: 9**

- 1 tree-hom axiom: `sim_implies_hom_for_trees`
- 1 covering predicate: `isLabeledSimCovering`
- 3 Grothendieck axioms: maximality, stability, transitivity
- 2 refinement axioms: bisim => sim, sim => trace
- 2 separation axioms: J_sim != J_trace, J_bisim != J_sim

**Status: Open Problem (a) in paper Section 8**

The naive observation-class approach (require every tree probe to have some sim in S)
provably fails Grothendieck stability -- this is demonstrated by the counterexample
`naive_sim_covering_not_stable` proved in this file. Simulation is asymmetric, so
pullback along a non-simulation morphism does not preserve the sim-covering property.

Caramello's quotient-theory duality guarantees that J_sim exists as a Grothendieck
topology (the geometric sequents encoding positive HML generate a topology by the
standard saturation construction), but does not yield an explicit covering predicate.
The generation formulas of Caramello-Lafforgue (2025) and Reggio's Bousfield-localization
characterization are the natural paths forward. Mathlib provides `Coverage.toGrothendieck`
(saturation of a coverage to a Grothendieck topology) and `ObjectProperty.isLocal`
(Bousfield localization infrastructure), but bridging these to the concrete LTS setting
requires substantial new development.

## Key Results

- `LabeledSimulation`: forward-only zig-zag for each label
- `labeledSimulates`: existence of forward simulation relating roots
- `labeledMutualSim`: mutual simulation equivalence
- `bisim_implies_sim`: bisimulation implies simulation
- `sim_implies_traceInclusion`: simulation implies trace inclusion
- `hom_implies_sim`: tree hom implies simulation
- `sim_compose`: simulations compose
- `vgPairB_simulates_vgPairA`: B simulates A (concrete)
- `vgPairA_not_simulates_vgPairB`: A does NOT simulate B (concrete)
- `vgPairBC_mutual_sim`: B and C are mutually similar
- `vgPairB_not_bisim_vgPairC`: B and C are NOT bisimilar
- `naive_sim_covering_not_stable`: stability failure for naive sim-covering (proven)
- `isLabeledSimCovering`: axiomatized covering predicate for J_sim
- `sim_topology_three_point_chain`: J_bisim < J_sim < J_trace

## Mathematical Significance

This completes the three-point chain in the labeled van Glabbeek spectrum:
  J_bisim  <  J_sim  <  J_trace
The simulation topology J_sim is the novel intermediate point. It separates:
- vgPairA and vgPairB (trace-equiv but NOT mutual-sim-equiv) -> J_sim != J_trace
- vgPairB and vgPairC (mutual-sim-equiv but NOT bisimilar) -> J_sim != J_bisim

The naive sim-covering definition (require every tree probe to have some sim in S)
fails stability because simulation is asymmetric. The correct J_sim requires
Caramello's machinery and is axiomatized here.

## References

- van Glabbeek, "The linear time--branching time spectrum I" (1990)
- Joyal-Nielsen-Winskel, "Bisimulation from open maps" (1996)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), III.2
- Caramello, "Theories, Sites, Toposes" (2017), Ch. 3
- Caramello-Lafforgue, "Generation formulas for Grothendieck topologies" (2025)
- Reggio, "Quantifiers and Duality" (2018), Ch. 4 (Bousfield localization)
-/

import RuleSys.PresheafTopos.LabeledBisimTopology

set_option autoImplicit false

namespace RTS.PresheafTopos

/-!
## Part 1: Labeled Simulation Definition
-/

/-- Forward-only simulation: if R s t and G.edge a s s', then ∃ t', H.edge a t t' ∧ R s' t'.
    Unlike bisimulation, there is no backward condition. H can "match" every move of G,
    but not vice versa. -/
def LabeledSimulation {L : Type} [Fintype L] [DecidableEq L]
    (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop) : Prop :=
  ∀ s t, R s t → ∀ (a : L) s', G.edge a s s' → ∃ t', H.edge a t t' ∧ R s' t'

/-- Decidability of LabeledSimulation when R is decidable. -/
instance instDecidableLabeledSimulation {L : Type} [Fintype L] [DecidableEq L]
    (G H : FinLTS L) (R : G.Vertex → H.Vertex → Prop) [DecidableRel R] :
    Decidable (LabeledSimulation G H R) :=
  Fintype.decidableForallFintype

/-- H simulates G from (v, w): there exists a relation R with R v w that is a forward
    simulation from G to H. Equivalently, every move of G from v can be matched by H from w. -/
def labeledSimulates {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (H : FinLTS L) (w : H.Vertex) : Prop :=
  ∃ R : G.Vertex → H.Vertex → Prop, R v w ∧ LabeledSimulation G H R

/-- Mutual simulation: G simulates H AND H simulates G.
    Strictly weaker than bisimulation (the same relation need not witness both directions). -/
def labeledMutualSim {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (v : G.Vertex) (H : FinLTS L) (w : H.Vertex) : Prop :=
  labeledSimulates G v H w ∧ labeledSimulates H w G v

/-!
## Part 2: Bisimulation Implies Simulation
-/

/-- The forward half of a bisimulation is a simulation. -/
theorem bisim_implies_sim {L : Type} [Fintype L] [DecidableEq L]
    {G H : FinLTS L} {R : G.Vertex → H.Vertex → Prop}
    (hR : LabeledBisimulation G H R) : LabeledSimulation G H R :=
  hR.1

/-- Bisimulation equivalence implies mutual simulation: extract forward halves from
    the bisimulation and its flip. -/
theorem bisimEquiv_implies_mutualSim {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v : G.Vertex} {H : FinLTS L} {w : H.Vertex}
    (h : labeledBisimEquiv G v H w) : labeledMutualSim G v H w := by
  obtain ⟨R, hRvw, hfwd, hbwd⟩ := h
  constructor
  · -- G simulates via R (forward direction of bisim)
    exact ⟨R, hRvw, hfwd⟩
  · -- H simulates via flip(R) (backward direction of bisim)
    exact ⟨fun h g => R g h, hRvw, fun s t hRts a s' hs' =>
      hbwd t s hRts a s' hs'⟩

/-!
## Part 3: Simulation Implies Trace Inclusion
-/

/-- If H simulates G from (v, w), then every trace of G at v is also a trace of H at w.
    Proof by induction on hasTrace: the simulation relation provides matching transitions
    at each step. -/
theorem sim_implies_traceInclusion {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v : G.Vertex} {H : FinLTS L} {w : H.Vertex}
    (hsim : labeledSimulates G v H w) :
    ∀ t, hasTrace G v t → hasTrace H w t := by
  obtain ⟨R, hRvw, hfwd⟩ := hsim
  -- Prove a stronger statement: if R s₁ s₂ and hasTrace G s₁ tr, then hasTrace H s₂ tr
  suffices h : ∀ (s₁ : G.Vertex) (tr : List L),
      hasTrace G s₁ tr → ∀ (s₂ : H.Vertex), R s₁ s₂ → hasTrace H s₂ tr by
    exact fun tr htr => h v tr htr w hRvw
  intro s₁ tr htr
  induction htr with
  | nil _ => intro s₂ _; exact hasTrace.nil s₂
  | cons l rest edge_ss' _ ih =>
    intro s₂ hRst
    obtain ⟨t', ht'_edge, hR_s't'⟩ := hfwd _ s₂ hRst l _ edge_ss'
    exact hasTrace.cons l rest ht'_edge (ih t' hR_s't')

/-- Mutual simulation implies trace equivalence: combine both inclusions. -/
theorem mutualSim_implies_traceEquiv {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v : G.Vertex} {H : FinLTS L} {w : H.Vertex}
    (h : labeledMutualSim G v H w) :
    labeledTraceEquiv G v H w := by
  ext t
  simp only [labeledTraceSet, Set.mem_setOf_eq]
  exact ⟨sim_implies_traceInclusion h.1 t, sim_implies_traceInclusion h.2 t⟩

/-!
## Part 4: Tree Hom ↔ Simulation
-/

/-- Any LTS homomorphism f : T → G gives a simulation of T by G.
    The relation R(s, t) := f(s) = t is a forward simulation: if T.edge a s s',
    then G.edge a (f s) (f s') by edge preservation, and R(s', f s'). -/
theorem hom_implies_sim {L : Type} [Fintype L] [DecidableEq L]
    {T G : FinLTS L} (f : LTSHom T G) (root : T.Vertex) :
    labeledSimulates T root G (f.toFun root) := by
  refine ⟨fun s t => f.toFun s = t, rfl, ?_⟩
  intro s t hRst a s' hedge
  rw [← hRst]
  exact ⟨f.toFun s', f.map_edge a s s' hedge, rfl⟩

/-- If T is a rooted tree and G simulates T from (root, v), then there exists a
    homomorphism T → G mapping root to v. This is the converse of `hom_implies_sim`,
    restricted to trees -- the tree structure provides the unique-path property needed
    to extract a function from the simulation relation via induction on tree depth.

    **Why axiomatized**: The proof requires König's lemma (or equivalent choice principle)
    to select witnessing successors at each branching node, plus induction on the
    well-founded tree structure. Open Problem (a) in the paper -- explicit J_sim
    covering predicate. This axiom is a prerequisite for the sim-covering predicate,
    not itself part of the Grothendieck topology axioms.

    **Classification**: `Axiomatized: tree-induction + choice -- standard but not yet formalized` -/
axiom sim_implies_hom_for_trees {L : Type} [Fintype L] [DecidableEq L]
    {T : FinLTS L} {root : T.Vertex} {G : FinLTS L} {v : G.Vertex}
    (hTree : LabeledIsRootedTree T)
    (hsim : labeledSimulates T root G v) :
    ∃ f : LTSHom T G, f.toFun root = v

/-!
## Part 5: Simulation Composition
-/

/-- Simulations compose: if R₁ is a simulation from T to G and R₂ is a simulation
    from G to H, then the relational composition is a simulation from T to H. -/
theorem sim_compose {L : Type} [Fintype L] [DecidableEq L]
    {T G H : FinLTS L}
    {R₁ : T.Vertex → G.Vertex → Prop} {R₂ : G.Vertex → H.Vertex → Prop}
    (h₁ : LabeledSimulation T G R₁) (h₂ : LabeledSimulation G H R₂) :
    LabeledSimulation T H (fun t h => ∃ g, R₁ t g ∧ R₂ g h) := by
  intro s t ⟨g, hR₁sg, hR₂gt⟩ a s' hedge
  obtain ⟨g', hg'_edge, hR₁s'g'⟩ := h₁ s g hR₁sg a s' hedge
  obtain ⟨t', ht'_edge, hR₂g't'⟩ := h₂ g t hR₂gt a g' hg'_edge
  exact ⟨t', ht'_edge, g', hR₁s'g', hR₂g't'⟩

/-- Simulation transitivity: if G simulates T and H simulates G, then H simulates T. -/
theorem labeledSimulates_trans {L : Type} [Fintype L] [DecidableEq L]
    {T : FinLTS L} {r : T.Vertex} {G : FinLTS L} {v : G.Vertex}
    {H : FinLTS L} {w : H.Vertex}
    (h₁ : labeledSimulates T r G v) (h₂ : labeledSimulates G v H w) :
    labeledSimulates T r H w := by
  obtain ⟨R₁, hR₁, hSim₁⟩ := h₁
  obtain ⟨R₂, hR₂, hSim₂⟩ := h₂
  exact ⟨fun t h => ∃ g, R₁ t g ∧ R₂ g h,
         ⟨v, hR₁, hR₂⟩,
         sim_compose hSim₁ hSim₂⟩

/-!
## Part 6: Simulation Separation Theorem

Mutual simulation equivalence is characterized by having the same tree-hom sets
(up to root-preservation). This bridges the algebraic (simulation) and categorical
(hom-set) perspectives.
-/

/-- If G and H are mutually similar, then for any rooted tree T, T has a root-preserving
    hom to G iff it has one to H.

    Proof: Given f : T → G root-preserving, hom_implies_sim gives G simulates T.
    Mutual sim gives H simulates G. By transitivity H simulates T.
    By sim_implies_hom_for_trees, ∃ g : T → H root-preserving. -/
theorem labeled_sim_separation {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {v : G.Vertex} {H : FinLTS L} {w : H.Vertex}
    (hms : labeledMutualSim G v H w) :
    ∀ (T : FinLTS L) (root : T.Vertex), LabeledIsRootedTree T →
      ((∃ f : LTSHom T G, f.toFun root = v) ↔ (∃ f : LTSHom T H, f.toFun root = w)) := by
  intro T root hTree
  constructor
  · -- G side → H side
    intro ⟨f, hf⟩
    -- f : T → G root-preserving gives: G simulates T
    have hGsimT : labeledSimulates T root G v := hf ▸ hom_implies_sim f root
    -- mutual sim: H simulates G
    have hHsimG : labeledSimulates G v H w := hms.1
    -- transitivity: H simulates T
    have hHsimT : labeledSimulates T root H w := labeledSimulates_trans hGsimT hHsimG
    -- tree + simulation → hom
    exact sim_implies_hom_for_trees hTree hHsimT
  · -- H side → G side
    intro ⟨f, hf⟩
    have hHsimT : labeledSimulates T root H w := hf ▸ hom_implies_sim f root
    have hGsimH : labeledSimulates H w G v := hms.2
    have hGsimT : labeledSimulates T root G v := labeledSimulates_trans hHsimT hGsimH
    exact sim_implies_hom_for_trees hTree hGsimT

/-!
## Part 7: vgPairB Simulates vgPairA (Concrete Proof)

Simulation R_BA relates:
  (0_A, 0_B), (1_A, 1_B), (2_A, 1_B), (3_A, 2_B), (4_A, 2_B)

Both a-successors of A map to B's single a-successor (which can do both b and c).
Dead states map to B's dead state.
-/

/-- Helper: a-successors of vertex 0 in vgPairA are exactly vertices 1 and 2. -/
private theorem vgPairA_a_successors (s : vgPairA.Vertex)
    (h : vgPairA.edge ThreeLabel.a ⟨0, by omega⟩ s) :
    s = ⟨1, by omega⟩ ∨ s = ⟨2, by omega⟩ := by
  revert s; native_decide

/-- The simulation relation from vgPairA to vgPairB. -/
private def sim_BA (s : vgPairA.Vertex) (t : vgPairB.Vertex) : Prop :=
  (s.val = 0 ∧ t.val = 0) ∨
  (s.val = 1 ∧ t.val = 1) ∨
  (s.val = 2 ∧ t.val = 1) ∨
  (s.val = 3 ∧ t.val = 2) ∨
  (s.val = 4 ∧ t.val = 2)

private instance : DecidableRel sim_BA := by
  intro s t; unfold sim_BA; exact inferInstance

/-- sim_BA is a forward simulation from vgPairA to vgPairB. -/
private theorem sim_BA_is_simulation : LabeledSimulation vgPairA vgPairB sim_BA := by
  native_decide

/-- vgPairB simulates vgPairA: the relation sim_BA is a forward simulation.

    Key: A's two a-successors (s1 for b, s2 for c) both map to B's single a-successor
    s1 (which can do both b and c). -/
theorem vgPairB_simulates_vgPairA :
    labeledSimulates vgPairA (⟨0, by omega⟩ : vgPairA.Vertex)
                     vgPairB (⟨0, by omega⟩ : vgPairB.Vertex) :=
  ⟨sim_BA, Or.inl ⟨rfl, rfl⟩, sim_BA_is_simulation⟩

/-!
## Part 8: vgPairA Does NOT Simulate vgPairB (Concrete Proof)

Key: B's vertex 1 can do both b and c. If R(1_B, s') and s' is an a-successor of 0 in A,
then s' ∈ {1, 2}. But vertex 1 has no c-edge and vertex 2 has no b-edge. Contradiction.
-/

/-- Helper: in vgPairA, no c-edge from vertex 1. -/
private theorem vgPairA_no_c_from_1' (w : vgPairA.Vertex) :
    ¬vgPairA.edge ThreeLabel.c ⟨1, by omega⟩ w := by
  revert w; native_decide

/-- Helper: in vgPairA, no b-edge from vertex 2. -/
private theorem vgPairA_no_b_from_2' (w : vgPairA.Vertex) :
    ¬vgPairA.edge ThreeLabel.b ⟨2, by omega⟩ w := by
  revert w; native_decide

/-- vgPairA does NOT simulate vgPairB.

    Proof: Assume R with R(0_B, 0_A) and simulation. B.edge a 0 1, so ∃ s' with
    A.edge a 0 s' ∧ R(1_B, s'). But s' ∈ {1, 2} (a-successors of 0 in A).
    Case s' = 1: B.edge c 1 2 requires A.edge c 1 ? — impossible (no c-edge from 1).
    Case s' = 2: B.edge b 1 2 requires A.edge b 2 ? — impossible (no b-edge from 2). -/
theorem vgPairA_not_simulates_vgPairB :
    ¬labeledSimulates vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                      vgPairA (⟨0, by omega⟩ : vgPairA.Vertex) := by
  intro ⟨R, hR0, hSim⟩
  -- B has a-edge from 0 to 1
  have hB_a : vgPairB.edge ThreeLabel.a ⟨0, by omega⟩ ⟨1, by omega⟩ := by native_decide
  -- Forward simulation: R(0_B, 0_A) and B.edge a 0 1 → ∃ s', A.edge a 0 s' ∧ R(1, s')
  obtain ⟨s', hs'_edge, hR_1s'⟩ := hSim _ _ hR0 ThreeLabel.a _ hB_a
  -- s' must be 1 or 2 in A
  rcases vgPairA_a_successors s' hs'_edge with rfl | rfl
  · -- s' = 1: B.edge c 1 2, need A.edge c 1 ?, but no c-edge from 1
    have hB_c : vgPairB.edge ThreeLabel.c ⟨1, by omega⟩ ⟨2, by omega⟩ := by native_decide
    obtain ⟨s'', hs''_edge, _⟩ := hSim _ _ hR_1s' ThreeLabel.c _ hB_c
    exact vgPairA_no_c_from_1' s'' hs''_edge
  · -- s' = 2: B.edge b 1 2, need A.edge b 2 ?, but no b-edge from 2
    have hB_b : vgPairB.edge ThreeLabel.b ⟨1, by omega⟩ ⟨2, by omega⟩ := by native_decide
    obtain ⟨s'', hs''_edge, _⟩ := hSim _ _ hR_1s' ThreeLabel.b _ hB_b
    exact vgPairA_no_b_from_2' s'' hs''_edge

/-- vgPairA and vgPairB are NOT mutually similar: A does not simulate B. -/
theorem vgPairA_vgPairB_not_mutual_sim :
    ¬labeledMutualSim vgPairA (⟨0, by omega⟩ : vgPairA.Vertex)
                      vgPairB (⟨0, by omega⟩ : vgPairB.Vertex) := by
  intro ⟨_, hsim_back⟩
  exact vgPairA_not_simulates_vgPairB hsim_back

/-!
## Part 9: vgPairB and vgPairC Mutual Simulation

vgPairC = a.b + a.c + a.(b+c), with Fin 7 vertices.
B's s1 (can do b+c) maps to C's s3 (also can do b+c) for C-simulates-B.
All C's a-successors map to B's s1 (can do b+c) for B-simulates-C.
-/

/-- Simulation relation: C simulates B. Maps B's branching vertex to C's branching vertex. -/
private def sim_CB (s : vgPairB.Vertex) (t : vgPairC.Vertex) : Prop :=
  (s.val = 0 ∧ t.val = 0) ∨
  (s.val = 1 ∧ t.val = 3) ∨
  (s.val = 2 ∧ t.val = 6)

private instance : DecidableRel sim_CB := by
  intro s t; unfold sim_CB; exact inferInstance

/-- sim_CB is a forward simulation from vgPairB to vgPairC. -/
private theorem sim_CB_is_simulation : LabeledSimulation vgPairB vgPairC sim_CB := by
  native_decide

/-- vgPairC simulates vgPairB: sim_CB is a forward simulation. -/
theorem vgPairC_simulates_vgPairB :
    labeledSimulates vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                     vgPairC (⟨0, by omega⟩ : vgPairC.Vertex) :=
  ⟨sim_CB, Or.inl ⟨rfl, rfl⟩, sim_CB_is_simulation⟩

/-- Simulation relation: B simulates C. All C's a-successors map to B's branching vertex. -/
private def sim_BC (s : vgPairC.Vertex) (t : vgPairB.Vertex) : Prop :=
  (s.val = 0 ∧ t.val = 0) ∨
  (s.val = 1 ∧ t.val = 1) ∨
  (s.val = 2 ∧ t.val = 1) ∨
  (s.val = 3 ∧ t.val = 1) ∨
  (s.val = 4 ∧ t.val = 2) ∨
  (s.val = 5 ∧ t.val = 2) ∨
  (s.val = 6 ∧ t.val = 2)

private instance : DecidableRel sim_BC := by
  intro s t; unfold sim_BC; exact inferInstance

/-- sim_BC is a forward simulation from vgPairC to vgPairB. -/
private theorem sim_BC_is_simulation : LabeledSimulation vgPairC vgPairB sim_BC := by
  native_decide

/-- vgPairB simulates vgPairC: sim_BC is a forward simulation.
    All of C's a-successors map to B's single a-successor s1 (which can do both b and c). -/
theorem vgPairB_simulates_vgPairC :
    labeledSimulates vgPairC (⟨0, by omega⟩ : vgPairC.Vertex)
                     vgPairB (⟨0, by omega⟩ : vgPairB.Vertex) :=
  ⟨sim_BC, Or.inl ⟨rfl, rfl⟩, sim_BC_is_simulation⟩

/-- vgPairB and vgPairC are mutually similar. -/
theorem vgPairBC_mutual_sim :
    labeledMutualSim vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                     vgPairC (⟨0, by omega⟩ : vgPairC.Vertex) :=
  ⟨vgPairC_simulates_vgPairB, vgPairB_simulates_vgPairC⟩

/-!
## Part 10: vgPairB and vgPairC Are NOT Bisimilar

Key: any bisimulation R with R(0_B, 0_C) must have R(1_B, 1_C) by the backward
condition (C.edge a 0 1, B's only a-successor is 1). But then forward from R(1_B, 1_C):
B.edge c 1 2 requires C.edge c 1 ?, but C vertex 1 has no c-edge. Contradiction.
-/

/-- Helper: in vgPairC, no c-edge from vertex 1. -/
private theorem vgPairC_no_c_from_1 (w : vgPairC.Vertex) :
    ¬vgPairC.edge ThreeLabel.c ⟨1, by omega⟩ w := by
  revert w; native_decide

/-- Helper: in vgPairB, the only a-successor of vertex 0 is vertex 1.
    (Local copy of private vgPairB_a_unique from LabeledBisimTopology.) -/
private theorem vgPairB_a_unique' (t : vgPairB.Vertex)
    (h : vgPairB.edge ThreeLabel.a ⟨0, by omega⟩ t) : t = ⟨1, by omega⟩ := by
  revert t; native_decide

/-- vgPairB and vgPairC are NOT bisimilar.

    Proof: Assume bisimulation R with R(0_B, 0_C).
    Backward from R(0_B, 0_C): C.edge a 0 1, so ∃ s', B.edge a 0 s' ∧ R(s', 1_C).
    B's only a-successor of 0 is 1. So R(1_B, 1_C).
    Forward from R(1_B, 1_C): B.edge c 1 2, so ∃ t', C.edge c 1_C t' ∧ R(2_B, t').
    But C vertex 1 has no c-edge. Contradiction. -/
theorem vgPairB_not_bisim_vgPairC :
    ¬labeledBisimEquiv vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                        vgPairC (⟨0, by omega⟩ : vgPairC.Vertex) := by
  intro ⟨R, hR_root, hfwd, hbwd⟩
  -- C.edge a 0 1
  have hC_a01 : vgPairC.edge ThreeLabel.a ⟨0, by omega⟩ ⟨1, by omega⟩ := by native_decide
  -- Backward: R(0_B, 0_C) and C.edge a 0 1 → ∃ s', B.edge a 0 s' ∧ R(s', 1_C)
  obtain ⟨s', hs'_edge, hR_s'1⟩ := hbwd _ _ hR_root ThreeLabel.a _ hC_a01
  -- s' must be 1 (unique a-successor of 0 in B)
  have hs'_eq := vgPairB_a_unique' s' hs'_edge
  rw [hs'_eq] at hR_s'1
  -- B.edge c 1 2
  have hB_c12 : vgPairB.edge ThreeLabel.c ⟨1, by omega⟩ ⟨2, by omega⟩ := by native_decide
  -- Forward: R(1_B, 1_C) and B.edge c 1 2 → ∃ t', C.edge c 1 t'
  obtain ⟨t', ht'_edge, _⟩ := hfwd _ _ hR_s'1 ThreeLabel.c _ hB_c12
  -- C vertex 1 has no c-edge
  exact vgPairC_no_c_from_1 t' ht'_edge

/-!
## Part 11: Naive Sim-Covering and Stability Failure

The naive approach to a simulation topology — requiring every tree probe to have
some simulation in S — fails stability because simulation is asymmetric.
-/

/-- A sieve S on G is naively sim-covering if: for every rooted tree T, whenever
    Hom(T, G) is nonempty, S ∩ Hom(T, G) is nonempty.
    This is weaker than bisim-covering (which requires ALL homs to be in S). -/
def isSimCoveringNaive {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (S : LTSSieve G) : Prop :=
  ∀ (T : FinLTS L), LabeledIsRootedTree T →
    Nonempty (LTSHom T G) → ∃ (g : LTSHom T G), S.mem T g

/-- The right-branch homomorphism: traceLTS [a] → fanLTS [a, a] mapping vertex 1 to
    the RIGHT child (vertex 2). -/
private def fRight : LTSHom (traceLTS [ThreeLabel.a]) (fanLTS [ThreeLabel.a, ThreeLabel.a]) where
  toFun v := if v.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_edge := by
    intro lbl s t hedge
    obtain ⟨hs_lt, hlabel, hj⟩ := hedge
    have hs0 : s.val = 0 := by
      have : s.val < [ThreeLabel.a].length := hs_lt; simp at this; omega
    have ht1 : t.val = 1 := by omega
    simp only [hs0, ↓reduceIte, ht1]
    have ha : lbl = ThreeLabel.a := by
      have h1 : ([ThreeLabel.a] : List ThreeLabel).get ⟨s.val, hs_lt⟩ = lbl := hlabel
      simp [hs0] at h1; exact h1.symm
    subst ha
    exact ⟨by trivial, ⟨⟨1, by decide⟩, by decide, by decide⟩⟩

/-- The sieve on fanLTS [a, a] generated by fRight: a morphism g : K → fanLTS [a,a]
    is in S iff g = comp(k, fRight) for some k : K → traceLTS [a]. -/
private def rightSieve : LTSSieve (fanLTS [ThreeLabel.a, ThreeLabel.a]) where
  mem := fun K g => ∃ k : LTSHom K (traceLTS [ThreeLabel.a]),
    g = LTSHom.comp k fRight
  precomp_closed := fun {_H K} g h ⟨k, heq⟩ => by
    exact ⟨LTSHom.comp h k, by rw [heq, LTSHom.comp_assoc]⟩

/-- Helper: given any hom f from a tree to fanLTS [a,a], construct k : tree → traceLTS [a]
    by mapping root to 0 and non-root to 1.

    The key insight: fanLTS [a,a] has only a-labeled edges, all from vertex 0 to {1, 2},
    so any tree mapping to it has depth <= 1 and only a-edges. -/
private def constructK {T : FinLTS ThreeLabel}
    (f : LTSHom T (fanLTS [ThreeLabel.a, ThreeLabel.a])) :
    LTSHom T (traceLTS [ThreeLabel.a]) where
  toFun v := if (f.toFun v).val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  map_edge := by
    intro lbl s t hedge
    have hfedge := f.map_edge lbl s t hedge
    obtain ⟨hfs0, ⟨i, hft, ha⟩⟩ := hfedge
    simp only [hfs0, ↓reduceIte]
    have hft_ne : ¬(f.toFun t).val = 0 := by omega
    simp only [hft_ne, ↓reduceIte]
    -- traceLTS [a].edge lbl 0 1: need 0 < 1 ∧ [a].get ⟨0, _⟩ = lbl ∧ 1 = 0 + 1
    -- lbl = [ThreeLabel.a, ThreeLabel.a].get i = ThreeLabel.a (both entries are a)
    have hall : ∀ j : Fin [ThreeLabel.a, ThreeLabel.a].length,
        [ThreeLabel.a, ThreeLabel.a].get j = ThreeLabel.a := by decide
    have ha_eq : lbl = ThreeLabel.a := by rw [ha]; exact hall i
    subst ha_eq
    exact ⟨by decide, by trivial, by trivial⟩

/-- rightSieve is naively sim-covering on fanLTS [a, a].

    For any rooted tree T with hom f : T → fanLTS [a,a], we construct k : T → traceLTS [a]
    (mapping root to 0, non-root to 1) and show comp(k, fRight) is a valid hom in S. -/
theorem rightSieve_naive_sim_covering :
    isSimCoveringNaive (fanLTS [ThreeLabel.a, ThreeLabel.a]) rightSieve := by
  intro T _hTree ⟨f⟩
  let k := constructK f
  exact ⟨LTSHom.comp k fRight, k, rfl⟩

/-- The left-branch homomorphism: traceLTS [a] → fanLTS [a, a] mapping vertex 1 to
    the LEFT child (vertex 1). -/
private def hLeft : LTSHom (traceLTS [ThreeLabel.a]) (fanLTS [ThreeLabel.a, ThreeLabel.a]) where
  toFun v := if v.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  map_edge := by
    intro lbl s t hedge
    obtain ⟨hs_lt, hlabel, hj⟩ := hedge
    have hs0 : s.val = 0 := by
      have : s.val < [ThreeLabel.a].length := hs_lt; simp at this; omega
    have ht1 : t.val = 1 := by omega
    simp only [hs0, ↓reduceIte, ht1]
    have ha : lbl = ThreeLabel.a := by
      have h1 : ([ThreeLabel.a] : List ThreeLabel).get ⟨s.val, hs_lt⟩ = lbl := hlabel
      simp [hs0] at h1; exact h1.symm
    subst ha
    exact ⟨by trivial, ⟨⟨0, by decide⟩, by decide, by decide⟩⟩

/-- The pullback of rightSieve along hLeft is NOT naively sim-covering on traceLTS [a].

    The identity on traceLTS [a] is a hom (and traceLTS [a] is a tree), but
    comp(g, hLeft) ∈ rightSieve requires comp(g, hLeft) = comp(k, fRight) for some k.
    Evaluating at vertex 1: hLeft maps to {0, 1} while fRight maps to {0, 2}.
    The only common value is 0, but reaching 0 at vertex 1 contradicts edge preservation. -/
theorem rightSieve_pullback_not_naive_sim_covering :
    ¬isSimCoveringNaive (traceLTS [ThreeLabel.a])
      (rightSieve.pullback hLeft) := by
  intro hcov
  have hTree := traceLTS_isLabeledRootedTree [ThreeLabel.a]
  have hne : Nonempty (LTSHom (traceLTS [ThreeLabel.a]) (traceLTS [ThreeLabel.a])) :=
    ⟨LTSHom.id _⟩
  obtain ⟨g, hg⟩ := hcov _ hTree hne
  obtain ⟨k, hk⟩ := hg
  -- Evaluate both sides at vertex 1: hLeft(g(1)) = fRight(k(1))
  have h1lt : (1 : ℕ) < [ThreeLabel.a].length + 1 := by decide
  have heq : (LTSHom.comp g hLeft).toFun ⟨1, h1lt⟩ =
             (LTSHom.comp k fRight).toFun ⟨1, h1lt⟩ := by rw [hk]
  have heq_val : (hLeft.toFun (g.toFun ⟨1, h1lt⟩)).val =
                 (fRight.toFun (k.toFun ⟨1, h1lt⟩)).val :=
    congrArg Fin.val heq
  -- fRight(v).val is 0 when v.val = 0, else 2
  have hfR : ∀ v : (traceLTS [ThreeLabel.a]).Vertex,
      (fRight.toFun v).val = if v.val = 0 then 0 else 2 := by
    intro v; simp [fRight]; split <;> simp_all
  -- hLeft(v).val is 0 when v.val = 0, else 1
  have hhL : ∀ v : (traceLTS [ThreeLabel.a]).Vertex,
      (hLeft.toFun v).val = if v.val = 0 then 0 else 1 := by
    intro v; simp [hLeft]; split <;> simp_all
  rw [hhL, hfR] at heq_val
  have hg1_bound := (g.toFun ⟨1, h1lt⟩).isLt
  have hk1_bound := (k.toFun ⟨1, h1lt⟩).isLt
  -- LHS ∈ {0, 1}, RHS ∈ {0, 2}. Equal only when both = 0, forcing g(1).val = 0.
  have hg1_zero : (g.toFun ⟨1, h1lt⟩).val = 0 := by
    split at heq_val <;> split at heq_val <;> omega
  -- g preserves edge: traceLTS [a] has edge a from 0 to 1
  have hedge : (traceLTS [ThreeLabel.a]).edge ThreeLabel.a
      (⟨0, by decide⟩ : (traceLTS [ThreeLabel.a]).Vertex)
      (⟨1, by decide⟩ : (traceLTS [ThreeLabel.a]).Vertex) := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Fin ([ThreeLabel.a].length + 1)).val < [ThreeLabel.a].length; decide
    · show [ThreeLabel.a].get ⟨(0 : Fin ([ThreeLabel.a].length + 1)).val, _⟩ = ThreeLabel.a; decide
    · show (1 : Fin ([ThreeLabel.a].length + 1)).val = (0 : Fin ([ThreeLabel.a].length + 1)).val + 1
      decide
  have hg_edge := g.map_edge ThreeLabel.a _ _ hedge
  obtain ⟨_, _, hg1_eq⟩ := hg_edge
  omega

/-- **Stability failure**: naive sim-covering is NOT stable under pullback.
    rightSieve naively sim-covers fanLTS [a,a], but its pullback along hLeft does NOT
    naively sim-cover traceLTS [a].

    This is the fundamental obstruction to defining J_sim naively: simulation's asymmetry
    means that "having some hom in S" is not preserved by precomposition. -/
theorem naive_sim_covering_not_stable :
    ∃ (G H : FinLTS ThreeLabel) (h : LTSHom H G) (S : LTSSieve G),
      isSimCoveringNaive G S ∧ ¬isSimCoveringNaive H (S.pullback h) :=
  ⟨fanLTS [ThreeLabel.a, ThreeLabel.a],
   traceLTS [ThreeLabel.a],
   hLeft,
   rightSieve,
   rightSieve_naive_sim_covering,
   rightSieve_pullback_not_naive_sim_covering⟩

/-!
## Part 12: Simulation Topology (Axiomatized)

The correct simulation topology J_sim requires Caramello's machinery for
topologies generated by equivalence-class conditions. We axiomatize its
existence and key properties.

**8 axioms below** (1 predicate + 3 Grothendieck + 2 refinement + 2 separation).
All are guaranteed by Caramello's quotient-theory duality but not given by
explicit covering sieves. See Open Problem (a) in paper Section 8.
-/

/-- The simulation-covering predicate for the topology J_sim.
    A sieve S on G is sim-covering if it satisfies a condition intermediate between
    bisim-covering (all tree homs in S) and trace-covering (all path homs in S).

    The precise definition would use Caramello's framework for topologies generated by
    observation-class equivalences, specifically the geometric sequents encoding positive
    HML (the simulation fragment of Hennessy-Milner logic). It cannot be defined by the
    naive observation-class approach due to the proven stability failure
    (`naive_sim_covering_not_stable` in this file).

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    The naive approach provably fails Grothendieck stability (proven counterexample in this
    file). Caramello's quotient-theory duality guarantees existence but not an explicit
    predicate. Caramello-Lafforgue generation formulas (2025) and Reggio's Bousfield-
    localization characterization are the natural paths forward.

    **Classification**: `Axiomatized: open problem -- J_sim requires Caramello quotient-theory duality` -/
axiom isLabeledSimCovering {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) (S : LTSSieve G) : Prop

/-!
**Reader's warning about `isLabeledSimCovering`.**

The declaration above is an *uninterpreted* predicate: an `axiom` of type `Prop` with
no defining clause and no characterising property. Nothing in this development pins
down which sieves satisfy it.

Every statement below that mentions it, including the maximality, stability and
transitivity axioms and the separation axioms
`sim_covering_separates_trace_sim` and `sim_covering_separates_sim_bisim`,
therefore constrains an unknown predicate rather than a constructed one. They are
mutually consistent, but they carry no mathematical content on their own: any
predicate satisfying the stated constraints would do, and none is exhibited.

This is deliberate and matches the paper, which obtains the simulation topology
through Caramello's quotient-theory duality and records the construction of explicit
covering sieves for it as the central open problem. It is recorded here so that a
reader does not mistake the axioms below for a construction, and so that the
strictness of the three-topology chain is understood to rest on them.

Note also that the separately defined `energyTopology .simulation` is *not* this
predicate; it collapses onto the bisimulation topology, as documented at
`SubtoposLattice.EnergyTestObjects.energyObsClass`.
-/

/-- **Maximality axiom:** The maximal sieve is sim-covering for every G.
    This is the first Grothendieck topology axiom: the maximal sieve (containing all
    morphisms into G) covers G. Follows automatically from any valid Grothendieck topology.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    Once `isLabeledSimCovering` is defined, this axiom follows from any valid Grothendieck
    topology (the maximal sieve trivially satisfies any covering condition).

    **Classification**: `Axiomatized: open problem -- Grothendieck axiom for J_sim` -/
axiom labeled_sim_covering_maximal {L : Type} [Fintype L] [DecidableEq L]
    (G : FinLTS L) :
    isLabeledSimCovering G (LTSSieve.maximal G)

/-- **Stability axiom:** If S sim-covers G, then the pullback h*(S) sim-covers H.
    This is the second Grothendieck topology axiom: covering sieves are closed under
    pullback. This is precisely the axiom that the naive sim-covering definition fails
    (proven by `naive_sim_covering_not_stable` in this file), making it the critical
    constraint that forces axiomatization.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    The naive observation-class candidate fails this axiom because simulation is asymmetric:
    pullback along a non-simulation morphism does not preserve the sim-covering property.
    Any correct explicit definition must satisfy stability by construction.

    **Classification**: `Axiomatized: open problem -- Grothendieck stability for J_sim` -/
axiom labeled_sim_covering_stable {L : Type} [Fintype L] [DecidableEq L]
    {G H : FinLTS L} {S : LTSSieve G}
    (h : LTSHom H G) (hS : isLabeledSimCovering G S) :
    isLabeledSimCovering H (S.pullback h)

/-- **Transitivity axiom:** If S sim-covers G and for every (H, f) in S the pullback
    f*(T) sim-covers H, then T sim-covers G. This is the third Grothendieck topology
    axiom: local character / transitivity of covering sieves. Follows automatically from
    any valid Grothendieck topology.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    Once `isLabeledSimCovering` is defined, this axiom must be verified for the specific
    predicate. For J_trace and J_bisim, transitivity follows from a self-probing argument
    (the test object T_0 is itself a path/tree, so id_{T_0} witnesses membership).

    **Classification**: `Axiomatized: open problem -- Grothendieck transitivity for J_sim` -/
axiom labeled_sim_covering_transitive {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {S T : LTSSieve G}
    (hS : isLabeledSimCovering G S)
    (hT : ∀ (H : FinLTS L) (f : LTSHom H G), S.mem H f →
      isLabeledSimCovering H (T.pullback f)) :
    isLabeledSimCovering G T

/-!
## Part 13: Three-Point Chain: J_bisim < J_sim < J_trace
-/

/-- Every bisim-covering sieve is sim-covering: J_bisim refines J_sim.
    Encodes the refinement J_bisim <= J_sim in the Grothendieck topology ordering.
    Semantically: bisimulation equivalence is finer than simulation equivalence, so
    bisim-covering (testing with all trees, requiring ALL homs) is a stronger condition
    than sim-covering.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    Without a concrete definition of `isLabeledSimCovering`, we cannot prove this inclusion.
    Once J_sim is made explicit, this should follow from the fact that bisim-covering
    requires all tree homs to be in S, which is at least as strong as any intermediate
    sim-covering condition.

    **Classification**: `Axiomatized: open problem -- J_bisim <= J_sim refinement` -/
axiom bisimCovering_implies_simCovering {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {S : LTSSieve G}
    (hS : isLabeledBisimCovering G S) : isLabeledSimCovering G S

/-- Every sim-covering sieve is trace-covering: J_sim refines J_trace.
    Encodes the refinement J_sim <= J_trace in the Grothendieck topology ordering.
    Semantically: simulation equivalence is finer than trace equivalence (proven by
    `sim_implies_traceInclusion`), so sim-covering is a stronger condition than
    trace-covering (which only tests with path digraphs).

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    Without a concrete definition of `isLabeledSimCovering`, we cannot prove this inclusion.
    Once J_sim is made explicit, this should follow from the fact that every path digraph
    is a tree, so trace-covering (testing with paths) is weaker than any tree-based
    sim-covering condition.

    **Classification**: `Axiomatized: open problem -- J_sim <= J_trace refinement` -/
axiom simCovering_implies_traceCovering {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {S : LTSSieve G}
    (hS : isLabeledSimCovering G S) : isLabeledTraceCovering G S

/-- J_trace is strictly coarser than J_sim: there exists a sieve that is trace-covering
    but not sim-covering. The witness system is vgPairA/vgPairB: they are trace-equivalent
    (proven by `mutualSim_implies_traceEquiv` + `vgPairB_simulates_vgPairA`) but NOT
    mutually similar (proven by `vgPairA_not_simulates_vgPairB`). The sieve that
    separates them is trace-covering but not sim-covering.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    The concrete witness systems (vgPairA/B) are fully verified in this file, but
    translating the separation into a covering-sieve statement requires the explicit
    `isLabeledSimCovering` predicate. The witness is: vgPairA and vgPairB are
    trace-equivalent but not simulation-equivalent, so J_sim distinguishes them
    while J_trace does not.

    **Classification**: `Axiomatized: open problem -- J_sim != J_trace separation witness` -/
axiom sim_covering_separates_trace_sim :
    ∃ (G : FinLTS ThreeLabel) (S : LTSSieve G),
      isLabeledTraceCovering G S ∧ ¬isLabeledSimCovering G S

/-- J_sim is strictly coarser than J_bisim: there exists a sieve that is sim-covering
    but not bisim-covering. The witness system is vgPairB/vgPairC: they are mutually
    similar (proven by `vgPairBC_mutual_sim`) but NOT bisimilar (proven by
    `vgPairB_not_bisim_vgPairC`). The sieve that separates them is sim-covering
    but not bisim-covering.

    **Why axiomatized**: Open Problem (a) in the paper -- explicit J_sim covering predicate.
    The concrete witness systems (vgPairB/C) are fully verified in this file, but
    translating the separation into a covering-sieve statement requires the explicit
    `isLabeledSimCovering` predicate. The witness is: vgPairB and vgPairC are
    simulation-equivalent but not bisimulation-equivalent, so J_bisim distinguishes them
    while J_sim does not.

    **Classification**: `Axiomatized: open problem -- J_bisim != J_sim separation witness` -/
axiom sim_covering_separates_sim_bisim :
    ∃ (G : FinLTS ThreeLabel) (S : LTSSieve G),
      isLabeledSimCovering G S ∧ ¬isLabeledBisimCovering G S

/-- The full ordering: J_bisim <= J_sim <= J_trace as Grothendieck topologies. -/
theorem sim_topology_ordering {L : Type} [Fintype L] [DecidableEq L]
    {G : FinLTS L} {S : LTSSieve G} :
    (isLabeledBisimCovering G S → isLabeledSimCovering G S) ∧
    (isLabeledSimCovering G S → isLabeledTraceCovering G S) :=
  ⟨bisimCovering_implies_simCovering, simCovering_implies_traceCovering⟩

/-- **Three-point strict chain:** J_bisim < J_sim < J_trace.

    This is the main result: the simulation topology J_sim sits strictly between the
    bisimulation and trace topologies, giving a three-point chain in the labeled
    van Glabbeek spectrum of Grothendieck topologies. -/
theorem sim_topology_three_point_chain :
    -- (1) J_bisim <= J_sim <= J_trace
    (∀ (L : Type) [Fintype L] [DecidableEq L] (G : FinLTS L) (S : LTSSieve G),
      isLabeledBisimCovering G S → isLabeledSimCovering G S) ∧
    (∀ (L : Type) [Fintype L] [DecidableEq L] (G : FinLTS L) (S : LTSSieve G),
      isLabeledSimCovering G S → isLabeledTraceCovering G S) ∧
    -- (2) Strict: J_sim ≠ J_trace (vgPairA/B witness)
    (∃ (G : FinLTS ThreeLabel) (S : LTSSieve G),
      isLabeledTraceCovering G S ∧ ¬isLabeledSimCovering G S) ∧
    -- (3) Strict: J_bisim ≠ J_sim (vgPairB/C witness)
    (∃ (G : FinLTS ThreeLabel) (S : LTSSieve G),
      isLabeledSimCovering G S ∧ ¬isLabeledBisimCovering G S) :=
  ⟨fun _ _ _ _ _ => bisimCovering_implies_simCovering,
   fun _ _ _ _ _ => simCovering_implies_traceCovering,
   sim_covering_separates_trace_sim,
   sim_covering_separates_sim_bisim⟩

/-!
## Part 14: Master Summary
-/

/-- Master theorem: simulation topology with all key results.

    Combines:
    1. Simulation definitions and their relationship to bisimulation and traces
    2. Concrete van Glabbeek separation proofs
    3. Naive stability failure counterexample
    4. Three Grothendieck axioms for J_sim
    5. Three-point strict chain J_bisim < J_sim < J_trace -/
theorem simulation_topology_summary :
    -- (1) Bisim implies mutual sim
    (∀ (G : FinLTS ThreeLabel) (v : G.Vertex) (H : FinLTS ThreeLabel) (w : H.Vertex),
      labeledBisimEquiv G v H w → labeledMutualSim G v H w) ∧
    -- (2) Mutual sim implies trace equiv
    (∀ (G : FinLTS ThreeLabel) (v : G.Vertex) (H : FinLTS ThreeLabel) (w : H.Vertex),
      labeledMutualSim G v H w → labeledTraceEquiv G v H w) ∧
    -- (3) Concrete: B simulates A
    labeledSimulates vgPairA (⟨0, by omega⟩ : vgPairA.Vertex)
                     vgPairB (⟨0, by omega⟩ : vgPairB.Vertex) ∧
    -- (4) Concrete: A does NOT simulate B
    ¬labeledSimulates vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                      vgPairA (⟨0, by omega⟩ : vgPairA.Vertex) ∧
    -- (5) Concrete: B and C mutually similar
    labeledMutualSim vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                     vgPairC (⟨0, by omega⟩ : vgPairC.Vertex) ∧
    -- (6) Concrete: B and C NOT bisimilar
    ¬labeledBisimEquiv vgPairB (⟨0, by omega⟩ : vgPairB.Vertex)
                        vgPairC (⟨0, by omega⟩ : vgPairC.Vertex) ∧
    -- (7) Naive stability failure
    (∃ (G H : FinLTS ThreeLabel) (h : LTSHom H G) (S : LTSSieve G),
      isSimCoveringNaive G S ∧ ¬isSimCoveringNaive H (S.pullback h)) ∧
    -- (8) Three-point chain
    (∀ (L : Type) [Fintype L] [DecidableEq L] (G : FinLTS L) (S : LTSSieve G),
      isLabeledBisimCovering G S → isLabeledSimCovering G S) ∧
    (∀ (L : Type) [Fintype L] [DecidableEq L] (G : FinLTS L) (S : LTSSieve G),
      isLabeledSimCovering G S → isLabeledTraceCovering G S) :=
  ⟨fun _ _ _ _ => bisimEquiv_implies_mutualSim,
   fun _ _ _ _ => mutualSim_implies_traceEquiv,
   vgPairB_simulates_vgPairA,
   vgPairA_not_simulates_vgPairB,
   vgPairBC_mutual_sim,
   vgPairB_not_bisim_vgPairC,
   naive_sim_covering_not_stable,
   fun _ _ _ _ _ => bisimCovering_implies_simCovering,
   fun _ _ _ _ _ => simCovering_implies_traceCovering⟩

end RTS.PresheafTopos
