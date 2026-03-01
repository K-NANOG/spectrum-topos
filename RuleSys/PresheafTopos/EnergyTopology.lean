/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Grothendieck Topology: Parametric Topology Structure

This file wraps the Phase 191 energy covering predicates into a formal
`EnergyGrothendieckTopology` structure and proves:

1. **Structure definition**: `EnergyGrothendieckTopology` with maximality, stability, transitivity
2. **LE ordering and extensionality**: coarseness ordering and structural equality
3. **Parametric constructor**: `energyTopology` builds a topology from any `NamedEquivalence`
4. **Existing topology wrappers**: `traceGrothendieckTopology`, `bisimGrothendieckTopology`,
   `simGrothendieckTopology`
5. **Identification theorems**: energy topologies at traces/bisim agree with existing definitions
6. **Antitone spectrum embedding**: finer equivalence → coarser topology (order reversal)
7. **Topology chain**: J_bisim ≤ J_sim ≤ J_trace
8. **SpectrumTopologyEmbedding**: bundled structure packaging the embedding
9. **Master summary**: combined theorem

## Mathematical Significance

The 13 named equivalences in the van Glabbeek spectrum each define a Grothendieck
topology on the category of finite labeled transition systems. The mapping
E ↦ J_E is antitone: finer behavioral equivalence (larger energy) yields a
coarser Grothendieck topology (fewer covering sieves needed). This is the
covering-level manifestation of the order reversal:
  larger energy → finer equivalence → more test objects → harder to cover

## References

- Bisping, "Process Equivalence Problems as Energy Games" (CAV 2023, PhD 2025)
- van Glabbeek, "The Linear Time - Branching Time Spectrum" (1990, 2001)
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic" (1992), III.2
-/

import RuleSys.SubtoposLattice.EnergyTestObjects
import RuleSys.PresheafTopos.SimulationTopology

set_option autoImplicit false

universe u

namespace Ruliology.PresheafTopos

/-!
## Section 1: EnergyGrothendieckTopology Structure

A Grothendieck topology on the category of finite L-labeled transition systems,
specified by a covering predicate satisfying maximality, stability, and transitivity.
-/

/-- A Grothendieck topology on the category of finite L-labeled transition systems.
The `covering` predicate specifies which sieves on each object are covering.
The three axioms (maximality, stability, transitivity) ensure this defines
a genuine Grothendieck topology. -/
structure EnergyGrothendieckTopology (L : Type) [Fintype L] [DecidableEq L] where
  /-- The covering predicate: `covering G S` holds iff sieve `S` on `G` is covering. -/
  covering : (G : FinLTS L) → LTSSieve G → Prop
  /-- Maximality: the maximal sieve (containing all morphisms) covers every object. -/
  maximal : ∀ G, covering G (LTSSieve.maximal G)
  /-- Stability: if S covers G, then the pullback f*(S) covers H for any f : H → G. -/
  stable : ∀ {G H : FinLTS L} {S : LTSSieve G} (f : LTSHom H G),
    covering G S → covering H (S.pullback f)
  /-- Transitivity: if S covers G and for every (H, f) in S the pullback f*(T) covers H,
  then T covers G. -/
  transitive : ∀ {G : FinLTS L} {S T : LTSSieve G},
    covering G S →
    (∀ (H : FinLTS L) (f : LTSHom H G), S.mem H f → covering H (T.pullback f)) →
    covering G T

/-!
## Section 2: LE Ordering and Extensionality

J₁ ≤ J₂ means every J₁-covering sieve is also J₂-covering (J₁ is coarser).
-/

/-- Coarseness ordering on topologies: J₁ ≤ J₂ iff every J₁-covering sieve is J₂-covering.
A coarser topology has fewer covering sieves: if J₁ ≤ J₂ then J₂ admits all J₁-covers. -/
instance {L : Type} [Fintype L] [DecidableEq L] :
    LE (EnergyGrothendieckTopology L) where
  le J₁ J₂ := ∀ G S, J₁.covering G S → J₂.covering G S

/-- Two energy Grothendieck topologies are equal iff they have the same covering sieves. -/
theorem EnergyGrothendieckTopology.ext {L : Type} [Fintype L] [DecidableEq L]
    {J₁ J₂ : EnergyGrothendieckTopology L}
    (h : ∀ G S, J₁.covering G S ↔ J₂.covering G S) : J₁ = J₂ := by
  cases J₁; cases J₂
  congr 1
  funext G S
  exact propext (h G S)

/-!
## Section 3: Parametric Constructor for All 13 Energy Topologies

Given any `NamedEquivalence` E, build a `EnergyGrothendieckTopology` using the
`isEnergyCovering E` predicate from EnergyTestObjects.lean.
-/

/-- The parametric energy topology: for any named equivalence E, the covering predicate
`isEnergyCovering E` satisfies all three Grothendieck axioms (proved in EnergyTestObjects.lean).

This maps each of the 13 van Glabbeek equivalences to a Grothendieck topology. -/
def energyTopology {L : Type} [Fintype L] [DecidableEq L]
    (E : NamedEquivalence) : EnergyGrothendieckTopology L where
  covering := Ruliology.isEnergyCovering E
  maximal := Ruliology.energyCovering_maximal E
  stable := fun f hS => Ruliology.energyCovering_stable E f hS
  transitive := fun hS hT => Ruliology.energyCovering_transitive E hS hT

/-!
## Section 4: Existing Topology Wrappers

Wrap the existing labeled trace, bisim, and sim covering predicates into
`EnergyGrothendieckTopology` structures.
-/

/-- The trace Grothendieck topology as an `EnergyGrothendieckTopology` structure.
Uses `isLabeledTraceCovering` and its three proven axioms. -/
def traceGrothendieckTopology {L : Type} [Fintype L] [DecidableEq L] :
    EnergyGrothendieckTopology L where
  covering := isLabeledTraceCovering
  maximal := labeled_trace_covering_maximal
  stable := fun f hS => labeled_trace_covering_stable f hS
  transitive := fun hS hT => labeled_trace_covering_transitive hS hT

/-- The bisimulation Grothendieck topology as an `EnergyGrothendieckTopology` structure.
Uses `isLabeledBisimCovering` and its three proven axioms. -/
def bisimGrothendieckTopology {L : Type} [Fintype L] [DecidableEq L] :
    EnergyGrothendieckTopology L where
  covering := isLabeledBisimCovering
  maximal := labeled_bisim_covering_maximal
  stable := fun f hS => labeled_bisim_covering_stable f hS
  transitive := fun hS hT => labeled_bisim_covering_transitive hS hT

/-- The simulation Grothendieck topology as an `EnergyGrothendieckTopology` structure.
Uses `isLabeledSimCovering` and its three axiomatized axioms. -/
def simGrothendieckTopology {L : Type} [Fintype L] [DecidableEq L] :
    EnergyGrothendieckTopology L where
  covering := isLabeledSimCovering
  maximal := labeled_sim_covering_maximal
  stable := fun f hS => labeled_sim_covering_stable f hS
  transitive := fun hS hT => labeled_sim_covering_transitive hS hT

/-!
## Section 5: Identification Theorems

The parametric `energyTopology` at `.traces` and `.bisimulation` agrees with the
existing `traceGrothendieckTopology` and `bisimGrothendieckTopology`.
-/

/-- The energy topology at `.traces` equals the trace Grothendieck topology.

Proof: by extensionality, using `energyCovering_traces_iff` from EnergyTestObjects.lean
which shows `isEnergyCovering .traces G S ↔ isLabeledTraceCovering G S`. -/
theorem energyTopology_traces_eq {L : Type} [Fintype L] [DecidableEq L] :
    @energyTopology L _ _ .traces = traceGrothendieckTopology :=
  EnergyGrothendieckTopology.ext fun G S =>
    Ruliology.energyCovering_traces_iff G S

/-- The energy topology at `.bisimulation` equals the bisim Grothendieck topology.

Proof: by extensionality, using `energyCovering_bisim_iff` from EnergyTestObjects.lean
which shows `isEnergyCovering .bisimulation G S ↔ isLabeledBisimCovering G S`. -/
theorem energyTopology_bisim_eq {L : Type} [Fintype L] [DecidableEq L] :
    @energyTopology L _ _ .bisimulation = bisimGrothendieckTopology :=
  EnergyGrothendieckTopology.ext fun G S =>
    Ruliology.energyCovering_bisim_iff G S

/-!
## Section 6: Antitone Spectrum Embedding

The mapping E ↦ energyTopology E is antitone: if E₁ ≤ E₂ (E₁ coarser equivalence),
then energyTopology E₂ ≤ energyTopology E₁ (J_{E₂} has fewer covering sieves).

This is the structure-level manifestation of the order reversal:
larger energy → finer equivalence → more test objects → harder to cover.
-/

/-- The energy topology map is antitone: finer equivalence → coarser topology.

E₁ ≤ E₂ means E₂ has more energy (finer equivalence). Then every E₁-covering sieve
is also E₂-covering (since E₁ has fewer test objects to satisfy), but NOT vice versa.
So `energyTopology E₂ ≤ energyTopology E₁` (J_{E₂} has fewer covering sieves). -/
theorem energyTopology_antitone {L : Type} [Fintype L] [DecidableEq L] :
    ∀ E₁ E₂ : NamedEquivalence, E₁ ≤ E₂ →
      @energyTopology L _ _ E₂ ≤ @energyTopology L _ _ E₁ :=
  fun E₁ E₂ hle G S hS => Ruliology.energyCovering_monotone E₁ E₂ hle G S hS

/-!
## Section 7: Topology Chain

The chain J_bisim ≤ J_sim ≤ J_trace follows from antitone + spectrum ordering.
-/

/-- The topology chain: J_bisim ≤ J_sim ≤ J_trace.

Since `traces ≤ simulation ≤ ... ≤ bisimulation` in the spectrum ordering, and
the topology map is antitone, we get:
`energyTopology .bisimulation ≤ energyTopology .simulation ≤ energyTopology .traces`. -/
theorem topology_chain {L : Type} [Fintype L] [DecidableEq L] :
    @energyTopology L _ _ .bisimulation ≤ energyTopology .simulation ∧
    @energyTopology L _ _ .simulation ≤ energyTopology .traces := by
  constructor
  · -- bisim ≤ sim: need simulation ≤ bisimulation in spectrum
    exact energyTopology_antitone .simulation .bisimulation
      (NamedEquivalence.simulation_le_readySimulation.trans
        (NamedEquivalence.readySimulation_le_twoNestedSimulation.trans
          NamedEquivalence.twoNestedSimulation_le_bisimulation))
  · -- sim ≤ trace: need traces ≤ simulation in spectrum
    exact energyTopology_antitone .traces .simulation
      NamedEquivalence.traces_le_simulation

/-!
## Section 8: SpectrumTopologyEmbedding

A bundled structure packaging the antitone spectrum embedding together with
its identification properties.
-/

/-- The spectrum topology embedding: bundles the energy topology map with its
key properties (antitone, identifies with existing topologies). -/
structure SpectrumTopologyEmbedding (L : Type) [Fintype L] [DecidableEq L] where
  /-- The topology map: each named equivalence gets a Grothendieck topology. -/
  topology : NamedEquivalence → EnergyGrothendieckTopology L
  /-- Antitone: finer equivalence → coarser topology. -/
  antitone : ∀ E₁ E₂, E₁ ≤ E₂ → topology E₂ ≤ topology E₁
  /-- At traces, agrees with the existing trace topology. -/
  traces_eq : topology .traces = traceGrothendieckTopology
  /-- At bisimulation, agrees with the existing bisim topology. -/
  bisim_eq : topology .bisimulation = bisimGrothendieckTopology

/-- The canonical spectrum embedding: the energy topology map with all its properties. -/
def spectrumEmbedding {L : Type} [Fintype L] [DecidableEq L] :
    SpectrumTopologyEmbedding L where
  topology := energyTopology
  antitone := energyTopology_antitone
  traces_eq := energyTopology_traces_eq
  bisim_eq := energyTopology_bisim_eq

/-!
## Section 9: Master Summary Theorem
-/

/-- **Master theorem**: Energy topologies provide an antitone embedding of the
van Glabbeek spectrum into the lattice of Grothendieck topologies.

Combines:
1. Antitone: E₁ ≤ E₂ → J_{E₂} ≤ J_{E₁}
2. Traces identification: energyTopology .traces = traceGrothendieckTopology
3. Bisim identification: energyTopology .bisimulation = bisimGrothendieckTopology
4. Topology chain: J_bisim ≤ J_sim ≤ J_trace -/
theorem energy_topology_summary {L : Type} [Fintype L] [DecidableEq L] :
    -- (1) Antitone embedding
    (∀ E₁ E₂ : NamedEquivalence, E₁ ≤ E₂ →
      @energyTopology L _ _ E₂ ≤ @energyTopology L _ _ E₁) ∧
    -- (2) Traces identification
    (@energyTopology L _ _ .traces = traceGrothendieckTopology) ∧
    -- (3) Bisim identification
    (@energyTopology L _ _ .bisimulation = bisimGrothendieckTopology) ∧
    -- (4) Topology chain
    (@energyTopology L _ _ .bisimulation ≤ energyTopology .simulation ∧
     @energyTopology L _ _ .simulation ≤ energyTopology .traces) :=
  ⟨energyTopology_antitone,
   energyTopology_traces_eq,
   energyTopology_bisim_eq,
   topology_chain⟩

/-!
## Summary

### Definitions (6)
- `EnergyGrothendieckTopology`: structure with covering + 3 axioms
- `energyTopology`: parametric topology constructor from NamedEquivalence
- `traceGrothendieckTopology`: J_trace as EnergyGrothendieckTopology
- `bisimGrothendieckTopology`: J_bisim as EnergyGrothendieckTopology
- `simGrothendieckTopology`: J_sim as EnergyGrothendieckTopology
- `SpectrumTopologyEmbedding`: bundled antitone embedding structure
- `spectrumEmbedding`: canonical instance

### Theorems (7)
- `EnergyGrothendieckTopology.ext`: extensionality
- `energyTopology_traces_eq`: energy topology at traces = J_trace
- `energyTopology_bisim_eq`: energy topology at bisim = J_bisim
- `energyTopology_antitone`: antitone embedding
- `topology_chain`: J_bisim ≤ J_sim ≤ J_trace
- `energy_topology_summary`: master summary theorem

### Axiom count: 0 new axioms
All proofs follow from existing infrastructure in EnergyTestObjects.lean and
the labeled topology files.
-/

end Ruliology.PresheafTopos
