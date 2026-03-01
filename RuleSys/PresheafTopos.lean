/-
# PresheafTopos: The Classifying Topos Set[T_LTS]

This module computes properties of the classifying topos Set[T_LTS] = [f.p.LTS_L^op, Set]
for labeled transition systems, working toward genuine topos-geometric backward flow.

## Sub-modules

- `FiniteDigraph`: The category f.p.LTS₁ (finite directed graphs with homomorphisms)
- `OreProperty`: Right Ore condition, De Morgan property, categorical properties table
- `SubobjectClassifier`: Sieves, unique atom theorem, ¬¬-topology characterization
- `ModalConnection`: Diamond subfunctor, geometric ↔ positive HML correspondence
- `PathDigraph`: Path digraphs P_n, trace sets, path-homomorphism bijection
- `TraceTopology`: J_trace Grothendieck topology, three axioms, strictly finer than ¬¬
- `TraceSeparation`: Trace separation theorem, PathDigraph density, concrete separations
- `HeytingImplication`: Heyting implication on Ω, adjunction, negation-collapse gap
- `BisimEquivalence`: Bisimulation definition, equivalence relation, strictly finer than trace
- `BisimTopology`: J_bisim Grothendieck topology, three axioms, strictly finer than J_trace
- `BisimSeparation`: Tree-generated sieve density, forward bisim-tree hom transfer, sieve hierarchy
- `SpectrumBracket`: Observation classes, parametric bracket J_bisim ⊆ J_C ⊆ J_trace, |L|=1 collapse
- `LabeledLTS`: Labeled transition systems FinLTS L, category instance, labeled traces, van Glabbeek examples
- `LabeledTraceTopology`: Labeled trace Grothendieck topology, separation theorem, traceLTS density
- `LabeledBisimTopology`: Labeled bisim topology, bracket theorem, strict separation
- `SimulationTopology`: Simulation topology J_sim, three-point chain J_bisim < J_sim < J_trace, stability failure
- `FreeExtension`: HMLPos formulas, witness vertices, Free Extension Lemma
- `NegationCollapse`: Negation collapse for geometric subfunctors, ¬S_φ = ⊥, ¬¬S_φ = ⊤
- `GeometricClosure`: Geometric Closure Theorem, Heyting implication ↔ free extension satisfaction
- `ExplicitComputations`: Four regimes of geometric Heyting implication, concrete TwoLabel examples
- `ComparisonLemma`: Comparison Lemma for trace topos, prefix-hom bijection, Cattani-Winskel connection
- `EnergyTopology`: Energy Grothendieck topology structure, antitone spectrum embedding, topology chain
- `TreeUnraveling`: Bounded tree unraveling construction, rooted tree property, back condition
- `DepthPreservation`: LabeledHML/LTSGeoFormula types, forward preservation, depth-bounded bisimilarity
- `EqualityElimination`: Tree edge structure, no self-loops, unique parent/label, step/equality characterization
- `GeometricVanBenthemDefs`: Core definitions (FinLTSBisimInvariant, dBisimilar) for the geometric van Benthem theorem
- `GeometricVanBenthem`: Geometric van Benthem theorem — bisim-inv geo formulas are d-bisim-invariant
- `CharacteristicFormula`: Characteristic HML formulas for tree unravelings, characterization theorem
- `GeoTreeDecomposition`: Geo-tree decomposition via characteristic formulas, root-only HML equivalence
- `BudgetBisimulation`: Padded tree construction, endpoint bisimulation, constructive backward transfer
- `BackwardTransfer`: Backward transfer — bisim-invariant geo formulas transfer from G to Tree_G
- `AxiomElimination`: Axiom elimination — geo_dBisim_invariant as theorem via characteristic formula transfer
- `SimulationInvariance`: Simulation invariance for geometric formulas, HMLPos characterization
-/

import RuleSys.PresheafTopos.FiniteDigraph
import RuleSys.PresheafTopos.OreProperty
import RuleSys.PresheafTopos.SubobjectClassifier
import RuleSys.PresheafTopos.ModalConnection
import RuleSys.PresheafTopos.PathDigraph
import RuleSys.PresheafTopos.TraceTopology
import RuleSys.PresheafTopos.TraceSeparation
import RuleSys.PresheafTopos.HeytingImplication
import RuleSys.PresheafTopos.BisimEquivalence
import RuleSys.PresheafTopos.BisimTopology
import RuleSys.PresheafTopos.BisimSeparation
import RuleSys.PresheafTopos.SpectrumBracket
import RuleSys.PresheafTopos.LabeledLTS
import RuleSys.PresheafTopos.LabeledTraceTopology
import RuleSys.PresheafTopos.LabeledBisimTopology
import RuleSys.PresheafTopos.SimulationTopology
import RuleSys.PresheafTopos.FreeExtension
import RuleSys.PresheafTopos.NegationCollapse
import RuleSys.PresheafTopos.GeometricClosure
import RuleSys.PresheafTopos.ExplicitComputations
import RuleSys.PresheafTopos.ComparisonLemma
import RuleSys.PresheafTopos.EnergyTopology
import RuleSys.PresheafTopos.TreeUnraveling
import RuleSys.PresheafTopos.DepthPreservation
import RuleSys.PresheafTopos.EqualityElimination
import RuleSys.PresheafTopos.GeometricVanBenthemDefs
import RuleSys.PresheafTopos.GeometricVanBenthem
import RuleSys.PresheafTopos.CharacteristicFormula
import RuleSys.PresheafTopos.GeoTreeDecomposition
import RuleSys.PresheafTopos.BudgetBisimulation
import RuleSys.PresheafTopos.BackwardTransfer
import RuleSys.PresheafTopos.AxiomElimination
import RuleSys.PresheafTopos.SimulationInvariance
