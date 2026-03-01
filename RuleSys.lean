/-
# RuleSys: Simulation and Bisimulation in the Classifying Topos

This library formalizes the topos-theoretic framework for process equivalences
developed in the companion paper. It connects the van Glabbeek spectrum to
Grothendieck topologies on classifying toposes via Caramello's bridge technique.

## Structure

- `RuleSys.Basic`: Category of multiway systems
- `RuleSys.Ruliad`: Presheaf topos construction
- `RuleSys.Observer`: Observers as coverages
- `RuleSys.TwoCategory`: 2-equivalence ObsCtxt ≃ SubTop(Ruliad)
- `RuleSys.GeometricTheory`: Geometric theory and Morita equivalence
- `RuleSys.Bisimulation`: Relational and functional bisimulation
- `RuleSys.HML`: Diamond-only Hennessy–Milner logic
- `RuleSys.SubtoposLattice`: L₃₀ spectrum lattice and energy–LT bridge
- `RuleSys.PresheafTopos`: Grothendieck topologies and geometric closure
-/

import RuleSys.Basic
import RuleSys.Ruliad
import RuleSys.Observer
import RuleSys.TwoCategory
import RuleSys.GeometricTheory
-- Geometric Logic infrastructure
import RuleSys.GeometricLogic.Formula
import RuleSys.GeometricLogic.Sequent
import RuleSys.GeometricLogic.TheoryOfSystem
import RuleSys.GeometricLogic.Interpretation
import RuleSys.GeometricLogic.SyntacticCategory
-- Semantic satisfaction and soundness
import RuleSys.GeometricLogic.Satisfaction
import RuleSys.GeometricLogic.SeparatingSequents
import RuleSys.GeometricLogic.Soundness
import RuleSys.GeometricLogic.SemanticSeparation
import RuleSys.FirstSeparation
import RuleSys.SecondSeparation
import RuleSys.QuotientBridge
-- HML and bisimulation-invariant fragment characterization
import RuleSys.HML
import RuleSys.HMLSeparation
import RuleSys.BoundedVanBenthem
-- Propositional Lindenbaum algebra
import RuleSys.GeometricLogic.PropositionalLindenbaum
-- Syntactic coverage and Grothendieck topology
import RuleSys.GeometricLogic.SyntacticCoverage
-- Bridge axiom: propositional classifying topos separation
import RuleSys.GeometricLogic.BridgeAxiom
-- Syntactic integration: propositional ↔ first-order bridge
import RuleSys.GeometricLogic.SyntacticIntegration
-- Small concrete systems and subtopos enumeration
import RuleSys.SubtoposLattice
-- Bridge technique demonstrations
import RuleSys.BridgeTechnique
-- Labeled HML with sublanguage hierarchy
import RuleSys.LabeledHML
-- 4-level spectrum separation via distinguishing formulas
import RuleSys.SpectrumSeparation
-- Labeled Lindenbaum quotients and spectrum connection
import RuleSys.LabeledLindenbaum
-- Labeled symmetry and kernel analysis
import RuleSys.LabeledSymmetry
-- Presheaf topos: f.p.LTS category and classifying topos properties
import RuleSys.PresheafTopos
-- Bridge: MultiwaySystem ↔ FinLTS Unit formal functor
import RuleSys.MultiwayToLTS
-- Van Benthem bridge: geometric van Benthem theorem for MultiwaySystem images
import RuleSys.VanBenthemBridge
