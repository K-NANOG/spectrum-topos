/-
# Axiom audit

Reproduces the formalisation claim made in the companion paper
(*A Classifying Topos for the Spectrum of Equivalences*, §Conclusion):
the headline results are proved with **zero custom axioms**.

Run:

    lake build RuleSys && lake env lean AxiomAudit.lean

Expected: every declaration below reports only some subset of

    propext, Classical.choice, Quot.sound

which are Lean's three standard axioms. In particular **no** `Lean.ofReduceBool`
and **no** `Lean.trustCompiler`. Both come from `native_decide`, which discharges
a goal by compiled evaluation instead of kernel reduction and is forbidden in
Mathlib for that reason. Their absence is what "zero custom axioms" means here.

Several results are stronger than the claim requires. `hml_bisimInvariant`
depends on no axioms at all, and the depth-1/2 van Benthem instances on
`propext` alone.
-/

import RuleSys

/-! ## The geometric direction -/

-- Geometric Closure Theorem: presheaf Heyting implication by testing at a
-- single canonical free extension.
#print axioms RTS.PresheafTopos.geometric_closure_theorem

-- The observation-class topologies J_trace and J_bisim.
#print axioms RTS.PresheafTopos.spectrum_bracket_upper
#print axioms RTS.PresheafTopos.spectrum_bracket_lower
#print axioms RTS.PresheafTopos.labeled_spectrum_bracket_upper
#print axioms RTS.PresheafTopos.labeled_spectrum_bracket_lower

-- Naive simulation instability: the observation-class approach provably fails
-- for simulation (the (-1)- versus 0-truncation mismatch).
#print axioms RTS.PresheafTopos.rightSieve_naive_sim_covering
#print axioms RTS.PresheafTopos.rightSieve_pullback_not_naive_sim_covering

/-! ## The logical direction -/

-- Diamond-only HML is bisimulation-invariant (forward direction of the
-- Geometric van Benthem Theorem).
#print axioms RTS.hml_bisimInvariant
#print axioms RTS.hml_depth0_constant

-- Confirmatory depth-bounded instances.
#print axioms RTS.depth1_unique_bisimInvariant
#print axioms RTS.depth2_unique_bisimInvariant

-- Characteristic formulas.
#print axioms RTS.PresheafTopos.characteristicHML_iff
#print axioms RTS.PresheafTopos.characteristicHML_self_satisfies
#print axioms RTS.PresheafTopos.characteristicHML_root_hom_transfer

/-! ## The algebraic direction -/

-- The lattice closure of the 13 named equivalences has exactly 30 elements:
-- 13 named plus 17 unnamed hybrids.
#print axioms RTS.lattice_closure_count
#print axioms RTS.SpectrumElement.card

-- L₃₀ bi-Heyting structure: the Heyting adjunction, ...
#print axioms RTS.SpectrumElement.birkhoffHimp_property
#print axioms RTS.SpectrumElement.birkhoffHimp_largest

-- ... the identity S → F = IF identifying impossible futures as the algebraic
-- mediator of the simulation--failures divide, ...
#print axioms RTS.SpectrumElement.himp_possibleFutures_impossibleFutures

-- ... and the co-Heyting side.
#print axioms RTS.SpectrumElement.pseudocomplement_property
#print axioms RTS.SpectrumElement.coHeytingNeg_property
#print axioms RTS.SpectrumElement.birkhoffSdiff_property
#print axioms RTS.SpectrumElement.birkhoffSdiff_smallest
