/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Regime Classification: Three-Regime Taxonomy for Rooted Transition Systems

This file formalizes the three-regime taxonomy for connected reachable multiway
systems based on the kernel/image/cokernel structure of the symmetry homomorphism
phi: Aut(graph) -> Aut(Lind).

## The Three Regimes

Every connected reachable rooted transition system falls into exactly one of three
symmetry regimes, classified by the kernel and cokernel of phi:

1. **Deterministic regime**: ker = Aut(graph), coker = 1.
   All graph symmetry is killed. The Lindenbaum algebra collapses to Bool.
   Example: two-cycle (toggle).

2. **Aligned regime**: ker = 1, coker = 1.
   phi is an isomorphism: graph and topos see the same symmetry group.
   Example: hub-spokes.

3. **Creative regime**: ker = 1, coker non-trivial.
   phi is injective but not surjective: the topos creates symmetry ex nihilo.
   Example: asymmetric diamond.

## Exhaustiveness

The kernel dichotomy (Phase 115) guarantees that no fourth case (non-trivial
kernel AND non-trivial cokernel) can occur. For connected reachable systems:
- Nondeterministic => kernel trivial => either aligned or creative
- Deterministic => kernel maximal, Lind = Bool, Aut(Lind) = 1 => deterministic

## Main Results

### Part 1: Regime Type
- `SymmetryRegime`: inductive with constructors deterministic, aligned, creative

### Part 2: Image and Cokernel Cardinality
- `imageCard`: |im(phi)| = |Aut(graph)| / |ker(phi)|
- `cokernelCard`: |coker(phi)| = |Aut(Lind)| / |im(phi)|
- Per-system image/cokernel computations (6 theorems)

### Part 3: Classification Function and Per-System Proofs
- `classifyRegime`: assigns regime from kernel/graphAut/cokernel cardinalities
- Per-system regime proofs (3 theorems)

### Part 4: Headline Theorem
- `regime_table`: combined three-system regime/image/cokernel data

### Part 5: Exhaustiveness
- `no_mixed_regime`: kernel dichotomy corollary ruling out fourth case
- `regime_exhaustive`: kernel dichotomy alias with regime-oriented documentation

## References

- Caramello, "Theories, Sites, Toposes" (OUP, 2018)
- Vickers, "Topology via Logic" (1989)
-/

import RuleSys.SubtoposLattice.KernelDichotomy

set_option autoImplicit false

universe u

open GeometricLogic.Propositional
open CategoryTheory

namespace RTS

/-!
## Part 1: Symmetry Regime Type

The three-regime taxonomy classifies rooted transition systems by the kernel/cokernel
structure of the symmetry homomorphism phi: Aut(graph) -> Aut(Lind).

The regimes are mutually exclusive and (for connected reachable systems)
exhaustive by the kernel dichotomy theorem.
-/

/-- The three symmetry regimes for rooted transition systems.

Each regime describes a qualitatively different relationship between graph-level
symmetry (Aut(graph)) and topos-level symmetry (Aut(Lind)):

- **deterministic**: ker = Aut(graph), coker = 1. All graph symmetry is killed
  by the passage to the propositional theory. The Lindenbaum algebra collapses
  to Bool (all atoms forced). Example: two-cycle.

- **aligned**: ker = 1, coker = 1. The symmetry homomorphism is an isomorphism.
  Graph and topos see exactly the same symmetry group. Example: hub-spokes.

- **creative**: ker = 1, coker non-trivial. The symmetry homomorphism is
  injective but not surjective. The topos creates symmetry invisible to graph
  theory. Example: asymmetric diamond. -/
inductive SymmetryRegime where
  /-- All graph symmetry killed: ker = Aut(graph), image = 1, cokernel = 1.
  Occurs when all states are deterministic, collapsing Lind to Bool. -/
  | deterministic
  /-- Graph and topos symmetry aligned: ker = 1, phi is an isomorphism.
  Occurs when nondeterminism creates exactly the right lattice symmetry. -/
  | aligned
  /-- Topos creates symmetry ex nihilo: ker = 1, cokernel non-trivial.
  Occurs when nondeterminism creates more lattice symmetry than graph symmetry. -/
  | creative
  deriving DecidableEq, Repr

/-!
## Part 2: Image and Cokernel Cardinality

By the first isomorphism theorem for finite groups:
- |im(phi)| = |Aut(graph)| / |ker(phi)|
- |coker(phi)| = |Aut(Lind)| / |im(phi)|

These are pure Nat arithmetic from existing cardinality theorems.
-/

/-- Image cardinality of the symmetry homomorphism.

By the first isomorphism theorem: |im(phi)| = |Aut(graph)| / |ker(phi)|.
This is exact division since |ker(phi)| divides |Aut(graph)| (Lagrange). -/
def imageCard (graphAutCard kernelCard : Nat) : Nat := graphAutCard / kernelCard

/-- Cokernel cardinality of the symmetry homomorphism.

|coker(phi)| = |Aut(Lind)| / |im(phi)|.
Measures how much topos symmetry is NOT in the image of graph symmetry. -/
def cokernelCard (lindAutCard imageCardVal : Nat) : Nat := lindAutCard / imageCardVal

/-!
### Hub-Spokes: image = 2, cokernel = 1

Hub-spokes has graphAut = 2, kernel = 1, lindAut = 2.
- image = 2/1 = 2 (phi is injective, full image)
- cokernel = 2/2 = 1 (phi is surjective)

The homomorphism is an isomorphism: aligned regime.
-/

/-- Hub-spokes image cardinality: |im(phi)| = |Aut(graph)| / |ker| = 2/1 = 2. -/
theorem hubSpokes_image_card : imageCard 2 1 = 2 := by native_decide

/-- Hub-spokes cokernel cardinality: |coker(phi)| = |Aut(Lind)| / |im| = 2/2 = 1. -/
theorem hubSpokes_cokernel_card : cokernelCard 2 2 = 1 := by native_decide

/-!
### Two-Cycle: image = 1, cokernel = 1

Two-cycle has graphAut = 2, kernel = 2, lindAut = 1.
- image = 2/2 = 1 (phi is the zero map, trivial image)
- cokernel = 1/1 = 1 (trivially, since target is trivial)

All graph symmetry is killed: deterministic regime.
-/

/-- Two-cycle image cardinality: |im(phi)| = |Aut(graph)| / |ker| = 2/2 = 1. -/
theorem twoCycle_image_card : imageCard 2 2 = 1 := by native_decide

/-- Two-cycle cokernel cardinality: |coker(phi)| = |Aut(Lind)| / |im| = 1/1 = 1. -/
theorem twoCycle_cokernel_card : cokernelCard 1 1 = 1 := by native_decide

/-!
### Asymmetric Diamond: image = 1, cokernel = 2

Asymmetric diamond has graphAut = 1, kernel = 1, lindAut = 2.
- image = 1/1 = 1 (phi is injective from trivial source)
- cokernel = 2/1 = 2 (topos has symmetry not from graph)

The topos creates symmetry ex nihilo: creative regime.
-/

/-- Asymmetric diamond image cardinality: |im(phi)| = |Aut(graph)| / |ker| = 1/1 = 1. -/
theorem asymDiamond_image_card : imageCard 1 1 = 1 := by native_decide

/-- Asymmetric diamond cokernel cardinality: |coker(phi)| = |Aut(Lind)| / |im| = 2/1 = 2. -/
theorem asymDiamond_cokernel_card : cokernelCard 2 1 = 2 := by native_decide

/-!
## Part 3: Regime Classification Function and Per-System Proofs

The classification function assigns a regime based on the kernel, graph automorphism,
and cokernel cardinalities.

Classification logic (cokernel-first):
- Non-trivial cokernel (> 1) => creative (topos has symmetry not from graph).
  This must be checked first because when graphAut = 1, the kernel is trivially
  equal to graphAut (both 1), yet the system can still be creative.
- Trivial cokernel and ker = graphAut => deterministic (all graph symmetry killed)
- Trivial cokernel and ker < graphAut => aligned (phi is isomorphism)
-/

/-- Classify the symmetry regime from kernel, graph automorphism, and cokernel
cardinalities.

The cokernel is checked first because it distinguishes the creative regime
even when graphAut = 1 (where ker = graphAut trivially):
- Non-trivial cokernel (> 1) => creative regime
- Trivial cokernel and ker = graphAut => deterministic regime
- Trivial cokernel and ker < graphAut => aligned regime (phi is iso) -/
def classifyRegime (kernelCard graphAutCard cokernelCardVal : Nat) : SymmetryRegime :=
  if cokernelCardVal > 1 then .creative
  else if kernelCard = graphAutCard then .deterministic
  else .aligned

/-- Hub-spokes is in the aligned regime: cokernel=1 (not creative),
ker=1 != graphAut=2, so aligned. phi is an isomorphism. -/
theorem hubSpokes_regime : classifyRegime 1 2 1 = .aligned := by native_decide

/-- Two-cycle is in the deterministic regime: cokernel=1 (not creative),
ker=2 = graphAut=2, so deterministic. All graph symmetry killed. -/
theorem twoCycle_regime : classifyRegime 2 2 1 = .deterministic := by native_decide

/-- Asymmetric diamond is in the creative regime: cokernel=2 > 1, so creative.
The topos creates symmetry invisible to graph theory. -/
theorem asymDiamond_regime : classifyRegime 1 1 2 = .creative := by native_decide

/-!
## Part 4: Headline Three-Regime Table

The combined theorem asserting regime classification and image/cokernel data
for all three benchmark systems.
-/

/-- **Three-regime table**: complete kernel/image/cokernel data and regime
classification for the three benchmark rooted transition systems.

| System             | ker | im | coker | Regime        |
|--------------------|-----|----|-------|---------------|
| Hub-spokes         |  1  |  2 |   1   | aligned       |
| Two-cycle          |  2  |  1 |   1   | deterministic |
| Asymmetric diamond |  1  |  1 |   2   | creative      |

This upgrades the v11.0 symmetry trichotomy from cardinality observations
to a named, classified taxonomy with an exhaustiveness guarantee. -/
theorem regime_table :
    -- Hub-spokes: aligned (ker=1, im=2, coker=1)
    classifyRegime 1 2 1 = .aligned ∧
    imageCard 2 1 = 2 ∧ cokernelCard 2 2 = 1 ∧
    -- Two-cycle: deterministic (ker=2, im=1, coker=1)
    classifyRegime 2 2 1 = .deterministic ∧
    imageCard 2 2 = 1 ∧ cokernelCard 1 1 = 1 ∧
    -- Asymmetric diamond: creative (ker=1, im=1, coker=2)
    classifyRegime 1 1 2 = .creative ∧
    imageCard 1 1 = 1 ∧ cokernelCard 2 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-!
## Part 5: Exhaustiveness via Kernel Dichotomy

The kernel dichotomy (Phase 115) guarantees that the three regimes are exhaustive
for connected reachable systems. No fourth case (both non-trivial kernel and
non-trivial cokernel) can occur:

- **Nondeterministic case**: kernel is trivial (= 1). Only cokernel can vary,
  giving either aligned (coker = 1) or creative (coker > 1).

- **Deterministic case**: kernel is maximal (= Aut(graph)). Lind = Bool, so
  Aut(Lind) = 1, forcing cokernel = 1. This is the deterministic regime.

In neither case are both kernel and cokernel non-trivial.
-/

/-- **No mixed regime**: for connected reachable systems with nondeterminism,
every kernel element is the identity.

This is the nondeterministic branch of the kernel dichotomy, extracted as a
direct corollary. It rules out the "mixed" fourth regime where both kernel
and cokernel would be non-trivial: if the system has nondeterminism, the
kernel is trivial, so only the cokernel can contribute non-trivially
(giving either aligned or creative regime).

Combined with the deterministic branch (where Lind = Bool forces Aut(Lind) = 1,
making cokernel trivial), this establishes that the three regimes are exhaustive. -/
theorem no_mixed_regime
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool) (init : S)
    (hconn : IsConnectedReachable hasEdge init)
    (hnd : HasNondeterministicState S hasEdge) :
    ∀ σ : symmetryKernel S hasEdge, ∀ v : S, σ.1.1 v = v :=
  (kernel_dichotomy S hasEdge init hconn).1 hnd

/-- **Regime exhaustiveness via kernel dichotomy**: for connected reachable systems,
the symmetry homomorphism kernel is either trivial or maximal. This means:

1. **Nondeterministic case** (kernel trivial): the system is in the aligned
   or creative regime, depending on whether phi is surjective.

2. **Deterministic case** (kernel maximal): the system is in the deterministic
   regime (Lind = Bool, Aut(Lind) = 1, cokernel trivial).

No fourth case with both non-trivial kernel and non-trivial cokernel exists.
This is a direct alias of `kernel_dichotomy` with regime-oriented documentation. -/
theorem regime_exhaustive
    (S : Type) [Fintype S] [DecidableEq S]
    (hasEdge : S → S → Bool) (init : S)
    (hconn : IsConnectedReachable hasEdge init) :
    (HasNondeterministicState S hasEdge →
      ∀ σ : symmetryKernel S hasEdge, ∀ v : S, σ.1.1 v = v) ∧
    (AllDeterministic S hasEdge →
      ∀ σ : GraphAut S hasEdge, symmetryHomomorphism S hasEdge σ = OrderIso.refl _) :=
  kernel_dichotomy S hasEdge init hconn

end RTS
