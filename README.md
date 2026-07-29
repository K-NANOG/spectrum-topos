# RuleSys

Lean 4 formalisation of *A Classifying Topos for the Spectrum of Equivalences*
([arXiv:2603.01056](https://arxiv.org/abs/2603.01056)).

Each labelled transition system receives a geometric theory whose classifying topos determines
its provable geometric sequents. Behavioural equivalences appear as Grothendieck topologies on a
fixed site, and van Glabbeek's linear-time–branching-time spectrum embeds as a finite sub-poset
of the coframe of subtoposes: behavioural abstraction is localization.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain and every dependency revision
are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get     # prebuilt Mathlib oleans
lake build RuleSys
```

This compiles the root module together with all 117 submodules, so `import RuleSys` brings the
whole development into scope.

## Axioms

The headline results are proved without custom axioms. To check:

```bash
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` runs `#print axioms` over the twenty-one declarations corresponding to the
paper's main theorems. Each reports a subset of `propext`, `Classical.choice` and `Quot.sound` —
Lean's three standard axioms — and nothing else. Several are stronger: `hml_bisimInvariant`
depends on no axioms at all, and the depth-1 and depth-2 van Benthem instances on `propext`
alone.

Elsewhere in the development, `axiom` declarations mark interfaces to published results the
formalisation takes as given rather than reproving: Caramello's quotient-theory duality,
van Glabbeek's logical characterisation theorems, and Bisping's energy-game framework. None is
reachable from the declarations above, which is what the audit establishes.

## Results

| Result | Declaration | File |
|---|---|---|
| Geometric Closure Theorem | `geometric_closure_theorem` | `PresheafTopos/GeometricClosure.lean` |
| Geometric van Benthem, forward direction | `hml_bisimInvariant` | `BoundedVanBenthem.lean` |
| Depth 0–2 instances | `hml_depth0_constant`, `depth1_unique_bisimInvariant`, `depth2_unique_bisimInvariant` | `BoundedVanBenthem.lean` |
| Characteristic formulas | `characteristicHML_self_satisfies` | `PresheafTopos/CharacteristicFormula.lean` |
| Topologies `J_trace`, `J_bisim` | `spectrum_bracket_upper`, `labeled_spectrum_bracket_upper` | `PresheafTopos/SpectrumBracket.lean`, `LabeledBisimTopology.lean` |
| Naive simulation instability | `rightSieve_pullback_not_naive_sim_covering` | `PresheafTopos/SimulationTopology.lean` |
| 30-element lattice closure | `lattice_closure_count`, `SpectrumElement.card` | `SubtoposLattice/LatticeClosureComputation.lean` |
| L₃₀ bi-Heyting structure, `S → F = IF` | `birkhoffHimp_property`, `birkhoffHimp_largest`, `himp_possibleFutures_impossibleFutures` | `SubtoposLattice/HeytingComputation.lean` |
| Co-Heyting subtraction | `birkhoffSdiff_property`, `birkhoffSdiff_smallest` | `SubtoposLattice/BirkhoffDownsets.lean` |
| First and Second Separation | | `FirstSeparation.lean`, `SecondSeparation.lean` |
| Energy–Lawvere–Tierney bridge | | `SubtoposLattice/EnergyLTBridge.lean` |

Paths are relative to `RuleSys/`.

## Layout

```
RuleSys.lean              root module
RuleSys/Basic.lean        category of rooted transition systems
RuleSys/RTSTopos.lean     presheaf topos construction
RuleSys/Observer.lean     observers as coverages
RuleSys/GeometricLogic/   formulas, sequents, syntactic category, soundness
RuleSys/Bisimulation.lean relational and functional bisimulation
RuleSys/HML.lean          diamond-only Hennessy–Milner logic
RuleSys/PresheafTopos/    Grothendieck topologies, geometric closure
RuleSys/SubtoposLattice/  L₃₀ spectrum lattice, energy bridge, Birkhoff representation
AxiomAudit.lean           axiom audit for the results above
```

## Licence

Apache 2.0.
