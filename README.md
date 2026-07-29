# RuleSys

Lean 4 formalisation of *A Classifying Topos for the Spectrum of Equivalences*
(https://arxiv.org/abs/2603.01056).

## Build

```bash
lake exe cache get
lake build RuleSys
```

The toolchain and every dependency revision are pinned in `lean-toolchain` and
`lake-manifest.json`. Building compiles the root module with all 117 submodules, so
`import RuleSys` brings the development into scope.

## Axioms

```bash
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` prints the axiom dependencies of the declarations corresponding to the
paper's main theorems. Each reports a subset of `propext`, `Classical.choice` and
`Quot.sound`.

## Licence

MIT. See `LICENSE`.
