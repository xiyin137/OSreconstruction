# OSReconstruction

A Lean 4 formalization of the **Osterwalder-Schrader reconstruction theorem**,
built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The verified proof package is **[`os-reconstruction/`](os-reconstruction/)**: a
self-contained source distribution pinned to Lean 4.33.0-rc1, with a Lean
contract guard, no `sorry`, and no project axioms. Its three reconstruction
theorems are checked by the standard Lean Comparator against an independent
Mathlib-only statement of the axioms. Start from
[`os-reconstruction/README.md`](os-reconstruction/README.md).

## Depending on this repository

```toml
[[require]]
name = "OSReconstruction"
git = "https://github.com/xiyin137/OSreconstruction.git"
subDir = "os-reconstruction"
```

`subDir` is required. The repository root is no longer a Lake package, so a
`require` that omits it fails rather than resolving to something else.

## The development tree

The package was extracted from a development tree that used to live at the
repository root, as a second Lake package also named `OSReconstruction`. Because
the two shared a name, a `require` without `subDir` silently selected the older
tree and its superseded specification.

That tree has been removed. It is preserved in history at
[`135ed13`](https://github.com/xiyin137/OSreconstruction/tree/135ed13df64ab2ba777475358e8d66ee983c291b),
which is also the comparison point used throughout
[`os-reconstruction/docs/CONTRACT_CHANGES.md`](os-reconstruction/docs/CONTRACT_CHANGES.md).

Two of its statements were found defective after extraction and are corrected in
the package. Both are worth knowing about before reading anything written
against the old tree:

- **Forward-tube growth.** The old `spectrum_condition` bounded the analytic
  continuation by `C(1+‖z‖)^N` on the *entire* forward tube. That clause is
  unsatisfiable for the free field, so the hypothesis class it defined excluded
  the intended models. The package states
  `ForwardTubeAnalyticityCompactSubset` — polynomial in the real part, uniform
  on compact sets of imaginary parts in the open cone — and carries positive
  energy separately, in a mandatory `spectral_support` field.
- **Euclidean growth.** The old `OSLinearGrowthCondition` used a single pair of
  Sobolev orders `(s, s)` at every arity. At arity zero that conflicts with its
  own normalization `S₀(f) = f(0)`, forcing `s = 0`. The package uses an
  arity-linear condition whose order grows with `n`.

`DEFINITIONS.md` went with it, being an index of files that no longer exist.
The prose left at the root — `docs/`, `Proofideas/`, `communication/`,
`history/`, `GAUSSIAN_FIELD_INTEGRATION.md`, and
`os_reconstruction_lean_proof_notes.tex` — are working notes from that effort.
They are kept for provenance, describe the old tree, and are not maintained.

## References

- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" I & II (1973, 1975)
- Streater-Wightman, "PCT, Spin and Statistics, and All That"
- Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
- Reed-Simon, "Methods of Modern Mathematical Physics" I
- Takesaki, "Theory of Operator Algebras" I, II, III

## License

This project is licensed under the Apache License 2.0 — see [LICENSE](LICENSE) for details.
