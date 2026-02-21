# OSReconstruction

A Lean 4 formalization of the **Osterwalder-Schrader reconstruction theorem** and supporting infrastructure in **von Neumann algebra theory**, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Overview

This project formalizes the mathematical bridge between Euclidean and relativistic quantum field theory. The OS reconstruction theorem establishes that Schwinger functions (Euclidean correlators) satisfying certain axioms can be analytically continued to yield Wightman functions defining a relativistic QFT, and vice versa.

### Modules

- **`OSReconstruction.Wightman`** — Wightman axioms, Schwartz tensor products, Poincaré/Lorentz groups, spacetime geometry, GNS construction, analytic continuation (tube domains, Bargmann-Hall-Wightman, edge-of-the-wedge), Wick rotation, and the reconstruction theorems.

- **`OSReconstruction.vNA`** — Von Neumann algebra foundations: cyclic/separating vectors, predual theory, Tomita-Takesaki modular theory, modular automorphism groups, KMS condition, spectral theory via Riesz-Markov-Kakutani, unbounded self-adjoint operators, and Stone's theorem.

### Dependencies

- [**gaussian-field**](https://github.com/mrdouglasny/gaussian-field) — Sorry-free Hermite function basis, Schwartz-Hermite expansion, Dynin-Mityagin and Pietsch nuclear space definitions, spectral theorem for compact self-adjoint operators, nuclear SVD, and Gaussian measure construction on weak duals.

## Building

Requires [Lean 4](https://lean-lang.org/) and [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

This will fetch Mathlib and all dependencies automatically. The first build may take a while.

## Project Status

The project builds cleanly. The formalization uses 15 named axioms encoding textbook results from Vladimirov, Jost, Bochner, Osterwalder-Schrader, and Streater-Wightman; see [`PROGRESS_REPORT.md`](PROGRESS_REPORT.md) for the full list.

Remaining work is tracked via `sorry` placeholders (~86 total across 27 files):

| Area | Sorry-free highlights | Remaining `sorry`s |
|------|----------------------|---------------------|
| E'→R' bridge | `os_to_wightman_full`: sorry-free | 0 |
| R→E bridge | `wightman_to_os_full`: boundary values via axiom | 0 |
| R→E properties | E0 (tempered), E1 (translation + SO(d+1) rotation), E3 (permutation) | 2 |
| Lorentz invariance | `W_analytic_lorentz_on_tube` + 4 helper lemmas | 0 |
| Forward tube distributions | `ForwardTubeDistributions.lean` (591 lines) | 0 |
| E→R analytic continuation | Paley-Wiener axiom + Bochner tube theorem axiom | 8 |
| GNS construction | Inner product, field operators, reproducing property | 0 |
| 1D edge-of-the-wedge | Via Morera's theorem | 0 |
| Spacetime geometry | Minkowski metric, Lorentz/Poincaré groups | 0 |
| Modular theory | Tomita operator, modular operator/conjugation | ~9 |
| Modular automorphisms | σ_t, Connes cocycle | ~14 |
| KMS condition | Equilibrium states | ~11 |

See [`PROGRESS_REPORT.md`](PROGRESS_REPORT.md) for a detailed breakdown of axioms, sorry census, and proof strategies. See also [`OSReconstruction/vNA/TODO.md`](OSReconstruction/vNA/TODO.md) and [`OSReconstruction/Wightman/TODO.md`](OSReconstruction/Wightman/TODO.md) for execution plans.

## File Structure

```
OSReconstruction/
├── vNA/                          # Von Neumann algebra theory
│   ├── Basic.lean                # Cyclic/separating vectors, standard form
│   ├── Predual.lean              # Normal functionals, σ-weak topology
│   ├── Antilinear.lean           # Antilinear operator infrastructure
│   ├── ModularTheory.lean        # Tomita-Takesaki: S, Δ, J
│   ├── ModularAutomorphism.lean  # σ_t, Connes cocycle
│   ├── KMS.lean                  # KMS condition
│   ├── Spectral/                 # Spectral theory via RMK (sorry-free)
│   ├── Unbounded/                # Unbounded operators, spectral theorem, Stone
│   ├── MeasureTheory/            # Spectral integrals, Stieltjes, Carathéodory
│   └── Bochner/                  # Operator Bochner integrals
├── Wightman/                     # Wightman QFT
│   ├── Basic.lean                # Core definitions
│   ├── WightmanAxioms.lean       # Axiom formalization
│   ├── OperatorDistribution.lean # Operator-valued distributions
│   ├── SchwartzTensorProduct.lean# Schwartz space tensor products
│   ├── Groups/                   # Lorentz and Poincaré groups
│   ├── Spacetime/                # Minkowski geometry
│   ├── NuclearSpaces/            # Nuclear spaces, gaussian-field bridge
│   ├── SCV/                      # Several complex variables infrastructure
│   └── Reconstruction/           # The reconstruction theorems
│       ├── GNSConstruction.lean  # GNS construction (sorry-free)
│       ├── AnalyticContinuation.lean  # Tube domains, BHW, edge-of-wedge
│       ├── WickRotation.lean     # OS ↔ Wightman bridge
│       └── Helpers/              # EdgeOfWedge, SeparatelyAnalytic
└── Reconstruction.lean           # Top-level reconstruction theorems
```

## References

- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" I & II (1973, 1975)
- Streater-Wightman, "PCT, Spin and Statistics, and All That"
- Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
- Reed-Simon, "Methods of Modern Mathematical Physics" I
- Takesaki, "Theory of Operator Algebras" I, II, III

## License

This project is licensed under the Apache License 2.0 — see [LICENSE](LICENSE) for details.
