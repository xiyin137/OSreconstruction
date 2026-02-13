# OSReconstruction

A Lean 4 formalization of the **Osterwalder-Schrader reconstruction theorem** and supporting infrastructure in **von Neumann algebra theory**, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Overview

This project formalizes the mathematical bridge between Euclidean and relativistic quantum field theory. The OS reconstruction theorem establishes that Schwinger functions (Euclidean correlators) satisfying certain axioms can be analytically continued to yield Wightman functions defining a relativistic QFT, and vice versa.

### Modules

- **`OSReconstruction.Wightman`** — Wightman axioms, Schwartz tensor products, Poincaré/Lorentz groups, spacetime geometry, GNS construction, analytic continuation (tube domains, Bargmann-Hall-Wightman, edge-of-the-wedge), Wick rotation, and the reconstruction theorems.

- **`OSReconstruction.vNA`** — Von Neumann algebra foundations: cyclic/separating vectors, predual theory, Tomita-Takesaki modular theory, modular automorphism groups, KMS condition, spectral theory via Riesz-Markov-Kakutani, unbounded self-adjoint operators, and Stone's theorem.

## Building

Requires [Lean 4](https://lean-lang.org/) and [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

This will fetch Mathlib and all dependencies automatically. The first build may take a while.

## Project Status

The project builds cleanly. Remaining work is tracked via `sorry` placeholders:

| Area | Sorry-free highlights | Remaining `sorry`s |
|------|----------------------|---------------------|
| Spectral theory (RMK chain) | Full chain: functional, measure, theorem, Cayley, projections | 0 |
| Unbounded operators | Basic definitions, graph theory | 0 |
| GNS construction | Inner product, field operators, reproducing property | 0 |
| 1D edge-of-the-wedge | Via Morera's theorem | 0 |
| Schwartz tensor product | Full infrastructure | 0 |
| Spacetime geometry | Minkowski metric, Lorentz/Poincaré groups | 0 |
| Modular theory | Tomita operator, modular operator/conjugation | ~9 |
| Modular automorphisms | σ_t, Connes cocycle | ~13 |
| KMS condition | Equilibrium states | ~9 |
| Stone's theorem (inverse) | Generator construction | ~4 |
| OS reconstruction bridge | Wick rotation, analytic continuation | ~26 (critical path) |

See [`OSReconstruction/vNA/TODO.md`](OSReconstruction/vNA/TODO.md) and [`OSReconstruction/Wightman/TODO.md`](OSReconstruction/Wightman/TODO.md) for detailed status and execution plans.

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
│   ├── NuclearSpaces/            # Nuclear spaces, Bochner-Minlos (deferred)
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
