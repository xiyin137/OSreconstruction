# Vladimirov-Tillmann Proof: File Guide

## What this proves

The Paley-Wiener-Schwartz analytical core of the Vladimirov-Tillmann theorem:
a holomorphic function on a tube domain with tempered distributional boundary
values has polynomial growth (the Vladimirov bound).

**Input axioms (3):**
1. `schwartz_clm_fubini_exchange` — CLM commutes with Schwartz-valued integrals
2. `bv_implies_fourier_support` — BV implies dual-cone Fourier support
3. `tube_holomorphic_unique_from_bv` — uniqueness from boundary values

**Output theorems (~30):** All Schwartz seminorm estimates, the Vladimirov
pointwise bound, BV convergence of the Fourier-Laplace extension, and
supporting infrastructure. ~10K lines, 0 sorrys.

## New files

### SCV/ (Several Complex Variables)

| File | Lines | Description |
|------|-------|-------------|
| `ConeDefs.lean` | ~35 | `IsCone`, `IsSalientCone`, `TubeDomainSetPi` (extracted to break import cycles) |
| `DualCone.lean` | ~220 | Dual cone properties, Hahn-Banach separation, `FixedConeCutoff` |
| `ConeCutoffSchwartz.lean` | ~900 | Concrete ψ_{z,R} construction, all decay estimates, coercivity |
| `FourierSupportCone.lean` | ~230 | `HasFourierSupportInDualCone`, Fourier support theorems |
| `PaleyWienerSchwartz.lean` | ~3500 | **Main file**: all PW seminorm bounds, Vladimirov pointwise bound, BV convergence, physicsFourierFlatCLM |
| `TubeBoundaryValueExistence.lean` | ~1200 | Tube slice temperedness, CR identity, M=0 BV existence (proved), M>0 (axiom) |
| `VladimirovProof.lean` | ~80 | Consistency proof for the axiom package |

### GeneralResults/ (Pure functional analysis)

| File | Lines | Description |
|------|-------|-------------|
| `ScalarFTC.lean` | ~125 | FTC identities: exp(w)-1 and exp(w)-1-w as integrals + norm bounds |
| `SchwartzCutoffExp.lean` | ~700 | Quantitative seminorm bounds for cutoff × exponential |
| `SchwartzDamping.lean` | ~460 | exp(-εL)·h → h in Schwartz topology |
| `SchwartzFubini.lean` | ~75 | CLM-integral exchange axiom |
| `SmoothCutoff.lean` | ~180 | Smooth cutoff adapted to closed sets via convolution mollifier |
| `DiffUnderIntegralSchwartz.lean` | ~180 | Differentiation under the integral for Schwartz pairings |
| `DistributionalLimit.lean` | ~130 | Equicontinuous families → distributional limits |

### Modified files

| File | Change |
|------|--------|
| `VladimirovTillmann.lean` | Added 2 new SCV axioms, imported PW, extracted ConeDefs |

## Dependency DAG

```
ConeDefs ← DualCone ← ConeCutoffSchwartz ← PaleyWienerSchwartz
                                              ↑
SmoothCutoff ← DualCone                      |
SchwartzCutoffExp ─────────────────────────→──┘
ScalarFTC ─────────────────────────────────→──┘
SchwartzDamping ───────────────────────────→──┘
SchwartzFubini ────────────────────────────→──┘
DiffUnderIntegralSchwartz ─────────────────→──┘
DistributionalLimit ───────────────────────→──┘
                                              ↓
PaleyWienerSchwartz → FourierSupportCone → VladimirovTillmann
```

## References

- Vladimirov, "Methods of the Theory of Generalized Functions" (2002), §25
- Hörmander, "The Analysis of Linear PDOs I" (1990), §7.4
- Streater & Wightman, "PCT, Spin and Statistics, and All That", Ch. 2
- Reed-Simon I, §V.3, §IX.3
