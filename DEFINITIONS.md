# OSReconstruction: Definitions Index

A comprehensive index of all definitions in the OSReconstruction Lean 4 project, organized by module.

---

## Wightman / Spacetime

### Metric (`Wightman/Spacetime/Metric.lean`)

| Definition | Line | Description |
|---|---|---|
| `MinkowskiSpace` | [56](OSReconstruction/Wightman/Spacetime/Metric.lean#L56) | Minkowski space `ℝ^{1,d}` as a `(d+1)`-dimensional real vector space |
| `metricSignature` | [64](OSReconstruction/Wightman/Spacetime/Metric.lean#L64) | The Minkowski metric signature `η = diag(−1, +1, …, +1)` (mostly-plus convention) |
| `minkowskiInner` | [93](OSReconstruction/Wightman/Spacetime/Metric.lean#L93) | The Minkowski inner product `η(x, y) = −x₀y₀ + x₁y₁ + ⋯ + x_dy_d` |
| `minkowskiNormSq` | [97](OSReconstruction/Wightman/Spacetime/Metric.lean#L97) | The Minkowski quadratic form `η(x, x) = −x₀² + ‖x_spatial‖²` |
| `timeComponent` | [164](OSReconstruction/Wightman/Spacetime/Metric.lean#L164) | The time component `x⁰` of a Minkowski space vector |
| `spatialComponents` | [167](OSReconstruction/Wightman/Spacetime/Metric.lean#L167) | The spatial components `(x¹, …, xᵈ)` of a Minkowski space vector |
| `ofTimeSpace` | [170](OSReconstruction/Wightman/Spacetime/Metric.lean#L170) | Constructs a Minkowski space vector from a time component and spatial components |
| `IsTimelike` | [197](OSReconstruction/Wightman/Spacetime/Metric.lean#L197) | A vector is timelike if `η(x, x) < 0` |
| `IsSpacelike` | [201](OSReconstruction/Wightman/Spacetime/Metric.lean#L201) | A vector is spacelike if `η(x, x) > 0` |
| `IsLightlike` | [205](OSReconstruction/Wightman/Spacetime/Metric.lean#L205) | A vector is lightlike (null) if `η(x, x) = 0` |
| `IsCausal` | [209](OSReconstruction/Wightman/Spacetime/Metric.lean#L209) | A vector is causal if `η(x, x) ≤ 0` |
| `AreSpacelikeSeparated` | [213](OSReconstruction/Wightman/Spacetime/Metric.lean#L213) | Two spacetime points are spacelike separated if their difference is spacelike |
| `IsFutureDirected` | [217](OSReconstruction/Wightman/Spacetime/Metric.lean#L217) | A vector is future-directed if `x⁰ > 0` |
| `ForwardLightCone` | [225](OSReconstruction/Wightman/Spacetime/Metric.lean#L225) | The forward light cone: causal vectors with `x⁰ ≥ 0` |
| `OpenForwardLightCone` | [229](OSReconstruction/Wightman/Spacetime/Metric.lean#L229) | The open forward light cone: timelike future-directed vectors |
| `ClosedForwardLightCone` | [233](OSReconstruction/Wightman/Spacetime/Metric.lean#L233) | The closed forward light cone |
| `BackwardLightCone` | [237](OSReconstruction/Wightman/Spacetime/Metric.lean#L237) | The backward light cone: causal vectors with `x⁰ ≤ 0` |
| `minkowskiMatrix` | [273](OSReconstruction/Wightman/Spacetime/Metric.lean#L273) | The Minkowski metric as a diagonal matrix `η = diag(−1, +1, …, +1)` |

### Minkowski Geometry (`Wightman/Spacetime/MinkowskiGeometry.lean`)

| Definition | Line | Description |
|---|---|---|
| `spatialNormSq` | [49](OSReconstruction/Wightman/Spacetime/MinkowskiGeometry.lean#L49) | Spatial squared norm `∑ᵢ (xᵢ)²` over spatial indices |
| `spatialInner` | [84](OSReconstruction/Wightman/Spacetime/MinkowskiGeometry.lean#L84) | Spatial inner product `∑ᵢ xᵢ yᵢ` over spatial indices |
| `complexMinkowskiQuadratic` | [179](OSReconstruction/Wightman/Spacetime/MinkowskiGeometry.lean#L179) | Complex Minkowski quadratic form `Q(ζ) = ∑_μ η_μ ζ_μ²` for complex vectors |

---

## Wightman / Groups

### Lorentz Group (`Wightman/Groups/Lorentz.lean`)

| Definition | Line | Description |
|---|---|---|
| `IsLorentzMatrix` | [54](OSReconstruction/Wightman/Groups/Lorentz.lean#L54) | Predicate: a matrix preserves the Minkowski metric `Λᵀ η Λ = η` |
| `LorentzGroup` | [275](OSReconstruction/Wightman/Groups/Lorentz.lean#L275) | The Lorentz group `O(1,d)` as a subtype of matrices preserving `η` |
| `IsProper` | [357](OSReconstruction/Wightman/Groups/Lorentz.lean#L357) | A Lorentz transformation has `det Λ = 1` |
| `IsOrthochronous` | [361](OSReconstruction/Wightman/Groups/Lorentz.lean#L361) | A Lorentz transformation has `Λ₀₀ ≥ 1` (preserves time direction) |
| `Restricted` | [535](OSReconstruction/Wightman/Groups/Lorentz.lean#L535) | The restricted Lorentz group `SO⁺(1,d)`: proper orthochronous transformations |
| `parity` | [546](OSReconstruction/Wightman/Groups/Lorentz.lean#L546) | Space inversion `P = diag(+1, −1, …, −1)` |
| `timeReversal` | [576](OSReconstruction/Wightman/Groups/Lorentz.lean#L576) | Time reversal `T = diag(−1, +1, …, +1)` |
| `Lorentz4` | [623](OSReconstruction/Wightman/Groups/Lorentz.lean#L623) | Abbreviation for the 3+1 dimensional Lorentz group |

### Poincare Group (`Wightman/Groups/Poincare.lean`)

| Definition | Line | Description |
|---|---|---|
| `PoincareGroup` | [55](OSReconstruction/Wightman/Groups/Poincare.lean#L55) | The Poincare group `ISO(1,d)` as pairs `(translation, Lorentz)` with semidirect product |
| `act` | [145](OSReconstruction/Wightman/Groups/Poincare.lean#L145) | Poincare group action on spacetime: `x ↦ Λx + a` |
| `translation'` | [169](OSReconstruction/Wightman/Groups/Poincare.lean#L169) | A pure translation element `(a, 1)` |
| `lorentz'` | [173](OSReconstruction/Wightman/Groups/Poincare.lean#L173) | A pure Lorentz transformation element `(0, Λ)` |
| `IsRestricted` | [208](OSReconstruction/Wightman/Groups/Poincare.lean#L208) | Poincare element whose Lorentz part is proper orthochronous |
| `Poincare4` | [230](OSReconstruction/Wightman/Groups/Poincare.lean#L230) | Abbreviation for the 3+1 dimensional Poincare group |

---

## Wightman / Operator-Valued Distributions and Axioms

### Operator-Valued Distributions (`Wightman/OperatorDistribution.lean`)

| Definition | Line | Description |
|---|---|---|
| `SpacetimeDim` | [56](OSReconstruction/Wightman/OperatorDistribution.lean#L56) | Spacetime dimension type `Fin(d+1) → ℝ` |
| `SchwartzSpacetime` | [59](OSReconstruction/Wightman/OperatorDistribution.lean#L59) | Schwartz space on `(d+1)`-dimensional spacetime with complex values |
| `DenseSubspace` | [63](OSReconstruction/Wightman/OperatorDistribution.lean#L63) | A dense subspace of a Hilbert space, used as common domain for field operators |
| `OperatorValuedDistribution` | [98](OSReconstruction/Wightman/OperatorDistribution.lean#L98) | Operator-valued distribution: maps Schwartz test functions to operators on a Hilbert space |
| `matrixElement` | [129](OSReconstruction/Wightman/OperatorDistribution.lean#L129) | The matrix element `f ↦ ⟨χ, φ(f) ψ⟩` for fixed vectors in the domain |
| `IsHermitian` | [137](OSReconstruction/Wightman/OperatorDistribution.lean#L137) | Field hermiticity: `⟨φ(f)χ, ψ⟩ = ⟨χ, φ(f̄)ψ⟩` |
| `algebraicSpan` | [163](OSReconstruction/Wightman/OperatorDistribution.lean#L163) | States reachable from vacuum by field operator applications |
| `WightmanNPoint` | [172](OSReconstruction/Wightman/OperatorDistribution.lean#L172) | Wightman n-point function `W_n(f₁,…,fₙ) = ⟨Ω, φ(f₁)⋯φ(fₙ) Ω⟩` |
| `PoincareRepresentation` | [286](OSReconstruction/Wightman/OperatorDistribution.lean#L286) | Unitary representation of the Poincare group on a Hilbert space |
| `translationContinuousInDirection` | [311](OSReconstruction/Wightman/OperatorDistribution.lean#L311) | Strong continuity predicate for the one-parameter translation subgroup in a fixed spacetime direction |
| `translationStronglyContinuous` | [315](OSReconstruction/Wightman/OperatorDistribution.lean#L315) | Strong continuity of all one-parameter translation subgroups |
| `momentum` | [332](OSReconstruction/Wightman/OperatorDistribution.lean#L332) | Energy-momentum operator `P_μ`, generator of translations |
| `hamiltonian` | [343](OSReconstruction/Wightman/OperatorDistribution.lean#L343) | Hamiltonian `H = P₀`, generator of time translations |
| `spatialMomentum` | [347](OSReconstruction/Wightman/OperatorDistribution.lean#L347) | Spatial momentum operators `Pᵢ`, generators of spatial translations |
| `momentumOp` | [473](OSReconstruction/Wightman/OperatorDistribution.lean#L473) | Stone-theorem momentum operator as an `UnboundedOperator`, defined from the generator of the strongly continuous translation subgroup |
| `hamiltonianOp` | [478](OSReconstruction/Wightman/OperatorDistribution.lean#L478) | Stone-theorem Hamiltonian `P₀` as an `UnboundedOperator` |
| `spatialMomentumOp` | [484](OSReconstruction/Wightman/OperatorDistribution.lean#L484) | Stone-theorem spatial momentum operator `Pᵢ` as an `UnboundedOperator` |

### Wightman Axioms (`Wightman/WightmanAxioms.lean`)

| Definition | Line | Description |
|---|---|---|
| `ForwardMomentumCone` | [66](OSReconstruction/Wightman/WightmanAxioms.lean#L66) | Closed forward light cone in momentum space: `p⁰ ≥ 0` and `p² ≤ 0` |
| `SpectralCondition` | [83](OSReconstruction/Wightman/WightmanAxioms.lean#L83) | Legacy weak spectrum-condition surface expressed using everywhere-defined Hamiltonian and spatial-momentum maps |
| `ComplexSpacetime` | [95](OSReconstruction/Wightman/WightmanAxioms.lean#L95) | Complexified spacetime `Fin(d+1) → ℂ` used for translation matrix coefficients |
| `TranslationForwardTube` | [99](OSReconstruction/Wightman/WightmanAxioms.lean#L99) | One-point forward tube `{ z ∈ ℂ^(d+1) | Im z ∈ V₊^open }` |
| `MatrixElementSpectralCondition` | [108](OSReconstruction/Wightman/WightmanAxioms.lean#L108) | Stone-compatible matrix-element spectral condition: strong continuity plus forward-tube holomorphic continuation of translation matrix coefficients (kept as legacy; see `SpectralConditionQFT`) |
| `SpectralConditionQFT` | [141](OSReconstruction/Wightman/WightmanAxioms.lean#L141) | Streater-Wightman Axiom II: P₀ ≥ 0 and P₀² ≥ Σᵢ Pᵢ² on Stone-generator domains, with strong continuity of translations. Used as the `WightmanQFT.spectrum_condition` field |
| `IsLocal` | [186](OSReconstruction/Wightman/WightmanAxioms.lean#L186) | Locality (microcausality): spacelike-separated fields commute |
| `WightmanQFT` | [217](OSReconstruction/Wightman/WightmanAxioms.lean#L217) | Complete Wightman QFT structure bundling Hilbert space, Poincare rep, vacuum, fields, and axioms; its `spectrum_condition` field uses `SpectralConditionQFT` |
| `InOpenForwardCone` | [579](OSReconstruction/Wightman/WightmanAxioms.lean#L579) | Predicate for membership in the open forward light cone: `η⁰ > 0` and `η² < 0` |
| `ForwardTube` | [604](OSReconstruction/Wightman/WightmanAxioms.lean#L604) | The forward tube `T_n`: complex configurations with successive imaginary differences in `V⁺` |
| `ExtendedForwardTube` | [650](OSReconstruction/Wightman/WightmanAxioms.lean#L650) | Extended forward tube `T'_n = ⋃_{Λ ∈ SO⁺} Λ(T_n)` |
| `wickRotatePoint` | [658](OSReconstruction/Wightman/WightmanAxioms.lean#L658) | Wick rotation `(τ, x⃗) ↦ (iτ, x⃗)` |
| `WightmanAnalyticity` | [679](OSReconstruction/Wightman/WightmanAxioms.lean#L679) | Analytic continuation of Wightman functions to the forward tube with distributional boundary values |

---

## Wightman / Reconstruction

### Core (`Wightman/Reconstruction/Core.lean`)

| Definition | Line | Description |
|---|---|---|
| `NPointDomain` | [66](OSReconstruction/Wightman/Reconstruction/Core.lean#L66) | Space of n-tuples of spacetime points `Fin n → SpacetimeDim d` |
| `SchwartzNPoint` | [69](OSReconstruction/Wightman/Reconstruction/Core.lean#L69) | Schwartz space of complex-valued test functions on n copies of spacetime |
| `BorchersSequence` | [156](OSReconstruction/Wightman/Reconstruction/Core.lean#L156) | Finitely supported sequence of Schwartz n-point test functions, forming the Borchers algebra |
| `WightmanInnerProduct` | [279](OSReconstruction/Wightman/Reconstruction/Core.lean#L279) | Sesquilinear form `⟨F, G⟩ = ∑_{n,m} W_{n+m}(f_n* ⊗ g_m)` on Borchers sequences |
| `IsPositiveDefinite` | [537](OSReconstruction/Wightman/Reconstruction/Core.lean#L537) | Wightman inner product is positive semi-definite |
| `WightmanFunctions` | [548](OSReconstruction/Wightman/Reconstruction/Core.lean#L548) | Complete structure bundling n-point distributions with all Wightman axioms |
| `borchersSetoid` | [822](OSReconstruction/Wightman/Reconstruction/Core.lean#L822) | GNS equivalence relation identifying null-norm Borchers sequences |
| `PreHilbertSpace` | [883](OSReconstruction/Wightman/Reconstruction/Core.lean#L883) | Quotient of Borchers sequences by the GNS null-space |
| `vacuum` | [964](OSReconstruction/Wightman/Reconstruction/Core.lean#L964) | Vacuum vector in the pre-Hilbert space |
| `fieldOperator` | [1158](OSReconstruction/Wightman/Reconstruction/Core.lean#L1158) | Smeared field operator `φ(f)` acting by prepending a test function |
| `PositiveTimeRegion` | [1212](OSReconstruction/Wightman/Reconstruction/Core.lean#L1212) | Set of n-point configurations where all time coordinates are strictly positive |
| `CoincidenceLocus` | [1232](OSReconstruction/Wightman/Reconstruction/Core.lean#L1232) | Points where at least two spacetime arguments coincide |
| `VanishesToInfiniteOrderOnCoincidence` | [1279](OSReconstruction/Wightman/Reconstruction/Core.lean#L1279) | A test function and all derivatives vanish on the coincidence locus |
| `ZeroDiagonalSchwartz` | [2254](OSReconstruction/Wightman/Reconstruction/Core.lean#L2254) | OS-I zero-diagonal test space: Schwartz functions vanishing to infinite order on the coincidence locus |
| `SchwingerFunctions` | [2491](OSReconstruction/Wightman/Reconstruction/Core.lean#L2491) | Euclidean correlation functionals on the zero-diagonal test space |
| `timeReflection` | [2517](OSReconstruction/Wightman/Reconstruction/Core.lean#L2517) | Euclidean time reflection `θ : (τ, x⃗) ↦ (−τ, x⃗)` |
| `SchwartzNPoint.osConj` | [2738](OSReconstruction/Wightman/Reconstruction/Core.lean#L2738) | OS conjugation: time reflection + complex conjugation |

### GNS Construction (`Wightman/Reconstruction/GNSHilbertSpace.lean`)

| Definition | Line | Description |
|---|---|---|
| `GNSHilbertSpace` | [313](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L313) | Cauchy completion of the pre-Hilbert space — the reconstructed Hilbert space |
| `gnsVacuum` | [316](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L316) | Vacuum vector in the GNS Hilbert space |
| `gnsPoincareRep` | [501](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L501) | Unitary Poincare representation on the GNS Hilbert space |
| `gnsFieldOp` | [568](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L568) | Smeared field operator on the GNS Hilbert space |
| `gnsDomain` | [612](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L612) | Dense subspace domain for field operators in the GNS Hilbert space |
| `gnsQFT` | [826](OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean#L826) | Fully assembled `WightmanQFT` from the GNS reconstruction |

### Schwinger–OS Axioms (`Wightman/Reconstruction/SchwingerOS.lean`)

| Definition | Line | Description |
|---|---|---|
| `OSInnerProduct` | [26](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L26) | Euclidean inner product `⟨F, G⟩_OS = ∑ S_{n+m}((θf̄_n) ⊗ g_m)` |
| `PositiveTimeBorchersSequence` | [223](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L223) | Borchers sequence supported in the ordered positive-time region |
| `OsterwalderSchraderAxioms` | [721](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L721) | Structure encoding OS axioms (E0–E4) for Euclidean Schwinger functions |
| `OSLinearGrowthCondition` | [1816](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L1816) | OS-II linear growth condition (E0') controlling factorial growth of distribution orders |
| `OSPreHilbertSpace` | [2109](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L2109) | Quotient of positive-time Borchers sequences by the OS null-space |
| `IsWickRotationPair` | [2430](OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean#L2430) | Schwinger and Wightman functions related by analytic continuation through the forward tube |

### Analytic Continuation (`Wightman/Reconstruction/AnalyticContinuation.lean`)

| Definition | Line | Description |
|---|---|---|
| `ComplexExtendedForwardTube` | [110](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L110) | Extended forward tube via the complex Lorentz group |
| `PermutedExtendedTube` | [130](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L130) | Union over all permutations and complex Lorentz transforms of permuted forward tubes |
| `IsEuclidean` | [168](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L168) | Complex configuration with purely imaginary time and real spatial components |
| `IsJostPoint` | [756](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L756) | A real point in the extended tube where all differences are spacelike |
| `SchwingerFromWightman` | [875](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L875) | Schwinger functions defined from analytic continuation at Wick-rotated points |
| `complexWickRotate` | [886](OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean#L886) | Holomorphic Wick rotation `(z₀, z₁,…) ↦ (iz₀, z₁,…)` |

### Wick Rotation (`Wightman/Reconstruction/WickRotation/`)

| Definition | File | Line | Description |
|---|---|---|---|
| `constructSchwingerFunctions` | [BHWTranslation.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/BHWTranslation.lean#L1386) | 1386 | Constructs OS-I Schwinger functions from Wightman functions via Wick-rotated BHW continuation |
| `constructWightmanFunctions` | [OSToWightmanBoundaryValues.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean#L547) | 547 | Constructs `WightmanFunctions` from OS axioms via distributional boundary values |
| `W_analytic_BHW` | [BHWExtension.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean#L268) | 268 | BHW holomorphic extension from forward tube to permuted extended tube |
| `reducedWightman` | [BHWReduced.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/BHWReduced.lean#L348) | 348 | Reduced Wightman functional in `(n−1)` difference variables |
| `EuclideanSemigroup` | [OSToWightmanSemigroup.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean#L70) | 70 | Contraction semigroup `{T(t)}_{t>0}` on the OS pre-Hilbert space, generating the Hamiltonian |
| `OSHilbertSpace` | [OSToWightmanSemigroup.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean#L2074) | 2074 | Cauchy completion of the OS pre-Hilbert space |
| `osTimeShiftHilbert` | [OSToWightmanSemigroup.lean](OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean#L2101) | 2101 | Euclidean time-shift operator extended to the completed OS Hilbert space |

### Spectral Equivalence (`Wightman/SpectralEquivalence.lean`)

| Definition | Line | Description |
|---|---|---|
| `ProductForwardMomentumCone` | [40](OSReconstruction/Wightman/SpectralEquivalence.lean#L40) | Product of closed forward light cones V̄₊ⁿ in momentum space |
| `SchwartzNPointSpace.fourierTransform` | [68](OSReconstruction/Wightman/SpectralEquivalence.lean#L68) | Fourier transform on n-point Schwartz space via transfer to EuclideanSpace |
| `diffVarReduction` | [125](OSReconstruction/Wightman/SpectralEquivalence.lean#L125) | Reduction to difference variables: precomposes with zero-basepoint section, `ξⱼ = xⱼ₊₁ - xⱼ` |
| `SpectralConditionDistribution` | [140](OSReconstruction/Wightman/SpectralEquivalence.lean#L140) | Momentum-space spectral condition: reduced Wightman distributions have Fourier support in V̄₊ⁿ |
| `ForwardTubeAnalyticity` | [156](OSReconstruction/Wightman/SpectralEquivalence.lean#L156) | Coordinate-space spectral condition: n-point functions extend holomorphically to the forward tube with distributional boundary values |
| `ProductForwardTube` | [176](OSReconstruction/Wightman/SpectralEquivalence.lean#L176) | Product forward tube in difference coordinates `{ ζ | ∀ k, Im(ζₖ) ∈ V⁺ }` |

### Schwartz Tensor Products (`Wightman/SchwartzTensorProduct.lean`)

| Definition | Line | Description |
|---|---|---|
| `SchwartzMap.conj` | [57](OSReconstruction/Wightman/SchwartzTensorProduct.lean#L57) | Pointwise complex conjugation of a Schwartz function |
| `SchwartzMap.reverse` | [107](OSReconstruction/Wightman/SchwartzTensorProduct.lean#L107) | Reversal of argument ordering in a Schwartz function |
| `SchwartzMap.borchersConj` | [183](OSReconstruction/Wightman/SchwartzTensorProduct.lean#L183) | Borchers conjugation: reverse arguments + complex conjugate |
| `SchwartzMap.tensorProduct` | [314](OSReconstruction/Wightman/SchwartzTensorProduct.lean#L314) | External tensor product `(f ⊗ g)(x₁,…,x_{m+k}) = f(x₁,…,xₘ) · g(x_{m+1},…,x_{m+k})` |
| `SchwartzMap.productTensor` | [1475](OSReconstruction/Wightman/SchwartzTensorProduct.lean#L1475) | Product tensor `(f₁ ⊗ ⋯ ⊗ fₙ)(x₁,…,xₙ) = f₁(x₁) · ⋯ · fₙ(xₙ)` |

### Nuclear Spaces (`Wightman/NuclearSpaces/`)

| Definition | File | Line | Description |
|---|---|---|---|
| `IsNuclearOperator` | [NuclearOperator.lean](OSReconstruction/Wightman/NuclearSpaces/NuclearOperator.lean#L75) | 75 | A bounded map admits a nuclear representation `T(x) = ∑ fₙ(x) yₙ` with `∑ ‖fₙ‖‖yₙ‖ < ∞` |
| `NuclearSpace` | [NuclearSpace.lean](OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean#L64) | 64 | A locally convex space is nuclear (Pietsch characterization) |
| `IsPositiveDefiniteFn` | [BochnerMinlos.lean](OSReconstruction/Wightman/NuclearSpaces/BochnerMinlos.lean#L75) | 75 | A function `φ` is positive-definite on an abelian group |
| `CharacteristicFunctional` | [BochnerMinlos.lean](OSReconstruction/Wightman/NuclearSpaces/BochnerMinlos.lean#L189) | 189 | Continuous positive-definite functional with `C(0) = 1`, generalizing the Fourier transform of a probability measure |
| `gaussianCharacteristicFunctional` | [BochnerMinlos.lean](OSReconstruction/Wightman/NuclearSpaces/BochnerMinlos.lean#L520) | 520 | Gaussian characteristic functional `C(f) = exp(−½ ⟨f, Af⟩)` |
| `IsRealPSDKernel` | [PositiveDefiniteKernels.lean](OSReconstruction/Wightman/NuclearSpaces/Helpers/PositiveDefiniteKernels.lean#L40) | 40 | Real-valued positive semi-definite kernel |

---

## Wightman / Bridge

### Axiom Bridge (`Bridge/AxiomBridge.lean`)

| Definition | Line | Description |
|---|---|---|
| `lorentzGroupEquiv` | [75](OSReconstruction/Bridge/AxiomBridge.lean#L75) | Equivalence `≃` between `LorentzLieGroup.LorentzGroup` and `LorentzGroup` |
| `restrictedLorentzGroupToWightman` | [109](OSReconstruction/Bridge/AxiomBridge.lean#L109) | Converts `RestrictedLorentzGroup` (LorentzLieGroup) to `LorentzGroup.Restricted` (Wightman) |
| `wightmanToRestrictedLorentzGroup` | [118](OSReconstruction/Bridge/AxiomBridge.lean#L118) | Converts `LorentzGroup.Restricted` (Wightman) to `RestrictedLorentzGroup` (LorentzLieGroup) |

---

## Complex Lie Groups

### Lorentz Lie Group (`ComplexLieGroups/LorentzLieGroup.lean`)

| Definition | Line | Description |
|---|---|---|
| `minkowskiSignature` | [57](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L57) | Metric signature `(−1, +1, …, +1)` |
| `minkowskiMatrix` | [61](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L61) | Minkowski metric matrix `η = diag(−1, +1, …, +1)` |
| `IsLorentzMatrix` | [80](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L80) | Predicate: `Λᵀ η Λ = η` |
| `LorentzGroup` | [100](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L100) | Full Lorentz group `O(1,d)` |
| `RestrictedLorentzGroup` | [216](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L216) | Restricted Lorentz group `SO⁺(1,d)`: proper and orthochronous |
| `IsInLorentzAlgebra` | [285](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L285) | Lie algebra condition `Xᵀη + ηX = 0` |
| `expLorentz` | [408](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L408) | Exponentiates a Lie algebra element to `SO⁺(1,d)` |
| `planarBoost` | [654](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L654) | Lorentz boost matrix in the `(0, k+1)` plane with rapidity `β` |
| `spatialRot` | [889](OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean#L889) | Spatial rotation matrix in the `(i+1, j+1)` plane by angle `θ` |

### Complex Lorentz Group (`ComplexLieGroups/Complexification.lean`)

| Definition | Line | Description |
|---|---|---|
| `ComplexLorentzGroup` | [61](OSReconstruction/ComplexLieGroups/Complexification.lean#L61) | Complex Lorentz group `SO⁺(1,d; ℂ)`: complex matrices preserving `η` with `det = 1` |
| `ηℂ` | [95](OSReconstruction/ComplexLieGroups/Complexification.lean#L95) | Complex Minkowski metric `diag(−1, +1, …, +1)` over `ℂ` |
| `ofReal` | [344](OSReconstruction/ComplexLieGroups/Complexification.lean#L344) | Embedding `SO⁺(1,d; ℝ) ↪ SO⁺(1,d; ℂ)` |
| `ofEuclidean` | [372](OSReconstruction/ComplexLieGroups/Complexification.lean#L372) | Embedding `SO(d+1; ℝ) ↪ SO⁺(1,d; ℂ)` via Wick rotation conjugation |
| `IsInLieAlgebra` | [464](OSReconstruction/ComplexLieGroups/Complexification.lean#L464) | Complex Lie algebra condition `Xᵀη + ηX = 0` |
| `expLieAlg` | [579](OSReconstruction/ComplexLieGroups/Complexification.lean#L579) | Exponentiates complex Lie algebra element to `SO⁺(1,d; ℂ)` |
| `toSOComplex` | [669](OSReconstruction/ComplexLieGroups/Complexification.lean#L669) | Wick rotation isomorphism to `SO(d+1; ℂ)` |

### SO(n; ℂ) (`ComplexLieGroups/SOConnected.lean`)

| Definition | Line | Description |
|---|---|---|
| `SOComplex` | [52](OSReconstruction/ComplexLieGroups/SOConnected.lean#L52) | Special complex orthogonal group `SO(n; ℂ)`: `AᵀA = I`, `det A = 1` |
| `IsSkewSymm` | [129](OSReconstruction/ComplexLieGroups/SOConnected.lean#L129) | Predicate: `Xᵀ = −X` (skew-symmetric) |
| `expSkew` | [189](OSReconstruction/ComplexLieGroups/SOConnected.lean#L189) | Exponentiates a skew-symmetric matrix to `SO(n; ℂ)` |
| `rotMatrix` | [289](OSReconstruction/ComplexLieGroups/SOConnected.lean#L289) | Givens rotation in the `(i,j)`-plane |

### BHW Core (`ComplexLieGroups/BHWCore.lean`)

| Definition | Line | Description |
|---|---|---|
| `ForwardTube` | [28](OSReconstruction/ComplexLieGroups/BHWCore.lean#L28) | Forward tube `T_n`: successive imaginary differences lie in `V⁺` |
| `complexLorentzAction` | [35](OSReconstruction/ComplexLieGroups/BHWCore.lean#L35) | Complex Lorentz group action on n-point configurations |
| `ExtendedTube` | [117](OSReconstruction/ComplexLieGroups/BHWCore.lean#L117) | Extended tube: union of complex Lorentz orbits of `T_n` |
| `PermutedExtendedTube` | [127](OSReconstruction/ComplexLieGroups/BHWCore.lean#L127) | Permuted extended tube `T''_n`: union over all permutations and Lorentz transforms |

### Geodesic Convexity (`ComplexLieGroups/GeodesicConvexity.lean`)

| Definition | Line | Description |
|---|---|---|
| `InOpenForwardCone` | [41](OSReconstruction/ComplexLieGroups/GeodesicConvexity.lean#L41) | Membership in the open forward light cone: `η⁰ > 0` and `∑ η_μ² ηᵘ < 0` |
| `conjLG` | [514](OSReconstruction/ComplexLieGroups/GeodesicConvexity.lean#L514) | Entrywise complex conjugation on `SO⁺(1,d; ℂ)` |

### Jost Points (`ComplexLieGroups/JostPoints.lean`)

| Definition | Line | Description |
|---|---|---|
| `IsSpacelike` | [58](OSReconstruction/ComplexLieGroups/JostPoints.lean#L58) | A real vector is spacelike (Minkowski norm² > 0) |
| `JostSet` | [150](OSReconstruction/ComplexLieGroups/JostPoints.lean#L150) | Set of real configurations where all points and pairwise differences are spacelike |
| `ForwardJostSet` | [266](OSReconstruction/ComplexLieGroups/JostPoints.lean#L266) | Configurations with consecutive differences having spatial component exceeding time component |

### Difference Coordinates (`ComplexLieGroups/DifferenceCoordinates.lean`)

| Definition | Line | Description |
|---|---|---|
| `diffCoordFun` | [53](OSReconstruction/ComplexLieGroups/DifferenceCoordinates.lean#L53) | Difference-coordinate map `L`: `L(z)(0) = z(0)`, `L(z)(k) = z(k) − z(k−1)` |
| `partialSumFun` | [61](OSReconstruction/ComplexLieGroups/DifferenceCoordinates.lean#L61) | Inverse `L⁻¹`: partial sums recovering original coordinates |
| `diffCoordLinearEquiv` | [145](OSReconstruction/ComplexLieGroups/DifferenceCoordinates.lean#L145) | Difference coordinates as a complex linear equivalence |
| `ProductForwardCone` | [222](OSReconstruction/ComplexLieGroups/DifferenceCoordinates.lean#L222) | Product cone: `Im(ξ_k) ∈ V⁺` for all `k` (forward tube in difference coords) |

### Reduced Difference Coordinates (`ComplexLieGroups/DifferenceCoordinatesReduced.lean`)

| Definition | Line | Description |
|---|---|---|
| `reducedDiffMap` | [90](OSReconstruction/ComplexLieGroups/DifferenceCoordinatesReduced.lean#L90) | Map from n-point configs to `(n−1)` successive-difference coordinates |
| `ReducedForwardTube` | [149](OSReconstruction/ComplexLieGroups/DifferenceCoordinatesReduced.lean#L149) | Forward tube in `(n−1)` reduced difference coordinates |
| `ReducedPermutedForwardTube` | [352](OSReconstruction/ComplexLieGroups/DifferenceCoordinatesReduced.lean#L352) | Reduced difference configs that lie in the forward tube after permutation |

### Connectedness (`ComplexLieGroups/Connectedness/`)

| Definition | File | Line | Description |
|---|---|---|---|
| `complexLorentzAction` | [Action.lean](OSReconstruction/ComplexLieGroups/Connectedness/Action.lean#L10) | 10 | Complex Lorentz group action on n-point configs |
| `orbitSet` | [OrbitSetBasic.lean](OSReconstruction/ComplexLieGroups/Connectedness/OrbitSetBasic.lean#L15) | 15 | Set of Lorentz transforms keeping `z` in the forward tube |
| `stabilizer` | [OrbitSetBasic.lean](OSReconstruction/ComplexLieGroups/Connectedness/OrbitSetBasic.lean#L24) | 24 | Stabilizer subgroup of a configuration under the Lorentz action |
| `ExtendedTube` | [PermutedTube.lean](OSReconstruction/ComplexLieGroups/Connectedness/PermutedTube.lean#L13) | 13 | Complex Lorentz orbit of the forward tube |
| `PermutedExtendedTube` | [PermutedTube.lean](OSReconstruction/ComplexLieGroups/Connectedness/PermutedTube.lean#L105) | 105 | Union over all permutations and Lorentz transforms |
| `stabilizerI0` | [StabilizerI0.lean](OSReconstruction/ComplexLieGroups/Connectedness/ComplexInvariance/StabilizerI0.lean#L210) | 210 | Stabilizer of the canonical `i·e₀` configuration |
| `wickMatrixJ` | [JostWitnessGeneralSigma.lean](OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/JostWitnessGeneralSigma.lean#L54) | 54 | Wick rotation matrix in the `(0,j)` plane |
| `jostWitnessPoint` | [JostWitnessGeneralSigma.lean](OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/JostWitnessGeneralSigma.lean#L276) | 276 | Specific n-point real config for BHW permutation connectedness |

---

## SCV (Several Complex Variables)

### Tube Domains (`SCV/TubeDomainExtension.lean`)

| Definition | Line | Description |
|---|---|---|
| `TubeDomain` | [64](OSReconstruction/SCV/TubeDomainExtension.lean#L64) | Tube domain `T(C) = { z ∈ ℂᵐ : Im(z) ∈ C }` |
| `realSubspace` | [105](OSReconstruction/SCV/TubeDomainExtension.lean#L105) | Real subspace `{ z ∈ ℂᵐ : Im(z) = 0 }` |
| `realEmbed` | [109](OSReconstruction/SCV/TubeDomainExtension.lean#L109) | Canonical embedding `ℝᵐ ↪ ℂᵐ` |

### Polydiscs (`SCV/Polydisc.lean`)

| Definition | Line | Description |
|---|---|---|
| `Polydisc` | [50](OSReconstruction/SCV/Polydisc.lean#L50) | Open polydisc `{ z : |zᵢ − cᵢ| < rᵢ }` |
| `closedPolydisc` | [55](OSReconstruction/SCV/Polydisc.lean#L55) | Closed polydisc `{ z : |zᵢ − cᵢ| ≤ rᵢ }` |
| `distinguishedBoundary` | [62](OSReconstruction/SCV/Polydisc.lean#L62) | Distinguished boundary (torus): `{ z : |zᵢ − cᵢ| = rᵢ }` |
| `SeparatelyDifferentiableOn` | [204](OSReconstruction/SCV/Polydisc.lean#L204) | A function is separately holomorphic in each variable |

### Edge of the Wedge (`SCV/EdgeOfWedge.lean`)

| Definition | Line | Description |
|---|---|---|
| `EOW.UpperHalfPlane` | [62](OSReconstruction/SCV/EdgeOfWedge.lean#L62) | Upper half-plane `{ z : Im(z) > 0 }` |
| `EOW.LowerHalfPlane` | [65](OSReconstruction/SCV/EdgeOfWedge.lean#L65) | Lower half-plane `{ z : Im(z) < 0 }` |
| `gluedFunction` | [81](OSReconstruction/SCV/EdgeOfWedge.lean#L81) | Piecewise function: `f⁺` on upper, `f⁻` on lower, `bv` on real line |

### Fourier-Laplace (`SCV/FourierLaplaceCore.lean`)

| Definition | Line | Description |
|---|---|---|
| `smoothCutoff` | [71](OSReconstruction/SCV/FourierLaplaceCore.lean#L71) | Smooth cutoff: 0 on `(−∞, −1]`, 1 on `[0, ∞)` |
| `psiZ` | [179](OSReconstruction/SCV/FourierLaplaceCore.lean#L179) | Test function `ψ_z(ξ) = χ(ξ) · exp(izξ)` for `Im(z) > 0` |
| `schwartzPsiZ` | [955](OSReconstruction/SCV/FourierLaplaceCore.lean#L955) | `ψ_z` as a Schwartz function when `Im(z) > 0` |
| `fourierLaplaceExt` | [1314](OSReconstruction/SCV/FourierLaplaceCore.lean#L1314) | Fourier-Laplace extension `F(z) = T(FT[ψ_z])` for one-sided Fourier support distributions |

### Paley-Wiener (`SCV/PaleyWiener.lean`)

| Definition | Line | Description |
|---|---|---|
| `HasOneSidedFourierSupport` | [114](OSReconstruction/SCV/PaleyWiener.lean#L114) | Distribution whose Fourier transform is supported on `[0, ∞)` |
| `upperHalfPlane` | [146](OSReconstruction/SCV/PaleyWiener.lean#L146) | Upper half-plane `{ z ∈ ℂ : Im(z) > 0 }` |

### Analyticity (`SCV/Analyticity.lean`)

| Definition | Line | Description |
|---|---|---|
| `cauchyCoeffPolydisc` | [60](OSReconstruction/SCV/Analyticity.lean#L60) | Multi-variable Cauchy coefficient on a polydisc |
| `cauchyPowerSeriesPolydisc` | [124](OSReconstruction/SCV/Analyticity.lean#L124) | Multi-variable Cauchy power series on a polydisc |

### Laplace-Schwartz (`SCV/LaplaceSchwartz.lean`)

| Definition | Line | Description |
|---|---|---|
| `HasFourierLaplaceRepr` | [74](OSReconstruction/SCV/LaplaceSchwartz.lean#L74) | Distributional boundary-value representation for a holomorphic function on a tube domain |
| `HasFourierLaplaceReprTempered` | [143](OSReconstruction/SCV/LaplaceSchwartz.lean#L143) | Tempered Fourier-Laplace representation with polynomial growth estimates |

### Semigroup Bochner (`SCV/SemigroupBochner.lean`, `SCV/SemigroupGroupBochner.lean`)

| Definition | File | Line | Description |
|---|---|---|---|
| `IsSemigroupPDKernel` | [SemigroupBochner.lean](OSReconstruction/SCV/SemigroupBochner.lean#L37) | 37 | Positive-definite kernel on the additive semigroup `(0, ∞)` |
| `IsSemigroupGroupPD` | [SemigroupGroupBochner.lean](OSReconstruction/SCV/SemigroupGroupBochner.lean#L25) | 25 | Positive-definite on the involutive semigroup `(t, a)* = (t, −a)` |

### Vladimirov-Tillmann (`SCV/VladimirovTillmann.lean`)

| Definition | Line | Description |
|---|---|---|
| `IsCone` | [44](OSReconstruction/SCV/VladimirovTillmann.lean#L44) | A set is a positive cone (closed under scaling by `λ > 0`) |
| `IsSalientCone` | [55](OSReconstruction/SCV/VladimirovTillmann.lean#L55) | A cone is salient (pointed): closure contains no complete line |

### Other SCV

| Definition | File | Line | Description |
|---|---|---|---|
| `translateSchwartz` | [DistributionalUniqueness.lean](OSReconstruction/SCV/DistributionalUniqueness.lean#L50) | 50 | Translates a Schwartz function by a fixed vector |
| `reflectSchwartz` | [DistributionalUniqueness.lean](OSReconstruction/SCV/DistributionalUniqueness.lean#L178) | 178 | Reflects a Schwartz function: `f ↦ f(−x)` |
| `realToComplex` | [TotallyRealIdentity.lean](OSReconstruction/SCV/TotallyRealIdentity.lean#L47) | 47 | Canonical embedding `ℝᵐ ↪ ℂᵐ` |
| `conjMap` | [TotallyRealIdentity.lean](OSReconstruction/SCV/TotallyRealIdentity.lean#L377) | 377 | Componentwise complex conjugation on `ℂᵐ` |
| `rudinC` | [MoebiusMap.lean](OSReconstruction/SCV/MoebiusMap.lean#L42) | 42 | Rudin's constant `c = √2 − 1` for the Moebius map construction |
| `moebiusRudin` | [MoebiusMap.lean](OSReconstruction/SCV/MoebiusMap.lean#L85) | 85 | Rudin's Moebius map `φ(w, λ) = (w + λ/c)/(1 + cλw)` |
| `iteratedCircleIntegral` | [IteratedCauchyIntegral.lean](OSReconstruction/SCV/IteratedCauchyIntegral.lean#L61) | 61 | Iterated circle integral over m circles |
| `cauchyKernelPolydisc` | [IteratedCauchyIntegral.lean](OSReconstruction/SCV/IteratedCauchyIntegral.lean#L178) | 178 | Cauchy kernel `∏ᵢ (wᵢ − zᵢ)⁻¹` |

---

## vNA (von Neumann Algebras)

### Basic (`vNA/Basic.lean`)

| Definition | Line | Description |
|---|---|---|
| `orbit` | [54](OSReconstruction/vNA/Basic.lean#L54) | Set of vectors `{aΩ : a ∈ M}` obtained by applying algebra elements to `Ω` |
| `cyclicSubspace` | [58](OSReconstruction/vNA/Basic.lean#L58) | Closed submodule generated by `MΩ` |
| `IsCyclic` | [62](OSReconstruction/vNA/Basic.lean#L62) | `Ω` is cyclic if closure of `MΩ = H` |
| `IsSeparating` | [66](OSReconstruction/vNA/Basic.lean#L66) | `Ω` is separating if `aΩ = 0 ⟹ a = 0` |
| `IsCyclicSeparating` | [70](OSReconstruction/vNA/Basic.lean#L70) | Both cyclic and separating |
| `VectorState` | [264](OSReconstruction/vNA/Basic.lean#L264) | State on `M` given by a unit vector |
| `Projection` | [315](OSReconstruction/vNA/Basic.lean#L315) | Self-adjoint idempotent in the vN algebra |

### Antilinear Maps (`vNA/Antilinear.lean`)

| Definition | Line | Description |
|---|---|---|
| `AntilinearMap` | [40](OSReconstruction/vNA/Antilinear.lean#L40) | Conjugate-linear map: `J(αx + y) = ᾱJ(x) + J(y)` |
| `AntiunitaryOp` | [104](OSReconstruction/vNA/Antilinear.lean#L104) | Antiunitary involution (e.g., modular conjugation `J`) |

### Predual (`vNA/Predual.lean`)

| Definition | Line | Description |
|---|---|---|
| `NormalFunctional` | [55](OSReconstruction/vNA/Predual.lean#L55) | σ-weakly continuous functional on a vN algebra |
| `State` | [138](OSReconstruction/vNA/Predual.lean#L138) | Positive normalized normal functional |
| `TraceClass` | [188](OSReconstruction/vNA/Predual.lean#L188) | Trace-class operator with rank-one decomposition |
| `sigmaWeakTopology` | [220](OSReconstruction/vNA/Predual.lean#L220) | σ-weak topology on `B(H)` induced by trace-class pairings |

### Modular Theory (`vNA/ModularTheory.lean`)

| Definition | Line | Description |
|---|---|---|
| `TomitaOperator` | [59](OSReconstruction/vNA/ModularTheory.lean#L59) | Antilinear operator `S₀: aΩ ↦ a*Ω` |
| `ModularOperator` | [115](OSReconstruction/vNA/ModularTheory.lean#L115) | Modular operator `Δ = S̄*S̄`, positive self-adjoint unbounded operator |
| `ModularConjugation` | [166](OSReconstruction/vNA/ModularTheory.lean#L166) | Modular conjugation `J` from polar decomposition `S = JΔ^{1/2}` |
| `StandardForm` | [308](OSReconstruction/vNA/ModularTheory.lean#L308) | vN algebra in standard form with modular data |

### Modular Automorphism (`vNA/ModularAutomorphism.lean`)

| Definition | Line | Description |
|---|---|---|
| `ModularAutomorphismGroup` | [55](OSReconstruction/vNA/ModularAutomorphism.lean#L55) | The modular automorphism group `σ_t` for a faithful normal state |
| `ConnesCocycle` | [293](OSReconstruction/vNA/ModularAutomorphism.lean#L293) | Connes cocycle relating two faithful normal states |

### KMS States (`vNA/KMS.lean`)

| Definition | Line | Description |
|---|---|---|
| `strip` | [56](OSReconstruction/vNA/KMS.lean#L56) | Open horizontal strip `0 < Im(z) < β` |
| `IsKMSState` | [80](OSReconstruction/vNA/KMS.lean#L80) | State satisfying the KMS condition at inverse temperature `β` |
| `inverseTemperature` | [154](OSReconstruction/vNA/KMS.lean#L154) | Inverse temperature `β = 1/(k_B T)` |
| `IsPassive` | [193](OSReconstruction/vNA/KMS.lean#L193) | No work extractable by cyclic unitary processes |
| `IsCompletelyPassive` | [230](OSReconstruction/vNA/KMS.lean#L230) | Stability under tensor products of cyclic processes |

### Unbounded Operators (`vNA/Unbounded/Basic.lean`)

| Definition | Line | Description |
|---|---|---|
| `UnboundedOperator` | [54](OSReconstruction/vNA/Unbounded/Basic.lean#L54) | Unbounded linear operator with a submodule domain |
| `IsDenselyDefined` | [71](OSReconstruction/vNA/Unbounded/Basic.lean#L71) | Domain closure equals the full Hilbert space |
| `IsClosed` | [118](OSReconstruction/vNA/Unbounded/Basic.lean#L118) | Graph is closed in `H × H` |
| `IsClosable` | [124](OSReconstruction/vNA/Unbounded/Basic.lean#L124) | `(0, y)` in graph closure implies `y = 0` |
| `adjoint` | [449](OSReconstruction/vNA/Unbounded/Basic.lean#L449) | Adjoint `T*` satisfying `⟨Tx, y⟩ = ⟨x, T*y⟩` |
| `IsSymmetric` | [902](OSReconstruction/vNA/Unbounded/Basic.lean#L902) | `⟨Tx, y⟩ = ⟨x, Ty⟩` on the domain |
| `IsSelfAdjoint` | [906](OSReconstruction/vNA/Unbounded/Basic.lean#L906) | `T = T*` including equality of domains |
| `IsPositive` | [1072](OSReconstruction/vNA/Unbounded/Basic.lean#L1072) | `Re⟨Tx, x⟩ ≥ 0` for all `x ∈ dom(T)` |

### Stone's Theorem (`vNA/Unbounded/StoneTheorem.lean`)

| Definition | Line | Description |
|---|---|---|
| `OneParameterUnitaryGroup` | [91](OSReconstruction/vNA/Unbounded/StoneTheorem.lean#L91) | Strongly continuous `U : ℝ → U(H)` with `U(s+t) = U(s)U(t)` |
| `generator` | [249](OSReconstruction/vNA/Unbounded/StoneTheorem.lean#L249) | Infinitesimal generator `A` with `Ax = lim (U(t)x − x)/(it)` |
| `StoneData` | [1449](OSReconstruction/vNA/Unbounded/StoneTheorem.lean#L1449) | Data witnessing Stone's theorem: self-adjoint `A` with `U(t) = exp(itA)` |
| `timeEvolution` | [1758](OSReconstruction/vNA/Unbounded/StoneTheorem.lean#L1758) | One-parameter unitary group `U(t) = exp(−itH)` for a Hamiltonian `H` |

### Spectral Theory (`vNA/Unbounded/Spectral.lean`)

| Definition | Line | Description |
|---|---|---|
| `SpectralMeasure` | [99](OSReconstruction/vNA/Unbounded/Spectral.lean#L99) | Projection-valued measure: `E ↦ P(E)` with σ-additivity, multiplicativity, `P(ℝ) = 1` |
| `FunctionalCalculus` | [1066](OSReconstruction/vNA/Unbounded/Spectral.lean#L1066) | Borel functional calculus: bounded functions → bounded operators |
| `spectralIntegral` | [2012](OSReconstruction/vNA/Unbounded/Spectral.lean#L2012) | Spectral integral `∫ f dμ_{x,y}` via polarization |
| `functionalCalculus` | [2037](OSReconstruction/vNA/Unbounded/Spectral.lean#L2037) | Operator `f(T) = ∫ f(λ) dP(λ)` via Riesz representation |

### Spectral via Cayley (`vNA/Spectral/CayleyTransform.lean`)

| Definition | Line | Description |
|---|---|---|
| `deficiencyPlus` | [69](OSReconstruction/vNA/Spectral/CayleyTransform.lean#L69) | Positive deficiency subspace `K₊ = (ran(T − i))⊥` |
| `deficiencyMinus` | [75](OSReconstruction/vNA/Spectral/CayleyTransform.lean#L75) | Negative deficiency subspace `K₋ = (ran(T + i))⊥` |
| `CayleyTransform` | [963](OSReconstruction/vNA/Spectral/CayleyTransform.lean#L963) | Cayley transform `U = (T − i)(T + i)⁻¹` for self-adjoint `T` |
| `cayleyMap` | [1399](OSReconstruction/vNA/Spectral/CayleyTransform.lean#L1399) | Cayley map `t ↦ (t − i)/(t + i)` from `ℝ` to `S¹ \ {1}` |

### Measure Theory (`vNA/MeasureTheory/`)

| Definition | File | Line | Description |
|---|---|---|---|
| `IntervalPremeasure` | [CaratheodoryExtension.lean](OSReconstruction/vNA/MeasureTheory/CaratheodoryExtension.lean#L86) | 86 | Premeasure on bounded closed intervals for Caratheodory extension |
| `SpectralPremeasure` | [CaratheodoryExtension.lean](OSReconstruction/vNA/MeasureTheory/CaratheodoryExtension.lean#L346) | 346 | Family of complex premeasures parametrized by pairs of Hilbert space vectors |
| `ComplexSpectralMeasure` | [SpectralIntegral.lean](OSReconstruction/vNA/MeasureTheory/SpectralIntegral.lean#L58) | 58 | σ-additive complex measure `μ_{x,y}(E) = ⟨x, P(E)y⟩` with finite total variation |
| `SpectralDistribution` | [SpectralStieltjes.lean](OSReconstruction/vNA/MeasureTheory/SpectralStieltjes.lean#L59) | 59 | Right-continuous monotone function `F(λ) = ⟨x, P((−∞,λ])x⟩` |
| `ProjectionValuedMeasure` | [SpectralStieltjes.lean](OSReconstruction/vNA/MeasureTheory/SpectralStieltjes.lean#L135) | 135 | Projection-valued measure: `E ↦ P(E)` with `P(E)² = P(E)`, `P(E)* = P(E)` |

### Bochner / CFC Infrastructure (`vNA/Bochner/CfcInfrastructure.lean`)

| Definition | Line | Description |
|---|---|---|
| `UnboundedCFC` | [376](OSReconstruction/vNA/Bochner/CfcInfrastructure.lean#L376) | Functional calculus `f(T)` for unbounded self-adjoint `T` via Cayley transform |
| `bumpOperator` | [840](OSReconstruction/vNA/Bochner/CfcInfrastructure.lean#L840) | Bump function operator for an interval via the CFC |
| `SOTConverges` | [1638](OSReconstruction/vNA/Bochner/CfcInfrastructure.lean#L1638) | Strong operator topology convergence: `A_n x → L x` for all `x` |
