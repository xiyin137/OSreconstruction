/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.Polydisc
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.LaplaceHolomorphic
import OSReconstruction.SCV.SemigroupBochner
import OSReconstruction.SCV.MultipleReflection
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.SeparatelyAnalytic
import OSReconstruction.SCV.EdgeOfWedge
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.ComplexSchwartz
import OSReconstruction.SCV.SchwartzExternalProduct
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.SCV.DistributionalEOWDbar
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.SCV.DistributionalEOWRepresentative
import OSReconstruction.SCV.DistributionalEOWApproxIdentity
import OSReconstruction.SCV.DistributionalEOWRegularity
import OSReconstruction.SCV.EuclideanWeyl
import OSReconstruction.SCV.EuclideanWeylFrechet
import OSReconstruction.SCV.EuclideanWeylBump
import OSReconstruction.SCV.EuclideanWeylPoisson
import OSReconstruction.SCV.EuclideanWeylRegularity
import OSReconstruction.SCV.EuclideanWeylProbe
import OSReconstruction.SCV.EuclideanWeylPairing
import OSReconstruction.SCV.EuclideanWeylApproxIdentity
import OSReconstruction.SCV.EuclideanWeylRepresentation
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.DistributionalEOWHolomorphic
import OSReconstruction.SCV.SchwartzPrependField
import OSReconstruction.SCV.SchwartzPartialEval
import OSReconstruction.SCV.TranslationDifferentiation
import OSReconstruction.SCV.HeadBlockIntegral
import OSReconstruction.SCV.HeadFiberAntideriv
import OSReconstruction.SCV.HeadFiberAntiderivInterval
import OSReconstruction.SCV.HeadFiberAntiderivDecay
import OSReconstruction.SCV.HeadBlockDescent
import OSReconstruction.SCV.DistributionalEOWKernelTransport
import OSReconstruction.SCV.DistributionalEOWKernelFactorization
import OSReconstruction.SCV.DistributionalEOWProductKernel
import OSReconstruction.SCV.ProductDensity
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.DistributionalEOWBoundaryProductKernel
import OSReconstruction.SCV.LocalEOWChartLinear
import OSReconstruction.SCV.LocalEOWSideCone
import OSReconstruction.SCV.LocalDistributionalEOWSlice
import OSReconstruction.SCV.LocalEOWFixedBasis
import OSReconstruction.SCV.LocalEOWChartEnvelope
import OSReconstruction.SCV.LocalEOWChartApproxIdentity
import OSReconstruction.SCV.LocalContinuousEOWSideAgreement
import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.SCV.VaryingKernelContinuity
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalDescentSupport
import OSReconstruction.SCV.LocalProductDescent
import OSReconstruction.SCV.LocalProductDescentIntegrals
import OSReconstruction.SCV.LocalProductRecovery
import OSReconstruction.SCV.LocalEOWChartRecovery
import OSReconstruction.SCV.LocalEOWChartAssembly
import OSReconstruction.SCV.LocalEOWDistributionalEnvelope
import OSReconstruction.SCV.HasFDerivAtProd
import OSReconstruction.SCV.PartialFourierSpatial

/-!
# Several Complex Variables

This module develops infrastructure for several complex variables (SCV),
with the goal of proving the multi-dimensional edge-of-the-wedge theorem.

## Modules

* `SCV.Polydisc` — Polydiscs and their topological properties
* `SCV.LaplaceHolomorphic` — holomorphic Laplace transforms on half-planes
* `SCV.SemigroupBochner` — semigroup positive-definite kernels on `(0, ∞)`
* `SCV.IteratedCauchyIntegral` — Iterated circle integrals and Cauchy formula for polydiscs
* `SCV.SeparatelyAnalytic` — Osgood/Hartogs infrastructure and extension lemmas
* `SCV.EdgeOfWedge` — 1D edge-of-the-wedge infrastructure
* `SCV.TubeDomainExtension` — Edge-of-the-wedge theorem via gap-point filling
-/
