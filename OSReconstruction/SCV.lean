/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.Polydisc
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.SeparatelyAnalytic
import OSReconstruction.SCV.EdgeOfWedge
import OSReconstruction.SCV.TubeDomainExtension

/-!
# Several Complex Variables

This module develops infrastructure for several complex variables (SCV),
with the goal of proving the multi-dimensional edge-of-the-wedge theorem.

## Modules

* `SCV.Polydisc` — Polydiscs and their topological properties
* `SCV.IteratedCauchyIntegral` — Iterated circle integrals and Cauchy formula for polydiscs
* `SCV.SeparatelyAnalytic` — Osgood/Hartogs infrastructure and extension lemmas
* `SCV.EdgeOfWedge` — 1D edge-of-the-wedge infrastructure
* `SCV.TubeDomainExtension` — Edge-of-the-wedge theorem via gap-point filling
-/
