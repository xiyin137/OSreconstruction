/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.MatrixLieGroup
import OSReconstruction.ComplexLieGroups.LorentzLieGroup
import OSReconstruction.ComplexLieGroups.Complexification
import OSReconstruction.ComplexLieGroups.BHWCore
import OSReconstruction.ComplexLieGroups.Connectedness

/-!
# Complex Lie Group Theory

This module develops the Lie group theory infrastructure needed to prove
the Bargmann-Hall-Wightman theorem: connectedness of SO⁺(1,d;ℂ),
holomorphicity of group actions, and the analytic continuation argument
from real to complex Lorentz invariance.

## Modules

* `ComplexLieGroups.MatrixLieGroup` — GL(n,ℂ) and SL(n,ℂ) as Lie groups
* `ComplexLieGroups.LorentzLieGroup` — Lorentz group as a topological group
* `ComplexLieGroups.Complexification` — SO⁺(1,d;ℂ) definition and connectedness
* `ComplexLieGroups.Connectedness` — BHW proof via identity theorem
-/
