/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Cone Definitions and Tube Domains

Basic definitions for cones and tube domains used throughout the SCV
and Wightman reconstruction modules. Extracted to break import cycles.
-/

noncomputable section

/-- A set is a (positive) cone if it is closed under scaling by strictly
    positive reals. -/
def IsCone {E : Type*} [SMul ℝ E] (C : Set E) : Prop :=
  ∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C

/-- A cone is salient (or pointed) if its closure contains no complete line. -/
def IsSalientCone {E : Type*} [AddCommGroup E] [TopologicalSpace E] (C : Set E) : Prop :=
  ∀ y, y ∈ closure C → -y ∈ closure C → y = 0

/-- The tube domain T(C) = { z | Im(z) ∈ C } for the nested Pi type
    used by the Wightman forward tube. -/
def TubeDomainSetPi {n d : ℕ} (C : Set (Fin n → Fin (d + 1) → ℝ)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k μ => (z k μ).im) ∈ C }

end
