/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic




























noncomputable section

open Complex Metric Set Filter Topology

namespace SCV

variable {m : ℕ}



/-- The open polydisc in `Fin m → ℂ` with center `c` and polyradius `r`.
    This is the product of open discs: `{z | ∀ i, |zᵢ - cᵢ| < rᵢ}`. -/
def Polydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.ball (c i) (r i) }

/-- The closed polydisc in `Fin m → ℂ` with center `c` and polyradius `r`.
    This is the product of closed discs: `{z | ∀ i, |zᵢ - cᵢ| ≤ rᵢ}`. -/
def closedPolydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.closedBall (c i) (r i) }

/-- The distinguished boundary (torus) of a polydisc: `{z | ∀ i, |zᵢ - cᵢ| = rᵢ}`.
    This is the Cartesian product of circles, NOT the topological boundary.
    For polydiscs with m ≥ 2, the distinguished boundary is a proper subset
    of the topological boundary. -/
def distinguishedBoundary (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, z i ∈ Metric.sphere (c i) (r i) }



theorem mem_polydisc_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ Polydisc c r ↔ ∀ i, dist (z i) (c i) < r i :=
  Iff.rfl

theorem mem_closedPolydisc_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ closedPolydisc c r ↔ ∀ i, dist (z i) (c i) ≤ r i :=
  Iff.rfl

theorem mem_distinguishedBoundary_iff {c : Fin m → ℂ} {r : Fin m → ℝ} {z : Fin m → ℂ} :
    z ∈ distinguishedBoundary c r ↔ ∀ i, dist (z i) (c i) = r i :=
  Iff.rfl

theorem center_mem_polydisc {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) :
    c ∈ Polydisc c r := by
  intro i; exact Metric.mem_ball_self (hr i)

theorem center_mem_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} (hr : ∀ i, 0 ≤ r i) :
    c ∈ closedPolydisc c r := by
  intro i; exact Metric.mem_closedBall_self (hr i)

theorem polydisc_subset_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Polydisc c r ⊆ closedPolydisc c r :=
  fun _ hz i => Metric.ball_subset_closedBall (hz i)

theorem distinguishedBoundary_subset_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    distinguishedBoundary c r ⊆ closedPolydisc c r :=
  fun _ hz i => Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp (hz i)))

theorem polydisc_mono {c : Fin m → ℂ} {r₁ r₂ : Fin m → ℝ} (h : ∀ i, r₁ i ≤ r₂ i) :
    Polydisc c r₁ ⊆ Polydisc c r₂ :=
  fun _ hz i => lt_of_lt_of_le (hz i) (h i)

theorem closedPolydisc_mono {c : Fin m → ℂ} {r₁ r₂ : Fin m → ℝ} (h : ∀ i, r₁ i ≤ r₂ i) :
    closedPolydisc c r₁ ⊆ closedPolydisc c r₂ :=
  fun _ hz i => le_trans (hz i) (h i)



theorem polydisc_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Polydisc c r = Set.univ.pi (fun i => Metric.ball (c i) (r i)) := by
  ext z; simp [Polydisc, Set.mem_pi]

theorem closedPolydisc_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    closedPolydisc c r = Set.univ.pi (fun i => Metric.closedBall (c i) (r i)) := by
  ext z; simp [closedPolydisc, Set.mem_pi]

theorem distinguishedBoundary_eq_pi {c : Fin m → ℂ} {r : Fin m → ℝ} :
    distinguishedBoundary c r = Set.univ.pi (fun i => Metric.sphere (c i) (r i)) := by
  ext z; simp [distinguishedBoundary, Set.mem_pi]



theorem polydisc_isOpen {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsOpen (Polydisc c r) := by
  rw [polydisc_eq_pi]
  exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)

theorem isCompact_closedPolydisc {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsCompact (closedPolydisc c r) := by
  rw [closedPolydisc_eq_pi]
  exact isCompact_univ_pi (fun i => ProperSpace.isCompact_closedBall (c i) (r i))

theorem isCompact_distinguishedBoundary {c : Fin m → ℂ} {r : Fin m → ℝ} :
    IsCompact (distinguishedBoundary c r) := by
  rw [distinguishedBoundary_eq_pi]
  exact isCompact_univ_pi (fun i => isCompact_sphere (c i) (r i))



theorem polydisc_convex {c : Fin m → ℂ} {r : Fin m → ℝ} :
    Convex ℝ (Polydisc c r) := by
  rw [polydisc_eq_pi]
  exact convex_pi (fun i _ => convex_ball (c i) (r i))









end SCV
