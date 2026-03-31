import OSReconstruction.SCV.VladimirovTillmann

/-!
# Tube-Domain Boundary Values from Polynomial Growth

This file isolates the pure several-complex-variables boundary-value theorem
needed by the OS reconstruction boundary-values layer.

The theorem surface is intentionally QFT-free: it is stated for a holomorphic
function on a tube domain over an open convex salient cone, with a global
polynomial-growth bound, and concludes existence of a continuous Schwartz
boundary-value functional obtained as a raywise limit.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-- Pure tube-domain boundary-value existence from holomorphy and global
polynomial growth.

This is the honest remaining SCV blocker on the active OS route: once a
holomorphic function on `TubeDomainSetPi C` is known to satisfy a global
polynomial-growth bound, the existence of a continuous boundary-value
functional on Schwartz test functions should be a pure complex-analytic /
functional-analytic theorem. -/
theorem tube_boundaryValueData_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)) := by
  sorry

end SCV
