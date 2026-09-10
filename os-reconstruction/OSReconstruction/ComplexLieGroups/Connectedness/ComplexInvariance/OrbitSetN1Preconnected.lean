import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.QuadricConeImPos

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {m : ℕ}

/-- The canonical one-point quadric cone is preconnected for every nonzero `c`. -/
theorem quadricConeSet_wScalarE0_isPreconnected
    (c : ℂ) (hc : c ≠ 0) :
    IsPreconnected (quadricConeSet_wScalarE0 (m := m) c) := by
  have hImPos :
      ∀ c' : ℂ, c' ≠ 0 → 0 < c'.im →
        IsPreconnected (quadricConeSet_wScalarE0 (m := m) c') := by
    intro c' hc' hcim'
    exact quadricConeSet_wScalarE0_isPreconnected_of_c_im_pos (m := m) c' hc' hcim'
  have hImNe :
      ∀ c' : ℂ, c' ≠ 0 → c'.im ≠ 0 →
        IsPreconnected (quadricConeSet_wScalarE0 (m := m) c') :=
    quadricConeSet_wScalarE0_isPreconnected_of_im_pos_reduction (m := m) hImPos
  exact
    (quadricConeSet_wScalarE0_isPreconnected_of_im_ne_zero_reduction
      (m := m) hImNe) c hc

/-- One-point forward-tube orbit sets are preconnected. -/
theorem orbitSet_forwardTube_one_isPreconnected
    (w : Fin 1 → Fin (m + 2) → ℂ)
    (hw : w ∈ ForwardTube (m + 1) 1) :
    IsPreconnected (orbitSet (d := m + 1) (n := 1) w) := by
  refine orbitSet_forwardTube_one_isPreconnected_of_quadricCone_family
    (m := m) w hw ?_
  intro c hc
  exact quadricConeSet_wScalarE0_isPreconnected (m := m) c hc

end BHW

