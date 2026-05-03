import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45

noncomputable section

namespace BHW

variable {d n : ℕ}

/-- Complex-linear relabelling of an `n`-point complex configuration by a
permutation of the point labels. -/
noncomputable def configPermCLE
    (ρ : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  { toFun := fun z k μ => z (ρ k) μ
    invFun := fun z k μ => z (ρ.symm k) μ
    map_add' := by
      intro z w
      rfl
    map_smul' := by
      intro c z
      rfl
    left_inv := by
      intro z
      ext k μ
      simp
    right_inv := by
      intro z
      ext k μ
      simp
    continuous_toFun := by
      refine continuous_pi ?_
      intro k
      refine continuous_pi ?_
      intro μ
      exact (continuous_apply μ).comp (continuous_apply (ρ k))
    continuous_invFun := by
      refine continuous_pi ?_
      intro k
      refine continuous_pi ?_
      intro μ
      exact (continuous_apply μ).comp (continuous_apply (ρ.symm k)) }

@[simp] theorem configPermCLE_apply
    (ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    configPermCLE (d := d) (n := n) ρ z =
      fun k μ => z (ρ k) μ := by
  rfl

@[simp] theorem configPermCLE_symm_apply
    (ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (configPermCLE (d := d) (n := n) ρ).symm z =
      fun k μ => z (ρ.symm k) μ := by
  rfl

/-- The OS45 common chart used for adjacent branch comparison: first relabel by
`ρ`, then apply the fixed OS45 quarter-turn chart. -/
noncomputable def os45CommonChartCLE
    (ρ : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  (configPermCLE (d := d) (n := n) ρ).trans
    (os45QuarterTurnCLE (d := d) (n := n))

@[simp] theorem os45CommonChartCLE_apply
    (ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    os45CommonChartCLE (d := d) (n := n) ρ z =
      os45QuarterTurnConfig (d := d) (n := n) (fun k μ => z (ρ k) μ) := by
  simp [os45CommonChartCLE]

@[simp] theorem os45CommonChartCLE_symm_apply
    (ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (os45CommonChartCLE (d := d) (n := n) ρ).symm z =
      fun k μ =>
        if μ = 0 then (1 + Complex.I) * z (ρ.symm k) μ
        else z (ρ.symm k) μ := by
  ext k μ
  simp [os45CommonChartCLE]

/-- The Wick-rotated image of a `σ`-ordered Euclidean positive-time
configuration lies in the OS-II first analytic-continuation region. -/
theorem wickRotate_ordered_mem_acrOne
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    BHW.permAct (d := d) σ (fun k => wickRotatePoint (x k)) ∈
      AnalyticContinuationRegion d n 1 := by
  intro i μ hμ
  have hμ0 : μ = 0 := by
    exact Fin.ext (Nat.eq_zero_of_le_zero hμ)
  subst μ
  by_cases hi : i.val = 0
  · have hpos : 0 < x (σ i) 0 := (hx i).1
    simpa [AnalyticContinuationRegion, BHW.permAct, wickRotatePoint, hi,
      Complex.sub_im] using hpos
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    have hj_lt_i : j < i := Fin.lt_def.mpr (by
      dsimp [j]
      omega)
    have hlt : x (σ j) 0 < x (σ i) 0 := (hx j).2 i hj_lt_i
    have hpos : 0 < x (σ i) 0 - x (σ j) 0 := sub_pos.mpr hlt
    simpa [AnalyticContinuationRegion, BHW.permAct, wickRotatePoint, hi, j,
      Complex.sub_im] using hpos

end BHW
