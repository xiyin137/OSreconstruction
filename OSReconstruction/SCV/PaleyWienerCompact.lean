import OSReconstruction.SCV.PaleyWienerSchwartz

noncomputable section

open scoped Topology
open Set

/-- Uniform seminorm bound for `multiDimPsiZExt` on a compact subset of the
tube.  This is the compact-set version of
`multiDimPsiZ_local_uniform_seminorm_bound`. -/
theorem multiDimPsiZExt_compactTubeSet_seminorm_bound
    {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C) (hC_cone : IsCone C)
    (hC_salient : IsSalientCone C)
    {K : Set (Fin m → ℂ)} (hK : IsCompact K)
    (hK_tube : K ⊆ SCV.TubeDomain C)
    (k l : ℕ) :
    ∃ B > 0,
      ∀ z ∈ K,
        SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z) ≤ B := by
  classical
  have hloc :
      ∀ z0 : K, ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧
        ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
          ‖z - z0.1‖ < δ →
            SchwartzMap.seminorm ℝ k l
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ≤
                B := by
    intro z0
    exact multiDimPsiZ_local_uniform_seminorm_bound
      hC_open hC_conv hC_cone hC_salient k l z0.1 (hK_tube z0.2)
  choose B δ hB_pos hδ_pos hlocal using hloc
  obtain ⟨s, hscover⟩ :=
    hK.elim_finite_subcover
      (fun z0 : K => Metric.ball z0.1 (δ z0))
      (fun z0 => Metric.isOpen_ball)
      (by
        intro z hz
        exact mem_iUnion.mpr
          ⟨⟨z, hz⟩, by
            simpa [Metric.mem_ball, dist_eq_norm] using hδ_pos ⟨z, hz⟩⟩)
  let Btot : ℝ := 1 + ∑ z0 ∈ s, B z0
  have hBtot_pos : 0 < Btot := by
    have hsum_nonneg : 0 ≤ ∑ z0 ∈ s, B z0 := by
      exact Finset.sum_nonneg fun z0 _hz0s => (hB_pos z0).le
    dsimp [Btot]
    linarith
  refine ⟨Btot, hBtot_pos, ?_⟩
  intro z hzK
  have hzcover : z ∈ ⋃ z0 ∈ s, Metric.ball z0.1 (δ z0) := hscover hzK
  rcases mem_iUnion.mp hzcover with ⟨z0, hzcover'⟩
  rcases mem_iUnion.mp hzcover' with ⟨hz0s, hzball⟩
  have hz_tube : z ∈ SCV.TubeDomain C := hK_tube hzK
  have hdist : ‖z - z0.1‖ < δ z0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hbase :
      SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z) ≤
        B z0 := by
    rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient z hz_tube]
    exact hlocal z0 z hz_tube hdist
  have hB_le_sum : B z0 ≤ ∑ z0 ∈ s, B z0 := by
    exact Finset.single_le_sum
      (fun y _hy => (hB_pos y).le) hz0s
  have hB_le_tot : B z0 ≤ Btot := by
    dsimp [Btot]
    linarith
  exact hbase.trans hB_le_tot
