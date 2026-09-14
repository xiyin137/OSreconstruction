/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketCarrierRegularity
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalProductRecovery










noncomputable section

open Complex MeasureTheory Set Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Quantitative nested balls around one complex-time point.  The radii
`σ`, `4σ`, `8σ`, and `16σ` are respectively used for pointwise recovery,
descent, product-kernel covariance, and the compact pairing cutoff. -/
structure LocalKernelWindowData
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (η ρ : ℝ)
    (w0 : OSIITimeGapSpace k) where
  sigma : ℝ
  sigma_pos : 0 < sigma
  carrier_window :
    ∀ z ∈ Metric.closedBall (0 : SCV.ComplexChartSpace k) (16 * sigma),
      w0 + z ∈ osiiNarrowTimeCarrier (k := k) η
  covariance_small : 16 * sigma < ρ
  kernel_small : 2 * sigma < R.radius

/-- Every point of the narrow carrier admits a nested local-kernel window
small enough for both the signed covariance radius and the anchored test
support radius. -/
theorem CommonCarrierRegularityData.exists_localKernelWindowData
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (η ρ : ℝ)
    (hρ : 0 < ρ)
    (w0 : OSIITimeGapSpace k)
    (hw0 : w0 ∈ osiiNarrowTimeCarrier (k := k) η) :
    Nonempty (LocalKernelWindowData R η ρ w0) := by
  obtain ⟨ε, hε, hε_sub⟩ :=
    SCV.exists_pos_closedBall_subset_of_isOpen
      (isOpen_osiiNarrowTimeCarrier η) hw0
  let σ : ℝ := min ε (min ρ R.radius) / 64
  have hmin_pos : 0 < min ε (min ρ R.radius) := by
    exact lt_min hε (lt_min hρ R.radius_pos)
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  have h16ε : 16 * σ < ε := by
    have hle : min ε (min ρ R.radius) ≤ ε := min_le_left _ _
    dsimp [σ]
    nlinarith
  have h16ρ : 16 * σ < ρ := by
    have hle :
        min ε (min ρ R.radius) ≤ ρ :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [σ]
    nlinarith
  have h2R : 2 * σ < R.radius := by
    have hle :
        min ε (min ρ R.radius) ≤ R.radius :=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [σ]
    nlinarith
  refine ⟨{
    sigma := σ
    sigma_pos := hσ
    carrier_window := ?_
    covariance_small := h16ρ
    kernel_small := h2R }⟩
  intro z hz
  apply hε_sub
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hz_norm : ‖z‖ ≤ 16 * σ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  simpa using hz_norm.trans h16ε.le

/-- The common time-shell distribution recentered at the anchored real test
coordinate and at one complex-time base point. -/
noncomputable def localRecenteredDistributionOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w0 : OSIITimeGapSpace k)
    (level : ℕ)
    (z : SCV.ComplexChartSpace k) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  (R.family.commonTimeShellDistributionOfOS
      OS η hηsum level (w0 + z) χ).comp
    (SCV.translateSchwartzCLM (-anchor))

@[simp]
theorem localRecenteredDistributionOfOS_apply
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w0 : OSIITimeGapSpace k)
    (level : ℕ)
    (z : SCV.ComplexChartSpace k)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    localRecenteredDistributionOfOS R OS η hηsum χ w0 level z ψ =
      R.family.commonTimeShellDistributionOfOS
        OS η hηsum level (w0 + z) χ
        (SCV.translateSchwartz (-anchor) ψ) := by
  simp [localRecenteredDistributionOfOS, ContinuousLinearMap.comp_apply,
    SCV.translateSchwartzCLM_apply]

/-- Every fixed recentered test gives a holomorphic scalar function on a
local window contained in the narrow carrier. -/
theorem LocalKernelWindowData.localRecenteredDistributionOfOS_differentiableOn
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    {R : CommonCarrierRegularityData A}
    {η ρ : ℝ}
    {w0 : OSIITimeGapSpace k}
    (W : LocalKernelWindowData R η ρ w0)
    (OS : OsterwalderSchraderAxioms d)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (level : ℕ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    DifferentiableOn ℂ
      (fun z : SCV.ComplexChartSpace k =>
        localRecenteredDistributionOfOS R
          OS η hηsum χ w0 level z ψ)
      (Metric.ball (0 : SCV.ComplexChartSpace k) (16 * W.sigma)) := by
  have hbase :=
    R.family.commonTimeShellDistributionOfOS_fixedTest_differentiableOn
      OS (SCV.translateSchwartz (-anchor) ψ)
      η hηsum level χ
  have haff :
      Differentiable ℂ
        (fun z : SCV.ComplexChartSpace k => w0 + z) := by
    fun_prop
  apply (hbase.comp haff.differentiableOn)
  intro z hz
  exact W.carrier_window z (Metric.ball_subset_closedBall hz)

/-- On the inner compact chart ball, the recentered distributions at every
spatial exhaustion level share one finite complex Schwartz-seminorm bound. -/
theorem LocalKernelWindowData.localRecenteredDistributionOfOS_uniform_schwartz_bound
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    {R : CommonCarrierRegularityData A}
    {η ρ : ℝ}
    {w0 : OSIITimeGapSpace k}
    (W : LocalKernelWindowData R η ρ w0)
    (OS : OsterwalderSchraderAxioms d)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ level z,
        z ∈ Metric.closedBall
          (0 : SCV.ComplexChartSpace k) (8 * W.sigma) →
        ∀ ψ : SchwartzMap (Fin k → ℝ) ℂ,
        ‖localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z ψ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ) ψ := by
  let B : Set (SCV.ComplexChartSpace k) :=
    Metric.closedBall (0 : SCV.ComplexChartSpace k) (8 * W.sigma)
  let K : Set (OSIITimeGapSpace k) :=
    (fun z : SCV.ComplexChartSpace k => w0 + z) '' B
  have hB_compact : IsCompact B := by
    exact isCompact_closedBall _ _
  have hshift_cont :
      Continuous (fun z : SCV.ComplexChartSpace k => w0 + z) := by
    fun_prop
  have hK_compact : IsCompact K := by
    exact hB_compact.image hshift_cont
  have hK_subset :
      K ⊆ osiiNarrowTimeCarrier (k := k) η := by
    rintro ζ ⟨z, hz, rfl⟩
    exact W.carrier_window z
      (Metric.closedBall_subset_closedBall (by
        nlinarith [W.sigma_pos]) hz)
  let J := ℕ × B
  let T : J → SchwartzMap (Fin k → ℝ) ℂ →L[ℝ] ℂ :=
    fun j =>
      (localRecenteredDistributionOfOS
        R OS η hηsum χ w0 j.1 j.2.1).restrictScalars ℝ
  have hT_pointwise :
      ∀ ψ : SchwartzMap (Fin k → ℝ) ℂ,
        ∃ C : ℝ, ∀ j : J, ‖T j ψ‖ ≤ C := by
    intro ψ
    obtain ⟨C, hC⟩ :=
      R.family.commonTimeShellDistributionOfOS_fixedTest_compact_bound
        OS η hηsum K hK_compact hK_subset χ
          (SCV.translateSchwartz (-anchor) ψ)
    refine ⟨C, ?_⟩
    intro j
    have hj :=
      hC j.1 (w0 + j.2.1)
        ⟨j.2.1, j.2.2, rfl⟩
    simpa [T, localRecenteredDistributionOfOS_apply] using hj
  obtain ⟨s, Cnn, _hCnn_ne, hboundℝ⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Fin k → ℝ) (F := ℂ) (G := ℂ) hT_pointwise
  have sup_apply_real_eq_complex :
      ∀ (s' : Finset (ℕ × ℕ))
        (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        (s'.sup
          (schwartzSeminormFamily ℝ (Fin k → ℝ) ℂ)) ψ =
        (s'.sup
          (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ)) ψ := by
    intro s' ψ
    induction s' using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have ha_eq :
            (schwartzSeminormFamily ℝ (Fin k → ℝ) ℂ a) ψ =
              (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ a) ψ := by
          cases a
          rfl
        simp [Finset.sup_insert, ih, ha_eq]
  refine ⟨s, (Cnn : ℝ), NNReal.coe_nonneg Cnn, ?_⟩
  intro level z hz ψ
  have h := hboundℝ (level, ⟨z, hz⟩) ψ
  calc
    ‖localRecenteredDistributionOfOS
        R OS η hηsum χ w0 level z ψ‖ =
        ‖T (level, ⟨z, hz⟩) ψ‖ := rfl
    _ ≤
        (Cnn • s.sup
          (schwartzSeminormFamily ℝ (Fin k → ℝ) ℂ)) ψ := h
    _ =
        (Cnn : ℝ) *
          s.sup (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ) ψ := by
      rw [Seminorm.smul_apply, sup_apply_real_eq_complex s ψ]
      rfl

/-- Partial evaluation of a mixed Schwartz test against the recentered
distribution is continuous on the compact pairing window, uniformly enough
to permit multiplication by any fixed chart cutoff. -/
theorem LocalKernelWindowData.localRecenteredDistributionOfOS_partialEval_continuousOn
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    {R : CommonCarrierRegularityData A}
    {η ρ : ℝ}
    {w0 : OSIITimeGapSpace k}
    (W : LocalKernelWindowData R η ρ w0)
    (OS : OsterwalderSchraderAxioms d)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (level : ℕ)
    (χU : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
    (F : SchwartzMap
      (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ) :
    ContinuousOn
      (fun z : SCV.ComplexChartSpace k =>
        χU z *
          localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F))
      (Metric.closedBall
        (0 : SCV.ComplexChartSpace k) (8 * W.sigma)) := by
  let B : Set (SCV.ComplexChartSpace k) :=
    Metric.closedBall (0 : SCV.ComplexChartSpace k) (8 * W.sigma)
  let T : B → SchwartzMap (Fin k → ℝ) ℂ →L[ℝ] ℂ :=
    fun z =>
      (localRecenteredDistributionOfOS
        R OS η hηsum χ w0 level z.1).restrictScalars ℝ
  obtain ⟨s, C, _hC, hbound⟩ :=
    W.localRecenteredDistributionOfOS_uniform_schwartz_bound
      OS hηsum χ
  have hT_pointwise :
      ∀ ψ : SchwartzMap (Fin k → ℝ) ℂ,
        ∃ M : ℝ, ∀ z : B, ‖T z ψ‖ ≤ M := by
    intro ψ
    refine ⟨C *
      s.sup (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ) ψ, ?_⟩
    intro z
    simpa [T, B] using hbound level z.1 z.2 ψ
  have hT_equi :
      UniformEquicontinuous (fun z : B => fun ψ => T z ψ) :=
    SchwartzMap.tempered_equicontinuous hT_pointwise
  have hT_fixed :
      ∀ ψ : SchwartzMap (Fin k → ℝ) ℂ,
        Continuous (fun z : B => T z ψ) := by
    intro ψ
    have hcontOn :
        ContinuousOn
          (fun z : SCV.ComplexChartSpace k =>
            localRecenteredDistributionOfOS
              R OS η hηsum χ w0 level z ψ)
          B := by
      exact
        (W.localRecenteredDistributionOfOS_differentiableOn
          OS hηsum χ level ψ).continuousOn.mono
            (Metric.closedBall_subset_ball (by
              nlinarith [W.sigma_pos]))
    have hrestrict :=
      continuousOn_iff_continuous_restrict.mp hcontOn
    simpa [T, B] using hrestrict
  let f : B → SchwartzMap (Fin k → ℝ) ℂ :=
    fun z => SCV.schwartzPartialEval₁CLM z.1 F
  have hf : Continuous f := by
    exact (SCV.continuous_schwartzPartialEval₁CLM F).comp
      continuous_subtype_val
  have hjoint :
      Continuous (fun p : B × B => T p.1 (f p.2)) :=
    continuous_joint_apply_of_uniformEquicontinuous
      (fun z : B => fun ψ => T z ψ) f hT_equi hT_fixed hf
  have hdiagMap : Continuous (fun z : B => (z, z)) := by
    fun_prop
  have hdiag :
      Continuous (fun z : B => T z (f z)) := by
    simpa using hjoint.comp hdiagMap
  have hcut :
      Continuous (fun z : B => χU z.1) :=
    χU.continuous.comp continuous_subtype_val
  rw [continuousOn_iff_continuous_restrict]
  simpa [T, f, B] using hcut.mul hdiag

/-- One chart cutoff constructs the pairing kernels at every spatial level,
and the whole level family shares a single mixed Schwartz-seminorm bound. -/
theorem LocalKernelWindowData.exists_uniformLocalPairingKernelFamilyOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    {R : CommonCarrierRegularityData A}
    {η ρ : ℝ}
    {w0 : OSIITimeGapSpace k}
    (W : LocalKernelWindowData R η ρ w0)
    (OS : OsterwalderSchraderAxioms d)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ∃ K : ℕ → SchwartzMap
        (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ,
      (∀ level ψ,
        SCV.KernelSupportWithin ψ R.radius →
          DifferentiableOn ℂ
            (fun z : SCV.ComplexChartSpace k =>
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ)
            (Metric.ball
              (0 : SCV.ComplexChartSpace k) (16 * W.sigma))) ∧
      (∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma)) →
        SCV.KernelSupportWithin ψ R.radius →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            ∫ z : SCV.ComplexChartSpace k,
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ * φ z) ∧
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ level
          (F : SchwartzMap
            (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ),
          ‖K level F‖ ≤
            C * s.sup
              (schwartzSeminormFamily ℂ
                (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ) F := by
  classical
  obtain ⟨χU, hχU_one, _hχU_support⟩ :=
    SCV.exists_complexChart_schwartz_cutoff_eq_one_on_closedBall
      (m := k) (R := 4 * W.sigma) (Rlarge := 8 * W.sigma)
      (by nlinarith [W.sigma_pos]) (by nlinarith [W.sigma_pos])
  obtain ⟨sL, CL, hCL, hLbound⟩ :=
    W.localRecenteredDistributionOfOS_uniform_schwartz_bound
      OS hηsum χ
  have hexists :
      ∀ level : ℕ,
        ∃ K : SchwartzMap
            (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ,
          (∀ ψ : SchwartzMap (Fin k → ℝ) ℂ,
            SCV.KernelSupportWithin ψ R.radius →
              DifferentiableOn ℂ
                (fun z : SCV.ComplexChartSpace k =>
                  localRecenteredDistributionOfOS
                    R OS η hηsum χ w0 level z ψ)
                (Metric.ball
                  (0 : SCV.ComplexChartSpace k) (16 * W.sigma))) ∧
          (∀ (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
              (ψ : SchwartzMap (Fin k → ℝ) ℂ),
            SCV.SupportsInOpen
              (φ : SCV.ComplexChartSpace k → ℂ)
              (Metric.ball
                (0 : SCV.ComplexChartSpace k) (4 * W.sigma)) →
            SCV.KernelSupportWithin ψ R.radius →
              K (SCV.schwartzTensorProduct₂ φ ψ) =
                ∫ z : SCV.ComplexChartSpace k,
                  localRecenteredDistributionOfOS
                    R OS η hηsum χ w0 level z ψ * φ z) ∧
          ∀ F : SchwartzMap
              (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ,
            K F =
              ∫ z in Metric.closedBall
                  (0 : SCV.ComplexChartSpace k) (8 * W.sigma),
                χU z *
                  localRecenteredDistributionOfOS
                    R OS η hηsum χ w0 level z
                      (SCV.schwartzPartialEval₁CLM z F) := by
    intro level
    apply SCV.localHolomorphicFamily_pairingCLM_of_fixedWindow
      (m := k)
      (Rcov := 4 * W.sigma)
      (Rcut := 8 * W.sigma)
      (Uhol :=
        Metric.ball (0 : SCV.ComplexChartSpace k) (16 * W.sigma))
      (χU := χU)
      (Good := fun ψ : SchwartzMap (Fin k → ℝ) ℂ =>
        SCV.KernelSupportWithin ψ R.radius)
      (G := fun ψ z =>
        localRecenteredDistributionOfOS
          R OS η hηsum χ w0 level z ψ)
      (L := fun z =>
        localRecenteredDistributionOfOS
          R OS η hηsum χ w0 level z)
    · nlinarith [W.sigma_pos]
    · nlinarith [W.sigma_pos]
    · exact Metric.ball_subset_ball (by nlinarith [W.sigma_pos])
    · exact hχU_one
    · intro z _hz ψ _hψ
      rfl
    · exact ⟨sL, CL, hCL, fun z hz ψ => hLbound level z hz ψ⟩
    · intro F
      exact W.localRecenteredDistributionOfOS_partialEval_continuousOn
        OS hηsum χ level χU F
    · intro ψ _hψ
      exact W.localRecenteredDistributionOfOS_differentiableOn
        OS hηsum χ level ψ
  choose K hK_holo hK_rep hK_eval using hexists
  let sball : Set (SCV.ComplexChartSpace k) :=
    Metric.closedBall (0 : SCV.ComplexChartSpace k) (8 * W.sigma)
  let pMixed :=
    schwartzSeminormFamily ℂ
      (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ
  have hs_compact : IsCompact sball := by
    exact isCompact_closedBall _ _
  have hs_fin : volume sball < ⊤ := by
    simpa [sball] using
      (measure_closedBall_lt_top
        (x := (0 : SCV.ComplexChartSpace k)) (r := 8 * W.sigma))
  obtain ⟨sPE, CPE, hCPE, hPE⟩ :=
    SCV.schwartzPartialEval₁CLM_compactSeminormBound
      (m := k) (8 * W.sigma)
      (by nlinarith [W.sigma_pos]) sL
  obtain ⟨M, hM⟩ :=
    hs_compact.exists_bound_of_continuousOn
      (f := fun z : SCV.ComplexChartSpace k => ‖χU z‖)
      ((continuous_norm.comp χU.continuous).continuousOn)
  let Mχ : ℝ := max M 0
  let Cpoint : ℝ := Mχ * CL * CPE
  let Cfinal : ℝ := Cpoint * (volume sball).toReal
  have hCfinal : 0 ≤ Cfinal := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by simp [Mχ]) hCL) hCPE)
      ENNReal.toReal_nonneg
  refine ⟨K, hK_holo, hK_rep, sPE, Cfinal, hCfinal, ?_⟩
  intro level F
  have hpoint_bound :
      ∀ z ∈ sball,
        ‖χU z *
          localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F)‖ ≤
          Cpoint * sPE.sup pMixed F := by
    intro z hz
    have hχ_bound : ‖χU z‖ ≤ Mχ := by
      have hMz : ‖χU z‖ ≤ M := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (χU z))]
          using hM z hz
      exact hMz.trans (le_max_left M 0)
    have hL :=
      hLbound level z (by simpa [sball] using hz)
        (SCV.schwartzPartialEval₁CLM z F)
    have hPE' :
        sL.sup (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ)
            (SCV.schwartzPartialEval₁CLM z F) ≤
          CPE * sPE.sup pMixed F := by
      simpa [sball, pMixed] using
        hPE z (by simpa [sball] using hz) F
    have hLmix :
        ‖localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F)‖ ≤
          (CL * CPE) * sPE.sup pMixed F := by
      calc
        _ ≤ CL *
            sL.sup (schwartzSeminormFamily ℂ (Fin k → ℝ) ℂ)
              (SCV.schwartzPartialEval₁CLM z F) := hL
        _ ≤ CL * (CPE * sPE.sup pMixed F) := by
          exact mul_le_mul_of_nonneg_left hPE' hCL
        _ = (CL * CPE) * sPE.sup pMixed F := by ring
    calc
      ‖χU z *
          localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F)‖
          =
        ‖χU z‖ *
          ‖localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F)‖ := norm_mul _ _
      _ ≤ Mχ * ((CL * CPE) * sPE.sup pMixed F) := by
        exact mul_le_mul hχ_bound hLmix
          (norm_nonneg _) (by simp [Mχ])
      _ = Cpoint * sPE.sup pMixed F := by ring
  rw [hK_eval level F]
  calc
    ‖∫ z in sball,
        χU z *
          localRecenteredDistributionOfOS
            R OS η hηsum χ w0 level z
              (SCV.schwartzPartialEval₁CLM z F)‖
        ≤
      (Cpoint * sPE.sup pMixed F) * (volume sball).toReal := by
        exact MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := volume) hs_fin hpoint_bound
    _ = Cfinal * sPE.sup pMixed F := by ring

/-- The explicit descended distribution attached to one member of a mixed
pairing-kernel family and one fixed normalized real-fiber bump. -/
def descendedLocalPairingDistribution
    (K : ℕ → SchwartzMap
      (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ)
    (ηb : SchwartzMap (Fin k → ℝ) ℂ)
    (level : ℕ) :
    SchwartzMap (SCV.ComplexChartSpace k) ℂ →L[ℂ] ℂ :=
  SCV.complexRealFiberTranslationDescentCLM
    (SCV.shearedProductKernelFunctional (K level)) ηb

/-- A common mixed-kernel seminorm bound survives the fixed shear and
real-fiber bump used by local descent.  Hence all descended distributions
share one finite family of chart-Schwartz seminorms. -/
theorem uniformLocalPairingKernelFamily_descended_bound
    (K : ℕ → SchwartzMap
      (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ)
    (ηb : SchwartzMap (Fin k → ℝ) ℂ)
    (sK : Finset (ℕ × ℕ))
    (CK : ℝ)
    (hCK : 0 ≤ CK)
    (hK : ∀ level
      (F : SchwartzMap
        (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ),
      ‖K level F‖ ≤
        CK * sK.sup
          (schwartzSeminormFamily ℂ
            (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ) F) :
    ∃ sH : Finset (ℕ × ℕ), ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ level (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ),
        ‖descendedLocalPairingDistribution K ηb level φ‖ ≤
          CH * sH.sup
            (schwartzSeminormFamily ℂ (SCV.ComplexChartSpace k) ℂ) φ := by
  let B :
      SchwartzMap (SCV.ComplexChartSpace k) ℂ →L[ℂ]
        SchwartzMap
          (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (SCV.realConvolutionShearCLE k).symm).comp
        (SCV.schwartzTensorProduct₂CLMRight ηb)
  obtain ⟨sH, CB, hCB, hB⟩ :=
    SCV.SchwartzMap.exists_schwartzCLM_finsetSeminormBound_between B sK
  refine ⟨sH, CK * CB, mul_nonneg hCK hCB, ?_⟩
  intro level φ
  have hK' := hK level (B φ)
  have hB' := hB φ
  calc
    ‖descendedLocalPairingDistribution K ηb level φ‖
        = ‖K level (B φ)‖ := by
          rfl
    _ ≤ CK * sK.sup
        (schwartzSeminormFamily ℂ
          (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ) (B φ) := hK'
    _ ≤ CK *
        (CB * sH.sup
          (schwartzSeminormFamily ℂ (SCV.ComplexChartSpace k) ℂ) φ) := by
          exact mul_le_mul_of_nonneg_left hB' hCK
    _ = (CK * CB) *
        sH.sup
          (schwartzSeminormFamily ℂ (SCV.ComplexChartSpace k) ℂ) φ := by
          ring

/-- The signed covariance radius, chart window, and pairing kernels can be
selected once for all spatial levels.  The resulting family has both a common
mixed-Schwartz bound and local covariance at every level. -/
theorem CommonCarrierRegularityData.exists_uniformLocallyCovariantPairingKernelFamilyOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w0 : OSIITimeGapSpace k)
    (hw0 : w0 ∈ osiiNarrowTimeCarrier (k := k) η) :
    ∃ (ρ : ℝ) (W : LocalKernelWindowData R η ρ w0)
      (K : ℕ → SchwartzMap
        (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ),
      (∀ level ψ,
        SCV.KernelSupportWithin ψ R.radius →
          DifferentiableOn ℂ
            (fun z : SCV.ComplexChartSpace k =>
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ)
            (Metric.ball
              (0 : SCV.ComplexChartSpace k) (16 * W.sigma))) ∧
      (∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma)) →
        SCV.KernelSupportWithin ψ R.radius →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            ∫ z : SCV.ComplexChartSpace k,
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ * φ z) ∧
      (∀ level,
        SCV.ProductKernelRealTranslationCovariantLocal (K level)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma))
          R.radius) ∧
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ level
          (F : SchwartzMap
            (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ),
          ‖K level F‖ ≤
            C * s.sup
              (schwartzSeminormFamily ℂ
                (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ) F := by
  obtain ⟨ρ, hρ, hcov⟩ :=
    R.exists_recentered_localCovarianceOfOS OS η hη hηsum
  obtain ⟨W⟩ :=
    R.exists_localKernelWindowData η ρ hρ w0 hw0
  obtain ⟨K, hK_holo, hK_rep, s, C, hC, hK_bound⟩ :=
    W.exists_uniformLocalPairingKernelFamilyOfOS OS hηsum χ
  refine ⟨ρ, W, K, hK_holo, hK_rep, ?_, s, C, hC, hK_bound⟩
  intro level
  apply SCV.localHolomorphicFamily_pairingCLM_localCovariant
    (m := k) (ρ := ρ)
    (K level)
    (fun ψ z =>
      localRecenteredDistributionOfOS
        R OS η hηsum χ w0 level z ψ)
    (4 * W.sigma) R.radius
  · nlinarith [W.covariance_small]
  · exact hK_rep level
  · intro ψ hψ
    exact (hK_holo level ψ hψ).continuousOn.mono
      (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]))
  · intro a ψ ha hψ hψa z hz hz_shift
    have hz_closed :
        z ∈ Metric.closedBall
          (0 : SCV.ComplexChartSpace k) (16 * W.sigma) := by
      exact Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]) hz)
    have hz_shift_closed :
        z - SCV.realEmbed a ∈ Metric.closedBall
          (0 : SCV.ComplexChartSpace k) (16 * W.sigma) := by
      exact Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]) hz_shift)
    have hw :
        w0 + z ∈ osiiNarrowTimeCarrier (k := k) η :=
      W.carrier_window z hz_closed
    have hshift_eq :
        w0 + z - osiiPositiveRealTimeEmbed a =
          w0 + (z - SCV.realEmbed a) := by
      ext i
      simp [SCV.realEmbed, osiiPositiveRealTimeEmbed]
      ring
    have hw_shift :
        w0 + z - osiiPositiveRealTimeEmbed a ∈
          osiiNarrowTimeCarrier (k := k) η := by
      rw [hshift_eq]
      exact W.carrier_window (z - SCV.realEmbed a) hz_shift_closed
    have hcov_apply :=
      hcov a ha ψ hψ hψa level (w0 + z) hw hw_shift χ
    rw [hshift_eq] at hcov_apply
    exact hcov_apply

/-- Uniform local descent for the common pairing-kernel family.  One
normalized real-fiber bump and one chart window work at every spatial level,
and the explicit descended distributions retain a common Schwartz bound. -/
theorem CommonCarrierRegularityData.exists_uniformDescendedDistributionFamilyOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w0 : OSIITimeGapSpace k)
    (hw0 : w0 ∈ osiiNarrowTimeCarrier (k := k) η) :
    ∃ (ρ : ℝ) (W : LocalKernelWindowData R η ρ w0)
      (K : ℕ → SchwartzMap
        (SCV.ComplexChartSpace k × (Fin k → ℝ)) ℂ →L[ℂ] ℂ)
      (ηb : SchwartzMap (Fin k → ℝ) ℂ),
      (∀ t : Fin k → ℝ, 0 ≤ (ηb t).re) ∧
      (∀ t : Fin k → ℝ, (ηb t).im = 0) ∧
      (∫ t : Fin k → ℝ, ηb t = 1) ∧
      SCV.KernelSupportWithin ηb (W.sigma / 2) ∧
      (∀ level ψ,
        SCV.KernelSupportWithin ψ R.radius →
          DifferentiableOn ℂ
            (fun z : SCV.ComplexChartSpace k =>
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ)
            (Metric.ball
              (0 : SCV.ComplexChartSpace k) (16 * W.sigma))) ∧
      (∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma)) →
        SCV.KernelSupportWithin ψ R.radius →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            ∫ z : SCV.ComplexChartSpace k,
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ * φ z) ∧
      (∀ level,
        SCV.ProductKernelRealTranslationCovariantLocal (K level)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma))
          R.radius) ∧
      (∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (2 * W.sigma)) →
        SCV.KernelSupportWithin ψ (W.sigma / 2) →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            descendedLocalPairingDistribution K ηb level
              (SCV.realConvolutionTest φ ψ)) ∧
      ∃ sH : Finset (ℕ × ℕ), ∃ CH : ℝ, 0 ≤ CH ∧
        ∀ level (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ),
          ‖descendedLocalPairingDistribution K ηb level φ‖ ≤
            CH * sH.sup
              (schwartzSeminormFamily ℂ
                (SCV.ComplexChartSpace k) ℂ) φ := by
  obtain ⟨ρ, W, K, hK_holo, hK_rep, hK_cov,
      sK, CK, hCK, hK_bound⟩ :=
    R.exists_uniformLocallyCovariantPairingKernelFamilyOfOS
      OS η hη hηsum χ w0 hw0
  obtain ⟨ηb, hηb_nonneg, hηb_real, hηb_norm, hηb_support⟩ :=
    SCV.exists_normalized_schwartz_bump_kernelSupportWithin
      (m := k) (W.sigma / 2) (half_pos W.sigma_pos)
  obtain ⟨sH, CH, hCH, hHdist_bound⟩ :=
    uniformLocalPairingKernelFamily_descended_bound
      K ηb sK CK hCK hK_bound
  have hmargin_desc_cov :
      ∀ z ∈ Metric.ball
          (0 : SCV.ComplexChartSpace k) (2 * W.sigma),
        ∀ t : Fin k → ℝ,
          ‖t‖ ≤ W.sigma / 2 + W.sigma / 2 →
          z + SCV.realEmbed t ∈
            Metric.ball
              (0 : SCV.ComplexChartSpace k) (4 * W.sigma) := by
    intro z hz t ht
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖z + SCV.realEmbed t‖
          ≤ ‖z‖ + ‖SCV.realEmbed t‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ‖t‖ := by
        gcongr
        exact SCV.norm_realEmbed_le t
      _ < 2 * W.sigma +
          (W.sigma / 2 + W.sigma / 2) := by
        exact add_lt_add_of_lt_of_le hz ht
      _ < 4 * W.sigma := by nlinarith [W.sigma_pos]
  have hsmall_radius :
      W.sigma / 2 + W.sigma / 2 ≤ R.radius := by
    have hsigma_radius : W.sigma ≤ R.radius := by
      have hsigma_two : W.sigma < 2 * W.sigma := by
        nlinarith [W.sigma_pos]
      exact (hsigma_two.trans W.kernel_small).le
    convert hsigma_radius using 1 <;> ring
  have hdesc :
      ∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (2 * W.sigma)) →
        SCV.KernelSupportWithin ψ (W.sigma / 2) →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            descendedLocalPairingDistribution K ηb level
              (SCV.realConvolutionTest φ ψ) := by
    intro level φ ψ hφ hψ
    have hK_cov_small :
        SCV.ProductKernelRealTranslationCovariantLocal (K level)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma))
          (W.sigma / 2 + W.sigma / 2) := by
      intro a φ' ψ' hφ' hφ'a hψ' hψ'a
      exact hK_cov level a φ' ψ' hφ' hφ'a
        (SCV.KernelSupportWithin.mono hψ' hsmall_radius)
        (SCV.KernelSupportWithin.mono hψ'a hsmall_radius)
    have hquotient :=
      SCV.shearedProductKernelFunctional_localQuotient_of_productCovariant
        (m := k)
        (r := W.sigma / 2)
        (rη := W.sigma / 2)
        (K level)
        (Metric.ball
          (0 : SCV.ComplexChartSpace k) (2 * W.sigma))
        (Metric.ball
          (0 : SCV.ComplexChartSpace k) (4 * W.sigma))
        (half_pos W.sigma_pos).le
        (half_pos W.sigma_pos).le
        ηb hηb_norm hηb_support hmargin_desc_cov hK_cov_small
        φ ψ hφ hψ
    simpa [descendedLocalPairingDistribution] using hquotient
  exact
    ⟨ρ, W, K, ηb, hηb_nonneg, hηb_real, hηb_norm, hηb_support,
      hK_holo, hK_rep, hK_cov, hdesc, sH, CH, hCH, hHdist_bound⟩

/-- The common recentered packet family has canonical local holomorphic
representatives with one pointwise bound on a closed chart ball, uniform in
the spatial exhaustion level. -/
theorem CommonCarrierRegularityData.exists_uniformLocalHolomorphicRepresentativeFamilyOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w0 : OSIITimeGapSpace k)
    (hw0 : w0 ∈ osiiNarrowTimeCarrier (k := k) η) :
    ∃ (ρ : ℝ) (W : LocalKernelWindowData R η ρ w0)
      (H : ℕ → SCV.ComplexChartSpace k → ℂ),
      (∀ level,
        DifferentiableOn ℂ (H level)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (2 * W.sigma))) ∧
      (∀ level (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.KernelSupportWithin ψ (W.sigma / 2) →
        ∀ z ∈ Metric.ball
          (0 : SCV.ComplexChartSpace k) (W.sigma / 2),
          localRecenteredDistributionOfOS
              R OS η hηsum χ w0 level z ψ =
            ∫ t : Fin k → ℝ,
              H level (z + SCV.realEmbed t) * ψ t) ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ level z,
          z ∈ Metric.closedBall
            (0 : SCV.ComplexChartSpace k) W.sigma →
            ‖H level z‖ ≤ M := by
  obtain ⟨ρ, W, K, ηb, _hηb_nonneg, _hηb_real,
      _hηb_norm, _hηb_support, hG_holo, hK_rep, _hK_cov,
      hdesc, sH, CH, hCH, hHdist_bound⟩ :=
    R.exists_uniformDescendedDistributionFamilyOfOS
      OS η hη hηsum χ w0 hw0
  let Hdist : ℕ →
      SchwartzMap (SCV.ComplexChartSpace k) ℂ →L[ℂ] ℂ :=
    descendedLocalPairingDistribution K ηb
  have hsigma_radius : W.sigma ≤ R.radius := by
    have hsigma_two : W.sigma < 2 * W.sigma := by
      nlinarith [W.sigma_pos]
    exact (hsigma_two.trans W.kernel_small).le
  have hhalf_radius : W.sigma / 2 ≤ R.radius := by
    exact (by nlinarith [W.sigma_pos] : W.sigma / 2 ≤ W.sigma).trans
      hsigma_radius
  have hmargin_core :
      ∀ z ∈ Metric.ball
          (0 : SCV.ComplexChartSpace k) (W.sigma / 2),
        ∀ t : Fin k → ℝ, ‖t‖ ≤ W.sigma / 2 →
          z + SCV.realEmbed t ∈
            Metric.ball
              (0 : SCV.ComplexChartSpace k) (2 * W.sigma) := by
    intro z hz t ht
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖z + SCV.realEmbed t‖
          ≤ ‖z‖ + ‖SCV.realEmbed t‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ‖t‖ := by
        gcongr
        exact SCV.norm_realEmbed_le t
      _ < W.sigma / 2 + W.sigma / 2 := by
        exact add_lt_add_of_lt_of_le hz ht
      _ < 2 * W.sigma := by nlinarith [W.sigma_pos]
  have hcompact_subset :
      Metric.closedBall
          (0 : SCV.ComplexChartSpace k) W.sigma ⊆
        Metric.ball
          (0 : SCV.ComplexChartSpace k) (2 * W.sigma) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    nlinarith [W.sigma_pos]
  have hG_holo_small :
      ∀ level ψ,
        SCV.KernelSupportWithin ψ (W.sigma / 2) →
          DifferentiableOn ℂ
            (fun z : SCV.ComplexChartSpace k =>
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ)
            (Metric.ball
              (0 : SCV.ComplexChartSpace k) (16 * W.sigma)) := by
    intro level ψ hψ
    exact hG_holo level ψ
      (SCV.KernelSupportWithin.mono hψ hhalf_radius)
  have hK_rep_small :
      ∀ level
          (φ : SchwartzMap (SCV.ComplexChartSpace k) ℂ)
          (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
          (φ : SCV.ComplexChartSpace k → ℂ)
          (Metric.ball
            (0 : SCV.ComplexChartSpace k) (4 * W.sigma)) →
        SCV.KernelSupportWithin ψ (W.sigma / 2) →
          K level (SCV.schwartzTensorProduct₂ φ ψ) =
            ∫ z : SCV.ComplexChartSpace k,
              localRecenteredDistributionOfOS
                R OS η hηsum χ w0 level z ψ * φ z := by
    intro level φ ψ hφ hψ
    exact hK_rep level φ ψ hφ
      (SCV.KernelSupportWithin.mono hψ hhalf_radius)
  obtain ⟨H, hH_holo, _hH_rep, hpointwise, M, hM, hH_bound⟩ :=
    SCV.localProductKernel_holomorphicRepresentative_uniform_compact
      (m := k)
      (r := W.sigma / 2)
      (Nat.pos_of_ne_zero (NeZero.ne k))
      (half_pos W.sigma_pos)
      K
      (fun level ψ z =>
        localRecenteredDistributionOfOS
          R OS η hηsum χ w0 level z ψ)
      Hdist
      (Metric.ball
        (0 : SCV.ComplexChartSpace k) (W.sigma / 2))
      (Metric.ball
        (0 : SCV.ComplexChartSpace k) (2 * W.sigma))
      (Metric.ball
        (0 : SCV.ComplexChartSpace k) (4 * W.sigma))
      (Metric.ball
        (0 : SCV.ComplexChartSpace k) (16 * W.sigma))
      (Metric.closedBall
        (0 : SCV.ComplexChartSpace k) W.sigma)
      Metric.isOpen_ball
      Metric.isOpen_ball
      (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]))
      (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]))
      (Metric.ball_subset_ball (by nlinarith [W.sigma_pos]))
      (isCompact_closedBall _ _)
      hcompact_subset
      hmargin_core
      hG_holo_small
      hK_rep_small
      hdesc
      sH CH hCH
      (by simpa [Hdist] using hHdist_bound)
  exact ⟨ρ, W, H, hH_holo, hpointwise, M, hM, hH_bound⟩

/-- The local uniformly bounded holomorphic kernels globalize over compact
subsets of the narrow carrier and control every shrinking packet scale. -/
theorem CommonCarrierRegularityData.family_hasUniformPacketCompactBoundOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    R.family.HasUniformPacketCompactBoundOfOS OS η hηsum := by
  rw [R.family.hasUniformPacketCompactBoundOfOS_iff_commonTimeShellDistributionOfOS
    OS η hη hηsum]
  intro K hK_compact hK_subset χ
  let β := {w : OSIITimeGapSpace k // w ∈ K}
  choose ρ W H hH_holo hH_pointwise M hM hH_bound using
    fun w : β =>
      R.exists_uniformLocalHolomorphicRepresentativeFamilyOfOS
        OS η hη hηsum χ w.1 (hK_subset w.2)
  let U : β → Set (OSIITimeGapSpace k) := fun w =>
    Metric.ball w.1 ((W w).sigma / 2)
  have hU_open : ∀ w : β, IsOpen (U w) := by
    intro w
    exact Metric.isOpen_ball
  have hK_cover : K ⊆ ⋃ w : β, U w := by
    intro ζ hζ
    refine mem_iUnion.mpr ⟨⟨ζ, hζ⟩, ?_⟩
    exact Metric.mem_ball_self (half_pos (W ⟨ζ, hζ⟩).sigma_pos)
  obtain ⟨t, ht_cover⟩ :=
    hK_compact.elim_finite_subcover U hU_open hK_cover
  have htail_exists :
      ∀ w : β, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        R.family.timeRadius N ≤ (W w).sigma / 2 := by
    intro w
    have hevent :
        ∀ᶠ N : ℕ in Filter.atTop,
          dist (R.family.timeRadius N) 0 < (W w).sigma / 2 :=
      (Metric.tendsto_nhds.mp R.family.timeRadius_tendsto)
        ((W w).sigma / 2) (half_pos (W w).sigma_pos)
    rw [Filter.eventually_atTop] at hevent
    obtain ⟨N₀, hN₀⟩ := hevent
    refine ⟨N₀, ?_⟩
    intro N hN
    have hdist := hN₀ N hN
    rw [Real.dist_eq] at hdist
    have habs :
        |R.family.timeRadius N| < (W w).sigma / 2 := by
      simpa using hdist
    exact (le_abs_self _).trans habs.le
  choose N₀ hN₀ using htail_exists
  let Ntail : ℕ := ∑ w ∈ t, N₀ w
  have hN₀_le : ∀ w ∈ t, N₀ w ≤ Ntail := by
    intro w hw
    dsimp [Ntail]
    exact Finset.single_le_sum
      (fun v _hv => Nat.zero_le (N₀ v)) hw
  have hhead_exists :
      ∀ N : Fin Ntail, ∃ C : ℝ, ∀ level ζ, ζ ∈ K →
        ‖R.family.commonTimeShellDistributionOfOS
            OS η hηsum level ζ χ (R.family.timeTest N)‖ ≤ C := by
    intro N
    exact R.family.commonTimeShellDistributionOfOS_fixedTest_compact_bound
      OS η hηsum K hK_compact hK_subset χ
        (R.family.timeTest N)
  choose Chead hChead using hhead_exists
  let C₀ : ℝ := ∑ N : Fin Ntail, max (Chead N) 0
  let C₁ : ℝ := ∑ w ∈ t, M w
  refine ⟨C₀ + C₁, ?_⟩
  intro N level ζ hζ
  by_cases hN : N < Ntail
  · let n : Fin Ntail := ⟨N, hN⟩
    calc
      ‖R.family.commonTimeShellDistributionOfOS
          OS η hηsum level ζ χ (R.family.timeTest N)‖
          ≤ Chead n := hChead n level ζ hζ
      _ ≤ max (Chead n) 0 := le_max_left _ _
      _ ≤ C₀ := by
        dsimp [C₀]
        exact Finset.single_le_sum
          (fun i _hi => le_max_right (Chead i) 0)
          (Finset.mem_univ n)
      _ ≤ C₀ + C₁ := by
        have hC₁ : 0 ≤ C₁ := by
          dsimp [C₁]
          exact Finset.sum_nonneg fun w hw => hM w
        linarith
  · have hNtail : Ntail ≤ N := Nat.le_of_not_gt hN
    have hζ_cover : ζ ∈ ⋃ w ∈ t, U w := ht_cover hζ
    rcases mem_iUnion.mp hζ_cover with ⟨w, hζ_cover⟩
    rcases mem_iUnion.mp hζ_cover with ⟨hw, hζU⟩
    let z : SCV.ComplexChartSpace k := ζ - w.1
    let ψ : SchwartzMap (Fin k → ℝ) ℂ :=
      I.test (N + R.family.carrierData.tailStart)
    have hz :
        z ∈ Metric.ball
          (0 : SCV.ComplexChartSpace k) ((W w).sigma / 2) := by
      simpa [z, U, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hζU
    have hradius :
        R.family.timeRadius N ≤ (W w).sigma / 2 :=
      hN₀ w N ((hN₀_le w hw).trans hNtail)
    have hψ_support :
        SCV.KernelSupportWithin ψ ((W w).sigma / 2) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      exact (I.support (N + R.family.carrierData.tailStart)).trans
        (Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall
            (by simpa [ψ, AnchoredPacketTimeShellFamilyData.timeRadius]
              using hradius)))
    have hpoint :=
      hH_pointwise w level ψ hψ_support z hz
    have hdistribution_eq :
        R.family.commonTimeShellDistributionOfOS
            OS η hηsum level ζ χ (R.family.timeTest N) =
          ∫ s : Fin k → ℝ,
            H w level (z + SCV.realEmbed s) * ψ s := by
      rw [← hpoint]
      simp [localRecenteredDistributionOfOS_apply, z, ψ,
        AnchoredPacketTimeShellFamilyData.timeTest]
    have hF_bound :
        ∀ s ∈ tsupport (ψ : (Fin k → ℝ) → ℂ),
          ‖H w level (z + SCV.realEmbed s)‖ ≤ M w := by
      intro s hs
      have hs_ball := hψ_support hs
      rw [Metric.mem_closedBall, dist_zero_right] at hs_ball
      apply hH_bound w level (z + SCV.realEmbed s)
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖z + SCV.realEmbed s‖
            ≤ ‖z‖ + ‖SCV.realEmbed s‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ‖s‖ := by
          gcongr
          exact SCV.norm_realEmbed_le s
        _ ≤ (W w).sigma / 2 + (W w).sigma / 2 := by
          have hz_le :
              ‖z‖ ≤ (W w).sigma / 2 := by
            rw [Metric.mem_ball, dist_zero_right] at hz
            exact hz.le
          exact add_le_add hz_le hs_ball
        _ = (W w).sigma := by ring
    have hlocal_bound :
        ‖R.family.commonTimeShellDistributionOfOS
            OS η hηsum level ζ χ (R.family.timeTest N)‖ ≤ M w := by
      rw [hdistribution_eq]
      exact SCV.norm_integral_mul_le_of_tsupport_bound
        ψ (fun s => H w level (z + SCV.realEmbed s)) (M w)
        (fun s => I.nonnegative
          (N + R.family.carrierData.tailStart) s)
        (fun s => I.real
          (N + R.family.carrierData.tailStart) s)
        (I.integral_one (N + R.family.carrierData.tailStart))
        hF_bound
    have hM_le : M w ≤ C₁ := by
      dsimp [C₁]
      exact Finset.single_le_sum
        (fun v _hv => hM v) hw
    have hC₀ : 0 ≤ C₀ := by
      dsimp [C₀]
      exact Finset.sum_nonneg fun n _hn => le_max_right (Chead n) 0
    exact hlocal_bound.trans (hM_le.trans (by linarith))

/-- The compact packet estimate follows for the original anchored family
because the carrier enlargement retains exactly the same approximate-identity
tail. -/
theorem CommonCarrierRegularityData.hasUniformPacketCompactBoundOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    A.HasUniformPacketCompactBoundOfOS OS η hηsum := by
  have hfamily :=
    R.family_hasUniformPacketCompactBoundOfOS OS η hη hηsum
  simpa [HasUniformPacketCompactBoundOfOS,
    AnchoredPacketTimeShellFamilyData.timeTest, R.tailStart_eq] using hfamily

/-- The foundational E-to-R packet bound is a theorem of the stated OS
hypotheses; no sharp-time restriction or additional analytic axiom is used. -/
theorem hasUniformPacketCompactBoundOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    A.HasUniformPacketCompactBoundOfOS OS η hηsum := by
  obtain ⟨R⟩ := A.nonempty_commonCarrierRegularityData
  exact R.hasUniformPacketCompactBoundOfOS OS η hη hηsum

/-- A zero-tail anchored carrier transfers its original-OS compact bound
directly to every untranslated approximate-identity scale. -/
theorem initialSpatialFactorPacketDistributionOfOS_scaleUniform_compact_bound
    (I : Section43ProductTimeApproximateIdentity k)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (tailStart : ℕ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ∃ C : ℝ, ∀ N level ζ, ζ ∈ K →
      ‖initialSpatialFactorPacketDistributionOfOS
          OS (I.test (N + tailStart))
            (I.test_compact (N + tailStart))
            (I.test_positive (N + tailStart))
            η hηsum level ζ χ‖ ≤ C := by
  obtain ⟨anchor, hanchor, hshift⟩ :=
    exists_positive_anchor_sub_mem_osiiNarrowTimeCarrier
      η K hK_compact hK_subset
  obtain ⟨A, hA_zero⟩ :=
    Section43ProductTimeApproximateIdentity.exists_anchoredPacketTimeShellFamilyData_zeroTail
      (d := d) I anchor hanchor
  let shift : OSIITimeGapSpace k → OSIITimeGapSpace k :=
    fun ζ => ζ - osiiPositiveRealTimeEmbed anchor
  let Kshift : Set (OSIITimeGapSpace k) := shift '' K
  have hKshift_compact : IsCompact Kshift :=
    hK_compact.image (continuous_id.sub continuous_const)
  have hKshift_subset :
      Kshift ⊆ osiiNarrowTimeCarrier (k := k) η := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hshift ζ hζ
  obtain ⟨C, hC⟩ :=
    A.hasUniformPacketCompactBoundOfOS OS η hη hηsum
      Kshift hKshift_compact hKshift_subset χ
  refine ⟨C, ?_⟩
  intro N level ζ hζ
  let φ := I.test (N + tailStart)
  have hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ) :=
    I.test_compact (N + tailStart)
  have hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k :=
    I.test_positive (N + tailStart)
  obtain ⟨htranslated_positive, htranslated_compact⟩ :=
    translate_positiveOrthant_schwartz_mem
      φ hφ_positive hφ_compact anchor hanchor
  let P := initialSpatialFactorPacketData
    (d := d) (SCV.translateSchwartz (-anchor) φ)
      htranslated_compact htranslated_positive level
  let Q := initialSpatialFactorPacketData
    (d := d) φ hφ_compact hφ_positive level
  have hζshift : shift ζ ∈ Kshift := ⟨ζ, hζ, rfl⟩
  have htranslation :=
    InitialSpatialFactorPacketData.narrowDistributionOfOS_translate_timeTest
      anchor hanchor P Q OS η hη hηsum χ (hKshift_subset hζshift)
  have hshift_add :
      shift ζ + osiiPositiveRealTimeEmbed anchor = ζ := by
    dsimp [shift]
    module
  have htest :
      A.timeTest (N + tailStart) =
        SCV.translateSchwartz (-anchor) φ := by
    simp [AnchoredPacketTimeShellFamilyData.timeTest, hA_zero, φ]
  have hdistribution_congr :
      ∀ (f g : SchwartzMap (Fin k → ℝ) ℂ)
        (hf : HasCompactSupport (f : (Fin k → ℝ) → ℂ))
        (hg : HasCompactSupport (g : (Fin k → ℝ) → ℂ))
        (hfp : tsupport (f : (Fin k → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion k)
        (hgp : tsupport (g : (Fin k → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion k),
        f = g →
          initialSpatialFactorPacketDistributionOfOS
              OS f hf hfp η hηsum level (shift ζ) χ =
            initialSpatialFactorPacketDistributionOfOS
              OS g hg hgp η hηsum level (shift ζ) χ := by
    intro f g hf hg hfp hgp hfg
    subst g
    rfl
  have hpacket :
      initialSpatialFactorPacketDistributionOfOS
          OS (A.timeTest (N + tailStart))
            (A.timeTest_compact (N + tailStart))
            (A.timeTest_positive (N + tailStart))
            η hηsum level (shift ζ) χ =
        initialSpatialFactorPacketDistributionOfOS
          OS φ hφ_compact hφ_positive
            η hηsum level ζ χ := by
    calc
      _ = initialSpatialFactorPacketDistributionOfOS
          OS (SCV.translateSchwartz (-anchor) φ)
            htranslated_compact htranslated_positive
            η hηsum level (shift ζ) χ :=
        hdistribution_congr _ _ _ _ _ _ htest
      _ = _ := by
        simpa [initialSpatialFactorPacketDistributionOfOS,
          P, Q, hshift_add] using htranslation
  have hbound := hC (N + tailStart) level (shift ζ) hζshift
  rw [hpacket] at hbound
  simpa [φ] using hbound

/-- Every fixed member of the genuine approximate identity has a
continuation stage and its exact Schwinger edge under the original OS
axioms. -/
theorem exists_initialTimeContinuationStageWithRealEdgeOfOS
    (I : Section43ProductTimeApproximateIdentity k)
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    ∃ A : OSIITimeContinuationStage d k,
      A.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
          A.distribution
          (osiiNarrowTimeCarrier (k := k) η) ∧
        (∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Tendsto
              (fun level =>
                initialSpatialFactorPacketDistributionOfOS
                  OS (I.test n) (I.test_compact n) (I.test_positive n)
                    η hηsum level ζ χ)
              atTop
              (nhds (A.distribution ζ χ))) ∧
        ∀ τ, ∀ hτ : τ ∈ section43TimeStrictPositiveRegion k,
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            A.distribution (osiiPositiveRealTimeEmbed τ) χ =
              OS.S (k + 1)
                ⟨initialReducedSpatialFullSourceCLM (d := d)
                    (SCV.translateSchwartz (-τ) (I.test n)) χ,
                  initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
                    (d := d) (SCV.translateSchwartz (-τ) (I.test n)) χ
                    (translate_positiveOrthant_schwartz_mem
                      (I.test n) (I.test_positive n) (I.test_compact n)
                      τ hτ).1⟩ := by
  apply exists_initialTimeContinuationStageOfOS_with_realEdge_of_factorwise_uniformBound
    OS (I.test n) (I.test_compact n) (I.test_positive n) η hη hηsum
  intro K hK_compact hK_subset χ
  obtain ⟨C, hC⟩ :=
    initialSpatialFactorPacketDistributionOfOS_scaleUniform_compact_bound
      I OS η hη hηsum n K hK_compact hK_subset χ
  exact ⟨C, fun level ζ hζ => by simpa using hC 0 level ζ hζ⟩

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
