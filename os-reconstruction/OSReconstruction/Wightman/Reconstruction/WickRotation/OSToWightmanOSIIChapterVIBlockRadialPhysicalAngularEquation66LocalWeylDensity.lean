/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66DensityRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapSynchronizedCommonSlope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedFlatWickCovariance
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalProductRecovery
import OSReconstruction.SCV.DistributionalRepresentationUniqueness














noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

namespace OSIIStep4FullSchwartzAngularContinuationData

private abbrev FlatSource := Fin (k * (d + 1)) -> Real

/-- Pull a flat test centered at zero to the reduced source chart centered at
`XiHat`. -/
noncomputable def equation66_centeredFlatReducedSourceCLM :
    SchwartzMap (FlatSource (d := d) (k := k)) Complex →L[Complex]
      SchwartzNPoint d k :=
  (unflattenSchwartzNPoint (d := d)).comp
    (SCV.translateSchwartzCLM
      (-osiiStep4MultiGapXiHatCenter d k center))

@[simp] theorem equation66_centeredFlatReducedSourceCLM_apply
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex) :
    equation66_centeredFlatReducedSourceCLM (d := d) (k := k)
        (center := center) psi =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz
          (-osiiStep4MultiGapXiHatCenter d k center) psi) := by
  rfl

/-- The full absolute-coordinate source used by the angular distribution. -/
noncomputable def equation66_centeredFlatFullSourceCLM :
    SchwartzMap (FlatSource (d := d) (k := k)) Complex →L[Complex]
      SchwartzNPoint d (k + 1) :=
  (BHW.reducedTestLift k d
    (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz).comp
      (equation66_centeredFlatReducedSourceCLM (d := d) (k := k)
        (center := center))

@[simp] theorem equation66_centeredFlatFullSourceCLM_apply
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex) :
    equation66_centeredFlatFullSourceCLM (d := d) (k := k)
        (center := center) psi =
      BHW.reducedTestLift k d
        (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
        (equation66_centeredFlatReducedSourceCLM (d := d) (k := k)
          (center := center) psi) := by
  rfl

theorem equation66_centeredFlatReducedSource_translate
    (a : FlatSource (d := d) (k := k))
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex) :
    equation66_centeredFlatReducedSourceCLM (d := d) (k := k) (center := center)
        (SCV.translateSchwartz a psi) =
      translateSchwartzConfiguration
        (osiiAxisPairUnflattenRealBlocks (d := d) a)
        (equation66_centeredFlatReducedSourceCLM (d := d) (k := k)
          (center := center) psi) := by
  ext x
  simp [equation66_centeredFlatReducedSourceCLM_apply,
    unflattenSchwartzNPoint_apply, SCV.translateSchwartz_apply,
    translateSchwartzConfiguration_apply,
    osiiAxisPairUnflattenRealBlocks]
  congr 1
  ext i
  simp
  have hi : finProdFinEquiv (i.divNat, i.modNat) = i :=
    finProdFinEquiv.apply_symm_apply i
  rw [hi]
  ring

theorem equation66_centeredFlatReducedSource_support
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex)
    (r : Real) (hr : r <= rho / 4)
    (hpsi : SCV.KernelSupportWithin psi r) :
    Function.support
        (flattenSchwartzNPoint (d := d)
          (equation66_centeredFlatReducedSourceCLM
            (d := d) (k := k) (center := center) psi)) ⊆
      Metric.closedBall
        (osiiStep4MultiGapXiHatCenter d k center) (rho / 4) := by
  intro x hx
  let c := osiiStep4MultiGapXiHatCenter d k center
  have hxne : psi (x - c) != 0 := by
    simpa [Function.mem_support, c, equation66_centeredFlatReducedSourceCLM,
      flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply,
      SCV.translateSchwartz_apply] using hx
  have hxt : x - c ∈ tsupport
      (psi : FlatSource (d := d) (k := k) -> Complex) :=
    subset_closure (by simpa [Function.mem_support] using hxne)
  have hball := hpsi hxt
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hball.trans hr

/-- The current angular continuation, tested against a flat source centered
at the origin. -/
noncomputable def equation66_centeredFlatPairing
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex)
    (z : Fin (k * (d + 1)) -> Complex) : Complex :=
  D.complexTargetPairing
    (equation66_centeredFlatReducedSourceCLM
      (d := d) (k := k) (center := center) psi) z

/-- Continuous-linear form of the centered flat pairing at an arbitrary
complex displacement. -/
noncomputable def equation66_centeredFlatPairingCLM
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (z : Fin (k * (d + 1)) -> Complex) :
    SchwartzMap (FlatSource (d := d) (k := k)) Complex →L[Complex] Complex :=
  (D.distribution
    (osiiStep4MultiGapComplexTargetLog d k Z.uniform.T center z)).comp
      (equation66_centeredFlatFullSourceCLM
        (d := d) (k := k) (center := center))

/-- Compact-local equicontinuity and weak holomorphy produce the mixed
product functional needed by local Weyl recovery. -/
theorem equation66_exists_centeredFlatPairingKernel
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (R sigma : Real) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 8)
    (hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain) :
    ∃ K : SchwartzMap
        ((Fin (k * (d + 1)) -> Complex) ×
          (FlatSource (d := d) (k := k))) Complex →L[Complex] Complex,
      (∀ psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex,
        DifferentiableOn Complex (D.equation66_centeredFlatPairing psi)
          (Metric.ball 0 R)) ∧
      ∀ (phi : SchwartzMap (Fin (k * (d + 1)) -> Complex) Complex)
          (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex),
        SCV.SupportsInOpen
          (phi : (Fin (k * (d + 1)) -> Complex) -> Complex)
          (Metric.ball 0 (2 * sigma)) ->
        K (SCV.schwartzTensorProduct₂ phi psi) =
          ∫ z : Fin (k * (d + 1)) -> Complex,
            D.equation66_centeredFlatPairing psi z * phi z := by
  let B : Set (Fin (k * (d + 1)) -> Complex) :=
    Metric.closedBall 0 (3 * sigma)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_domain : B ⊆ D.complexTargetDomain := by
    intro z hz
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz (by linarith)
  let logMap : (Fin (k * (d + 1)) -> Complex) ->
      (Fin k -> osiiAxisPairIndex d -> Complex) :=
    osiiStep4MultiGapComplexTargetLog d k Z.uniform.T center
  let Klog : Set (Fin k -> osiiAxisPairIndex d -> Complex) :=
    logMap '' B
  have hlog_cont : ContinuousOn logMap B := by
    exact
      (differentiableOn_osiiStep4MultiGapComplexTargetLog
        d k Z.uniform.T center).continuousOn.mono
          (fun z hz => (hB_domain hz).1)
  have hKlog_compact : IsCompact Klog :=
    hB_compact.image_of_continuousOn hlog_cont
  have hKlog_carrier : Klog ⊆ D.carrier := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hB_domain hz).2
  obtain ⟨sD, CD, hCD, hDbound⟩ :=
    D.exists_uniform_schwartzBound_on_compact
      Klog hKlog_compact hKlog_carrier
  obtain ⟨s, Cmap, hCmap, hmap⟩ :=
    SCV.SchwartzMap.exists_schwartzCLM_finsetSeminormBound_between
      (equation66_centeredFlatFullSourceCLM
        (d := d) (k := k) (center := center)) sD
  have hLbound :
      ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 <= C ∧
        ∀ z ∈ Metric.closedBall
            (0 : Fin (k * (d + 1)) -> Complex) (3 * sigma),
        ∀ psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex,
          ‖D.equation66_centeredFlatPairingCLM z psi‖ <=
            C * s.sup
              (schwartzSeminormFamily Complex
                (FlatSource (d := d) (k := k)) Complex) psi := by
    refine ⟨s, CD * Cmap, mul_nonneg hCD.le hCmap, ?_⟩
    intro z hz psi
    have hzB : z ∈ B := hz
    have hzlog : logMap z ∈ Klog := ⟨z, hzB, rfl⟩
    calc
      ‖D.equation66_centeredFlatPairingCLM z psi‖ <=
          CD * sD.sup
            (schwartzSeminormFamily Complex
              (NPointDomain d (k + 1)) Complex)
            (equation66_centeredFlatFullSourceCLM
              (d := d) (k := k) (center := center) psi) := by
        exact hDbound (logMap z) hzlog _
      _ <= CD * (Cmap * s.sup
            (schwartzSeminormFamily Complex
              (FlatSource (d := d) (k := k)) Complex) psi) := by
        exact mul_le_mul_of_nonneg_left (hmap psi) hCD.le
      _ = (CD * Cmap) * s.sup
            (schwartzSeminormFamily Complex
              (FlatSource (d := d) (k := k)) Complex) psi := by ring
  obtain ⟨chi, hchi_one, _hchi_support⟩ :=
    SCV.exists_complexChart_schwartz_cutoff_eq_one_on_closedBall
      (m := k * (d + 1))
      (R := 2 * sigma) (Rlarge := 3 * sigma)
      (by positivity) (by linarith)
  have hcont_integrand :
      ∀ F : SchwartzMap
          ((Fin (k * (d + 1)) -> Complex) ×
            (FlatSource (d := d) (k := k))) Complex,
        ContinuousOn
          (fun z : Fin (k * (d + 1)) -> Complex =>
            chi z * D.equation66_centeredFlatPairingCLM z
              (SCV.schwartzPartialEval₁CLM z F))
          (Metric.closedBall 0 (3 * sigma)) := by
    intro F
    let inner : (Fin (k * (d + 1)) -> Complex) ->
        (Fin k -> osiiAxisPairIndex d -> Complex) ×
          SchwartzNPoint d (k + 1) := fun z =>
      (logMap z,
        equation66_centeredFlatFullSourceCLM
          (d := d) (k := k) (center := center)
          (SCV.schwartzPartialEval₁CLM z F))
    have hinner : ContinuousOn inner B := by
      apply ContinuousOn.prodMk hlog_cont
      exact
        ((equation66_centeredFlatFullSourceCLM
          (d := d) (k := k) (center := center)).continuous.comp
          (SCV.continuous_schwartzPartialEval₁CLM F)).continuousOn
    have hmaps : MapsTo inner B (D.carrier ×ˢ Set.univ) := by
      intro z hz
      exact ⟨(hB_domain hz).2, Set.mem_univ _⟩
    have hpair : ContinuousOn
        (fun z : Fin (k * (d + 1)) -> Complex =>
          D.equation66_centeredFlatPairingCLM z
            (SCV.schwartzPartialEval₁CLM z F)) B := by
      simpa [inner, equation66_centeredFlatPairingCLM, logMap] using
        D.continuousOn_joint.comp hinner hmaps
    exact (chi.continuous.continuousOn.mul hpair)
  obtain ⟨K, hKholo, hKrep, _hKeval⟩ :=
    SCV.localHolomorphicFamily_pairingCLM_of_fixedWindow
      (m := k * (d + 1))
      (Rcov := 2 * sigma) (Rcut := 3 * sigma)
      (hRcov_pos := by positivity) (hRcov_cut := by linarith)
      (Uhol := Metric.ball 0 R)
      (hUcov_hol := by
        exact Metric.ball_subset_ball (by linarith))
      (chi) hchi_one
      (Good := fun _ : SchwartzMap
        (FlatSource (d := d) (k := k)) Complex => True)
      (G := D.equation66_centeredFlatPairing)
      (L := D.equation66_centeredFlatPairingCLM)
      (hL_value := fun _ _ _ _ => rfl)
      (hL_bound := hLbound)
      (hcont_integrand := hcont_integrand)
      (hG_holo := fun psi _ =>
        (D.complexTargetPairing_differentiableOn
          (equation66_centeredFlatReducedSourceCLM
            (d := d) (k := k) (center := center) psi)).mono hball)
  exact ⟨K, fun psi => hKholo psi trivial,
    fun phi psi hphi => hKrep phi psi hphi trivial⟩

theorem equation66_centeredFlatPairing_translate_eq
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (R sigma : Real) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 8)
    (hsigma_rho : sigma <= rho / 2)
    (hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain)
    (a : FlatSource (d := d) (k := k))
    (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex)
    (ha : ‖a‖ < 5 * sigma)
    (hpsi : SCV.KernelSupportWithin psi (sigma / 2))
    (hpsi_shift : SCV.KernelSupportWithin
      (SCV.translateSchwartz a psi) (sigma / 2))
    (w : Fin (k * (d + 1)) -> Complex)
    (hw : w ∈ Metric.ball 0 (2 * sigma)) :
    D.equation66_centeredFlatPairing (SCV.translateSchwartz a psi) w =
      D.equation66_centeredFlatPairing psi (w - SCV.realEmbed a) := by
  have hsource := equation66_centeredFlatReducedSource_support
    (d := d) (k := k) (rho := rho) (center := center)
    psi (sigma / 2) (by linarith) hpsi
  have hsource_shift := equation66_centeredFlatReducedSource_support
    (d := d) (k := k) (rho := rho) (center := center)
    (SCV.translateSchwartz a psi) (sigma / 2) (by linarith) hpsi_shift
  have ha_unflatten :
      osiiAxisPairUnflattenRealBlocks (d := d) a =
        fun i mu => a (finProdFinEquiv (i, mu)) := by
    ext i mu
    exact osiiAxisPairUnflattenRealBlocks_apply a i mu
  have hsource_translate :
      translateSchwartzConfiguration
          (fun i mu => a (finProdFinEquiv (i, mu)))
          (equation66_centeredFlatReducedSourceCLM
            (d := d) (k := k) (center := center) psi) =
        equation66_centeredFlatReducedSourceCLM
          (d := d) (k := k) (center := center)
          (SCV.translateSchwartz a psi) := by
    rw [← ha_unflatten]
    exact (equation66_centeredFlatReducedSource_translate
      (d := d) (k := k) (center := center) a psi).symm
  have hU_domain : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) (2 * sigma) ⊆
      D.complexTargetDomain := by
    intro z hz
    apply hball
    exact Metric.ball_subset_ball (by linarith) hz
  have hU_shift : ∀ z,
      z ∈ Metric.ball
        (0 : Fin (k * (d + 1)) -> Complex) (2 * sigma) ->
      z - SCV.realEmbed a ∈ D.complexTargetDomain := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖z - SCV.realEmbed a‖ <= ‖z‖ + ‖SCV.realEmbed a‖ :=
        norm_sub_le _ _
      _ = ‖z‖ + ‖a‖ := by rw [SCV.norm_realEmbed_eq]
      _ < 2 * sigma + 5 * sigma := add_lt_add hz ha
      _ < R := by linarith
  have hcov := D.complexTargetPairing_translate_eqOn
    (equation66_centeredFlatReducedSourceCLM
      (d := d) (k := k) (center := center) psi)
    a hsource (by rw [hsource_translate]; exact hsource_shift)
    (Metric.ball 0 (2 * sigma)) Metric.isOpen_ball
    (Metric.isConnected_ball (by positivity)) 0
    (Metric.mem_ball_self (by positivity)) hU_domain hU_shift
  change D.complexTargetPairing
      (equation66_centeredFlatReducedSourceCLM
        (d := d) (k := k) (center := center)
        (SCV.translateSchwartz a psi)) w =
    D.complexTargetPairing
      (equation66_centeredFlatReducedSourceCLM
        (d := d) (k := k) (center := center) psi)
      (w - SCV.realEmbed a)
  rw [← hsource_translate]
  exact hcov hw

/-- The mixed centered-source kernel has the local real-translation
covariance required by product descent. -/
theorem equation66_exists_locallyCovariantCenteredFlatPairingKernel
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (R sigma : Real) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 8)
    (hsigma_rho : sigma <= rho / 2)
    (hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain) :
    ∃ K : SchwartzMap
        ((Fin (k * (d + 1)) -> Complex) ×
          (FlatSource (d := d) (k := k))) Complex →L[Complex] Complex,
      (∀ psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex,
        DifferentiableOn Complex (D.equation66_centeredFlatPairing psi)
          (Metric.ball 0 R)) ∧
      (∀ (phi : SchwartzMap (Fin (k * (d + 1)) -> Complex) Complex)
          (psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex),
        SCV.SupportsInOpen
          (phi : (Fin (k * (d + 1)) -> Complex) -> Complex)
          (Metric.ball 0 (2 * sigma)) ->
        K (SCV.schwartzTensorProduct₂ phi psi) =
          ∫ z : Fin (k * (d + 1)) -> Complex,
            D.equation66_centeredFlatPairing psi z * phi z) ∧
      SCV.ProductKernelRealTranslationCovariantLocal K
        (Metric.ball 0 (2 * sigma)) (sigma / 2) := by
  obtain ⟨K, hKholo, hKrep⟩ :=
    D.equation66_exists_centeredFlatPairingKernel
      R sigma hsigma hsigma_R hball
  refine ⟨K, hKholo, hKrep, ?_⟩
  apply SCV.localHolomorphicFamily_pairingCLM_localCovariant
    (m := k * (d + 1)) (ρ := 5 * sigma)
    K D.equation66_centeredFlatPairing (2 * sigma) (sigma / 2)
  · linarith
  · intro phi psi hphi _hpsi
    exact hKrep phi psi hphi
  · intro psi _hpsi
    exact (hKholo psi).continuousOn.mono
      (Metric.ball_subset_ball (by linarith))
  · intro a psi ha hpsi hpsi_shift w hw _hw_shift
    exact D.equation66_centeredFlatPairing_translate_eq
      R sigma hsigma hsigma_R hsigma_rho hball
      a psi ha hpsi hpsi_shift w hw

/-- Local product descent and distributional Weyl regularity turn the
centered flat family into an honest holomorphic scalar density. -/
theorem equation66_exists_centeredFlatHolomorphicRepresentative
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (R sigma : Real) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 8)
    (hsigma_rho : sigma <= rho / 2)
    (hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain) :
    ∃ H : (Fin (k * (d + 1)) -> Complex) -> Complex,
      DifferentiableOn Complex H (Metric.ball 0 sigma) ∧
      ∀ (psi : SchwartzMap
          (FlatSource (d := d) (k := k)) Complex),
        SCV.KernelSupportWithin psi (sigma / 4) ->
        ∀ z ∈ Metric.ball
          (0 : Fin (k * (d + 1)) -> Complex) (sigma / 2),
          D.equation66_centeredFlatPairing psi z =
            ∫ t : FlatSource (d := d) (k := k),
              H (z + SCV.realEmbed t) * psi t := by
  obtain ⟨K, hKholo, hKrep, hKcov⟩ :=
    D.equation66_exists_locallyCovariantCenteredFlatPairingKernel
      R sigma hsigma hsigma_R hsigma_rho hball
  obtain ⟨eta, _heta_nonneg, _heta_real, heta_norm, heta_support⟩ :=
    SCV.exists_normalized_schwartz_bump_kernelSupportWithin
      (m := k * (d + 1)) (sigma / 4) (by positivity)
  have hm : 0 < k * (d + 1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.zero_lt_succ d)
  have hmargin_core :
      ∀ z ∈ Metric.ball
          (0 : Fin (k * (d + 1)) -> Complex) (sigma / 2),
        ∀ t : FlatSource (d := d) (k := k), ‖t‖ <= sigma / 4 ->
          z + SCV.realEmbed t ∈ Metric.ball
            (0 : Fin (k * (d + 1)) -> Complex) sigma := by
    intro z hz t ht
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖z + SCV.realEmbed t‖ <= ‖z‖ + ‖SCV.realEmbed t‖ :=
        norm_add_le _ _
      _ = ‖z‖ + ‖t‖ := by rw [SCV.norm_realEmbed_eq]
      _ < sigma / 2 + sigma / 4 := add_lt_add_of_lt_of_le hz ht
      _ < sigma := by linarith
  have hmargin_desc_cov :
      ∀ z ∈ Metric.ball
          (0 : Fin (k * (d + 1)) -> Complex) sigma,
        ∀ t : FlatSource (d := d) (k := k),
          ‖t‖ <= sigma / 4 + sigma / 4 ->
            z + SCV.realEmbed t ∈ Metric.ball
              (0 : Fin (k * (d + 1)) -> Complex) (2 * sigma) := by
    intro z hz t ht
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖z + SCV.realEmbed t‖ <= ‖z‖ + ‖SCV.realEmbed t‖ :=
        norm_add_le _ _
      _ = ‖z‖ + ‖t‖ := by rw [SCV.norm_realEmbed_eq]
      _ < sigma + (sigma / 4 + sigma / 4) :=
        add_lt_add_of_lt_of_le hz ht
      _ < 2 * sigma := by linarith
  have hKcov' : SCV.ProductKernelRealTranslationCovariantLocal K
      (Metric.ball
        (0 : Fin (k * (d + 1)) -> Complex) (2 * sigma))
      (sigma / 4 + sigma / 4) := by
    simpa only [show sigma / 4 + sigma / 4 = sigma / 2 by ring] using hKcov
  obtain ⟨H, hH_holo, _Hdist, _hH_rep, _hdesc, hpointwise⟩ :=
    SCV.localCovariantProductKernel_holomorphicRepresentative
      (m := k * (d + 1))
      (r := sigma / 4) (rη := sigma / 4)
      hm (by positivity) (by positivity)
      K D.equation66_centeredFlatPairing
      (Metric.ball 0 (sigma / 2))
      (Metric.ball 0 sigma)
      (Metric.ball 0 (2 * sigma))
      (Metric.ball 0 R)
      Metric.isOpen_ball Metric.isOpen_ball
      (Metric.ball_subset_ball (by linarith))
      (Metric.ball_subset_ball (by linarith))
      (Metric.ball_subset_ball (by linarith))
      hmargin_core eta heta_norm heta_support
      hmargin_desc_cov hKcov'
      (fun psi _hpsi => hKholo psi)
      (fun phi psi hphi _hpsi => hKrep phi psi hphi)
  exact ⟨H, hH_holo, hpointwise⟩

theorem equation66_recenteredFlatKernel_support
    (phi : SchwartzNPoint d k)
    (c : FlatSource (d := d) (k := k))
    (r : Real)
    (hphi : Function.support (flattenSchwartzNPoint (d := d) phi) ⊆
      Metric.closedBall c r) :
    SCV.KernelSupportWithin
      (SCV.translateSchwartz c (flattenSchwartzNPoint (d := d) phi)) r := by
  intro t ht
  rw [OSIIChapterV.tsupport_translateSchwartz_eq_preimage] at ht
  have hflat : tsupport
      ((flattenSchwartzNPoint (d := d) phi :
        SchwartzMap (FlatSource (d := d) (k := k)) Complex) :
        FlatSource (d := d) (k := k) -> Complex) ⊆
      Metric.closedBall c r :=
    closure_minimal hphi isClosed_closedBall
  have htball := hflat ht
  rw [Metric.mem_closedBall, dist_zero_right] at ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at htball
  simpa using htball

theorem equation66_centeredFlatReducedSource_recenter
    (phi : SchwartzNPoint d k) :
    equation66_centeredFlatReducedSourceCLM
        (d := d) (k := k) (center := center)
        (SCV.translateSchwartz
          (osiiStep4MultiGapXiHatCenter d k center)
          (flattenSchwartzNPoint (d := d) phi)) = phi := by
  ext x
  simp [equation66_centeredFlatReducedSourceCLM_apply,
    SCV.translateSchwartz_apply, unflattenSchwartzNPoint_apply,
    flattenSchwartzNPoint_apply]

/-- Absolute-coordinate form of the Weyl representative.  It gives exactly
the support-local imaginary-slice representation consumed by equation (6.6). -/
theorem equation66_exists_holomorphic_density_representsOnSupport
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (R sigma : Real) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 8)
    (hsigma_rho : sigma <= rho / 2)
    (hball : Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) R ⊆
        D.complexTargetDomain) :
    ∃ F : (Fin (k * (d + 1)) -> Complex) -> Complex,
      DifferentiableOn Complex F
        (Metric.ball
          (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) sigma) ∧
      D.imaginarySliceFamily.RepresentsOnSupport
        (Metric.closedBall
          (0 : FlatSource (d := d) (k := k)) (sigma / 4))
        (Metric.closedBall
          (osiiStep4MultiGapXiHatCenter d k center) (sigma / 4)) F := by
  obtain ⟨H, hH_holo, hpointwise⟩ :=
    D.equation66_exists_centeredFlatHolomorphicRepresentative
      R sigma hsigma hsigma_R hsigma_rho hball
  let c := osiiStep4MultiGapXiHatCenter d k center
  let F : (Fin (k * (d + 1)) -> Complex) -> Complex :=
    fun z => H (z - SCV.realEmbed c)
  have hF_holo : DifferentiableOn Complex F
      (Metric.ball (SCV.realEmbed c) sigma) := by
    exact hH_holo.comp
      (differentiable_id.sub
        (differentiable_const (SCV.realEmbed c))).differentiableOn
      (by
        intro z hz
        rw [Metric.mem_ball, dist_zero_right]
        simpa [Metric.mem_ball, dist_eq_norm] using hz)
  refine ⟨F, hF_holo, ?_⟩
  intro y hy phi hphi
  let flat : SchwartzMap (FlatSource (d := d) (k := k)) Complex :=
    flattenSchwartzNPoint (d := d) phi
  let psi : SchwartzMap (FlatSource (d := d) (k := k)) Complex :=
    SCV.translateSchwartz c flat
  have hpsi : SCV.KernelSupportWithin psi (sigma / 4) := by
    exact equation66_recenteredFlatKernel_support
      (d := d) (k := k) phi c (sigma / 4) hphi
  let zi : Fin (k * (d + 1)) -> Complex :=
    osiiStep4ComplexOfRealImag 0 y
  have hzi : zi ∈ Metric.ball
      (0 : Fin (k * (d + 1)) -> Complex) (sigma / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    have hy_norm : ‖y‖ <= sigma / 4 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    calc
      ‖zi‖ <= ‖(0 : FlatSource (d := d) (k := k))‖ + ‖y‖ :=
        osiiStep4ComplexOfRealImag_norm_le_add 0 y
      _ <= sigma / 4 := by simpa using hy_norm
      _ < sigma / 2 := by linarith
  have hp := hpointwise psi hpsi zi hzi
  have hcentered : equation66_centeredFlatReducedSourceCLM
      (d := d) (k := k) (center := center) psi = phi := by
    simpa [psi, c, flat] using
      (equation66_centeredFlatReducedSource_recenter
        (d := d) (k := k) (center := center) phi)
  have hp' : D.imaginarySliceFamily y phi =
      ∫ t : FlatSource (d := d) (k := k),
        H (zi + SCV.realEmbed t) * psi t := by
    simpa [equation66_centeredFlatPairing, hcentered, zi] using hp
  rw [hp']
  let g : FlatSource (d := d) (k := k) -> Complex := fun x =>
    F (osiiStep4ComplexOfRealImag x y) * flat x
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : MeasureTheory.Measure
      (FlatSource (d := d) (k := k)))) g c
  calc
    (∫ t : FlatSource (d := d) (k := k),
        H (zi + SCV.realEmbed t) * psi t) =
        ∫ t : FlatSource (d := d) (k := k), g (t + c) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      have harg : zi + SCV.realEmbed t =
          osiiStep4ComplexOfRealImag (t + c) y - SCV.realEmbed c := by
        ext i
        simp [zi, osiiStep4ComplexOfRealImag, SCV.realEmbed]
        ring
      rw [harg]
      simp [g, F, psi, flat, SCV.translateSchwartz_apply]
    _ = ∫ x : FlatSource (d := d) (k := k), g x := hshift
    _ = ∫ x : FlatSource (d := d) (k := k),
        F (osiiStep4ComplexOfRealImag x y) *
          flattenSchwartzNPoint (d := d) phi x := by rfl

/-- Stable output package for the local-Weyl equation-(6.6) construction.
Downstream growth arguments should consume this record rather than depend on
the internal product-kernel descent. -/
structure OSIIEquation66LocalWeylDensityData
    (D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc) where
  scale : Real
  scale_pos : 0 < scale
  scale_le : scale <= rho / 2
  scale_le_sixteen : scale <= 16
  density : (Fin (k * (d + 1)) -> Complex) -> Complex
  holomorphic : DifferentiableOn Complex density
    (Metric.ball
      (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) scale)
  represents : D.imaginarySliceFamily.RepresentsOnSupport
    (Metric.closedBall
      (0 : FlatSource (d := d) (k := k)) (scale / 4))
      (Metric.closedBall
      (osiiStep4MultiGapXiHatCenter d k center) (scale / 4)) density
  firstCarrierCoverage : forall y : FlatSource (d := d) (k := k),
    y ∈ Metric.closedBall 0 (scale / 4) ->
      osiiStep4MultiGapTargetLog d k Z.uniform.T center y ∈
        osiiAxisPairMultiGapLogDomain d k
  meanValue : density (osiiStep4ComplexOfRealImag
      (osiiStep4MultiGapXiHatCenter d k center) 0) =
    ∫ y' : FlatSource (d := d) (k := k),
      ∫ y : FlatSource (d := d) (k := k),
        osiiStep4DistributionalPartialConvolutionTransform
          D.imaginarySliceFamily scale_pos
            (osiiStep4MultiGapXiHatCenter d k center) y y'

/-- On the exact equation-(6.6) support box, the OS-built distributional
transform is the synchronized coherent pairing at the physical target log.
The first-carrier coverage stored in `A` is the only continuation provenance
used here. -/
theorem OSIIEquation66LocalWeylDensityData.distributionalPartialConvolutionTransform_eq_coherentPairing
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc}
    (A : OSIIEquation66LocalWeylDensityData D)
    (p : FlatSource (d := d) (k := k) ×
      FlatSource (d := d) (k := k))
    (hp : p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
      (d + 1) k A.scale) :
    osiiStep4DistributionalPartialConvolutionTransform
        D.imaginarySliceFamily A.scale_pos
          (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2 =
      Z.coherent.pairing OS lgc
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k A.scale_pos (osiiStep4MultiGapXiHatCenter d k center)
            p.1 p.2)
        (osiiStep4MultiGapTargetLog d k Z.uniform.T center p.1) := by
  let f := osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    d k A.scale_pos (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2
  let w := osiiStep4MultiGapTargetLog d k Z.uniform.T center p.1
  have hw : w ∈ osiiAxisPairMultiGapLogDomain d k :=
    A.firstCarrierCoverage p.1 hp.1
  change D.distribution w f = Z.coherent.pairing OS lgc f w
  rw [D.extendsFirst hw]
  exact Z.coherent.distribution_apply OS lgc w f

/-- Equation `(6.7)` for the local-Weyl density.  The analytic density and
mean-value construction are already internal to `A`; the only remaining
input is a uniform bound for the OS-built distributional transform on its
exact scaled support box. -/
theorem OSIIEquation66LocalWeylDensityData.norm_density_center_le_supportVolume_mul_bound
    {D : OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter) Z OS lgc}
    (A : OSIIEquation66LocalWeylDensityData D)
    (B : Real)
    (hbound : forall p,
      p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
          (d + 1) k A.scale ->
        ‖osiiStep4DistributionalPartialConvolutionTransform
            D.imaginarySliceFamily A.scale_pos
              (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2‖ <= B) :
    ‖A.density (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0)‖ <=
      B * ((A.scale / 2) ^ (k * (d + 1)) *
        (A.scale / 4) ^ (k * (d + 1))) := by
  let c : Fin (k * (d + 1)) -> Complex :=
    osiiStep4ComplexOfRealImag
      (osiiStep4MultiGapXiHatCenter d k center) 0
  have hradial : forall z,
      z ∈ osiiStep4FullBlockRadialClosedSupport
          (d + 1) k (3 * A.scale) ->
        c + z ∈ Metric.ball
          (SCV.realEmbed
            (osiiStep4MultiGapXiHatCenter d k center)) A.scale := by
    intro z hz
    have h := localBallDensityGeometry_radialSupport
      (d := d) (k := k) (center := center)
      (2 * A.scale) A.scale (mul_pos (by norm_num) A.scale_pos) A.scale_pos
      (by linarith) z hz
    simpa [c, osiiLocalBallDensityGeometry] using h
  apply osiiStep4FullBlockRadialG_norm_le_supportVolume_mul_sup_local
    (d + 1) k A.scale_pos A.density c
    (Metric.ball
      (SCV.realEmbed
        (osiiStep4MultiGapXiHatCenter d k center)) A.scale)
    A.holomorphic hradial B
  intro p hp
  have hy : p.1 ∈ Metric.closedBall
      (0 : FlatSource (d := d) (k := k)) (A.scale / 4) := hp.1
  have hsource : Function.support
      (flattenSchwartzNPoint (d := d)
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k A.scale_pos
            (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2)) ⊆
      Metric.closedBall
        (osiiStep4MultiGapXiHatCenter d k center) (A.scale / 4) :=
    flatten_osiiStep4CenteredPartialConvolutionKernelFullSource_support_subset
      d k A.scale_pos
        (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2
  have heq :=
    osiiStep4DistributionalPartialConvolutionTransform_eq_partialTransform_of_representsOnSupport
      D.imaginarySliceFamily A.density
      (Metric.closedBall
        (0 : FlatSource (d := d) (k := k)) (A.scale / 4))
      (Metric.closedBall
        (osiiStep4MultiGapXiHatCenter d k center) (A.scale / 4))
      A.represents A.scale_pos
      (osiiStep4MultiGapXiHatCenter d k center) p.1 p.2 hy hsource
  rw [← heq]
  exact hbound p hp

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
