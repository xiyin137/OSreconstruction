import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialRealEdge

/-!
# OS II Chapter VI: production radial operator-norm Gevrey bounds

Cauchy power-series coefficients control the entire continuous multilinear
operator, not only coordinate derivatives. The exact real-edge restriction
then gives the operator-norm bounds required by production Schwartz seminorms.
-/

noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction

set_option maxHeartbeats 800000 in
theorem osiiProductionCauchyPowerSeries_norm_le_of_coefficient_bound
    {m : Nat}
    (f : (Fin (m + 1) → Complex) → Complex)
    (z : Fin (m + 1) → Complex) (R : Real)
    (n : Nat) (M : Real)
    (hcoeff : ∀ alpha : Fin (m + 1) → Nat,
      (∑ i, alpha i) = n →
        ‖SCV.cauchyCoeffPolydisc f z (fun _ => R) alpha‖ ≤ M) :
    ‖SCV.cauchyPowerSeriesPolydisc f z (fun _ => R) n‖ ≤
      ((m + 1 : Nat) : Real) ^ n * M := by
  let F : (Fin n → Fin (m + 1)) →
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => Fin (m + 1) → Complex) Complex :=
    fun sigma =>
      (ContinuousMultilinearMap.mkPiRing Complex (Fin n)
        ((↑(∏ i, (SCV.multiIdx sigma i).factorial) /
            ↑n.factorial : Complex) •
          SCV.cauchyCoeffPolydisc f z (fun _ => R)
            (SCV.multiIdx sigma))).compContinuousLinearMap
              (fun j => ContinuousLinearMap.proj (sigma j))
  have hseries :
      SCV.cauchyPowerSeriesPolydisc f z (fun _ => R) n =
        ∑ sigma, F sigma := rfl
  have hterm : ∀ sigma : Fin n → Fin (m + 1), ‖F sigma‖ ≤ M := by
    intro sigma
    have hfactorial :
        (∏ i : Fin (m + 1), (SCV.multiIdx sigma i).factorial) ≤
          n.factorial := by
      apply Nat.le_of_dvd (Nat.factorial_pos n)
      simpa [SCV.multiIdx_sum sigma] using
        (Nat.prod_factorial_dvd_factorial_sum
          (Finset.univ : Finset (Fin (m + 1)))
          (SCV.multiIdx sigma))
    calc
      ‖F sigma‖ ≤
          ‖ContinuousMultilinearMap.mkPiRing Complex (Fin n)
            ((↑(∏ i, (SCV.multiIdx sigma i).factorial) /
                ↑n.factorial : Complex) •
              SCV.cauchyCoeffPolydisc f z (fun _ => R)
                (SCV.multiIdx sigma))‖ *
            ∏ j, ‖(ContinuousLinearMap.proj (sigma j) :
              (Fin (m + 1) → Complex) →L[Complex] Complex)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖ContinuousMultilinearMap.mkPiRing Complex (Fin n)
            ((↑(∏ i, (SCV.multiIdx sigma i).factorial) /
                ↑n.factorial : Complex) •
              SCV.cauchyCoeffPolydisc f z (fun _ => R)
                (SCV.multiIdx sigma))‖ * 1 := by
        gcongr
        apply Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => ?_)
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro v
        simpa using norm_le_pi_norm v (sigma j)
      _ = ‖((↑(∏ i, (SCV.multiIdx sigma i).factorial) /
                ↑n.factorial : Complex) •
              SCV.cauchyCoeffPolydisc f z (fun _ => R)
                (SCV.multiIdx sigma))‖ := by
        rw [ContinuousMultilinearMap.norm_mkPiRing, mul_one]
      _ ≤ 1 * ‖SCV.cauchyCoeffPolydisc f z (fun _ => R)
            (SCV.multiIdx sigma)‖ := by
        rw [norm_smul]
        gcongr
        rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
        exact div_le_one_of_le₀ (Nat.cast_le.mpr hfactorial)
          (Nat.cast_nonneg _)
      _ ≤ M := by
        rw [one_mul]
        exact hcoeff (SCV.multiIdx sigma) (SCV.multiIdx_sum sigma)
  rw [hseries]
  calc
    ‖∑ sigma : Fin n → Fin (m + 1), F sigma‖ ≤
        ∑ _sigma : Fin n → Fin (m + 1), M :=
      norm_sum_le_of_le _ (fun sigma _ => hterm sigma)
    _ = ((m + 1 : Nat) : Real) ^ n * M := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rfl

theorem osiiProduction_iteratedFDeriv_norm_le_powerSeries
    {m : Nat}
    {f : (Fin (m + 1) → Complex) → Complex}
    {z : Fin (m + 1) → Complex}
    {p : FormalMultilinearSeries Complex (Fin (m + 1) → Complex) Complex}
    (hp : HasFPowerSeriesAt f p z) (n : Nat) :
    ‖iteratedFDeriv Complex n f z‖ ≤
      (n.factorial : Real) * ‖p n‖ := by
  obtain ⟨radius, hradius⟩ := hp
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [hradius.iteratedFDeriv_eq_sum_of_completeSpace]
  calc
    ‖∑ sigma : Equiv.Perm (Fin n),
        p n (fun i => v (sigma i))‖ ≤
      ∑ sigma : Equiv.Perm (Fin n),
        ‖p n‖ * ∏ i, ‖v (sigma i)‖ :=
        norm_sum_le_of_le _ (fun sigma _ =>
          ContinuousMultilinearMap.le_opNorm _ _)
    _ = (n.factorial : Real) * ‖p n‖ * ∏ i, ‖v i‖ := by
      have hperm :
          (∑ sigma : Equiv.Perm (Fin n),
            ‖p n‖ * ∏ i, ‖v (sigma i)‖) =
          ∑ _sigma : Equiv.Perm (Fin n),
            ‖p n‖ * ∏ i, ‖v i‖ := by
        apply Finset.sum_congr rfl
        intro sigma _
        congr 1
        exact Equiv.prod_comp sigma (fun i => ‖v i‖)
      rw [hperm]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem osiiProductionComplexRadialBump_iteratedFDeriv_gevrey_bound
    {m : Nat}
    (x : EuclideanSpace Real (Fin (m + 1)))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (n : Nat) :
    ‖iteratedFDeriv Complex n
        (fun z => osiiProductionComplexRadialBump z -
          osiiProductionRadialAnnulusBaseline x)
        (fun i => (x i : Complex))‖ ≤
      Real.exp 6 *
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 := by
  let delta := osiiProductionRadialAnnulusMargin x
  let center : Fin (m + 1) → Complex := fun i => (x i : Complex)
  let R : Real := delta / (65536 * ((m + 1 : Nat) : Real))
  let B : Real := delta / (32768 * ((m + 1 : Nat) : Real))
  let U : Set (Fin (m + 1) → Complex) :=
    SCV.Polydisc center (fun _ => B)
  let f : (Fin (m + 1) → Complex) → Complex :=
    fun z => osiiProductionComplexRadialBump z -
      osiiProductionRadialAnnulusBaseline x
  let M : Real :=
    Real.exp 6 * (98304 * ((m + 1 : Nat) : Real)) ^ n *
      (n.factorial : Real)
  have hm : 0 < m + 1 := by omega
  have hmreal : (0 : Real) < (m + 1 : Nat) := by exact_mod_cast hm
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRB : R < B := by
    dsimp [R, B]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_pos hdelta hmreal]
  have hU : IsOpen U := SCV.polydisc_isOpen
  have hclosed :
      SCV.closedPolydisc center (fun _ => R) ⊆ U := by
    intro z hz i
    exact (SCV.mem_closedPolydisc_iff.mp hz i).trans_lt hRB
  have hdiff : DifferentiableOn Complex f U := by
    intro z hz
    have hcoord :
        ∀ i, ‖z i - (x i : Complex)‖ ≤
          osiiProductionRadialAnnulusMargin x /
            (32768 * ((m + 1 : Nat) : Real)) := by
      intro i
      have hi := SCV.mem_polydisc_iff.mp hz i
      simpa [center, B, delta, dist_eq_norm] using hi.le
    exact
      ((osiiProductionComplexRadialBump_differentiableAt
        hm x hx_lower hx_upper z hcoord).sub
          (differentiableAt_const
            (osiiProductionRadialAnnulusBaseline x))).differentiableWithinAt
  have hseries :=
    SCV.hasFPowerSeriesAt_cauchyPowerSeriesPolydisc_of_differentiableOn
      hR hU hclosed hdiff
  have hcoeff :
      ∀ alpha : Fin (m + 1) → Nat,
        (∑ i, alpha i) = n →
          ‖SCV.cauchyCoeffPolydisc f center (fun _ => R) alpha‖ ≤ M := by
    intro alpha halpha
    have hbound :=
      osiiProductionComplexRadialBump_cauchyCoeff_gevrey_bound
        hm x hx_lower hx_upper alpha
    simpa [f, center, R, delta, M, halpha] using hbound
  have hpbound :=
    osiiProductionCauchyPowerSeries_norm_le_of_coefficient_bound
      f center R n M hcoeff
  have hderiv := osiiProduction_iteratedFDeriv_norm_le_powerSeries
    hseries n
  have hscale :
      ((m + 1 : Nat) : Real) ^ n *
          (98304 * ((m + 1 : Nat) : Real)) ^ n =
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  change ‖iteratedFDeriv Complex n f center‖ ≤ _
  calc
    ‖iteratedFDeriv Complex n f center‖ ≤
        (n.factorial : Real) *
          ‖SCV.cauchyPowerSeriesPolydisc f center (fun _ => R) n‖ :=
      hderiv
    _ ≤ (n.factorial : Real) *
          (((m + 1 : Nat) : Real) ^ n * M) := by
      gcongr
    _ = Real.exp 6 *
          (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
            (n.factorial : Real) ^ 2 := by
      dsimp [M]
      rw [← hscale]
      ring

theorem osiiProductionRealRadialBump_iteratedFDeriv_gevrey_bound
    {m : Nat}
    (x : EuclideanSpace Real (Fin (m + 1)))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiProductionRealRadialSlice x) 0‖ ≤
      Real.exp 6 *
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 := by
  let center : Fin (m + 1) → Complex := fun i => (x i : Complex)
  let delta := osiiProductionRadialAnnulusMargin x
  let B : Real := delta / (32768 * ((m + 1 : Nat) : Real))
  let U : Set (Fin (m + 1) → Complex) :=
    SCV.Polydisc center (fun _ => B)
  let f : (Fin (m + 1) → Complex) → Complex :=
    fun z => osiiProductionComplexRadialBump z -
      osiiProductionRadialAnnulusBaseline x
  let bound : Real :=
    Real.exp 6 *
      (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2
  have hm : 0 < m + 1 := by omega
  have hmreal : (0 : Real) < (m + 1 : Nat) := by exact_mod_cast hm
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hU : IsOpen U := SCV.polydisc_isOpen
  have hcenter : center ∈ U := SCV.center_mem_polydisc (fun _ => hB)
  have hf : DifferentiableOn Complex f U := by
    intro z hz
    have hcoord :
        ∀ i, ‖z i - (x i : Complex)‖ ≤
          osiiProductionRadialAnnulusMargin x /
            (32768 * ((m + 1 : Nat) : Real)) := by
      intro i
      have hi := SCV.mem_polydisc_iff.mp hz i
      simpa [center, B, delta, dist_eq_norm] using hi.le
    exact
      ((osiiProductionComplexRadialBump_differentiableAt
        hm x hx_lower hx_upper z hcoord).sub
          (differentiableAt_const
            (osiiProductionRadialAnnulusBaseline x))).differentiableWithinAt
  have hreal :
      (fun v : Fin (m + 1) → Real =>
        OSIIChapterV.realAffineSlice f center v) =ᶠ[𝓝 0]
          osiiProductionRealRadialSlice x := by
    simpa [f, center] using
      osiiProductionComplexRadialBump_realEdge_eventuallyEq
        x hx_lower hx_upper
  have hcomplex : ‖iteratedFDeriv Complex n f center‖ ≤ bound := by
    simpa [f, center, bound] using
      osiiProductionComplexRadialBump_iteratedFDeriv_gevrey_bound
        x hx_lower hx_upper n
  change ‖iteratedFDeriv Real n (osiiProductionRealRadialSlice x) 0‖ ≤ bound
  apply ContinuousMultilinearMap.opNorm_le_bound (by
    dsimp [bound]
    positivity)
  intro directions
  have htransfer :=
    OSIIChapterV.iteratedFDeriv_eq_realEdge_iteratedFDeriv
      (inferInstance : IsScalarTower Real Complex Complex)
      (inferInstance : IsScalarTower Real Complex (Fin (m + 1) → Complex))
      hU hcenter hf hreal directions
  rw [← htransfer]
  calc
    ‖iteratedFDeriv Complex n f center
        (fun j i => (directions j i : Complex))‖ ≤
      ‖iteratedFDeriv Complex n f center‖ *
        ∏ j, ‖fun i => (directions j i : Complex)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ bound * ∏ j, ‖directions j‖ := by
      apply mul_le_mul hcomplex
      · apply Finset.prod_le_prod
        · intro j _
          exact norm_nonneg _
        · intro j _
          apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
          intro i
          simpa using norm_le_pi_norm (directions j) i
      · positivity
      · dsimp [bound]
        positivity

end OSReconstruction
