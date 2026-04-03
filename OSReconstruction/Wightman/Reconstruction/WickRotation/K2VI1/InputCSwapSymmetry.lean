import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

noncomputable section

open Complex Topology MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The positive time-ordering sector in the Euclidean two-point domain. -/
def posTimeSector_local : Set (NPointDomain d 2) :=
  {x : NPointDomain d 2 | x 0 0 < x 1 0}

/-- The positive time-ordering sector is open. -/
theorem isOpen_posTimeSector_local :
    IsOpen (posTimeSector_local (d := d)) := by
  apply isOpen_lt
  · exact continuous_apply_apply 0 0
  · exact continuous_apply_apply 1 0

/-- The positive time-ordering sector is disjoint from the coincidence locus. -/
theorem posTimeSector_disjoint_coincidenceLocus_local :
    Disjoint (posTimeSector_local (d := d)) (CoincidenceLocus d 2) := by
  rw [Set.disjoint_left]
  intro x hx hxcoin
  simp only [posTimeSector_local, Set.mem_setOf_eq] at hx
  rcases hxcoin with ⟨i, j, hij, hijEq⟩
  have : x i 0 = x j 0 := congrFun hijEq 0
  fin_cases i <;> fin_cases j <;> simp_all

/-- Any Schwartz test supported in the positive time-ordering sector is already
zero-diagonal. -/
theorem vanishesOnCoincidence_of_tsupport_subset_posTimeSector_local
    (f : SchwartzNPoint d 2)
    (hf : tsupport (f : NPointDomain d 2 → ℂ) ⊆ posTimeSector_local (d := d)) :
    VanishesToInfiniteOrderOnCoincidence f := by
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint f
    (Set.disjoint_of_subset_left hf
      (posTimeSector_disjoint_coincidenceLocus_local (d := d)))

/-- Reindexing a two-point zero-diagonal Schwartz test by the transposition
still gives a zero-diagonal Schwartz test. -/
def zdsSwap_local (f : ZeroDiagonalSchwartz d 2) : ZeroDiagonalSchwartz d 2 :=
  ⟨reindexSchwartz (d := d) (Equiv.swap (0 : Fin 2) (1 : Fin 2)) f.1,
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      (d := d) f.2 (Equiv.swap (0 : Fin 2) (1 : Fin 2))⟩

@[simp] theorem zdsSwap_local_apply
    (f : ZeroDiagonalSchwartz d 2) (x : NPointDomain d 2) :
    (zdsSwap_local (d := d) f).1 x = f.1 (swapTwoPointAssembly_local (d := d) x) := by
  rfl

/-- `E3` specialized to the two-point swap. -/
theorem E3_twoPoint_swap_local
    (OS : OsterwalderSchraderAxioms d)
    (f : ZeroDiagonalSchwartz d 2) :
    OS.S 2 f = OS.S 2 (zdsSwap_local (d := d) f) := by
  exact
    OS.E3_symmetric (n := 2) (σ := Equiv.swap (0 : Fin 2) (1 : Fin 2)) f
      (zdsSwap_local (d := d) f)
      (fun x => by rfl)

/-- The negative time-ordering sector in the Euclidean two-point domain. -/
def negTimeSector_local : Set (NPointDomain d 2) :=
  {x : NPointDomain d 2 | x 1 0 < x 0 0}

private def twoPointSwapMeasurableEquiv_local :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin 2 => SpacetimeDim d)
    (Equiv.swap (0 : Fin 2) (1 : Fin 2))

private theorem twoPointSwap_measurePreserving_local :
    MeasureTheory.MeasurePreserving
      (twoPointSwapMeasurableEquiv_local (d := d)) volume volume := by
  simpa [twoPointSwapMeasurableEquiv_local] using
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin 2 => SpacetimeDim d)
      (Equiv.swap (0 : Fin 2) (1 : Fin 2)))

private theorem twoPointSwapMeasurableEquiv_eq_local :
    ((twoPointSwapMeasurableEquiv_local (d := d)) : NPointDomain d 2 → NPointDomain d 2) =
      swapTwoPointAssembly_local (d := d) := by
  funext x
  let x' :
      (a : Fin 2) →
        (fun _ : Fin 2 => SpacetimeDim d) ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) a) := x
  funext i
  fin_cases i
  · simpa [twoPointSwapMeasurableEquiv_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (1 : Fin 2)))
  · simpa [twoPointSwapMeasurableEquiv_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (0 : Fin 2)))

private theorem continuous_swapTwoPointAssembly_local :
    Continuous (swapTwoPointAssembly_local (d := d)) := by
  refine continuous_pi ?_
  intro i
  fin_cases i
  · simpa [swapTwoPointAssembly_local] using
      (continuous_apply (1 : Fin 2) : Continuous fun x : NPointDomain d 2 => x 1)
  · simpa [swapTwoPointAssembly_local] using
      (continuous_apply (0 : Fin 2) : Continuous fun x : NPointDomain d 2 => x 0)

/-- The common one-variable sectorwise kernel is even under `ξ ↦ -ξ`. -/
theorem commonDifferenceKernel_real_neg_invariant_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (ξ : SpacetimeDim d) :
    commonDifferenceKernel_real_local (d := d) G (-ξ) =
      commonDifferenceKernel_real_local (d := d) G ξ := by
  by_cases hpos : 0 < ξ 0
  · have hneg' : (-ξ) 0 < 0 := by simpa using hpos
    have hnot_pos' : ¬ 0 < (-ξ) 0 := by linarith
    have hnot_neg : ¬ ξ 0 < 0 := by linarith
    simp [commonDifferenceKernel_real_local, hpos, hneg', hnot_pos', hnot_neg, neg_neg]
  · by_cases hneg : ξ 0 < 0
    · have hpos' : 0 < (-ξ) 0 := by simpa using hneg
      have hnot_neg' : ¬ (-ξ) 0 < 0 := by linarith
      have hnot_pos : ¬ 0 < ξ 0 := hpos
      simp [commonDifferenceKernel_real_local, hnot_pos, hneg, hpos', hnot_neg', neg_neg]
    · have hzero : ξ 0 = 0 := by linarith
      have hzero' : (-ξ) 0 = 0 := by simp [hzero]
      have hnot_pos : ¬ 0 < ξ 0 := hpos
      simp [commonDifferenceKernel_real_local, hnot_pos, hneg, hzero, hzero']

/-- The common sectorwise real Euclidean kernel is pointwise invariant under
swapping the two Euclidean arguments. -/
theorem commonK2TimeParametricKernel_real_swap_invariant_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (x : NPointDomain d 2) :
    commonK2TimeParametricKernel_real_local (d := d) G
        (swapTwoPointAssembly_local (d := d) x) =
      commonK2TimeParametricKernel_real_local (d := d) G x := by
  calc
    commonK2TimeParametricKernel_real_local (d := d) G
        (swapTwoPointAssembly_local (d := d) x)
      =
      commonDifferenceKernel_real_local (d := d) G
        ((swapTwoPointAssembly_local (d := d) x) 1 -
          (swapTwoPointAssembly_local (d := d) x) 0) := by
            simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel]
    _ =
      commonDifferenceKernel_real_local (d := d) G (-(x 1 - x 0)) := by
            simp [swapTwoPointAssembly_local, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ =
      commonDifferenceKernel_real_local (d := d) G (x 1 - x 0) := by
            rw [commonDifferenceKernel_real_neg_invariant_local]
    _ =
      commonK2TimeParametricKernel_real_local (d := d) G x := by
            simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel]

private theorem integral_commonK_mul_zdsSwap_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (f : ZeroDiagonalSchwartz d 2) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x) =
      ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          ((zdsSwap_local (d := d) f).1 x) := by
  let e := twoPointSwapMeasurableEquiv_local (d := d)
  have he := twoPointSwap_measurePreserving_local (d := d)
  have heq := twoPointSwapMeasurableEquiv_eq_local (d := d)
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x)
      =
      ∫ y : NPointDomain d 2,
        (fun x : NPointDomain d 2 =>
          commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x)) (e y) := by
            symm
            exact he.integral_comp' (f := e)
              (g := fun x : NPointDomain d 2 =>
                commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x))
    _ =
      ∫ y : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G y *
          ((zdsSwap_local (d := d) f).1 y) := by
            refine integral_congr_ae ?_
            filter_upwards with y
            rw [heq]
            rw [commonK2TimeParametricKernel_real_swap_invariant_local]
            simp [zdsSwap_local_apply]

/-- On zero-diagonal Schwartz tests whose support lies entirely in the positive
time-ordering sector, the sectorwise common kernel already reproduces
`OS.S 2`. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_of_tsupport_subset_posTimeSector_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
          v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (f : ZeroDiagonalSchwartz d 2)
    (hf : tsupport (f.1 : NPointDomain d 2 → ℂ) ⊆ posTimeSector_local (d := d)) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x) =
      OS.S 2 f := by
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x)
      =
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          by_cases hfx : f.1 x = 0
          · simp [hfx]
          · have hxmem : x ∈ tsupport (f.1 : NPointDomain d 2 → ℂ) :=
              subset_tsupport _ (by simpa [Function.mem_support] using hfx)
            have hx : x ∈ posTimeSector_local (d := d) := hf hxmem
            rw [commonK2TimeParametricKernel_real_eq_of_pos_local (d := d) G hG_diff x hx]
    _ = OS.S 2 f := by
          symm
          exact hG_euclid f

/-- On zero-diagonal Schwartz tests whose support lies entirely in the negative
time-ordering sector, the sectorwise common kernel also reproduces `OS.S 2`,
by swapping into the positive sector and using `E3`. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_of_tsupport_subset_negTimeSector_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
          v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (f : ZeroDiagonalSchwartz d 2)
    (hf : tsupport (f.1 : NPointDomain d 2 → ℂ) ⊆ negTimeSector_local (d := d)) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x) =
      OS.S 2 f := by
  have hswap_pos :
      tsupport (((zdsSwap_local (d := d) f).1) : NPointDomain d 2 → ℂ) ⊆
        posTimeSector_local (d := d) := by
    intro x hx
    have hmem_swap :
        swapTwoPointAssembly_local (d := d) x ∈ tsupport (f.1 : NPointDomain d 2 → ℂ) := by
      exact tsupport_comp_subset_preimage (f.1 : NPointDomain d 2 → ℂ)
        (f := swapTwoPointAssembly_local (d := d))
        (continuous_swapTwoPointAssembly_local (d := d)) hx
    have hneg : swapTwoPointAssembly_local (d := d) x ∈ negTimeSector_local (d := d) :=
      hf hmem_swap
    simpa [negTimeSector_local, posTimeSector_local, swapTwoPointAssembly_local] using hneg
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x)
      =
      ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          ((zdsSwap_local (d := d) f).1 x) := by
            exact integral_commonK_mul_zdsSwap_local (d := d) G f
    _ = OS.S 2 (zdsSwap_local (d := d) f) := by
          exact
            commonK2TimeParametricKernel_real_eq_schwinger_of_tsupport_subset_posTimeSector_local
              (d := d) OS G hG_euclid hG_diff (zdsSwap_local (d := d) f) hswap_pos
    _ = OS.S 2 f := by
          symm
          exact E3_twoPoint_swap_local (d := d) OS f

/-- Fixed imaginary-time shift used on the positive sector to move both raw
Euclidean configurations into `ACR(1)`. -/
private def posTimeSectorImagShift_local
    (x : NPointDomain d 2) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * ((1 - x 0 0 : ℝ) : ℂ) else 0

/-- Shifted raw Euclidean section for the common witness on the positive
time-ordering sector. -/
private def shiftedPosTimeSection_local
    (x : NPointDomain d 2) : Fin 2 → Fin (d + 1) → ℂ :=
  fun i => wickRotatePoint (x i) + posTimeSectorImagShift_local (d := d) x

private theorem continuous_wickRotatePoint_local :
    Continuous (wickRotatePoint (d := d)) := by
  apply continuous_pi
  intro μ
  simp only [wickRotatePoint]
  split_ifs
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact Complex.continuous_ofReal.comp (continuous_apply μ)

private theorem continuous_posTimeSectorImagShift_local :
    Continuous (posTimeSectorImagShift_local (d := d)) := by
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord :
        Continuous (fun a : NPointDomain d 2 => (1 - a 0 0 : ℝ)) :=
      continuous_const.sub (continuous_apply_apply 0 0)
    change Continuous (fun a : NPointDomain d 2 => Complex.I * (((1 - a 0 0 : ℝ) : ℂ)))
    exact ((continuous_const : Continuous fun _ : NPointDomain d 2 => Complex.I).mul
      (Complex.continuous_ofReal.comp hcoord))
  ·
    simpa [posTimeSectorImagShift_local, hμ] using
      (continuous_const : Continuous fun _ : NPointDomain d 2 => (0 : ℂ))

private theorem continuous_shiftedPosTimeSection_local :
    Continuous (shiftedPosTimeSection_local (d := d)) := by
  apply continuous_pi
  intro i
  exact (continuous_wickRotatePoint_local (d := d)).comp (continuous_apply i) |>.add
    (continuous_posTimeSectorImagShift_local (d := d))

private theorem shiftedPosTimeSection_mem_acrOne_local
    (x : NPointDomain d 2)
    (hx : x ∈ posTimeSector_local (d := d)) :
    shiftedPosTimeSection_local (d := d) x ∈ AnalyticContinuationRegion d 2 1 := by
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq] at *
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  subst hμ0
  fin_cases i
  · simp [shiftedPosTimeSection_local, posTimeSectorImagShift_local, wickRotatePoint]
  · simp [shiftedPosTimeSection_local, posTimeSectorImagShift_local, wickRotatePoint]
    exact by
      have hx' : x 0 0 < x 1 0 := hx
      linarith

private theorem norm_wickRotatePoint_le_local
    (ξ : SpacetimeDim d) :
    ‖wickRotatePoint ξ‖ ≤ ‖ξ‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg ξ)]
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [wickRotatePoint, Complex.norm_mul, Complex.norm_I, one_mul, Real.norm_eq_abs]
    exact norm_le_pi_norm ξ 0
  · simp [wickRotatePoint, hμ, Real.norm_eq_abs]
    exact norm_le_pi_norm ξ μ

private theorem norm_posTimeSectorImagShift_le_local
    (x : NPointDomain d 2) :
    ‖posTimeSectorImagShift_local (d := d) x‖ ≤ 1 + ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖)]
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    change ‖Complex.I * (((1 - x 0 0 : ℝ) : ℂ))‖ ≤ 1 + ‖x‖
    rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    have hcoord0 : ‖x 0 0‖ ≤ ‖x 0‖ := by
      exact norm_le_pi_norm (x 0) 0
    have hcoord : ‖x 0 0‖ ≤ ‖x‖ := hcoord0.trans (norm_le_pi_norm x 0)
    have habs : |x 0 0| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using hcoord
    calc
      |1 - x 0 0| = |(1 : ℝ) + (-x 0 0)| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-x 0 0| := abs_add_le _ _
      _ = 1 + |x 0 0| := by simp
      _ ≤ 1 + ‖x‖ := by nlinarith
  · have : 0 ≤ (1 + ‖x‖ : ℝ) := by positivity
    simpa [posTimeSectorImagShift_local, hμ]

private theorem norm_shiftedPosTimeSection_le_local
    (x : NPointDomain d 2) :
    ‖shiftedPosTimeSection_local (d := d) x‖ ≤ 2 * (1 + ‖x‖) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + ‖x‖))]
  intro i
  have hshift : ‖posTimeSectorImagShift_local (d := d) x‖ ≤ 1 + ‖x‖ :=
    norm_posTimeSectorImagShift_le_local (d := d) x
  calc
    ‖shiftedPosTimeSection_local (d := d) x i‖
        = ‖wickRotatePoint (x i) + posTimeSectorImagShift_local (d := d) x‖ := by
            simp [shiftedPosTimeSection_local]
    _ ≤ ‖wickRotatePoint (x i)‖ + ‖posTimeSectorImagShift_local (d := d) x‖ := norm_add_le _ _
    _ ≤ ‖x i‖ + ‖posTimeSectorImagShift_local (d := d) x‖ := by
          gcongr
          exact norm_wickRotatePoint_le_local (d := d) (x i)
    _ ≤ ‖x i‖ + (1 + ‖x‖) := by gcongr
    _ ≤ ‖x‖ + (1 + ‖x‖) := by
          gcongr
          exact norm_le_pi_norm x i
    _ = 2 * (1 + ‖x‖) - 1 := by ring
    _ ≤ 2 * (1 + ‖x‖) := by nlinarith [norm_nonneg x]

/-- Production package for the raw common Euclidean section on the positive
time-ordering sector.

This is the exact positive-sector support needed by the E3 route: after
choosing the upstream translation-invariant `ACR(1)` witness, the raw Euclidean
section `x ↦ k2TimeParametricKernel G x` is continuous on the open sector
`{x | x₀⁰ < x₁⁰}` and satisfies a polynomial bound there. The swapped sector is
honestly still separate data and should not be smuggled into this package. -/
theorem schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectorPackage_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x * (f.1 x)) ∧
      ContinuousOn (fun x : NPointDomain d 2 =>
        k2TimeParametricKernel (d := d) G x) (posTimeSector_local (d := d)) ∧
      ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
        ∀ x : NPointDomain d 2, x ∈ posTimeSector_local (d := d) →
          ‖k2TimeParametricKernel (d := d) G x‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  let hS_pack :=
    _root_.schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
      (d := d) OS lgc 2
  let S₁ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := Classical.choose hS_pack
  have hS₁_hol :
      DifferentiableOn ℂ S₁ (AnalyticContinuationRegion d 2 1) :=
    (Classical.choose_spec hS_pack).1
  have hS₁_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          S₁ (fun j => wickRotatePoint (x j)) * (f.1 x) :=
    (Classical.choose_spec hS_pack).2.1
  have _hS₁_perm :
      ∀ (σ : Equiv.Perm (Fin 2)) (z : Fin 2 → Fin (d + 1) → ℂ),
        S₁ (fun j => z (σ j)) = S₁ z :=
    (Classical.choose_spec hS_pack).2.2.1
  have hS₁_trans :
      ∀ (z : Fin 2 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S₁ (fun j => z j + a) = S₁ z :=
    (Classical.choose_spec hS_pack).2.2.2.1
  have _hS₁_negCanonical :
      ∀ (x : NPointDomain d 2) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S₁ (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S₁ (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I) :=
    (Classical.choose_spec hS_pack).2.2.2.2.1
  obtain ⟨C₁, N, hC₁, hS₁_growth⟩ :=
    (Classical.choose_spec hS_pack).2.2.2.2.2
  let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat 2 d u)
  have hG_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x * (f.1 x) := by
    intro f
    simpa [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat] using hS₁_euclid f
  have hS₁_cont : ContinuousOn S₁ (AnalyticContinuationRegion d 2 1) :=
    hS₁_hol.continuousOn
  have hraw_eq :
      (fun x : NPointDomain d 2 => k2TimeParametricKernel (d := d) G x) =
        (fun x : NPointDomain d 2 => S₁ (shiftedPosTimeSection_local (d := d) x)) := by
    funext x
    calc
      k2TimeParametricKernel (d := d) G x
          = S₁ (fun i => wickRotatePoint (x i)) := by
              simp [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat]
      _ = S₁ (shiftedPosTimeSection_local (d := d) x) := by
            symm
            simpa [shiftedPosTimeSection_local, posTimeSectorImagShift_local] using
              hS₁_trans (fun i => wickRotatePoint (x i))
                (posTimeSectorImagShift_local (d := d) x)
  have hraw_cont :
      ContinuousOn (fun x : NPointDomain d 2 => k2TimeParametricKernel (d := d) G x)
        (posTimeSector_local (d := d)) := by
    rw [hraw_eq]
    refine hS₁_cont.comp (continuous_shiftedPosTimeSection_local (d := d)).continuousOn ?_
    intro x hx
    exact shiftedPosTimeSection_mem_acrOne_local (d := d) x hx
  refine ⟨G, hG_euclid, hraw_cont, C₁ * (5 : ℝ) ^ N, N, ?_, ?_⟩
  · positivity
  · intro x hx
    have hmem := shiftedPosTimeSection_mem_acrOne_local (d := d) x hx
    have hnorm := norm_shiftedPosTimeSection_le_local (d := d) x
    have hbound0 : ‖S₁ (shiftedPosTimeSection_local (d := d) x)‖ ≤
        C₁ * (1 + ‖shiftedPosTimeSection_local (d := d) x‖) ^ N :=
      hS₁_growth _ hmem
    rw [show k2TimeParametricKernel (d := d) G x =
        S₁ (shiftedPosTimeSection_local (d := d) x) from by
          simpa using congrFun hraw_eq x]
    calc
      ‖S₁ (shiftedPosTimeSection_local (d := d) x)‖
          ≤ C₁ * (1 + ‖shiftedPosTimeSection_local (d := d) x‖) ^ N := hbound0
      _ ≤ C₁ * (1 + 2 * (1 + ‖x‖)) ^ N := by
            gcongr
      _ = C₁ * (3 + 2 * ‖x‖) ^ N := by ring
      _ ≤ C₁ * (5 * (1 + ‖x‖)) ^ N := by
            apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
            gcongr
            nlinarith [norm_nonneg x]
      _ = (C₁ * (5 : ℝ) ^ N) * (1 + ‖x‖) ^ N := by
            rw [mul_assoc, mul_pow]

end OSReconstruction
