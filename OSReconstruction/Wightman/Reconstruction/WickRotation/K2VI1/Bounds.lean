import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {d : ℕ} [NeZero d]

/-- Nonnegative real-valued normalized approximate-identity probes have unit
`L¹` norm. This is the scalar input behind the VI.1 regularization bounds. -/
theorem approxIdentity_L1_norm_eq_one_vi1Bounds_local
    (φ : SchwartzSpacetime d)
    (hφ_nonneg : ∀ x, 0 ≤ (φ x).re)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1) :
    ∫ x : SpacetimeDim d, ‖φ x‖ = 1 := by
  have hnorm_re : ∀ x : SpacetimeDim d, ‖φ x‖ = (φ x).re := by
    intro x
    rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg x, (hφ_real x).symm⟩]
  simp_rw [hnorm_re]
  rw [show (fun x => (φ x).re) = (fun x => RCLike.re (φ x)) from rfl]
  rw [integral_re (SchwartzMap.integrable φ)]
  have := congrArg Complex.re hφ_int
  simpa using this

/-- Reflection preserves the unit `L¹` norm of a real nonnegative normalized
probe. -/
theorem reflected_approxIdentity_L1_norm_eq_one_vi1Bounds_local
    (φ : SchwartzSpacetime d)
    (hφ_nonneg : ∀ x, 0 ≤ (φ x).re)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1) :
    ∫ x : SpacetimeDim d, ‖reflectedSchwartzSpacetime φ x‖ = 1 := by
  have hnonneg_refl : ∀ x : SpacetimeDim d, 0 ≤ (reflectedSchwartzSpacetime φ x).re := by
    intro x
    change 0 ≤ (φ (fun i => if i = 0 then -x 0 else x i)).re
    simpa [timeReflection] using hφ_nonneg (timeReflection d x)
  have hreal_refl : ∀ x : SpacetimeDim d, (reflectedSchwartzSpacetime φ x).im = 0 := by
    intro x
    change (φ (fun i => if i = 0 then -x 0 else x i)).im = 0
    simpa [timeReflection] using hφ_real (timeReflection d x)
  have h_int_refl :
      ∫ x : SpacetimeDim d, reflectedSchwartzSpacetime φ x = 1 := by
    rw [reflectedSchwartzSpacetime_integral_eq_local]
    exact hφ_int
  exact approxIdentity_L1_norm_eq_one_vi1Bounds_local
    (d := d) (reflectedSchwartzSpacetime φ) hnonneg_refl hreal_refl h_int_refl

/-- A direct `lgc.growth_estimate` bound for the OS inner product of a single
positive-time one-point test against itself. -/
theorem onePoint_inner_self_bounded_vi1Bounds_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1)
    (hf : tsupport ((f : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
          (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ : OSPreHilbertSpace OS)
          (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ : OSPreHilbertSpace OS)‖ ≤ C := by
  let s := lgc.sobolev_index
  have hzero :
      VanishesToInfiniteOrderOnCoincidence (f.osConjTensorProduct f) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1) (f := f) (g := f) hf hf
  let P : ℝ :=
    lgc.alpha * lgc.beta ^ 2 * ((2).factorial : ℝ) ^ lgc.gamma
  let S : ℝ :=
    2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
      ((SchwartzMap.seminorm ℝ s i f) * (SchwartzMap.seminorm ℝ 0 (s - i) f) +
        (SchwartzMap.seminorm ℝ 0 i f) * (SchwartzMap.seminorm ℝ s (s - i) f))
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    have halpha_nonneg : 0 ≤ lgc.alpha := le_of_lt lgc.alpha_pos
    have hbeta_nonneg : 0 ≤ lgc.beta ^ 2 := by
      exact pow_nonneg (le_of_lt lgc.beta_pos) _
    have hfac_nonneg : 0 ≤ ((2).factorial : ℝ) := by positivity
    have hrpow_nonneg : 0 ≤ ((2).factorial : ℝ) ^ lgc.gamma := by
      simpa using Real.rpow_nonneg hfac_nonneg lgc.gamma
    exact mul_nonneg (mul_nonneg halpha_nonneg hbeta_nonneg) hrpow_nonneg
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact Finset.sum_nonneg (by
        intro i
        intro hi
        refine mul_nonneg (Nat.cast_nonneg _) ?_
        refine add_nonneg ?_ ?_
        · exact mul_nonneg (by positivity) (by positivity)
        · exact mul_nonneg (by positivity) (by positivity))
  refine ⟨P * S, mul_nonneg hP_nonneg hS_nonneg, ?_⟩
  have hsingle :
      PositiveTimeBorchersSequence.osInner OS
        (PositiveTimeBorchersSequence.single 1 f hf)
        (PositiveTimeBorchersSequence.single 1 f hf) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct f)) := by
    unfold PositiveTimeBorchersSequence.osInner
    simpa using
      (OSInnerProduct_single_single (d := d) OS.S OS.E0_linear 1 1 f f)
  have hgrowth :
      ‖OS.S 2 ⟨f.osConjTensorProduct f, hzero⟩‖ ≤
        P * SchwartzMap.seminorm ℝ s s (f.osConjTensorProduct f) := by
    simpa [P, s] using lgc.growth_estimate 2 ⟨f.osConjTensorProduct f, hzero⟩
  have htensor :
      SchwartzMap.seminorm ℝ s s (f.osConjTensorProduct f) ≤ S := by
    calc
      SchwartzMap.seminorm ℝ s s (f.osConjTensorProduct f)
          = SchwartzMap.seminorm ℝ s s (f.osConj.tensorProduct f) := by
              rfl
      _ ≤ 2 ^ s * ∑ i ∈ Finset.range (s + 1), ↑(s.choose i) *
            ((SchwartzMap.seminorm ℝ s i f.osConj) * (SchwartzMap.seminorm ℝ 0 (s - i) f) +
              (SchwartzMap.seminorm ℝ 0 i f.osConj) * (SchwartzMap.seminorm ℝ s (s - i) f)) :=
            SchwartzMap.tensorProduct_seminorm_le (p := s) (l := s) f.osConj f
      _ ≤ S := by
        dsimp [S]
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
        intro i hi
        have hfSi : SchwartzMap.seminorm ℝ s i f.osConj ≤ SchwartzMap.seminorm ℝ s i f :=
          SchwartzNPoint.seminorm_osConj_le (d := d) s i f
        have hf0i : SchwartzMap.seminorm ℝ 0 i f.osConj ≤ SchwartzMap.seminorm ℝ 0 i f :=
          SchwartzNPoint.seminorm_osConj_le (d := d) 0 i f
        have hci : (0 : ℝ) ≤ ↑(s.choose i) := Nat.cast_nonneg _
        apply mul_le_mul_of_nonneg_left ?_ hci
        refine add_le_add ?_ ?_
        · exact mul_le_mul hfSi le_rfl (by positivity) (by positivity)
        · exact mul_le_mul hf0i le_rfl (by positivity) (by positivity)
  calc
    ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
        (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ : OSPreHilbertSpace OS)
        (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ : OSPreHilbertSpace OS)‖
      = ‖OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct f))‖ := by
          rw [OSPreHilbertSpace.inner_eq]
          rw [hsingle]
    _ = ‖OS.S 2 ⟨f.osConjTensorProduct f, hzero⟩‖ := by
          rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f.osConjTensorProduct f) hzero]
    _ ≤ P * SchwartzMap.seminorm ℝ s s (f.osConjTensorProduct f) := hgrowth
    _ ≤ P * S := by exact mul_le_mul_of_nonneg_left htensor hP_nonneg
    _ = P * (2 ^ s *
          ∑ i ∈ Finset.range (s + 1),
            ↑(s.choose i) *
              (SchwartzMap.seminorm ℝ s i f * SchwartzMap.seminorm ℝ 0 (s - i) f +
                SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ s (s - i) f)) := by
          rfl

/-- Generic OS semigroup-group diagonal matrix elements are bounded by the
square norm of the underlying vector, uniformly in positive time and all
spatial translations. -/
theorem osSemigroupGroupMatrixElement_norm_le_two_mul_norm_sq_vi1Bounds_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : OSHilbertSpace OS)
    (t : ℝ) (a : Fin d → ℝ)
    (ht : 0 < t) :
    ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ 2 * ‖x‖ ^ 2 := by
  have hU :
      osSpatialTranslateHilbert (d := d) OS a ∈
        unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
    constructor
    · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
    · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
  have hU_norm :
      ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ := by
    simpa using
      (ContinuousLinearMap.norm_map_of_mem_unitary
        (u := osSpatialTranslateHilbert (d := d) OS a) hU x)
  calc
    ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖
        = ‖@inner ℂ (OSHilbertSpace OS) _ x
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              have hinner :
                  osSemigroupGroupMatrixElement (d := d) OS lgc x t a =
                    @inner ℂ (OSHilbertSpace OS) _ x
                      ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                        ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
                simpa [osSpatialTranslateHilbert_zero (d := d) OS] using
                  (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                    (d := d) OS lgc x (0 : Fin d → ℝ) a t ht)
              rw [hinner]
    _ ≤ ‖x‖ *
          ‖(osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
            exact norm_inner_le_norm _ _
    _ ≤ ‖x‖ *
          (‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)‖ *
            ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm
              (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) x)
    _ ≤ ‖x‖ * (2 * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
            gcongr
            exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (t : ℂ) (by simpa using ht)
    _ = ‖x‖ * (2 * ‖x‖) := by rw [hU_norm]
    _ = 2 * ‖x‖ ^ 2 := by ring

/-- Combining the one-point OS inner bound with the generic semigroup-group
matrix-element estimate gives a finite positive-time orbit bound for any
positive-time one-point test. -/
theorem onePoint_osSemigroupGroupMatrixElement_bounded_vi1Bounds_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1)
    (hf : tsupport ((f : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1) :
    let xpre : OSPreHilbertSpace OS := (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ :
      OSPreHilbertSpace OS)
    let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ C := by
  dsimp
  let xpre : OSPreHilbertSpace OS := (⟦PositiveTimeBorchersSequence.single 1 f hf⟧ :
    OSPreHilbertSpace OS)
  let x : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS))
  rcases onePoint_inner_self_bounded_vi1Bounds_local (d := d) OS lgc f hf with
    ⟨C0, hC0_nonneg, hC0⟩
  have hx_sq_eq :
      ‖x‖ ^ 2 =
        ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            xpre xpre‖ := by
    calc
      ‖x‖ ^ 2 = ‖@inner ℂ (OSHilbertSpace OS) _ x x‖ := by
        simpa using (norm_sq_eq (x := x))
      _ = ‖@inner ℂ (OSPreHilbertSpace OS) (OSPreHilbertSpace.instInner OS)
            xpre xpre‖ := by
          rw [show x = (((show OSPreHilbertSpace OS from xpre) : OSHilbertSpace OS)) by rfl]
          rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  have hx_sq_le : ‖x‖ ^ 2 ≤ C0 := by
    rw [hx_sq_eq]
    exact hC0
  refine ⟨2 * C0, by positivity, ?_⟩
  intro t a ht
  calc
    ‖osSemigroupGroupMatrixElement (d := d) OS lgc x t a‖ ≤ 2 * ‖x‖ ^ 2 :=
      osSemigroupGroupMatrixElement_norm_le_two_mul_norm_sq_vi1Bounds_local
        (d := d) OS lgc x t a ht
    _ ≤ 2 * C0 := by
      exact mul_le_mul_of_nonneg_left hx_sq_le (by positivity)
