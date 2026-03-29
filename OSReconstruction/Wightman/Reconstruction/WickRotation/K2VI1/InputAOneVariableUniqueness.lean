import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- On the positive-time strip, two continuous one-variable kernels agree once
they have the same compact-support Schwartz pairings there. -/
theorem eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local
    {K K' : SpacetimeDim d → ℂ}
    (hK : ContinuousOn K {ξ : SpacetimeDim d | 0 < ξ 0})
    (hK' : ContinuousOn K' {ξ : SpacetimeDim d | 0 < ξ 0})
    (hint : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
      ∫ ξ : SpacetimeDim d, K ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K' ξ * h ξ) :
    Set.EqOn K K' {ξ : SpacetimeDim d | 0 < ξ 0} := by
  have hU : IsOpen ({ξ : SpacetimeDim d | 0 < ξ 0} : Set (SpacetimeDim d)) := by
    simpa using isOpen_lt continuous_const (continuous_apply (0 : Fin (d + 1)))
  exact SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
    (E := SpacetimeDim d) hU hK hK' hint

/-- If a family of positive-time kernels induces the same compact-support
Schwartz pairing functional on the strip `{ξ₀ > 0}`, one kernel may be chosen
for all members of the family. -/
theorem exists_common_positiveTime_kernel_of_compactSupport_pairing_eq_local
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | 0 < ξ 0})
    (hh_pos : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (hpair_eq : ∀ n m (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_seq m ξ * h ξ) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | 0 < ξ 0} ∧
      ∀ n, I n = ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := by
  refine ⟨K_seq 0, hK_cont 0, ?_⟩
  intro n
  have hEqOn :
      Set.EqOn (K_seq n) (K_seq 0) {ξ : SpacetimeDim d | 0 < ξ 0} := by
    exact eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local
      (d := d) (hK_cont n) (hK_cont 0) (hpair_eq n 0)
  calc
    I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ := hfactor n
    _ = ∫ ξ : SpacetimeDim d, K_seq 0 ξ * h_seq n ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hzero : h_seq n ξ = 0
          · simp [hzero]
          · have hξ_mem : ξ ∈ tsupport (h_seq n : SpacetimeDim d → ℂ) := by
              exact subset_tsupport _ (Function.mem_support.mpr hzero)
            have hξ_pos : 0 < ξ 0 := hh_pos n hξ_mem
            simp [hEqOn hξ_pos]

/-- Input-A shaped consequence of the previous theorem: once the per-probe
one-variable kernels induce the same compact-support positive-time functional,
one common difference kernel factors all admissible shells. -/
theorem exists_common_differenceKernel_factorization_of_common_positiveTime_pairing_eq_local
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | 0 < ξ 0})
    (hh_pos : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (hpair_eq : ∀ n m (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_seq m ξ * h ξ) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | 0 < ξ 0} ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K x *
              twoPointDifferenceLift χ₀ (h_seq n) x := by
  obtain ⟨K, hK_cont, hcommon⟩ :=
    exists_common_positiveTime_kernel_of_compactSupport_pairing_eq_local
      (d := d) K_seq h_seq I hK_cont hh_pos hfactor hpair_eq
  refine ⟨K, hK_cont, ?_⟩
  intro n
  calc
    I n = ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := hcommon n
    _ = (∫ u : SpacetimeDim d, χ₀ u) * ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := by
          rw [hχ₀]
          ring
    _ =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K x *
            twoPointDifferenceLift χ₀ (h_seq n) x := by
          symm
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K χ₀ (h_seq n)

/-- The common-functional version of the previous theorem: if every per-probe
positive-time kernel induces one fixed compact-support functional, then one
common difference kernel already factors all Input-A shells. -/
theorem exists_common_differenceKernel_factorization_of_common_positiveTime_functional_local
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | 0 < ξ 0})
    (hh_pos : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (L : SchwartzSpacetime d → ℂ)
    (hcommon : ∀ n (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ = L h) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | 0 < ξ 0} ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K x *
              twoPointDifferenceLift χ₀ (h_seq n) x := by
  refine exists_common_differenceKernel_factorization_of_common_positiveTime_pairing_eq_local
    (d := d) χ₀ hχ₀ K_seq h_seq I hK_cont hh_pos hfactor ?_
  intro n m h hh_compact hh_pos_h
  rw [hcommon n h hh_compact hh_pos_h, hcommon m h hh_compact hh_pos_h]

/-- Fixed-strip uniqueness variant: if two kernels are continuous on the open
strip `{-t < ξ₀}`, then compact-support Schwartz pairing equality on that strip
forces pointwise equality there. -/
theorem eqOn_fixedStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local
    (t : ℝ)
    {K K' : SpacetimeDim d → ℂ}
    (hK : ContinuousOn K {ξ : SpacetimeDim d | -t < ξ 0})
    (hK' : ContinuousOn K' {ξ : SpacetimeDim d | -t < ξ 0})
    (hint : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0} →
      ∫ ξ : SpacetimeDim d, K ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K' ξ * h ξ) :
    Set.EqOn K K' {ξ : SpacetimeDim d | -t < ξ 0} := by
  have hU : IsOpen ({ξ : SpacetimeDim d | -t < ξ 0} : Set (SpacetimeDim d)) := by
    simpa using isOpen_lt continuous_const (continuous_apply (0 : Fin (d + 1)))
  exact SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
    (E := SpacetimeDim d) hU hK hK' hint

/-- A kernel continuous on a fixed strip is continuous at the origin whenever
the strip contains `0`. This is the exact continuity-at-zero payoff needed by
the descended approximate-identity step. -/
theorem continuousAt_zero_of_continuousOn_fixedStrip_local
    (t : ℝ)
    (ht : 0 < t)
    {K : SpacetimeDim d → ℂ}
    (hK : ContinuousOn K {ξ : SpacetimeDim d | -t < ξ 0}) :
    ContinuousAt K 0 := by
  have hU : IsOpen ({ξ : SpacetimeDim d | -t < ξ 0} : Set (SpacetimeDim d)) := by
    simpa using isOpen_lt continuous_const (continuous_apply (0 : Fin (d + 1)))
  exact (hU.continuousOn_iff.mp hK) (by simp [ht])

/-- Fixed-strip common-kernel package: if all per-probe kernels are continuous
on `{-t < ξ₀}`, all shell tests live on that strip, each `Iₙ` already
factorizes through its own kernel, and all compact-support strip pairings are
independent of `n`, then one common kernel works for every `n`. -/
theorem exists_common_fixedStrip_kernel_of_compactSupport_pairing_eq_local
    (t : ℝ)
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | -t < ξ 0})
    (hh_strip : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (hpair_eq : ∀ n m (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_seq m ξ * h ξ) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | -t < ξ 0} ∧
      ∀ n, I n = ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := by
  refine ⟨K_seq 0, hK_cont 0, ?_⟩
  intro n
  have hEqOn :
      Set.EqOn (K_seq n) (K_seq 0) {ξ : SpacetimeDim d | -t < ξ 0} := by
    exact eqOn_fixedStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local
      (d := d) t (hK_cont n) (hK_cont 0) (hpair_eq n 0)
  calc
    I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ := hfactor n
    _ = ∫ ξ : SpacetimeDim d, K_seq 0 ξ * h_seq n ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hzero : h_seq n ξ = 0
          · simp [hzero]
          · have hξ_mem : ξ ∈ tsupport (h_seq n : SpacetimeDim d → ℂ) := by
              exact subset_tsupport _ (Function.mem_support.mpr hzero)
            have hξ_strip : -t < ξ 0 := hh_strip n hξ_mem
            simp [hEqOn hξ_strip]

/-- Fixed-strip difference-kernel factorization: once all per-probe kernels
induce the same compact-support functional on `{-t < ξ₀}`, one common
difference kernel already works for all descended shells. -/
theorem exists_common_differenceKernel_factorization_of_common_fixedStrip_pairing_eq_local
    (t : ℝ)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | -t < ξ 0})
    (hh_strip : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (hpair_eq : ∀ n m (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_seq m ξ * h ξ) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | -t < ξ 0} ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K x *
              twoPointDifferenceLift χ₀ (h_seq n) x := by
  obtain ⟨K, hK_cont_common, hcommon⟩ :=
    exists_common_fixedStrip_kernel_of_compactSupport_pairing_eq_local
      (d := d) t K_seq h_seq I hK_cont hh_strip hfactor hpair_eq
  refine ⟨K, hK_cont_common, ?_⟩
  intro n
  calc
    I n = ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := hcommon n
    _ = (∫ u : SpacetimeDim d, χ₀ u) * ∫ ξ : SpacetimeDim d, K ξ * h_seq n ξ := by
          rw [hχ₀]
          ring
    _ =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K x *
            twoPointDifferenceLift χ₀ (h_seq n) x := by
          symm
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K χ₀ (h_seq n)

/-- Final fixed-strip common-functional reduction: if all compact-support strip
pairings are represented by one fixed functional `L`, then one common kernel is
enough for the whole Input-A factorization, together with continuity at `0`. -/
theorem exists_common_differenceKernel_factorization_of_common_fixedStrip_functional_local
    (t : ℝ)
    (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K_seq : ℕ → SpacetimeDim d → ℂ)
    (h_seq : ℕ → SchwartzSpacetime d)
    (I : ℕ → ℂ)
    (hK_cont : ∀ n, ContinuousOn (K_seq n) {ξ : SpacetimeDim d | -t < ξ 0})
    (hh_strip : ∀ n, tsupport (h_seq n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0})
    (hfactor : ∀ n, I n = ∫ ξ : SpacetimeDim d, K_seq n ξ * h_seq n ξ)
    (L : SchwartzSpacetime d → ℂ)
    (hcommon : ∀ n (h : SchwartzSpacetime d),
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -t < ξ 0} →
      ∫ ξ : SpacetimeDim d, K_seq n ξ * h ξ = L h) :
    ∃ K : SpacetimeDim d → ℂ,
      ContinuousOn K {ξ : SpacetimeDim d | -t < ξ 0} ∧
      ContinuousAt K 0 ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K x *
              twoPointDifferenceLift χ₀ (h_seq n) x := by
  obtain ⟨K, hK_cont_common, hpair_common⟩ :=
    exists_common_differenceKernel_factorization_of_common_fixedStrip_pairing_eq_local
      (d := d) t χ₀ hχ₀ K_seq h_seq I hK_cont hh_strip hfactor (by
        intro n m h hh_compact hh_strip_h
        rw [hcommon n h hh_compact hh_strip_h, hcommon m h hh_compact hh_strip_h])
  have hK0 : ContinuousAt K 0 := by
    exact continuousAt_zero_of_continuousOn_fixedStrip_local
      (d := d) t ht hK_cont_common
  exact ⟨K, hK_cont_common, hK0, hpair_common⟩

end OSReconstruction
