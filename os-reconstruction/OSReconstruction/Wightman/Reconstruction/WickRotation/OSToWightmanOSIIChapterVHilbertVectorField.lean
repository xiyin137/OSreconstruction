/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceTaylor














noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

set_option backward.isDefEq.respectTransparency false in
/-- A pointwise limit of continuous complex-linear maps from complex Schwartz
space is again continuous complex-linear.

Continuity is obtained from Banach-Steinhaus on the underlying real
barrelled Schwartz space; complex linearity follows by uniqueness of limits.
-/
noncomputable def SchwartzMap.continuousLinearMapOfTendstoComplex
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    [CompleteSpace H]
    (T : ℕ → SchwartzMap E ℂ →L[ℂ] H)
    (F : SchwartzMap E ℂ → H)
    (hT :
      Tendsto (fun n f => T n f) atTop (𝓝 F)) :
    SchwartzMap E ℂ →L[ℂ] H := by
  have hF_add : ∀ f g, F (f + g) = F f + F g := by
    intro f g
    apply tendsto_nhds_unique
      ((tendsto_pi_nhds.mp hT) (f + g))
    simpa only [map_add] using
      ((tendsto_pi_nhds.mp hT) f).add
        ((tendsto_pi_nhds.mp hT) g)
  have hF_smul : ∀ c : ℂ, ∀ f, F (c • f) = c • F f := by
    intro c f
    apply tendsto_nhds_unique
      ((tendsto_pi_nhds.mp hT) (c • f))
    simpa only [map_smul] using
      tendsto_const_nhds.smul ((tendsto_pi_nhds.mp hT) f)
  letI : ContinuousSMul ℝ (SchwartzMap E ℂ) :=
    SchwartzMap.instContinuousSMul
  let LR : SchwartzMap E ℂ →L[ℝ] H :=
    continuousLinearMapOfTendsto
      (fun n => (T n).restrictScalars ℝ) hT
  exact
    { toLinearMap :=
        { toFun := F
          map_add' := hF_add
          map_smul' := hF_smul }
      cont := by
        simpa [LR, continuousLinearMapOfTendsto] using LR.continuous }

/-- Fixed positive-time source Taylor coefficients before selecting the
complex increment. -/
structure PositiveTimeSourceTaylorFamily
    (d n k : ℕ) [NeZero d] where
  coefficient :
    (Fin k → ℕ) → euclideanPositiveTimeSubmodule (d := d) n

namespace PositiveTimeSourceTaylorFamily

variable {d n k : ℕ} [NeZero d]

/-- Evaluate a fixed source Taylor family at one complex increment. -/
def coefficientData
    (T : PositiveTimeSourceTaylorFamily d n k)
    (increment : Fin k → ℂ) :
    PositiveTimeSourceCoefficientData d n k where
  coefficient := T.coefficient
  increment := increment

/-- One source Taylor monomial. -/
def monomial
    (T : PositiveTimeSourceTaylorFamily d n k)
    (increment : Fin k → ℂ)
    (α : Fin k → ℕ) : ℂ :=
  ∏ i, increment i ^ α i

/-- The homogeneous positive-time source polynomial of total degree `p`. -/
def homogeneousSource
    (T : PositiveTimeSourceTaylorFamily d n k)
    (increment : Fin k → ℂ)
    (p : ℕ) : euclideanPositiveTimeSubmodule (d := d) n :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
    T.monomial increment α • T.coefficient α

@[simp] theorem coefficientData_homogeneousSource
    (T : PositiveTimeSourceTaylorFamily d n k)
    (increment : Fin k → ℂ)
    (p : ℕ) :
    (T.coefficientData increment).homogeneousSource p =
      T.homogeneousSource increment p :=
  rfl

/-- The finite OS Hilbert Taylor polynomial. -/
def partialSum
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (increment : Fin k → ℂ) : OSHilbertSpace OS :=
  ∑ p ∈ Finset.range N,
    ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
      T.monomial increment α •
        osiiPositiveTimeSingleVectorCLM OS n (T.coefficient α)

/-- The source-level and Hilbert-level presentations of the finite Taylor
polynomial agree. -/
theorem partialSum_eq_source
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (increment : Fin k → ℂ) :
    T.partialSum OS N increment =
      osiiPositiveTimeSingleVectorCLM OS n
        (∑ p ∈ Finset.range N,
          T.homogeneousSource increment p) := by
  simp only [partialSum, homogeneousSource, map_sum, map_smul]

/-- The finite Taylor polynomial is the partial sum of the concrete reflected
Hilbert Gram data at that increment. -/
theorem partialSum_eq_gramData
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (increment : Fin k → ℂ) :
    T.partialSum OS N increment =
      (positiveTimeTaylorGramData OS n
        (T.homogeneousSource increment)).partialSum N := by
  rw [positiveTimeTaylorGramData_partialSum_eq]
  exact T.partialSum_eq_source OS N increment

@[simp] theorem homogeneousSource_zero_zero
    (T : PositiveTimeSourceTaylorFamily d n k) :
    T.homogeneousSource 0 0 = T.coefficient 0 := by
  rw [homogeneousSource, Finset.Nat.antidiagonalTuple_zero_right]
  simp [monomial]

@[simp] theorem homogeneousSource_zero_succ
    (T : PositiveTimeSourceTaylorFamily d n k)
    (p : ℕ) :
    T.homogeneousSource 0 (p + 1) = 0 := by
  rw [homogeneousSource]
  apply Finset.sum_eq_zero
  intro α hα
  have hsum :
      ∑ i, α i = p + 1 :=
    Finset.Nat.mem_antidiagonalTuple.mp hα
  have hα_ne : α ≠ 0 := by
    intro h
    subst α
    simp at hsum
  have hi : ∃ i, α i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hα_ne (funext h)
  obtain ⟨i, hi⟩ := hi
  rw [monomial,
    Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi),
    zero_smul]

/-- Every nonempty finite Taylor polynomial evaluates at zero to the original
OS source vector. -/
theorem partialSum_zero_of_one_le
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    {N : ℕ} (hN : 1 ≤ N) :
    T.partialSum OS N 0 =
      osiiPositiveTimeSingleVectorCLM OS n (T.coefficient 0) := by
  rw [T.partialSum_eq_source]
  rw [← Finset.sum_range_add_sum_Ico _ hN]
  have htail :
      ∑ p ∈ Finset.Ico 1 N, T.homogeneousSource 0 p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_Ico.mp hp
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp1
    simpa [Nat.add_comm] using T.homogeneousSource_zero_succ q
  rw [htail, add_zero, Finset.sum_range_one,
    T.homogeneousSource_zero_zero]

/-- A locally uniform Hilbert Taylor field is anchored at zero by the
original positive-time OS source vector. -/
theorem limit_zero_eq_source
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin k → ℂ) → OSHilbertSpace OS)
    (U : Set (Fin k → ℂ))
    (hzero : (0 : Fin k → ℂ) ∈ U)
    (hΨ :
      TendstoLocallyUniformlyOn (T.partialSum OS) Ψ atTop U) :
    Ψ 0 = osiiPositiveTimeSingleVectorCLM OS n (T.coefficient 0) := by
  have htendsto :
      Tendsto (fun N => T.partialSum OS N 0) atTop (𝓝 (Ψ 0)) :=
    hΨ.tendsto_at hzero
  have heventually :
      (fun N => T.partialSum OS N 0) =ᶠ[atTop]
        fun _ => osiiPositiveTimeSingleVectorCLM OS n (T.coefficient 0) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact T.partialSum_zero_of_one_le OS hN
  exact tendsto_nhds_unique htendsto
    (tendsto_const_nhds.congr' heventually.symm)

theorem differentiable_monomial
    (T : PositiveTimeSourceTaylorFamily d n k)
    (α : Fin k → ℕ) :
    Differentiable ℂ (fun z => T.monomial z α) := by
  unfold monomial
  fun_prop

/-- Every finite OS Hilbert Taylor polynomial is entire in the increment. -/
theorem differentiable_partialSum
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ) :
    Differentiable ℂ (T.partialSum OS N) := by
  apply Differentiable.fun_sum
  intro p hp
  apply Differentiable.fun_sum
  intro α hα
  exact (T.differentiable_monomial α).smul_const _

private theorem norm_reflectedCauchyIncrement_le
    {r : ℝ} {increment : Fin k → ℂ}
    (hincrement : ∀ i, ‖increment i‖ ≤ r) :
    ∀ j, ‖reflectedCauchyIncrement increment j‖ ≤ r := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedCauchyIncrement_left (k := k)]
    simpa using hincrement i
  · intro i
    rw [reflectedCauchyIncrement_right (k := k)]
    exact hincrement i

private theorem norm_reflectedCauchyIncrement_lt
    {R : ℝ} {increment : Fin k → ℂ}
    (hincrement : ∀ i, ‖increment i‖ < R) :
    ∀ j, ‖reflectedCauchyIncrement increment j‖ < R := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedCauchyIncrement_left (k := k)]
    simpa using hincrement i
  · intro i
    rw [reflectedCauchyIncrement_right (k := k)]
    exact hincrement i

/-- A fixed reflected scalar Cauchy polydisc makes the positive-time Hilbert
Taylor polynomials uniformly Cauchy on every strictly smaller closed
polydisc, provided the scalar Gram coefficients have the genuine reflected
Cauchy identification there. -/
theorem uniformCauchySeqOn_partialSum_of_reflectedPolydisc
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (D : ReflectedCauchyPolydiscData k)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.radius)
    (hcoeff :
      ∀ z ∈ SCV.closedPolydisc
          (0 : Fin k → ℂ) (fun _ => r),
        ∀ p q,
          ∀ hincrement :
            ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius,
          positiveTimeTaylorScalarGram OS n
              (T.homogeneousSource z) p q =
            (D.atIncrement
              (reflectedCauchyIncrement z) hincrement).scalarGram p q) :
    UniformCauchySeqOn
      (T.partialSum OS) atTop
      (SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r)) := by
  let G :
      (Fin k → ℂ) → HilbertTaylorGramData (OSHilbertSpace OS) :=
    fun z => positiveTimeTaylorGramData OS n (T.homogeneousSource z)
  have hG :
      UniformCauchySeqOn
        (fun N z => (G z).partialSum N) atTop
        (SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r)) := by
    apply
      HilbertTaylorGramData.uniformCauchySeqOn_partialSum_of_norm_scalarGram_le
        G
        (SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r))
        (D.gradedMajorant r)
        (D.gradedMajorant_nonneg hr)
        (D.summable_gradedMajorant hr hrR)
    intro z hz p q
    have hz_le : ∀ i, ‖z i‖ ≤ r := by
      intro i
      simpa [dist_zero_right] using hz i
    have hz_lt : ∀ i, ‖z i‖ < D.radius :=
      fun i => (hz_le i).trans_lt hrR
    let hincrement :
        ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius :=
      norm_reflectedCauchyIncrement_lt hz_lt
    rw [positiveTimeTaylorGramData_scalarGram,
      hcoeff z hz p q hincrement]
    exact
      D.norm_scalarGram_atIncrement_le_gradedMajorant
        hr hrR (reflectedCauchyIncrement z) hincrement
        (norm_reflectedCauchyIncrement_le hz_le) p q
  have hpartial :
      T.partialSum OS =
        fun N z =>
          (positiveTimeTaylorGramData OS n
            (T.homogeneousSource z)).partialSum N := by
    funext N z
    exact T.partialSum_eq_gramData OS N z
  rw [hpartial]
  exact hG

/-- A single reflected scalar Cauchy polydisc constructs the holomorphic OS
Hilbert-valued Taylor field on its open interior.

The scalar coefficient identity is required throughout the open polydisc.
Uniform convergence on smaller closed polydiscs, completeness, and strong
holomorphy are then consequences rather than extra hypotheses. -/
theorem exists_holomorphicField_of_reflectedPolydisc
    (T : PositiveTimeSourceTaylorFamily d n k)
    (OS : OsterwalderSchraderAxioms d)
    (D : ReflectedCauchyPolydiscData k)
    (hcoeff :
      ∀ z ∈ SCV.Polydisc
          (0 : Fin k → ℂ) (fun _ => D.radius),
        ∀ p q,
          ∀ hincrement :
            ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius,
          positiveTimeTaylorScalarGram OS n
              (T.homogeneousSource z) p q =
            (D.atIncrement
              (reflectedCauchyIncrement z) hincrement).scalarGram p q) :
    ∃ Ψ : (Fin k → ℂ) → OSHilbertSpace OS,
      TendstoLocallyUniformlyOn
          (T.partialSum OS) Ψ atTop
          (SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)) ∧
        DifferentiableOn ℂ Ψ
          (SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)) := by
  apply
    SCV.exists_tendstoLocallyUniformlyOn_differentiableOn_fin_of_locally_uniformCauchy
  · intro z hz
    let r := (‖z‖ + D.radius) / 2
    have hz_norm : ‖z‖ < D.radius := by
      rw [pi_norm_lt_iff D.radius_pos]
      intro i
      simpa [dist_zero_right] using hz i
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      linarith [norm_nonneg z, D.radius_pos]
    have hzr : ‖z‖ < r := by
      dsimp [r]
      linarith
    have hrR : r < D.radius := by
      dsimp [r]
      linarith
    let V :=
      SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r)
    have hz_open :
        z ∈ SCV.Polydisc (0 : Fin k → ℂ) (fun _ => r) := by
      intro i
      change dist (z i) 0 < r
      rw [dist_zero_right]
      exact (norm_le_pi_norm z i).trans_lt hzr
    have hV_nhds :
        V ∈ 𝓝[
          SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)] z := by
      apply mem_nhdsWithin_of_mem_nhds
      exact Filter.mem_of_superset
        (SCV.polydisc_isOpen.mem_nhds hz_open)
        SCV.polydisc_subset_closedPolydisc
    refine ⟨V, hV_nhds, ?_⟩
    apply T.uniformCauchySeqOn_partialSum_of_reflectedPolydisc
      OS D hr_nonneg hrR
    intro w hw p q hincrement
    apply hcoeff w
    intro i
    exact (hw i).trans_lt hrR
  · intro N
    exact (T.differentiable_partialSum OS N).differentiableOn
  · exact SCV.polydisc_isOpen

end PositiveTimeSourceTaylorFamily

end OSIIChapterV
end OSReconstruction
