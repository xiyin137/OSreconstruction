/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWSideCone
import OSReconstruction.SCV.LocalEOWFixedBasis

/-!
# One-Chart Local EOW Envelope Geometry

This file starts the one-chart distributional EOW envelope layer with the
small chart-side geometry needed by the recovery theorem.  The strict side
balls are coordinate objects, but their images under `localEOWChart` have
original imaginary parts transported by `localEOWRealLinearPart ys`; this is
the chart-linear correction needed before the real-mollifier kernel route.
-/

noncomputable section

open Complex Metric Set

namespace SCV

variable {m : ℕ}

/-- Strict positive chart-side ball used by the local recovery theorem. -/
def StrictPositiveImagBall (R : ℝ) : Set (ComplexChartSpace m) :=
  Metric.ball 0 R ∩ {w | ∀ j, 0 < (w j).im}

/-- Strict negative chart-side ball used by the local recovery theorem. -/
def StrictNegativeImagBall (R : ℝ) : Set (ComplexChartSpace m) :=
  Metric.ball 0 R ∩ {w | ∀ j, (w j).im < 0}

theorem isOpen_StrictPositiveImagBall (R : ℝ) :
    IsOpen (StrictPositiveImagBall (m := m) R) := by
  dsimp [StrictPositiveImagBall]
  refine Metric.isOpen_ball.inter ?_
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_apply j))

theorem isOpen_StrictNegativeImagBall (R : ℝ) :
    IsOpen (StrictNegativeImagBall (m := m) R) := by
  dsimp [StrictNegativeImagBall]
  refine Metric.isOpen_ball.inter ?_
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (Complex.continuous_im.comp (continuous_apply j))
      continuous_const

/-- Coordinatewise imaginary part is norm-controlled by the complex chart
norm. -/
theorem norm_complexChart_im_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).im)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm (w j)).trans (norm_le_pi_norm w j)

/-- Coordinatewise real part is norm-controlled by the complex chart norm. -/
theorem norm_complexChart_re_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).re)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (w j)).trans (norm_le_pi_norm w j)

theorem norm_complexChart_im_lt_of_mem_ball {R : ℝ}
    {w : ComplexChartSpace m} (hw : w ∈ Metric.ball 0 R) :
    ‖(fun j : Fin m => (w j).im)‖ < R := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact lt_of_le_of_lt (norm_complexChart_im_le w) hw

theorem norm_complexChart_re_lt_of_mem_ball {R : ℝ}
    {w : ComplexChartSpace m} (hw : w ∈ Metric.ball 0 R) :
    ‖(fun j : Fin m => (w j).re)‖ < R := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact lt_of_le_of_lt (norm_complexChart_re_le w) hw

theorem StrictPositiveImagBall_im_nonneg {R : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    ∀ j, 0 ≤ (w j).im :=
  fun j => (hw.2 j).le

theorem StrictNegativeImagBall_im_nonpos {R : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    ∀ j, (w j).im ≤ 0 :=
  fun j => (hw.2 j).le

theorem StrictPositiveImagBall_im_sum_pos
    (hm : 0 < m) {R : ℝ} {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    0 < ∑ j, (w j).im := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact Finset.sum_pos (fun j _ => hw.2 j) Finset.univ_nonempty

theorem StrictNegativeImagBall_neg_im_sum_pos
    (hm : 0 < m) {R : ℝ} {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    0 < ∑ j, - (w j).im := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact Finset.sum_pos (fun j _ => neg_pos.mpr (hw.2 j))
    Finset.univ_nonempty

theorem StrictPositiveImagBall_im_sum_le_card_mul {R : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    (∑ j, (w j).im) ≤ (Fintype.card (Fin m) : ℝ) * R := by
  have hcoord : ∀ j, (w j).im ≤ R := by
    intro j
    have hnorm : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hw.1
    exact (calc
      (w j).im ≤ |(w j).im| := le_abs_self _
      _ ≤ ‖w j‖ := Complex.abs_im_le_norm (w j)
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ < R := hnorm).le
  calc
    ∑ j, (w j).im ≤ ∑ _j : Fin m, R :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = (Fintype.card (Fin m) : ℝ) * R := by simp

theorem StrictNegativeImagBall_neg_im_sum_le_card_mul {R : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    (∑ j, - (w j).im) ≤ (Fintype.card (Fin m) : ℝ) * R := by
  have hcoord : ∀ j, - (w j).im ≤ R := by
    intro j
    have hnorm : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hw.1
    exact (calc
      - (w j).im ≤ |-(w j).im| := le_abs_self _
      _ = |(w j).im| := abs_neg _
      _ ≤ ‖w j‖ := Complex.abs_im_le_norm (w j)
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ < R := hnorm).le
  calc
    ∑ j, - (w j).im ≤ ∑ _j : Fin m, R :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = (Fintype.card (Fin m) : ℝ) * R := by simp

/-- Adding a small real chart displacement to a strict positive side point
preserves strict positivity and only enlarges the chart norm by the real
displacement size. -/
theorem StrictPositiveImagBall_add_realEmbed_mem_ball_of_norm_le {R r Rbig : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R)
    {t : Fin m → ℝ} (ht : ‖t‖ ≤ r)
    (hRr : R + r < Rbig) :
    w + realEmbed t ∈ Metric.ball (0 : ComplexChartSpace m) Rbig ∧
      ∀ j, 0 < ((w + realEmbed t) j).im := by
  have hw_norm : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hw.1
  have hreal_norm : ‖realEmbed t‖ ≤ ‖t‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
    intro j
    simp [realEmbed, Complex.norm_real]
    exact norm_le_pi_norm t j
  constructor
  · rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖w + realEmbed t‖ ≤ ‖w‖ + ‖realEmbed t‖ := norm_add_le _ _
      _ ≤ ‖w‖ + ‖t‖ := add_le_add le_rfl hreal_norm
      _ < R + r := add_lt_add_of_lt_of_le hw_norm ht
      _ < Rbig := hRr
  · intro j
    simpa [realEmbed] using hw.2 j

/-- Adding a small real chart displacement to a strict negative side point
preserves strict negativity and only enlarges the chart norm by the real
displacement size. -/
theorem StrictNegativeImagBall_add_realEmbed_mem_ball_of_norm_le {R r Rbig : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R)
    {t : Fin m → ℝ} (ht : ‖t‖ ≤ r)
    (hRr : R + r < Rbig) :
    w + realEmbed t ∈ Metric.ball (0 : ComplexChartSpace m) Rbig ∧
      ∀ j, ((w + realEmbed t) j).im < 0 := by
  have hw_norm : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hw.1
  have hreal_norm : ‖realEmbed t‖ ≤ ‖t‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
    intro j
    simp [realEmbed, Complex.norm_real]
    exact norm_le_pi_norm t j
  constructor
  · rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖w + realEmbed t‖ ≤ ‖w‖ + ‖realEmbed t‖ := norm_add_le _ _
      _ ≤ ‖w‖ + ‖t‖ := add_le_add le_rfl hreal_norm
      _ < R + r := add_lt_add_of_lt_of_le hw_norm ht
      _ < Rbig := hRr
  · intro j
    simpa [realEmbed] using hw.2 j

/-- Simultaneous small scale for the one-chart recovery assembly.  The larger
side-neighborhood radius is `4 * σ`, while the mixed chart-kernel radius is
`2 * σ`. -/
theorem exists_oneChartRecoveryScale
    {δ δside ρin rpoly rψOrig M : ℝ}
    (hδ : 0 < δ)
    (hδside : 0 < δside)
    (hρin : 0 < ρin)
    (hrpoly : 0 < rpoly)
    (hrψOrig : 0 < rψOrig)
    (hM : 0 ≤ M) :
    ∃ σ : ℝ,
      0 < σ ∧
      128 * σ ≤ δ ∧
      4 * σ < δside ∧
      4 * σ < ρin ∧
      (Fintype.card (Fin m) : ℝ) * (4 * σ) < rpoly ∧
      M * (2 * σ) ≤ rψOrig := by
  let c : ℝ := (Fintype.card (Fin m) : ℝ)
  let bδ : ℝ := δ / 256
  let bside : ℝ := δside / 8
  let bρ : ℝ := ρin / 8
  let bpoly : ℝ := rpoly / (8 * (c + 1))
  let bψ : ℝ := rψOrig / (4 * (M + 1))
  let σ : ℝ := min bδ (min bside (min bρ (min bpoly bψ)))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1_pos : 0 < c + 1 := by positivity
  have hM1_pos : 0 < M + 1 := by nlinarith
  have hbδ_pos : 0 < bδ := by
    dsimp [bδ]
    positivity
  have hbside_pos : 0 < bside := by
    dsimp [bside]
    positivity
  have hbρ_pos : 0 < bρ := by
    dsimp [bρ]
    positivity
  have hbpoly_pos : 0 < bpoly := by
    dsimp [bpoly]
    positivity
  have hbψ_pos : 0 < bψ := by
    dsimp [bψ]
    positivity
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact lt_min hbδ_pos
      (lt_min hbside_pos (lt_min hbρ_pos (lt_min hbpoly_pos hbψ_pos)))
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  have hσ_le_bδ : σ ≤ bδ := by
    dsimp [σ]
    exact min_le_left _ _
  have hσ_le_bside : σ ≤ bside := by
    dsimp [σ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hσ_le_bρ : σ ≤ bρ := by
    dsimp [σ]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hσ_le_bpoly : σ ≤ bpoly := by
    dsimp [σ]
    exact (((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  have hσ_le_bψ : σ ≤ bψ := by
    dsimp [σ]
    exact (((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨σ, hσ_pos, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [bδ] at hσ_le_bδ
    nlinarith
  · dsimp [bside] at hσ_le_bside
    nlinarith
  · dsimp [bρ] at hσ_le_bρ
    nlinarith
  · dsimp [bpoly] at hσ_le_bpoly
    have hden_poly : 0 < 8 * (c + 1) := by positivity
    have hmul_poly : σ * (8 * (c + 1)) ≤ rpoly := by
      exact (le_div_iff₀ hden_poly).mp hσ_le_bpoly
    have hcoef : 8 * c ≤ 8 * (c + 1) := by nlinarith
    have hσ8c_le : σ * (8 * c) ≤ σ * (8 * (c + 1)) :=
      mul_le_mul_of_nonneg_left hcoef hσ_nonneg
    have htwo : 2 * (c * (4 * σ)) ≤ rpoly := by
      calc
        2 * (c * (4 * σ)) = σ * (8 * c) := by ring
        _ ≤ σ * (8 * (c + 1)) := hσ8c_le
        _ ≤ rpoly := hmul_poly
    have hhalf : c * (4 * σ) ≤ rpoly / 2 := by
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using htwo)
    have hhalf_lt : rpoly / 2 < rpoly := by nlinarith
    exact lt_of_le_of_lt hhalf hhalf_lt
  · dsimp [bψ] at hσ_le_bψ
    have hdenψ : 0 < 4 * (M + 1) := by positivity
    have hmulψ : σ * (4 * (M + 1)) ≤ rψOrig := by
      exact (le_div_iff₀ hdenψ).mp hσ_le_bψ
    have hcoef : 2 * M ≤ 4 * (M + 1) := by nlinarith
    have hleft : M * (2 * σ) ≤ σ * (4 * (M + 1)) := by
      calc
        M * (2 * σ) = σ * (2 * M) := by ring
        _ ≤ σ * (4 * (M + 1)) :=
          mul_le_mul_of_nonneg_left hcoef hσ_nonneg
    exact hleft.trans hmulψ

/-- Scalar radius margins forced by the one-chart recovery scale.  These are
the finite arithmetic inequalities used by the local product-kernel recovery
call. -/
theorem oneChartRecoveryScale_radius_margins
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 128 * σ ≤ δ) :
    0 < 8 * σ ∧
      8 * σ < 16 * σ ∧
      16 * σ < δ / 2 ∧
      2 * (8 * σ) < δ / 4 ∧
      σ + σ < 4 * σ ∧
      4 * σ + (σ + σ) < 8 * σ := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A real translation by a kernel supported in the core radius sends the
chart core ball into the descent ball. -/
theorem oneChartRecoveryScale_core_translate_mem_desc
    {σ : ℝ} (hσ : 0 < σ)
    {z : ComplexChartSpace m} (hz : z ∈ Metric.ball 0 σ)
    {t : Fin m → ℝ} (ht : ‖t‖ ≤ σ) :
    z + realEmbed t ∈ Metric.ball (0 : ComplexChartSpace m) (4 * σ) := by
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  have hreal_norm : ‖realEmbed t‖ ≤ ‖t‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
    intro j
    simp [realEmbed, Complex.norm_real]
    exact norm_le_pi_norm t j
  calc
    ‖z + realEmbed t‖ ≤ ‖z‖ + ‖realEmbed t‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖t‖ := add_le_add le_rfl hreal_norm
    _ < σ + σ := add_lt_add_of_lt_of_le hz ht
    _ < 4 * σ := by nlinarith

/-- A real translation by the mixed recovery radius sends the descent ball into
the covariance ball. -/
theorem oneChartRecoveryScale_desc_translate_mem_cov
    {σ : ℝ} (hσ : 0 < σ)
    {z : ComplexChartSpace m} (hz : z ∈ Metric.ball 0 (4 * σ))
    {t : Fin m → ℝ} (ht : ‖t‖ ≤ σ + σ) :
    z + realEmbed t ∈ Metric.ball (0 : ComplexChartSpace m) (8 * σ) := by
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  have hreal_norm : ‖realEmbed t‖ ≤ ‖t‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
    intro j
    simp [realEmbed, Complex.norm_real]
    exact norm_le_pi_norm t j
  calc
    ‖z + realEmbed t‖ ≤ ‖z‖ + ‖realEmbed t‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖t‖ := add_le_add le_rfl hreal_norm
    _ < 4 * σ + (σ + σ) := add_lt_add_of_lt_of_le hz ht
    _ < 8 * σ := by nlinarith

/-- The covariance ball selected by the one-chart scale lies inside the
holomorphy window. -/
theorem oneChartRecoveryScale_cov_ball_subset_half
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 128 * σ ≤ δ) :
    Metric.ball (0 : ComplexChartSpace m) (8 * σ) ⊆
      Metric.ball (0 : ComplexChartSpace m) (δ / 2) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  have hsmall : 8 * σ < δ / 2 := by nlinarith
  exact lt_trans hz hsmall

/-- The closed cutoff ball selected by the one-chart scale lies inside the
holomorphy window. -/
theorem oneChartRecoveryScale_cut_closedBall_subset_half
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 128 * σ ≤ δ) :
    Metric.closedBall (0 : ComplexChartSpace m) (16 * σ) ⊆
      Metric.ball (0 : ComplexChartSpace m) (δ / 2) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [Metric.mem_ball, dist_zero_right]
  have hsmall : 16 * σ < δ / 2 := by nlinarith
  exact lt_of_le_of_lt hz hsmall

/-- The imaginary part of the affine local EOW chart is the real-linear chart
part applied to the coordinate imaginary vector. -/
theorem localEOWChart_im_eq_realLinearPart_im
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : ComplexChartSpace m) :
    (fun i => (localEOWChart x0 ys w i).im) =
      localEOWRealLinearPart ys (fun j => (w j).im) := by
  ext i
  simp [localEOWChart_im, localEOWRealLinearPart]

/-- Strict positive chart imaginary coordinates map to the local side cone
through the real-linear part of the EOW chart. -/
theorem localEOWRealLinearPart_im_mem_sideCone_of_strictPositive
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R : ℝ} (hε : 0 < ε)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      localEOWSideCone ys ε := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have him_nonneg : ∀ j, 0 ≤ (w j).im := fun j => (hw.2 j).le
  have him_sum_pos : 0 < ∑ j, (w j).im :=
    Finset.sum_pos (fun j _ => hw.2 j) Finset.univ_nonempty
  exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
    him_nonneg him_sum_pos

/-- Strict negative chart imaginary coordinates map to the negative image of
the local side cone. -/
theorem localEOWRealLinearPart_im_mem_neg_sideCone_of_strictNegative
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R : ℝ} (hε : 0 < ε)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      Neg.neg '' localEOWSideCone ys ε := by
  let v : Fin m → ℝ := fun j => - (w j).im
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => by
    dsimp [v]
    exact (neg_pos.mpr (hw.2 j)).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    exact Finset.sum_pos (fun j _ => neg_pos.mpr (hw.2 j))
      Finset.univ_nonempty
  refine ⟨localEOWRealLinearPart ys v,
    localEOWRealLinearPart_mem_localEOWSideCone ys hε hv_nonneg
      hv_sum_pos, ?_⟩
  have hv_eq : v = -(fun j : Fin m => (w j).im) := by
    ext j
    rfl
  calc
    -localEOWRealLinearPart ys v =
        -localEOWRealLinearPart ys (-(fun j : Fin m => (w j).im)) := by
          rw [hv_eq]
    _ = localEOWRealLinearPart ys (fun j : Fin m => (w j).im) := by
          rw [localEOWRealLinearPart_neg]
          simp

/-- A strict positive chart-side ball small enough in coordinates maps into a
truncated local side cone. -/
theorem localEOWRealLinearPart_im_mem_truncatedSideCone_of_strictPositive
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      localEOWSideCone ys ε ∩ Metric.ball 0 rside := by
  constructor
  · exact localEOWRealLinearPart_im_mem_sideCone_of_strictPositive
      hm ys hε hw
  · rw [Metric.mem_ball, dist_zero_right]
    exact hδside (fun j => (w j).im)
      (lt_of_lt_of_le (norm_complexChart_im_lt_of_mem_ball hw.1) hRδ)

/-- A strict negative chart-side ball small enough in coordinates maps into the
negative image of a truncated local side cone. -/
theorem localEOWRealLinearPart_im_mem_neg_truncatedSideCone_of_strictNegative
    (hm : 0 < m)
    (ys : Fin m → Fin m → ℝ) {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWRealLinearPart ys (fun j => (w j).im) ∈
      Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
  let v : Fin m → ℝ := fun j => - (w j).im
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => by
    dsimp [v]
    exact (neg_pos.mpr (hw.2 j)).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    exact Finset.sum_pos (fun j _ => neg_pos.mpr (hw.2 j))
      Finset.univ_nonempty
  have hv_norm_lt : ‖v‖ < δside := by
    have him_lt : ‖(fun j : Fin m => (w j).im)‖ < R :=
      norm_complexChart_im_lt_of_mem_ball hw.1
    calc
      ‖v‖ = ‖(fun j : Fin m => (w j).im)‖ := by
        dsimp [v]
        rw [show (fun j : Fin m => -(w j).im) =
            -(fun j : Fin m => (w j).im) by
          ext j
          rfl]
        exact norm_neg (fun j : Fin m => (w j).im)
      _ < δside := lt_of_lt_of_le him_lt hRδ
  refine ⟨localEOWRealLinearPart ys v, ?_, ?_⟩
  · constructor
    · exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
        hv_nonneg hv_sum_pos
    · rw [Metric.mem_ball, dist_zero_right]
      exact hδside v hv_norm_lt
  · have hv_eq : v = -(fun j : Fin m => (w j).im) := by
      ext j
      rfl
    calc
      -localEOWRealLinearPart ys v =
          -localEOWRealLinearPart ys (-(fun j : Fin m => (w j).im)) := by
            rw [hv_eq]
      _ = localEOWRealLinearPart ys (fun j : Fin m => (w j).im) := by
            rw [localEOWRealLinearPart_neg]
            simp

/-- The local EOW chart sends a small strict positive coordinate side ball into
the tube over the truncated original side cone. -/
theorem localEOWChart_mem_TubeDomain_truncatedSideCone_of_strictPositive
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWChart x0 ys w ∈
      TubeDomain (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
  change (fun i => (localEOWChart x0 ys w i).im) ∈
    localEOWSideCone ys ε ∩ Metric.ball 0 rside
  rw [localEOWChart_im_eq_realLinearPart_im]
  exact localEOWRealLinearPart_im_mem_truncatedSideCone_of_strictPositive
    hm ys hε hδside hRδ hw

/-- The local EOW chart sends a small strict negative coordinate side ball into
the tube over the negative truncated original side cone. -/
theorem localEOWChart_mem_TubeDomain_neg_truncatedSideCone_of_strictNegative
    (hm : 0 < m)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ε R rside δside : ℝ}
    (hε : 0 < ε)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hRδ : R ≤ δside)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWChart x0 ys w ∈
      TubeDomain (Neg.neg '' (localEOWSideCone ys ε ∩
        Metric.ball 0 rside)) := by
  change (fun i => (localEOWChart x0 ys w i).im) ∈
    Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside)
  rw [localEOWChart_im_eq_realLinearPart_im]
  exact localEOWRealLinearPart_im_mem_neg_truncatedSideCone_of_strictNegative
    hm ys hε hδside hRδ hw

/-- Strict positive chart-side balls feed the fixed-window plus polywedge
membership theorem once their radius has the required real and coordinate-sum
smallness. -/
theorem localEOWChart_mem_fixedWindow_of_strictPositiveImagBall
    (hm : 0 < m)
    (Ωplus : Set (ComplexChartSpace m))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ r R : ℝ} (hRρ : R ≤ ρ)
    (hcardR : (Fintype.card (Fin m) : ℝ) * R < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictPositiveImagBall (m := m) R) :
    localEOWChart x0 ys w ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (w j).re
  let v : Fin m → ℝ := fun j => (w j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hw.1
    calc
      ‖u‖ ≤ ‖w‖ := by
        simpa [u] using norm_complexChart_re_le w
      _ ≤ R := hnorm.le
      _ ≤ ρ := hRρ
  have hv_nonneg : ∀ j, 0 ≤ v j := by
    intro j
    exact StrictPositiveImagBall_im_nonneg hw j
  have hv_sum_pos : 0 < ∑ j, v j := by
    simpa [v] using StrictPositiveImagBall_im_sum_pos hm hw
  have hv_sum_lt : (∑ j, v j) < r := by
    exact lt_of_le_of_lt
      (by
        simpa [v] using
          StrictPositiveImagBall_im_sum_le_card_mul (m := m) hw)
      hcardR
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = w := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- Strict negative chart-side balls feed the fixed-window minus polywedge
membership theorem once their radius has the required real and coordinate-sum
smallness. -/
theorem localEOWChart_mem_fixedWindow_of_strictNegativeImagBall
    (hm : 0 < m)
    (Ωminus : Set (ComplexChartSpace m))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ r R : ℝ} (hRρ : R ≤ ρ)
    (hcardR : (Fintype.card (Fin m) : ℝ) * R < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : ComplexChartSpace m}
    (hw : w ∈ StrictNegativeImagBall (m := m) R) :
    localEOWChart x0 ys w ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (w j).re
  let v : Fin m → ℝ := fun j => (w j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hw.1
    calc
      ‖u‖ ≤ ‖w‖ := by
        simpa [u] using norm_complexChart_re_le w
      _ ≤ R := hnorm.le
      _ ≤ ρ := hRρ
  have hv_nonpos : ∀ j, v j ≤ 0 := by
    intro j
    exact StrictNegativeImagBall_im_nonpos hw j
  have hv_sum_pos : 0 < ∑ j, -v j := by
    simpa [v] using StrictNegativeImagBall_neg_im_sum_pos hm hw
  have hv_sum_lt : (∑ j, -v j) < r := by
    exact lt_of_le_of_lt
      (by
        simpa [v] using
          StrictNegativeImagBall_neg_im_sum_le_card_mul (m := m) hw)
      hcardR
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = w := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- Original chart points whose inverse affine chart has small real part.  This
is the real-window factor in the local side domains used by the one-chart
distributional EOW proof. -/
def localEOWAffineRealWindow
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) (R : ℝ) :
    Set (ComplexChartSpace m) :=
  {z | ‖(fun j : Fin m =>
    (((localEOWComplexAffineEquiv x0 ys hli).symm z) j).re)‖ < R}

theorem isOpen_localEOWAffineRealWindow
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) (R : ℝ) :
    IsOpen (localEOWAffineRealWindow x0 ys hli R) := by
  let A := localEOWComplexAffineEquiv x0 ys hli
  have hreal :
      Continuous fun z : ComplexChartSpace m =>
        fun j : Fin m => ((A.symm z) j).re := by
    refine continuous_pi ?_
    intro j
    exact Complex.continuous_re.comp
      ((continuous_apply j).comp A.symm.continuous)
  have hnorm : Continuous fun z : ComplexChartSpace m =>
      ‖(fun j : Fin m => ((A.symm z) j).re)‖ :=
    continuous_norm.comp hreal
  simpa [localEOWAffineRealWindow, A] using
    isOpen_lt hnorm continuous_const

theorem localEOWComplexAffineEquiv_symm_localEOWChart
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) (w : ComplexChartSpace m) :
    (localEOWComplexAffineEquiv x0 ys hli).symm
        (localEOWChart x0 ys w) = w := by
  simpa [localEOWComplexAffineEquiv_apply] using
    (localEOWComplexAffineEquiv x0 ys hli).symm_apply_apply w

/-- A chart point whose coordinate real part is small lies in the corresponding
original affine real window after applying the local EOW chart. -/
theorem localEOWChart_mem_affineRealWindow_of_re_norm_lt
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) {R : ℝ}
    {w : ComplexChartSpace m}
    (hw_re : ‖(fun j : Fin m => (w j).re)‖ < R) :
    localEOWChart x0 ys w ∈ localEOWAffineRealWindow x0 ys hli R := by
  dsimp [localEOWAffineRealWindow]
  simpa [localEOWComplexAffineEquiv_symm_localEOWChart x0 ys hli w]
    using hw_re

theorem localEOWChart_mem_affineRealWindow_of_mem_ball
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) {R : ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ Metric.ball 0 R) :
    localEOWChart x0 ys w ∈ localEOWAffineRealWindow x0 ys hli R :=
  localEOWChart_mem_affineRealWindow_of_re_norm_lt x0 ys hli
    (norm_complexChart_re_lt_of_mem_ball hw)

/-- Adding a small original real displacement moves the inverse-chart real
window from radius `2 * ρ` to radius `3 * ρ`. -/
theorem localEOWAffineRealWindow_add_realEmbed
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) {ρ : ℝ}
    {z : ComplexChartSpace m}
    (hz : z ∈ localEOWAffineRealWindow x0 ys hli (2 * ρ))
    {t : Fin m → ℝ}
    (ht : ‖(localEOWRealLinearCLE ys hli).symm t‖ < ρ) :
    z + realEmbed t ∈ localEOWAffineRealWindow x0 ys hli (3 * ρ) := by
  let A := localEOWComplexAffineEquiv x0 ys hli
  let e := localEOWRealLinearCLE ys hli
  let u : Fin m → ℝ := fun j => ((A.symm z) j).re
  let v : Fin m → ℝ := e.symm t
  have hsymm :
      A.symm (z + realEmbed t) = A.symm z + realEmbed (e.symm t) := by
    simpa [A, e] using
      localEOWComplexAffineEquiv_symm_add_realEmbed x0 ys hli z t
  have hreal :
      (fun j : Fin m => ((A.symm (z + realEmbed t)) j).re) = u + v := by
    rw [hsymm]
    ext j
    simp [u, v, realEmbed]
  have hu : ‖u‖ < 2 * ρ := by
    simpa [localEOWAffineRealWindow, A, u] using hz
  have hv : ‖v‖ < ρ := by
    simpa [v, e] using ht
  dsimp [localEOWAffineRealWindow]
  calc
    ‖(fun j : Fin m => ((A.symm (z + realEmbed t)) j).re)‖ =
        ‖u + v‖ := by rw [hreal]
    _ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
    _ < 2 * ρ + ρ := add_lt_add hu hv
    _ = 3 * ρ := by ring

end SCV
