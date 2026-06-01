import OSReconstruction.SCV.VladimirovTillmann

/-!
# Tube-Domain Boundary Values from Polynomial Growth

This file isolates the pure several-complex-variables boundary-value theorem
needed by the OS reconstruction boundary-values layer.

The theorem surface is intentionally QFT-free: it is stated for a holomorphic
function on a tube domain over an open convex salient cone, with a global
polynomial-growth bound, and concludes existence of a continuous Schwartz
boundary-value functional obtained as a raywise limit.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

private theorem tube_slice_mem_of_cone
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → Fin (d + 1) → ℝ) :
    (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) ∈ TubeDomainSetPi C := by
  have hy : ε • η ∈ C := hC_cone η hη ε hε
  change (fun k μ =>
    (((x k μ : ℂ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I).im)) ∈ C
  simpa [Pi.smul_apply, mul_assoc]
    using hy

private theorem continuous_tubeSlice_of_holomorphic
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : Fin n → Fin (d + 1) → ℝ =>
      F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)) := by
  have harg_cont :
      Continuous (fun x : Fin n → Fin (d + 1) → ℝ =>
        fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  have hcomp :
      ContinuousOn
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I))
        Set.univ := by
    refine hF_hol.continuousOn.comp harg_cont.continuousOn ?_
    intro x hx
    exact tube_slice_mem_of_cone C hC_cone η hη ε hε x
  simpa using hcomp

private theorem tubeSlice_polyGrowth_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C_slice : ℝ, 0 < C_slice ∧
      ∀ x : Fin n → Fin (d + 1) → ℝ,
        ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤
          C_slice * (1 + ‖x‖) ^ N := by
  refine ⟨C_bd * (1 + ‖ε • η‖) ^ N, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro x
  let z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I
  have hz : z ∈ TubeDomainSetPi C :=
    tube_slice_mem_of_cone C hC_cone η hη ε hε x
  have hgrow := hF_growth z hz
  have hnorm :
      ‖z‖ ≤ ‖x‖ + ‖ε • η‖ := by
    change
      ‖(fun k μ => (x k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤
        ‖x‖ + ‖ε • η‖
    have hxC :
        ‖(fun k μ => (x k μ : ℂ))‖ ≤ ‖x‖ := by
      change ‖(fun k : Fin n => fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ))‖ ≤ ‖x‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin n => fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ)))
        (r := ‖x‖)
        (show 0 ≤ ‖x‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hxCk : ‖fun μ => ((x k μ : ℝ) : ℂ)‖ ≤ ‖x k‖ := by
        change ‖(fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ))‖ ≤ ‖x k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ)))
          (r := ‖x k‖)
          (show 0 ≤ ‖x k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖((x k μ : ℝ) : ℂ)‖ = ‖x k μ‖ := by simp
          _ ≤ ‖x k‖ := norm_le_pi_norm (f := x k) μ
      exact le_trans hxCk (norm_le_pi_norm (f := x) k)
    have hyI :
        ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ ≤ ‖ε • η‖ := by
      change
        ‖(fun k : Fin n => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖ε • η‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin n => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
        (r := ‖ε • η‖)
        (show 0 ≤ ‖ε • η‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hyIk : ‖fun μ => (((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤ ‖(ε • η) k‖ := by
        change
          ‖(fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖(ε • η) k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
          (r := ‖(ε • η) k‖)
          (show 0 ≤ ‖(ε • η) k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖(((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ = ‖ε * η k μ‖ := by simp
          _ = ‖(ε • η) k μ‖ := by simp [Pi.smul_apply]
          _ ≤ ‖(ε • η) k‖ := norm_le_pi_norm (f := (ε • η) k) μ
      exact le_trans hyIk (norm_le_pi_norm (f := ε • η) k)
    calc
      ‖(fun k μ => (x k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖fun k μ => (x k μ : ℂ)‖ + ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ ≤ ‖x‖ + ‖ε • η‖ := add_le_add hxC hyI
  have hone :
      1 + ‖z‖ ≤ (1 + ‖ε • η‖) * (1 + ‖x‖) := by
    have htmp : 1 + ‖z‖ ≤ 1 + (‖x‖ + ‖ε • η‖) := by
      linarith [hnorm]
    have hprod : 1 + (‖x‖ + ‖ε • η‖) ≤ (1 + ‖ε • η‖) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg x, norm_nonneg (ε • η)]
    exact le_trans htmp hprod
  calc
    ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N := hgrow
    _ ≤ C_bd * ((1 + ‖ε • η‖) * (1 + ‖x‖)) ^ N := by
      gcongr
    _ = (C_bd * (1 + ‖ε • η‖) ^ N) * (1 + ‖x‖) ^ N := by
      rw [mul_pow]
      ring

private theorem tubeSlice_uniformPolyGrowth_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C) :
    ∃ C_slice : ℝ, 0 < C_slice ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ x : Fin n → Fin (d + 1) → ℝ,
        ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤
          C_slice * (1 + ‖x‖) ^ N := by
  refine ⟨C_bd * (1 + ‖η‖) ^ N, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro ε hε hε_lt x
  let z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I
  have hz : z ∈ TubeDomainSetPi C :=
    tube_slice_mem_of_cone C hC_cone η hη ε hε x
  have hgrow := hF_growth z hz
  have hnorm :
      ‖z‖ ≤ ‖x‖ + ‖ε • η‖ := by
    change
      ‖(fun k μ => (x k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤
        ‖x‖ + ‖ε • η‖
    have hxC :
        ‖(fun k μ => (x k μ : ℂ))‖ ≤ ‖x‖ := by
      change ‖(fun k : Fin n => fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ))‖ ≤ ‖x‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin n => fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ)))
        (r := ‖x‖)
        (show 0 ≤ ‖x‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hxCk : ‖fun μ => ((x k μ : ℝ) : ℂ)‖ ≤ ‖x k‖ := by
        change ‖(fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ))‖ ≤ ‖x k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) => ((x k μ : ℝ) : ℂ)))
          (r := ‖x k‖)
          (show 0 ≤ ‖x k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖((x k μ : ℝ) : ℂ)‖ = ‖x k μ‖ := by simp
          _ ≤ ‖x k‖ := norm_le_pi_norm (f := x k) μ
      exact le_trans hxCk (norm_le_pi_norm (f := x) k)
    have hyI :
        ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ ≤ ‖ε • η‖ := by
      change
        ‖(fun k : Fin n => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖ε • η‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin n => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
        (r := ‖ε • η‖)
        (show 0 ≤ ‖ε • η‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hyIk : ‖fun μ => (((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤ ‖(ε • η) k‖ := by
        change
          ‖(fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖(ε • η) k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
          (r := ‖(ε • η) k‖)
          (show 0 ≤ ‖(ε • η) k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖(((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ = ‖ε * η k μ‖ := by simp
          _ = ‖(ε • η) k μ‖ := by simp [Pi.smul_apply]
          _ ≤ ‖(ε • η) k‖ := norm_le_pi_norm (f := (ε • η) k) μ
      exact le_trans hyIk (norm_le_pi_norm (f := ε • η) k)
    calc
      ‖(fun k μ => (x k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖fun k μ => (x k μ : ℂ)‖ + ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ ≤ ‖x‖ + ‖ε • η‖ := add_le_add hxC hyI
  have hone :
      1 + ‖z‖ ≤ (1 + ‖ε • η‖) * (1 + ‖x‖) := by
    have htmp : 1 + ‖z‖ ≤ 1 + (‖x‖ + ‖ε • η‖) := by
      linarith [hnorm]
    have hprod : 1 + (‖x‖ + ‖ε • η‖) ≤ (1 + ‖ε • η‖) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg x, norm_nonneg (ε • η)]
    exact le_trans htmp hprod
  have hε_norm_le_one : ‖ε‖ ≤ (1 : ℝ) := by
    rw [Real.norm_of_nonneg (le_of_lt hε)]
    linarith
  have hεη_norm_le : ‖ε • η‖ ≤ ‖η‖ := by
    calc
      ‖ε • η‖ = ‖ε‖ * ‖η‖ := norm_smul ε η
      _ ≤ 1 * ‖η‖ := by
        gcongr
      _ = ‖η‖ := by ring
  have hscale_le :
      (1 + ‖ε • η‖) * (1 + ‖x‖) ≤ (1 + ‖η‖) * (1 + ‖x‖) := by
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  calc
    ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N := hgrow
    _ ≤ C_bd * ((1 + ‖ε • η‖) * (1 + ‖x‖)) ^ N := by
      gcongr
    _ ≤ C_bd * ((1 + ‖η‖) * (1 + ‖x‖)) ^ N := by
      apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
      exact pow_le_pow_left₀ (by positivity) hscale_le N
    _ = (C_bd * (1 + ‖η‖) ^ N) * (1 + ‖x‖) ^ N := by
      rw [mul_pow]
      ring

private theorem exists_tubeSlice_integral_clm_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
      ∀ φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
        T φ = ∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x := by
  let K : (Fin n → Fin (d + 1) → ℝ) → ℂ :=
    fun x => F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)
  have hK_cont : Continuous K :=
    continuous_tubeSlice_of_holomorphic C hC_cone hF_hol η hη ε hε
  obtain ⟨C_slice, hC_slice_pos, hK_bound⟩ :=
    tubeSlice_polyGrowth_of_polyGrowth C hC_cone C_bd N hC hF_growth η hη ε hε
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume :
        MeasureTheory.Measure (Fin n → Fin (d + 1) → ℝ)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have hKφ_int :
      ∀ φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
        MeasureTheory.Integrable (fun x => K x * φ x) MeasureTheory.volume := by
    intro φ
    set D_fin : ℕ := Module.finrank ℝ (Fin n → Fin (d + 1) → ℝ)
    set M : ℕ := N + D_fin + 1
    have hD_lt : (D_fin : ℝ) < ↑(D_fin + 1) := by
      push_cast
      linarith
    have hI_int : MeasureTheory.Integrable
        (fun x : Fin n → Fin (d + 1) → ℝ => (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)))
        MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    set sem := (Finset.Iic (M, 0)).sup
      (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ) φ
    have hsem_bound :
        ∀ x : Fin n → Fin (d + 1) → ℝ,
          (1 + ‖x‖) ^ M * ‖φ x‖ ≤ 2 ^ M * sem := by
      intro x
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
        (le_refl M) (le_refl 0) φ x
      rwa [norm_iteratedFDeriv_zero] at h
    have hpointwise : ∀ x : Fin n → Fin (d + 1) → ℝ,
        ‖K x * φ x‖ ≤
          C_slice * 2 ^ M * sem * (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)) := by
      intro x
      have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by
        linarith [norm_nonneg x]
      have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D_fin + 1) := pow_pos h1x_pos _
      rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast, norm_mul]
      have step1 : ‖K x‖ * ‖φ x‖ ≤ C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ :=
        mul_le_mul_of_nonneg_right (hK_bound x) (norm_nonneg _)
      have step2 : (1 + ‖x‖) ^ N * ‖φ x‖ ≤
          2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by
        rw [le_mul_inv_iff₀ h1xD1_pos]
        have hM : N + (D_fin + 1) = M := by
          omega
        calc
          (1 + ‖x‖) ^ N * ‖φ x‖ * (1 + ‖x‖) ^ (D_fin + 1)
              = (1 + ‖x‖) ^ (N + (D_fin + 1)) * ‖φ x‖ := by
                rw [pow_add]
                ring
          _ = (1 + ‖x‖) ^ M * ‖φ x‖ := by rw [hM]
          _ ≤ 2 ^ M * sem := hsem_bound x
      calc
        ‖K x‖ * ‖φ x‖ ≤ C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ := step1
        _ = C_slice * ((1 + ‖x‖) ^ N * ‖φ x‖) := by ring
        _ ≤ C_slice * (2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left step2 (le_of_lt hC_slice_pos)
        _ = C_slice * 2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by ring
    refine hI_int.const_mul (C_slice * 2 ^ M * sem) |>.mono' ?_ ?_
    · exact hK_cont.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hpointwise
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (fun φ => ∫ x, K x * φ x) ?_ ?_ ?_,
    fun φ => rfl⟩
  · intro φ ψ
    simp only [SchwartzMap.add_apply, mul_add]
    exact MeasureTheory.integral_add (hKφ_int φ) (hKφ_int ψ)
  · intro a φ
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : Fin n → Fin (d + 1) → ℝ, K x * (a * φ x) = a * (K x * φ x) from
      fun x => by ring]
    exact MeasureTheory.integral_const_mul a _
  · set D_fin : ℕ := Module.finrank ℝ (Fin n → Fin (d + 1) → ℝ)
    set M : ℕ := N + D_fin + 1
    have hD_lt : (D_fin : ℝ) < ↑(D_fin + 1) := by
      push_cast
      linarith
    set I_D : ℝ :=
      ∫ x : Fin n → Fin (d + 1) → ℝ, (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ))
    set C_sem : ℝ := C_slice * 2 ^ M * I_D
    refine ⟨Finset.Iic (M, 0), C_sem, ?_, ?_⟩
    · apply mul_nonneg (mul_nonneg (le_of_lt hC_slice_pos) (by positivity))
      apply MeasureTheory.integral_nonneg
      intro x
      apply Real.rpow_nonneg
      linarith [norm_nonneg x]
    · intro φ
      set sem := (Finset.Iic (M, 0)).sup
        (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ) φ
      have hsem_bound :
          ∀ x : Fin n → Fin (d + 1) → ℝ,
            (1 + ‖x‖) ^ M * ‖φ x‖ ≤ 2 ^ M * sem := by
        intro x
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
          (le_refl M) (le_refl 0) φ x
        rwa [norm_iteratedFDeriv_zero] at h
      have hpointwise : ∀ᵐ x : Fin n → Fin (d + 1) → ℝ ∂MeasureTheory.volume,
          ‖K x * φ x‖ ≤
            C_slice * 2 ^ M * sem * (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)) := by
        filter_upwards with x
        have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by
          linarith [norm_nonneg x]
        have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D_fin + 1) := pow_pos h1x_pos _
        rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast, norm_mul]
        have step1 : ‖K x‖ * ‖φ x‖ ≤ C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ :=
          mul_le_mul_of_nonneg_right (hK_bound x) (norm_nonneg _)
        have step2 : (1 + ‖x‖) ^ N * ‖φ x‖ ≤
            2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ h1xD1_pos]
          have hM : N + (D_fin + 1) = M := by
            omega
          calc
            (1 + ‖x‖) ^ N * ‖φ x‖ * (1 + ‖x‖) ^ (D_fin + 1)
                = (1 + ‖x‖) ^ (N + (D_fin + 1)) * ‖φ x‖ := by
                  rw [pow_add]
                  ring
            _ = (1 + ‖x‖) ^ M * ‖φ x‖ := by rw [hM]
            _ ≤ 2 ^ M * sem := hsem_bound x
        calc
          ‖K x‖ * ‖φ x‖ ≤ C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ := step1
          _ = C_slice * ((1 + ‖x‖) ^ N * ‖φ x‖) := by ring
          _ ≤ C_slice * (2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹) :=
            mul_le_mul_of_nonneg_left step2 (le_of_lt hC_slice_pos)
          _ = C_slice * 2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by ring
      calc
        ‖∫ x : Fin n → Fin (d + 1) → ℝ, K x * φ x‖
            ≤ ∫ x : Fin n → Fin (d + 1) → ℝ, ‖K x * φ x‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x : Fin n → Fin (d + 1) → ℝ,
            C_slice * 2 ^ M * sem * (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)) :=
              MeasureTheory.integral_mono_ae
                (hKφ_int φ).norm
                ((integrable_one_add_norm hD_lt).const_mul (C_slice * 2 ^ M * sem))
                hpointwise
        _ = C_slice * 2 ^ M * sem * I_D := by
              rw [MeasureTheory.integral_const_mul]
        _ = C_sem * sem := by
              ring
        _ = C_sem * (Finset.Iic (M, 0)).sup
              (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ) φ := by
              simp [sem]

private noncomputable def tubeSliceIntegralCLM_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  Classical.choose <|
    exists_tubeSlice_integral_clm_of_polyGrowth C hC_cone hF_hol
      C_bd N hC hF_growth η hη ε hε

private theorem tubeSliceIntegralCLM_of_polyGrowth_apply
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε)
    (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ) :
    tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth η hη ε hε φ =
      ∫ x : Fin n → Fin (d + 1) → ℝ,
        F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x :=
  (Classical.choose_spec <|
    exists_tubeSlice_integral_clm_of_polyGrowth C hC_cone hF_hol
      C_bd N hC hF_growth η hη ε hε) φ

private theorem tubeSliceIntegralCLM_uniformSeminormBound_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C) :
    ∃ s : Finset (ℕ × ℕ), ∃ C_sem : ℝ, 0 ≤ C_sem ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε_lt : ε < 1,
      ∀ φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
        ‖tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth η hη ε hε φ‖
          ≤ C_sem * (s.sup (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ)) φ := by
  obtain ⟨C_slice, hC_slice_pos, hK_bound⟩ :=
    tubeSlice_uniformPolyGrowth_of_polyGrowth C hC_cone C_bd N hC hF_growth η hη
  set D_fin : ℕ := Module.finrank ℝ (Fin n → Fin (d + 1) → ℝ)
  set M : ℕ := N + D_fin + 1
  have hD_lt : (D_fin : ℝ) < ↑(D_fin + 1) := by
    push_cast
    linarith
  set I_D : ℝ :=
    ∫ x : Fin n → Fin (d + 1) → ℝ, (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ))
  set C_sem : ℝ := C_slice * 2 ^ M * I_D
  refine ⟨Finset.Iic (M, 0), C_sem, ?_, ?_⟩
  · apply mul_nonneg (mul_nonneg (le_of_lt hC_slice_pos) (by positivity))
    apply MeasureTheory.integral_nonneg
    intro x
    apply Real.rpow_nonneg
    linarith [norm_nonneg x]
  · intro ε hε hε_lt φ
    set sem := (Finset.Iic (M, 0)).sup
      (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ) φ
    have hsem_bound :
        ∀ x : Fin n → Fin (d + 1) → ℝ,
          (1 + ‖x‖) ^ M * ‖φ x‖ ≤ 2 ^ M * sem := by
      intro x
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
        (le_refl M) (le_refl 0) φ x
      rwa [norm_iteratedFDeriv_zero] at h
    have hpointwise : ∀ᵐ x : Fin n → Fin (d + 1) → ℝ ∂MeasureTheory.volume,
        ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x‖ ≤
          C_slice * 2 ^ M * sem * (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)) := by
      filter_upwards with x
      have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by
        linarith [norm_nonneg x]
      have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D_fin + 1) := pow_pos h1x_pos _
      rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast, norm_mul]
      have step1 :
          ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ * ‖φ x‖ ≤
            C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ :=
        mul_le_mul_of_nonneg_right (hK_bound ε hε hε_lt x) (norm_nonneg _)
      have step2 : (1 + ‖x‖) ^ N * ‖φ x‖ ≤
          2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by
        rw [le_mul_inv_iff₀ h1xD1_pos]
        have hM : N + (D_fin + 1) = M := by
          omega
        calc
          (1 + ‖x‖) ^ N * ‖φ x‖ * (1 + ‖x‖) ^ (D_fin + 1)
              = (1 + ‖x‖) ^ (N + (D_fin + 1)) * ‖φ x‖ := by
                rw [pow_add]
                ring
          _ = (1 + ‖x‖) ^ M * ‖φ x‖ := by rw [hM]
          _ ≤ 2 ^ M * sem := hsem_bound x
      calc
        ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ * ‖φ x‖
            ≤ C_slice * (1 + ‖x‖) ^ N * ‖φ x‖ := step1
        _ = C_slice * ((1 + ‖x‖) ^ N * ‖φ x‖) := by ring
        _ ≤ C_slice * (2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left step2 (le_of_lt hC_slice_pos)
        _ = C_slice * 2 ^ M * sem * ((1 + ‖x‖) ^ (D_fin + 1))⁻¹ := by ring
    have hInt_kernel :
        MeasureTheory.Integrable
          (fun x : Fin n → Fin (d + 1) → ℝ =>
            F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x)
          MeasureTheory.volume := by
      have h_cont :
          Continuous
            (fun x : Fin n → Fin (d + 1) → ℝ =>
              F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I)) :=
        continuous_tubeSlice_of_holomorphic C hC_cone hF_hol η hη ε hε
      refine ((integrable_one_add_norm hD_lt).const_mul (C_slice * 2 ^ M * sem)).mono' ?_ ?_
      · exact h_cont.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable
      · exact hpointwise
    calc
      ‖tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth η hη ε hε φ‖
          = ‖∫ x : Fin n → Fin (d + 1) → ℝ,
              F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x‖ := by
                rw [tubeSliceIntegralCLM_of_polyGrowth_apply]
      _ ≤ ∫ x : Fin n → Fin (d + 1) → ℝ,
            ‖F (fun k μ => ↑(x k μ) + ((ε * η k μ : ℝ) : ℂ) * Complex.I) * φ x‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ x : Fin n → Fin (d + 1) → ℝ,
            C_slice * 2 ^ M * sem * (1 + ‖x‖) ^ (-(↑(D_fin + 1) : ℝ)) :=
          MeasureTheory.integral_mono_ae
            hInt_kernel.norm
            ((integrable_one_add_norm hD_lt).const_mul (C_slice * 2 ^ M * sem))
            hpointwise
      _ = C_slice * 2 ^ M * sem * I_D := by
            rw [MeasureTheory.integral_const_mul]
      _ = C_sem * sem := by
            ring
      _ = C_sem * (Finset.Iic (M, 0)).sup
            (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ) φ := by
            simp [sem]

private theorem tube_boundaryValueData_of_polyGrowth_of_denseSubset
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (U : Set (SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ))
    (hU_dense : Dense U)
    (hU_bv : ∀ φ, φ ∈ U → ∀ η : Fin n → Fin (d + 1) → ℝ, η ∈ C →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W φ))) :
    ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
      (η : Fin n → Fin (d + 1) → ℝ),
      η ∈ C →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W φ)) := by
  intro φ η hη
  obtain ⟨s, C_sem, hC_sem_nonneg, hT_bound⟩ :=
    tubeSliceIntegralCLM_uniformSeminormBound_of_polyGrowth
      C hC_cone hF_hol C_bd N hC hF_growth η hη
  let p : Seminorm ℂ (SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ) :=
    s.sup (schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ)
  have hp_cont : Continuous p := by
    refine Seminorm.continuous_of_le ?_
      (show p ≤ ∑ i ∈ s, schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ i by
        simpa [p] using
          Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ
            (Fin n → Fin (d + 1) → ℝ) ℂ) s)
    change Continuous (fun x =>
      Seminorm.coeFnAddMonoidHom ℂ
        (SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (∑ i ∈ s, schwartzSeminormFamily ℂ (Fin n → Fin (d + 1) → ℝ) ℂ i) x)
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      (schwartz_withSeminorms ℂ (Fin n → Fin (d + 1) → ℝ) ℂ).continuous_seminorm i
  have hφ_closure : φ ∈ closure (U : Set (SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)) :=
    hU_dense φ
  rw [mem_closure_iff_seq_limit] at hφ_closure
  obtain ⟨u, hu_mem, hu_tendsto⟩ := hφ_closure
  have hp_small :
      Filter.Tendsto (fun m : ℕ => p (u m - φ)) Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun m : ℕ => u m - φ) Filter.atTop
        (nhds (0 : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)) := by
      simpa using (hu_tendsto.sub tendsto_const_nhds :
        Filter.Tendsto (fun m : ℕ => u m - φ) Filter.atTop (nhds (φ - φ)))
    simpa using (hp_cont.tendsto 0).comp hsub
  have hW_tendsto :
      Filter.Tendsto (fun m : ℕ => W (u m)) Filter.atTop (nhds (W φ)) :=
    W.continuous.tendsto φ |>.comp hu_tendsto
  refine Metric.tendsto_nhds.mpr ?_
  intro εtol hεtol
  let A : ℝ := max C_sem 1
  have hA_pos : 0 < A := by
    dsimp [A]
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hp_small (εtol / (3 * A)) (by
    exact div_pos hεtol (by positivity))
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hW_tendsto (εtol / 3) (by positivity)
  let M := max N₁ N₂
  have huM_small : p (u M - φ) < εtol / (3 * A) := by
    have hdist := hN₁ M (le_max_left _ _)
    have hp_nonneg : 0 ≤ p (u M - φ) := apply_nonneg p _
    simpa [Real.dist_eq, abs_of_nonneg hp_nonneg] using hdist
  have hWM_small : dist (W (u M)) (W φ) < εtol / 3 := hN₂ M (le_max_right _ _)
  have hconv_uM := hU_bv (u M) (hu_mem M) η hη
  have hconv_uM' :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
          (W (u M)) < εtol / 3 := by
    have hconv_metric := (Metric.tendsto_nhds.mp hconv_uM) (εtol / 3) (by positivity)
    simpa using hconv_metric
  have hlt_one :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hlt_one, hconv_uM'] with ε hε_pos hε_lt hmid
  have hdiff_eq :
      dist
        (∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
        (∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
      =
        ‖tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth
            η hη ε hε_pos (φ - u M)‖ := by
    rw [dist_eq_norm]
    congr 1
    calc
      (∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
          -
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x
          =
          tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth
            η hη ε hε_pos φ
            -
          tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth
            η hη ε hε_pos (u M) := by
              rw [tubeSliceIntegralCLM_of_polyGrowth_apply,
                tubeSliceIntegralCLM_of_polyGrowth_apply]
              simp [mul_assoc]
      _ =
          tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth
            η hη ε hε_pos (φ - u M) := by
              rw [← map_sub]
  have hdiff_small :
      dist
        (∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
        (∫ x : Fin n → Fin (d + 1) → ℝ,
          F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
      < εtol / 3 := by
    rw [hdiff_eq]
    have hboundM :=
      hT_bound ε hε_pos hε_lt (φ - u M)
    have hp_symm : p (φ - u M) = p (u M - φ) := by
      rw [show φ - u M = -(u M - φ) by
        ext x
        simp]
      simpa using map_neg_eq_map p (u M - φ)
    calc
      ‖tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol C_bd N hC hF_growth
          η hη ε hε_pos (φ - u M)‖
        ≤ C_sem * p (φ - u M) := hboundM
      _ = C_sem * p (u M - φ) := by rw [hp_symm]
      _ ≤ A * p (u M - φ) := by
            gcongr
            dsimp [A]
            exact le_max_left _ _
      _ < A * (εtol / (3 * A)) := by
            gcongr
      _ = εtol / 3 := by
            field_simp [show A ≠ 0 by linarith]
  calc
    dist
      (∫ x : Fin n → Fin (d + 1) → ℝ,
        F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
      (W φ)
        ≤
        dist
          (∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
          (∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
        +
        dist
          (∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
          (W (u M))
        +
        dist (W (u M)) (W φ) := by
            nlinarith [dist_triangle
              (∫ x : Fin n → Fin (d + 1) → ℝ,
                F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
              (∫ x : Fin n → Fin (d + 1) → ℝ,
                F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
              (W φ),
              dist_triangle
                (∫ x : Fin n → Fin (d + 1) → ℝ,
                  F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * (u M) x)
                (W (u M)) (W φ)]
    _ < εtol := by
          nlinarith [hdiff_small, hmid, hWM_small]

/-- Pure tube-domain boundary-value existence from holomorphy and global
polynomial growth.

This is the reviewed pure SCV / functional-analytic theorem now used on the
active OS route: once a holomorphic function on `TubeDomainSetPi C` is known
to satisfy a global polynomial-growth bound, it admits a continuous
Schwartz boundary-value functional with raywise convergence.

The theorem is intentionally isolated at the SCV layer because it is a
Vladimirov-style boundary-value existence result, not a QFT-specific input. -/
axiom tube_boundaryValueData_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ))

/-- Moving-test boundary-value upgrade for a fixed already-selected boundary
functional.

This is the form to use when a surrounding development has already fixed the
boundary distribution (for example `bvt_W`).  The fixed-test convergence
identifies that selected `W`; the proof exposes the same private slice-CLM
family and Banach-Steinhaus step used in the tube-boundary-value construction,
so no new boundary functional is chosen. -/
theorem tube_boundaryValueData_moving_of_fixed
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_cone : IsCone C)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hW_fixed :
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)))
    (η : Fin n → Fin (d + 1) → ℝ) (hη : η ∈ C)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (εseq : α → ℝ)
    (hεseq : Filter.Tendsto εseq l (nhdsWithin 0 (Set.Ioi 0)))
    {φseq : α → SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ}
    {φ0 : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ}
    (hφseq : Filter.Tendsto φseq l (nhds φ0)) :
    Filter.Tendsto
      (fun a : α => ∫ x : Fin n → Fin (d + 1) → ℝ,
        F (fun k μ =>
          ↑(x k μ) + (εseq a : ℂ) * ↑(η k μ) * Complex.I) *
          φseq a x)
      l
      (nhds (W φ0)) := by
  classical
  let restrictCLMReal :
      (SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ) →
        SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ := fun L =>
    { toLinearMap :=
        { toFun := fun φ => L φ
          map_add' := by
            intro φ ψ
            exact L.map_add φ ψ
          map_smul' := by
            intro r φ
            simpa [Complex.real_smul] using L.map_smul (r : ℂ) φ }
      cont := L.continuous }
  let Tseq : ℝ →
      SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ := fun ε =>
    if hε : 0 < ε then
      restrictCLMReal
        (tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol
          C_bd N hC hF_growth η hη ε hε)
    else 0
  have hTseq_fixed :
      ∀ ψ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
        Filter.Tendsto (fun ε : ℝ => Tseq ε ψ)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (restrictCLMReal W ψ)) := by
    intro ψ
    refine Filter.Tendsto.congr' ?_ (hW_fixed ψ η hη)
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε_pos' : 0 < ε := hε_pos
    dsimp [Tseq]
    rw [dif_pos hε_pos']
    change
      (∫ x : Fin n → Fin (d + 1) → ℝ,
        F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * ψ x) =
      (tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol
        C_bd N hC hF_growth η hη ε hε_pos') ψ
    rw [tubeSliceIntegralCLM_of_polyGrowth_apply]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    norm_num [Complex.ofReal_mul]
  have hTseq_comp :
      ∀ ψ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
        Filter.Tendsto (fun a : α => Tseq (εseq a) ψ)
          l (nhds (restrictCLMReal W ψ)) := by
    intro ψ
    exact (hTseq_fixed ψ).comp hεseq
  have hmoving :
      Filter.Tendsto
        (fun a : α => Tseq (εseq a) (φseq a))
        l (nhds (restrictCLMReal W φ0)) :=
    SchwartzMap.tempered_apply_tendsto_of_tendsto_filter
      (T := fun a : α => Tseq (εseq a))
      (S := restrictCLMReal W) hTseq_comp hφseq
  refine Filter.Tendsto.congr' ?_ hmoving
  have hpos_event : ∀ᶠ a in l, 0 < εseq a :=
    hεseq.eventually self_mem_nhdsWithin
  filter_upwards [hpos_event] with a hε_pos
  dsimp [Tseq]
  rw [dif_pos hε_pos]
  change
    (tubeSliceIntegralCLM_of_polyGrowth C hC_cone hF_hol
      C_bd N hC hF_growth η hη (εseq a) hε_pos) (φseq a) =
    ∫ x : Fin n → Fin (d + 1) → ℝ,
      F (fun k μ =>
        ↑(x k μ) + (εseq a : ℂ) * ↑(η k μ) * Complex.I) *
        φseq a x
  rw [tubeSliceIntegralCLM_of_polyGrowth_apply]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  norm_num [Complex.ofReal_mul]

end SCV
