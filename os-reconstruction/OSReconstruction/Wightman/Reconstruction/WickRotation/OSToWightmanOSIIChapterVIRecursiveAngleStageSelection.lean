import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAngleExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius

/-!
# OS II Chapter VI: Quantitative recursive-angle stage selection

The Chapter V recursive sectors exhaust the product right half-plane.  For
the Chapter VI growth argument, qualitative exhaustion is not enough: the
chosen stage must be controlled in terms of the point's distance from the
angular boundary.  This file derives that quantitative selection from
`(5.28)` and converts the angular defect to the standard norm and
boundary-distance factors used in `(6.31)`.
-/

noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction

private theorem finUnivNonempty (k : ℕ) [NeZero k] :
    (Finset.univ : Finset (Fin k)).Nonempty := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let i : Fin k := ⟨0, hk⟩
  exact ⟨i, Finset.mem_univ i⟩

/-- Largest coordinate argument of a positive-arity time-gap vector. -/
noncomputable def osiiTimeMaxAbsArg
    (k : ℕ) [NeZero k] (ζ : Fin k → ℂ) : ℝ :=
  Finset.univ.sup' (finUnivNonempty k) (fun i => |Complex.arg (ζ i)|)

/-- Angular distance from the boundary of the product right half-plane. -/
def osiiTimeAngularDefect
    (k : ℕ) [NeZero k] (ζ : Fin k → ℂ) : ℝ :=
  Real.pi / 2 - osiiTimeMaxAbsArg k ζ

theorem abs_arg_le_osiiTimeMaxAbsArg
    {k : ℕ} [NeZero k] (ζ : Fin k → ℂ) (i : Fin k) :
    |Complex.arg (ζ i)| ≤ osiiTimeMaxAbsArg k ζ := by
  exact Finset.le_sup'
    (fun j : Fin k => |Complex.arg (ζ j)|) (Finset.mem_univ i)

theorem osiiTimeMaxAbsArg_lt_pi_div_two
    {k : ℕ} [NeZero k] {ζ : Fin k → ℂ}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    osiiTimeMaxAbsArg k ζ < Real.pi / 2 := by
  rw [osiiTimeMaxAbsArg, Finset.sup'_lt_iff]
  intro i _
  exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl (hζ i))

theorem osiiTimeAngularDefect_pos
    {k : ℕ} [NeZero k] {ζ : Fin k → ℂ}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    0 < osiiTimeAngularDefect k ζ := by
  exact sub_pos.2 (osiiTimeMaxAbsArg_lt_pi_div_two hζ)

private theorem norm_apply_le_pi_norm
    {k : ℕ} (ζ : Fin k → ℂ) (i : Fin k) :
    ‖ζ i‖ ≤ ‖ζ‖ := by
  rw [Pi.norm_def]
  exact_mod_cast
    Finset.le_sup (s := Finset.univ) (f := fun j : Fin k => ‖ζ j‖₊)
      (Finset.mem_univ i)

/-- The canonical Chapter VI radius, divided by the global norm, is no
larger than the angular defect. -/
theorem regularizationRadius_div_norm_le_angularDefect
    {k : ℕ} [NeZero k]
    (ζ : Fin k → ℂ)
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    osiiChapterVIRegularizationRadius k ζ / ‖ζ‖ ≤
      osiiTimeAngularDefect k ζ := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup' (finUnivNonempty k)
      (fun j : Fin k => |Complex.arg (ζ j)|)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hzi_ne : ζ i ≠ 0 := by
    intro hzero
    have hi_re := hζ i
    rw [hzero] at hi_re
    simp at hi_re
  have hnorm_i_pos : 0 < ‖ζ i‖ := norm_pos_iff.mpr hzi_ne
  have hnorm_i_le : ‖ζ i‖ ≤ ‖ζ‖ := norm_apply_le_pi_norm ζ i
  have hnorm_pos : 0 < ‖ζ‖ := hnorm_i_pos.trans_le hnorm_i_le
  have hradius_pos : 0 < osiiChapterVIRegularizationRadius k ζ :=
    osiiChapterVIRegularizationRadius_pos hk hζ
  have hradius_le_re :
      osiiChapterVIRegularizationRadius k ζ ≤ (ζ i).re :=
    osiiChapterVIRegularizationRadius_le_re hζ i
  have hdefect_nonneg : 0 ≤ osiiTimeAngularDefect k ζ :=
    (osiiTimeAngularDefect_pos hζ).le
  have hsin_le :
      Real.sin (osiiTimeAngularDefect k ζ) ≤
        osiiTimeAngularDefect k ζ :=
    Real.sin_le hdefect_nonneg
  have hsin_eq :
      Real.sin (osiiTimeAngularDefect k ζ) = (ζ i).re / ‖ζ i‖ := by
    rw [osiiTimeAngularDefect, osiiTimeMaxAbsArg, hi,
      Real.sin_pi_div_two_sub, Real.cos_abs, Complex.cos_arg hzi_ne]
  calc
    osiiChapterVIRegularizationRadius k ζ / ‖ζ‖ ≤
        osiiChapterVIRegularizationRadius k ζ / ‖ζ i‖ := by
      exact div_le_div_of_nonneg_left hradius_pos.le hnorm_i_pos hnorm_i_le
    _ ≤ (ζ i).re / ‖ζ i‖ := by
      exact div_le_div_of_nonneg_right hradius_le_re hnorm_i_pos.le
    _ = Real.sin (osiiTimeAngularDefect k ζ) := hsin_eq.symm
    _ ≤ osiiTimeAngularDefect k ζ := hsin_le

/-- The reciprocal angular defect is controlled by the two standard
Vladimirov growth factors. -/
theorem angularDefect_inv_le_norm_mul_boundaryFactor
    {k : ℕ} [NeZero k]
    (ζ : Fin k → ℂ)
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    (osiiTimeAngularDefect k ζ)⁻¹ ≤
      ‖ζ‖ * (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hδ_pos : 0 < osiiTimeAngularDefect k ζ :=
    osiiTimeAngularDefect_pos hζ
  have hρ_pos : 0 < osiiChapterVIRegularizationRadius k ζ :=
    osiiChapterVIRegularizationRadius_pos hk hζ
  have hnorm_pos : 0 < ‖ζ‖ := by
    obtain ⟨i, _⟩ := finUnivNonempty k
    have hzi_ne : ζ i ≠ 0 := by
      intro hzero
      have hi_re := hζ i
      rw [hzero] at hi_re
      simp at hi_re
    exact (norm_pos_iff.mpr hzi_ne).trans_le (norm_apply_le_pi_norm ζ i)
  have hradius_le :
      osiiChapterVIRegularizationRadius k ζ ≤
        osiiTimeAngularDefect k ζ * ‖ζ‖ := by
    exact (div_le_iff₀ hnorm_pos).1
      (regularizationRadius_div_norm_le_angularDefect ζ hζ)
  have hinv_le_radius :
      (osiiTimeAngularDefect k ζ)⁻¹ ≤
        ‖ζ‖ / osiiChapterVIRegularizationRadius k ζ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hδ_pos hρ_pos).2
    simpa [mul_comm] using hradius_le
  have hradius_ratio :=
    osiiChapterVIRegularizationRadius_ratio_le hk hζ
  have hinv_radius_le :
      (osiiChapterVIRegularizationRadius k ζ)⁻¹ ≤
        1 + (osiiTimeBoundaryDistance k ζ)⁻¹ := by
    calc
      (osiiChapterVIRegularizationRadius k ζ)⁻¹ =
          (1 / 16 : ℝ) *
            (16 / osiiChapterVIRegularizationRadius k ζ) := by
        field_simp
      _ ≤ (1 / 16 : ℝ) *
          (16 * (1 + (osiiTimeBoundaryDistance k ζ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hradius_ratio (by norm_num)
      _ = 1 + (osiiTimeBoundaryDistance k ζ)⁻¹ := by ring
  calc
    (osiiTimeAngularDefect k ζ)⁻¹ ≤
        ‖ζ‖ / osiiChapterVIRegularizationRadius k ζ := hinv_le_radius
    _ = ‖ζ‖ * (osiiChapterVIRegularizationRadius k ζ)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ ‖ζ‖ * (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) :=
      mul_le_mul_of_nonneg_left hinv_radius_le (norm_nonneg ζ)

/-- A single positive constant dominating the coordinatewise constants from
the recursive-angle estimate `(5.28)`. -/
noncomputable def recursiveAngleQuantitativeEnvelope
    (k : ℕ) [NeZero k] : ℝ :=
  Real.pi / 2 *
    (1 + Finset.univ.sup' (finUnivNonempty k)
      (fun i : Fin k =>
        OSIIChapterV.recursiveAngleQuantitativeConstant i.val))

theorem recursiveAngleQuantitativeEnvelope_pos
    (k : ℕ) [NeZero k] :
    0 < recursiveAngleQuantitativeEnvelope k := by
  have hsup_nonneg :
      0 ≤ Finset.univ.sup' (finUnivNonempty k)
        (fun i : Fin k =>
          OSIIChapterV.recursiveAngleQuantitativeConstant i.val) := by
    obtain ⟨i, hi⟩ := finUnivNonempty k
    exact (OSIIChapterV.recursiveAngleQuantitativeConstant_nonneg i.val).trans
      (Finset.le_sup'
        (fun j : Fin k =>
          OSIIChapterV.recursiveAngleQuantitativeConstant j.val) hi)
  exact mul_pos (by positivity) (by linarith)

/-- The stage-selection envelope has an explicit exponential-in-arity bound,
instead of an uncontrolled constant chosen separately at each arity. -/
theorem recursiveAngleQuantitativeEnvelope_le_three_pow
    (k : ℕ) [NeZero k] :
    recursiveAngleQuantitativeEnvelope k ≤
      Real.pi / 2 * (1 + (3 : ℝ) ^ k) := by
  unfold recursiveAngleQuantitativeEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr
  rw [Finset.sup'_le_iff]
  intro i _
  change (3 : ℝ) ^ i.val ≤ (3 : ℝ) ^ k
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt i.isLt)

theorem recursiveAngleQuantitativeCoefficient_le_envelope
    {k : ℕ} [NeZero k] (i : Fin k) :
    Real.pi / 2 *
        OSIIChapterV.recursiveAngleQuantitativeConstant i.val ≤
      recursiveAngleQuantitativeEnvelope k := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hi :
      OSIIChapterV.recursiveAngleQuantitativeConstant i.val ≤
        Finset.univ.sup' (finUnivNonempty k)
          (fun j : Fin k =>
            OSIIChapterV.recursiveAngleQuantitativeConstant j.val) :=
    Finset.le_sup'
      (fun j : Fin k =>
        OSIIChapterV.recursiveAngleQuantitativeConstant j.val)
      (Finset.mem_univ i)
  unfold recursiveAngleQuantitativeEnvelope
  gcongr
  linarith

private theorem one_lt_sqrt_two :
    (1 : ℝ) < Real.sqrt 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  nlinarith

/-- A point in the product right half-plane lies in a recursive-angle sector
whose depth is controlled by its angular defect. -/
theorem exists_recursiveAngle_stage_with_quantitative_depth
    {k : ℕ} [NeZero k]
    (ζ : Fin k → ℂ)
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    ∃ N : ℕ,
      ζ ∈ OSIIChapterV.osiiTimeArgumentSector
        (fun i : Fin k => OSIIChapterV.recursiveAngle (i.val + 1) N) ∧
      (Real.sqrt 2) ^ N ≤
        Real.sqrt 2 *
          (1 + recursiveAngleQuantitativeEnvelope k /
            osiiTimeAngularDefect k ζ) := by
  let Γ := recursiveAngleQuantitativeEnvelope k
  let δ := osiiTimeAngularDefect k ζ
  let x := max 1 (Γ / δ)
  have hΓ_pos : 0 < Γ := by
    simpa [Γ] using recursiveAngleQuantitativeEnvelope_pos k
  have hδ_pos : 0 < δ := by
    simpa [δ] using osiiTimeAngularDefect_pos hζ
  have hratio_nonneg : 0 ≤ Γ / δ := div_nonneg hΓ_pos.le hδ_pos.le
  have hx_one : 1 ≤ x := by exact le_max_left _ _
  obtain ⟨n, hn_le, hn_lt⟩ :=
    exists_nat_pow_near hx_one one_lt_sqrt_two
  refine ⟨n + 1, ?_, ?_⟩
  · refine ⟨hζ, ?_⟩
    intro i
    have hratio_lt_pow :
        Γ / δ < (Real.sqrt 2) ^ (n + 1) :=
      (le_max_right 1 (Γ / δ)).trans_lt hn_lt
    have hpow_pos : 0 < (Real.sqrt 2) ^ (n + 1) :=
      pow_pos (Real.sqrt_pos.2 (by norm_num)) _
    have hΓ_div_pow_lt :
        Γ / (Real.sqrt 2) ^ (n + 1) < δ := by
      apply (div_lt_iff₀ hpow_pos).2
      apply (div_lt_iff₀ hδ_pos).1 at hratio_lt_pow
      simpa [mul_comm] using hratio_lt_pow
    have hmax_lt :
        osiiTimeMaxAbsArg k ζ <
          Real.pi / 2 - Γ / (Real.sqrt 2) ^ (n + 1) := by
      dsimp [δ, osiiTimeAngularDefect] at hΓ_div_pow_lt
      linarith
    have hcoeff :=
      recursiveAngleQuantitativeCoefficient_le_envelope (k := k) i
    have hcoeff_div :
        Real.pi / 2 *
              OSIIChapterV.recursiveAngleQuantitativeConstant i.val /
              (Real.sqrt 2) ^ (n + 1) ≤
            Γ / (Real.sqrt 2) ^ (n + 1) :=
      div_le_div_of_nonneg_right hcoeff hpow_pos.le
    have hlower :=
      OSIIChapterV.recursiveAngle_quantitative_lower_bound
        i.val (n + 1)
    calc
      |Complex.arg (ζ i)| ≤ osiiTimeMaxAbsArg k ζ :=
        abs_arg_le_osiiTimeMaxAbsArg ζ i
      _ < Real.pi / 2 - Γ / (Real.sqrt 2) ^ (n + 1) := hmax_lt
      _ ≤ Real.pi / 2 -
          (Real.pi / 2 *
            OSIIChapterV.recursiveAngleQuantitativeConstant i.val) /
              (Real.sqrt 2) ^ (n + 1) := sub_le_sub_left hcoeff_div _
      _ = Real.pi / 2 *
          (1 - OSIIChapterV.recursiveAngleQuantitativeConstant i.val /
            (Real.sqrt 2) ^ (n + 1)) := by ring
      _ ≤ OSIIChapterV.recursiveAngle (i.val + 1) (n + 1) := hlower
  · have hx_bound : x ≤ 1 + Γ / δ := by
      exact max_le (by linarith) (by linarith)
    rw [pow_succ]
    calc
      (Real.sqrt 2) ^ n * Real.sqrt 2 ≤ x * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hn_le (Real.sqrt_nonneg 2)
      _ ≤ (1 + Γ / δ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hx_bound (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (1 + Γ / δ) := by ring

/-- Quantitative stage selection in the standard Chapter VI growth
coordinates. -/
theorem exists_recursiveAngle_stage_with_standard_growth_depth
    {k : ℕ} [NeZero k]
    (ζ : Fin k → ℂ)
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    ∃ N : ℕ,
      ζ ∈ OSIIChapterV.osiiTimeArgumentSector
        (fun i : Fin k => OSIIChapterV.recursiveAngle (i.val + 1) N) ∧
      (Real.sqrt 2) ^ N ≤
        Real.sqrt 2 * (1 + recursiveAngleQuantitativeEnvelope k) *
          (1 + ‖ζ‖) *
            (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) := by
  obtain ⟨N, hsector, hdepth⟩ :=
    exists_recursiveAngle_stage_with_quantitative_depth ζ hζ
  refine ⟨N, hsector, hdepth.trans ?_⟩
  let Γ := recursiveAngleQuantitativeEnvelope k
  let δ := osiiTimeAngularDefect k ζ
  let b := 1 + (osiiTimeBoundaryDistance k ζ)⁻¹
  have hΓ_nonneg : 0 ≤ Γ := by
    simpa [Γ] using (recursiveAngleQuantitativeEnvelope_pos k).le
  have hboundary_pos : 0 < osiiTimeBoundaryDistance k ζ :=
    osiiTimeBoundaryDistance_pos
      (Nat.pos_of_ne_zero (NeZero.ne k)) hζ
  have hb_one : 1 ≤ b := by
    dsimp [b]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hboundary_pos.le)
  have hangular : δ⁻¹ ≤ ‖ζ‖ * b := by
    simpa [δ, b] using angularDefect_inv_le_norm_mul_boundaryFactor ζ hζ
  have hinside :
      1 + Γ / δ ≤ (1 + Γ) * (1 + ‖ζ‖) * b := by
    calc
      1 + Γ / δ = 1 + Γ * δ⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1 + Γ * (‖ζ‖ * b) := by
        gcongr
      _ ≤ (1 + Γ) * (1 + ‖ζ‖) * b := by
        have hnb : 0 ≤ ‖ζ‖ * b :=
          mul_nonneg (norm_nonneg ζ) (le_trans zero_le_one hb_one)
        have hΓb : 0 ≤ Γ * b :=
          mul_nonneg hΓ_nonneg (le_trans zero_le_one hb_one)
        nlinarith
  simpa [Γ, δ, b, mul_assoc] using
    mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2)

end OSReconstruction
