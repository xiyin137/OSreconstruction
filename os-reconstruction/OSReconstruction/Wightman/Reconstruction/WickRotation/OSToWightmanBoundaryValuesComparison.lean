/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.SCV.DistributionalEOWCutoff
























open scoped Classical NNReal
open BigOperators Finset

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {d : ℕ} [NeZero d]

def canonicalForwardConeDirection (n : ℕ) : Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ = 0 then (↑(k : ℕ) + 1 : ℝ) else 0

theorem canonicalForwardConeDirection_mem (n : ℕ) :
    InForwardCone d n (canonicalForwardConeDirection (d := d) n) := by
  let η₀ : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i
        split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  rw [inForwardCone_iff_mem_forwardConeAbs]
  intro k
  simp only []
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [canonicalForwardConeDirection, η₀, h]
  · by_cases hμ : μ = 0
    · simp [canonicalForwardConeDirection, η₀, hμ]
      have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hk_pos]
        simp
      rw [this]
      ring
    · simp [canonicalForwardConeDirection, η₀, hμ]



private theorem boundary_ray_translation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x i + a) =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  let aN : NPointDomain d n := fun _ => a
  let gfun : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f x
  have hga :
      (fun x : NPointDomain d n => gfun (x + aN)) =
        fun x : NPointDomain d n =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
    ext x
    calc
      gfun (x + aN)
          = F_n (fun k μ => ↑((x + aN) k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
              rfl
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
            congr
            ext k μ
            simp [aN, Pi.add_apply, add_sub_cancel_right]
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
            rfl
  rw [← hga, MeasureTheory.integral_add_right_eq_self gfun aN]
  simp only [gfun]
  congr 1
  ext x
  exact congrArg (fun z : ℂ => z * f x) (hF_inv a x η ε hε)

private theorem bv_translation_invariance_transfer_of_F_invariant
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  intro a f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun i => x i + a) := by
      congr 1
      ext x
      have hxg : g x = f (fun i => x i + a) := by
        change g.toFun x = f.toFun (fun i => x i + a)
        exact hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => x i + a) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_translation_invariant_of_F_invariant (d := d) n F_n hF_inv a f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_translation_invariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  exact bv_translation_invariance_transfer_of_F_invariant (d := d) n W_n F_n hBV hF_inv

theorem integral_lorentz_eq_self_full {n : ℕ}
    (Λ : FullLorentzGroup d)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have habs : |Λ.val.det| = 1 := by
    rcases FullLorentzGroup.det_eq_pm_one Λ with hdet | hdet
    · rw [hdet]
      simp
    · rw [hdet]
      simp
  have hdet_ne : Λ.val.det ≠ 0 := by
    intro hzero
    rw [hzero] at habs
    norm_num at habs
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmv : (fun v => Λ.val.mulVec v) = Matrix.toLin' Λ.val := by
    ext v
    simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d + 1) → ℝ => Λ.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]
    constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [habs]
  let e : (Fin n → Fin (d + 1) → ℝ) ≃ᵐ (Fin n → Fin (d + 1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.mulVec (a i)
        invFun := fun a i => Λ⁻¹.val.mulVec (a i)
        left_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛinv_mul]
        right_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛ_mul_inv] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_Λ.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Λinv.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

theorem bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d),
        LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
          F_n (fun k μ => ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ_ortho f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := orthochronous_preserves_forward_cone (d := d) Λ hΛ_ortho diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
      have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
      rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
      rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
      exact h1
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa only [LorentzGroup.toFull, hlin, Matrix.mulVec_mulVec,
        hΛinv_mul, Matrix.one_mulVec] using
        (integral_lorentz_eq_self_full (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ hΛ_ortho x ε hε] with x hx
      rw [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

omit [NeZero d] in
private theorem locality_unflatten_flattenSchwartzNPoint
    {n : ℕ} (f : SchwartzNPoint d n) :
    OSReconstruction.unflattenSchwartzNPoint (d := d)
      (OSReconstruction.flattenSchwartzNPoint (d := d) f) = f := by
  ext x
  simp [OSReconstruction.flattenSchwartzNPoint_apply,
    OSReconstruction.unflattenSchwartzNPoint_apply]

private noncomputable def localityUnitBallBumpSchwartzNPointRadius
    (n : ℕ) (R : ℝ) (hR : 0 < R) : SchwartzNPoint d n :=
  OSReconstruction.unflattenSchwartzNPoint (d := d)
    (OSReconstruction.unitBallBumpSchwartzPiRadius (n * (d + 1)) R hR)

private noncomputable def localityBumpTruncationRadiusNPoint
    {n : ℕ} (f : SchwartzNPoint d n) (N : ℕ) : SchwartzNPoint d n :=
  SchwartzMap.smulLeftCLM ℂ
    (localityUnitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)) f

set_option maxHeartbeats 4000000 in
private theorem localityBumpTruncationRadiusNPoint_eq_unflatten
    {n : ℕ} (f : SchwartzNPoint d n) (N : ℕ) :
    localityBumpTruncationRadiusNPoint (d := d) f N =
      OSReconstruction.unflattenSchwartzNPoint (d := d)
        (OSReconstruction.bumpTruncationRadius
          (OSReconstruction.flattenSchwartzNPoint (d := d) f) N) := by
  ext x
  rw [localityBumpTruncationRadiusNPoint]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((localityUnitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N) : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (localityUnitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)).hasTemperateGrowth
    f x]
  rw [localityUnitBallBumpSchwartzNPointRadius,
    OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [OSReconstruction.flattenSchwartzNPoint_apply, smul_eq_mul]

set_option maxHeartbeats 4000000 in
/-- Compactly supported approximants that preserve vanishing outside a set.

The approximants are ordinary radial bump truncations of `f`.  Compact support
comes from the bump, convergence is the standard Schwartz-density theorem, and
the zero-off property is preserved because each approximant is a pointwise
multiple of `f`. -/
theorem exists_compactSupportApprox_zeroOff_npoint
    {n : ℕ} (U : Set (NPointDomain d n)) (f : SchwartzNPoint d n)
    (hf_zero : ∀ x, x ∉ U → f x = 0) :
    ∃ fN : ℕ → SchwartzNPoint d n,
      (∀ N, HasCompactSupport (fN N : NPointDomain d n → ℂ)) ∧
      (∀ N x, x ∉ U → fN N x = 0) ∧
      Filter.Tendsto fN Filter.atTop (nhds f) := by
  let fN : ℕ → SchwartzNPoint d n :=
    fun N => localityBumpTruncationRadiusNPoint (d := d) f N
  refine ⟨fN, ?_, ?_, ?_⟩
  · intro N
    have hflat_compact :
        HasCompactSupport
          (((OSReconstruction.bumpTruncationRadius
            (OSReconstruction.flattenSchwartzNPoint (d := d) f) N :
              SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)) :
            (Fin (n * (d + 1)) → ℝ) → ℂ) := by
      simpa [OSReconstruction.bumpTruncationRadius,
        OSReconstruction.bumpTruncationRadiusValue] using
        OSReconstruction.hasCompactSupport_cutoff_mul_radius
          (m := n * (d + 1)) (R := OSReconstruction.bumpTruncationRadiusValue N)
          (OSReconstruction.bumpTruncationRadiusValue_pos N)
          (OSReconstruction.flattenSchwartzNPoint (d := d) f)
    simpa [fN] using
      (show HasCompactSupport
          ((localityBumpTruncationRadiusNPoint (d := d) f N :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) from by
        rw [localityBumpTruncationRadiusNPoint_eq_unflatten (d := d)]
        convert hflat_compact.comp_homeomorph
            (flattenCLEquivReal n (d + 1)).toHomeomorph using 1
        funext x
        simp only [Function.comp_apply,
          OSReconstruction.unflattenSchwartzNPoint_apply]
        rfl)
  · intro N x hxU
    change
      (localityBumpTruncationRadiusNPoint (d := d) f N :
        SchwartzNPoint d n) x = 0
    rw [localityBumpTruncationRadiusNPoint]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((localityUnitBallBumpSchwartzNPointRadius (d := d) n
        (OSReconstruction.bumpTruncationRadiusValue N)
        (OSReconstruction.bumpTruncationRadiusValue_pos N) : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
      (localityUnitBallBumpSchwartzNPointRadius (d := d) n
        (OSReconstruction.bumpTruncationRadiusValue N)
        (OSReconstruction.bumpTruncationRadiusValue_pos N)).hasTemperateGrowth
      f x]
    simp [hf_zero x hxU]
  · have hunflat :=
      ((OSReconstruction.unflattenSchwartzNPoint (d := d)).continuous.tendsto
        (OSReconstruction.flattenSchwartzNPoint (d := d) f)).comp
          (SchwartzMap.tendsto_bump_truncation_nhds
            (OSReconstruction.flattenSchwartzNPoint (d := d) f))
    have hrew :
        fN =
          fun N : ℕ =>
            OSReconstruction.unflattenSchwartzNPoint (d := d)
              (OSReconstruction.bumpTruncationRadius
                (OSReconstruction.flattenSchwartzNPoint (d := d) f) N) := by
      funext N
      simpa [fN] using
        localityBumpTruncationRadiusNPoint_eq_unflatten (d := d) f N
    rw [hrew]
    change Filter.Tendsto
      ((OSReconstruction.unflattenSchwartzNPoint (d := d)) ∘
        fun N : ℕ => OSReconstruction.bumpTruncationRadius
          (OSReconstruction.flattenSchwartzNPoint (d := d) f) N)
      Filter.atTop (nhds f)
    simpa only [locality_unflatten_flattenSchwartzNPoint (d := d) f] using hunflat

private noncomputable def localityPermuteSchwartzCLM {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)

/-- Compact adjacent locality extends to all Schwartz tests by radial compact
exhaustion, preserving the selected adjacent spacelike support condition. -/
theorem bv_local_commutativity_full_of_compact_support_adjacent_locality {n : ℕ}
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_cont : Continuous W_n)
    (i : Fin n) (hi : i.val + 1 < n)
    (hcompact :
      ∀ (f g : SchwartzNPoint d n),
        HasCompactSupport (f : NPointDomain d n → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d
            (x i) (x ⟨i.val + 1, hi⟩)) →
        (∀ x, g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
        W_n f = W_n g) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      W_n f = W_n g := by
  intro f g hsp hswap
  let j : Fin n := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin n) := Equiv.swap i j
  let U : Set (NPointDomain d n) :=
    {x | MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)}
  have hf_zero : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    by_contra hfx
    exact hxU (hsp x hfx)
  obtain ⟨fN, hfN_compact, hfN_zero, hfN_tendsto⟩ :=
    exists_compactSupportApprox_zeroOff_npoint (d := d) U f hf_zero
  let P : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    localityPermuteSchwartzCLM (d := d) τ
  let gN : ℕ → SchwartzNPoint d n := fun N => P (fN N)
  have hcompact_eq : ∀ N, W_n (fN N) = W_n (gN N) := by
    intro N
    refine hcompact (fN N) (gN N) (hfN_compact N) ?_ ?_
    · intro x hfx
      by_contra hxU
      exact hfx (hfN_zero N x hxU)
    · intro x
      change localityPermuteSchwartzCLM (d := d) (Equiv.swap i j) (fN N) x =
        (fN N).toFun (fun k => x (Equiv.swap i j k))
      rfl
  have hleft :
      Filter.Tendsto (fun N => W_n (fN N)) Filter.atTop (nhds (W_n f)) :=
    (hW_cont.tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    exact (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => W_n (gN N)) Filter.atTop (nhds (W_n g)) :=
    (hW_cont.tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => W_n (fN N)) Filter.atTop (nhds (W_n g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right
