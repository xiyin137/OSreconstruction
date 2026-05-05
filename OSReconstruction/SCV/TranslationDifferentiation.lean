import OSReconstruction.SCV.DistributionalEOWKernel
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Translation Differentiation on Schwartz Space

This file extracts the QFT-free translation difference-quotient theorem needed
for head-block descent.  It deliberately lives in `SCV`, rather than importing
the older Wightman reconstruction file where the same analytic argument first
appeared.
-/

noncomputable section

open scoped SchwartzMap LineDeriv Topology
open SchwartzMap

namespace SCV

/-- A first-order translation estimate in Schwartz seminorms. -/
theorem exists_seminorm_translateSchwartz_sub_le_linear {m : ℕ}
    (g : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n (translateSchwartz (t • v) g - g) ≤ C * |t| := by
  obtain ⟨D, hD_nonneg, hD⟩ := seminorm_translateSchwartz_le (m := m) k (n + 1) g
  let C : ℝ := ‖v‖ * D * (1 + ‖v‖) ^ k
  refine ⟨C, by positivity, ?_⟩
  intro t ht
  refine SchwartzMap.seminorm_le_bound ℝ k n (translateSchwartz (t • v) g - g)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let hxFun : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • H (x + s • (t • v))
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (g.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hxFun_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt hxFun
          (‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    simpa [hxFun] using hcomp.const_smul (‖x‖ ^ k)
  have hxFun_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖ ≤ C * |t| := by
    intro s hs
    have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_of_lt hs.2⟩
    have hs_abs : |s| ≤ 1 := by
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := le_of_lt hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    have hstv_norm : ‖s • (t • v)‖ ≤ ‖v‖ := by
      calc
        ‖s • (t • v)‖ = |s| * (|t| * ‖v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (1 * ‖v‖) := by
          gcongr
        _ = ‖v‖ := by ring
    have hone_pow :
        (1 + ‖s • (t • v)‖) ^ k ≤ (1 + ‖v‖) ^ k := by
      gcongr
    have hseminorm0 :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (⇑(translateSchwartz (s • (t • v)) g)) x‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      exact le_trans (SchwartzMap.le_seminorm ℂ k (n + 1) _ x) (hD (s • (t • v)))
    have hseminorm :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v))‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      have htrans :
          iteratedFDeriv ℝ (n + 1) (⇑(translateSchwartz (s • (t • v)) g)) x =
            iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v)) := by
        simpa [translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) (n + 1)
            (s • (t • v)) x)
      simpa [htrans] using hseminorm0
    have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
    calc
      ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖
          = ‖x‖ ^ k * ‖(fderiv ℝ H (x + s • (t • v))) (t • v)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxpow_nonneg]
      _ ≤ ‖x‖ ^ k * (‖fderiv ℝ H (x + s • (t • v))‖ * ‖t • v‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
      _ = (‖x‖ ^ k * ‖fderiv ℝ H (x + s • (t • v))‖) * ‖t • v‖ := by ring
      _ = (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ)
            (x + s • (t • v))‖) * ‖t • v‖ := by
            rw [norm_fderiv_iteratedFDeriv]
      _ ≤ (D * (1 + ‖s • (t • v)‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ ≤ (D * (1 + ‖v‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ = (D * (1 + ‖v‖) ^ k) * (|t| * ‖v‖) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = C * |t| := by
            dsimp [C]
            ring
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := hxFun)
      (f' := fun s => ‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v)))
      (fun s hs => (hxFun_hasDeriv s).hasDerivWithinAt)
      hxFun_bound
  have hiter_eq :
      iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) g - g)) x =
        H (x + t • v) - H x := by
    have hf : ContDiff ℝ n (⇑(translateSchwartz (t • v) g)) :=
      (translateSchwartz (t • v) g).smooth n
    have hg : ContDiff ℝ n (⇑g) := g.smooth n
    have hfg :
        (⇑(translateSchwartz (t • v) g - g) : (Fin m → ℝ) → ℂ) =
          (⇑(translateSchwartz (t • v) g)) + fun z => -(⇑g z) := by
      ext z
      simp [sub_eq_add_neg]
    have hneg : (fun z => -(⇑g z)) = -⇑g := rfl
    rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt, hneg,
      iteratedFDeriv_neg_apply]
    have htrans :
        iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) g)) x =
          H (x + t • v) := by
      simpa [H, translateSchwartz] using
        (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) n (t • v) x)
    simp [H, htrans, sub_eq_add_neg]
  have hxFun_diff :
      hxFun 1 - hxFun 0 = ‖x‖ ^ k • (H (x + t • v) - H x) := by
    simp [hxFun, smul_sub]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) g - g)) x‖
        = ‖hxFun 1 - hxFun 0‖ := by
            rw [hxFun_diff, hiter_eq, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := by simpa [sub_eq_add_neg] using hmv

/-- Directional derivatives of Schwartz functions commute. -/
theorem lineDerivOp_comm {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v w : Fin m → ℝ) :
    ∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- A single directional derivative commutes past an iterated directional derivative. -/
theorem lineDerivOp_iterated_comm {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (u : Fin n → Fin m → ℝ) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact lineDerivOp_comm f v (u (Fin.last n))

/-- Differentiating an iterated derivative in direction `v` is the same as
iterating after the line derivative `∂_v`. -/
theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v x : Fin m → ℝ) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : (Fin m → ℝ) → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzMap (Fin m → ℝ) ℂ => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [lineDerivOp_iterated_comm (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) (m := u) (x := x))

set_option maxHeartbeats 1200000 in
/-- Every Schwartz seminorm of the translation difference-quotient error is
`O(|t|)` near zero. -/
theorem exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (t⁻¹ • (translateSchwartz (t • v) f - f) - ∂_{v} f) ≤ C * |t| := by
  let g : SchwartzMap (Fin m → ℝ) ℂ := ∂_{v} f
  obtain ⟨C, hC_nonneg, hC⟩ := exists_seminorm_translateSchwartz_sub_le_linear g v k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_ne ht_abs
  refine SchwartzMap.seminorm_le_bound ℝ k n
    (t⁻¹ • (translateSchwartz (t • v) f - f) - ∂_{v} f)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)
  let K :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let ψ : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • (t⁻¹ • H (x + s • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (s • K x)
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (f.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hpsi_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt ψ (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    have hmain0 :
        HasDerivAt
          (fun r : ℝ => t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x)
          (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) s := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_sub] using
        (hcomp.const_smul t⁻¹).sub_const (t⁻¹ • H x)
    have hscale :
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v)) =
          K (x + s • (t • v)) := by
      calc
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))
            = t⁻¹ • (t • ((fderiv ℝ H (x + s • (t • v))) v)) := by
                rw [ContinuousLinearMap.map_smul]
        _ = (t⁻¹ * t) • ((fderiv ℝ H (x + s • (t • v))) v) := by
                rw [smul_smul]
        _ = (fderiv ℝ H (x + s • (t • v))) v := by
                rw [inv_mul_cancel₀ ht_ne, one_smul]
        _ = K (x + s • (t • v)) := by
                rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv
                  (f := f) (v := v) (x := x + s • (t • v))]
    have hlin :
        HasDerivAt (fun r : ℝ => r • K x) (K x) s := by
      simpa [one_smul] using (hasDerivAt_id s).smul_const (K x)
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x) s := by
      convert (hmain0.const_smul (‖x‖ ^ k)).sub (hlin.const_smul (‖x‖ ^ k)) using 1
    have hsub :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
      convert hsub' using 1
      calc
        ‖x‖ ^ k • (K (x + s • (t • v)) - K x)
            = ‖x‖ ^ k • K (x + s • (t • v)) - ‖x‖ ^ k • K x := by
                rw [smul_sub]
        _ = ‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x := by
                rw [hscale]
    exact hsub
  have hpsi_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖ ≤ C * |t| := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le_one : s ≤ 1 := le_of_lt hs.2
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs_nonneg]
      exact hs_le_one
    have hst_abs : |s * t| ≤ 1 := by
      calc
        |s * t| = |s| * |t| := by rw [abs_mul]
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have hiter_eq :
        iteratedFDeriv ℝ n (⇑(translateSchwartz ((s * t) • v) g - g)) x =
          K (x + s • (t • v)) - K x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(translateSchwartz ((s * t) • v) g)) x =
            K (x + s • (t • v)) := by
        simpa [K, translateSchwartz, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) n ((s * t) • v) x)
      rw [show (⇑(translateSchwartz ((s * t) • v) g - g) : (Fin m → ℝ) → ℂ) =
            (⇑(translateSchwartz ((s * t) • v) g)) + fun z => -(⇑g z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply
          ((translateSchwartz ((s * t) • v) g).smooth n).contDiffAt
          (g.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑g z)) = -⇑g by rfl, iteratedFDeriv_neg_apply]
      simp [K, hshift, sub_eq_add_neg]
    have hpoint :
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ ≤ C * |s * t| := by
      calc
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ n (⇑(translateSchwartz ((s * t) • v) g - g)) x‖ := by
                  rw [hiter_eq]
        _ ≤ SchwartzMap.seminorm ℝ k n (translateSchwartz ((s * t) • v) g - g) := by
              exact SchwartzMap.le_seminorm ℂ k n _ x
        _ ≤ C * |s * t| := hC (s * t) hst_abs
    calc
      ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖
          = ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
              have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
              simp [abs_of_nonneg hxpow_nonneg]
      _ ≤ C * |s * t| := hpoint
      _ = C * (|s| * |t|) := by rw [abs_mul]
      _ ≤ C * |t| := by
            have hs_t : |s| * |t| ≤ |t| := by
              simpa [one_mul] using
                (mul_le_mul_of_nonneg_right hs_abs (abs_nonneg t))
            gcongr
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (hf := fun s hs => (hpsi_hasDeriv s).hasDerivWithinAt)
      (bound := hpsi_bound)
  have htarget :
      iteratedFDeriv ℝ n
        (↑(t⁻¹ • (translateSchwartz (t • v) f - f) - ∂_{v} f) :
          (Fin m → ℝ) → ℂ) x =
        t⁻¹ • (H (x + t • v) - H x) - K x := by
    have hshift_sub :
        iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) f - f)) x =
          H (x + t • v) - H x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) f)) x = H (x + t • v) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := (f : (Fin m → ℝ) → ℂ)) n (t • v) x)
      rw [show (⇑(translateSchwartz (t • v) f - f) : (Fin m → ℝ) → ℂ) =
            (⇑(translateSchwartz (t • v) f)) + fun z => -(⇑f z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply ((translateSchwartz (t • v) f).smooth n).contDiffAt
          (f.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑f z)) = -⇑f by rfl, iteratedFDeriv_neg_apply]
      simp [H, hshift, sub_eq_add_neg]
    change
      iteratedFDeriv ℝ n
        (⇑(t⁻¹ • (translateSchwartz (t • v) f - f)) + fun z => -((g : (Fin m → ℝ) → ℂ) z)) x =
        t⁻¹ • (H (x + t • v) - H x) - K x
    rw [iteratedFDeriv_add_apply
      ((t⁻¹ • (translateSchwartz (t • v) f - f)).smooth n).contDiffAt
      (g.smooth n).neg.contDiffAt]
    have hsc :
        iteratedFDeriv ℝ n (⇑(t⁻¹ • (translateSchwartz (t • v) f - f))) x =
          t⁻¹ • iteratedFDeriv ℝ n (⇑(translateSchwartz (t • v) f - f)) x := by
      simpa [Pi.smul_apply] using
        (iteratedFDeriv_const_smul_apply'
          (𝕜 := ℝ) (a := t⁻¹)
          (f := (⇑(translateSchwartz (t • v) f - f) : (Fin m → ℝ) → ℂ))
          (x := x)
          ((translateSchwartz (t • v) f - f).smooth n).contDiffAt)
    have hneg :
        iteratedFDeriv ℝ n (fun z => -((g : (Fin m → ℝ) → ℂ) z)) x = - K x := by
      simpa [K] using
        (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n) (f := (g : (Fin m → ℝ) → ℂ)) (x := x))
    rw [hsc, hneg, hshift_sub]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have hψ0 : ψ 0 = 0 := by
    ext u
    simp [ψ]
  have hψ1 :
      ψ 1 =
        ‖x‖ ^ k •
          iteratedFDeriv ℝ n
            (↑(t⁻¹ • (translateSchwartz (t • v) f - f) - ∂_{v} f) :
              (Fin m → ℝ) → ℂ) x := by
    rw [show ψ 1 =
          ‖x‖ ^ k • (t⁻¹ • (H (x + t • v) - H x) - K x) by
            simp [ψ, sub_eq_add_neg, add_left_comm, add_comm]]
    rw [htarget]
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (↑(t⁻¹ • (translateSchwartz (t • v) f - f) - ∂_{v} f) :
            (Fin m → ℝ) → ℂ) x‖
        = ‖ψ 1 - ψ 0‖ := by
            rw [hψ0, hψ1, sub_zero, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := hmv

/-- Translation difference quotients converge to the directional derivative in
the Schwartz topology. -/
theorem tendsto_diffQuotient_translateSchwartz_zero {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (translateSchwartz (t • v) f - f))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (∂_{v} f)) := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro p ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le f v p.1 p.2
  let δ : ℝ := min 1 (ε / (C + 1))
  have hδ_pos : 0 < δ := by
    have hC1 : 0 < C + 1 := by linarith
    have hquot : 0 < ε / (C + 1) := by positivity
    exact lt_min zero_lt_one hquot
  have hball :
      Metric.ball (0 : ℝ) δ ∩ ({0}ᶜ : Set ℝ) ∈ nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) := by
    simpa [Set.inter_comm] using
      (inter_mem_nhdsWithin ({0}ᶜ : Set ℝ) (Metric.ball_mem_nhds (0 : ℝ) hδ_pos))
  refine Filter.mem_of_superset hball ?_
  intro t ht
  rcases ht with ⟨ht_ball, ht_punctured⟩
  have ht_abs : |t| < δ := by
    simpa [Real.dist_eq] using ht_ball
  have ht_one : |t| ≤ 1 := by
    exact le_trans (le_of_lt ht_abs) (min_le_left _ _)
  have hbound := hC t (by simpa using ht_punctured) ht_one
  have hδ_eps : C * |t| < ε := by
    have hC1 : 0 < C + 1 := by linarith
    have hC_le : C ≤ C + 1 := by linarith
    have ht_eps : |t| < ε / (C + 1) := lt_of_lt_of_le ht_abs (min_le_right _ _)
    calc
      C * |t| ≤ (C + 1) * |t| := by
        gcongr
      _ < (C + 1) * (ε / (C + 1)) := by
        gcongr
      _ = ε := by
        field_simp [ne_of_gt hC1]
  exact lt_of_le_of_lt hbound hδ_eps

end SCV
