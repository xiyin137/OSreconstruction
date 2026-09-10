/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel
import Mathlib.Analysis.Calculus.FDeriv.Symmetric











noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped LineDeriv

namespace SCV

/-- Translation on Euclidean Schwartz space as a continuous linear map:
`(euclideanTranslateSchwartzCLM a φ)(x) = φ (x + a)`. -/
noncomputable def euclideanTranslateSchwartzCLM
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ ι) ℂ := by
  let g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => x + a
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper :
      ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖a‖ := by
      calc
        ‖x‖ = ‖(x + a) - a‖ := by simp
        _ ≤ ‖g x‖ + ‖a‖ := by simpa [g] using norm_sub_le (x + a) a
    have hfac : ‖g x‖ + ‖a‖ ≤ (1 + ‖a‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg a]
    have hpow : (1 + ‖g x‖) ^ (1 : ℕ) = 1 + ‖g x‖ := by simp
    rw [hpow]
    exact le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem euclideanTranslateSchwartz_apply
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanTranslateSchwartzCLM a φ x = φ (x + a) := rfl

@[simp]
theorem euclideanTranslateSchwartzCLM_zero
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanTranslateSchwartzCLM (0 : EuclideanSpace ℝ ι) φ = φ := by
  ext x
  simp

/-- The reflected translate of a Euclidean Schwartz kernel:
`euclideanReflectedTranslate x ρ y = ρ (y - x)`. -/
noncomputable def euclideanReflectedTranslate
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  euclideanTranslateSchwartzCLM (-x) ρ

@[simp]
theorem euclideanReflectedTranslate_apply
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanReflectedTranslate x ρ y = ρ (y - x) := by
  simp [euclideanReflectedTranslate, sub_eq_add_neg]

/-- If a reflected Euclidean kernel of radius `r` is centered at a point whose
closed `r`-ball lies in `V`, then the reflected translate is compactly
supported in `V`. -/
theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)}
    {x : EuclideanSpace ℝ ι} {r : ℝ}
    {ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ}
    (hx : Metric.closedBall x r ⊆ V)
    (hρ : tsupport (ρ : EuclideanSpace ℝ ι → ℂ) ⊆
      Metric.closedBall 0 r) :
    SupportsInOpen
      (euclideanReflectedTranslate x ρ :
        EuclideanSpace ℝ ι → ℂ) V := by
  let e : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι := Homeomorph.addRight (-x)
  have hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall 0 r) (isClosed_tsupport _) hρ
  constructor
  · change HasCompactSupport fun y : EuclideanSpace ℝ ι => ρ (e y)
    exact hρ_compact.comp_homeomorph e
  · have htsupport :
        tsupport
          (euclideanReflectedTranslate x ρ :
            EuclideanSpace ℝ ι → ℂ) =
          e ⁻¹' tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [e, euclideanReflectedTranslate, sub_eq_add_neg] using
        (tsupport_comp_eq_preimage
          (g := (ρ : EuclideanSpace ℝ ι → ℂ)) e)
    intro y hy
    have hyρ : y - x ∈ tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [htsupport, e, sub_eq_add_neg] using hy
    have hyball0 : y - x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) r :=
      hρ hyρ
    have hyball : y ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hyball0
    exact hx hyball

private theorem iteratedFDeriv_sub_euclidean_schwartz
    {ι : Type*} [Fintype ι]
    (f g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (n : ℕ) (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg :
      (⇑(f - g) : EuclideanSpace ℝ ι → ℂ) =
        (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt,
    hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

/-- Euclidean directional derivatives of Schwartz functions commute. -/
theorem euclideanLineDerivOp_comm
    {ι : Type*} [Fintype ι]
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v w : EuclideanSpace ℝ ι) :
    ∂_{v} ((∂_{w} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))) x =
        (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2
          (f : EuclideanSpace ℝ ι → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2
          (f : EuclideanSpace ℝ ι → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- A single Euclidean directional derivative commutes past an iterated
directional derivative. -/
theorem euclideanLineDerivOp_iterated_comm
    {ι : Type*} [Fintype ι] {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι)
    (u : Fin n → EuclideanSpace ℝ ι) :
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
      exact euclideanLineDerivOp_comm f v (u (Fin.last n))

/-- Differentiating an iterated Euclidean derivative in direction `v` is the
same as iterating after the line derivative `∂_v`. -/
theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv
    {ι : Type*} [Fintype ι] {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v x : EuclideanSpace ℝ ι) :
    fderiv ℝ (iteratedFDeriv ℝ n
        (f : EuclideanSpace ℝ ι → ℂ)) x v =
      iteratedFDeriv ℝ n
        (((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          EuclideanSpace ℝ ι → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n
        (f : EuclideanSpace ℝ ι → ℂ)) x v) u =
        iteratedFDeriv ℝ (n + 1)
          (f : EuclideanSpace ℝ ι → ℂ) x (Fin.cons v u) := by
      simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
      symm
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
      simpa using
        (congrArg (fun g : SchwartzMap (EuclideanSpace ℝ ι) ℂ => g x)
          (LineDeriv.iteratedLineDerivOp_succ_left
            (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
      rw [euclideanLineDerivOp_iterated_comm (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
            EuclideanSpace ℝ ι → ℂ)) x u := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := (∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))
          (m := u) (x := x))

/-- Pointwise iterated-derivative formula for the Euclidean translation
difference-quotient error. -/
theorem euclideanDiffQuotient_iteratedFDeriv_pointwise
    {ι : Type*} [Fintype ι] {n : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι) {t : ℝ} (_ht : t ≠ 0)
    (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ n
      (↑(t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) - ∂_{v} φ) :
        EuclideanSpace ℝ ι → ℂ) x =
      t⁻¹ •
        (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
          iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
      iteratedFDeriv ℝ n
        (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          EuclideanSpace ℝ ι → ℂ)) x := by
  let g : SchwartzMap (EuclideanSpace ℝ ι) ℂ := ∂_{v} φ
  have hshift_sub :
      iteratedFDeriv ℝ n
        (⇑(euclideanTranslateSchwartzCLM (t • v) φ - φ)) x =
        iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
          iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x := by
    have hshift :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) φ)) x =
          iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) := by
      simpa using
        (iteratedFDeriv_comp_add_right
          (f := (φ : EuclideanSpace ℝ ι → ℂ)) n (t • v) x)
    rw [iteratedFDeriv_sub_euclidean_schwartz, hshift]
  change
    iteratedFDeriv ℝ n
      (⇑(t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ)) +
        fun z => -((g : EuclideanSpace ℝ ι → ℂ) z)) x =
      t⁻¹ •
        (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
          iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
      iteratedFDeriv ℝ n
        (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          EuclideanSpace ℝ ι → ℂ)) x
  rw [iteratedFDeriv_add_apply
    ((t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ)).smooth n).contDiffAt
    (g.smooth n).neg.contDiffAt]
  have hsc :
      iteratedFDeriv ℝ n
        (⇑(t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ))) x =
        t⁻¹ • iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) φ - φ)) x := by
    simpa [Pi.smul_apply] using
      (iteratedFDeriv_const_smul_apply'
        (𝕜 := ℝ) (a := t⁻¹)
        (f := (⇑(euclideanTranslateSchwartzCLM (t • v) φ - φ) :
          EuclideanSpace ℝ ι → ℂ))
        (x := x)
        ((euclideanTranslateSchwartzCLM (t • v) φ - φ).smooth n).contDiffAt)
  have hneg :
      iteratedFDeriv ℝ n
        (fun z => -((g : EuclideanSpace ℝ ι → ℂ) z)) x =
        -iteratedFDeriv ℝ n
          (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
            EuclideanSpace ℝ ι → ℂ)) x := by
    simpa [g] using
      (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n)
        (f := (g : EuclideanSpace ℝ ι → ℂ)) (x := x))
  rw [hsc, hneg, hshift_sub]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Weighted pointwise bound for the Euclidean translation difference-quotient
error, assuming the first-order estimate for `∂_v φ`. -/
theorem euclideanDiffQuotient_weighted_pointwise_bound
    {ι : Type*} [Fintype ι] {n : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι) (k : ℕ)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC : ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℝ k n
        (euclideanTranslateSchwartzCLM (t • v)
          (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) -
          ∂_{v} φ) ≤ C * |t|)
    {t : ℝ} (ht_ne : t ≠ 0) (ht_abs : |t| ≤ 1)
    (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ k *
        ‖t⁻¹ •
            (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
              iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
          iteratedFDeriv ℝ n
            (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              EuclideanSpace ℝ ι → ℂ)) x‖ ≤ C * |t| := by
  let g : SchwartzMap (EuclideanSpace ℝ ι) ℂ := ∂_{v} φ
  let H :
      EuclideanSpace ℝ ι →
        ContinuousMultilinearMap ℝ
          (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ)
  let K :
      EuclideanSpace ℝ ι →
        ContinuousMultilinearMap ℝ
          (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    iteratedFDeriv ℝ n (g : EuclideanSpace ℝ ι → ℂ)
  let ψ : ℝ →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun s => ‖x‖ ^ k • (t⁻¹ • H (x + s • (t • v)) - t⁻¹ • H x) -
      ‖x‖ ^ k • (s • K x)
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (φ.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hpsi_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt ψ (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
    intro s
    have hgamma :
        HasDerivAt
          (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] ℝ := 1
      let Lsmul : ℝ →L[ℝ] EuclideanSpace ℝ ι :=
        ContinuousLinearMap.smulRight L (t • v)
      simpa [L, Lsmul, ContinuousLinearMap.smulRight_apply, one_smul,
        add_comm, add_left_comm, add_assoc] using (Lsmul.hasDerivAt).const_add x
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
                rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv
                  (f := φ) (v := v) (x := x + s • (t • v))]
    have hlin : HasDerivAt (fun r : ℝ => r • K x) (K x) s := by
      simpa [one_smul] using (hasDerivAt_id s).smul_const (K x)
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) -
              ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) -
            ‖x‖ ^ k • K x) s := by
      convert (hmain0.const_smul (‖x‖ ^ k)).sub (hlin.const_smul (‖x‖ ^ k)) using 1
    have hsub :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) -
              ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
      convert hsub' using 1
      calc
        ‖x‖ ^ k • (K (x + s • (t • v)) - K x)
            = ‖x‖ ^ k • K (x + s • (t • v)) - ‖x‖ ^ k • K x := by
                rw [smul_sub]
        _ = ‖x‖ ^ k •
              (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) -
              ‖x‖ ^ k • K x := by
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
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM ((s * t) • v) g - g)) x =
          K (x + s • (t • v)) - K x := by
      have hshift :
          iteratedFDeriv ℝ n
            (⇑(euclideanTranslateSchwartzCLM ((s * t) • v) g)) x =
            K (x + s • (t • v)) := by
        simpa [K, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (iteratedFDeriv_comp_add_right
            (f := (g : EuclideanSpace ℝ ι → ℂ)) n ((s * t) • v) x)
      rw [iteratedFDeriv_sub_euclidean_schwartz, hshift]
    have hpoint :
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ ≤ C * |s * t| := by
      calc
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ n
                  (⇑(euclideanTranslateSchwartzCLM ((s * t) • v) g - g)) x‖ := by
                  rw [hiter_eq]
        _ ≤ SchwartzMap.seminorm ℝ k n
              (euclideanTranslateSchwartzCLM ((s * t) • v) g - g) := by
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
  have hψ0 : ψ 0 = 0 := by
    ext u
    simp [ψ]
  have hψ1 :
      ψ 1 =
        ‖x‖ ^ k •
          (t⁻¹ •
            (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
              iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
          iteratedFDeriv ℝ n
            (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              EuclideanSpace ℝ ι → ℂ)) x) := by
    change
      ‖x‖ ^ k • (t⁻¹ • H (x + (1 : ℝ) • (t • v)) - t⁻¹ • H x) -
          ‖x‖ ^ k • ((1 : ℝ) • K x) =
        ‖x‖ ^ k •
          (t⁻¹ •
            (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
              iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
          iteratedFDeriv ℝ n
            (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              EuclideanSpace ℝ ι → ℂ)) x)
    have hcenter : x + (1 : ℝ) • (t • v) = x + t • v := by
      rw [one_smul]
    rw [hcenter]
    have hKone : ‖x‖ ^ k • ((1 : ℝ) • K x) = ‖x‖ ^ k • K x := by
      rw [one_smul]
    rw [hKone]
    calc
      ‖x‖ ^ k • (t⁻¹ • H (x + t • v) - t⁻¹ • H x) -
          ‖x‖ ^ k • K x =
          ‖x‖ ^ k • ((t⁻¹ • H (x + t • v) - t⁻¹ • H x) - K x) := by
        exact (smul_sub (‖x‖ ^ k)
          (t⁻¹ • H (x + t • v) - t⁻¹ • H x) (K x)).symm
      _ =
        ‖x‖ ^ k •
          (t⁻¹ •
            (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
              iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
          iteratedFDeriv ℝ n
            (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              EuclideanSpace ℝ ι → ℂ)) x) := by
        congr 1
        dsimp [H, K, g]
        rw [smul_sub]
  calc
    ‖x‖ ^ k *
        ‖t⁻¹ •
            (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
              iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
          iteratedFDeriv ℝ n
            (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              EuclideanSpace ℝ ι → ℂ)) x‖
        = ‖ψ 1 - ψ 0‖ := by
            rw [hψ0, hψ1, sub_zero, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := hmv

/-- Euclidean Schwartz translations compose additively. -/
theorem euclideanTranslateSchwartzCLM_comp
    {ι : Type*} [Fintype ι]
    (a b : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanTranslateSchwartzCLM a (euclideanTranslateSchwartzCLM b ρ) =
      euclideanTranslateSchwartzCLM (a + b) ρ := by
  ext y
  simp [add_assoc]

/-- Compactly supported Euclidean translations are continuous in the Schwartz
topology. -/
theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hψ_compact : HasCompactSupport (ψ : EuclideanSpace ℝ ι → ℂ))
  (a0 : EuclideanSpace ℝ ι) :
    Tendsto (fun a : EuclideanSpace ℝ ι => euclideanTranslateSchwartzCLM a ψ)
      (𝓝 a0) (𝓝 (euclideanTranslateSchwartzCLM a0 ψ)) := by
  let K : Set (EuclideanSpace ℝ ι) :=
    tsupport (ψ : EuclideanSpace ℝ ι → ℂ)
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set (EuclideanSpace ℝ ι) := Metric.closedBall a0 1
  have ha0J : a0 ∈ J := Metric.mem_closedBall_self (by positivity)
  have hJ_compact : IsCompact J := isCompact_closedBall _ _
  let Ktrans : Set (EuclideanSpace ℝ ι) :=
    (fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => p.1 - p.2) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod hJ_compact).image ?_
    exact continuous_fst.sub continuous_snd
  let q : EuclideanSpace ℝ ι → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := continuous_norm.pow k
  obtain ⟨B, hB⟩ :=
    hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2)
  have hH_cont : Continuous H := by
    let A : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
        EuclideanSpace ℝ ι := fun p => p.1 + p.2
    have hA : Continuous A := continuous_fst.add continuous_snd
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod hJ_compact).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 a0 := Metric.closedBall_mem_nhds _ (by positivity)
  have hball_nhds : Metric.ball a0 δ ∈ 𝓝 a0 := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with a ha
  have haJ : a ∈ J := ha.1
  have hadist : dist a a0 < δ := ha.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM a ψ - euclideanTranslateSchwartzCLM a0 ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_a : (x, a) ∈ Ktrans ×ˢ J := ⟨hx, haJ⟩
    have hpair_a0 : (x, a0) ∈ Ktrans ×ˢ J := ⟨hx, ha0J⟩
    have hpair_dist : dist (x, a) (x, a0) < δ := by
      simpa [Prod.dist_eq] using hadist
    have hderiv_close : ‖H (x, a) - H (x, a0)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_a _ hpair_a0 hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (pow_nonneg (norm_nonneg x) k)
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x =
          H (x, a) - H (x, a0) := by
      have htrans_a :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            H (x, a) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)
      have htrans_a0 :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            H (x, a0) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)
      rw [iteratedFDeriv_sub_euclidean_schwartz, htrans_a, htrans_a0]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, a) - H (x, a0)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K] using hy'
    have hx_not_a : x + a ∉ K := by
      intro hxa
      exact hx ⟨(x + a, a), ⟨hxa, haJ⟩, by simp⟩
    have hx_not_a0 : x + a0 ∉ K := by
      intro hxa0
      exact hx ⟨(x + a0, a0), ⟨hxa0, ha0J⟩, by simp⟩
    have hzero_a : iteratedFDeriv ℝ n (⇑ψ) (x + a) = 0 := by
      by_contra hne
      exact hx_not_a (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_a0 : iteratedFDeriv ℝ n (⇑ψ) (x + a0) = 0 := by
      by_contra hne
      exact hx_not_a0 (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_euclidean_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a0) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)]
      simp [hzero_a, hzero_a0]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

end SCV
