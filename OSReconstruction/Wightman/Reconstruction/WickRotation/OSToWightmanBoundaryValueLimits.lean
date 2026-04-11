/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.SCV.VladimirovTillmann

/-!
# OS to Wightman Boundary Value Limits

This module packages the already-proved OS-side `t → 0+` limits of the
`singleSplit_xiShift` holomorphic traces. The point is to isolate the genuine
remaining gap on the active OS route:

- the positive-real `xiShift` shell already converges to the Euclidean/OS term;
- what still remains is the Wightman-side boundary-value identification, not the
  semigroup-side limit.
-/

open scoped Classical NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem unflatten_add_flatTimeShiftDirection_local {n : ℕ}
    (u : Fin (n * (d + 1)) → ℝ) (t : ℝ) :
    (flattenCLEquivReal n (d + 1)).symm (u + t • flatTimeShiftDirection d n) =
      fun i => ((flattenCLEquivReal n (d + 1)).symm u i) - timeShiftVec d t := by
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [sub_eq_add_neg]
  · simp [flatTimeShiftDirection, timeShiftVec, hμ]

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_eq_unflatten_translate_local {n : ℕ}
    (t : ℝ) (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) t f =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (t • flatTimeShiftDirection d n)
          (flattenSchwartzNPoint (d := d) f)) := by
  ext x
  simp [SCV.translateSchwartz_apply, unflatten_add_flatTimeShiftDirection_local]

omit [NeZero d] in
private theorem hasCompactSupport_flattenSchwartzNPoint_local {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    HasCompactSupport
      ((flattenSchwartzNPoint (d := d) f :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
  simpa [flattenSchwartzNPoint] using
    hf.comp_homeomorph ((flattenCLEquivReal n (d + 1)).symm.toHomeomorph)

omit [NeZero d] in
private theorem tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport_local {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t f) (nhds t₀)
      (nhds (timeShiftSchwartzNPoint (d := d) t₀ f)) := by
  let ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f
  have hψ : HasCompactSupport ((ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
      (Fin (n * (d + 1)) → ℝ) → ℂ) :=
    hasCompactSupport_flattenSchwartzNPoint_local (d := d) f hf
  have hη : Continuous (fun t : ℝ => t • flatTimeShiftDirection d n) :=
    continuous_id.smul continuous_const
  have hflat_full :
      Filter.Tendsto
        (fun s : Fin (n * (d + 1)) → ℝ => SCV.translateSchwartz s ψ)
        (nhds (t₀ • flatTimeShiftDirection d n))
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ
      (t₀ • flatTimeShiftDirection d n)
  have hflat :
      Filter.Tendsto
        (fun t : ℝ => SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ)
        (nhds t₀)
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    hflat_full.comp (hη.tendsto t₀)
  have hunflat :
      Filter.Tendsto
        (fun t : ℝ =>
          unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ))
        (nhds t₀)
        (nhds
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ))) :=
    (((unflattenSchwartzNPoint (d := d) :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n).continuous).tendsto
      _).comp hflat
  simpa [ψ, timeShiftSchwartzNPoint_eq_unflatten_translate_local] using hunflat

/-- Compact-support continuity of the reconstructed Wightman pairing along real
time shifts of the right factor.

This is the exact continuity input needed to turn a positive-real identification
of the chosen `singleSplit_xiShift` holomorphic trace into the current theorem-3
limit hypothesis `hHlimit`. -/
theorem tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g))) := by
  have hshift :
      Filter.Tendsto
        (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t g)
        (nhds 0)
        (nhds g) := by
    have hzeroVec : timeShiftVec d 0 = 0 := by
      ext μ
      refine Fin.cases ?_ ?_ μ
      · simp [timeShiftVec]
      · intro i
        simp [timeShiftVec]
    have hzero : timeShiftSchwartzNPoint (d := d) 0 g = g := by
      ext x
      simp [hzeroVec]
    simpa [hzero] using
      tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport_local (d := d) g hg_compact 0
  have hconj :
      Filter.Tendsto
        (fun t : ℝ => f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
        (nhds 0)
        (nhds (f.conjTensorProduct g)) := by
    exact ((SchwartzMap.conjTensorProduct_continuous_right f).tendsto g).comp hshift
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
        (nhds 0)
        (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g))) := by
    exact ((bvt_W_continuous (d := d) OS lgc (n + m)).tendsto
      (f.conjTensorProduct g)).comp hconj
  exact hW.mono_left nhdsWithin_le_nhds

/-- Flattened dual-cone support package for the reconstructed Wightman
boundary values. This discharges the multivariate spectral-support input from
the merged `spectrum_condition` data once and for all on the honest current
theorem surface. -/
private theorem exists_flattened_bvt_W_dualCone_distribution
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone
          ((flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n) Tflat ∧
        ∀ (φ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ),
          bvt_W OS lgc n (unflattenSchwartzNPoint (d := d) φ) =
            Tflat (physicsFourierFlatCLM φ) := by
  let Wcl : SchwartzNPoint d n →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := bvt_W OS lgc n
          map_add' := (bvt_W_linear (d := d) OS lgc n).map_add
          map_smul' := (bvt_W_linear (d := d) OS lgc n).map_smul }
      cont := bvt_W_continuous (d := d) OS lgc n }
  have hWcl : ∀ f : SchwartzNPoint d n, Wcl f = bvt_W OS lgc n f := by
    intro f
    rfl
  have hC_open : IsOpen (ForwardConeAbs d n) := forwardConeAbs_isOpen d n
  have hC_conv : Convex ℝ (ForwardConeAbs d n) := forwardConeAbs_convex d n
  have hC_cone : IsCone (ForwardConeAbs d n) := by
    intro y hy t ht
    exact forwardConeAbs_smul d n t ht y hy
  have hC_salient : IsSalientCone (ForwardConeAbs d n) :=
    forwardConeAbs_salient d n
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n)
        (TubeDomainSetPi (ForwardConeAbs d n)) := by
    simpa [forwardTube_eq_imPreimage] using bvt_F_holomorphic (d := d) OS lgc n
  have hF_growth :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ TubeDomainSetPi (ForwardConeAbs d n) →
          ‖bvt_F OS lgc n z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    have hGrowthPkg :
        ∃ (C_bd : ℝ) (N : ℕ),
          0 < C_bd ∧
          ∀ z ∈ ForwardTube d n,
            ‖bvt_F OS lgc n z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
      rcases (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec with
        ⟨_hhol, hrest⟩
      rcases hrest with ⟨_hF_euclid, hrest⟩
      rcases hrest with ⟨_hF_perm, hrest⟩
      rcases hrest with ⟨_hF_trans, hrest⟩
      exact hrest.2
    obtain ⟨C_bd, N, hC_pos, hbound⟩ := hGrowthPkg
    refine ⟨C_bd, N, hC_pos, ?_⟩
    intro z hz
    simpa [forwardTube_eq_imPreimage] using
      hbound z (by simpa [forwardTube_eq_imPreimage] using hz)
  have hF_bv :
      ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ ForwardConeAbs d n →
        ∀ (φ : SchwartzNPoint d n),
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * φ x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Wcl φ)) := by
    intro η hη φ
    rw [hWcl]
    exact bvt_boundary_values (d := d) OS lgc n φ η
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).2 hη)
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    bv_implies_fourier_support (C := ForwardConeAbs d n)
      hC_open hC_conv hC_cone hC_salient
      (F := bvt_F OS lgc n) hF_holo hF_growth Wcl hF_bv
  refine ⟨Tflat, hTflat_supp, ?_⟩
  intro φ
  simpa [Wcl, unflattenSchwartzNPoint] using hTflat_repr φ

/-- Reindex a flattened sum that only samples the time-coordinate slots. -/
private theorem sum_over_flat_timeSlots
    {n : ℕ}
    (a : Fin n → ℝ)
    (ξ : Fin (n * (d + 1)) → ℝ) :
    (∑ i, (if (finProdFinEquiv.symm i).2 = 0 then a ((finProdFinEquiv.symm i).1) else 0) * ξ i) =
      ∑ k : Fin n, a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
  classical
  symm
  simpa [Fintype.sum_prod_type] using
    (Fintype.sum_bijective
      (fun p : Fin n × Fin (d + 1) => finProdFinEquiv p)
      finProdFinEquiv.bijective
      (fun p : Fin n × Fin (d + 1) => (if p.2 = 0 then a p.1 else 0) * ξ (finProdFinEquiv p))
      (fun i : Fin (n * (d + 1)) =>
        (if (finProdFinEquiv.symm i).2 = 0 then a ((finProdFinEquiv.symm i).1) else 0) * ξ i)
      (by
        intro p
        simp))

/-- Correct sign geometry for the flattened Stage-5 blocker: any frequency
vector in the dual cone of the flattened absolute forward cone pairs
nonpositively with `flatTimeShiftDirection`.

The sign is subtle but important. `translateSchwartz t₀ ψ` is defined by
`x ↦ ψ (x + t₀)`, while `flatTimeShiftDirection` already has `-1` in every time
slot. So the surviving one-variable orbit theorem must use the nonpositive
pairing orientation `⟨ξ, v⟩ ≤ 0`, not the reversed sign that earlier chat
sketches implicitly assumed. -/
private theorem flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n : ℕ}
    {ξ : Fin (n * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n)) :
    ∑ i, flatTimeShiftDirection d n i * ξ i ≤ 0 := by
  classical
  let S : ℝ := ∑ k : Fin n, ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
  have hS_nonneg : 0 ≤ S := by
    by_contra hS
    have hSneg : S < 0 := lt_of_not_ge hS
    let W : ℝ := ∑ k : Fin n, (k : ℝ) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
    let ε : ℝ := (-S) / (2 * (|W| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply div_pos
      · linarith
      · positivity
    let yε : Fin n → Fin (d + 1) → ℝ :=
      fun k μ => if μ = 0 then (1 + (k : ℝ) * ε : ℝ) else 0
    let e0 : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
    have he0 : InOpenForwardCone d e0 := by
      constructor
      · simp [e0]
      · simp [e0, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hεe0 : InOpenForwardCone d (ε • e0) :=
      inOpenForwardCone_smul d ε hε_pos e0 he0
    have hyε_mem : yε ∈ ForwardConeAbs d n := by
      intro k
      by_cases hk : (k : ℕ) = 0
      · convert he0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [yε, e0, hk]
        · simp [yε, e0, hk, hμ]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
        have hkcast : (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) := Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
          have hreal : ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
            exact_mod_cast hnat
          linarith
        convert hεe0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          have hmain :
              (1 + (k : ℝ) * ε) -
                  (1 + ((((k : ℕ) - 1 : ℕ) : ℝ)) * ε) = ε := by
            nlinarith [hkcast]
          simp [yε, e0, hk, Pi.smul_apply, smul_eq_mul, hmain]
        · simp [yε, e0, hk, hμ, Pi.smul_apply, smul_eq_mul]
    have hpair_nonneg :
        0 ≤ ∑ i, (flattenCLEquivReal n (d + 1) yε) i * ξ i := by
      exact (mem_dualConeFlat.mp hξ)
        ((flattenCLEquivReal n (d + 1)) yε) ⟨yε, hyε_mem, rfl⟩
    have hsum_rewrite :
        (∑ i, (flattenCLEquivReal n (d + 1) yε) i * ξ i) = S + ε * W := by
      calc
        (∑ i, (flattenCLEquivReal n (d + 1) yε) i * ξ i)
            = ∑ k : Fin n, (1 + (k : ℝ) * ε) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
              simpa [yε, flattenCLEquivReal_apply] using
                (sum_over_flat_timeSlots (d := d)
                  (a := fun k : Fin n => (1 + (k : ℝ) * ε : ℝ)) ξ)
        _ = ∑ k : Fin n,
              (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
                ((k : ℝ) * ε) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
        _ = ∑ k : Fin n, ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
              ∑ k : Fin n, ((k : ℝ) * ε) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
              rw [Finset.sum_add_distrib]
        _ = S + ε * W := by
              have hcomm :
                  ∑ k : Fin n, ((k : ℝ) * ε) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) =
                    ε * ∑ k : Fin n, (k : ℝ) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                calc
                  ∑ k : Fin n, ((k : ℝ) * ε) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
                      = ∑ k : Fin n, ε * ((k : ℝ) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          ring
                  _ = ε * ∑ k : Fin n, (k : ℝ) * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                          rw [Finset.mul_sum]
              simpa [S, W] using congrArg (fun t => ∑ k : Fin n,
                ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) + t) hcomm
    have hW_bound : ε * W ≤ (-S) / 2 := by
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hstep1 : ε * W ≤ ε * |W| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self W) hε_nonneg
      have hstep2 : ε * |W| ≤ (-S) / 2 := by
        have hratio : |W| / (|W| + 1) ≤ (1 : ℝ) := by
          have hne : (|W| + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hne]
          nlinarith [abs_nonneg W]
        have hrepr : ε * |W| = ((-S) / 2) * (|W| / (|W| + 1)) := by
          have hne : 2 * (|W| + 1) ≠ 0 := by positivity
          dsimp [ε]
          field_simp [hne]
        rw [hrepr]
        have hcoeff_nonneg : 0 ≤ (-S) / 2 := by linarith
        simpa using mul_le_mul_of_nonneg_left hratio hcoeff_nonneg
      exact le_trans hstep1 hstep2
    rw [hsum_rewrite] at hpair_nonneg
    linarith [hpair_nonneg, hW_bound, hSneg]
  have hsum_eq :
      ∑ i, flatTimeShiftDirection d n i * ξ i = -S := by
    change ∑ i,
        (if (finProdFinEquiv.symm i).2 = 0 then (-1 : ℝ) else 0) * ξ i = -S
    rw [sum_over_flat_timeSlots (d := d) (a := fun _ : Fin n => (-1 : ℝ)) ξ]
    simpa [S]
  rw [hsum_eq]
  linarith

/-- Translation becomes multiplication by the expected phase under the
physics-convention flat Fourier transform. This is the first concrete
frequency-space ingredient for the flattened Stage-5 spectral theorem. -/
private theorem physicsFourierFlatCLM_translateSchwartz_apply
    {m : ℕ}
    (a : Fin m → ℝ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (ξ : Fin m → ℝ) :
    physicsFourierFlatCLM (SCV.translateSchwartz a ψ) ξ =
      Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
        physicsFourierFlatCLM ψ ξ := by
  rw [← physicsFourierFlatCLM_integral, ← physicsFourierFlatCLM_integral]
  let g : (Fin m → ℝ) → ℂ := fun x =>
    Complex.exp (Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))) * ψ x
  have hg_shift :
      (fun x : Fin m → ℝ => g (x + a)) =
        (fun x : Fin m → ℝ =>
          Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) *
            SCV.translateSchwartz a ψ x) := by
    funext x
    simp [g, SCV.translateSchwartz_apply]
  calc
    ∫ x : Fin m → ℝ,
        Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) *
          SCV.translateSchwartz a ψ x
      = ∫ x : Fin m → ℝ, g (x + a) := by
          simp [hg_shift]
    _ = ∫ x : Fin m → ℝ, g x := by
          simpa [g] using MeasureTheory.integral_add_right_eq_self g a
    _ = ∫ x : Fin m → ℝ,
          Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
            (Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          dsimp [g]
          have hsum :
              Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ)) =
                -(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ)) +
                  Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
            calc
              Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))
                  = ∑ i, Complex.I * ((((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))) := by
                      rw [Finset.mul_sum]
              _ = ∑ i, (Complex.I * ((x i : ℂ) * (ξ i : ℂ)) -
                    Complex.I * ((a i : ℂ) * (ξ i : ℂ))) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = -(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ)) +
                    Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
                      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
                      ring
          rw [hsum, Complex.exp_add]
          simp [mul_assoc]
    _ = Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
          ∫ x : Fin m → ℝ,
            Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))))
              (fun x : Fin m → ℝ =>
                Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x))

private theorem fourierInv_eq_cexp_integral_local
    (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourierInv φ ξ =
      ∫ x : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * φ x := by
  have hcoe :
      FourierTransform.fourierInv φ ξ =
        FourierTransform.fourierInv (φ : ℝ → ℂ) ξ := by
    simpa using congrArg (fun g => g ξ) (SchwartzMap.fourierInv_coe (f := φ))
  rw [hcoe, Real.fourierInv_eq' (f := (φ : ℝ → ℂ)) (w := ξ)]
  congr 1
  ext v
  have hinner : ∀ a b : ℝ, @inner ℝ ℝ _ a b = b * a := by
    intro a b
    simp [inner, mul_comm]
  simp only [smul_eq_mul, hinner, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- One-variable phase evaluation for the current flattened Stage-5 route:
pairing a pure oscillatory phase against the Fourier transform of a Schwartz
test recovers the test at the matching nonnegative frequency. -/
private theorem integral_phase_mul_fourierTransform_eq_eval
    (χ : SchwartzMap ℝ ℂ)
    (lam : ℝ) :
    ∫ t : ℝ,
      Complex.exp (-(Complex.I * (lam : ℂ) * t)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t =
      χ (-lam / (2 * Real.pi)) := by
  have hfourierInv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) χ) (-lam / (2 * Real.pi)) =
        χ (-lam / (2 * Real.pi)) := by
    simpa using
      congrArg
        (fun f : SchwartzMap ℝ ℂ => f (-lam / (2 * Real.pi)))
        (FourierTransform.fourierInv_fourier_eq χ)
  rw [fourierInv_eq_cexp_integral_local
      (φ := (SchwartzMap.fourierTransformCLM ℂ) χ)
      (ξ := -lam / (2 * Real.pi))] at hfourierInv
  calc
    ∫ t : ℝ,
        Complex.exp (-(Complex.I * (lam : ℂ) * t)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t
      =
        ∫ t : ℝ,
          Complex.exp (2 * Real.pi * Complex.I * ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with t
              congr 2
              have harg :
                  2 * Real.pi * Complex.I * ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ) =
                    -(Complex.I * (lam : ℂ) * t) := by
                have hscalar_real :
                    (2 * Real.pi) * (-lam / (2 * Real.pi)) * t = -(lam * t) := by
                  field_simp [Real.pi_ne_zero]
                have hscalar :
                    ((2 * Real.pi : ℂ) *
                        (((-lam / (2 * Real.pi) : ℝ) : ℂ))) * (t : ℂ) =
                      -((lam : ℂ) * t) := by
                  exact_mod_cast hscalar_real
                calc
                  2 * Real.pi * Complex.I * ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (t : ℂ)
                      = Complex.I *
                          ((((2 * Real.pi : ℂ) *
                              (((-lam / (2 * Real.pi) : ℝ) : ℂ))) * (t : ℂ))) := by
                            ring
                  _ = Complex.I * (-((lam : ℂ) * t)) := by rw [hscalar]
                  _ = -(Complex.I * (lam : ℂ) * t) := by ring
              rw [harg]
    _ = χ (-lam / (2 * Real.pi)) := hfourierInv

/-- Negative-support tests kill the one-variable oscillatory phase whenever the
frequency parameter is nonpositive. This is the exact scalar vanishing used in
the flattened dual-cone Stage-5 support step. -/
private theorem integral_phase_mul_fourierTransform_eq_zero_of_negSupport_of_nonpos
    (χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0)
    {lam : ℝ}
    (hlam : lam ≤ 0) :
    ∫ t : ℝ,
      Complex.exp (-(Complex.I * (lam : ℂ) * t)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t = 0 := by
  rw [integral_phase_mul_fourierTransform_eq_eval (χ := χ) lam]
  by_cases hχ0 : χ (-lam / (2 * Real.pi)) = 0
  · exact hχ0
  · exfalso
    have hmem : -lam / (2 * Real.pi) ∈ Function.support (χ : ℝ → ℂ) :=
      Function.mem_support.mpr hχ0
    have hneg : -lam / (2 * Real.pi) < 0 := hχ_supp _ hmem
    have hnonneg : 0 ≤ -lam / (2 * Real.pi) := by
      have hnum : 0 ≤ -lam := by linarith
      have hden : 0 ≤ 2 * Real.pi := by positivity
      exact div_nonneg hnum hden
    exact (not_lt_of_ge hnonneg hneg).elim

/-- Pointwise dual-cone vanishing for the existing tail-block time-shift
geometry: once the flattened frequency variable lies in the dual cone, the
one-variable oscillatory phase associated with `flatTimeShiftDirection`
annihilates Fourier transforms of negative-support Schwartz tests. -/
private theorem integral_flatTimeShiftDirection_phase_mul_fourierTransform_eq_zero_of_negSupport
    {n : ℕ}
    (χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0)
    {ξ : Fin (n * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n)) :
    ∫ t : ℝ,
      Complex.exp
          (-(Complex.I * ((∑ i, flatTimeShiftDirection d n i * ξ i : ℝ) : ℂ) * t)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t = 0 := by
  exact integral_phase_mul_fourierTransform_eq_zero_of_negSupport_of_nonpos
    (χ := χ) hχ_supp
    (flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) hξ)

 /-
/-- Tail-block version of `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:
after inserting the right-block time-shift vector into the full flattened
`(n+m)`-point space, every dual-cone frequency still pairs nonpositively with
that inserted translation direction. This is the exact geometry needed by the
final full-flat spectral assembly. -/
private theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i ≤ 0 := by
  classical
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  have hS_nonneg : 0 ≤ S := by
    by_contra hS
    have hSneg : S < 0 := lt_of_not_ge hS
    let W : ℝ :=
      ∑ k : Fin (n + m),
        (if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)) *
          ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
    let ε : ℝ := (-S) / (2 * (|W| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply div_pos
      · linarith
      · positivity
    let yε : Fin (n + m) → Fin (d + 1) → ℝ :=
      fun k μ =>
        if μ = 0 then
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
        else 0
    let e0 : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
    have he0 : InOpenForwardCone d e0 := by
      constructor
      · simp [e0]
      · simp [e0, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hεe0 : InOpenForwardCone d (ε • e0) :=
      inOpenForwardCone_smul d ε hε_pos e0 he0
    have hyε_mem : yε ∈ ForwardConeAbs d (n + m) := by
      intro k
      by_cases hk0 : (k : ℕ) = 0
      · have hk_nat : (k : ℕ) = 0 := hk0
        have hk_zero : (k : ℝ) = 0 := by exact_mod_cast hk_nat
        convert inOpenForwardCone_smul d
          (if (0 : ℕ) < n then (1 : ℝ) * ε else (1 : ℝ))
          (by
            by_cases hn : 0 < n
            · simp [hn, hε_pos]
            · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
              simp [hn0])
          e0 he0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          by_cases hn : 0 < n
          · have hk_lt : (k : ℕ) < n := by simpa [hk0] using hn
            simp [yε, e0, hk0, hk_zero, hk_lt, hn, Pi.smul_apply, smul_eq_mul]
          · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
            simp [yε, e0, hk0, hk_zero, hn0, Pi.smul_apply, smul_eq_mul]
        · simp [yε, e0, hk0, hμ, Pi.smul_apply, smul_eq_mul]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
        by_cases hk_lt : (k : ℕ) < n
        · have hkcast :
            ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              exact_mod_cast hnat
          convert hεe0 using 1
          ext μ
          by_cases hμ : μ = 0
          · subst hμ
            have hkprev_lt : ((k : ℕ) - 1) < n := by omega
            have hmain :
                (((k : ℝ) + 1) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = ε := by
              nlinarith [hkcast]
            simp [yε, e0, hk_lt, hk0, Pi.smul_apply, smul_eq_mul, hmain, hkprev_lt]
          · simp [yε, e0, hk_lt, hk0, hμ, Pi.smul_apply, smul_eq_mul]
        · by_cases hk_eq : (k : ℕ) = n
          · convert he0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              have hkcast : (k : ℝ) = (n : ℝ) := by exact_mod_cast hk_eq
              have hprev_cast :
                  ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
                have hnat : (k : ℕ) - 1 + 1 = n := by
                  rw [hk_eq]
                  exact Nat.sub_add_cancel (show 1 ≤ n from hn_pos)
                exact_mod_cast hnat
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = 1 := by
                nlinarith [hkcast, hprev_cast]
              simpa [yε, e0, hk_lt, hk_eq, hk0, hn0_ne,
                hkprev_lt, hn_pos, Pi.smul_apply, smul_eq_mul] using hmain
            · have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              simp [yε, e0, hk_lt, hk_eq, hk0, hn0_ne, hkprev_lt,
                hn_pos, hμ, Pi.smul_apply, smul_eq_mul]
          · have hk_gt : n < (k : ℕ) := by omega
            have hkprev_ge : n ≤ (k : ℕ) - 1 := by omega
            have hkprev_not_lt : ¬ ((k : ℕ) - 1 < n) := by omega
            have hkcast :
                (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              have hreal : ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
                exact_mod_cast hnat
              linarith
            convert hεe0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (1 + ((((k : ℕ) - 1 : ℕ) : ℝ)) * ε) = ε := by
                nlinarith [hkcast]
              simp [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0,
                Pi.smul_apply, smul_eq_mul, hmain]
            · simpa [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0, hμ,
                Pi.smul_apply, smul_eq_mul]
    have hpair_nonneg :
        0 ≤ ∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i := by
      exact (mem_dualConeFlat.mp hξ)
        ((flattenCLEquivReal (n + m) (d + 1)) yε) ⟨yε, hyε_mem, rfl⟩
    have hsum_rewrite :
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i) = S + ε * W := by
      let a : Fin (n + m) → ℝ :=
        fun k =>
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
      let b : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else 1
      let c : Fin (n + m) → ℝ :=
        fun k => if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)
      calc
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i)
            = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                simpa [yε, a, flattenCLEquivReal_apply] using
                  (sum_over_flat_timeSlots (d := d) (a := a) ξ)
        _ = ∑ k : Fin (n + m),
              (b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
                ε * (c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hk_lt : (k : ℕ) < n
              · simp [a, b, c, hk_lt]
                ring
              · simp [a, b, c, hk_lt]
                ring
        _ = (∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) +
              ε * (∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = S + ε * W := by
              have hb :
                  ∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = S := by
                rw [Fin.sum_univ_add]
                simp [b, S]
              have hc :
                  ∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = W := by
                simp [c, W]
              rw [hb, hc]
    have hW_bound : ε * W ≤ (-S) / 2 := by
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hstep1 : ε * W ≤ ε * |W| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self W) hε_nonneg
      have hstep2 : ε * |W| ≤ (-S) / 2 := by
        have hratio : |W| / (|W| + 1) ≤ (1 : ℝ) := by
          have hne : (|W| + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hne]
          nlinarith [abs_nonneg W]
        have hrepr : ε * |W| = ((-S) / 2) * (|W| / (|W| + 1)) := by
          have hne : 2 * (|W| + 1) ≠ 0 := by positivity
          dsimp [ε]
          field_simp [hne]
        rw [hrepr]
        have hcoeff_nonneg : 0 ≤ (-S) / 2 := by linarith
        simpa using mul_le_mul_of_nonneg_left hratio hcoeff_nonneg
      exact le_trans hstep1 hstep2
    rw [hsum_rewrite] at hpair_nonneg
    linarith [hpair_nonneg, hW_bound, hSneg]
  let vEff : Fin ((n + m) * (d + 1)) → ℝ :=
    ((OSReconstruction.castFinCLE
      (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
      (OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m)))
  let y : Fin (n + m) → Fin (d + 1) → ℝ :=
    (flattenCLEquivReal (n + m) (d + 1)).symm vEff
  have hsplitFirst :
      splitFirst n m y = 0 := by
    dsimp [y, vEff]
    rw [splitFirst_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m))]
    simp
  have hsplitLast :
      splitLast n m y =
        (flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m) := by
    dsimp [y, vEff]
    rw [splitLast_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTimeShiftDirection d m))]
    simp
  have hy_formula :
      ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
        y k μ = if μ = 0 then if (k : ℕ) < n then 0 else -1 else 0 := by
    intro k μ
    by_cases hk : (k : ℕ) < n
    · let k' : Fin n := ⟨k, hk⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval :
          y k μ = 0 := by
        have h := congrArg (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      simp [hk, hval]
    · let j : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n j = k := by
        apply Fin.ext
        simp [j]
        omega
      have h := congrArg (fun z : Fin m → Fin (d + 1) → ℝ => z j) hsplitLast
      have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
      have htail :
          y k μ = ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ := by
        simpa [j, hk_tail] using h'
      have htail_formula :
          ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ =
            if μ = 0 then -1 else 0 := by
        simp [flatTimeShiftDirection]
      simp [hk, htail, htail_formula]
  have hsum_eq :
      ∑ i, vEff i * ξ i = -S := by
    let a : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else -1
    calc
      ∑ i, vEff i * ξ i
          = ∑ i, (flattenCLEquivReal (n + m) (d + 1) y) i * ξ i := by
              simp [y, vEff]
      _ = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
            simpa [a, hy_formula, flattenCLEquivReal_apply] using
              (sum_over_flat_timeSlots (d := d) (a := a) ξ)
      _ = -S := by
            rw [Fin.sum_univ_eq_sum_range]
            rw [Finset.sum_range_add]
            have hhead_zero :
                ∑ k in Finset.range n,
                  a ⟨k, by omega⟩ *
                    ξ (finProdFinEquiv (⟨k, by omega⟩, (0 : Fin (d + 1)))) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro k hk
              have hk_lt' : ((⟨k, by omega⟩ : Fin (n + m)) : ℕ) < n := by simpa
              simp [a, hk_lt']
            have htail :
                ∑ k in Finset.range m,
                  a ⟨n + k, by omega⟩ *
                    ξ (finProdFinEquiv (⟨n + k, by omega⟩, (0 : Fin (d + 1)))) = -S := by
              rw [S, Fin.sum_univ_eq_sum_range]
              refine congrArg Neg.neg ?_
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk_not_lt : ¬ ((⟨n + k, by omega⟩ : Fin (n + m)) : ℕ) < n := by omega
              simp [a, hk_not_lt]
            rw [hhead_zero, zero_add, htail]
  dsimp [vEff]
  rw [hsum_eq]
  linarith

-/

 /-
/-- The inserted full-flat tail time-shift vector pairs with any frequency
vector as the negative sum of the tail-block time-frequency coordinates.

This is just the algebraic content of the inserted-tail geometry. It does not
yet use the dual-cone hypothesis; that analytic sign step remains the live
blocker. -/
private theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
    {n m : ℕ}
    (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i =
      - ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1)))) := by
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  let xSplit : Fin (n * (d + 1) + m * (d + 1)) → ℝ :=
    OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m)
  let vEff : Fin ((n + m) * (d + 1)) → ℝ :=
    ((OSReconstruction.castFinCLE
      (by ring : (n + m) * (d + 1) = n * (d + 1) + m * (d + 1))).symm xSplit)
  have hvEff_targetVec :
      vEff =
        ((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))) xSplit) := by
    ext i
    rfl
  let y : Fin (n + m) → Fin (d + 1) → ℝ :=
    (flattenCLEquivReal (n + m) (d + 1)).symm vEff
  have hsplitFirst :
      splitFirst n m y = 0 := by
    dsimp [y, vEff]
    rw [splitFirst_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simp
  have hsplitLast :
      splitLast n m y =
        (flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m) := by
    dsimp [y, vEff]
    rw [splitLast_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simp
  have hy_formula :
      ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
        y k μ = if μ = 0 then if (k : ℕ) < n then 0 else -1 else 0 := by
    intro k μ
    by_cases hk : (k : ℕ) < n
    · let k' : Fin n := ⟨k, hk⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval :
          y k μ = 0 := by
        have h := congrArg (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      simp [hk, hval]
    · let j : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n j = k := by
        apply Fin.ext
        simp [j, Fin.natAdd]
        omega
      have hval :
          y k μ =
            ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ := by
        have h := congrArg (fun z : Fin m → Fin (d + 1) → ℝ => z j) hsplitLast
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [splitLast, j, hk_tail] using h'
      have hflat :
          ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ =
            if μ = 0 then -1 else 0 := by
        change flatTimeShiftDirection d m (finProdFinEquiv (j, μ)) = _
        simp [flatTimeShiftDirection]
      simp [hk, hval, hflat]
  have hsum_eq :
      ∑ i, vEff i * ξ i = -S := by
    change ∑ i,
        (if (finProdFinEquiv.symm i).2 = 0 then
            if ((finProdFinEquiv.symm i).1 : ℕ) < n then 0 else (-1 : ℝ)
          else 0) * ξ i = -S
    rw [sum_over_flat_timeSlots
      (d := d)
      (a := fun k : Fin (n + m) => if (k : ℕ) < n then (0 : ℝ) else -1) ξ]
    have htail :
        ∑ k : Fin (n + m),
          (if (k : ℕ) < n then (0 : ℝ) else -1) *
            ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = -S := by
      rw [show ∑ k : Fin (n + m),
            (if (k : ℕ) < n then (0 : ℝ) else -1) *
              ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) =
            ∑ k in Finset.range (n + m),
              (if k < n then (0 : ℝ) else -1) *
                ξ (finProdFinEquiv (⟨k, by omega⟩, (0 : Fin (d + 1)))) by
            simpa using
              (Fin.sum_univ_eq_sum_range
                (f := fun k : Fin (n + m) =>
                  (if (k : ℕ) < n then (0 : ℝ) else -1) *
                    ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))))]
      rw [Finset.sum_range_add]
      have hhead_zero :
          ∑ k in Finset.range n,
            (if k < n then (0 : ℝ) else -1) *
              ξ (finProdFinEquiv (⟨k, by omega⟩, (0 : Fin (d + 1)))) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        simp [hk]
      have htail_eq :
          ∑ k in Finset.range m,
            (if n + k < n then (0 : ℝ) else -1) *
              ξ (finProdFinEquiv (⟨n + k, by omega⟩, (0 : Fin (d + 1)))) = -S := by
        rw [S, Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk_not_lt : ¬ ((⟨n + k, by omega⟩ : Fin (n + m)) : ℕ) < n := by omega
        congr 2
        · simp [hk_not_lt]
        · congr 1
          apply congrArg (fun i : Fin (n + m) => finProdFinEquiv (i, (0 : Fin (d + 1))))
          apply Fin.ext
          simp [Fin.natAdd]
      rw [hhead_zero, zero_add, htail_eq]
    simpa [hy_formula] using htail
  dsimp [vEff]
  rw [hsum_eq]

-/

/-- Reindexing a translated Schwartz function is the same as translating the
reindexed Schwartz function by the correspondingly reindexed vector. This lets
the flattened Stage-5 spectral step use the already-proved Fourier shift
theorem on the exact full-flat tensor test surface produced by the support
transfer layer. -/
private theorem reindexSchwartzFin_translateSchwartz
    {a b : ℕ}
    (h : a = b)
    (u : Fin a → ℝ)
    (F : SchwartzMap (Fin a → ℝ) ℂ) :
    OSReconstruction.reindexSchwartzFin h (SCV.translateSchwartz u F) =
      SCV.translateSchwartz
        ((OSReconstruction.castFinCLE h) u)
        (OSReconstruction.reindexSchwartzFin h F) := by
  ext x
  rw [OSReconstruction.reindexSchwartzFin_apply, SCV.translateSchwartz_apply,
    SCV.translateSchwartz_apply, OSReconstruction.reindexSchwartzFin_apply]
  simp

/-- Fourier-shift specialization on the exact full-flat translated tensor
surface produced by `exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution_translate`.
After reindexing the split head/tail block back to the literal `(n+m)`-point
flattening, the real-time tail translation still appears as the expected
oscillatory phase. -/
private theorem physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply
    {n m : ℕ}
    (a : Fin (m * (d + 1)) → ℝ)
    (Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ)
    (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
          (SCV.translateSchwartz
            (OSReconstruction.zeroHeadBlockShift (m := n * (d + 1)) (n := m * (d + 1)) a)
            Ψ)) ξ =
      Complex.exp
          (-(Complex.I *
              ∑ i,
                ((((OSReconstruction.castFinCLE
                  (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
                  (OSReconstruction.zeroHeadBlockShift
                    (m := n * (d + 1)) (n := m * (d + 1)) a)) i : ℝ) : ℂ) *
                  (ξ i : ℂ))) *
        physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
            Ψ) ξ := by
  rw [reindexSchwartzFin_translateSchwartz]
  simpa using
    physicsFourierFlatCLM_translateSchwartz_apply
      ((OSReconstruction.castFinCLE
        (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1)) a))
      (OSReconstruction.reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
        Ψ)
      ξ

/-- The reconstructed Wightman pairing against a fixed left factor is a
continuous linear functional of the right factor. This packages the exact
ambient-side scalar functional used later when building one-variable witnesses
from real-time shifts on the right block. -/
private noncomputable def bvt_W_conjTensorProduct_rightCLM
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) :
    SchwartzNPoint d m →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun g => bvt_W OS lgc (n + m) (f.conjTensorProduct g)
      map_add' := fun g₁ g₂ => by
        rw [SchwartzMap.conjTensorProduct_add_right]
        exact (bvt_W_linear (d := d) OS lgc (n + m)).map_add _ _
      map_smul' := fun c g => by
        rw [SchwartzMap.conjTensorProduct_smul_right]
        exact (bvt_W_linear (d := d) OS lgc (n + m)).map_smul _ _ }
  cont := (bvt_W_continuous (d := d) OS lgc (n + m)).comp
    (SchwartzMap.conjTensorProduct_continuous_right f)

/-- Reindexing the flattened `(n+m)`-point real block into
`n*(d+1) + m*(d+1)` identifies the first block with the first `n` spacetime
variables. -/
private theorem splitFirst_reindex_flatten_symm_eq
    {n m : ℕ}
    (x : Fin (n * (d + 1) + m * (d + 1)) → ℝ) :
    splitFirst n m
        ((flattenCLEquivReal (n + m) (d + 1)).symm
          ((OSReconstruction.castFinCLE (by ring : (n + m) * (d + 1) =
            n * (d + 1) + m * (d + 1))).symm x)) =
      (flattenCLEquivReal n (d + 1)).symm
        (splitFirst (n * (d + 1)) (m * (d + 1)) x) := by
  ext i μ
  change
    x ((finCongr (by ring : (n + m) * (d + 1) =
      n * (d + 1) + m * (d + 1)))
      (finProdFinEquiv (Fin.castAdd m i, μ))) =
    x (Fin.castAdd (m * (d + 1)) (finProdFinEquiv (i, μ)))
  refine congrArg x ?_
  apply Fin.ext
  simp [finProdFinEquiv]

/-- Reindexing the flattened `(n+m)`-point real block into
`n*(d+1) + m*(d+1)` identifies the last block with the final `m` spacetime
variables. -/
private theorem splitLast_reindex_flatten_symm_eq
    {n m : ℕ}
    (x : Fin (n * (d + 1) + m * (d + 1)) → ℝ) :
    splitLast n m
        ((flattenCLEquivReal (n + m) (d + 1)).symm
          ((OSReconstruction.castFinCLE (by ring : (n + m) * (d + 1) =
            n * (d + 1) + m * (d + 1))).symm x)) =
      (flattenCLEquivReal m (d + 1)).symm
        (splitLast (n * (d + 1)) (m * (d + 1)) x) := by
  ext j μ
  change
    x ((finCongr (by ring : (n + m) * (d + 1) =
      n * (d + 1) + m * (d + 1)))
      (finProdFinEquiv (Fin.natAdd n j, μ))) =
    x (Fin.natAdd (n * (d + 1)) (finProdFinEquiv (j, μ)))
  refine congrArg x ?_
  apply Fin.ext
  simp [finProdFinEquiv]
  ring

/-- The inserted full-flat tail time-shift vector pairs with any frequency
vector as the negative sum of the tail-block time-frequency coordinates.

This is just the algebraic content of the inserted-tail geometry. It does not
yet use the dual-cone hypothesis; that analytic sign step remains the live
blocker. -/
private theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
    {n m : ℕ}
    (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i =
      - ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1)))) := by
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  let xSplit : Fin (n * (d + 1) + m * (d + 1)) → ℝ :=
    OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m)
  let vEff : Fin ((n + m) * (d + 1)) → ℝ :=
    ((OSReconstruction.castFinCLE
      (by ring : (n + m) * (d + 1) = n * (d + 1) + m * (d + 1))).symm xSplit)
  have hvEff_targetVec :
      vEff =
        ((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))) xSplit) := by
    ext i
    rfl
  let y : Fin (n + m) → Fin (d + 1) → ℝ :=
    (flattenCLEquivReal (n + m) (d + 1)).symm vEff
  have hsplitFirst :
      splitFirst n m y = 0 := by
    dsimp [y, vEff, xSplit]
    rw [splitFirst_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simpa [xSplit] using
      (splitFirst_zeroHeadBlockShift_eq_zero
        (m := n * (d + 1)) (n := m * (d + 1))
        (a := flatTimeShiftDirection d m))
  have hsplitLast :
      splitLast n m y =
        (flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m) := by
    dsimp [y, vEff, xSplit]
    rw [splitLast_reindex_flatten_symm_eq
      (d := d) (n := n) (m := m)
      (x := xSplit)]
    simpa [xSplit] using
      (splitLast_zeroHeadBlockShift_eq
        (m := n * (d + 1)) (n := m * (d + 1))
        (a := flatTimeShiftDirection d m))
  have hy_formula :
      ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
        y k μ = if μ = 0 then if (k : ℕ) < n then 0 else -1 else 0 := by
    intro k μ
    by_cases hk : (k : ℕ) < n
    · let k' : Fin n := ⟨k, hk⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval :
          y k μ = 0 := by
        have h := congrArg (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      simp [hk, hval]
    · let j : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n j = k := by
        apply Fin.ext
        simp [j, Fin.natAdd]
        omega
      have hval :
          y k μ =
            ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ := by
        have h := congrArg (fun z : Fin m → Fin (d + 1) → ℝ => z j) hsplitLast
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [splitLast, j, hk_tail] using h'
      have hflat :
          ((flattenCLEquivReal m (d + 1)).symm (flatTimeShiftDirection d m)) j μ =
            if μ = 0 then -1 else 0 := by
        change flatTimeShiftDirection d m (finProdFinEquiv (j, μ)) = _
        simp [flatTimeShiftDirection]
      simp [hk, hval, hflat]
  have hvEff_formula :
      ∀ i,
        vEff i =
          (if (finProdFinEquiv.symm i).2 = 0 then
            if (((finProdFinEquiv.symm i).1 : Fin (n + m)) : ℕ) < n then 0 else (-1 : ℝ)
           else 0) := by
    intro i
    have hv :
        (flattenCLEquivReal (n + m) (d + 1) y) i = vEff i := by
      simpa [y] using
        congrArg (fun z : Fin ((n + m) * (d + 1)) → ℝ => z i)
          ((flattenCLEquivReal (n + m) (d + 1)).apply_symm_apply vEff)
    rw [← hv]
    simpa [flattenCLEquivReal_apply] using
      hy_formula (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hsum_eq :
      ∑ i, vEff i * ξ i = -S := by
    calc
      ∑ i, vEff i * ξ i
          = ∑ i,
              (if (finProdFinEquiv.symm i).2 = 0 then
                  if (((finProdFinEquiv.symm i).1 : Fin (n + m)) : ℕ) < n then 0 else (-1 : ℝ)
                else 0) * ξ i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hvEff_formula i]
      _ = -S := by
        rw [sum_over_flat_timeSlots
          (d := d)
          (a := fun k : Fin (n + m) => if (k : ℕ) < n then (0 : ℝ) else -1) ξ]
        rw [Fin.sum_univ_add]
        have hhead_zero :
            (∑ k : Fin n,
              (if ((Fin.castAdd m k : Fin (n + m)) : ℕ) < n then (0 : ℝ) else -1) *
                ξ (finProdFinEquiv (Fin.castAdd m k, (0 : Fin (d + 1))))) = 0 := by
          simp
        have htail_eq :
            (∑ k : Fin m,
              (if ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n then (0 : ℝ) else -1) *
                ξ (finProdFinEquiv (Fin.natAdd n k, (0 : Fin (d + 1))))) = -S := by
          simp [S]
        rw [hhead_zero, zero_add, htail_eq]
  simpa [S, xSplit, hvEff_targetVec] using hsum_eq

/-- Tail-block version of `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:
after inserting the right-block time-shift vector into the full flattened
`(n+m)`-point space, every dual-cone frequency still pairs nonpositively with
that inserted translation direction. This is the exact geometry needed by the
final full-flat spectral assembly. -/
private theorem zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ i,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i ≤ 0 := by
  classical
  let S : ℝ :=
    ∑ j : Fin m, ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  have hS_nonneg : 0 ≤ S := by
    by_contra hS
    have hSneg : S < 0 := lt_of_not_ge hS
    let W : ℝ :=
      ∑ k : Fin (n + m),
        (if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)) *
          ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
    let ε : ℝ := (-S) / (2 * (|W| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply div_pos
      · linarith
      · positivity
    let yε : Fin (n + m) → Fin (d + 1) → ℝ :=
      fun k μ =>
        if μ = 0 then
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
        else 0
    let e0 : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
    have he0 : InOpenForwardCone d e0 := by
      constructor
      · simp [e0]
      · simp [e0, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
    have hεe0 : InOpenForwardCone d (ε • e0) :=
      inOpenForwardCone_smul d ε hε_pos e0 he0
    have hyε_mem : yε ∈ ForwardConeAbs d (n + m) := by
      intro k
      by_cases hk0 : (k : ℕ) = 0
      · have hk_nat : (k : ℕ) = 0 := hk0
        have hk_zero : (k : ℝ) = 0 := by exact_mod_cast hk_nat
        convert inOpenForwardCone_smul d
          (if (0 : ℕ) < n then (1 : ℝ) * ε else (1 : ℝ))
          (by
            by_cases hn : 0 < n
            · simp [hn, hε_pos]
            · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
              simp [hn0])
          e0 he0 using 1
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          by_cases hn : 0 < n
          · have hk_lt : (k : ℕ) < n := by simpa [hk0] using hn
            simp [yε, e0, hk0, hk_zero, hk_lt, hn, Pi.smul_apply, smul_eq_mul]
          · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
            simp [yε, e0, hk0, hk_zero, hn0, Pi.smul_apply, smul_eq_mul]
        · simp [yε, e0, hk0, hμ, Pi.smul_apply, smul_eq_mul]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
        by_cases hk_lt : (k : ℕ) < n
        · have hkcast :
            ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
            have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
              Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
            exact_mod_cast hnat
          convert hεe0 using 1
          ext μ
          by_cases hμ : μ = 0
          · subst hμ
            have hkprev_lt : ((k : ℕ) - 1) < n := by omega
            have hmain :
                (((k : ℝ) + 1) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = ε := by
              nlinarith [hkcast]
            simp [yε, e0, hk_lt, hk0, Pi.smul_apply, smul_eq_mul, hmain, hkprev_lt]
          · simp [yε, e0, hk_lt, hk0, hμ, Pi.smul_apply, smul_eq_mul]
        · by_cases hk_eq : (k : ℕ) = n
          · convert he0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              have hkcast : (k : ℝ) = (n : ℝ) := by exact_mod_cast hk_eq
              have hprev_cast :
                  ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
                have hnat : (k : ℕ) - 1 + 1 = n := by
                  rw [hk_eq]
                  exact Nat.sub_add_cancel (show 1 ≤ n from hn_pos)
                exact_mod_cast hnat
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * ε) = 1 := by
                nlinarith [hkcast, hprev_cast]
              simpa [yε, e0, hk_lt, hk_eq, hk0, hn0_ne,
                hkprev_lt, hn_pos, Pi.smul_apply, smul_eq_mul] using hmain
            · have hn_pos : 0 < n := by omega
              have hn0_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
              have hkprev_lt : ((k : ℕ) - 1) < n := by omega
              simp [yε, e0, hk_lt, hk_eq, hk0, hn0_ne, hkprev_lt,
                hn_pos, hμ, Pi.smul_apply, smul_eq_mul]
          · have hk_gt : n < (k : ℕ) := by omega
            have hkprev_ge : n ≤ (k : ℕ) - 1 := by omega
            have hkprev_not_lt : ¬ ((k : ℕ) - 1 < n) := by omega
            have hkcast :
                (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
              have hnat : (k : ℕ) - 1 + 1 = (k : ℕ) :=
                Nat.sub_add_cancel (show 1 ≤ (k : ℕ) from hkpos)
              have hreal : ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
                exact_mod_cast hnat
              linarith
            convert hεe0 using 1
            ext μ
            by_cases hμ : μ = 0
            · subst hμ
              have hmain :
                  (1 + (k : ℝ) * ε) -
                    (1 + ((((k : ℕ) - 1 : ℕ) : ℝ)) * ε) = ε := by
                nlinarith [hkcast]
              simp [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0,
                Pi.smul_apply, smul_eq_mul, hmain]
            · simpa [yε, e0, hk_lt, hk_eq, hk_gt, hkprev_ge, hkprev_not_lt, hk0, hμ,
                Pi.smul_apply, smul_eq_mul]
    have hpair_nonneg :
        0 ≤ ∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i := by
      exact (mem_dualConeFlat.mp hξ)
        ((flattenCLEquivReal (n + m) (d + 1)) yε) ⟨yε, hyε_mem, rfl⟩
    have hsum_rewrite :
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i) = S + ε * W := by
      let a : Fin (n + m) → ℝ :=
        fun k =>
          if (k : ℕ) < n then (((k : ℝ) + 1) * ε : ℝ)
          else (1 + (k : ℝ) * ε : ℝ)
      let b : Fin (n + m) → ℝ := fun k => if (k : ℕ) < n then 0 else 1
      let c : Fin (n + m) → ℝ :=
        fun k => if (k : ℕ) < n then ((k : ℝ) + 1) else (k : ℝ)
      calc
        (∑ i, (flattenCLEquivReal (n + m) (d + 1) yε) i * ξ i)
            = ∑ k : Fin (n + m), a k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) := by
                simpa [yε, a, flattenCLEquivReal_apply] using
                  (sum_over_flat_timeSlots (d := d) (a := a) ξ)
        _ = ∑ k : Fin (n + m),
              (b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) +
                ε * (c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hk_lt : (k : ℕ) < n
              · simp [a, b, c, hk_lt]
                ring
              · simp [a, b, c, hk_lt]
                ring
        _ = (∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) +
              ε * (∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = S + ε * W := by
              have hb :
                  ∑ k : Fin (n + m), b k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = S := by
                rw [Fin.sum_univ_add]
                simp [b, S]
              have hc :
                  ∑ k : Fin (n + m), c k * ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) = W := by
                simp [c, W]
              rw [hb, hc]
    have hW_bound : ε * W ≤ (-S) / 2 := by
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hstep1 : ε * W ≤ ε * |W| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self W) hε_nonneg
      have hstep2 : ε * |W| ≤ (-S) / 2 := by
        have hratio : |W| / (|W| + 1) ≤ (1 : ℝ) := by
          have hne : (|W| + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hne]
          nlinarith [abs_nonneg W]
        have hrepr : ε * |W| = ((-S) / 2) * (|W| / (|W| + 1)) := by
          have hne : 2 * (|W| + 1) ≠ 0 := by positivity
          dsimp [ε]
          field_simp [hne]
        rw [hrepr]
        have hcoeff_nonneg : 0 ≤ (-S) / 2 := by linarith
        simpa using mul_le_mul_of_nonneg_left hratio hcoeff_nonneg
      exact le_trans hstep1 hstep2
    rw [hsum_rewrite] at hpair_nonneg
    linarith [hpair_nonneg, hW_bound, hSneg]
  rw [zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
    (d := d) (n := n) (m := m) ξ]
  linarith

/-- After flattening and reindexing the real block into head/tail form, the
ambient conjugated tensor product is exactly the ordinary flat tensor product of
the left Borchers conjugate with the right factor. This is the precise
factorization seam needed to turn the live Stage-5 right-block CLM into a
consumer of the full flattened `(n+m)`-point spectral package. -/
private theorem reindex_flattenSchwartzNPoint_conjTensorProduct_eq_tensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    OSReconstruction.reindexSchwartzFin (by ring : (n + m) * (d + 1) =
        n * (d + 1) + m * (d + 1))
      (flattenSchwartzNPoint (d := d) (f.conjTensorProduct g)) =
      (flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
        (flattenSchwartzNPoint (d := d) g) := by
  ext x
  rw [OSReconstruction.reindexSchwartzFin_apply, flattenSchwartzNPoint_apply,
    SchwartzMap.tensorProduct_apply, flattenSchwartzNPoint_apply,
    flattenSchwartzNPoint_apply, SchwartzMap.borchersConj_apply,
    SchwartzMap.conjTensorProduct_apply]
  simp only [splitFirst_reindex_flatten_symm_eq, splitLast_reindex_flatten_symm_eq]

/-- Translating only the tail block of a flat tensor product is the same as
translating the full flat Schwartz function by the corresponding zero-head
block shift. -/
private theorem tensorProduct_translateSchwartz_tail_eq_translate_zeroHeadBlock
    {n m : ℕ}
    (φ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
    (ψ : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ)
    (a : Fin (m * (d + 1)) → ℝ) :
    φ.tensorProduct (SCV.translateSchwartz a ψ) =
      SCV.translateSchwartz
        (OSReconstruction.zeroHeadBlockShift (m := n * (d + 1)) (n := m * (d + 1)) a)
        (φ.tensorProduct ψ) := by
  ext x
  simp [SchwartzMap.tensorProduct_apply, SCV.translateSchwartz_apply]

/-- The fixed-left-factor right-block CLM is not a separate spectral object:
after inserting the left Borchers-conjugate flat tensor factor and reindexing
back to the literal `(n+m)`-point flattening, it is exactly the merged VT
frequency-side distribution for arity `n + m`. This is the precise bridge from
the current Stage-5 right-block theorem surface back to the full multivariate
dual-cone support package. -/
private theorem exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n) :
    ∃ (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone
          ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)) Tflat ∧
        ∀ (ψ : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ),
          ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
            (unflattenSchwartzNPoint (d := d))) ψ =
            Tflat
              (physicsFourierFlatCLM
                (OSReconstruction.reindexSchwartzFin
                  (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
                  ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ))) := by
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc (n + m)
  refine ⟨Tflat, hTflat_supp, ?_⟩
  intro ψ
  have hψ_flat :
      flattenSchwartzNPoint (d := d) (unflattenSchwartzNPoint (d := d) ψ) = ψ := by
    ext u
    simp [flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply]
  have hflat :
      OSReconstruction.reindexSchwartzFin
          (by ring : (n + m) * (d + 1) = n * (d + 1) + m * (d + 1))
          (flattenSchwartzNPoint (d := d)
            (f.conjTensorProduct
              (unflattenSchwartzNPoint (d := d) ψ))) =
        (flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ := by
    simpa [hψ_flat] using
      reindex_flattenSchwartzNPoint_conjTensorProduct_eq_tensorProduct
        (d := d) f (unflattenSchwartzNPoint (d := d) ψ)
  have hflat' := congrArg
      (OSReconstruction.reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))) hflat
  have hfull_left :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d)
            (f.conjTensorProduct (unflattenSchwartzNPoint (d := d) ψ))) =
        f.conjTensorProduct (unflattenSchwartzNPoint (d := d) ψ) := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hfull :
      f.conjTensorProduct (unflattenSchwartzNPoint (d := d) ψ) =
        unflattenSchwartzNPoint (d := d)
          (OSReconstruction.reindexSchwartzFin
            (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
            ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ)) := by
    exact hfull_left.symm.trans
      (congrArg (unflattenSchwartzNPoint (d := d)) hflat')
  calc
    ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d))) ψ
      = bvt_W OS lgc (n + m)
          (f.conjTensorProduct (unflattenSchwartzNPoint (d := d) ψ)) := by
            simp [bvt_W_conjTensorProduct_rightCLM]
    _ = bvt_W OS lgc (n + m)
          (unflattenSchwartzNPoint (d := d)
            (OSReconstruction.reindexSchwartzFin
              (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
              ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ))) := by
            rw [hfull]
    _ = Tflat
          (physicsFourierFlatCLM
            (OSReconstruction.reindexSchwartzFin
              (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
              ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ))) := by
            simpa using hTflat_repr
              (OSReconstruction.reindexSchwartzFin
                (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
                ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct ψ))

/-- Translate-orbit specialization of
`exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution`: the
fixed-left-factor real time shifts of the right block are already represented by
the same full flattened dual-cone distribution, acting on a tail-block
translation of the split flat tensor product. This removes the last hidden
flattening algebra from the live Stage-5 spectral blocker. -/
private theorem exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    ∃ (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone
          ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)) Tflat ∧
        ∀ t : ℝ,
          ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
            (unflattenSchwartzNPoint (d := d)))
            (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
              (flattenSchwartzNPoint (d := d) g)) =
            Tflat
              (physicsFourierFlatCLM
                (OSReconstruction.reindexSchwartzFin
                  (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
                  (SCV.translateSchwartz
                    (OSReconstruction.zeroHeadBlockShift
                      (m := n * (d + 1)) (n := m * (d + 1))
                      (t • flatTimeShiftDirection d m))
                    ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
                      (flattenSchwartzNPoint (d := d) g))))) := by
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution
      (d := d) OS lgc f
  refine ⟨Tflat, hTflat_supp, ?_⟩
  intro t
  have htail :
      (flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
          (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
            (flattenSchwartzNPoint (d := d) g)) =
        SCV.translateSchwartz
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := m * (d + 1))
            (t • flatTimeShiftDirection d m))
          ((flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
            (flattenSchwartzNPoint (d := d) g)) := by
    simpa using tensorProduct_translateSchwartz_tail_eq_translate_zeroHeadBlock
      (d := d) (n := n) (m := m)
      (flattenSchwartzNPoint (d := d) f.borchersConj)
      (flattenSchwartzNPoint (d := d) g)
      (t • flatTimeShiftDirection d m)
  simpa [htail] using
    hTflat_repr
      (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
        (flattenSchwartzNPoint (d := d) g))

/-- Exact flattening rewrite for the ambient time-shift pairing: after fixing
the left factor, translating the right factor in real time is the same as
applying the induced right-factor CLM to the flattened Schwartz function
translated along `flatTimeShiftDirection`.

This is a genuine blocker reduction for the current Stage-5 route. It moves the
time-shift pairing from `SchwartzNPoint` to ordinary Schwartz translation on
`ℝ^{m(d+1)}`, so later spectral arguments can target a fixed CLM on plain
Schwartz space instead of redoing tensor/flattening bookkeeping each time. -/
private theorem bvt_W_conjTensorProduct_timeShift_eq_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (t : ℝ) :
    bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) =
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g)) := by
  simp [bvt_W_conjTensorProduct_rightCLM, timeShiftSchwartzNPoint_eq_unflatten_translate_local]

/-- Stage-5 scalar pairing rewrite on the honest current theorem surface:
after fixing the left factor, pairing the ambient right-time-shift scalar
functional against a one-variable test `χ` is exactly the same as pairing `χ`
against the corresponding flattened-Schwartz translation orbit.

This is a genuine blocker reduction for the live `hzero` seam. It moves the
entire scalar spectral pairing from `SchwartzNPoint` language to ordinary
Schwartz translation on `ℝ^{m(d+1)}`, so the remaining work can target the
flattened translation functional directly instead of repeatedly redoing
tensor/flattening bookkeeping under the integral sign. -/
private theorem integral_bvt_W_conjTensorProduct_timeShift_mul_eq_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (χ : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t =
      ∫ t : ℝ,
        ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
          (unflattenSchwartzNPoint (d := d)))
          (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
            (flattenSchwartzNPoint (d := d) g)) * χ t := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [bvt_W_conjTensorProduct_timeShift_eq_flattened_translate
    (d := d) (OS := OS) (lgc := lgc) f g t]

/-- Fourier-transform specialization of
`integral_bvt_W_conjTensorProduct_timeShift_mul_eq_flattened_translate`.
This is the exact scalar pairing surface occurring in the current Stage-5
spectral-support / paired-vanishing argument. -/
private theorem integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_eq_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (χ : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t =
      ∫ t : ℝ,
        ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
          (unflattenSchwartzNPoint (d := d)))
          (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
            (flattenSchwartzNPoint (d := d) g)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t := by
  simpa using
    integral_bvt_W_conjTensorProduct_timeShift_mul_eq_flattened_translate
      (d := d) (OS := OS) (lgc := lgc) f g
      (SchwartzMap.fourierTransformCLM ℂ χ)

/-- Compact-support continuity of the ambient Wightman pairing along arbitrary
real time shifts of the right factor. This is one of the two direct
`paley_wiener_one_step` inputs for the ambient witness route. -/
private theorem continuous_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Continuous (fun t : ℝ =>
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  have hshift :
      Filter.Tendsto
        (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t g)
        (nhds t₀)
        (nhds (timeShiftSchwartzNPoint (d := d) t₀ g)) := by
    exact tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport_local
      (d := d) g hg_compact t₀
  have hconj :
      Filter.Tendsto
        (fun t : ℝ => f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
        (nhds t₀)
        (nhds (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t₀ g))) := by
    exact ((SchwartzMap.conjTensorProduct_continuous_right f).tendsto
      (timeShiftSchwartzNPoint (d := d) t₀ g)).comp hshift
  exact ((bvt_W_continuous (d := d) OS lgc (n + m)).tendsto
    (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t₀ g))).comp hconj

/-- Compact-support polynomial-growth input for the ambient witness route:
along real time shifts of the right factor, the reconstructed Wightman pairing
against a fixed left factor grows at most polynomially. -/
private theorem hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    SCV.HasPolynomialGrowthOnLine (fun t : ℝ =>
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  classical
  let T : SchwartzNPoint d m →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f
  let ψ : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) g
  let Tflat : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp (unflattenSchwartzNPoint (d := d))
  let q : Seminorm ℂ (SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ) :=
    (normSeminorm ℂ ℂ).comp Tflat.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun h : SchwartzMap (Fin (m * (d + 1)) → ℝ) ℂ => ‖Tflat h‖)
    simpa [q, Seminorm.comp_apply, coe_normSeminorm] using
      continuous_norm.comp Tflat.continuous
  obtain ⟨s, C0, hC0_ne, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ (Fin (m * (d + 1)) → ℝ) ℂ) q hq_cont
  have hD :
      ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧
        ∀ a : Fin (m * (d + 1)) → ℝ,
          (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
            (SCV.translateSchwartz a ψ) ≤
              D * (1 + ‖a‖) ^ p.1 := by
    intro p
    simpa [schwartzSeminormFamily] using
      SCV.seminorm_translateSchwartz_le p.1 p.2 ψ
  choose D hD_nonneg hD_bound using hD
  let η : Fin (m * (d + 1)) → ℝ := flatTimeShiftDirection d m
  let N : ℕ := s.sup Prod.fst
  let A : ℝ := (1 + ‖η‖) ^ N
  let Dsum : ℝ := ∑ p ∈ s, D p * A
  let Cbound : ℝ := (C0 : ℝ) * Dsum + 1
  have hC0_pos : 0 < (C0 : ℝ) := by
    have hC0_ne' : (C0 : ℝ) ≠ 0 := by
      exact_mod_cast hC0_ne
    exact lt_of_le_of_ne C0.2 hC0_ne'.symm
  have hDsum_nonneg : 0 ≤ Dsum := by
    dsimp [Dsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact mul_nonneg (hD_nonneg p) (pow_nonneg (by positivity) _)
  refine ⟨Cbound, N, by
    dsimp [Cbound]
    nlinarith, ?_⟩
  intro t
  let a : Fin (m * (d + 1)) → ℝ := t • η
  let u : ℝ := 1 + ‖a‖
  let v : ℝ := (1 + ‖η‖) * (1 + |t|)
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    positivity
  have hv_ge_one : 1 ≤ v := by
    dsimp [v]
    have h1 : 1 ≤ 1 + ‖η‖ := by nlinarith [norm_nonneg η]
    have h2 : 1 ≤ 1 + |t| := by nlinarith [abs_nonneg t]
    nlinarith
  have hu_le_v : u ≤ v := by
    dsimp [u, v, a]
    rw [norm_smul]
    simpa using
      (show 1 + |t| * ‖η‖ ≤ (1 + ‖η‖) * (1 + |t|) by
        nlinarith [abs_nonneg t, norm_nonneg η])
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ))
          (SCV.translateSchwartz a ψ) ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
          (SCV.translateSchwartz a ψ) := by
    exact Seminorm.le_def.mp
      (Seminorm.finset_sup_le_sum
        (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ) s)
        (SCV.translateSchwartz a ψ)
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
            (SCV.translateSchwartz a ψ) =
          ∑ p ∈ s',
            (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
              (SCV.translateSchwartz a ψ) := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert b s' hb ih =>
        simp [Finset.sum_insert, hb, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
          (SCV.translateSchwartz a ψ) ≤
        Dsum * (1 + |t|) ^ N := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
          (SCV.translateSchwartz a ψ)
        = ∑ p ∈ s,
            (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
              (SCV.translateSchwartz a ψ) := by
              simpa using hsum_apply s
      _ ≤ ∑ p ∈ s, D p * v ^ N := by
            refine Finset.sum_le_sum ?_
            intro p hp
            have hpN : p.1 ≤ N := Finset.le_sup hp
            calc
              (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
                  (SCV.translateSchwartz a ψ)
                ≤ D p * u ^ p.1 := hD_bound p a
              _ ≤ D p * v ^ p.1 := by
                  refine mul_le_mul_of_nonneg_left ?_ (hD_nonneg p)
                  exact pow_le_pow_left₀ hu_nonneg hu_le_v _
              _ ≤ D p * v ^ N := by
                  refine mul_le_mul_of_nonneg_left ?_ (hD_nonneg p)
                  exact pow_le_pow_right₀ hv_ge_one hpN
      _ = (∑ p ∈ s, D p) * v ^ N := by
            simp [Finset.sum_mul]
      _ ≤ Dsum * (1 + |t|) ^ N := by
            have hA_ge_one : 1 ≤ A := by
              dsimp [A]
              exact one_le_pow₀ (by nlinarith [norm_nonneg η])
            have hv_pow :
                v ^ N = A * (1 + |t|) ^ N := by
              dsimp [v, A]
              rw [mul_pow]
            rw [hv_pow]
            calc
              (∑ p ∈ s, D p) * (A * (1 + |t|) ^ N)
                  = ((∑ p ∈ s, D p) * A) * (1 + |t|) ^ N := by ring
              _ ≤ Dsum * (1 + |t|) ^ N := by
                  rw [show (∑ p ∈ s, D p) * A = Dsum by
                    simp [Dsum, Finset.sum_mul]]
  have hmain :
      ‖Tflat (SCV.translateSchwartz a ψ)‖ ≤
        (C0 : ℝ) * (Dsum * (1 + |t|) ^ N) := by
    calc
      ‖Tflat (SCV.translateSchwartz a ψ)‖
          ≤ (C0 • s.sup (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ))
              (SCV.translateSchwartz a ψ) := by
                simpa [q, Seminorm.comp_apply, coe_normSeminorm] using
                  hbound (SCV.translateSchwartz a ψ)
      _ = (C0 : ℝ) *
            (s.sup (schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ))
              (SCV.translateSchwartz a ψ) := by
            rfl
      _ ≤ (C0 : ℝ) *
            ((∑ p ∈ s, schwartzSeminormFamily ℂ (Fin (m * (d + 1)) → ℝ) ℂ p)
              (SCV.translateSchwartz a ψ)) := by
            gcongr
      _ ≤ (C0 : ℝ) * (Dsum * (1 + |t|) ^ N) := by
            gcongr
  have hEq :
      bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) =
        Tflat (SCV.translateSchwartz a ψ) := by
    simpa [T, Tflat, ψ, a, η] using
      bvt_W_conjTensorProduct_timeShift_eq_flattened_translate
        (d := d) (OS := OS) (lgc := lgc) f g t
  calc
    ‖bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))‖
      = ‖Tflat (SCV.translateSchwartz a ψ)‖ := by rw [hEq]
    _ ≤ (C0 : ℝ) * (Dsum * (1 + |t|) ^ N) := hmain
    _ ≤ Cbound * (1 + |t|) ^ N := by
        have hpow_nonneg : 0 ≤ (1 + |t|) ^ N := by positivity
        have haux :
            (C0 : ℝ) * (Dsum * (1 + |t|) ^ N) ≤
              ((C0 : ℝ) * Dsum + 1) * (1 + |t|) ^ N := by
          have hpow_ge_one : 1 ≤ (1 + |t|) ^ N := by
            exact one_le_pow₀ (by nlinarith [abs_nonneg t])
          nlinarith
        simpa [Cbound, mul_assoc, mul_left_comm, mul_comm] using haux

/-- Exact flattened-surface continuity for the live Stage-5 blocker:
after fixing the left factor, the scalar functional of the translated
flattened right factor is continuous in the translation parameter. -/
private theorem continuous_bvt_W_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Continuous (fun t : ℝ =>
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g))) := by
  rw [show
      (fun t : ℝ =>
        ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
          (unflattenSchwartzNPoint (d := d)))
          (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
            (flattenSchwartzNPoint (d := d) g))) =
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) by
      funext t
      symm
      exact bvt_W_conjTensorProduct_timeShift_eq_flattened_translate
        (d := d) (OS := OS) (lgc := lgc) f g t]
  exact continuous_bvt_W_conjTensorProduct_timeShift
    (d := d) OS lgc f g hg_compact

/-- Exact flattened-surface polynomial growth for the live Stage-5 blocker:
the translated flattened right-factor pairing grows at most polynomially in the
real translation parameter. -/
private theorem hasPolynomialGrowthOnLine_bvt_W_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    SCV.HasPolynomialGrowthOnLine (fun t : ℝ =>
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g))) := by
  rw [show
      (fun t : ℝ =>
        ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
          (unflattenSchwartzNPoint (d := d)))
          (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
            (flattenSchwartzNPoint (d := d) g))) =
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) by
      funext t
      symm
      exact bvt_W_conjTensorProduct_timeShift_eq_flattened_translate
        (d := d) (OS := OS) (lgc := lgc) f g t]
  exact hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShift
    (d := d) OS lgc f g

/-- Exact flattened-surface integrability for the Stage-5 spectral pairing:
the translated flattened right-factor functional pairs integrably against the
Fourier transform of any one-variable Schwartz test. -/
private theorem integrable_bvt_W_flattened_translate_mul_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
  exact SCV.integrable_mul_fourierTransform_of_continuous_polynomialGrowthOnLine
    (f := fun t : ℝ =>
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g)))
    (continuous_bvt_W_flattened_translate
      (d := d) OS lgc f g hg_compact)
    (hasPolynomialGrowthOnLine_bvt_W_flattened_translate
      (d := d) OS lgc f g)
    χ

/-- Zero-head-block insertion commutes with scalar multiplication. This lets the
final flattened spectral step treat the inserted tail translation as a genuine
one-parameter orbit `t • η`. -/
@[simp] private theorem zeroHeadBlockShift_smul
    {m n : ℕ}
    (t : ℝ)
    (a : Fin n → ℝ) :
    OSReconstruction.zeroHeadBlockShift (m := m) (n := n) (t • a) =
      t • OSReconstruction.zeroHeadBlockShift (m := m) (n := n) a := by
  induction m generalizing a with
  | zero =>
      ext i
      simp [OSReconstruction.zeroHeadBlockShift, Pi.smul_apply]
  | succ m ih =>
      rw [OSReconstruction.zeroHeadBlockShift, OSReconstruction.zeroHeadBlockShift,
        ← ContinuousLinearEquiv.map_smul]
      congr 1
      ext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j
        simp [ih, Pi.smul_apply]

/-- Scalar real-translation orbits are continuous in the Schwartz topology. -/
private theorem continuous_translateSchwartz_smul_local {m : ℕ}
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    Continuous (fun t : ℝ => SCV.translateSchwartz (t • η) ψ) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let ψ₀ : SchwartzMap (Fin m → ℝ) ℂ := SCV.translateSchwartz (t₀ • η) ψ
  have hzero : ContinuousAt (fun t : ℝ => SCV.translateSchwartz (t • η) ψ₀) 0 := by
    simp only [ContinuousAt]
    rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
    intro p ε hε
    let D : SchwartzMap (Fin m → ℝ) ℂ := LineDeriv.lineDerivOp η ψ₀
    let pSem : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
      schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p
    have hquot := OSReconstruction.tendsto_diffQuotient_translateSchwartz_zero ψ₀ η
    rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _] at hquot
    specialize hquot p 1 zero_lt_one
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter] at hquot
    obtain ⟨s, hs_nhds, hs_prop⟩ := hquot
    let M : ℝ := pSem D
    have hM_nonneg : 0 ≤ M := apply_nonneg pSem D
    have hM_pos : 0 < M + 1 := by linarith
    let δ : ℝ := ε / (M + 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    refine Filter.mem_of_superset
      (Filter.inter_mem hs_nhds (Metric.ball_mem_nhds 0 hδ_pos)) ?_
    intro t ht
    rcases ht with ⟨hts, htball⟩
    simp only [Set.mem_setOf_eq]
    have htrans0 : SCV.translateSchwartz (0 : Fin m → ℝ) ψ₀ = ψ₀ := by
      ext x
      simp [SCV.translateSchwartz_apply]
    rw [show (0 : ℝ) • η = (0 : Fin m → ℝ) from zero_smul ℝ η, htrans0]
    have ht_abs : |t| < δ := by
      simpa [Real.dist_eq, δ] using htball
    by_cases ht0 : t = 0
    · subst ht0
      simpa [zero_smul, htrans0] using hε
    · have htnz : t ∈ ({0}ᶜ : Set ℝ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
      have hq :
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) < 1 :=
        hs_prop ⟨hts, htnz⟩
      have hsplit :
          t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) =
            (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + D := by
        abel
      have hq' :
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) < 1 + M := by
        calc
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀))
              = pSem ((t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + D) := by
                  congr 1
          _ ≤ pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + pSem D :=
                map_add_le_add _ _ _
          _ < 1 + M := by
                dsimp [M] at *
                linarith
      have hdecomp :
          SCV.translateSchwartz (t • η) ψ₀ - ψ₀ =
            t • (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) := by
        rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]
      calc
        pSem (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)
            = pSem (t • (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀))) :=
              congr_arg pSem hdecomp
        _ = |t| * pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) :=
              map_smul_eq_mul _ _ _
        _ < δ * (1 + M) := by
              gcongr
        _ = ε := by
              dsimp [δ]
              field_simp [hM_pos.ne']
              ring
  have hshift : ContinuousAt (fun t : ℝ => t - t₀) t₀ := by
    simpa using (continuous_id.sub continuous_const).continuousAt
  have hcomp :
      ContinuousAt (fun t : ℝ => SCV.translateSchwartz ((t - t₀) • η) ψ₀) t₀ := by
    simpa [Function.comp] using
      (ContinuousAt.comp_of_eq hzero hshift (by simp))
  have hEqfun :
      (fun t : ℝ => SCV.translateSchwartz (t • η) ψ) =
        (fun t : ℝ => SCV.translateSchwartz ((t - t₀) • η) ψ₀) := by
    funext t
    ext x
    simp only [ψ₀, SCV.translateSchwartz_apply, sub_eq_add_neg]
    congr 1
    ext i
    simp [Pi.smul_apply, Pi.add_apply]
    ring
  rw [hEqfun]
  exact hcomp

/-- Exact continuity of the full flattened Fourier-shift orbit used in the
final Stage-5 support theorem. -/
private theorem continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift
    {n m : ℕ}
    (Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ) :
    Continuous (fun t : ℝ =>
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
          (SCV.translateSchwartz
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (t • flatTimeShiftDirection d m))
            Ψ))) := by
  let η :
      Fin (n * (d + 1) + m * (d + 1)) → ℝ :=
    OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m)
  have hcont_base :
      Continuous (fun t : ℝ => SCV.translateSchwartz (t • η) Ψ) :=
    continuous_translateSchwartz_smul_local η Ψ
  have hcont_reindex :
      Continuous (fun t : ℝ =>
        OSReconstruction.reindexSchwartzFin
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
          (SCV.translateSchwartz (t • η) Ψ)) :=
    ((OSReconstruction.reindexSchwartzFin
      (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))).continuous).comp hcont_base
  have hEq :
      (fun t : ℝ =>
        physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
            (SCV.translateSchwartz
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (t • flatTimeShiftDirection d m))
              Ψ))) =
      (fun t : ℝ =>
        physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
            (SCV.translateSchwartz (t • η) Ψ))) := by
    funext t
    simp [η, zeroHeadBlockShift_smul]
  rw [hEq]
  exact physicsFourierFlatCLM.continuous.comp hcont_reindex

/-- Polynomial seminorm growth of the full flattened Fourier-shift orbit. This
is the exact Schwartz-family bound needed by `schwartz_clm_fubini_exchange` in
the final flattened spectral step. -/
private theorem exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift
    {n m : ℕ}
    (Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ)
    (k l : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k l
          (physicsFourierFlatCLM
            (OSReconstruction.reindexSchwartzFin
              (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
              (SCV.translateSchwartz
                (OSReconstruction.zeroHeadBlockShift
                  (m := n * (d + 1)) (n := m * (d + 1))
                  (t • flatTimeShiftDirection d m))
                Ψ))) ≤
          C * (1 + |t|) ^ N := by
  classical
  let η :
      Fin (n * (d + 1) + m * (d + 1)) → ℝ :=
    OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m)
  let L :
      SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ :=
    (physicsFourierFlatCLM : _).comp
      (OSReconstruction.reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
  let q : Seminorm ℂ (SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ) :=
    (schwartzSeminormFamily ℂ (Fin ((n + m) * (d + 1)) → ℝ) ℂ (k, l)).comp L.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ =>
      schwartzSeminormFamily ℂ (Fin ((n + m) * (d + 1)) → ℝ) ℂ (k, l) (L φ))
    exact
      ((schwartz_withSeminorms ℂ (Fin ((n + m) * (d + 1)) → ℝ) ℂ).continuous_seminorm
        (k, l)).comp L.continuous
  obtain ⟨s, D, hD_ne, hq_bound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ) q hq_cont
  have hD_pos : 0 < (D : ℝ) := by
    exact lt_of_le_of_ne D.2 (by exact_mod_cast hD_ne.symm)
  have hB :
      ∀ p : ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
        schwartzSeminormFamily ℂ
          (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p
          (SCV.translateSchwartz (t • η) Ψ) ≤
            B * (1 + |t|) ^ p.1 := by
    intro p
    obtain ⟨B0, hB0_nonneg, hB0⟩ :=
      SCV.seminorm_translateSchwartz_le p.1 p.2 Ψ
    let B : ℝ := B0 * (1 + ‖η‖) ^ p.1
    refine ⟨B, by
      dsimp [B]
      exact mul_nonneg hB0_nonneg (pow_nonneg (by positivity) _), ?_⟩
    intro t
    calc
      schwartzSeminormFamily ℂ
          (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p
          (SCV.translateSchwartz (t • η) Ψ)
          ≤ B0 * (1 + ‖t • η‖) ^ p.1 := hB0 (t • η)
      _ ≤ B0 * (((1 + ‖η‖) * (1 + |t|)) ^ p.1) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0_nonneg
          have hmain : 1 + ‖t • η‖ ≤ (1 + ‖η‖) * (1 + |t|) := by
            rw [norm_smul, Real.norm_eq_abs]
            nlinarith [abs_nonneg t, norm_nonneg η]
          exact pow_le_pow_left₀ (by positivity) hmain _
      _ = B * (1 + |t|) ^ p.1 := by
          calc
            B0 * (((1 + ‖η‖) * (1 + |t|)) ^ p.1)
                = B0 * ((1 + ‖η‖) ^ p.1 * (1 + |t|) ^ p.1) := by
                    rw [mul_pow]
            _ = B * (1 + |t|) ^ p.1 := by
                    dsimp [B]
                    ring
  choose B hB_nonneg hB_bound using hB
  let N : ℕ := s.sup Prod.fst
  let Bsum : ℝ := ∑ p ∈ s, B p
  let C : ℝ := (D : ℝ) * Bsum + 1
  have hBsum_nonneg : 0 ≤ Bsum := by
    dsimp [Bsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hB_nonneg p
  refine ⟨C, N, by
    dsimp [C]
    nlinarith [show 0 < (D : ℝ) from hD_pos], ?_⟩
  intro t
  let ψt : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
    SCV.translateSchwartz (t • η) Ψ
  let u : ℝ := 1 + |t|
  have hu_ge_one : 1 ≤ u := by
    dsimp [u]
    linarith [abs_nonneg t]
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ
          (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p) ψt =
          ∑ p ∈ s',
            schwartzSeminormFamily ℂ
              (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p ψt := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ
        (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p) ψt ≤
        Bsum * u ^ N := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ
        (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p) ψt
          = ∑ p ∈ s,
              schwartzSeminormFamily ℂ
                (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p ψt := by
                  simpa using hsum_apply s
      _ ≤ ∑ p ∈ s, B p * u ^ N := by
            refine Finset.sum_le_sum ?_
            intro p hp
            have hpN : p.1 ≤ N := Finset.le_sup hp
            calc
              schwartzSeminormFamily ℂ
                  (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p ψt
                  ≤ B p * u ^ p.1 := hB_bound p t
              _ ≤ B p * u ^ N := by
                    refine mul_le_mul_of_nonneg_left ?_ (hB_nonneg p)
                    exact pow_le_pow_right₀ hu_ge_one hpN
      _ = Bsum * u ^ N := by
            simp [Bsum, Finset.sum_mul]
  have hL_bound :
      SchwartzMap.seminorm ℝ k l (L ψt) ≤ (D : ℝ) * (Bsum * u ^ N) := by
    calc
      SchwartzMap.seminorm ℝ k l (L ψt) = q ψt := by
        rfl
      _ ≤ (D • s.sup (schwartzSeminormFamily ℂ
            (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ)) ψt := hq_bound ψt
      _ = (D : ℝ) *
            (s.sup (schwartzSeminormFamily ℂ
              (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ)) ψt := by
            rfl
      _ ≤ (D : ℝ) *
            ((∑ p ∈ s, schwartzSeminormFamily ℂ
              (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ p) ψt) := by
            gcongr
            exact Seminorm.le_def.mp
              (Seminorm.finset_sup_le_sum
                (schwartzSeminormFamily ℂ
                  (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ) s) ψt
      _ ≤ (D : ℝ) * (Bsum * u ^ N) := by
            gcongr
  calc
    SchwartzMap.seminorm ℝ k l
        (physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
            (SCV.translateSchwartz
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (t • flatTimeShiftDirection d m))
              Ψ)))
        = SchwartzMap.seminorm ℝ k l (L ψt) := by
            simp [L, ψt, η, zeroHeadBlockShift_smul]
    _ ≤ (D : ℝ) * (Bsum * u ^ N) := hL_bound
    _ ≤ C * u ^ N := by
          have hCu : (D : ℝ) * (Bsum * u ^ N) ≤ ((D : ℝ) * Bsum + 1) * u ^ N := by
            have hu_pow_ge_one : 1 ≤ u ^ N := by
              exact one_le_pow₀ hu_ge_one
            nlinarith
          simpa [C, u, mul_assoc, mul_left_comm, mul_comm] using hCu

/-- A one-variable normalized Schwartz bump with total integral `1`. -/
private noncomputable def normedUnitBumpSchwartzLocal : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private theorem integral_normedUnitBumpSchwartzLocal :
    ∫ x : ℝ, normedUnitBumpSchwartzLocal x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartzLocal x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    simpa [normedUnitBumpSchwartzLocal, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

/-- A product normalized Schwartz bump on `Fin k → ℝ`. -/
private noncomputable def normedUnitBumpSchwartzPi : ∀ k : ℕ,
    SchwartzMap (Fin k → ℝ) ℂ
  | 0 => by
      let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
      have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
        simpa [f] using (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
      have hf_compact : HasCompactSupport f := by
        simpa [HasCompactSupport, tsupport, Function.support, f] using
          (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
      exact hf_compact.toSchwartzMap hf_smooth
  | k + 1 => normedUnitBumpSchwartzLocal.prependField (normedUnitBumpSchwartzPi k)

private theorem integral_normedUnitBumpSchwartzPi :
    ∀ k : ℕ, ∫ x : Fin k → ℝ, normedUnitBumpSchwartzPi k x = 1
  | 0 => by
      have happly :
          (fun x : Fin 0 → ℝ => normedUnitBumpSchwartzPi 0 x) = fun _ : Fin 0 → ℝ => (1 : ℂ) := by
        funext x
        simp [normedUnitBumpSchwartzPi]
      rw [happly]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      simpa [hvol] using
        (MeasureTheory.integral_dirac (a := default) (f := fun _ : Fin 0 → ℝ => (1 : ℂ)))
  | k + 1 => by
      calc
        ∫ x : Fin (k + 1) → ℝ, normedUnitBumpSchwartzPi (k + 1) x
            =
          ∫ z : ℝ × (Fin k → ℝ), normedUnitBumpSchwartzPi (k + 1) (Fin.cons z.1 z.2) := by
              simpa using
                (OSReconstruction.integral_finSucc_cons_eq
                  (f := fun x : Fin (k + 1) → ℝ => normedUnitBumpSchwartzPi (k + 1) x)).symm
        _ = ∫ z : ℝ × (Fin k → ℝ),
              normedUnitBumpSchwartzLocal z.1 * normedUnitBumpSchwartzPi k z.2 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              simp [normedUnitBumpSchwartzPi, SchwartzMap.prependField_apply]
        _ = (∫ x : ℝ, normedUnitBumpSchwartzLocal x) *
              (∫ y : Fin k → ℝ, normedUnitBumpSchwartzPi k y) := by
              simpa using
                (MeasureTheory.integral_prod_mul
                  (f := fun x : ℝ => normedUnitBumpSchwartzLocal x)
                  (g := fun y : Fin k → ℝ => normedUnitBumpSchwartzPi k y))
        _ = 1 := by
              rw [integral_normedUnitBumpSchwartzLocal, integral_normedUnitBumpSchwartzPi k]
              ring

/-- Change of variables through a finite coordinate reindexing. -/
private theorem integral_comp_castFinCLE_eq {a b : ℕ}
    (h : a = b)
    (f : (Fin b → ℝ) → ℂ) :
    (∫ x : Fin a → ℝ, f ((OSReconstruction.castFinCLE h) x)) =
      ∫ y : Fin b → ℝ, f y := by
  let e : (Fin a → ℝ) ≃ᵐ (Fin b → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin b => ℝ) (finCongr h)
  have he :
      MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
    simpa [e] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin b => ℝ) (finCongr h))
  simpa [e, OSReconstruction.castFinCLE, MeasurableEquiv.piCongrLeft,
    ContinuousLinearEquiv.piCongrLeft] using
    (he.integral_comp' (f := e) (g := f))

/-- Tail-block phase vanishing on the full flattened dual-cone surface. -/
private theorem integral_zeroHeadBlockShift_flatTimeShiftDirection_phase_mul_fourierTransform_eq_zero_of_negSupport
    {n m : ℕ}
    (χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0)
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∫ t : ℝ,
      Complex.exp
          (-(Complex.I *
              ((∑ i,
                  (((OSReconstruction.castFinCLE
                    (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
                    (OSReconstruction.zeroHeadBlockShift
                      (m := n * (d + 1)) (n := m * (d + 1))
                      (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) * t)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t = 0 := by
  exact integral_phase_mul_fourierTransform_eq_zero_of_negSupport_of_nonpos
    (χ := χ) hχ_supp
    (zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m) hξ)

set_option maxHeartbeats 800000 in
/-- Final flattened spectral vanishing on the live Stage-5 theorem surface:
the translated full-flat VT dual-cone distribution annihilates Fourier
transforms of negative-support one-variable tests. -/
private theorem integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0) :
    ∫ t : ℝ,
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t = 0 := by
  classical
  let M : ℕ := (n + m) * (d + 1)
  have hM_pos : 0 < M := by
    dsimp [M]
    have hnm_pos : 0 < n + m := by omega
    exact Nat.mul_pos hnm_pos (Nat.succ_pos _)
  let k : ℕ := M - 1
  have hk : k + 1 = M := by
    dsimp [k]
    exact Nat.succ_pred_eq_of_pos hM_pos
  let χhat : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ χ
  let β : SchwartzMap (Fin k → ℝ) ℂ := normedUnitBumpSchwartzPi k
  let fpad0 : SchwartzMap (Fin (k + 1) → ℝ) ℂ := χhat.prependField β
  let fpad : SchwartzMap (Fin M → ℝ) ℂ := OSReconstruction.reindexSchwartzFin hk fpad0
  let Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
    (flattenSchwartzNPoint (d := d) f.borchersConj).tensorProduct
      (flattenSchwartzNPoint (d := d) g)
  let orbit : ℝ → SchwartzMap (Fin M → ℝ) ℂ :=
    fun t =>
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
          (SCV.translateSchwartz
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (t • flatTimeShiftDirection d m))
            Ψ))
  let headCoord : (Fin M → ℝ) → ℝ :=
    fun x => ((OSReconstruction.castFinCLE hk).symm x) 0
  let gFamily : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ := fun x => orbit (headCoord x)
  obtain ⟨Tflat, hTflat_supp, hTflat_repr⟩ :=
    exists_flattened_bvt_W_conjTensorProduct_right_dualCone_distribution_translate
      (d := d) OS lgc f g
  have hg_cont : Continuous gFamily := by
    dsimp [gFamily, orbit, headCoord]
    exact
      (continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift
        (d := d) (n := n) (m := m) Ψ).comp
        ((continuous_apply (0 : Fin (k + 1))).comp
          ((OSReconstruction.castFinCLE hk).symm.continuous))
  have hg_bound :
      ∀ (k0 l0 : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ x : Fin M → ℝ,
          SchwartzMap.seminorm ℝ k0 l0 (gFamily x) ≤ C * (1 + ‖x‖) ^ N := by
    intro k0 l0
    obtain ⟨C, N, hC_pos, hC_bound⟩ :=
      exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift
        (d := d) (n := n) (m := m) Ψ k0 l0
    refine ⟨C, N, hC_pos, ?_⟩
    intro x
    have hcoord :
        |headCoord x| ≤ ‖x‖ := by
      have hhead :
          headCoord x = x ((finCongr hk) 0) := by
        simp [headCoord, OSReconstruction.castFinCLE_symm_apply]
      rw [hhead]
      simpa using (norm_le_pi_norm (f := x) (i := (finCongr hk) 0))
    calc
      SchwartzMap.seminorm ℝ k0 l0 (gFamily x)
          ≤ C * (1 + |headCoord x|) ^ N := hC_bound (headCoord x)
      _ ≤ C * (1 + ‖x‖) ^ N := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC_pos)
          exact pow_le_pow_left₀ (by positivity) (by linarith) N
  obtain ⟨Φ, hΦ_eval, hΦ_pair⟩ :=
    schwartz_clm_fubini_exchange Tflat gFamily fpad hg_cont hg_bound
  have hPair_repr :
      ∫ x : Fin M → ℝ, Tflat (gFamily x) * fpad x =
        ∫ t : ℝ,
          ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
            (unflattenSchwartzNPoint (d := d)))
            (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
              (flattenSchwartzNPoint (d := d) g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t := by
    let pairing : ℝ → ℂ := fun t =>
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g))
    have hrepr_x : ∀ x : Fin M → ℝ, Tflat (gFamily x) = pairing (headCoord x) := by
      intro x
      simpa [pairing, gFamily, headCoord, orbit] using (hTflat_repr (headCoord x)).symm
    let F : (Fin (k + 1) → ℝ) → ℂ := fun z => pairing (z 0) * fpad0 z
    calc
      ∫ x : Fin M → ℝ, Tflat (gFamily x) * fpad x
          = ∫ x : Fin M → ℝ, F ((OSReconstruction.castFinCLE hk).symm x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              rw [hrepr_x x]
              simp [F, headCoord, fpad, fpad0, OSReconstruction.reindexSchwartzFin_apply]
      _ = ∫ z : Fin (k + 1) → ℝ, F z := by
            simpa using integral_comp_castFinCLE_eq (h := hk.symm) (f := F)
      _ = ∫ p : ℝ × (Fin k → ℝ), pairing p.1 * (χhat p.1 * β p.2) := by
            simpa [F, fpad0, SchwartzMap.prependField_apply, mul_assoc] using
              (OSReconstruction.integral_finSucc_cons_eq (f := F)).symm
      _ = (∫ t : ℝ, pairing t * χhat t) * (∫ y : Fin k → ℝ, β y) := by
            simpa [mul_assoc] using
              (MeasureTheory.integral_prod_mul
                (f := fun t : ℝ => pairing t * χhat t)
                (g := fun y : Fin k → ℝ => β y))
      _ = ∫ t : ℝ, pairing t * χhat t := by
            rw [integral_normedUnitBumpSchwartzPi]
            ring
  have hΦ_vanish :
      ∀ ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)),
        Φ ξ = 0 := by
    intro ξ hξ
    rw [hΦ_eval ξ]
    let phase : ℝ → ℂ := fun t =>
      Complex.exp
        (-(Complex.I *
            ((∑ i,
                (((OSReconstruction.castFinCLE
                  (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
                  (OSReconstruction.zeroHeadBlockShift
                    (m := n * (d + 1)) (n := m * (d + 1))
                    (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) * t))
    let base : ℂ :=
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1))
          Ψ) ξ
    have horbit_phase : ∀ t : ℝ, orbit t ξ = phase t * base := by
      intro t
      dsimp [orbit, phase, base]
      rw [physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply
        (d := d) (n := n) (m := m)
        (a := t • flatTimeShiftDirection d m) (Ψ := Ψ) (ξ := ξ)]
      congr 1
      have hsum :
          (∑ i,
              ((((OSReconstruction.castFinCLE
                (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
                (OSReconstruction.zeroHeadBlockShift
                  (m := n * (d + 1)) (n := m * (d + 1))
                  (t • flatTimeShiftDirection d m))) i : ℝ) : ℂ) *
                (ξ i : ℂ)) =
            ((∑ i,
                (((OSReconstruction.castFinCLE
                  (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
                  (OSReconstruction.zeroHeadBlockShift
                    (m := n * (d + 1)) (n := m * (d + 1))
                    (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) * t := by
        norm_num
        simp [zeroHeadBlockShift_smul, Finset.mul_sum, Pi.smul_apply,
          mul_assoc, mul_left_comm, mul_comm]
      rw [hsum]
      ring
    let G : (Fin (k + 1) → ℝ) → ℂ := fun z => orbit (z 0) ξ * fpad0 z
    calc
      ∫ x : Fin M → ℝ, gFamily x ξ * fpad x
          = ∫ x : Fin M → ℝ, G ((OSReconstruction.castFinCLE hk).symm x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [G, gFamily, headCoord, fpad, fpad0, OSReconstruction.reindexSchwartzFin_apply]
      _ = ∫ z : Fin (k + 1) → ℝ, G z := by
            simpa using integral_comp_castFinCLE_eq (h := hk.symm) (f := G)
      _ = ∫ p : ℝ × (Fin k → ℝ), orbit p.1 ξ * (χhat p.1 * β p.2) := by
            simpa [G, fpad0, SchwartzMap.prependField_apply, mul_assoc] using
              (OSReconstruction.integral_finSucc_cons_eq (f := G)).symm
      _ = ∫ p : ℝ × (Fin k → ℝ), base * ((phase p.1 * χhat p.1) * β p.2) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with p
            rw [horbit_phase p.1]
            ring
      _ = base * ∫ p : ℝ × (Fin k → ℝ), (phase p.1 * χhat p.1) * β p.2 := by
            simpa using
              (MeasureTheory.integral_const_mul base
                (fun p : ℝ × (Fin k → ℝ) => (phase p.1 * χhat p.1) * β p.2))
      _ = base * ((∫ t : ℝ, phase t * χhat t) * (∫ y : Fin k → ℝ, β y)) := by
            congr 1
            simpa [mul_assoc] using
              (MeasureTheory.integral_prod_mul
                (f := fun t : ℝ => phase t * χhat t)
                (g := fun y : Fin k → ℝ => β y))
      _ = base * (0 * 1) := by
            rw [integral_zeroHeadBlockShift_flatTimeShiftDirection_phase_mul_fourierTransform_eq_zero_of_negSupport
              (d := d) (n := n) (m := m) (χ := χ) hχ_supp hξ,
              integral_normedUnitBumpSchwartzPi]
      _ = 0 := by ring
  have hTflat_zero : Tflat Φ = 0 := by
    unfold HasFourierSupportInDualCone HasFourierSupportIn at hTflat_supp
    apply hTflat_supp
    intro ξ hξ_supp hξ_dual
    exact hξ_supp (hΦ_vanish ξ hξ_dual)
  calc
    ∫ t : ℝ,
      ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
        (unflattenSchwartzNPoint (d := d)))
        (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
          (flattenSchwartzNPoint (d := d) g)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) t
        = ∫ x : Fin M → ℝ, Tflat (gFamily x) * fpad x := by
            symm
            exact hPair_repr
    _ = Tflat Φ := by symm; exact hΦ_pair
    _ = 0 := hTflat_zero

/-- Exact hypothesis transfer for the live Stage-5 blocker: if the flattened
translation functional has one-sided Fourier support, then so does the original
time-shift pairing functional. This means the remaining spectral theorem can be
proved directly on the flattened surface and then fed into the existing ambient
Paley-Wiener witness route without further bookkeeping. -/
private theorem hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift_of_flattened
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (h_spectral_flat :
      SCV.HasOneSidedFourierSupport
        (fun χ : SchwartzMap ℝ ℂ =>
          ∫ t : ℝ,
            ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
              (unflattenSchwartzNPoint (d := d)))
              (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
                (flattenSchwartzNPoint (d := d) g)) * χ t)) :
    SCV.HasOneSidedFourierSupport
      (fun χ : SchwartzMap ℝ ℂ =>
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t) := by
  intro χ hχ_supp
  change
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t = 0
  rw [integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_eq_flattened_translate
    (d := d) (OS := OS) (lgc := lgc) f g χ]
  exact h_spectral_flat χ hχ_supp

/-- The flattened Stage-5 spectral theorem on the exact theorem surface now
proved in production: the full translated flat pairing annihilates Fourier
transforms of negative-support tests. -/
private theorem hasOneSidedFourierSupport_bvt_W_flattened_translate
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    SCV.HasOneSidedFourierSupport
      (fun χ : SchwartzMap ℝ ℂ =>
        ∫ t : ℝ,
          ((bvt_W_conjTensorProduct_rightCLM (d := d) OS lgc f).comp
            (unflattenSchwartzNPoint (d := d)))
            (SCV.translateSchwartz (t • flatTimeShiftDirection d m)
              (flattenSchwartzNPoint (d := d) g)) * χ t) := by
  intro χ hχ_supp
  exact integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport
    (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g χ hχ_supp

/-- Honest Stage-5 spectral package on the original time-shift theorem surface:
for compact right input and positive arity, the reconstructed Wightman
time-shift pairing has one-sided Fourier support. -/
private theorem hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    SCV.HasOneSidedFourierSupport
      (fun χ : SchwartzMap ℝ ℂ =>
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t) := by
  exact hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift_of_flattened
    (d := d) (OS := OS) (lgc := lgc) (f := f) (g := g)
    (hasOneSidedFourierSupport_bvt_W_flattened_translate
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g)

/-- Ambient-witness existence on the current Stage-5 route: once the real-time
Wightman pairing against a fixed ambient tensor has one-sided Fourier support,
the existing Paley-Wiener infrastructure produces the required upper-half-plane
holomorphic witness. This is the honest ambient replacement for the rejected
`H = singleSplit` shortcut. -/
theorem bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (h_spectral :
      SCV.HasOneSidedFourierSupport
        (fun χ : SchwartzMap ℝ ℂ =>
          ∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => H (↑x + ↑η * Complex.I))) ∧
      (∀ χ : SchwartzMap ℝ ℂ,
        Filter.Tendsto
          (fun η : ℝ => ∫ x : ℝ, H (↑x + ↑η * Complex.I) * χ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t))) := by
  exact SCV.paley_wiener_one_step_simple
    (f := fun t : ℝ =>
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    (continuous_bvt_W_conjTensorProduct_timeShift
      (d := d) OS lgc f g hg_compact)
    (hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShift
      (d := d) OS lgc f g)
    h_spectral

/-- Honest Stage-5 spectral reduction for the ambient witness route: if an
upper-half-plane trace `H` has the reconstructed Wightman time-shift pairing as
its boundary value, and if the positive-height pairings against Fourier
transforms of negative-support tests already vanish, then the ambient
Paley-Wiener witness exists.

This is not a new route or a fake shortcut. It simply packages the exact way
the newly-landed reverse-Paley-Wiener reduction theorem feeds the existing
ambient witness existence theorem. The remaining live content is therefore the
shell-specific vanishing hypothesis `hzero`, not another abstract support
statement. -/
theorem bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_boundaryValue_of_paired_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_bv :
      ∀ χ : SchwartzMap ℝ ℂ,
        Filter.Tendsto
          (fun η : ℝ => ∫ x : ℝ, H (↑x + ↑η * Complex.I) * χ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t)))
    (hzero :
      ∀ (χ : SchwartzMap ℝ ℂ),
        (∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0) →
        ∀ η : ℝ, 0 < η →
          ∫ x : ℝ, H (↑x + ↑η * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x = 0) :
    ∃ Hw : ℂ → ℂ,
      DifferentiableOn ℂ Hw SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => Hw (↑x + ↑η * Complex.I))) ∧
      (∀ χ : SchwartzMap ℝ ℂ,
        Filter.Tendsto
          (fun η : ℝ => ∫ x : ℝ, Hw (↑x + ↑η * Complex.I) * χ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t))) := by
  refine bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension
    (d := d) OS lgc f g hg_compact ?_
  exact SCV.hasOneSidedFourierSupport_of_boundaryValue_of_paired_zero
    H
    (fun χ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t)
    hH_bv
    hzero

/-- The Stage-5 spectral blocker is now discharged on the original time-shift
surface: for positive right arity, the Paley-Wiener witness for the reconstructed
Wightman time-shift pairing exists unconditionally from the flattened dual-cone
support theorem proved above. -/
theorem bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => H (↑x + ↑η * Complex.I))) ∧
      (∀ χ : SchwartzMap ℝ ℂ,
        Filter.Tendsto
          (fun η : ℝ => ∫ x : ℝ, H (↑x + ↑η * Complex.I) * χ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t))) := by
  exact bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension
    (d := d) OS lgc f g hg_compact
    (hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g)

/-- The canonical ambient upper-half-plane witness for the reconstructed
Wightman right-time-shift pairing, chosen from the now-closed Stage-5 spectral
package.

This mirrors the existing `bvt_singleSplit_xiShiftHolomorphicValue` pattern:
the witness is no longer merely existential in the theorem-3 lane. The live
remaining blocker can now be stated directly on this explicit holomorphic
function rather than on an anonymous `∃ H`. -/
noncomputable def bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ℂ → ℂ :=
  Classical.choose <|
    bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened
      (d := d) OS lgc hm f g hg_compact

/-- The chosen ambient Wightman time-shift witness is holomorphic on the upper
half-plane. -/
theorem differentiableOn_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    DifferentiableOn ℂ
      (bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
        (d := d) OS lgc hm f g hg_compact)
      SCV.upperHalfPlane :=
  (Classical.choose_spec <|
    bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened
      (d := d) OS lgc hm f g hg_compact).1

/-- The chosen ambient Wightman time-shift witness has polynomial growth on
every positive horizontal line. -/
theorem hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (η : ℝ) (hη : 0 < η) :
    SCV.HasPolynomialGrowthOnLine
      (fun x =>
        bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
          (d := d) OS lgc hm f g hg_compact (↑x + ↑η * Complex.I)) :=
  (Classical.choose_spec <|
    bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened
      (d := d) OS lgc hm f g hg_compact).2.1 η hη

/-- The chosen ambient Wightman time-shift witness has the reconstructed
time-shift pairing as its distributional boundary value. -/
theorem tendsto_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
            (d := d) OS lgc hm f g hg_compact (↑x + ↑η * Complex.I) * χ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t)) :=
  (Classical.choose_spec <|
    bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened
      (d := d) OS lgc hm f g hg_compact).2.2 χ

/-- Any upper-half-plane witness with the linewise polynomial-growth package
used in the ambient Paley-Wiener route pairs integrably with Fourier transforms
of Schwartz tests. This is the exact real-line integrability input needed by
the current Stage-5 `hzero` contour-shift argument. -/
private theorem integrable_mul_fourierTransform_of_upperHalfPlaneWitness
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H SCV.upperHalfPlane)
    (hH_growth :
      ∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => H (↑x + ↑η * Complex.I)))
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        H (↑x + ↑η * Complex.I) * (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
  have hline_maps :
      Set.MapsTo (fun x : ℝ => (↑x : ℂ) + ↑η * Complex.I) Set.univ SCV.upperHalfPlane := by
    intro x hx
    simpa [SCV.upperHalfPlane, hη]
  have hline_cont :
      Continuous (fun x : ℝ => H (↑x + ↑η * Complex.I)) := by
    have hmap_cont : Continuous (fun x : ℝ => (↑x : ℂ) + ↑η * Complex.I) := by
      fun_prop
    exact hH_holo.continuousOn.comp_continuous hmap_cont (by
      intro x
      simpa [SCV.upperHalfPlane, hη])
  exact SCV.integrable_mul_fourierTransform_of_continuous_polynomialGrowthOnLine
    (f := fun x : ℝ => H (↑x + ↑η * Complex.I))
    hline_cont
    (hH_growth η hη)
    χ

/-- Boundary-value recovery for the chosen ambient Wightman time-shift witness,
specialized to Fourier transforms of Schwartz tests.

This is the exact public theorem surface needed when the remaining theorem-3
arguments pair the chosen witness against `𝓕χ` rather than a raw Schwartz test. -/
theorem tendsto_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness_boundaryValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
            (d := d) OS lgc hm f g hg_compact (↑x + ↑η * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t)) := by
  simpa using
    tendsto_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      f g hg_compact ((SchwartzMap.fourierTransformCLM ℂ) χ)

/-- Integrability of the chosen ambient Wightman time-shift witness against the
Fourier transform of any Schwartz test along positive horizontal lines.

This is the concrete public specialization of the generic upper-half-plane
witness integrability theorem, so later theorem-3 arguments can stay on the
chosen witness surface rather than re-opening existential packaging. -/
theorem integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
          (d := d) OS lgc hm f g hg_compact (↑x + ↑η * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
  exact integrable_mul_fourierTransform_of_upperHalfPlaneWitness
    (H := bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
      (d := d) OS lgc hm f g hg_compact)
    (differentiableOn_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g hg_compact)
    (hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftUpperHalfPlaneWitness
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g hg_compact)
    χ hη

/-- The real-time Wightman pairing against a compactly supported right factor
defines an actual tempered functional on one-variable Schwartz space.

This is the explicit line-functional hidden inside the Stage-5 ambient
Paley-Wiener witness. Making it concrete is the first honest step toward
computing the witness on the positive imaginary axis, rather than carrying an
anonymous `Classical.choose` witness forever. -/
private theorem exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ T : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
      ∀ χ : SchwartzMap ℝ ℂ,
        T χ =
          ∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t := by
  let h : ℝ → ℂ := fun t =>
    bvt_W OS lgc (n + m)
      (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
  have hh_cont : Continuous h :=
    continuous_bvt_W_conjTensorProduct_timeShift
      (d := d) OS lgc f g hg_compact
  rcases hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShift
      (d := d) OS lgc f g with ⟨C_bound, N, hC_bound_pos, h_growth_bound⟩
  let M : ℕ := N + 2
  let sem : SchwartzMap ℝ ℂ → ℝ :=
    fun χ => (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) χ
  have h_decay_int_nat : MeasureTheory.Integrable
      (fun t : ℝ => ((1 + ‖t‖) ^ 2)⁻¹) MeasureTheory.volume := by
    have h_decay_int : MeasureTheory.Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) MeasureTheory.volume := by
      have : (Module.finrank ℝ ℝ : ℝ) < (2 : ℝ) := by norm_num
      simpa using integrable_one_add_norm this
    simpa [Real.rpow_neg (by positivity : 0 ≤ (1 + ‖(0 : ℝ)‖)), Real.rpow_natCast] using
      h_decay_int
  have hsem_bound : ∀ (χ : SchwartzMap ℝ ℂ) (t : ℝ),
      (1 + ‖t‖) ^ M * ‖χ t‖ ≤ 2 ^ M * sem χ := by
    intro χ t
    simpa [sem, M, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (M, 0)) (k := M) (n := 0)
        (le_rfl) (le_rfl) χ t)
  have h_pointwise_bound : ∀ (χ : SchwartzMap ℝ ℂ) (t : ℝ),
      ‖h t * χ t‖ ≤
        C_bound * 2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹ := by
    intro χ t
    have h_growth_t : ‖h t‖ ≤ C_bound * (1 + ‖t‖) ^ N := by
      simpa [h] using h_growth_bound t
    have h_pow_pos : 0 < (1 + ‖t‖) ^ 2 := by positivity
    have h_decay_step :
        (1 + ‖t‖) ^ N * ‖χ t‖ ≤
          2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ h_pow_pos]
      calc
        (1 + ‖t‖) ^ N * ‖χ t‖ * (1 + ‖t‖) ^ 2
            = (1 + ‖t‖) ^ M * ‖χ t‖ := by
                rw [show M = N + 2 by simp [M], pow_add]
                ring
        _ ≤ 2 ^ M * sem χ := hsem_bound χ t
    have h_decay_mul :
        C_bound * (1 + ‖t‖) ^ N * ‖χ t‖ ≤
          C_bound * (2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹) := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left h_decay_step (le_of_lt hC_bound_pos))
    calc
      ‖h t * χ t‖ = ‖h t‖ * ‖χ t‖ := norm_mul _ _
      _ ≤ C_bound * (1 + ‖t‖) ^ N * ‖χ t‖ :=
        mul_le_mul_of_nonneg_right h_growth_t (norm_nonneg _)
      _ ≤ C_bound * (2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹) := h_decay_mul
      _ = C_bound * 2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹ := by ring
  have h_integrable : ∀ χ : SchwartzMap ℝ ℂ,
      MeasureTheory.Integrable (fun t : ℝ => h t * χ t) MeasureTheory.volume := by
    intro χ
    have h_majorant_int : MeasureTheory.Integrable
        (fun t : ℝ => C_bound * 2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹)
        MeasureTheory.volume :=
      h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem χ)
    refine h_majorant_int.mono' ((hh_cont.mul χ.continuous).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (h_pointwise_bound χ)
  let I₂ : ℝ := ∫ t : ℝ, ((1 + ‖t‖) ^ 2)⁻¹
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun χ : SchwartzMap ℝ ℂ => ∫ t : ℝ, h t * χ t)
      (fun χ ψ => by
        simpa [h, mul_add] using
          (MeasureTheory.integral_add
            (f := fun t : ℝ => h t * χ t)
            (g := fun t : ℝ => h t * ψ t)
            (h_integrable χ) (h_integrable ψ)))
      (fun a χ => by
        simpa [h, mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_smul a (fun t : ℝ => h t * χ t)))
      (by
        have hI₂_nonneg : 0 ≤ I₂ := by
          unfold I₂
          exact MeasureTheory.integral_nonneg fun _ => by positivity
        refine ⟨Finset.Iic (M, 0), C_bound * 2 ^ M * I₂, ?_, ?_⟩
        · exact mul_nonneg (mul_nonneg (le_of_lt hC_bound_pos) (by positivity)) hI₂_nonneg
        · intro χ
          calc
            ‖∫ t : ℝ, h t * χ t‖ ≤ ∫ t : ℝ, ‖h t * χ t‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t : ℝ, C_bound * 2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹ :=
              MeasureTheory.integral_mono_ae (h_integrable χ).norm
                (h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem χ))
                (Filter.Eventually.of_forall (h_pointwise_bound χ))
            _ = C_bound * 2 ^ M * I₂ * sem χ := by
              rw [show (∫ t : ℝ, C_bound * 2 ^ M * sem χ * ((1 + ‖t‖) ^ 2)⁻¹) =
                  (C_bound * 2 ^ M * sem χ) * I₂ by
                    simp [I₂, MeasureTheory.integral_const_mul]]
              ring
            _ = (C_bound * 2 ^ M * I₂) *
                (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) χ := by
              simp [sem, mul_assoc] )
  refine ⟨T, ?_⟩
  intro χ
  rfl

/-- The concrete Fourier-Laplace witness attached to the real-time Wightman
pairing functional. Unlike the existing `Classical.choose` witness, this is an
explicit scaled `SCV.fourierLaplaceExt`, so its interior values can be
computed directly on the positive imaginary axis. -/
private noncomputable def bvt_W_conjTensorProduct_timeShiftCanonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    let T :=
      Classical.choose <|
        exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
          (d := d) OS lgc f g hg_compact
    SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w))
      (by
        have hscaled : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
        simpa [Complex.mul_im] using hscaled)
  else
    0

private theorem bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    DifferentiableOn ℂ
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact)
      SCV.upperHalfPlane := by
  let T :=
    Classical.choose <|
      exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
        (d := d) OS lgc f g hg_compact
  let Fcore : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  let F : ℂ → ℂ := Fcore ∘ fun w => (((2 * Real.pi : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    have hmap :
        Set.MapsTo (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane SCV.upperHalfPlane := by
      intro z hz
      dsimp [SCV.upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane := by
      intro z hz
      simpa using
        ((((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (((2 * Real.pi : ℝ) : ℂ))).differentiableWithinAt))
    simpa [F, Fcore] using (SCV.fourierLaplaceExt_differentiableOn T).comp hmul hmap
  have hEq :
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact = F := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      change
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc f g hg_compact w =
          if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
            SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
          else 0
      rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, dif_pos hw, dif_pos hscaled]
    · have hnotscaled : ¬ 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        intro hscaled
        have hscaled' : 0 < (2 * Real.pi) * w.im := by
          simpa [Complex.mul_im, mul_assoc] using hscaled
        nlinarith [Real.two_pi_pos, hscaled']
      change
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc f g hg_compact w =
          if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
            SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
          else 0
      rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, dif_neg hw, dif_neg hnotscaled]
  rw [hEq]
  exact hF_diff

/-- The concrete canonical Stage-5 witness has polynomial growth on every
positive horizontal line. This is the exact growth package needed to keep the
later theorem-3 arguments on the canonical witness surface instead of falling
back to the older existential one. -/
private theorem hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (η : ℝ) (hη : 0 < η) :
    SCV.HasPolynomialGrowthOnLine
      (fun x =>
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I)) := by
  let T :=
    Classical.choose <|
      exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
        (d := d) OS lgc f g hg_compact
  obtain ⟨C, N, hC_nonneg, hbound⟩ :=
    SCV.fourierLaplaceExt_horizontal_growth T
      ((2 * Real.pi) * η) (mul_pos Real.two_pi_pos hη)
  refine ⟨C * (2 * Real.pi) ^ N, N, by positivity, fun x => ?_⟩
  have hw : 0 < (↑x + ↑η * Complex.I).im := by simpa using hη
  have hscaled :
      0 < ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I)).im) := by
    simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hη
  have hline :
      ‖SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled‖
        ≤ C * (1 + |(2 * Real.pi) * x|) ^ N := by
    simpa [mul_add, mul_assoc, add_comm, add_left_comm, add_assoc] using
      hbound ((2 * Real.pi) * x)
  have hscale_le : 1 + |(2 * Real.pi) * x| ≤ (2 * Real.pi) * (1 + |x|) := by
    have hpi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hpi_nonneg : 0 ≤ 2 * Real.pi := by positivity
    rw [abs_mul, abs_of_nonneg hpi_nonneg]
    nlinarith [abs_nonneg x]
  have hpow_le :
      (1 + |(2 * Real.pi) * x|) ^ N ≤ ((2 * Real.pi) * (1 + |x|)) ^ N := by
    exact pow_le_pow_left₀ (by positivity) hscale_le N
  calc
    ‖bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I)‖
        =
      ‖SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled‖ := by
          simp [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, hη, T]
    _ ≤ C * (1 + |(2 * Real.pi) * x|) ^ N := hline
    _ ≤ C * (((2 * Real.pi) * (1 + |x|)) ^ N) := by
          exact mul_le_mul_of_nonneg_left hpow_le (le_of_lt hC_nonneg)
    _ = C * ((2 * Real.pi) ^ N * (1 + |x|) ^ N) := by rw [mul_pow]
    _ = (C * (2 * Real.pi) ^ N) * (1 + |x|) ^ N := by ring

/-- Integrability of the canonical Stage-5 witness against Fourier transforms
of Schwartz tests along positive horizontal lines. This is the canonical-
witness analogue of the older existential-witness integrability package. -/
private theorem integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
  exact integrable_mul_fourierTransform_of_upperHalfPlaneWitness
    (H := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) OS lgc f g hg_compact)
    (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
      (d := d) (OS := OS) (lgc := lgc) f g hg_compact)
    (hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) (OS := OS) (lgc := lgc) f g hg_compact)
    χ hη

/-- The explicit canonical Stage-5 witness has the reconstructed Wightman
time-shift pairing as its distributional boundary value. This closes the
boundary-value half of the canonical-witness route and avoids falling back to
the older existential witness surface. -/
private theorem tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) * χ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * χ t)) := by
  let T :=
    Classical.choose <|
      exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
        (d := d) OS lgc f g hg_compact
  have hT_apply := Classical.choose_spec <|
    exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
      (d := d) OS lgc f g hg_compact
  have hT_supp : SCV.HasOneSidedFourierSupport T := by
    intro φ hφ_neg
    rw [hT_apply]
    exact hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g φ hφ_neg
  simpa [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, T, hT_apply χ] using
    (SCV.paley_wiener_half_line_explicit T hT_supp).2.2 χ

/-- On the positive imaginary axis, the canonical ambient witness is given by
the Fourier-Laplace integral of the real-time Wightman pairing functional
against the standard `ψ_z` kernel. This is the first concrete interior-value
formula for the Stage-5 ambient witness. -/
private theorem bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (η * Complex.I) =
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
          (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) t := by
  let T :=
    Classical.choose <|
      exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
        (d := d) OS lgc f g hg_compact
  have hT_apply := Classical.choose_spec <|
    exists_bvt_W_conjTensorProduct_timeShift_temperedFunctional
      (d := d) OS lgc f g hg_compact
  have him : 0 < (η * Complex.I).im := by
    simpa using hη
  rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, dif_pos him]
  rw [SCV.fourierLaplaceExt_eq]
  simpa [T] using
    hT_apply
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (η * Complex.I)))
          (by
            simpa [Complex.mul_im, hη.ne']
              using mul_pos Real.two_pi_pos hη)))

/-- Zero-translation specialization of the proved Schwinger-side `t → 0+` limit
for the compact ordered positive-time `singleSplit_xiShift` shell.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298

This packages the OS/Schwinger side only; it does not identify the Wightman
boundary value yet. -/
theorem bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct g) y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct g)))) := by
  have ha0_zero : (Fin.cons 0 (0 : Fin d → ℝ) : SpacetimeDim d) = 0 := by
    funext μ
    refine Fin.cases ?_ ?_ μ
    · simp
    · intro i
      simp
  have htranslate_zero :
      translateSchwartzNPoint (d := d) (Fin.cons 0 (0 : Fin d → ℝ)) g = g := by
    ext x
    simp [translateSchwartzNPoint_apply, ha0_zero]
  simpa [htranslate_zero] using
    bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact (0 : Fin d → ℝ)

/-- The OS one-variable holomorphic bridge behind the compact ordered
positive-time `singleSplit_xiShift` shell comes with its boundary limit to the
Euclidean Schwinger tensor term.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter V, pp. 290-297 for the holomorphic continuation machinery
- OS II Chapter VI.1, pp. 297-298 for the current boundary-limit stage

This packages the semigroup-side part of the positivity route as an honest
scalar holomorphic statement. -/
theorem bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y) ∧
      Filter.Tendsto
        (fun t : ℝ => H (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct g)))) := by
  rcases bvt_exists_singleSplit_xiShift_holomorphicValue
      (d := d) OS lgc hm f hf_ord g hg_ord hg_compact with
    ⟨H, hH_holo, hH_real⟩
  refine ⟨H, hH_holo, hH_real, ?_⟩
  have htrace :
      (fun t : ℝ => H (t : ℂ))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hH_real t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
      (d := d) OS lgc n m hm f hf_ord hf_compact g hg_ord hg_compact

/-- Chosen scalar holomorphic trace whose positive-real boundary is the
`singleSplit_xiShift` shell for compact ordered positive-time data.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter V, pp. 290-297

This is a production wrapper around the already-proved OS-side holomorphic
matrix element. -/
noncomputable def bvt_singleSplit_xiShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) : ℂ → ℂ :=
  Classical.choose <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact

theorem differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    DifferentiableOn ℂ
      (bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
      {z : ℂ | 0 < z.re} :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).1

theorem bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).2.1 t ht

/-- On positive real times, the chosen scalar holomorphic `singleSplit_xiShift`
trace is exactly the Schwinger value of the right time-shifted simple tensor. -/
theorem bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  calc
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y :=
      bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
        (d := d) (OS := OS) (lgc := lgc) hm
        f hf_ord hf_compact g hg_ord hg_compact t ht
    _ =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
      symm
      exact schwinger_simpleTensor_timeShift_eq_xiShift
        (d := d) (OS := OS) (hm := hm) (Ψ := bvt_F OS lgc (n + m))
        (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
        (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct g)))) :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).2.2

/-- If the positive-real Schwinger values of the chosen `singleSplit_xiShift`
trace are already identified with the reconstructed Wightman pairing against the
right-time-shifted test function, then the current theorem-3 limit hypothesis
follows immediately. -/
/-
Deprecated route note:

The hypothesis `hschw` below is mathematically false on the intended theorem
surface. The left-hand side is the Euclidean/OS time-shifted Schwinger pairing,
whose free-field momentum-space form carries a Laplace factor `e^{-ω_p t}` and
Laplace-transformed test functions. The right-hand side is the reconstructed
Wightman boundary-value pairing against a real Minkowski time translation,
whose free-field momentum-space form carries the oscillatory factor
`e^{-i ω_p t}` and the Fourier-transformed test functions.

So this theorem remains a logically valid implication from a false premise, but
it is dead-end infrastructure and not part of the endorsed theorem-3 route. -/
theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hschw :
      ∀ t : ℝ, 0 < t →
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
          =
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (f.conjTensorProduct g))) := by
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
        =
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :=
        bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
          (d := d) (OS := OS) (lgc := lgc) hm
          f hf_ord hf_compact g hg_ord hg_compact t ht
      _ =
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
        hschw t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (OS := OS) (lgc := lgc) f g hg_compact

/-- If the chosen scalar holomorphic `singleSplit_xiShift` trace agrees on the
positive real axis with the reconstructed Wightman pairing against the
right-time-shifted test function, then its `t → 0+` limit is exactly the
theorem-3 boundary-value target.

This turns the current abstract compact-shell hypothesis `hHlimit` into the
more concrete OS-route task of identifying positive real Euclidean time shifts
with the corresponding Wightman pairing. -/
theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (f.conjTensorProduct g))) := by
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (OS := OS) (lgc := lgc) f g hg_compact

/-- Ambient-representative variant of the same theorem: if the chosen scalar
`singleSplit_xiShift` trace built from positive-time preimages `f, g` agrees on
positive real times with the reconstructed Wightman pairing against ambient
representatives `φ, ψ`, then its `t → 0+` limit is exactly
`bvt_W (φ.conjTensorProduct ψ)`.

This is the internal-supplier form used on the corrected Section-4.3 route:
the public theorem surface stays on the ambient representative/preimage data,
while the one-variable holomorphic trace remains local to this file. -/
theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_ambient_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (φ : SchwartzNPoint d n)
    (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct ψ))) := by
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (OS := OS) (lgc := lgc) φ ψ hψ_compact

/-- On the right half-plane, a holomorphic scalar trace is determined by its
positive-real values.

OS paper role:
- auxiliary uniqueness principle for the OS II theorem-3 lane
- used to keep the remaining gap in the shape "construct the Wightman-side
  holomorphic realization with the same positive-real values"

This is not itself quoted as a numbered OS theorem; it is a local analytic
uniqueness lemma used to keep the production theorem surface honest. -/
theorem eqOn_rightHalfPlane_of_ofReal_eq
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hreal : ∀ t : ℝ, 0 < t → H₀ (t : ℂ) = H₁ (t : ℂ)) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hpos : 0 < 1 + ε := by linarith
    exact hV_sub ⟨hz_in_V, hz_ne⟩ (hreal (1 + ε) hpos)
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Any holomorphic realization of the positive-real `singleSplit_xiShift`
shell must agree with the chosen scalar trace on the full right half-plane. -/
theorem bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real : ∀ t : ℝ, 0 < t →
      H (t : ℂ) =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) :
    Set.EqOn H
      (bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
      {z : ℂ | 0 < z.re} := by
  exact eqOn_rightHalfPlane_of_ofReal_eq H
    (bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
    hH_holo
    (differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
    (fun t ht => by
      rw [hH_real t ht,
        bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
          (d := d) (OS := OS) (lgc := lgc) hm f hf_ord hf_compact g hg_ord hg_compact t ht])

/-- Positivity comparison on compact ordered positive-time Borchers vectors,
restated so that the remaining theorem-3 seam is the Wightman boundary value of
the chosen scalar holomorphic `singleSplit_xiShift` trace rather than a raw
integral net.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current boundary-value substep -/
theorem bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((G : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((G : BorchersSequence d).funcs 0)))))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((G : BorchersSequence d).funcs m))
              (G.ordered_tsupport m)
              (hG_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((G : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d) (G : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  apply
    bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) F G hF_compact hG_compact hzero
  intro n m hm
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n)
          (hF_compact n)
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m)
          (hG_compact m) (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((G : BorchersSequence d).funcs m)) y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n)
      (hF_compact n)
      (((G : BorchersSequence d).funcs m))
      (G.ordered_tsupport m)
      (hG_compact m) t ht
  exact Filter.Tendsto.congr' htrace (hHlimit n m hm)

/-- In the self-pair case, the same chosen scalar holomorphic trace already
reduces positivity to OS reflection positivity.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II IV.2, p. 288
- current substep on the active route: OS II Chapter VI.1, pp. 297-298

This is the sharpened theorem-3 surface: the remaining gap is the Wightman
boundary value of that scalar trace, not any semigroup-side continuity
statement. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)))))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  rw [bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (d := d) (OS := OS) (lgc := lgc) F F hF_compact hF_compact hzero hHlimit]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-- The same theorem-3 positivity reduction, with the degree-`0` repair
internalized via Hermiticity of the reconstructed boundary values.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current boundary-value substep

This is a real blocker shrink on the active OS route: after the OS/Schwinger
limit is packaged for the chosen holomorphic trace, the only remaining exposed
input is the Wightman-side boundary-value identification `hHlimit`. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  apply
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) hherm F hF_compact
  intro n m hm
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n)
          (hF_compact n)
          (((F : BorchersSequence d).funcs m))
          (F.ordered_tsupport m)
          (hF_compact m) (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs m)) y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n)
      (hF_compact n)
      (((F : BorchersSequence d).funcs m))
      (F.ordered_tsupport m)
      (hF_compact m) t ht
  exact Filter.Tendsto.congr' htrace (hHlimit n m hm)
