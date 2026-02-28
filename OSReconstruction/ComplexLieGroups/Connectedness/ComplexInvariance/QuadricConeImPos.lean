import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {m : ℕ}

private def etaContractFixed
    (c : ℂ) (η : MinkowskiSpace (m + 1)) (t : ℝ) : MinkowskiSpace (m + 1) :=
  fun μ =>
    Fin.cases
      (Real.sqrt (c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η))
      (fun i => (1 - t) * η i.succ) μ

private lemma minkowskiNormSq_etaContractFixed
    (c : ℂ) (η : MinkowskiSpace (m + 1)) (t : ℝ) :
    MinkowskiSpace.minkowskiNormSq (m + 1) (etaContractFixed (m := m) c η t) = -c.im ^ 2 := by
  have hs_nonneg : 0 ≤ MinkowskiSpace.spatialNormSq (m + 1) η := by
    exact MinkowskiSpace.spatialNormSq_nonneg (d := m + 1) η
  have harg_nonneg :
      0 ≤ c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by
    nlinarith [sq_nonneg c.im, sq_nonneg (1 - t), hs_nonneg]
  have htime_sq :
      (etaContractFixed (m := m) c η t 0) ^ 2 =
        c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by
    simp [etaContractFixed, Real.sq_sqrt, harg_nonneg]
  have hspatial :
      MinkowskiSpace.spatialNormSq (m + 1) (etaContractFixed (m := m) c η t) =
        (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by
    unfold MinkowskiSpace.spatialNormSq
    simp [etaContractFixed]
    calc
      ∑ i : Fin (m + 1), ((1 - t) * η i.succ) ^ 2
          = ∑ i : Fin (m + 1), (1 - t) ^ 2 * η i.succ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (1 - t) ^ 2 * ∑ i : Fin (m + 1), η i.succ ^ 2 := by
            simp [Finset.mul_sum]
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  rw [htime_sq, hspatial]
  ring

private lemma inOpenForwardCone_etaContractFixed
    (c : ℂ) (η : MinkowskiSpace (m + 1)) (hcim : 0 < c.im) (t : ℝ) :
    InOpenForwardCone (m + 1) (etaContractFixed (m := m) c η t) := by
  refine ⟨?_, ?_⟩
  · have harg_pos :
      0 < c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by
      nlinarith [sq_pos_of_pos hcim, MinkowskiSpace.spatialNormSq_nonneg (d := m + 1) η]
    simpa [etaContractFixed] using Real.sqrt_pos.mpr harg_pos
  · have hnorm := minkowskiNormSq_etaContractFixed (m := m) c η t
    have hneg_norm :
        MinkowskiSpace.minkowskiNormSq (m + 1) (etaContractFixed (m := m) c η t) < 0 := by
      nlinarith [hnorm, hcim]
    simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, minkowskiSignature, sq, pow_two] using hneg_norm

private lemma etaContractFixed_zero
    (c : ℂ) (η : MinkowskiSpace (m + 1))
    (hcone : InOpenForwardCone (m + 1) η)
    (hηnorm : MinkowskiSpace.minkowskiNormSq (m + 1) η = -c.im ^ 2) :
    etaContractFixed (m := m) c η 0 = η := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · have hs_nonneg : 0 ≤ MinkowskiSpace.spatialNormSq (m + 1) η := by
      exact MinkowskiSpace.spatialNormSq_nonneg (d := m + 1) η
    have hsq : η 0 ^ 2 = c.im ^ 2 + MinkowskiSpace.spatialNormSq (m + 1) η := by
      rw [MinkowskiSpace.minkowskiNormSq_decomp] at hηnorm
      linarith
    have hpos : 0 ≤ η 0 := le_of_lt hcone.1
    have hsqrt :
        Real.sqrt (c.im ^ 2 + MinkowskiSpace.spatialNormSq (m + 1) η) = η 0 := by
      have harg_nonneg : 0 ≤ c.im ^ 2 + MinkowskiSpace.spatialNormSq (m + 1) η := by
        nlinarith [sq_nonneg c.im, hs_nonneg]
      rw [← hsq, Real.sqrt_sq hpos]
    simp [etaContractFixed, hsqrt]
  · intro i
    simp [etaContractFixed]

private lemma etaContractFixed_one
    (c : ℂ) (hcim : 0 < c.im) :
    etaContractFixed (m := m) c (fun μ => if μ = 0 then c.im else 0) 1 =
      (fun μ => if μ = 0 then c.im else 0) := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [etaContractFixed, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hcim)]
  · intro i
    simp [etaContractFixed]

private lemma parallel_value_etaContractFixed
    (c : ℂ) (η : MinkowskiSpace (m + 1)) (t : ℝ) :
    (fun μ : Fin (m + 2) =>
      (((c.re / c.im) * (etaContractFixed (m := m) c η t μ) : ℝ) : ℂ) +
        ((etaContractFixed (m := m) c η t μ : ℝ) : ℂ) * Complex.I)
      =
    (fun μ : Fin (m + 2) =>
      if μ = 0 then
        (Real.sqrt (c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η) : ℂ) *
          ((c.re / c.im : ℝ) + Complex.I)
      else
        ((1 - t) * η μ : ℝ) * ((c.re / c.im : ℝ) + Complex.I)) := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [etaContractFixed, mul_add]
    ring
  · intro i
    simp [etaContractFixed, mul_add]
    ring

private lemma etaContractFixed_one_general
    (c : ℂ) (η : MinkowskiSpace (m + 1)) (hcim : 0 < c.im) :
    etaContractFixed (m := m) c η 1 = (fun μ => if μ = 0 then c.im else 0) := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [etaContractFixed, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hcim)]
  · intro i
    simp [etaContractFixed]

private lemma continuous_etaContractFixed
    (c : ℂ) (η : MinkowskiSpace (m + 1)) :
    Continuous (fun t : ℝ => etaContractFixed (m := m) c η t) := by
  apply continuous_pi
  intro μ
  refine Fin.cases ?_ ?_ μ
  · have harg :
        Continuous
          (fun t : ℝ =>
            c.im ^ 2 + (1 - t) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η) :=
      continuous_const.add
        (((continuous_const.sub continuous_id).pow 2).mul continuous_const)
    simpa [etaContractFixed] using harg.sqrt
  · intro i
    simpa [etaContractFixed] using
      (continuous_const.sub continuous_id).mul continuous_const

private lemma joinedIn_parallelSlice_to_canonical
    (c : ℂ) (hcim : 0 < c.im)
    (η : MinkowskiSpace (m + 1))
    (hcone : InOpenForwardCone (m + 1) η)
    (hηnorm : MinkowskiSpace.minkowskiNormSq (m + 1) η = -c.im ^ 2) :
    JoinedIn
      (quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
      (fun μ : Fin (m + 2) =>
        (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I))
      (fun μ : Fin (m + 2) => if μ = 0 then c else 0) := by
  have hηcontI :
      Continuous (fun t : Set.Icc (0 : ℝ) 1 => etaContractFixed (m := m) c η t) :=
    (continuous_etaContractFixed (m := m) c η).comp continuous_subtype_val
  let p : Path
      (fun μ : Fin (m + 2) =>
        (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I))
      (fun μ : Fin (m + 2) => if μ = 0 then c else 0) :=
    { toFun := fun t =>
        (fun μ : Fin (m + 2) =>
          (((c.re / c.im) * (etaContractFixed (m := m) c η t μ) : ℝ) : ℂ) +
            ((etaContractFixed (m := m) c η t μ : ℝ) : ℂ) * Complex.I)
      continuous_toFun := by
        apply continuous_pi
        intro μ
        have hμ :
            Continuous (fun t : Set.Icc (0 : ℝ) 1 => etaContractFixed (m := m) c η t μ) :=
          (continuous_apply μ).comp hηcontI
        have hμc :
            Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
              ((etaContractFixed (m := m) c η t μ : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp hμ
        have hre :
            Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
              (((c.re / c.im) * (etaContractFixed (m := m) c η t μ) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_const.mul hμ)
        exact hre.add (hμc.mul continuous_const)
      source' := by
        ext μ
        simp [etaContractFixed_zero, hcone, hηnorm]
      target' := by
        ext μ
        have hη1 : etaContractFixed (m := m) c η 1 = (fun ν => if ν = 0 then c.im else 0) :=
          etaContractFixed_one_general (m := m) c η hcim
        refine Fin.cases ?_ ?_ μ
        · simp [hη1, hcim.ne']
        · intro i
          simp [hη1] }
  refine ⟨p, ?_⟩
  intro t
  have hcone_t :
      InOpenForwardCone (m + 1) (etaContractFixed (m := m) c η t) :=
    inOpenForwardCone_etaContractFixed (m := m) c η hcim t
  have hnorm_t :
      MinkowskiSpace.minkowskiNormSq (m + 1) (etaContractFixed (m := m) c η t) = -c.im ^ 2 :=
    minkowskiNormSq_etaContractFixed (m := m) c η t
  exact parallel_mem_quadricConeSet_im_with_value (m := m) c hcim
    (etaContractFixed (m := m) c η t) hcone_t hnorm_t

private def parallelPoint
    (c : ℂ) (η : MinkowskiSpace (m + 1)) :
    Fin (m + 2) → ℂ :=
  fun μ => (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I)

private lemma minkowskiNormSq_smul
    (a : ℝ) (η : MinkowskiSpace (m + 1)) :
    MinkowskiSpace.minkowskiNormSq (m + 1) (a • η) =
      a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
  unfold MinkowskiSpace.minkowskiNormSq
  rw [MinkowskiSpace.minkowskiInner_smul_left, MinkowskiSpace.minkowskiInner_smul_right]
  ring

private lemma orthogonal_timelike_norm_zero_eq_zero
    (ζ η : MinkowskiSpace (m + 1))
    (hcone : InOpenForwardCone (m + 1) η)
    (horth : MinkowskiSpace.minkowskiInner (m + 1) ζ η = 0)
    (hzero : MinkowskiSpace.minkowskiNormSq (m + 1) ζ = 0) :
    ζ = 0 := by
  have hdom :
      (η 0) ^ 2 > MinkowskiSpace.spatialNormSq (m + 1) η := by
    have hηtimelike : MinkowskiSpace.IsTimelike (m + 1) η := by
      simpa [MinkowskiSpace.IsTimelike, MinkowskiSpace.minkowskiNormSq,
        MinkowskiSpace.minkowskiInner, MinkowskiSpace.metricSignature,
        minkowskiSignature, sq] using hcone.2
    simpa using MinkowskiSpace.timelike_time_dominates_space (d := m + 1) η hηtimelike
  have hsi : ζ 0 * η 0 = MinkowskiSpace.spatialInner (m + 1) ζ η := by
    rw [MinkowskiSpace.minkowskiInner_eq_time_spatial (d := m + 1) ζ η] at horth
    linarith
  have hsq :
      (ζ 0) ^ 2 * (η 0) ^ 2 = (MinkowskiSpace.spatialInner (m + 1) ζ η) ^ 2 := by
    have := congrArg (fun x : ℝ => x ^ 2) hsi
    nlinarith [this]
  have hcs := MinkowskiSpace.spatial_cauchy_schwarz (d := m + 1) ζ η
  have hspζ_eq : MinkowskiSpace.spatialNormSq (m + 1) ζ = (ζ 0) ^ 2 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp (d := m + 1) ζ] at hzero
    linarith
  have hz0 : ζ 0 = 0 := by
    by_contra hz0ne
    have hz0_sq_pos : 0 < (ζ 0) ^ 2 := sq_pos_of_ne_zero hz0ne
    have hineq :
        (ζ 0) ^ 2 * (η 0) ^ 2 ≤ (ζ 0) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by
      calc
        (ζ 0) ^ 2 * (η 0) ^ 2 = (MinkowskiSpace.spatialInner (m + 1) ζ η) ^ 2 := hsq
        _ ≤ MinkowskiSpace.spatialNormSq (m + 1) ζ * MinkowskiSpace.spatialNormSq (m + 1) η := hcs
        _ = (ζ 0) ^ 2 * MinkowskiSpace.spatialNormSq (m + 1) η := by rw [hspζ_eq]
    have hineq' : (η 0) ^ 2 ≤ MinkowskiSpace.spatialNormSq (m + 1) η := by
      nlinarith [hineq, hz0_sq_pos]
    linarith [hdom, hineq']
  have hspζ_zero : MinkowskiSpace.spatialNormSq (m + 1) ζ = 0 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp (d := m + 1) ζ] at hzero
    simp [hz0] at hzero
    exact hzero
  have hsp_comp_zero : ∀ i : Fin (m + 1), ζ i.succ = 0 := by
    have hsum_zero : ∑ i : Fin (m + 1), ζ i.succ ^ 2 = 0 := by
      simpa [MinkowskiSpace.spatialNormSq] using hspζ_zero
    have hsum_each := Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) => sq_nonneg (ζ i.succ))
    intro i
    exact sq_eq_zero_iff.mp (hsum_each.mp hsum_zero i (Finset.mem_univ i))
  ext μ
  refine Fin.cases ?_ ?_ μ
  · exact hz0
  · intro i
    exact hsp_comp_zero i

private theorem quadricConeSet_im_with_value_isPreconnected_of_im_pos
    (c : ℂ) (hcim : 0 < c.im) :
    IsPreconnected (quadricConeSet_im_with_value (m := m) (-(c ^ 2))) := by
  refine
    (isPreconnected_of_joinedIn_base
      (S := quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
      (x0 := (fun μ : Fin (m + 2) => if μ = 0 then c else 0)) ?_ ?_)
  · exact canonical_mem_quadricConeSet_im_with_value (m := m) c hcim
  · intro u hu
    let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
    let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
    rcases (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) u).1 hu with
      ⟨hcone, hinner, hnorm⟩
    set q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
    set K : ℝ := -(c.re * c.im)
    set ζ : MinkowskiSpace (m + 1) := ξ - (K / q) • η
    have hqneg : q < 0 := by
      have : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
        simpa [η, InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
          MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
      simpa [q] using this
    have hqlow : -c.im ^ 2 ≤ q := by
      simpa [q, η] using minkowskiNormSq_eta_lower_bound (m := m) c u hu
    by_cases hζ0 : MinkowskiSpace.minkowskiNormSq (m + 1) ζ = 0
    · have hqeq : q = -c.im ^ 2 := by
        simpa [ξ, η, q, K, ζ] using
          q_eq_neg_im_sq_of_zero_orth_component (m := m) c u hu hζ0
      have hinner_eval : MinkowskiSpace.minkowskiInner (m + 1) ξ η = K := by
        have hk_im : (-(c ^ 2)).im / 2 = K := by
          simp [K, pow_two, Complex.mul_im]
          ring
        linarith [hinner, hk_im]
      have hdecomp := minkowskiNormSq_decompose_along_timelike (m := m) ξ η hcone
      rcases hdecomp with ⟨horth0, _⟩
      have hKq : K / q = (MinkowskiSpace.minkowskiInner (m + 1) ξ η) / q := by
        rw [hinner_eval]
      have horth : MinkowskiSpace.minkowskiInner (m + 1) ζ η = 0 := by
        simpa [ζ, q, hKq] using horth0
      have hζeq : ζ = 0 :=
        orthogonal_timelike_norm_zero_eq_zero (m := m) ζ η hcone horth hζ0
      have hξeq : ξ = (K / q) • η := by
        have : ξ - (K / q) • η = 0 := by simpa [ζ] using hζeq
        exact sub_eq_zero.mp this
      have hcoef : K / MinkowskiSpace.minkowskiNormSq (m + 1) η = c.re / c.im := by
        have hqeq' : MinkowskiSpace.minkowskiNormSq (m + 1) η = -c.im ^ 2 := by
          simpa [q] using hqeq
        calc
          K / MinkowskiSpace.minkowskiNormSq (m + 1) η
              = (-(c.re * c.im)) / (-c.im ^ 2) := by simp [K, hqeq']
          _ = c.re / c.im := by
                field_simp [hcim.ne']
      have hparallel :
          u =
            parallelPoint (m := m) c η := by
        ext μ
        calc
          u μ = ((u μ).re : ℂ) + ((u μ).im : ℂ) * Complex.I := (Complex.re_add_im (u μ)).symm
          _ = ((ξ μ : ℝ) : ℂ) + ((η μ : ℝ) : ℂ) * Complex.I := by simp [ξ, η]
          _ = ((((K / q) • η) μ : ℝ) : ℂ) + ((η μ : ℝ) : ℂ) * Complex.I := by
                simp [hξeq]
          _ = (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I) := by
                simp [hcoef, q, Pi.smul_apply, smul_eq_mul]
          _ = parallelPoint (m := m) c η μ := rfl
      rw [hparallel]
      change
        JoinedIn
          (quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
          (fun μ : Fin (m + 2) => if μ = 0 then c else 0)
          (fun μ : Fin (m + 2) =>
            (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I))
      exact (joinedIn_parallelSlice_to_canonical (m := m) c hcim η hcone
        (by simpa [q] using hqeq)).symm
    · -- Main remaining branch: contract the orthogonal component `ζ` to zero while
      -- preserving membership in `quadricConeSet_im_with_value (-(c^2))`.
      have hinner_eval : MinkowskiSpace.minkowskiInner (m + 1) ξ η = K := by
        have hk_im : (-(c ^ 2)).im / 2 = K := by
          simp [K, pow_two, Complex.mul_im]
          ring
        linarith [hinner, hk_im]
      have hdecomp := minkowskiNormSq_decompose_along_timelike (m := m) ξ η hcone
      rcases hdecomp with ⟨horth0, hnorm_decomp0⟩
      have hKq : K / q = (MinkowskiSpace.minkowskiInner (m + 1) ξ η) / q := by
        rw [hinner_eval]
      have horth : MinkowskiSpace.minkowskiInner (m + 1) ζ η = 0 := by
        simpa [ζ, q, hKq] using horth0
      have hηtimelike : MinkowskiSpace.IsTimelike (m + 1) η := by
        simpa [MinkowskiSpace.IsTimelike, InOpenForwardCone, MinkowskiSpace.minkowskiNormSq,
          MinkowskiSpace.minkowskiInner, MinkowskiSpace.metricSignature, minkowskiSignature, sq]
          using hcone.2
      have hηfuture : MinkowskiSpace.IsFutureDirected (m + 1) η := by
        simpa [MinkowskiSpace.IsFutureDirected, MinkowskiSpace.timeComponent, InOpenForwardCone]
          using hcone.1
      have hζ_nonneg : 0 ≤ MinkowskiSpace.minkowskiNormSq (m + 1) ζ :=
        MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
          (d := m + 1) ζ η hηtimelike hηfuture horth
      set z2 : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) ζ
      have hz2pos : 0 < z2 := by
        have hz2ne : z2 ≠ 0 := by
          intro hz2eq
          exact hζ0 (by simpa [z2] using hz2eq)
        exact lt_of_le_of_ne (by simpa [z2] using hζ_nonneg) (Ne.symm hz2ne)
      let r : ℝ := -c.im ^ 2
      let M : ℝ := c.im ^ 2 - c.re ^ 2
      let qLine : Set.Icc (0 : ℝ) 1 → ℝ := fun t => (1 - (t : ℝ)) * q + (t : ℝ) * r
      let num : Set.Icc (0 : ℝ) 1 → ℝ :=
        fun t => qLine t ^ 2 + M * qLine t - (c.re * c.im) ^ 2
      let scale : Set.Icc (0 : ℝ) 1 → ℝ := fun t => Real.sqrt (qLine t / q)
      let etaPath : Set.Icc (0 : ℝ) 1 → MinkowskiSpace (m + 1) := fun t => scale t • η
      let lam : Set.Icc (0 : ℝ) 1 → ℝ := fun t => Real.sqrt (num t / (qLine t * z2))
      let xiPath : Set.Icc (0 : ℝ) 1 → MinkowskiSpace (m + 1) :=
        fun t => (K / qLine t) • etaPath t + lam t • ζ
      let uPath : Set.Icc (0 : ℝ) 1 → (Fin (m + 2) → ℂ) :=
        fun t μ => ((xiPath t μ : ℝ) : ℂ) + ((etaPath t μ : ℝ) : ℂ) * Complex.I
      have hrneg : r < 0 := by
        nlinarith [sq_pos_of_pos hcim]
      have hqne : q ≠ 0 := ne_of_lt hqneg
      have hqline_neg : ∀ t : Set.Icc (0 : ℝ) 1, qLine t < 0 := by
        intro t
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        nlinarith [hqneg, hrneg, ht0, ht1]
      have hqline_lower : ∀ t : Set.Icc (0 : ℝ) 1, r ≤ qLine t := by
        intro t
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        nlinarith [hqlow, ht0, ht1, r]
      have hcone_etaPath :
          ∀ t : Set.Icc (0 : ℝ) 1, InOpenForwardCone (m + 1) (etaPath t) := by
        intro t
        have hqline_div_q_pos : 0 < qLine t / q :=
          div_pos_of_neg_of_neg (hqline_neg t) hqneg
        have hscale_pos : 0 < scale t := by
          simpa [scale] using Real.sqrt_pos.mpr hqline_div_q_pos
        simpa [etaPath] using
          inOpenForwardCone_smul_pos (d := m + 1) (η := η) hcone hscale_pos
      have hnorm_etaPath :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiNormSq (m + 1) (etaPath t) = qLine t := by
        intro t
        have hqline_div_q_nonneg : 0 ≤ qLine t / q := by
          exact le_of_lt (div_pos_of_neg_of_neg (hqline_neg t) hqneg)
        calc
          MinkowskiSpace.minkowskiNormSq (m + 1) (etaPath t)
              = (scale t) ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
                  simpa [etaPath] using minkowskiNormSq_smul (m := m) (scale t) η
          _ = (qLine t / q) * q := by
                simp [scale, q, Real.sq_sqrt, hqline_div_q_nonneg]
          _ = qLine t := by field_simp [hqne]
      have hnum_nonpos : ∀ t : Set.Icc (0 : ℝ) 1, num t ≤ 0 := by
        intro t
        have hA_nonneg : 0 ≤ qLine t + c.im ^ 2 := by
          nlinarith [hqline_lower t, r]
        have hB_nonpos : qLine t - c.re ^ 2 ≤ 0 := by
          nlinarith [hqline_neg t, sq_nonneg c.re]
        have hfac : num t = (qLine t + c.im ^ 2) * (qLine t - c.re ^ 2) := by
          dsimp [num, qLine, M, r]
          ring
        rw [hfac]
        exact mul_nonpos_of_nonneg_of_nonpos hA_nonneg hB_nonpos
      have hratio_nonneg :
          ∀ t : Set.Icc (0 : ℝ) 1, 0 ≤ num t / (qLine t * z2) := by
        intro t
        have hden_neg : qLine t * z2 < 0 := mul_neg_of_neg_of_pos (hqline_neg t) hz2pos
        exact div_nonneg_of_nonpos (hnum_nonpos t) (le_of_lt hden_neg)
      have hqline_ne : ∀ t : Set.Icc (0 : ℝ) 1, qLine t ≠ 0 := fun t =>
        ne_of_lt (hqline_neg t)
      have hz2ne : z2 ≠ 0 := ne_of_gt hz2pos
      have hqlinez2_ne : ∀ t : Set.Icc (0 : ℝ) 1, qLine t * z2 ≠ 0 := by
        intro t
        exact mul_ne_zero (hqline_ne t) hz2ne
      have hqLine_cont : Continuous qLine := by
        dsimp [qLine]
        exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
          (continuous_subtype_val.mul continuous_const)
      have hnum_cont : Continuous num := by
        dsimp [num]
        exact ((hqLine_cont.pow 2).add (continuous_const.mul hqLine_cont)).sub continuous_const
      have hratio_cont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => num t / (qLine t * z2)) :=
        hnum_cont.div (hqLine_cont.mul continuous_const) hqlinez2_ne
      have hscale_cont : Continuous scale := by
        have hratio_q_cont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => qLine t / q) :=
          hqLine_cont.div continuous_const (fun _ => hqne)
        simpa [scale] using hratio_q_cont.sqrt
      have hlam_cont : Continuous lam := by
        simpa [lam] using hratio_cont.sqrt
      have hetaPath_cont : Continuous etaPath := by
        apply continuous_pi
        intro μ
        simpa [etaPath, Pi.smul_apply, smul_eq_mul] using hscale_cont.mul continuous_const
      have hxiPath_cont : Continuous xiPath := by
        apply continuous_pi
        intro μ
        have hKdiv_cont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => K / qLine t) :=
          continuous_const.div hqLine_cont hqline_ne
        have hterm1 :
            Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
              ((K / qLine t) • etaPath t) μ) := by
          simpa [Pi.smul_apply, smul_eq_mul] using
            hKdiv_cont.mul ((continuous_apply μ).comp hetaPath_cont)
        have hterm2 :
            Continuous (fun t : Set.Icc (0 : ℝ) 1 => (lam t • ζ) μ) := by
          simpa [Pi.smul_apply, smul_eq_mul] using hlam_cont.mul continuous_const
        simpa [xiPath] using hterm1.add hterm2
      have huPath_cont : Continuous uPath := by
        apply continuous_pi
        intro μ
        have hxiμ : Continuous (fun t : Set.Icc (0 : ℝ) 1 => xiPath t μ) :=
          (continuous_apply μ).comp hxiPath_cont
        have hetaμ : Continuous (fun t : Set.Icc (0 : ℝ) 1 => etaPath t μ) :=
          (continuous_apply μ).comp hetaPath_cont
        exact (Complex.continuous_ofReal.comp hxiμ).add
          ((Complex.continuous_ofReal.comp hetaμ).mul continuous_const)
      have hk_im : (-(c ^ 2)).im / 2 = K := by
        simp [K, pow_two, Complex.mul_im]
        ring
      have hk_re : (-(c ^ 2)).re = M := by
        simp [M, pow_two, Complex.mul_re]
      have hinner_zeta_etaPath :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiInner (m + 1) ζ (etaPath t) = 0 := by
        intro t
        calc
          MinkowskiSpace.minkowskiInner (m + 1) ζ (etaPath t)
              = scale t * MinkowskiSpace.minkowskiInner (m + 1) ζ η := by
                  simp [etaPath, MinkowskiSpace.minkowskiInner_smul_right]
          _ = 0 := by simp [horth]
      have hinner_etaPath_zeta :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiInner (m + 1) (etaPath t) ζ = 0 := by
        intro t
        simpa [MinkowskiSpace.minkowskiInner_comm] using hinner_zeta_etaPath t
      have hinner_xiPath_etaPath :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiInner (m + 1) (xiPath t) (etaPath t) = K := by
        intro t
        calc
          MinkowskiSpace.minkowskiInner (m + 1) (xiPath t) (etaPath t)
              = MinkowskiSpace.minkowskiInner (m + 1)
                  ((K / qLine t) • etaPath t + lam t • ζ) (etaPath t) := by
                    rfl
          _ = (K / qLine t) * MinkowskiSpace.minkowskiInner (m + 1) (etaPath t) (etaPath t) +
                (lam t) * MinkowskiSpace.minkowskiInner (m + 1) ζ (etaPath t) := by
                  simp [MinkowskiSpace.minkowskiInner_add_left,
                    MinkowskiSpace.minkowskiInner_smul_left]
          _ = (K / qLine t) * qLine t + (lam t) * 0 := by
                have hηη :
                    MinkowskiSpace.minkowskiInner (m + 1) (etaPath t) (etaPath t) = qLine t := by
                  simpa [MinkowskiSpace.minkowskiNormSq] using hnorm_etaPath t
                simp [hηη, hinner_zeta_etaPath t]
          _ = K := by
                have hmul : (K / qLine t) * qLine t = K := by
                  field_simp [hqline_ne t]
                simp [hmul]
      have hlam_sq :
          ∀ t : Set.Icc (0 : ℝ) 1, (lam t) ^ 2 = num t / (qLine t * z2) := by
        intro t
        simp [lam, Real.sq_sqrt, hratio_nonneg t]
      have hnorm_xiPath :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiNormSq (m + 1) (xiPath t) =
              (K / qLine t) ^ 2 * qLine t + (lam t) ^ 2 * z2 := by
        intro t
        calc
          MinkowskiSpace.minkowskiNormSq (m + 1) (xiPath t)
              = MinkowskiSpace.minkowskiInner (m + 1)
                  ((K / qLine t) • etaPath t + lam t • ζ)
                  ((K / qLine t) • etaPath t + lam t • ζ) := by
                    rfl
          _ = MinkowskiSpace.minkowskiInner (m + 1)
                ((K / qLine t) • etaPath t) ((K / qLine t) • etaPath t)
              + MinkowskiSpace.minkowskiInner (m + 1)
                  ((K / qLine t) • etaPath t) (lam t • ζ)
              + (MinkowskiSpace.minkowskiInner (m + 1)
                  (lam t • ζ) ((K / qLine t) • etaPath t)
                + MinkowskiSpace.minkowskiInner (m + 1)
                    (lam t • ζ) (lam t • ζ)) := by
                rw [MinkowskiSpace.minkowskiInner_add_left, MinkowskiSpace.minkowskiInner_add_right,
                  MinkowskiSpace.minkowskiInner_add_right]
          _ = (K / qLine t) ^ 2 * qLine t + 0 + (0 + (lam t) ^ 2 * z2) := by
                have hηη :
                    MinkowskiSpace.minkowskiInner (m + 1) (etaPath t) (etaPath t) = qLine t := by
                  simpa [MinkowskiSpace.minkowskiNormSq] using hnorm_etaPath t
                simp [MinkowskiSpace.minkowskiInner_smul_left,
                  MinkowskiSpace.minkowskiInner_smul_right, MinkowskiSpace.minkowskiNormSq, hηη,
                  hinner_zeta_etaPath t, hinner_etaPath_zeta t, z2]
                ring
          _ = (K / qLine t) ^ 2 * qLine t + (lam t) ^ 2 * z2 := by ring
      have hnormDiff_xi_eta :
          ∀ t : Set.Icc (0 : ℝ) 1,
            MinkowskiSpace.minkowskiNormSq (m + 1) (xiPath t) -
              MinkowskiSpace.minkowskiNormSq (m + 1) (etaPath t) = M := by
        intro t
        have hKterm : (K / qLine t) ^ 2 * qLine t = K ^ 2 / qLine t := by
          field_simp [hqline_ne t]
        have hlam_term : (lam t) ^ 2 * z2 = num t / qLine t := by
          rw [hlam_sq t]
          field_simp [hqline_ne t, hz2ne]
        calc
          MinkowskiSpace.minkowskiNormSq (m + 1) (xiPath t) -
              MinkowskiSpace.minkowskiNormSq (m + 1) (etaPath t)
              = ((K / qLine t) ^ 2 * qLine t + (lam t) ^ 2 * z2) - qLine t := by
                  simp [hnorm_xiPath t, hnorm_etaPath t]
          _ = K ^ 2 / qLine t + num t / qLine t - qLine t := by
                rw [hKterm, hlam_term]
          _ = M := by
                have hKsq : K ^ 2 = (c.re * c.im) ^ 2 := by
                  simp [K, sq]
                rw [hKsq]
                dsimp [num]
                field_simp [hqline_ne t]
                ring
      have huPath_mem :
          ∀ t : Set.Icc (0 : ℝ) 1,
            uPath t ∈ quadricConeSet_im_with_value (m := m) (-(c ^ 2)) := by
        intro t
        refine (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) (uPath t)).2 ?_
        refine ⟨by simpa [uPath] using hcone_etaPath t, ?_, ?_⟩
        · calc
            MinkowskiSpace.minkowskiInner (m + 1)
                (fun μ : Fin (m + 2) => (uPath t μ).re)
                (fun μ : Fin (m + 2) => (uPath t μ).im)
                = MinkowskiSpace.minkowskiInner (m + 1) (xiPath t) (etaPath t) := by
                    simp [uPath]
            _ = K := hinner_xiPath_etaPath t
            _ = (-(c ^ 2)).im / 2 := by simpa using hk_im.symm
        · calc
            MinkowskiSpace.minkowskiNormSq (m + 1)
                (fun μ : Fin (m + 2) => (uPath t μ).re)
              - MinkowskiSpace.minkowskiNormSq (m + 1)
                  (fun μ : Fin (m + 2) => (uPath t μ).im)
                = MinkowskiSpace.minkowskiNormSq (m + 1) (xiPath t) -
                    MinkowskiSpace.minkowskiNormSq (m + 1) (etaPath t) := by
                      simp [uPath]
            _ = M := hnormDiff_xi_eta t
            _ = (-(c ^ 2)).re := by simpa using hk_re.symm
      let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
      let t1 : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
      have hpoly_id := poly_identity_of_mem (m := m) c u hu
      have hnum0 : num t0 = q * z2 := by
        have htmp :
            q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 = z2 * q := by
          simpa [ξ, η, q, K, ζ, z2] using hpoly_id
        simpa [num, qLine, M, r, t0, mul_comm] using htmp
      have hratio0 : num t0 / (qLine t0 * z2) = 1 := by
        have hnum0' : num t0 = qLine t0 * z2 := by simpa [qLine, t0] using hnum0
        rw [hnum0']
        have hq0ne : qLine t0 ≠ 0 := hqline_ne t0
        field_simp [hq0ne]
      have hscale0 : scale t0 = 1 := by
        simp [scale, qLine, t0, hqne]
      have hlam0 : lam t0 = 1 := by
        simp [lam, hratio0]
      have heta0 : etaPath t0 = η := by
        ext μ
        simp [etaPath, hscale0]
      have hxi0 : xiPath t0 = ξ := by
        have hq0 : qLine t0 = q := by simp [qLine, t0]
        calc
          xiPath t0 = (K / qLine t0) • etaPath t0 + lam t0 • ζ := by
                        simp [xiPath]
          _ = (K / q) • η + 1 • ζ := by simp [hlam0, heta0, hq0]
          _ = (K / q) • η + ζ := by simp
          _ = ξ := by
                simp [ζ, sub_eq_add_neg, add_left_comm]
      let η1 : MinkowskiSpace (m + 1) := etaPath t1
      have hnum1 : num t1 = 0 := by
        dsimp [num, qLine]
        simp [t1, M, r]
        ring
      have hlam1 : lam t1 = 0 := by
        simp [lam, hnum1]
      have hcoef1 : K / qLine t1 = c.re / c.im := by
        simp [qLine, t1, K, r]
        field_simp [hcim.ne']
      have hxi1 : xiPath t1 = (c.re / c.im) • η1 := by
        have hq1 : qLine t1 = r := by simp [qLine, t1]
        calc
          xiPath t1 = (K / qLine t1) • etaPath t1 + lam t1 • ζ := by
                        simp [xiPath]
          _ = (K / r) • η1 + 0 • ζ := by
                simp [hq1, η1, hlam1]
          _ = (K / r) • η1 := by simp
          _ = (c.re / c.im) • η1 := by
                have hcoef1' : K / r = c.re / c.im := by simpa [hq1] using hcoef1
                simp [hcoef1']
      have huPath0 : uPath t0 = u := by
        ext μ
        calc
          uPath t0 μ = ((xiPath t0 μ : ℝ) : ℂ) + ((etaPath t0 μ : ℝ) : ℂ) * Complex.I := rfl
          _ = ((ξ μ : ℝ) : ℂ) + ((η μ : ℝ) : ℂ) * Complex.I := by simp [hxi0, heta0]
          _ = ((u μ).re : ℂ) + ((u μ).im : ℂ) * Complex.I := by simp [ξ, η]
          _ = u μ := Complex.re_add_im (u μ)
      have huPath1 : uPath t1 = parallelPoint (m := m) c η1 := by
        ext μ
        simp [uPath, parallelPoint, η1, hxi1, Pi.smul_apply, smul_eq_mul]
      let pA : Path u (parallelPoint (m := m) c η1) :=
        { toFun := uPath
          continuous_toFun := huPath_cont
          source' := huPath0
          target' := huPath1 }
      have hA :
          JoinedIn (quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
            u (parallelPoint (m := m) c η1) := by
        refine ⟨pA, ?_⟩
        intro t
        simpa using huPath_mem t
      have hcone1 : InOpenForwardCone (m + 1) η1 := by
        simpa [η1] using hcone_etaPath t1
      have hnorm1 : MinkowskiSpace.minkowskiNormSq (m + 1) η1 = -c.im ^ 2 := by
        simpa [η1, qLine, t1, r] using hnorm_etaPath t1
      have hB :
          JoinedIn (quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
            (parallelPoint (m := m) c η1)
            (fun μ : Fin (m + 2) => if μ = 0 then c else 0) := by
        change
          JoinedIn (quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
            (fun μ : Fin (m + 2) =>
              (((c.re / c.im) * η1 μ : ℝ) : ℂ) + ((η1 μ : ℂ) * Complex.I))
            (fun μ : Fin (m + 2) => if μ = 0 then c else 0)
        exact joinedIn_parallelSlice_to_canonical (m := m) c hcim η1 hcone1 hnorm1
      exact hB.symm.trans hA.symm

theorem quadricConeSet_wScalarE0_isPreconnected_of_c_im_pos
    (c : ℂ) (hc : c ≠ 0) (hcim : 0 < c.im) :
    IsPreconnected (quadricConeSet_wScalarE0 (m := m) c) := by
  have hpre_im :
      IsPreconnected (quadricConeSet_im_with_value (m := m) (-(c ^ 2))) :=
    quadricConeSet_im_with_value_isPreconnected_of_im_pos (m := m) c hcim
  have hpre_img :
      IsPreconnected ((fun u : Fin (m + 2) → ℂ => fun μ => u μ / c) ''
        quadricConeSet_im_with_value (m := m) (-(c ^ 2))) := by
    have hcont :
        Continuous (fun u : Fin (m + 2) → ℂ => fun μ => u μ / c) := by
      apply continuous_pi
      intro μ
      simpa [div_eq_mul_inv] using
        (continuous_apply μ).mul continuous_const
    exact hpre_im.image _ hcont.continuousOn
  simpa [quadricConeSet_wScalarE0_eq_scale_to_im_with_value (m := m) c hc] using hpre_img


end BHW
