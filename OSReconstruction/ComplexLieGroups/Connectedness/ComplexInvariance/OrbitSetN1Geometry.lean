import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.StabilizerI0
import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetQuotient

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {m : ℕ}

/-- Image of the one-point orbit set under the first-column map. -/
abbrev firstColOrbitImage_wScalarE0_geom (c : ℂ) :
    Set (Fin (m + 2) → ℂ) :=
  (firstColCLG (m := m)) '' orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)

/-- Minkowski quadratic form on column vectors in dimension `m+2`
with signature `(-,+,...,+)`. -/
def minkowskiColQuadric (v : Fin (m + 2) → ℂ) : ℂ :=
  ∑ μ : Fin (m + 2), (minkowskiSignature (m + 1) μ : ℂ) * v μ ^ 2

/-- Full first-column image of `SO⁺(1,m+1;ℂ)`. -/
abbrev firstColImageCLG : Set (Fin (m + 2) → ℂ) :=
  Set.range (firstColCLG (m := m))

/-- Cone cut of the Minkowski unit quadric used by one-point orbit images. -/
abbrev quadricConeSet_wScalarE0 (c : ℂ) : Set (Fin (m + 2) → ℂ) :=
  {v : Fin (m + 2) → ℂ |
    minkowskiColQuadric (m := m) v = (-1 : ℂ) ∧
    InOpenForwardCone (m + 1) (fun μ => (c * v μ).im)}

private lemma minkowskiColQuadric_eq_complexMinkowskiQuadratic
    (v : Fin (m + 2) → ℂ) :
    minkowskiColQuadric (m := m) v =
      MinkowskiSpace.complexMinkowskiQuadratic (m + 1) v := by
  simp [minkowskiColQuadric, MinkowskiSpace.complexMinkowskiQuadratic,
    MinkowskiSpace.metricSignature, minkowskiSignature]

theorem quadricConeSet_wScalarE0_empty_of_c_im_zero
    (c : ℂ) (hc : c ≠ 0) (hcim : c.im = 0) :
    quadricConeSet_wScalarE0 (m := m) c = (∅ : Set (Fin (m + 2) → ℂ)) := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨hvquad, hcone⟩
    have hcre_ne : c.re ≠ 0 := by
      intro hcre
      apply hc
      apply Complex.ext <;> simp [hcre, hcim]
    let ξ : MinkowskiSpace (m + 1) := fun μ => (v μ).re
    let η : MinkowskiSpace (m + 1) := fun μ => (v μ).im
    have hcone_scaled :
        InOpenForwardCone (m + 1) (fun μ => c.re * η μ) := by
      simpa [η, Complex.mul_im, hcim, mul_comm, mul_left_comm, mul_assoc] using hcone
    have hcone_or_neg :
        InOpenForwardCone (m + 1) η ∨ InOpenForwardCone (m + 1) (fun μ => -η μ) := by
      by_cases hcre_pos : 0 < c.re
      · left
        have hpos : 0 < c.re⁻¹ := by
          simpa [one_div] using (inv_pos.mpr hcre_pos)
        have hscaled :=
          inOpenForwardCone_smul_pos (d := m + 1) (η := fun μ => c.re * η μ) hcone_scaled hpos
        have hscale_eq : c.re⁻¹ • (fun μ => c.re * η μ) = η := by
          ext μ
          have hmul : c.re⁻¹ * c.re = (1 : ℝ) := by field_simp [hcre_ne]
          calc
            (c.re⁻¹ • (fun μ => c.re * η μ)) μ = (c.re⁻¹ * c.re) * η μ := by
              simp [Pi.smul_apply, mul_assoc]
            _ = η μ := by simp [hmul]
        simpa [hscale_eq] using hscaled
      · right
        have hcre_neg : c.re < 0 := lt_of_le_of_ne (le_of_not_gt hcre_pos) (by simpa using hcre_ne)
        have hdiv_neg : 1 / c.re < 0 := one_div_neg.mpr hcre_neg
        have hpos : 0 < (-1 / c.re) := by
          have hneg : 0 < -(1 / c.re) := neg_pos.mpr hdiv_neg
          simpa [neg_div] using hneg
        have hscaled :=
          inOpenForwardCone_smul_pos (d := m + 1) (η := fun μ => c.re * η μ) hcone_scaled hpos
        have hscale_eq : (-1 / c.re) • (fun μ => c.re * η μ) = (fun μ => -η μ) := by
          ext μ
          have hmul : (-1 / c.re) * c.re = (-1 : ℝ) := by field_simp [hcre_ne]
          calc
            ((-1 / c.re) • (fun μ => c.re * η μ)) μ = ((-1 / c.re) * c.re) * η μ := by
              simp [Pi.smul_apply, mul_assoc]
            _ = -η μ := by simp [hmul]
        simpa [hscale_eq] using hscaled
    have hq_eval :
        MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ) = (-1 : ℂ) := by
      simpa [minkowskiColQuadric_eq_complexMinkowskiQuadratic (m := m) v] using hvquad
    have him_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).im =
          2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).im =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).im := by
                simp [ξ, η, Complex.re_add_im]
        _ = 2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η :=
              MinkowskiSpace.complexQuadratic_im (d := m + 1) ξ η
    have horth : MinkowskiSpace.minkowskiInner (m + 1) ξ η = 0 := by
      have hIm :
          (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).im = 0 := by
        simp [hq_eval]
      linarith [him_formula, hIm]
    have hre_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).re =
          MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
            MinkowskiSpace.minkowskiNormSq (m + 1) η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).re =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).re := by
                simp [ξ, η, Complex.re_add_im]
        _ = MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
              MinkowskiSpace.minkowskiNormSq (m + 1) η :=
            MinkowskiSpace.complexQuadratic_re (d := m + 1) ξ η
    have hRe :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => v μ)).re = -1 := by
      simp [hq_eval]
    rcases hcone_or_neg with hconeη | hconeNeg
    · have hcone' : η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
        refine ⟨hconeη.1, ?_⟩
        simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
          MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hconeη.2
      have hξ_nonneg : MinkowskiSpace.minkowskiNormSq (m + 1) ξ ≥ 0 :=
        MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
          (d := m + 1) ξ η hcone'.2 hcone'.1 horth
      linarith [hre_formula, hRe, hξ_nonneg, hcone'.2]
    · have hcone' : (fun μ => -η μ) 0 > 0 ∧
        MinkowskiSpace.minkowskiNormSq (m + 1) (fun μ => -η μ) < 0 := by
        refine ⟨hconeNeg.1, ?_⟩
        simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
          MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hconeNeg.2
      have horthNeg :
          MinkowskiSpace.minkowskiInner (m + 1) ξ (fun μ => -η μ) = 0 := by
        simpa [MinkowskiSpace.minkowskiInner] using congrArg Neg.neg horth
      have hξ_nonneg : MinkowskiSpace.minkowskiNormSq (m + 1) ξ ≥ 0 :=
        MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
          (d := m + 1) ξ (fun μ => -η μ) hcone'.2 hcone'.1 horthNeg
      have hnormNeg :
          MinkowskiSpace.minkowskiNormSq (m + 1) (fun μ => -η μ) =
            MinkowskiSpace.minkowskiNormSq (m + 1) η := by
        simp [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
      have hη_neg : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
        simpa [hnormNeg] using hcone'.2
      linarith [hre_formula, hRe, hξ_nonneg, hη_neg]
  · intro hv
    exact hv.elim

theorem quadricConeSet_wScalarE0_isPreconnected_of_c_im_zero
    (c : ℂ) (hc : c ≠ 0) (hcim : c.im = 0) :
    IsPreconnected (quadricConeSet_wScalarE0 (m := m) c) := by
  have hempty := quadricConeSet_wScalarE0_empty_of_c_im_zero (m := m) c hc hcim
  simpa [hempty] using (isPreconnected_empty : IsPreconnected (∅ : Set (Fin (m + 2) → ℂ)))

theorem quadricConeSet_wScalarE0_nonempty_of_c_im_ne_zero
    (c : ℂ) (hcim : c.im ≠ 0) :
    (quadricConeSet_wScalarE0 (m := m) c).Nonempty := by
  by_cases hpos : 0 < c.im
  · refine ⟨fun μ => if μ = 0 then (1 : ℂ) else 0, ?_⟩
    refine ⟨?_, ?_⟩
    · simp [minkowskiColQuadric, minkowskiSignature]
    · constructor
      · simpa [Complex.mul_im] using hpos
      · rw [Fin.sum_univ_succ]
        simp [minkowskiSignature]
        nlinarith
  · have hneg : c.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hcim
    refine ⟨fun μ => if μ = 0 then (-1 : ℂ) else 0, ?_⟩
    refine ⟨?_, ?_⟩
    · simp [minkowskiColQuadric, minkowskiSignature]
    · constructor
      · have hnegIm : 0 < -c.im := neg_pos.mpr hneg
        simpa [Complex.mul_im] using hnegIm
      · rw [Fin.sum_univ_succ]
        simp [minkowskiSignature]
        nlinarith

theorem quadricConeSet_wScalarE0_isPreconnected_of_im_ne_zero_reduction
    (hmain :
      ∀ c : ℂ, c ≠ 0 → c.im ≠ 0 →
        IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    ∀ c : ℂ, c ≠ 0 → IsPreconnected (quadricConeSet_wScalarE0 (m := m) c) := by
  intro c hc
  by_cases hcim : c.im = 0
  · exact quadricConeSet_wScalarE0_isPreconnected_of_c_im_zero (m := m) c hc hcim
  · exact hmain c hc hcim

theorem quadricConeSet_wScalarE0_eq_neg_image
    (c : ℂ) :
    quadricConeSet_wScalarE0 (m := m) c =
      (fun v : Fin (m + 2) → ℂ => fun μ => -v μ) ''
        quadricConeSet_wScalarE0 (m := m) (-c) := by
  ext v
  constructor
  · intro hv
    refine ⟨fun μ => -v μ, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [minkowskiColQuadric, mul_assoc] using hv.1
      · simpa [Complex.mul_im, mul_assoc] using hv.2
    · ext μ
      simp
  · rintro ⟨u, hu, hv⟩
    refine ⟨?_, ?_⟩
    · have huq : minkowskiColQuadric (m := m) u = (-1 : ℂ) := hu.1
      calc
        minkowskiColQuadric (m := m) v = minkowskiColQuadric (m := m) (fun μ => -u μ) := by
          simp [hv]
        _ = minkowskiColQuadric (m := m) u := by
          unfold minkowskiColQuadric
          refine Finset.sum_congr rfl ?_
          intro μ _
          ring_nf
        _ = (-1 : ℂ) := huq
    · have hcone : InOpenForwardCone (m + 1) (fun μ => ((-c) * u μ).im) := hu.2
      have hcone_eq :
          (fun μ => c.re * (v μ).im + c.im * (v μ).re) =
          (fun μ => -(c.im * (u μ).re) + -(c.re * (u μ).im)) := by
        ext μ
        have hvμ : v μ = -u μ := by
          have hvμ' : -u μ = v μ := by
            simpa using congrArg (fun f => f μ) hv
          simpa [eq_comm] using hvμ'
        rw [hvμ]
        simp [Complex.neg_re, Complex.neg_im]
        ring
      simpa [Complex.mul_im, hcone_eq] using hcone

theorem quadricConeSet_wScalarE0_isPreconnected_of_im_pos_reduction
    (hmain :
      ∀ c : ℂ, c ≠ 0 → 0 < c.im →
        IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    ∀ c : ℂ, c ≠ 0 → c.im ≠ 0 →
      IsPreconnected (quadricConeSet_wScalarE0 (m := m) c) := by
  intro c hc hcim
  by_cases hpos : 0 < c.im
  · exact hmain c hc hpos
  · have hneg : 0 < (-c).im := by
      have hlt : c.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hcim
      simpa using neg_pos.mpr hlt
    have hpre_neg : IsPreconnected (quadricConeSet_wScalarE0 (m := m) (-c)) :=
      hmain (-c) (neg_ne_zero.mpr hc) hneg
    have hpre_img : IsPreconnected ((fun v : Fin (m + 2) → ℂ => fun μ => -v μ) ''
      quadricConeSet_wScalarE0 (m := m) (-c)) :=
      hpre_neg.image _ (continuous_neg.continuousOn)
    simpa [quadricConeSet_wScalarE0_eq_neg_image (m := m) c] using hpre_img

lemma firstColImageCLG_minkowski_eq_neg_one :
    firstColImageCLG (m := m) ⊆
      {v : Fin (m + 2) → ℂ | minkowskiColQuadric (m := m) v = (-1 : ℂ)} := by
  intro v hv
  rcases hv with ⟨Λ, rfl⟩
  have h00 := Λ.metric_preserving 0 0
  simpa [minkowskiColQuadric, firstColCLG, minkowskiSignature, one_mul, pow_two, mul_assoc]
    using h00

lemma firstColImageCLG_surj_of_minkowski_eq_neg_one
    (v : Fin (m + 2) → ℂ)
    (hv : minkowskiColQuadric (m := m) v = (-1 : ℂ)) :
    v ∈ firstColImageCLG (m := m) := by
  let u : Fin (m + 2) → ℂ :=
    fun k => Fin.cases (v 0) (fun i => v i.succ * Complex.I) k
  have hu_unit : ∑ k : Fin (m + 2), u k ^ 2 = (1 : ℂ) := by
    calc
      ∑ k : Fin (m + 2), u k ^ 2
          = (v 0) ^ 2 + ∑ i : Fin (m + 1), (v i.succ * Complex.I) ^ 2 := by
              rw [Fin.sum_univ_succ]
              simp [u]
      _ = (v 0) ^ 2 + ∑ i : Fin (m + 1), (-(v i.succ ^ 2)) := by
            refine congrArg (fun t => (v 0) ^ 2 + t) ?_
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (v i.succ * Complex.I) ^ 2 = v i.succ ^ 2 * Complex.I ^ 2 := by ring
              _ = v i.succ ^ 2 * (-1) := by simp [Complex.I_sq]
              _ = -(v i.succ ^ 2) := by ring
      _ = (v 0) ^ 2 - ∑ i : Fin (m + 1), (v i.succ) ^ 2 := by
            simp [sub_eq_add_neg]
      _ = 1 := by
            have hv_decomp :
                (∑ μ : Fin (m + 2),
                  (minkowskiSignature (m + 1) μ : ℂ) * v μ ^ 2)
                  = -(v 0) ^ 2 + ∑ i : Fin (m + 1), v i.succ ^ 2 := by
              rw [Fin.sum_univ_succ]
              simp [minkowskiSignature]
            have hv' : -(v 0) ^ 2 + ∑ i : Fin (m + 1), v i.succ ^ 2 = (-1 : ℂ) := by
              exact hv_decomp ▸ hv
            calc
              (v 0) ^ 2 - ∑ i : Fin (m + 1), v i.succ ^ 2
                  = - (-(v 0) ^ 2 + ∑ i : Fin (m + 1), v i.succ ^ 2) := by ring
              _ = -(-1 : ℂ) := by rw [hv']
              _ = 1 := by norm_num
  rcases SOComplex.exists_so_with_firstCol (m := m) u hu_unit with ⟨A, hAcol⟩
  let Λ : ComplexLorentzGroup (m + 1) := ComplexLorentzGroup.fromSOComplex (d := m + 1) A
  have hto :
      ComplexLorentzGroup.toSOComplex (d := m + 1) Λ = A := by
    simpa [Λ] using (ComplexLorentzGroup.toSOComplex_fromSOComplex (d := m + 1) A)
  have hΛcol : firstColCLG (m := m) Λ = v := by
    ext k
    refine Fin.cases ?_ ?_ k
    · calc
        firstColCLG (m := m) Λ 0 = Λ.val 0 0 := rfl
        _ = (ComplexLorentzGroup.toSOComplex (d := m + 1) Λ).val 0 0 := by
              simpa using (ComplexLorentzGroup.toSOComplex_entry_00 (d := m + 1) Λ).symm
        _ = A.val 0 0 := by simp [hto]
        _ = u 0 := hAcol 0
        _ = v 0 := by simp [u]
    · intro i
      have hmul :
          Λ.val i.succ 0 * Complex.I =
            (ComplexLorentzGroup.toSOComplex (d := m + 1) Λ).val i.succ 0 := by
        simpa using (ComplexLorentzGroup.toSOComplex_entry_succ0 (d := m + 1) Λ i).symm
      have hA : (ComplexLorentzGroup.toSOComplex (d := m + 1) Λ).val i.succ 0 = u i.succ := by
        simpa [hto] using hAcol i.succ
      have hmul' : Λ.val i.succ 0 * Complex.I = v i.succ * Complex.I := by
        simpa [u] using hmul.trans hA
      have hcancel := congrArg (fun z : ℂ => z * (-Complex.I)) hmul'
      have htmp : Λ.val i.succ 0 = v i.succ := by
        simpa [mul_assoc] using hcancel
      simpa [firstColCLG] using htmp
  exact ⟨Λ, hΛcol⟩

theorem firstColImageCLG_eq_minkowskiQuadric :
    firstColImageCLG (m := m) =
      {v : Fin (m + 2) → ℂ | minkowskiColQuadric (m := m) v = (-1 : ℂ)} := by
  ext v
  constructor
  · intro hv
    exact firstColImageCLG_minkowski_eq_neg_one (m := m) hv
  · intro hv
    exact firstColImageCLG_surj_of_minkowski_eq_neg_one (m := m) v hv

/-- One-point quadric slice in configuration space at Minkowski value `-c²`. -/
abbrev onePointQuadricSet_wScalarE0 (c : ℂ) : Set (Fin 1 → Fin (m + 2) → ℂ) :=
  {z | minkowskiColQuadric (m := m) (fun μ => z 0 μ) = -(c ^ 2)}

lemma minkowskiColQuadric_smul (c : ℂ) (v : Fin (m + 2) → ℂ) :
    minkowskiColQuadric (m := m) (fun μ => c * v μ) =
      c ^ 2 * minkowskiColQuadric (m := m) v := by
  unfold minkowskiColQuadric
  calc
    ∑ μ : Fin (m + 2), (minkowskiSignature (m + 1) μ : ℂ) * (c * v μ) ^ 2
        = ∑ μ : Fin (m + 2),
            c ^ 2 * ((minkowskiSignature (m + 1) μ : ℂ) * v μ ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro μ _
              ring
    _ = c ^ 2 * ∑ μ : Fin (m + 2), ((minkowskiSignature (m + 1) μ : ℂ) * v μ ^ 2) := by
          rw [Finset.mul_sum]
    _ = c ^ 2 * minkowskiColQuadric (m := m) v := by rfl

/-- Cone-cut normalization: scaling by `c` turns the condition
`Im(c * v) ∈ V₊` into a plain-imaginary condition at Minkowski value `-(c^2)`. -/
theorem quadricConeSet_wScalarE0_eq_scale_to_im_with_value
    (c : ℂ) (hc : c ≠ 0) :
    quadricConeSet_wScalarE0 (m := m) c =
      (fun u : Fin (m + 2) → ℂ => fun μ => u μ / c) ''
        {u : Fin (m + 2) → ℂ |
          minkowskiColQuadric (m := m) u = -(c ^ 2) ∧
            InOpenForwardCone (m + 1) (fun μ => (u μ).im)} := by
  ext v
  constructor
  · intro hv
    refine ⟨fun μ => c * v μ, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · calc
          minkowskiColQuadric (m := m) (fun μ => c * v μ)
              = c ^ 2 * minkowskiColQuadric (m := m) v := by
                  simpa using minkowskiColQuadric_smul (m := m) c v
          _ = c ^ 2 * (-1 : ℂ) := by simp [hv.1]
          _ = -(c ^ 2) := by ring
      · simpa [Complex.mul_im, mul_assoc] using hv.2
    · ext μ
      field_simp [hc]
  · rintro ⟨u, hu, hv⟩
    refine ⟨?_, ?_⟩
    · have huq : minkowskiColQuadric (m := m) u = -(c ^ 2) := hu.1
      calc
        minkowskiColQuadric (m := m) v
            = minkowskiColQuadric (m := m) (fun μ => u μ / c) := by simp [hv]
        _ = (1 / c ^ 2) * minkowskiColQuadric (m := m) u := by
              have hdiv : (fun μ => u μ / c) = (fun μ => c⁻¹ * u μ) := by
                ext μ
                simp [div_eq_mul_inv, mul_comm]
              simpa [one_div, hdiv] using minkowskiColQuadric_smul (m := m) (c⁻¹) u
        _ = (1 / c ^ 2) * (-(c ^ 2)) := by rw [huq]
        _ = (-1 : ℂ) := by
              field_simp [pow_ne_zero 2 hc]
    · have hcone : InOpenForwardCone (m + 1) (fun μ => (u μ).im) := hu.2
      have hu_eq : (fun μ => u μ) = (fun μ => c * v μ) := by
        funext μ
        have hvμ : u μ / c = v μ := by
          simpa using congrArg (fun f => f μ) hv
        calc
          u μ = c * (u μ / c) := by field_simp [hc]
          _ = c * v μ := by rw [hvμ]
      simpa [hu_eq, Complex.mul_im, mul_assoc] using hcone

/-- Normalized cone-cut set at Minkowski value `k` with plain-imaginary cone condition. -/
abbrev quadricConeSet_im_with_value (k : ℂ) : Set (Fin (m + 2) → ℂ) :=
  {u : Fin (m + 2) → ℂ |
    minkowskiColQuadric (m := m) u = k ∧
      InOpenForwardCone (m + 1) (fun μ => (u μ).im)}

/-- Real/imaginary decomposition of membership in `quadricConeSet_im_with_value k`. -/
theorem mem_quadricConeSet_im_with_value_iff
    (k : ℂ) (u : Fin (m + 2) → ℂ) :
    u ∈ quadricConeSet_im_with_value (m := m) k ↔
      let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
      let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
      InOpenForwardCone (m + 1) η ∧
      MinkowskiSpace.minkowskiInner (m + 1) ξ η = k.im / 2 ∧
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
        MinkowskiSpace.minkowskiNormSq (m + 1) η = k.re := by
  constructor
  · intro hu
    rcases hu with ⟨huq, hcone⟩
    let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
    let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
    have hq_eval :
        MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ) = k := by
      simp [minkowskiColQuadric_eq_complexMinkowskiQuadratic (m := m) u] at huq ⊢
      exact huq
    have him_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).im =
          2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).im =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).im := by
                simp [ξ, η, Complex.re_add_im]
        _ = 2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η :=
              MinkowskiSpace.complexQuadratic_im (d := m + 1) ξ η
    have hre_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).re =
          MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
            MinkowskiSpace.minkowskiNormSq (m + 1) η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).re =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).re := by
                simp [ξ, η, Complex.re_add_im]
        _ = MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
              MinkowskiSpace.minkowskiNormSq (m + 1) η :=
            MinkowskiSpace.complexQuadratic_re (d := m + 1) ξ η
    refine ⟨hcone, ?_, ?_⟩
    · have him_eq :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).im = k.im := by
        simp [hq_eval]
      linarith [him_formula, him_eq]
    · have hre_eq :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).re = k.re := by
        simp [hq_eval]
      linarith [hre_formula, hre_eq]
  · intro hu
    let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
    let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
    rcases hu with ⟨hcone, hinner, hnorm⟩
    have him_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).im =
          2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).im =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).im := by
                simp [ξ, η, Complex.re_add_im]
        _ = 2 * MinkowskiSpace.minkowskiInner (m + 1) ξ η :=
              MinkowskiSpace.complexQuadratic_im (d := m + 1) ξ η
    have hre_formula :
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).re =
          MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
            MinkowskiSpace.minkowskiNormSq (m + 1) η := by
      calc
        (MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ)).re =
            (MinkowskiSpace.complexMinkowskiQuadratic (m + 1)
              (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).re := by
                simp [ξ, η, Complex.re_add_im]
        _ = MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
              MinkowskiSpace.minkowskiNormSq (m + 1) η :=
            MinkowskiSpace.complexQuadratic_re (d := m + 1) ξ η
    have hq_eval :
        MinkowskiSpace.complexMinkowskiQuadratic (m + 1) (fun μ => u μ) = k := by
      apply Complex.ext
      · linarith [hre_formula, hnorm]
      · linarith [him_formula, hinner]
    refine ⟨?_, hcone⟩
    simp [minkowskiColQuadric_eq_complexMinkowskiQuadratic (m := m) u] at hq_eval ⊢
    exact hq_eval

lemma minkowskiNormSq_decompose_along_timelike
    (ξ η : MinkowskiSpace (m + 1))
    (hηcone : InOpenForwardCone (m + 1) η) :
    let a : ℝ := (MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
      (MinkowskiSpace.minkowskiNormSq (m + 1) η)
    let ζ : MinkowskiSpace (m + 1) := ξ - a • η
    MinkowskiSpace.minkowskiInner (m + 1) ζ η = 0 ∧
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ =
        a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η +
          MinkowskiSpace.minkowskiNormSq (m + 1) ζ := by
  let a : ℝ := (MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
    (MinkowskiSpace.minkowskiNormSq (m + 1) η)
  let ζ : MinkowskiSpace (m + 1) := ξ - a • η
  have hηneg : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
    simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hηcone.2
  have hηne : MinkowskiSpace.minkowskiNormSq (m + 1) η ≠ 0 := ne_of_lt hηneg
  refine ⟨?_, ?_⟩
  · change MinkowskiSpace.minkowskiInner (m + 1) (ξ - a • η) η = 0
    calc
      MinkowskiSpace.minkowskiInner (m + 1) (ξ - a • η) η
          = MinkowskiSpace.minkowskiInner (m + 1) ξ η -
              a * MinkowskiSpace.minkowskiInner (m + 1) η η := by
            calc
              MinkowskiSpace.minkowskiInner (m + 1) (ξ - a • η) η
                  = MinkowskiSpace.minkowskiInner (m + 1) (ξ + -(a • η)) η := by
                      simp [sub_eq_add_neg]
              _ = MinkowskiSpace.minkowskiInner (m + 1) ξ η +
                    MinkowskiSpace.minkowskiInner (m + 1) (-(a • η)) η := by
                    rw [MinkowskiSpace.minkowskiInner_add_left]
              _ = MinkowskiSpace.minkowskiInner (m + 1) ξ η -
                    MinkowskiSpace.minkowskiInner (m + 1) (a • η) η := by
                    rw [MinkowskiSpace.minkowskiInner_neg_left]
                    ring_nf
              _ = MinkowskiSpace.minkowskiInner (m + 1) ξ η -
                    a * MinkowskiSpace.minkowskiInner (m + 1) η η := by
                    rw [MinkowskiSpace.minkowskiInner_smul_left]
      _ = MinkowskiSpace.minkowskiInner (m + 1) ξ η -
            a * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
            simp [MinkowskiSpace.minkowskiNormSq]
      _ = 0 := by
            have hmul0 :
                (MinkowskiSpace.minkowskiInner (m + 1) ξ η /
                  MinkowskiSpace.minkowskiNormSq (m + 1) η) *
                  MinkowskiSpace.minkowskiNormSq (m + 1) η =
                MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
              field_simp [hηne]
            have hmul : a * MinkowskiSpace.minkowskiNormSq (m + 1) η =
                MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
              simpa [a] using hmul0
            linarith [hmul]
  · change MinkowskiSpace.minkowskiNormSq (m + 1) ξ =
      a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η +
        MinkowskiSpace.minkowskiNormSq (m + 1) (ξ - a • η)
    have hnorm_expand :
        MinkowskiSpace.minkowskiNormSq (m + 1) (ξ - a • η) =
          MinkowskiSpace.minkowskiNormSq (m + 1) ξ
            - 2 * a * MinkowskiSpace.minkowskiInner (m + 1) ξ η
            + a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
      unfold MinkowskiSpace.minkowskiNormSq
      calc
        MinkowskiSpace.minkowskiInner (m + 1) (ξ - a • η) (ξ - a • η)
            = MinkowskiSpace.minkowskiInner (m + 1) (ξ + -(a • η)) (ξ + -(a • η)) := by
                simp [sub_eq_add_neg]
        _ = MinkowskiSpace.minkowskiInner (m + 1) ξ (ξ + -(a • η)) +
              MinkowskiSpace.minkowskiInner (m + 1) (-(a • η)) (ξ + -(a • η)) := by
              rw [MinkowskiSpace.minkowskiInner_add_left]
        _ = (MinkowskiSpace.minkowskiInner (m + 1) ξ ξ +
              MinkowskiSpace.minkowskiInner (m + 1) ξ (-(a • η))) +
            (MinkowskiSpace.minkowskiInner (m + 1) (-(a • η)) ξ +
              MinkowskiSpace.minkowskiInner (m + 1) (-(a • η)) (-(a • η))) := by
              rw [MinkowskiSpace.minkowskiInner_add_right, MinkowskiSpace.minkowskiInner_add_right]
        _ = MinkowskiSpace.minkowskiInner (m + 1) ξ ξ -
              a * MinkowskiSpace.minkowskiInner (m + 1) ξ η -
              a * MinkowskiSpace.minkowskiInner (m + 1) ξ η +
              a ^ 2 * MinkowskiSpace.minkowskiInner (m + 1) η η := by
              rw [MinkowskiSpace.minkowskiInner_neg_right, MinkowskiSpace.minkowskiInner_smul_right,
                MinkowskiSpace.minkowskiInner_neg_left, MinkowskiSpace.minkowskiInner_smul_left,
                MinkowskiSpace.minkowskiInner_neg_left, MinkowskiSpace.minkowskiInner_neg_right,
                MinkowskiSpace.minkowskiInner_smul_left, MinkowskiSpace.minkowskiInner_smul_right,
                MinkowskiSpace.minkowskiInner_comm (m + 1) η ξ]
              ring_nf
        _ = MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
              2 * a * MinkowskiSpace.minkowskiInner (m + 1) ξ η +
              a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
              simp [MinkowskiSpace.minkowskiNormSq]
              ring
    have htarget :
        MinkowskiSpace.minkowskiNormSq (m + 1) ξ =
          a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η +
            MinkowskiSpace.minkowskiNormSq (m + 1) (ξ - a • η) := by
      have hmul0 :
          (MinkowskiSpace.minkowskiInner (m + 1) ξ η /
            MinkowskiSpace.minkowskiNormSq (m + 1) η) *
            MinkowskiSpace.minkowskiNormSq (m + 1) η =
          MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
        field_simp [hηne]
      have hmul1 : a * MinkowskiSpace.minkowskiNormSq (m + 1) η =
          MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
        simpa [a] using hmul0
      have hmul : a * MinkowskiSpace.minkowskiInner (m + 1) ξ η =
          a ^ 2 * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
        rw [← hmul1]
        ring
      nlinarith [hnorm_expand, hmul]
    simpa [add_comm, add_left_comm, add_assoc] using htarget

lemma minkowskiNormSq_eta_lower_bound
    (c : ℂ)
    (u : Fin (m + 2) → ℂ)
    (hu : u ∈ quadricConeSet_im_with_value (m := m) (-(c ^ 2))) :
    -c.im ^ 2 ≤
      MinkowskiSpace.minkowskiNormSq (m + 1) (fun μ => (u μ).im) := by
  rcases (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) u).1 hu with
    ⟨hcone, hinner, hnorm⟩
  let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
  let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
  have hdecomp := minkowskiNormSq_decompose_along_timelike (m := m) ξ η hcone
  rcases hdecomp with ⟨horth, hnorm_decomp⟩
  have hηneg : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
    simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
  have hζ_nonneg :
      0 ≤ MinkowskiSpace.minkowskiNormSq (m + 1)
        (ξ -
          ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
            (MinkowskiSpace.minkowskiNormSq (m + 1) η)) • η) :=
    MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
      (d := m + 1)
      (ξ :=
        ξ -
          ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
            (MinkowskiSpace.minkowskiNormSq (m + 1) η)) • η)
      (η := η)
      hηneg hcone.1 (by simpa using horth)
  have hineq_core :
      (MinkowskiSpace.minkowskiNormSq (m + 1) ξ) *
          (MinkowskiSpace.minkowskiNormSq (m + 1) η) ≤
        (MinkowskiSpace.minkowskiInner (m + 1) ξ η) ^ 2 := by
    have hηne : MinkowskiSpace.minkowskiNormSq (m + 1) η ≠ 0 := ne_of_lt hηneg
    have hmain :
        MinkowskiSpace.minkowskiNormSq (m + 1) ξ =
          ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
            (MinkowskiSpace.minkowskiNormSq (m + 1) η)) ^ 2 *
            MinkowskiSpace.minkowskiNormSq (m + 1) η
          +
            MinkowskiSpace.minkowskiNormSq (m + 1)
              (ξ -
                ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
                  (MinkowskiSpace.minkowskiNormSq (m + 1) η)) • η) := by
      simpa [ξ, η] using hnorm_decomp
    have hmain' :
        (MinkowskiSpace.minkowskiNormSq (m + 1) ξ) *
          (MinkowskiSpace.minkowskiNormSq (m + 1) η)
        ≤
        ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
          (MinkowskiSpace.minkowskiNormSq (m + 1) η)) ^ 2 *
          (MinkowskiSpace.minkowskiNormSq (m + 1) η) ^ 2 := by
      have hmul :
          MinkowskiSpace.minkowskiNormSq (m + 1)
              (ξ -
                ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
                  (MinkowskiSpace.minkowskiNormSq (m + 1) η)) • η)
            * MinkowskiSpace.minkowskiNormSq (m + 1) η
          ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hζ_nonneg (le_of_lt hηneg)
      nlinarith [hmain, hmul]
    have hsq :
        ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
          (MinkowskiSpace.minkowskiNormSq (m + 1) η)) ^ 2 *
          (MinkowskiSpace.minkowskiNormSq (m + 1) η) ^ 2 =
          (MinkowskiSpace.minkowskiInner (m + 1) ξ η) ^ 2 := by
      field_simp [hηne]
    calc
      (MinkowskiSpace.minkowskiNormSq (m + 1) ξ) *
          (MinkowskiSpace.minkowskiNormSq (m + 1) η)
          ≤
          ((MinkowskiSpace.minkowskiInner (m + 1) ξ η) /
            (MinkowskiSpace.minkowskiNormSq (m + 1) η)) ^ 2 *
            (MinkowskiSpace.minkowskiNormSq (m + 1) η) ^ 2 := hmain'
      _ = (MinkowskiSpace.minkowskiInner (m + 1) ξ η) ^ 2 := hsq
  have hinner_eval :
      MinkowskiSpace.minkowskiInner (m + 1) ξ η = -(c.re * c.im) := by
    have : (-(c ^ 2)).im / 2 = -(c.re * c.im) := by
      simp [pow_two, Complex.mul_im]
      ring
    linarith [hinner, this]
  have hnorm_eval :
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
        MinkowskiSpace.minkowskiNormSq (m + 1) η = c.im ^ 2 - c.re ^ 2 := by
    have : (-(c ^ 2)).re = c.im ^ 2 - c.re ^ 2 := by
      simp [pow_two, Complex.mul_re]
    linarith [hnorm, this]
  set q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
  set p : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) ξ
  have hp : p = q + (c.im ^ 2 - c.re ^ 2) := by
    have hnorm_eval' : p - q = c.im ^ 2 - c.re ^ 2 := by
      simpa [p, q] using hnorm_eval
    linarith [hnorm_eval']
  have hineq_num : p * q ≤ (c.re * c.im) ^ 2 := by
    have hinner_sq :
        (MinkowskiSpace.minkowskiInner (m + 1) ξ η) ^ 2 = (c.re * c.im) ^ 2 := by
      rw [hinner_eval]
      ring
    simpa [p, q] using hineq_core.trans_eq hinner_sq
  have hpoly :
      q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 ≤ 0 := by
    nlinarith [hineq_num, hp]
  have hfactor :
      (q + c.im ^ 2) * (q - c.re ^ 2) ≤ 0 := by
    have hring :
        (q + c.im ^ 2) * (q - c.re ^ 2) =
        q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 := by ring
    linarith [hpoly, hring]
  have hneg_factor : q - c.re ^ 2 < 0 := by
    have hqneg : q < 0 := by simpa [q] using hηneg
    linarith [hqneg, sq_nonneg c.re]
  have hbound : 0 ≤ q + c.im ^ 2 := by
    by_contra hlt
    have hlt' : q + c.im ^ 2 < 0 := lt_of_not_ge hlt
    have hpos_prod : 0 < (q + c.im ^ 2) * (q - c.re ^ 2) := by
      exact mul_pos_of_neg_of_neg hlt' hneg_factor
    exact (not_lt_of_ge hfactor) hpos_prod
  have hbound' : -c.im ^ 2 ≤ q := by linarith [hbound]
  simpa [q] using hbound'

lemma minkowskiNormSq_eta_interval
    (c : ℂ)
    (u : Fin (m + 2) → ℂ)
    (hu : u ∈ quadricConeSet_im_with_value (m := m) (-(c ^ 2))) :
    (let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im;
     -c.im ^ 2 ≤ MinkowskiSpace.minkowskiNormSq (m + 1) η ∧
       MinkowskiSpace.minkowskiNormSq (m + 1) η < 0) := by
  let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
  have hlow : -c.im ^ 2 ≤ MinkowskiSpace.minkowskiNormSq (m + 1) η :=
    minkowskiNormSq_eta_lower_bound (m := m) c u hu
  rcases (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) u).1 hu with
    ⟨hcone, _, _⟩
  have hneg : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
    simpa [η, InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
  exact ⟨hlow, hneg⟩

lemma canonical_mem_quadricConeSet_im_with_value
    (c : ℂ) (hcim : 0 < c.im) :
    (fun μ : Fin (m + 2) => if μ = 0 then c else 0) ∈
      quadricConeSet_im_with_value (m := m) (-(c ^ 2)) := by
  refine ⟨?_, ?_⟩
  · simp [minkowskiColQuadric, minkowskiSignature]
  · constructor
    · simpa using hcim
    · rw [Fin.sum_univ_succ]
      simp [minkowskiSignature]
      nlinarith [hcim]

lemma parallel_mem_quadricConeSet_im_with_value
    (c : ℂ) (hcim : 0 < c.im)
    (η : MinkowskiSpace (m + 1))
    (hcone : InOpenForwardCone (m + 1) η)
    (hηnorm : MinkowskiSpace.minkowskiNormSq (m + 1) η = -c.im ^ 2) :
    (fun μ : Fin (m + 2) =>
      (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I)) ∈
      quadricConeSet_im_with_value (m := m) (-(c ^ 2)) := by
  have hηnorm_ne : MinkowskiSpace.minkowskiNormSq (m + 1) η ≠ 0 := by
    rw [hηnorm]
    nlinarith [hcim]
  let ξ : MinkowskiSpace (m + 1) := (c.re / c.im) • η
  have hinner : MinkowskiSpace.minkowskiInner (m + 1) ξ η = -(c.re * c.im) := by
    calc
      MinkowskiSpace.minkowskiInner (m + 1) ξ η
          = (c.re / c.im) * MinkowskiSpace.minkowskiInner (m + 1) η η := by
              simp [ξ, MinkowskiSpace.minkowskiInner_smul_left]
      _ = (c.re / c.im) * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
            simp [MinkowskiSpace.minkowskiNormSq]
      _ = (c.re / c.im) * (-c.im ^ 2) := by rw [hηnorm]
      _ = -(c.re * c.im) := by
            field_simp [hcim.ne']
  have hnorm : MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
      MinkowskiSpace.minkowskiNormSq (m + 1) η = c.im ^ 2 - c.re ^ 2 := by
    calc
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
          MinkowskiSpace.minkowskiNormSq (m + 1) η
          = ((c.re / c.im) ^ 2 - 1) * MinkowskiSpace.minkowskiNormSq (m + 1) η := by
              unfold MinkowskiSpace.minkowskiNormSq
              simp [ξ, MinkowskiSpace.minkowskiInner_smul_left,
                MinkowskiSpace.minkowskiInner_smul_right]
              ring
      _ = ((c.re / c.im) ^ 2 - 1) * (-c.im ^ 2) := by rw [hηnorm]
      _ = c.im ^ 2 - c.re ^ 2 := by
            field_simp [hcim.ne']
            ring
  refine (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2))
    (fun μ : Fin (m + 2) =>
      (((c.re / c.im) * η μ : ℝ) : ℂ) + ((η μ : ℂ) * Complex.I))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · simpa using hcone
  · have hk_im : (-(c ^ 2)).im / 2 = -(c.re * c.im) := by
      simp [pow_two, Complex.mul_im]
      ring
    calc
      MinkowskiSpace.minkowskiInner (m + 1)
          (fun μ : Fin (m + 2) =>
            (((((c.re / c.im) * η μ : ℝ) : ℂ) + (↑(η μ) * I)).re))
          (fun μ : Fin (m + 2) =>
            (((((c.re / c.im) * η μ : ℝ) : ℂ) + (↑(η μ) * I)).im))
          = MinkowskiSpace.minkowskiInner (m + 1) ξ η := by
              simp [MinkowskiSpace.minkowskiInner, ξ, Pi.smul_apply, smul_eq_mul]
      _ = -(c.re * c.im) := hinner
      _ = (-(c ^ 2)).im / 2 := by simpa using hk_im.symm
  · have hk_re : (-(c ^ 2)).re = c.im ^ 2 - c.re ^ 2 := by
      simp [pow_two, Complex.mul_re]
    calc
      MinkowskiSpace.minkowskiNormSq (m + 1)
          (fun μ : Fin (m + 2) =>
            (((((c.re / c.im) * η μ : ℝ) : ℂ) + (↑(η μ) * I)).re))
          - MinkowskiSpace.minkowskiNormSq (m + 1)
              (fun μ : Fin (m + 2) =>
                (((((c.re / c.im) * η μ : ℝ) : ℂ) + (↑(η μ) * I)).im))
          = MinkowskiSpace.minkowskiNormSq (m + 1) ξ - MinkowskiSpace.minkowskiNormSq (m + 1) η := by
              simp [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
                ξ, Pi.smul_apply, smul_eq_mul]
      _ = c.im ^ 2 - c.re ^ 2 := hnorm
      _ = (-(c ^ 2)).re := by simpa using hk_re.symm

lemma poly_identity_of_mem
    (c : ℂ)
    (u : Fin (m + 2) → ℂ)
    (hu : u ∈ quadricConeSet_im_with_value (m := m) (-(c ^ 2))) :
    let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
    let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
    let q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
    let K : ℝ := -(c.re * c.im)
    let ζ : MinkowskiSpace (m + 1) := ξ - (K / q) • η
    q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 =
      MinkowskiSpace.minkowskiNormSq (m + 1) ζ * q := by
  rcases (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) u).1 hu with
    ⟨hcone, hinner, hnorm⟩
  let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
  let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
  let q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
  let K : ℝ := -(c.re * c.im)
  let ζ : MinkowskiSpace (m + 1) := ξ - (K / q) • η
  have hηneg : q < 0 := by
    have : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
      simpa [η, InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
        MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
    simpa [q] using this
  have hqne : q ≠ 0 := ne_of_lt hηneg
  have hinner_eval : MinkowskiSpace.minkowskiInner (m + 1) ξ η = K := by
    have hk_im : (-(c ^ 2)).im / 2 = K := by
      simp [K, pow_two, Complex.mul_im]
      ring
    linarith [hinner, hk_im]
  have hnorm_eval :
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ -
        MinkowskiSpace.minkowskiNormSq (m + 1) η = c.im ^ 2 - c.re ^ 2 := by
    have hk_re : (-(c ^ 2)).re = c.im ^ 2 - c.re ^ 2 := by
      simp [pow_two, Complex.mul_re]
    linarith [hnorm, hk_re]
  have hdecomp := minkowskiNormSq_decompose_along_timelike (m := m) ξ η hcone
  rcases hdecomp with ⟨horth, hnorm_decomp⟩
  have hKq : K / q = (MinkowskiSpace.minkowskiInner (m + 1) ξ η) / q := by
    rw [hinner_eval]
  have hnorm_decomp' :
      MinkowskiSpace.minkowskiNormSq (m + 1) ξ =
        (K / q) ^ 2 * q + MinkowskiSpace.minkowskiNormSq (m + 1) ζ := by
    simpa [ζ, q, hKq] using hnorm_decomp
  have hpoly_aux :
      q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - K ^ 2 =
        MinkowskiSpace.minkowskiNormSq (m + 1) ζ * q := by
    have hKsq : (K / q) ^ 2 * q = K ^ 2 / q := by
      field_simp [hqne]
    have hξeq :
        MinkowskiSpace.minkowskiNormSq (m + 1) ξ = K ^ 2 / q + MinkowskiSpace.minkowskiNormSq (m + 1) ζ := by
      simpa [hKsq] using hnorm_decomp'
    have hξeq2 :
        K ^ 2 / q + MinkowskiSpace.minkowskiNormSq (m + 1) ζ - q = c.im ^ 2 - c.re ^ 2 := by
      linarith [hnorm_eval, hξeq]
    have hmul :
        K ^ 2 + MinkowskiSpace.minkowskiNormSq (m + 1) ζ * q - q ^ 2 =
          (c.im ^ 2 - c.re ^ 2) * q := by
      have hmul' :
          (K ^ 2 / q + MinkowskiSpace.minkowskiNormSq (m + 1) ζ - q) * q =
            (c.im ^ 2 - c.re ^ 2) * q := by
        exact congrArg (fun x : ℝ => x * q) hξeq2
      field_simp [hqne] at hmul'
      linarith [hmul']
    nlinarith [hmul]
  simpa [K, sq] using hpoly_aux

lemma norm_eq_neg_im_sq_of_poly_zero
    (c : ℂ) {q : ℝ}
    (hqneg : q < 0)
    (hpoly : q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 = 0) :
    q = -c.im ^ 2 := by
  have hfac : (q + c.im ^ 2) * (q - c.re ^ 2) = 0 := by
    nlinarith [hpoly]
  have hneg2 : q - c.re ^ 2 < 0 := by
    linarith [hqneg, sq_nonneg c.re]
  have hne2 : q - c.re ^ 2 ≠ 0 := ne_of_lt hneg2
  have hq0 : q + c.im ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfac with hq0 | hq2
    · exact hq0
    · exact (hne2 hq2).elim
  linarith [hq0]

lemma q_eq_neg_im_sq_of_zero_orth_component
    (c : ℂ)
    (u : Fin (m + 2) → ℂ)
    (hu : u ∈ quadricConeSet_im_with_value (m := m) (-(c ^ 2)))
    (hzero :
      let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
      let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
      let q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
      let K : ℝ := -(c.re * c.im)
      let ζ : MinkowskiSpace (m + 1) := ξ - (K / q) • η
      MinkowskiSpace.minkowskiNormSq (m + 1) ζ = 0) :
    let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
    MinkowskiSpace.minkowskiNormSq (m + 1) η = -c.im ^ 2 := by
  let ξ : MinkowskiSpace (m + 1) := fun μ => (u μ).re
  let η : MinkowskiSpace (m + 1) := fun μ => (u μ).im
  let q : ℝ := MinkowskiSpace.minkowskiNormSq (m + 1) η
  let K : ℝ := -(c.re * c.im)
  let ζ : MinkowskiSpace (m + 1) := ξ - (K / q) • η
  have hqneg : q < 0 := by
    rcases (mem_quadricConeSet_im_with_value_iff (m := m) (-(c ^ 2)) u).1 hu with
      ⟨hcone, _, _⟩
    have : MinkowskiSpace.minkowskiNormSq (m + 1) η < 0 := by
      simpa [η, InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
        MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
    simpa [q] using this
  have hpoly_id := poly_identity_of_mem (m := m) c u hu
  have hpoly0 :
      q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 = 0 := by
    have hKsq : K ^ 2 = (c.re * c.im) ^ 2 := by
      simp [K, sq]
    have hζ0 : MinkowskiSpace.minkowskiNormSq (m + 1) ζ = 0 := by
      simpa [ξ, η, q, K, ζ] using hzero
    have hpoly_id' :
        q ^ 2 + (c.im ^ 2 - c.re ^ 2) * q - (c.re * c.im) ^ 2 =
          MinkowskiSpace.minkowskiNormSq (m + 1) ζ * q := by
      simpa [ξ, η, q, K, ζ] using hpoly_id
    rw [hpoly_id', hζ0]
    ring
  have hq := norm_eq_neg_im_sq_of_poly_zero c hqneg hpoly0
  change q = -c.im ^ 2
  exact hq

lemma orbit_wScalarE0_subset_onePointQuadricSet (c : ℂ) :
    MulAction.orbit (ComplexLorentzGroup (m + 1)) (wScalarE0 (m := m) c) ⊆
      onePointQuadricSet_wScalarE0 (m := m) c := by
  intro z hz
  rcases hz with ⟨Λ, rfl⟩
  have hcol_quad :
      minkowskiColQuadric (m := m) (firstColCLG (m := m) Λ) = (-1 : ℂ) := by
    exact firstColImageCLG_minkowski_eq_neg_one (m := m) ⟨Λ, rfl⟩
  simp [onePointQuadricSet_wScalarE0]
  change minkowskiColQuadric (m := m) (fun μ =>
    complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) 0 μ) = -(c ^ 2)
  rw [complexLorentzAction_wScalarE0 (m := m) Λ c]
  change minkowskiColQuadric (m := m) (fun μ => c * firstColCLG (m := m) Λ μ) = -(c ^ 2)
  calc
    minkowskiColQuadric (m := m) (fun μ => c * firstColCLG (m := m) Λ μ)
        = c ^ 2 * minkowskiColQuadric (m := m) (firstColCLG (m := m) Λ) := by
            simpa using minkowskiColQuadric_smul (m := m) c (firstColCLG (m := m) Λ)
    _ = c ^ 2 * (-1 : ℂ) := by rw [hcol_quad]
    _ = -(c ^ 2) := by ring

lemma onePointQuadricSet_subset_orbit_wScalarE0 (c : ℂ) (hc : c ≠ 0) :
    onePointQuadricSet_wScalarE0 (m := m) c ⊆
      MulAction.orbit (ComplexLorentzGroup (m + 1)) (wScalarE0 (m := m) c) := by
  intro z hz
  have hvquad :
      minkowskiColQuadric (m := m) (fun μ => z 0 μ / c) = (-1 : ℂ) := by
    have hzquad : minkowskiColQuadric (m := m) (fun μ => z 0 μ) = -(c ^ 2) := hz
    have hscale := minkowskiColQuadric_smul (m := m) c (fun μ => z 0 μ / c)
    have hrewrite : (fun μ => c * (z 0 μ / c)) = (fun μ => z 0 μ) := by
      funext μ
      field_simp [hc]
    rw [hrewrite] at hscale
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    apply mul_left_cancel₀ hc2
    calc
      c ^ 2 * minkowskiColQuadric (m := m) (fun μ => z 0 μ / c)
          = minkowskiColQuadric (m := m) (fun μ => z 0 μ) := hscale.symm
      _ = -(c ^ 2) := hzquad
      _ = c ^ 2 * (-1 : ℂ) := by ring
  rcases firstColImageCLG_surj_of_minkowski_eq_neg_one (m := m) (fun μ => z 0 μ / c) hvquad with
    ⟨Λ, hcolΛ⟩
  refine ⟨Λ, ?_⟩
  ext k μ
  fin_cases k
  have hμ : Λ.val μ 0 = z 0 μ / c := by
    simpa [firstColCLG] using congrArg (fun f => f μ) hcolΛ
  change complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) 0 μ = z 0 μ
  rw [complexLorentzAction_wScalarE0 (m := m) Λ c]
  have hmain : c * Λ.val μ 0 = z 0 μ := by
    calc
      c * Λ.val μ 0 = c * (z 0 μ / c) := by rw [hμ]
      _ = z 0 μ := by field_simp [hc]
  simpa using hmain

lemma orbit_wScalarE0_eq_onePointQuadricSet (c : ℂ) (hc : c ≠ 0) :
    MulAction.orbit (ComplexLorentzGroup (m + 1)) (wScalarE0 (m := m) c) =
      onePointQuadricSet_wScalarE0 (m := m) c := by
  ext z
  constructor
  · intro hz
    exact orbit_wScalarE0_subset_onePointQuadricSet (m := m) c hz
  · intro hz
    exact onePointQuadricSet_subset_orbit_wScalarE0 (m := m) c hc hz

lemma continuous_onePointQuadricFn_wScalarE0 (c : ℂ) :
    Continuous (fun z : Fin 1 → Fin (m + 2) → ℂ =>
      minkowskiColQuadric (m := m) (fun μ => z 0 μ) + c ^ 2) := by
  unfold minkowskiColQuadric
  refine (continuous_finset_sum Finset.univ ?_).add continuous_const
  intro μ _
  exact continuous_const.mul
    (((continuous_apply μ).comp (continuous_apply (0 : Fin 1))).pow 2)

lemma isClosed_onePointQuadricSet_wScalarE0 (c : ℂ) :
    IsClosed (onePointQuadricSet_wScalarE0 (m := m) c) := by
  have hcont : Continuous (fun z : Fin 1 → Fin (m + 2) → ℂ =>
      minkowskiColQuadric (m := m) (fun μ => z 0 μ) + c ^ 2) :=
    continuous_onePointQuadricFn_wScalarE0 (m := m) c
  have hclosed0 : IsClosed ({(0 : ℂ)} : Set ℂ) := isClosed_singleton
  have hEq : onePointQuadricSet_wScalarE0 (m := m) c =
      (fun z : Fin 1 → Fin (m + 2) → ℂ =>
        minkowskiColQuadric (m := m) (fun μ => z 0 μ) + c ^ 2) ⁻¹' ({(0 : ℂ)} : Set ℂ) := by
    ext z
    constructor
    · intro hz
      change (minkowskiColQuadric (m := m) (fun μ => z 0 μ) + c ^ 2) = 0
      change minkowskiColQuadric (m := m) (fun μ => z 0 μ) = -(c ^ 2) at hz
      calc
        minkowskiColQuadric (m := m) (fun μ => z 0 μ) + c ^ 2 = (-(c ^ 2)) + c ^ 2 := by rw [hz]
        _ = 0 := by ring
    · intro hz
      simp [onePointQuadricSet_wScalarE0] at hz ⊢
      exact eq_neg_of_add_eq_zero_left hz
  rw [hEq]
  exact hclosed0.preimage hcont

/-- Baire structure on the one-point orbit subtype of `wScalarE0 c` (`c ≠ 0`). -/
theorem baireSpace_orbitSubtype_wScalarE0 (c : ℂ) (hc : c ≠ 0) :
    BaireSpace (orbitSubtype (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) := by
  have hEqSet :
      MulAction.orbit (ComplexLorentzGroup (m + 1)) (wScalarE0 (m := m) c) =
        onePointQuadricSet_wScalarE0 (m := m) c :=
    orbit_wScalarE0_eq_onePointQuadricSet (m := m) c hc
  have hClosed : IsClosed (onePointQuadricSet_wScalarE0 (m := m) c) :=
    isClosed_onePointQuadricSet_wScalarE0 (m := m) c
  haveI : CompleteSpace (onePointQuadricSet_wScalarE0 (m := m) c) :=
    hClosed.completeSpace_coe
  haveI : BaireSpace (onePointQuadricSet_wScalarE0 (m := m) c) := by
    infer_instance
  let hHomeo : orbitSubtype (d := m + 1) (n := 1) (wScalarE0 (m := m) c) ≃ₜ
      onePointQuadricSet_wScalarE0 (m := m) c :=
    Homeomorph.setCongr hEqSet
  exact hHomeo.symm.baireSpace

/-- One-point first-column orbit image for `wScalarE0 c` as a cone-cut of the
Minkowski unit quadric. -/
theorem firstColOrbitImage_wScalarE0_eq_quadric_inter_cone
    (c : ℂ) :
    firstColOrbitImage_wScalarE0_geom (m := m) c =
      quadricConeSet_wScalarE0 (m := m) c := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨Λ, hΛorbit, hcol⟩
    refine ⟨?_, ?_⟩
    · exact firstColImageCLG_minkowski_eq_neg_one (m := m) ⟨Λ, hcol⟩
    · have hcone :=
        (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ).1 hΛorbit
      simpa [hcol] using hcone
  · intro hv
    rcases hv with ⟨hquad, hcone⟩
    rcases firstColImageCLG_surj_of_minkowski_eq_neg_one (m := m) v hquad with ⟨Λ, hcolΛ⟩
    have hΛorbit :
        Λ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) := by
      exact (mem_orbitSet_wScalarE0_iff_firstCol (m := m) c Λ).2 (by simpa [hcolΛ] using hcone)
    exact ⟨Λ, hΛorbit, hcolΛ⟩

theorem isPreconnected_firstColOrbitImage_wScalarE0_geom_of_quadricCone
    (c : ℂ)
    (hpre : IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    IsPreconnected (firstColOrbitImage_wScalarE0_geom (m := m) c) := by
  simpa [firstColOrbitImage_wScalarE0_eq_quadric_inter_cone (m := m) c] using hpre

/-- Restricted first-column map on the canonical one-point orbit set. -/
abbrev firstColOrbitMapRestricted_wScalarE0_geom (c : ℂ) :
    orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) →
      firstColOrbitImage_wScalarE0_geom (m := m) c :=
  fun Λ => ⟨firstColCLG (m := m) Λ, ⟨Λ, Λ.property, rfl⟩⟩

theorem isConnected_fiber_firstColOrbitMapRestricted_wScalarE0_geom
    (c : ℂ)
    (y : firstColOrbitImage_wScalarE0_geom (m := m) c) :
    IsConnected
      ((firstColOrbitMapRestricted_wScalarE0_geom (m := m) c) ⁻¹' ({y} : Set _)) := by
  rcases y with ⟨v, hy⟩
  rcases hy with ⟨Λ0, hΛ0_orbit, hΛ0col⟩
  have hv : v ∈ firstColOrbitImage_wScalarE0_geom (m := m) c := ⟨Λ0, hΛ0_orbit, hΛ0col⟩
  have hfiber_conn :
      IsConnected (orbitFirstColFiber_wScalarE0 (m := m) c v) :=
    isConnected_orbitFirstColFiber_wScalarE0_of_nonempty (m := m) c v
      ⟨Λ0, hΛ0_orbit, hΛ0col⟩
  let incl : orbitFirstColFiber_wScalarE0 (m := m) c v →
      orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) :=
    fun g => ⟨g.1, g.2.1⟩
  have h_incl_cont : Continuous incl :=
    continuous_subtype_val.subtype_mk (fun g => g.2.1)
  have h_range_conn : IsConnected (Set.range incl) := by
    letI : ConnectedSpace (orbitFirstColFiber_wScalarE0 (m := m) c v) :=
      Subtype.connectedSpace hfiber_conn
    exact isConnected_range h_incl_cont
  have h_range_eq :
      Set.range incl =
        ((firstColOrbitMapRestricted_wScalarE0_geom (m := m) c) ⁻¹' ({⟨v, hv⟩} : Set _)) := by
    ext Λ
    constructor
    · rintro ⟨g, rfl⟩
      rcases g with ⟨g, hg_orbit, hg_col⟩
      apply Subtype.ext
      simpa [firstColOrbitMapRestricted_wScalarE0_geom] using hg_col
    · intro hΛ
      have hEq : firstColCLG (m := m) (Λ : ComplexLorentzGroup (m + 1)) = v := by
        exact congrArg Subtype.val hΛ
      refine ⟨⟨(Λ : ComplexLorentzGroup (m + 1)), ⟨Λ.property, hEq⟩⟩, ?_⟩
      ext
      rfl
  simpa [h_range_eq] using h_range_conn

theorem orbitSet_wScalarE0_isPreconnected_of_quadricCone_and_firstColQuotient
    (c : ℂ)
    (hwc : wScalarE0 (m := m) c ∈ ForwardTube (m + 1) 1)
    (hquot : Topology.IsQuotientMap
      (firstColOrbitMapRestricted_wScalarE0_geom (m := m) c))
    (hpre : IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    IsPreconnected (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) := by
  have hpreImg :
      IsPreconnected (firstColOrbitImage_wScalarE0_geom (m := m) c) :=
    isPreconnected_firstColOrbitImage_wScalarE0_geom_of_quadricCone (m := m) c hpre
  haveI : PreconnectedSpace (firstColOrbitImage_wScalarE0_geom (m := m) c) :=
    isPreconnected_iff_preconnectedSpace.mp hpreImg
  have hFib :
      ∀ y : firstColOrbitImage_wScalarE0_geom (m := m) c,
        IsConnected
          ((firstColOrbitMapRestricted_wScalarE0_geom (m := m) c) ⁻¹' ({y} : Set _)) :=
    isConnected_fiber_firstColOrbitMapRestricted_wScalarE0_geom (m := m) c
  haveI : Nonempty (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hwc⟩⟩
  haveI : PreconnectedSpace (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    IsQuotientMap.preconnectedSpace_of_connectedFibers hquot hFib
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- Orbit-map image for `wScalarE0 c`. -/
abbrev orbitImage_wScalarE0_geom (c : ℂ) :
    Set (Fin 1 → Fin (m + 2) → ℂ) :=
  (orbitMap (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) ''
    orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)

/-- Scale/pack map `v ↦ (fun _ μ => c * v μ)`. -/
abbrev scalePack_geom (c : ℂ) :
    (Fin (m + 2) → ℂ) → (Fin 1 → Fin (m + 2) → ℂ) :=
  fun v _ μ => c * v μ

/-- Unpack/scale-inverse map for `c ≠ 0`. -/
abbrev scaleUnpack_geom (c : ℂ) :
    (Fin 1 → Fin (m + 2) → ℂ) → (Fin (m + 2) → ℂ) :=
  fun z μ => z 0 μ / c

lemma continuous_scalePack_geom (c : ℂ) :
    Continuous (scalePack_geom (m := m) c) := by
  apply continuous_pi
  intro k
  fin_cases k
  apply continuous_pi
  intro μ
  exact continuous_const.mul (continuous_apply μ)

lemma continuous_scaleUnpack_geom (c : ℂ) :
    Continuous (scaleUnpack_geom (m := m) c) := by
  apply continuous_pi
  intro μ
  have h0μ : Continuous (fun z : Fin 1 → Fin (m + 2) → ℂ => z 0 μ) :=
    (continuous_apply μ).comp (continuous_apply 0)
  simpa [scaleUnpack_geom, div_eq_mul_inv] using h0μ.mul continuous_const

lemma scaleUnpack_scalePack_geom (c : ℂ) (hc : c ≠ 0) (v : Fin (m + 2) → ℂ) :
    scaleUnpack_geom (m := m) c (scalePack_geom (m := m) c v) = v := by
  ext μ
  simp [scaleUnpack_geom, scalePack_geom, hc]

lemma scalePack_scaleUnpack_geom (c : ℂ) (hc : c ≠ 0) (z : Fin 1 → Fin (m + 2) → ℂ) :
    scalePack_geom (m := m) c (scaleUnpack_geom (m := m) c z) = z := by
  ext k μ
  fin_cases k
  change c * (z 0 μ / c) = z 0 μ
  rw [div_eq_mul_inv]
  calc
    c * (z 0 μ * c⁻¹) = (c * c⁻¹) * z 0 μ := by ring
    _ = z 0 μ := by simp [hc]

lemma orbitImage_wScalarE0_eq_scalePack_image_firstCol_geom
    (c : ℂ) :
    orbitImage_wScalarE0_geom (m := m) c =
      (scalePack_geom (m := m) c) '' firstColOrbitImage_wScalarE0_geom (m := m) c := by
  ext z
  constructor
  · rintro ⟨Λ, hΛ, rfl⟩
    refine ⟨firstColCLG (m := m) Λ, ⟨Λ, hΛ, rfl⟩, ?_⟩
    ext k μ
    fin_cases k
    change c * Λ.val μ 0 =
      (complexLorentzAction (d := m + 1) (n := 1) Λ
        (wScalarE0 (m := m) c) 0 μ)
    rw [complexLorentzAction_wScalarE0 (m := m) Λ c]
  · rintro ⟨v, hv, rfl⟩
    rcases hv with ⟨Λ, hΛ, hvΛ⟩
    refine ⟨Λ, hΛ, ?_⟩
    ext k μ
    fin_cases k
    change (complexLorentzAction (d := m + 1) (n := 1) Λ (wScalarE0 (m := m) c) 0 μ) =
      c * v μ
    rw [complexLorentzAction_wScalarE0 (m := m) Λ c]
    have hvμ : Λ.val μ 0 = v μ := by
      simpa [firstColCLG] using congrArg (fun f => f μ) hvΛ
    simp [hvμ]

theorem isPreconnected_orbitImage_wScalarE0_geom_of_firstColImage
    (c : ℂ)
    (hpre : IsPreconnected (firstColOrbitImage_wScalarE0_geom (m := m) c)) :
    IsPreconnected (orbitImage_wScalarE0_geom (m := m) c) := by
  have hpre1 : IsPreconnected ((scalePack_geom (m := m) c) ''
      firstColOrbitImage_wScalarE0_geom (m := m) c) :=
    hpre.image (scalePack_geom (m := m) c) (continuous_scalePack_geom (m := m) c).continuousOn
  simpa [orbitImage_wScalarE0_eq_scalePack_image_firstCol_geom (m := m) c] using hpre1

theorem orbitSet_wScalarE0_isPreconnected_of_quadricCone_nonempty
    (c : ℂ) (hc : c ≠ 0)
    (hne : Nonempty (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)))
    (hpre : IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    IsPreconnected (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) := by
  letI : BaireSpace (orbitSubtype (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    baireSpace_orbitSubtype_wScalarE0 (m := m) c hc
  have hpreFirst :
      IsPreconnected (firstColOrbitImage_wScalarE0_geom (m := m) c) :=
    isPreconnected_firstColOrbitImage_wScalarE0_geom_of_quadricCone (m := m) c hpre
  have hpreImg :
      IsPreconnected (orbitImage_wScalarE0_geom (m := m) c) :=
    isPreconnected_orbitImage_wScalarE0_geom_of_firstColImage (m := m) c hpreFirst
  haveI : PreconnectedSpace (orbitImage_wScalarE0_geom (m := m) c) :=
    isPreconnected_iff_preconnectedSpace.mp hpreImg
  have hstab :
      IsConnected (stabilizer (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    isConnected_stabilizer_wScalarE0 (m := m) c hc
  have hquot :
      Topology.IsQuotientMap (fun Λ : orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) =>
        (⟨orbitMap (d := m + 1) (n := 1) (wScalarE0 (m := m) c) Λ,
          ⟨Λ, Λ.property, rfl⟩⟩ :
          orbitMap (d := m + 1) (n := 1) (wScalarE0 (m := m) c) ''
            orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c))) :=
    orbitSet_restricted_orbitMap_isQuotient_of_baireOrbit
      (d := m + 1) (n := 1) (w := wScalarE0 (m := m) c)
  exact orbitSet_isPreconnected_of_stabilizer_connected_nonempty
    (d := m + 1) (n := 1) (w := wScalarE0 (m := m) c) hne hstab hquot

theorem orbitSet_wScalarE0_isPreconnected_of_quadricCone
    (c : ℂ) (hc : c ≠ 0)
    (hwc : wScalarE0 (m := m) c ∈ ForwardTube (m + 1) 1)
    (hpre : IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    IsPreconnected (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) := by
  have hne : Nonempty (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hwc⟩⟩
  exact orbitSet_wScalarE0_isPreconnected_of_quadricCone_nonempty
    (m := m) c hc hne hpre

/-- One-point reduction: preconnectedness for all one-point forward-tube orbit sets
follows from preconnectedness of the canonical quadric-cone slices. -/
theorem orbitSet_forwardTube_one_isPreconnected_of_quadricCone_family
    (w : Fin 1 → Fin (m + 2) → ℂ)
    (hw : w ∈ ForwardTube (m + 1) 1)
    (hquad : ∀ c : ℂ, c ≠ 0 → IsPreconnected (quadricConeSet_wScalarE0 (m := m) c)) :
    IsPreconnected (orbitSet (d := m + 1) (n := 1) w) := by
  obtain ⟨Γ, c, hc, hEq⟩ := exists_action_wScalarE0_of_forwardTube_one (m := m) w hw
  have hΓmem : Γ ∈ orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c) := by
    simpa [orbitSet, hEq] using hw
  have hpre0 : IsPreconnected (orbitSet (d := m + 1) (n := 1) (wScalarE0 (m := m) c)) :=
    orbitSet_wScalarE0_isPreconnected_of_quadricCone_nonempty (m := m) c hc
      ⟨⟨Γ, hΓmem⟩⟩ (hquad c hc)
  exact orbitSet_isPreconnected_of_orbit_eq (d := m + 1) (n := 1)
    (w0 := wScalarE0 (m := m) c) (w := w) Γ hEq hpre0

end BHW
