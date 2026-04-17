import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransformCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits

/-!
# Section 4.3 Fourier-Laplace Closure

This file contains the finite-support closure step that is downstream of the
compiled transform-image positivity theorem.  It deliberately keeps the
remaining density assumption explicit and pairwise on the Section 4.3 frequency
quotient: once a sequence of transform-component carriers converges on all
finite Wightman tensor terms, positivity passes to the limiting public
`BorchersSequence`.
-/

noncomputable section

open scoped Topology FourierTransform BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem borchersConj_continuous_closure {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
  let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := fun y i => y (Fin.rev i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y i => y (Fin.rev i)
      left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i)
      continuous_invFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i) }
  let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
  have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
    intro f
    ext x
    simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.reverse_apply, revCLE]
  have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
    let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzMap.conj
        map_add' := fun f g => by
          ext x
          simp [SchwartzMap.conj_apply]
        map_smul' := fun c f => by
          simpa using (SchwartzMap.conj_smul (c := (c : ℂ)) f) }
    exact WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      conjL (fun q => by
        rcases q with ⟨k, l⟩
        refine ⟨{(k, l)}, 1, ?_⟩
        intro f
        simpa [Finset.sup_singleton] using SchwartzMap.seminorm_conj_le k l f)
  show Continuous (fun f => (revCLM f).conj)
  exact hconj_cont.comp revCLM.continuous |>.congr (fun f => by
    show (revCLM f).conj = f.borchersConj
    rw [hrev]
    rfl)

omit [NeZero d] in
private theorem conjTensorProduct_continuous_closure {n m : ℕ} :
    Continuous
      (fun p : SchwartzNPoint d n × SchwartzNPoint d m => p.1.conjTensorProduct p.2) := by
  have hpair :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          (p.1.borchersConj, p.2)) :=
    ((borchersConj_continuous_closure (d := d)).comp continuous_fst).prodMk continuous_snd
  let h :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          p.1.borchersConj.tensorProduct p.2) :=
    SchwartzMap.tensorProduct_continuous.comp hpair
  simpa [SchwartzMap.conjTensorProduct] using h

/-- Successor-right Wightman pair scalar descent through the two component
Section 4.3 frequency projections.

This is the first quotient-safe piece of the final finite-product closure: the
proof does **not** claim that the full tensor frequency projection descends
from the two component quotients.  Instead it uses the actual Wightman spectral
support of `bvt_W` and the spectral-region factorization of the flattened
conjugate tensor product. -/
theorem bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ₁ φ₂ : SchwartzNPoint d n)
    (ψ₁ ψ₂ : SchwartzNPoint d (m + 1))
    (hφ :
      section43FrequencyProjection (d := d) n φ₁ =
        section43FrequencyProjection (d := d) n φ₂)
    (hψ :
      section43FrequencyProjection (d := d) (m + 1) ψ₁ =
        section43FrequencyProjection (d := d) (m + 1) ψ₂) :
    bvt_W OS lgc (n + (m + 1)) (φ₁.conjTensorProduct ψ₁) =
      bvt_W OS lgc (n + (m + 1)) (φ₂.conjTensorProduct ψ₂) := by
  obtain ⟨Tflat, hTflat_supp, hTflat_bv⟩ :=
    bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion
      (d := d) OS lgc (n + (m + 1))
  have hφ_quot :
      section43PositiveEnergyQuotientMap (d := d) n
          (section43FrequencyRepresentative (d := d) n φ₁) =
        section43PositiveEnergyQuotientMap (d := d) n
          (section43FrequencyRepresentative (d := d) n φ₂) := by
    simpa [section43FrequencyProjection] using hφ
  have hψ_quot :
      section43PositiveEnergyQuotientMap (d := d) (m + 1)
          (section43FrequencyRepresentative (d := d) (m + 1) ψ₁) =
        section43PositiveEnergyQuotientMap (d := d) (m + 1)
          (section43FrequencyRepresentative (d := d) (m + 1) ψ₂) := by
    simpa [section43FrequencyProjection] using hψ
  have hφ_eqOn :
      Set.EqOn
        (section43FrequencyRepresentative (d := d) n φ₁ :
          NPointDomain d n → ℂ)
        (section43FrequencyRepresentative (d := d) n φ₂ :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) hφ_quot
  have hψ_eqOn :
      Set.EqOn
        (section43FrequencyRepresentative (d := d) (m + 1) ψ₁ :
          NPointDomain d (m + 1) → ℂ)
        (section43FrequencyRepresentative (d := d) (m + 1) ψ₂ :
          NPointDomain d (m + 1) → ℂ)
        (section43PositiveEnergyRegion d (m + 1)) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := m + 1) hψ_quot
  have hEqSpectral :
      Set.EqOn
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁)) :
            (Fin ((n + (m + 1)) * (d + 1)) → ℝ) → ℂ)
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂)) :
            (Fin ((n + (m + 1)) * (d + 1)) → ℝ) → ℂ)
        (section43WightmanSpectralRegion d (n + (m + 1))) := by
    intro ξ hξ
    let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
    have hleft_mem :
        section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ ∈
          section43PositiveEnergyRegion d n := by
      simpa [qξ] using
        section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
          (d := d) (n := n) (r := m + 1) (Nat.succ_pos m) hξ
    have hright_mem :
        section43RightTailBlock d n (m + 1) qξ ∈
          section43PositiveEnergyRegion d (m + 1) := by
      simpa [qξ] using
        section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
          (d := d) (n := n) (r := m + 1) hξ
    have hleft_eq :=
      hφ_eqOn hleft_mem
    have hright_eq :=
      hψ_eqOn hright_mem
    have hfac₁ :=
      physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
        (d := d) (n := n) (m := m) φ₁ ψ₁ hξ
    have hfac₂ :=
      physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
        (d := d) (n := n) (m := m) φ₂ ψ₂ hξ
    dsimp only at hfac₁ hfac₂
    rw [hfac₁, hfac₂, hleft_eq, hright_eq]
  have hflat₁ :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁)) =
        φ₁.conjTensorProduct ψ₁ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hflat₂ :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂)) =
        φ₂.conjTensorProduct ψ₂ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  calc
    bvt_W OS lgc (n + (m + 1)) (φ₁.conjTensorProduct ψ₁)
        = bvt_W OS lgc (n + (m + 1))
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))) := by
          rw [hflat₁]
    _ = Tflat
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))) := by
          simpa using
            hTflat_bv
              (flattenSchwartzNPoint (d := d) (φ₁.conjTensorProduct ψ₁))
    _ = Tflat
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))) := by
          exact hasFourierSupportIn_eqOn hTflat_supp hEqSpectral
    _ = bvt_W OS lgc (n + (m + 1))
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))) := by
          simpa using
            (hTflat_bv
              (flattenSchwartzNPoint (d := d) (φ₂.conjTensorProduct ψ₂))).symm
    _ = bvt_W OS lgc (n + (m + 1)) (φ₂.conjTensorProduct ψ₂) := by
          rw [hflat₂]

/-- In degree zero, equality of Section 4.3 frequency projections is equality
of the unique scalar value. -/
theorem section43FrequencyProjection_zero_eval_eq
    (φ ψ : SchwartzNPoint d 0)
    (hproj :
      section43FrequencyProjection (d := d) 0 φ =
        section43FrequencyProjection (d := d) 0 ψ) :
    φ 0 = ψ 0 := by
  have hquot :
      section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative (d := d) 0 φ) =
        section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative (d := d) 0 ψ) := by
    simpa [section43FrequencyProjection] using hproj
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hquot
  have h0 : (0 : NPointDomain d 0) ∈ section43PositiveEnergyRegion d 0 := by
    simp [section43PositiveEnergyRegion]
  have hpoint := hEqOn h0
  rw [section43FrequencyRepresentative_zero_apply d φ 0] at hpoint
  rw [section43FrequencyRepresentative_zero_apply d ψ 0] at hpoint
  exact hpoint

/-- Wightman pair scalar descent through the two component Section 4.3
frequency projections.

The positive-right-degree branch is the genuine spectral-region argument in
`bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight`.
The right-degree-zero branch is handled separately: `(0,0)` is scalar
evaluation, while `(n+1,0)` is flipped to successor-right by Hermiticity. -/
theorem bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ₁ φ₂ : SchwartzNPoint d n)
    (ψ₁ ψ₂ : SchwartzNPoint d m)
    (hφ :
      section43FrequencyProjection (d := d) n φ₁ =
        section43FrequencyProjection (d := d) n φ₂)
    (hψ :
      section43FrequencyProjection (d := d) m ψ₁ =
        section43FrequencyProjection (d := d) m ψ₂) :
    bvt_W OS lgc (n + m) (φ₁.conjTensorProduct ψ₁) =
      bvt_W OS lgc (n + m) (φ₂.conjTensorProduct ψ₂) := by
  cases m with
  | succ m =>
      exact
        bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
          (d := d) OS lgc φ₁ φ₂ ψ₁ ψ₂ hφ hψ
  | zero =>
      cases n with
      | zero =>
          have hφ0 := section43FrequencyProjection_zero_eval_eq (d := d) φ₁ φ₂ hφ
          have hψ0 := section43FrequencyProjection_zero_eval_eq (d := d) ψ₁ ψ₂ hψ
          have hφ_eq : φ₁ = φ₂ := by
            ext x
            have hx : x = (0 : NPointDomain d 0) := Subsingleton.elim _ _
            rw [hx]
            exact hφ0
          have hψ_eq : ψ₁ = ψ₂ := by
            ext x
            have hx : x = (0 : NPointDomain d 0) := Subsingleton.elim _ _
            rw [hx]
            exact hψ0
          rw [hφ_eq, hψ_eq]
      | succ n =>
          have hscalar :
              ∀ (φ : SchwartzNPoint d (n + 1)) (ψ : SchwartzNPoint d 0),
                bvt_W OS lgc ((n + 1) + 0) (φ.conjTensorProduct ψ) =
                  starRingEnd ℂ
                    (bvt_W OS lgc (0 + (n + 1)) (ψ.conjTensorProduct φ)) := by
            intro φ ψ
            let Fφ : BorchersSequence d := BorchersSequence.single (n + 1) φ
            let Gψ : BorchersSequence d := BorchersSequence.single 0 ψ
            have hFG :
                WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ =
                  bvt_W OS lgc ((n + 1) + 0) (φ.conjTensorProduct ψ) := by
              simpa [Fφ, Gψ] using
                WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc)
                  (n := n + 1) (m := 0) (f := φ) (g := ψ)
            have hGF :
                WightmanInnerProduct d (bvt_W OS lgc) Gψ Fφ =
                  bvt_W OS lgc (0 + (n + 1)) (ψ.conjTensorProduct φ) := by
              simpa [Fφ, Gψ] using
                WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc)
                  (n := 0) (m := n + 1) (f := ψ) (g := φ)
            have hherm :
                WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ =
                  starRingEnd ℂ
                    (WightmanInnerProduct d (bvt_W OS lgc) Gψ Fφ) :=
              WightmanInnerProduct_hermitian_of (d := d) (W := bvt_W OS lgc)
                (bvt_hermitian_from_boundaryValue (d := d) OS lgc) Fφ Gψ
            calc
              bvt_W OS lgc ((n + 1) + 0) (φ.conjTensorProduct ψ)
                  = WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ := hFG.symm
              _ = starRingEnd ℂ
                    (WightmanInnerProduct d (bvt_W OS lgc) Gψ Fφ) := hherm
              _ = starRingEnd ℂ
                    (bvt_W OS lgc (0 + (n + 1)) (ψ.conjTensorProduct φ)) := by
                    rw [hGF]
          have hflip :
              bvt_W OS lgc (0 + (n + 1)) (ψ₁.conjTensorProduct φ₁) =
                bvt_W OS lgc (0 + (n + 1)) (ψ₂.conjTensorProduct φ₂) :=
            bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq_succRight
              (d := d) (n := 0) (m := n) OS lgc ψ₁ ψ₂ φ₁ φ₂ hψ hφ
          calc
            bvt_W OS lgc ((n + 1) + 0) (φ₁.conjTensorProduct ψ₁)
                = starRingEnd ℂ
                    (bvt_W OS lgc (0 + (n + 1)) (ψ₁.conjTensorProduct φ₁)) :=
                  hscalar φ₁ ψ₁
            _ = starRingEnd ℂ
                    (bvt_W OS lgc (0 + (n + 1)) (ψ₂.conjTensorProduct φ₂)) := by
                  rw [hflip]
            _ = bvt_W OS lgc ((n + 1) + 0) (φ₂.conjTensorProduct ψ₂) :=
                  (hscalar φ₂ ψ₂).symm

/-- The Wightman tensor scalar descended to the two component Section 4.3
frequency quotients.

The representative used in the raw formula is the continuous inverse of the
deterministic frequency representative.  Well-definedness is supplied by
`bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq`, so this
definition is quotient-safe rather than an arbitrary preimage wrapper. -/
noncomputable def bvt_W_pairing_descended_frequencyProjection
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) :
    Section43PositiveEnergyComponent (d := d) n →
      Section43PositiveEnergyComponent (d := d) m → ℂ := by
  intro u v
  refine Quotient.liftOn₂ u v
    (fun (Φ : SchwartzNPoint d n) (Ψ : SchwartzNPoint d m) =>
      bvt_W OS lgc (n + m)
        ((section43FrequencyRepresentativeInv d n Φ).conjTensorProduct
          (section43FrequencyRepresentativeInv d m Ψ))) ?_
  intro Φ₁ Ψ₁ Φ₂ Ψ₂ hΦ hΨ
  have hΦq :
      (Submodule.Quotient.mk Φ₁ : Section43PositiveEnergyComponent (d := d) n) =
        Submodule.Quotient.mk Φ₂ :=
    Quotient.sound hΦ
  have hΨq :
      (Submodule.Quotient.mk Ψ₁ : Section43PositiveEnergyComponent (d := d) m) =
        Submodule.Quotient.mk Ψ₂ :=
    Quotient.sound hΨ
  have hΦproj :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Φ₁) =
        section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Φ₂) := by
    simpa [section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hΦq
  have hΨproj :
      section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m Ψ₁) =
        section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m Ψ₂) := by
    simpa [section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hΨq
  exact
    bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
      (d := d) OS lgc
      (section43FrequencyRepresentativeInv d n Φ₁)
      (section43FrequencyRepresentativeInv d n Φ₂)
      (section43FrequencyRepresentativeInv d m Ψ₁)
      (section43FrequencyRepresentativeInv d m Ψ₂)
      hΦproj hΨproj

/-- Applying the descended pair scalar to actual frequency projections recovers
the original Wightman tensor scalar. -/
theorem bvt_W_pairing_descended_frequencyProjection_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) :
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n m
        (section43FrequencyProjection (d := d) n φ)
        (section43FrequencyProjection (d := d) m ψ) =
      bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) := by
  unfold bvt_W_pairing_descended_frequencyProjection section43FrequencyProjection
    section43PositiveEnergyQuotientMap
  change
    bvt_W OS lgc (n + m)
        ((section43FrequencyRepresentativeInv d n
            (section43FrequencyRepresentative (d := d) n φ)).conjTensorProduct
          (section43FrequencyRepresentativeInv d m
            (section43FrequencyRepresentative (d := d) m ψ))) =
      bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ)
  have hφproj :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n
            (section43FrequencyRepresentative (d := d) n φ)) =
        section43FrequencyProjection (d := d) n φ := by
    simp [section43FrequencyProjection, section43FrequencyRepresentativeInv_right]
  have hψproj :
      section43FrequencyProjection (d := d) m
          (section43FrequencyRepresentativeInv d m
            (section43FrequencyRepresentative (d := d) m ψ)) =
        section43FrequencyProjection (d := d) m ψ := by
    simp [section43FrequencyProjection, section43FrequencyRepresentativeInv_right]
  exact
    bvt_W_conjTensorProduct_eq_of_section43FrequencyProjection_eq
      (d := d) OS lgc
      (section43FrequencyRepresentativeInv d n
        (section43FrequencyRepresentative (d := d) n φ))
      φ
      (section43FrequencyRepresentativeInv d m
        (section43FrequencyRepresentative (d := d) m ψ))
      ψ
      hφproj hψproj

/-- The descended Wightman tensor scalar is continuous on the product of the
two Section 4.3 component frequency quotients. -/
theorem continuous_bvt_W_pairing_descended_frequencyProjection
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) :
    Continuous
      (fun p : Section43PositiveEnergyComponent (d := d) n ×
          Section43PositiveEnergyComponent (d := d) m =>
        bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n m
          p.1 p.2) := by
  have hqn :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) n :
          SchwartzNPoint d n → Section43PositiveEnergyComponent (d := d) n) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) n).isOpenQuotientMap_mkQ
  have hqm :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) m :
          SchwartzNPoint d m → Section43PositiveEnergyComponent (d := d) m) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) m).isOpenQuotientMap_mkQ
  let invn : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    section43FrequencyRepresentativeInv d n
  let invm : SchwartzNPoint d m →L[ℂ] SchwartzNPoint d m :=
    section43FrequencyRepresentativeInv d m
  have hraw :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          bvt_W OS lgc (n + m)
            ((invn p.1).conjTensorProduct (invm p.2))) := by
    have hinv :
        Continuous
          (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
            (invn p.1, invm p.2)) :=
      (invn.continuous.comp continuous_fst).prodMk
        (invm.continuous.comp continuous_snd)
    have hct :
        Continuous
          (fun q : SchwartzNPoint d n × SchwartzNPoint d m =>
            q.1.conjTensorProduct q.2) :=
      conjTensorProduct_continuous_closure (d := d) (n := n) (m := m)
    have htensor_comp :
        Continuous
          ((fun q : SchwartzNPoint d n × SchwartzNPoint d m =>
              q.1.conjTensorProduct q.2) ∘
            fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
              (invn p.1, invm p.2)) :=
      hct.comp hinv
    have htensor :
        Continuous
          (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
            (invn p.1).conjTensorProduct (invm p.2)) := by
      simpa only [Function.comp] using htensor_comp
    exact (bvt_W_continuous (d := d) OS lgc (n + m)).comp htensor
  refine (hqn.prodMap hqm).isQuotientMap.continuous_iff.2 ?_
  have hcomp :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n m
            (section43PositiveEnergyQuotientMap (d := d) n p.1)
            (section43PositiveEnergyQuotientMap (d := d) m p.2)) := by
    refine hraw.congr ?_
    intro p
    unfold bvt_W_pairing_descended_frequencyProjection section43PositiveEnergyQuotientMap
    rfl
  exact hcomp

/-- The finite product of Section 4.3 component frequency quotients up to
degree `B`. -/
abbrev Section43FiniteComponentProduct (d B : ℕ) [NeZero d] :=
  (n : Fin (B + 1)) → Section43PositiveEnergyComponent (d := d) n.val

/-- A compact ordered Euclidean source for one Section 4.3 Fourier-Laplace
transform component. -/
structure Section43CompactOrderedSource (d n : ℕ) [NeZero d] where
  f : SchwartzNPoint d n
  ordered :
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n
  compact : HasCompactSupport (f : NPointDomain d n → ℂ)

/-- The genuine Section 4.3 Fourier-Laplace transform component as a map from
compact ordered sources to the positive-energy quotient. -/
noncomputable def section43FourierLaplaceTransformComponentMap
    (d n : ℕ) [NeZero d] :
    Section43CompactOrderedSource d n →
      Section43PositiveEnergyComponent (d := d) n :=
  fun src =>
    section43FourierLaplaceTransformComponent d n
      src.f src.ordered src.compact

/-- If the preimage of the compact ordered Fourier-Laplace transform image is
dense in ambient Schwartz space, then the transform component map has dense
range in the Section 4.3 positive-energy quotient.  This is the quotient-map
form of the remaining analytic density theorem. -/
theorem denseRange_section43FourierLaplaceTransformComponentMap_of_dense_preimage
    (d n : ℕ) [NeZero d]
    (hpre :
      Dense
        ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
          Set.range (section43FourierLaplaceTransformComponentMap d n))) :
    DenseRange (section43FourierLaplaceTransformComponentMap d n) := by
  have hq :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap (d := d) n :
          SchwartzNPoint d n → Section43PositiveEnergyComponent (d := d) n) := by
    simpa [section43PositiveEnergyQuotientMap] using
      (section43PositiveEnergyVanishingSubmodule (d := d) n).isOpenQuotientMap_mkQ
  exact hq.dense_preimage_iff.mp hpre

/-- The finite product of genuine compact ordered Section 4.3 transform
components up to degree `B`. -/
noncomputable def section43FiniteTransformComponentMap
    (d B : ℕ) [NeZero d] :
    ((n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) →
      Section43FiniteComponentProduct d B :=
  fun src n => section43FourierLaplaceTransformComponentMap d n.val (src n)

/-- Componentwise dense range implies dense range of the finite transform
component product.  This isolates the pure product-topology step from the
analytic Fourier-Laplace density theorem. -/
theorem denseRange_section43FiniteTransformComponentMap_of_components
    (d B : ℕ) [NeZero d]
    (hdense :
      ∀ n : Fin (B + 1),
        DenseRange (section43FourierLaplaceTransformComponentMap d n.val)) :
    DenseRange (section43FiniteTransformComponentMap d B) := by
  change DenseRange
    (Pi.map
      (fun n : Fin (B + 1) =>
        section43FourierLaplaceTransformComponentMap d n.val))
  exact DenseRange.piMap hdense

/-- The positive-time Borchers sequence associated to a finite compact ordered
source tuple, padded by zero above the finite bound. -/
noncomputable def section43FiniteSource_to_positiveTimeBorchersSequence
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence :=
    { funcs := fun n =>
        if h : n ≤ B then
          (src ⟨n, Nat.lt_succ_of_le h⟩).f
        else
          0
      bound := B
      bound_spec := by
        intro n hn
        have hnot : ¬ n ≤ B := by omega
        simp [hnot] }
  ordered_tsupport := by
    intro n
    by_cases h : n ≤ B
    · simpa [h] using (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
    · simp [h]

/-- Compactness of each padded component of
`section43FiniteSource_to_positiveTimeBorchersSequence`. -/
theorem section43FiniteSource_to_positiveTimeBorchersSequence_compact
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    ∀ n,
      HasCompactSupport
        ((((section43FiniteSource_to_positiveTimeBorchersSequence d B src :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  intro n
  by_cases h : n ≤ B
  · simpa [section43FiniteSource_to_positiveTimeBorchersSequence, h] using
      (src ⟨n, Nat.lt_succ_of_le h⟩).compact
  · simpa [section43FiniteSource_to_positiveTimeBorchersSequence, h] using
      (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d n → ℂ))

/-- The source-decorated transform-component carrier associated to a finite
compact ordered source tuple, padded by zero above the finite bound. -/
noncomputable def section43FiniteSource_to_BvtTransformComponentSequence
    (d B : ℕ) [NeZero d]
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    BvtTransformComponentSequence d where
  toBorchers :=
    { funcs := fun n =>
        if h : n ≤ B then
          section43TransformComponentTarget d n
            (src ⟨n, Nat.lt_succ_of_le h⟩).f
            (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
            (src ⟨n, Nat.lt_succ_of_le h⟩).compact
        else
          0
      bound := B
      bound_spec := by
        intro n hn
        have hnot : ¬ n ≤ B := by omega
        simp [hnot] }
  source := section43FiniteSource_to_positiveTimeBorchersSequence d B src
  source_compact :=
    section43FiniteSource_to_positiveTimeBorchersSequence_compact d B src
  freq_eq := by
    intro n
    by_cases h : n ≤ B
    · simpa [section43FiniteSource_to_positiveTimeBorchersSequence,
        section43FourierLaplaceTransformComponentMap, h] using
        section43TransformComponentTarget_freq_eq d n
          (src ⟨n, Nat.lt_succ_of_le h⟩).f
          (src ⟨n, Nat.lt_succ_of_le h⟩).ordered
          (src ⟨n, Nat.lt_succ_of_le h⟩).compact
    · have hzero_ord :
          tsupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
            OrderedPositiveTimeRegion d n := by
        simp
      have hzero_compact :
          HasCompactSupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
        HasCompactSupport.zero
      simp [section43FiniteSource_to_positiveTimeBorchersSequence, h,
        section43FourierLaplaceTransformComponent_zero]

/-- The descended finite Wightman quadratic form on component frequency
quotients. -/
noncomputable def bvt_W_finiteComponentQuadratic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ) :
    Section43FiniteComponentProduct d B → ℂ :=
  fun u =>
    ∑ n : Fin (B + 1), ∑ m : Fin (B + 1),
      bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n.val m.val
        (u n) (u m)

/-- The finite component quadratic form is continuous. -/
theorem continuous_bvt_W_finiteComponentQuadratic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ) :
    Continuous (bvt_W_finiteComponentQuadratic (d := d) OS lgc B) := by
  unfold bvt_W_finiteComponentQuadratic
  refine continuous_finset_sum _ (fun n _hn => ?_)
  refine continuous_finset_sum _ (fun m _hm => ?_)
  have hcoords :
      Continuous
        (fun u : Section43FiniteComponentProduct d B => (u n, u m)) :=
    (continuous_apply n).prodMk (continuous_apply m)
  exact
    (continuous_bvt_W_pairing_descended_frequencyProjection
      (d := d) OS lgc n.val m.val).comp hcoords

/-- Evaluating the finite component quadratic form on the component frequency
projections of a bounded Borchers sequence recovers the Wightman inner product. -/
theorem bvt_W_finiteComponentQuadratic_apply_borchers
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ)
    (F : BorchersSequence d)
    (hB : F.bound ≤ B) :
    bvt_W_finiteComponentQuadratic (d := d) OS lgc B
        (fun n =>
          section43FrequencyProjection (d := d) n.val (F.funcs n.val)) =
      WightmanInnerProduct d (bvt_W OS lgc) F F := by
  have hF_eq :
      WightmanInnerProduct d (bvt_W OS lgc) F F =
        WightmanInnerProductN d (bvt_W OS lgc) F F (B + 1) (B + 1) := by
    exact WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
      (F := F) (G := F) (N₁ := B + 1) (N₂ := B + 1)
      (Nat.succ_le_succ hB) (Nat.succ_le_succ hB)
  rw [hF_eq]
  unfold bvt_W_finiteComponentQuadratic WightmanInnerProductN
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < B + 1 := Finset.mem_range.mp hn
  rw [dif_pos hnlt]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlt : m < B + 1 := Finset.mem_range.mp hm
  rw [dif_pos hmlt]
  exact bvt_W_pairing_descended_frequencyProjection_apply
    (d := d) OS lgc n m (F.funcs n) (F.funcs m)

/-- The finite descended quadratic form is nonnegative on the finite product of
genuine compact ordered Fourier-Laplace transform components. -/
theorem bvt_W_finiteComponentQuadratic_nonneg_on_finiteTransformComponentMap
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ)
    (src : (n : Fin (B + 1)) → Section43CompactOrderedSource d n.val) :
    0 ≤
      (bvt_W_finiteComponentQuadratic (d := d) OS lgc B
        (section43FiniteTransformComponentMap d B src)).re := by
  let A := section43FiniteSource_to_BvtTransformComponentSequence d B src
  have htuple :
      (fun n : Fin (B + 1) =>
        section43FrequencyProjection (d := d) n.val (A.toBorchers.funcs n.val)) =
        section43FiniteTransformComponentMap d B src := by
    funext n
    have hn : n.val ≤ B := Nat.lt_succ_iff.mp n.isLt
    have hfreq := A.freq_eq n.val
    simpa [A, section43FiniteSource_to_BvtTransformComponentSequence,
      section43FiniteSource_to_positiveTimeBorchersSequence,
      section43FiniteTransformComponentMap,
      section43FourierLaplaceTransformComponentMap, hn] using hfreq
  have hA_bound : A.toBorchers.bound ≤ B := by
    rfl
  have hquad :
      bvt_W_finiteComponentQuadratic (d := d) OS lgc B
          (section43FiniteTransformComponentMap d B src) =
        WightmanInnerProduct d (bvt_W OS lgc) A.toBorchers A.toBorchers := by
    rw [← htuple]
    exact bvt_W_finiteComponentQuadratic_apply_borchers
      (d := d) OS lgc B A.toBorchers hA_bound
  rw [hquad]
  exact bvt_wightmanInner_self_nonneg_onTransformImage (d := d) OS lgc A

/-- Closed-set bridge for the finite component quadratic form: if a dense set
of finite component tuples has nonnegative quadratic value, then every finite
component tuple has nonnegative quadratic value. -/
theorem bvt_W_finiteComponentQuadratic_nonneg_of_denseRange
    {X : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ)
    (T : X → Section43FiniteComponentProduct d B)
    (hT_dense : DenseRange T)
    (hT_nonneg :
      ∀ x : X,
        0 ≤
          (bvt_W_finiteComponentQuadratic (d := d) OS lgc B (T x)).re)
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (bvt_W_finiteComponentQuadratic (d := d) OS lgc B u).re := by
  let Q : Section43FiniteComponentProduct d B → ℂ :=
    bvt_W_finiteComponentQuadratic (d := d) OS lgc B
  let S : Set (Section43FiniteComponentProduct d B) := {u | 0 ≤ (Q u).re}
  have hclosed : IsClosed S := by
    have hcont : Continuous (fun u : Section43FiniteComponentProduct d B => (Q u).re) :=
      Complex.continuous_re.comp
        (continuous_bvt_W_finiteComponentQuadratic (d := d) OS lgc B)
    change IsClosed
      ((fun u : Section43FiniteComponentProduct d B => (Q u).re) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.preimage hcont
  have hrange : Set.range T ⊆ S := by
    rintro _ ⟨x, rfl⟩
    exact hT_nonneg x
  have hclosure_subset : closure (Set.range T) ⊆ S :=
    hclosed.closure_subset_iff.mpr hrange
  have hu_closure : u ∈ closure (Set.range T) := by
    rw [hT_dense.closure_eq]
    exact Set.mem_univ u
  exact hclosure_subset hu_closure

/-- Conditional finite-component positivity: once the genuine compact ordered
Fourier-Laplace transform components are dense in each degree, the descended
finite Wightman quadratic form is nonnegative on every finite component tuple. -/
theorem bvt_W_finiteComponentQuadratic_nonneg_of_component_denseRange
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (B : ℕ)
    (hdense :
      ∀ n : Fin (B + 1),
        DenseRange (section43FourierLaplaceTransformComponentMap d n.val))
    (u : Section43FiniteComponentProduct d B) :
    0 ≤ (bvt_W_finiteComponentQuadratic (d := d) OS lgc B u).re := by
  exact
    bvt_W_finiteComponentQuadratic_nonneg_of_denseRange
      (d := d) OS lgc B
      (section43FiniteTransformComponentMap d B)
      (denseRange_section43FiniteTransformComponentMap_of_components d B hdense)
      (fun src =>
        bvt_W_finiteComponentQuadratic_nonneg_on_finiteTransformComponentMap
          (d := d) OS lgc B src)
      u

/-- Conditional positivity of the reconstructed Wightman functional from the
single remaining analytic input: componentwise dense range of the compact
ordered Section 4.3 Fourier-Laplace transform map. -/
theorem bvt_W_positive_of_component_denseRange
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hdense :
      ∀ n : ℕ,
        DenseRange (section43FourierLaplaceTransformComponentMap d n))
    (F : BorchersSequence d) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  have hfinite :
      0 ≤
        (bvt_W_finiteComponentQuadratic (d := d) OS lgc F.bound
          (fun n : Fin (F.bound + 1) =>
            section43FrequencyProjection (d := d) n.val (F.funcs n.val))).re :=
    bvt_W_finiteComponentQuadratic_nonneg_of_component_denseRange
      (d := d) OS lgc F.bound
      (fun n => hdense n.val)
      (fun n : Fin (F.bound + 1) =>
        section43FrequencyProjection (d := d) n.val (F.funcs n.val))
  have happ :=
    bvt_W_finiteComponentQuadratic_apply_borchers
      (d := d) OS lgc F.bound F le_rfl
  rw [happ] at hfinite
  exact hfinite

/-- Conditional positivity from the ambient-Schwartz preimage-density form of
the remaining analytic Fourier-Laplace density theorem. -/
theorem bvt_W_positive_of_component_dense_preimage
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hdense_pre :
      ∀ n : ℕ,
        Dense
          ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
            Set.range (section43FourierLaplaceTransformComponentMap d n)))
    (F : BorchersSequence d) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re :=
  bvt_W_positive_of_component_denseRange (d := d) OS lgc
    (fun n =>
      denseRange_section43FourierLaplaceTransformComponentMap_of_dense_preimage
        d n (hdense_pre n))
    F

/-- If transform-component carriers converge to a Borchers sequence on every
pairwise Section 4.3 frequency-projection tensor term in the finite support of
`F`, then their Wightman self-inner-products converge to that of `F`.

This is the exact finite-support continuity closure needed after the descended
functional `bvt_W_descended_frequencyProjection` has been constructed. -/
theorem tendsto_wightmanInner_self_of_pairwise_frequencyProjection_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d)
    (A : ℕ → BvtTransformComponentSequence d)
    (hA_bound : ∀ K, (A K).toBorchers.bound ≤ F.bound)
    (hpair :
      ∀ n m, n ≤ F.bound → m ≤ F.bound →
        Filter.Tendsto
          (fun K =>
            section43FrequencyProjection (d := d) (n + m)
              (((A K).toBorchers.funcs n).conjTensorProduct
                ((A K).toBorchers.funcs m)))
          Filter.atTop
          (nhds
            (section43FrequencyProjection (d := d) (n + m)
              ((F.funcs n).conjTensorProduct (F.funcs m))))) :
    Filter.Tendsto
      (fun K =>
        WightmanInnerProduct d (bvt_W OS lgc)
          (A K).toBorchers (A K).toBorchers)
      Filter.atTop
      (nhds (WightmanInnerProduct d (bvt_W OS lgc) F F)) := by
  let N := F.bound + 1
  have hA_eq :
      ∀ K,
        WightmanInnerProduct d (bvt_W OS lgc)
            (A K).toBorchers (A K).toBorchers =
          WightmanInnerProductN d (bvt_W OS lgc)
            (A K).toBorchers (A K).toBorchers N N := by
    intro K
    exact WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
      (F := (A K).toBorchers) (G := (A K).toBorchers)
      (N₁ := N) (N₂ := N)
      (Nat.succ_le_succ (hA_bound K))
      (Nat.succ_le_succ (hA_bound K))
  have hF_eq :
      WightmanInnerProduct d (bvt_W OS lgc) F F =
        WightmanInnerProductN d (bvt_W OS lgc) F F N N := by
    rfl
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun K => (hA_eq K).symm) ?_
  rw [hF_eq]
  unfold WightmanInnerProductN
  refine tendsto_finset_sum _ (fun n hn => ?_)
  refine tendsto_finset_sum _ (fun m hm => ?_)
  have hn_le : n ≤ F.bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hm_le : m ≤ F.bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hD :
      Filter.Tendsto
        (fun K =>
          bvt_W_descended_frequencyProjection (d := d) OS lgc (n + m)
            (section43FrequencyProjection (d := d) (n + m)
              (((A K).toBorchers.funcs n).conjTensorProduct
                ((A K).toBorchers.funcs m))))
        Filter.atTop
        (nhds
          (bvt_W_descended_frequencyProjection (d := d) OS lgc (n + m)
            (section43FrequencyProjection (d := d) (n + m)
              ((F.funcs n).conjTensorProduct (F.funcs m))))) :=
    ((bvt_W_descended_frequencyProjection (d := d) OS lgc (n + m)).continuous.tendsto
      _).comp (hpair n m hn_le hm_le)
  simpa [bvt_W_descended_frequencyProjection_apply] using hD

/-- Positivity passes from transform-component carriers to a public Borchers
sequence whenever the carriers converge pairwise in the Section 4.3 frequency
quotient on all finite Wightman tensor terms. -/
theorem bvt_W_positive_of_pairwise_frequencyProjection_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d)
    (A : ℕ → BvtTransformComponentSequence d)
    (hA_bound : ∀ K, (A K).toBorchers.bound ≤ F.bound)
    (hpair :
      ∀ n m, n ≤ F.bound → m ≤ F.bound →
        Filter.Tendsto
          (fun K =>
            section43FrequencyProjection (d := d) (n + m)
              (((A K).toBorchers.funcs n).conjTensorProduct
                ((A K).toBorchers.funcs m)))
          Filter.atTop
          (nhds
            (section43FrequencyProjection (d := d) (n + m)
              ((F.funcs n).conjTensorProduct (F.funcs m))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  have hconv :=
    tendsto_wightmanInner_self_of_pairwise_frequencyProjection_tendsto
      (d := d) OS lgc F A hA_bound hpair
  have hre :
      Filter.Tendsto
        (fun K : ℕ =>
          (WightmanInnerProduct d (bvt_W OS lgc)
            (A K).toBorchers (A K).toBorchers).re)
        Filter.atTop
        (nhds ((WightmanInnerProduct d (bvt_W OS lgc) F F).re)) := by
    simpa [Function.comp] using
      (Complex.continuous_re.continuousAt.tendsto.comp hconv)
  have hnonneg :
      ∀ K,
        0 ≤
          (WightmanInnerProduct d (bvt_W OS lgc)
            (A K).toBorchers (A K).toBorchers).re := by
    intro K
    exact bvt_wightmanInner_self_nonneg_onTransformImage (d := d) OS lgc (A K)
  exact isClosed_Ici.mem_of_tendsto hre (Filter.Eventually.of_forall hnonneg)

end OSReconstruction
