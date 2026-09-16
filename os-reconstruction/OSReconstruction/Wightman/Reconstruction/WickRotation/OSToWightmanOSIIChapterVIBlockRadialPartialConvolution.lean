/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMeanValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIPartialConvolutionKernel
import Mathlib.MeasureTheory.Group.Integral











noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

theorem osiiStep4ComplexOfRealImag_smul
    {m : ℕ} (a : ℝ) (x y : Fin m → ℝ) :
    osiiStep4ComplexOfRealImag (a • x) (a • y) =
      a • osiiStep4ComplexOfRealImag x y := by
  ext i
  simp [osiiStep4ComplexOfRealImag, Complex.ofReal_mul]
  ring

theorem osiiStep4PartialConvolutionKernel_fullBlock_scale
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin (k * q) → ℂ) (y' : Fin (k * q) → ℝ) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho) z y' =
      (16 / rho) ^ (3 * q * k) *
        osiiStep4PartialConvolutionKernel
          (osiiStep4FullBlockRadialG q k 16)
          ((16 / rho) • z) ((16 / rho) • y') := by
  let a : ℝ := 16 / rho
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let H : (Fin (k * q) → ℝ) → ℝ := fun u =>
    osiiStep4FullBlockRadialG q k 16
        (a • z - osiiStep4ComplexOfRealImag u (a • y')) *
      osiiStep4FullBlockRadialG q k 16
        (osiiStep4ComplexOfRealImag u (a • y'))
  have hpoint (x : Fin (k * q) → ℝ) :
      osiiStep4FullBlockRadialG q k rho
          (z - osiiStep4ComplexOfRealImag x y') *
        osiiStep4FullBlockRadialG q k rho
          (osiiStep4ComplexOfRealImag x y') =
        a ^ (4 * q * k) * H (a • x) := by
    rw [osiiStep4FullBlockRadialG_scale q k hrho,
      osiiStep4FullBlockRadialG_scale q k hrho]
    have hsub :
        a • (z - osiiStep4ComplexOfRealImag x y') =
          a • z - osiiStep4ComplexOfRealImag (a • x) (a • y') := by
      ext i
      simp [osiiStep4ComplexOfRealImag, Complex.ofReal_mul]
      ring
    have hcplx :
        a • osiiStep4ComplexOfRealImag x y' =
          osiiStep4ComplexOfRealImag (a • x) (a • y') :=
      (osiiStep4ComplexOfRealImag_smul a x y').symm
    dsimp only [a] at hsub hcplx ⊢
    rw [hsub, hcplx]
    dsimp only [H, a]
    have hpow :
        (16 / rho) ^ (2 * q * k) * (16 / rho) ^ (2 * q * k) =
          (16 / rho) ^ (4 * q * k) := by
      rw [← pow_add]
      congr 1
      ring
    rw [← hpow]
    ring
  rw [osiiStep4PartialConvolutionKernel]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hscale := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Fin (k * q) → ℝ)) H a (hR := ha.le)
  rw [hscale]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    smul_eq_mul]
  rw [← mul_assoc]
  rw [show a ^ (4 * q * k) * (a ^ (k * q))⁻¹ =
      a ^ (3 * q * k) by
    have hpow : 4 * q * k = 3 * q * k + k * q := by ring
    rw [hpow, pow_add]
    field_simp]
  dsimp only [a]
  congr 1

/-- The shear `(z, z') -> (z - z', z')` as a homeomorphism. -/
def osiiStep4ComplexSubProdHomeomorph (m : ℕ) :
    ((Fin m → ℂ) × (Fin m → ℂ)) ≃ₜ
      ((Fin m → ℂ) × (Fin m → ℂ)) :=
  (Homeomorph.prodComm (Fin m → ℂ) (Fin m → ℂ)).trans
    ((Homeomorph.shearAddRight (Fin m → ℂ)).symm.trans
      (Homeomorph.prodComm (Fin m → ℂ) (Fin m → ℂ)))

@[simp]
theorem osiiStep4ComplexSubProdHomeomorph_apply
    (m : ℕ) (p : (Fin m → ℂ) × (Fin m → ℂ)) :
    osiiStep4ComplexSubProdHomeomorph m p = (p.1 - p.2, p.2) := by
  simp [osiiStep4ComplexSubProdHomeomorph, Homeomorph.trans_apply,
    sub_eq_add_neg, add_comm]

theorem osiiStep4FullBlockRadialG_pair_hasCompactSupport
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℂ) =>
        (osiiStep4FullBlockRadialG q k rho p.1 : ℂ) *
          (osiiStep4FullBlockRadialG q k rho p.2 : ℂ)) := by
  let gC : (Fin (k * q) → ℂ) → ℂ := fun z =>
    (osiiStep4FullBlockRadialG q k rho z : ℂ)
  have hgcompact : HasCompactSupport gC := by
    simpa [gC, Function.comp_def] using
      (osiiStep4FullBlockRadialG_hasCompactSupport q k hrho).comp_left
        Complex.ofReal_zero
  apply HasCompactSupport.intro (hgcompact.prod hgcompact)
  intro p hp
  by_cases hp1 : p.1 ∈ tsupport gC
  · have hp2 : p.2 ∉ tsupport gC := by
      intro hp2
      exact hp ⟨hp1, hp2⟩
    have hz2 : gC p.2 = 0 := by
      by_contra hne
      exact hp2 (subset_tsupport gC (Function.mem_support.mpr hne))
    simp [gC, hz2]
  · have hz1 : gC p.1 = 0 := by
      by_contra hne
      exact hp1 (subset_tsupport gC (Function.mem_support.mpr hne))
    simp [gC, hz1]

theorem osiiStep4FullBlockRadialG_convolution_pair_hasCompactSupport
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℂ) =>
        (osiiStep4FullBlockRadialG q k rho (p.1 - p.2) : ℂ) *
          (osiiStep4FullBlockRadialG q k rho p.2 : ℂ)) := by
  simpa [Function.comp_def] using
    (osiiStep4FullBlockRadialG_pair_hasCompactSupport q k hrho).comp_homeomorph
      (osiiStep4ComplexSubProdHomeomorph (k * q))

theorem osiiStep4FullBlockRadialG_weighted_convolution_integrable
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF : Continuous F) :
    Integrable
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℂ) =>
        F (c + p.1) *
          ((osiiStep4FullBlockRadialG q k rho (p.1 - p.2) : ℂ) *
            (osiiStep4FullBlockRadialG q k rho p.2 : ℂ)))
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        (volume : Measure (Fin (k * q) → ℂ))) := by
  have hgcont : Continuous (osiiStep4FullBlockRadialG q k rho) :=
    osiiStep4FullBlockRadialG_continuous q k hrho
  have hcont : Continuous
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℂ) =>
        F (c + p.1) *
          ((osiiStep4FullBlockRadialG q k rho (p.1 - p.2) : ℂ) *
            (osiiStep4FullBlockRadialG q k rho p.2 : ℂ))) := by
    exact
      (hF.comp (continuous_const.add continuous_fst)).mul
        ((Complex.continuous_ofReal.comp
          (hgcont.comp (continuous_fst.sub continuous_snd))).mul
        (Complex.continuous_ofReal.comp (hgcont.comp continuous_snd)))
  have hcompact : HasCompactSupport
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℂ) =>
        F (c + p.1) *
          ((osiiStep4FullBlockRadialG q k rho (p.1 - p.2) : ℂ) *
            (osiiStep4FullBlockRadialG q k rho p.2 : ℂ))) :=
    (osiiStep4FullBlockRadialG_convolution_pair_hasCompactSupport
      q k hrho).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The self-convolution still represents evaluation when the function is
holomorphic on the translated closed support with doubled block radius. -/
theorem
    osiiStep4FullBlockRadialG_convolution_weighted_meanValue_of_differentiableOn
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF_cont : Continuous F)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k (2 * rho),
      c + z ∈ U) :
    (∫ z : Fin (k * q) → ℂ,
        F (c + z) *
          (osiiStep4ComplexConvolutionDensity
            (osiiStep4FullBlockRadialG q k rho) z : ℂ)) =
      F c := by
  let g : (Fin (k * q) → ℂ) → ℝ :=
    osiiStep4FullBlockRadialG q k rho
  let P : ((Fin (k * q) → ℂ) × (Fin (k * q) → ℂ)) → ℂ := fun p =>
    F (c + p.1) * ((g (p.1 - p.2) : ℂ) * (g p.2 : ℂ))
  have hPint : Integrable P
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        (volume : Measure (Fin (k * q) → ℂ))) := by
    simpa [P, g] using
      osiiStep4FullBlockRadialG_weighted_convolution_integrable
        q k hrho F c hF_cont
  have hinner : ∀ z' : Fin (k * q) → ℂ,
      (∫ z : Fin (k * q) → ℂ, P (z, z')) =
        (g z' : ℂ) * F (c + z') := by
    intro z'
    by_cases hz' : g z' = 0
    · simp [P, hz']
    · have hz'support :
          z' ∈ osiiStep4FullBlockRadialClosedSupport q k rho := by
        have hz'open := osiiStep4FullBlockRadialG_support_subset q k hrho
          (Function.mem_support.mpr hz')
        intro i
        exact (hz'open i).le
      have htranslate :=
        (integral_add_right_eq_self
          (μ := (volume : Measure (Fin (k * q) → ℂ)))
          (fun z : Fin (k * q) → ℂ => P (z, z')) z').symm
      have hinnerSupport : ∀ w ∈ osiiStep4FullBlockRadialClosedSupport q k rho,
          (c + z') + w ∈ U := by
        intro w hw
        have hsum : z' + w ∈
            osiiStep4FullBlockRadialClosedSupport q k (2 * rho) := by
          intro i
          have hblock :
              (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
                  (z' + w) i =
                (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i +
                  (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm w i := by
            ext mu
            rfl
          rw [hblock]
          have hcle :
              osiiStep4ComplexBlockToEuclideanCLE q
                  ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i +
                    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm w i) =
                osiiStep4ComplexBlockToEuclideanCLE q
                    ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i) +
                  osiiStep4ComplexBlockToEuclideanCLE q
                    ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm w i) := by
            exact map_add _ _ _
          rw [hcle]
          calc
            ‖osiiStep4ComplexBlockToEuclideanCLE q
                  ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i) +
                osiiStep4ComplexBlockToEuclideanCLE q
                  ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm w i)‖ ≤
                ‖osiiStep4ComplexBlockToEuclideanCLE q
                  ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i)‖ +
                ‖osiiStep4ComplexBlockToEuclideanCLE q
                  ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm w i)‖ :=
              norm_add_le _ _
            _ ≤ rho / 8 + rho / 8 := add_le_add (hz'support i) (hw i)
            _ = (2 * rho) / 8 := by ring
        simpa [add_assoc] using hsupport (z' + w) hsum
      have hmean :=
        osiiStep4FullBlockRadialG_weighted_meanValue_of_differentiableOn
          q k hrho F (c + z') hF_cont U hF hinnerSupport
      calc
        (∫ z : Fin (k * q) → ℂ, P (z, z')) =
            ∫ w : Fin (k * q) → ℂ,
              F ((c + z') + w) * ((g w : ℂ) * (g z' : ℂ)) := by
          simpa [P, add_assoc, add_comm, add_left_comm] using htranslate
        _ = (∫ w : Fin (k * q) → ℂ,
              (g w : ℂ) * F ((c + z') + w)) * (g z' : ℂ) := by
          calc
            (∫ w : Fin (k * q) → ℂ,
                F ((c + z') + w) * ((g w : ℂ) * (g z' : ℂ))) =
                ∫ w : Fin (k * q) → ℂ,
                  ((g w : ℂ) * F ((c + z') + w)) * (g z' : ℂ) := by
              apply integral_congr_ae
              filter_upwards with w
              ring
            _ = (∫ w : Fin (k * q) → ℂ,
                  (g w : ℂ) * F ((c + z') + w)) * (g z' : ℂ) := by
              exact integral_mul_const (g z' : ℂ)
                (fun w : Fin (k * q) → ℂ =>
                  (g w : ℂ) * F ((c + z') + w))
        _ = F (c + z') * (g z' : ℂ) := by rw [hmean]
        _ = (g z' : ℂ) * F (c + z') := mul_comm _ _
  have houterSupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k rho,
      c + z ∈ U := by
    intro z hz
    apply hsupport z
    intro i
    exact (hz i).trans (by nlinarith [hrho])
  calc
    (∫ z : Fin (k * q) → ℂ,
        F (c + z) *
          (osiiStep4ComplexConvolutionDensity
            (osiiStep4FullBlockRadialG q k rho) z : ℂ)) =
        ∫ z : Fin (k * q) → ℂ,
          ∫ z' : Fin (k * q) → ℂ, P (z, z') := by
      apply integral_congr_ae
      filter_upwards with z
      rw [show osiiStep4FullBlockRadialG q k rho = g from rfl]
      calc
        F (c + z) * (osiiStep4ComplexConvolutionDensity g z : ℂ) =
            F (c + z) *
              (∫ z' : Fin (k * q) → ℂ,
                (g (z - z') * g z' : ℂ)) := by
          rw [osiiStep4ComplexConvolutionDensity]
          congr 1
          simpa using
            (integral_complex_ofReal
              (μ := (volume : Measure (Fin (k * q) → ℂ)))
              (f := fun z' : Fin (k * q) → ℂ =>
                g (z - z') * g z')).symm
        _ = ∫ z' : Fin (k * q) → ℂ,
              F (c + z) * (g (z - z') * g z' : ℂ) := by
          exact (integral_const_mul (F (c + z))
            (fun z' : Fin (k * q) → ℂ =>
              (g (z - z') * g z' : ℂ))).symm
        _ = ∫ z' : Fin (k * q) → ℂ, P (z, z') := by
          apply integral_congr_ae
          filter_upwards with z'
          simp [P]
    _ = ∫ z' : Fin (k * q) → ℂ,
          ∫ z : Fin (k * q) → ℂ, P (z, z') := by
      exact integral_integral_swap hPint
    _ = ∫ z' : Fin (k * q) → ℂ,
          (g z' : ℂ) * F (c + z') := by
      apply integral_congr_ae
      filter_upwards with z'
      exact hinner z'
    _ = F c := by
      simpa [g] using
        osiiStep4FullBlockRadialG_weighted_meanValue_of_differentiableOn
          q k hrho F c hF_cont U hF houterSupport

/-- Integrability of the exact OS-II partial-kernel transform follows by
disintegrating the jointly integrable complex convolution integrand. -/
theorem osiiStep4FullBlockRadialG_partialKernel_weighted_integrable
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF : Continuous F) :
    Integrable
      (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℝ) =>
        F (c + p.1) *
          (osiiStep4PartialConvolutionKernel
            (osiiStep4FullBlockRadialG q k rho) p.1 p.2 : ℂ))
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        (volume : Measure (Fin (k * q) → ℝ))) := by
  let g : (Fin (k * q) → ℂ) → ℝ :=
    osiiStep4FullBlockRadialG q k rho
  let P : ((Fin (k * q) → ℂ) × (Fin (k * q) → ℂ)) → ℂ := fun p =>
    F (c + p.1) * ((g (p.1 - p.2) : ℂ) * (g p.2 : ℂ))
  have hPint : Integrable P
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        (volume : Measure (Fin (k * q) → ℂ))) := by
    simpa [P, g] using
      osiiStep4FullBlockRadialG_weighted_convolution_integrable
        q k hrho F c hF
  let e := osiiStep4ComplexRealImagMeasurableEquiv (k * q)
  have he : MeasurePreserving e
      (volume : Measure (Fin (k * q) → ℂ))
      ((volume : Measure (Fin (k * q) → ℝ)).prod
        (volume : Measure (Fin (k * q) → ℝ))) :=
    osiiStep4ComplexRealImagMeasurableEquiv_measurePreserving (k * q)
  let Q : ((Fin (k * q) → ℂ) ×
      ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ))) → ℂ := fun p =>
    P (p.1, e.symm p.2)
  have hsplit : MeasurePreserving
      (Prod.map id e.symm)
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        ((volume : Measure (Fin (k * q) → ℝ)).prod
          (volume : Measure (Fin (k * q) → ℝ))))
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        (volume : Measure (Fin (k * q) → ℂ))) :=
    (MeasurePreserving.id
      (volume : Measure (Fin (k * q) → ℂ))).prod he.symm
  have hQint : Integrable Q
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        ((volume : Measure (Fin (k * q) → ℝ)).prod
          (volume : Measure (Fin (k * q) → ℝ)))) := by
    have hcomp := hsplit.integrable_comp_of_integrable hPint
    simpa [Q, Function.comp_def, Prod.map] using hcomp
  let R : (((Fin (k * q) → ℂ) × (Fin (k * q) → ℝ)) ×
      (Fin (k * q) → ℝ)) → ℂ := fun p =>
    Q (p.1.1, (p.2, p.1.2))
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure (Fin (k * q) → ℝ)).prod
        (volume : Measure (Fin (k * q) → ℝ)))
      ((volume : Measure (Fin (k * q) → ℝ)).prod
        (volume : Measure (Fin (k * q) → ℝ))) :=
    Measure.measurePreserving_swap
  have hreorder : MeasurePreserving
      (fun p : (((Fin (k * q) → ℂ) × (Fin (k * q) → ℝ)) ×
          (Fin (k * q) → ℝ)) => (p.1.1, (p.2, p.1.2)))
      (((volume : Measure (Fin (k * q) → ℂ)).prod
          (volume : Measure (Fin (k * q) → ℝ))).prod
        (volume : Measure (Fin (k * q) → ℝ)))
      ((volume : Measure (Fin (k * q) → ℂ)).prod
        ((volume : Measure (Fin (k * q) → ℝ)).prod
          (volume : Measure (Fin (k * q) → ℝ)))) := by
    have hassoc := measurePreserving_prodAssoc
      (volume : Measure (Fin (k * q) → ℂ))
      (volume : Measure (Fin (k * q) → ℝ))
      (volume : Measure (Fin (k * q) → ℝ))
    have hprod :=
      (MeasurePreserving.id
        (volume : Measure (Fin (k * q) → ℂ))).prod hswap
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc, Prod.map] using
      hprod.comp hassoc
  have hRint : Integrable R
      (((volume : Measure (Fin (k * q) → ℂ)).prod
          (volume : Measure (Fin (k * q) → ℝ))).prod
        (volume : Measure (Fin (k * q) → ℝ))) := by
    have hcomp := hreorder.integrable_comp_of_integrable hQint
    simpa [R, Function.comp_def] using hcomp
  have hintegrated := hRint.integral_prod_left
  have hpoint : (fun p : (Fin (k * q) → ℂ) × (Fin (k * q) → ℝ) =>
      F (c + p.1) *
        (osiiStep4PartialConvolutionKernel g p.1 p.2 : ℂ)) =
      (fun p => ∫ x' : Fin (k * q) → ℝ, R (p, x')) := by
    funext p
    rw [osiiStep4PartialConvolutionKernel]
    rw [← integral_complex_ofReal]
    calc
      F (c + p.1) *
          (∫ x' : Fin (k * q) → ℝ,
            Complex.ofReal
              (g (p.1 - osiiStep4ComplexOfRealImag x' p.2) *
                g (osiiStep4ComplexOfRealImag x' p.2))) =
          ∫ x' : Fin (k * q) → ℝ,
            F (c + p.1) *
              Complex.ofReal
                (g (p.1 - osiiStep4ComplexOfRealImag x' p.2) *
                  g (osiiStep4ComplexOfRealImag x' p.2)) := by
        exact (integral_const_mul (F (c + p.1)) _).symm
      _ = ∫ x' : Fin (k * q) → ℝ, R (p, x') := by
        apply integral_congr_ae
        filter_upwards with x'
        simp [R, Q, P, e]
  rw [show osiiStep4FullBlockRadialG q k rho = g from rfl]
  rw [hpoint]
  exact hintegrated

/-- Paper-faithful OS-II `(6.6)` under holomorphy only on the translated
doubled support sampled by the self-convolution. -/
theorem
    osiiStep4FullBlockRadialG_partialConvolution_meanValue_of_differentiableOn
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF_cont : Continuous F)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k (2 * rho),
      c + z ∈ U) :
    F c =
      ∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
        osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c y y' := by
  exact osiiStep4_partialConvolution_meanValue
    (osiiStep4FullBlockRadialG q k rho) F c
    (osiiStep4FullBlockRadialG_convolution_integrable q k hrho)
    (osiiStep4FullBlockRadialG_partialKernel_weighted_integrable
      q k hrho F c hF_cont)
    (osiiStep4FullBlockRadialG_convolution_weighted_meanValue_of_differentiableOn
      q k hrho F c hF_cont U hF hsupport)

end OSReconstruction
