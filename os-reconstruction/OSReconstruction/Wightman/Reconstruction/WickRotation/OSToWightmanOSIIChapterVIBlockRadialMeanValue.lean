/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.MeanValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialRegularizer












noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

/-- Common complex-phase rotation of one coordinate block. -/
def osiiStep4ComplexBlockPhaseRotation
    (q : ℕ) (a : Circle) (z : Fin q → ℂ) : Fin q → ℂ :=
  fun i => (a : ℂ) * z i

/-- The common phase rotation as a measurable equivalence. -/
def osiiStep4ComplexBlockPhaseRotationMeasurableEquiv
    (q : ℕ) (a : Circle) : (Fin q → ℂ) ≃ᵐ (Fin q → ℂ) :=
  MeasurableEquiv.piCongrRight
    (fun _ : Fin q => (rotation a).toMeasurableEquiv)

@[simp]
theorem osiiStep4ComplexBlockPhaseRotationMeasurableEquiv_apply
    (q : ℕ) (a : Circle) (z : Fin q → ℂ) :
    osiiStep4ComplexBlockPhaseRotationMeasurableEquiv q a z =
      osiiStep4ComplexBlockPhaseRotation q a z := by
  rfl

@[simp]
theorem osiiStep4ComplexBlockPhaseRotation_apply
    (q : ℕ) (a : Circle) (z : Fin q → ℂ) (i : Fin q) :
    osiiStep4ComplexBlockPhaseRotation q a z i = (a : ℂ) * z i :=
  rfl

theorem osiiStep4ComplexBlockPhaseRotation_measurePreserving
    (q : ℕ) (a : Circle) :
    MeasurePreserving (osiiStep4ComplexBlockPhaseRotation q a)
      (volume : Measure (Fin q → ℂ))
      (volume : Measure (Fin q → ℂ)) := by
  simpa [osiiStep4ComplexBlockPhaseRotation,
    osiiStep4ComplexBlockPhaseRotationMeasurableEquiv, rotation_apply] using
    (volume_preserving_pi
      (fun _ : Fin q => (rotation a).measurePreserving))

theorem osiiStep4ComplexBlockRadialG_phaseRotation
    (q : ℕ) (rho : ℝ) (a : Circle) (z : Fin q → ℂ) :
    osiiStep4ComplexBlockRadialG q rho
        (osiiStep4ComplexBlockPhaseRotation q a z) =
      osiiStep4ComplexBlockRadialG q rho z := by
  simpa [osiiStep4ComplexBlockPhaseRotation, Pi.smul_apply] using
    osiiStep4ComplexBlockRadialG_smul_of_norm_one
      q rho (a : ℂ) (Circle.norm_coe a) z

theorem osiiStep4ComplexBlockRadialG_weighted_phaseRotation
    (q : ℕ) {rho : ℝ} (_hrho : 0 < rho)
    (F : (Fin q → ℂ) → ℂ) (c : Fin q → ℂ) (a : Circle) :
    (∫ z : Fin q → ℂ,
        (osiiStep4ComplexBlockRadialG q rho z : ℂ) *
          F (c + osiiStep4ComplexBlockPhaseRotation q a z)) =
      ∫ z : Fin q → ℂ,
        (osiiStep4ComplexBlockRadialG q rho z : ℂ) * F (c + z) := by
  let H : (Fin q → ℂ) → ℂ := fun z =>
    (osiiStep4ComplexBlockRadialG q rho z : ℂ) * F (c + z)
  have hchange :=
    (osiiStep4ComplexBlockPhaseRotation_measurePreserving q a).integral_comp'
      (f := osiiStep4ComplexBlockPhaseRotationMeasurableEquiv q a) H
  simpa [H, osiiStep4ComplexBlockRadialG_phaseRotation] using hchange

/-- The one-variable mean value along the complex line through `z`, requiring
holomorphy only on a set containing the closed unit disk in that line. -/
theorem osiiStep4_intervalIntegral_phaseLine_eq_center_of_differentiableOn
    {q : ℕ} (F : (Fin q → ℂ) → ℂ) (c z : Fin q → ℂ)
    (U : Set (Fin q → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hline : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, c + w • z ∈ U) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        F (c + osiiStep4ComplexBlockPhaseRotation q (Circle.exp theta) z)) =
      (2 * Real.pi : ℝ) • F c := by
  let g : ℂ → (Fin q → ℂ) := fun w => c + w • z
  let f : ℂ → ℂ := fun w => F (g w)
  have hg : Differentiable ℂ g := by
    dsimp [g]
    fun_prop
  have hfOn : DifferentiableOn ℂ f (g ⁻¹' U) := by
    exact hF.comp hg.differentiableOn (Set.mapsTo_preimage g U)
  have hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ g ⁻¹' U := by
    intro w hw
    exact hline w hw
  have hf : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) :=
    hfOn.diffContOnCl_ball hclosed
  have hmean : Real.circleAverage f 0 1 = f 0 :=
    (by simpa using hf :
      DiffContOnCl ℂ f (Metric.ball (0 : ℂ) |(1 : ℝ)|)).circleAverage
  let A : ℂ :=
    ∫ theta in (0 : ℝ)..2 * Real.pi,
      F (c + osiiStep4ComplexBlockPhaseRotation q (Circle.exp theta) z)
  have hscaled : (2 * Real.pi : ℝ)⁻¹ • A = F c := by
    calc
      (2 * Real.pi : ℝ)⁻¹ • A = Real.circleAverage f 0 1 := by
        rw [Real.circleAverage_def]
        congr 1
        apply intervalIntegral.integral_congr
        intro theta _htheta
        apply congrArg F
        funext i
        simp [g, osiiStep4ComplexBlockPhaseRotation,
          circleMap, Pi.smul_apply]
      _ = f 0 := hmean
      _ = F c := by simp [f, g]
  calc
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        F (c + osiiStep4ComplexBlockPhaseRotation q (Circle.exp theta) z)) =
        A := rfl
    _ = (1 : ℝ) • A := (one_smul ℝ A).symm
    _ = ((2 * Real.pi) * (2 * Real.pi)⁻¹ : ℝ) • A := by
      rw [mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
    _ = (2 * Real.pi : ℝ) • ((2 * Real.pi : ℝ)⁻¹ • A) := by
      exact (smul_smul (2 * Real.pi : ℝ) (2 * Real.pi : ℝ)⁻¹ A).symm
    _ = (2 * Real.pi : ℝ) • F c := by rw [hscaled]

theorem osiiStep4ComplexBlockRadialG_phase_integrable
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin q → ℂ) → ℂ) (c : Fin q → ℂ)
    (hF : Continuous F) :
    Integrable
      (fun p : ℝ × (Fin q → ℂ) =>
        (osiiStep4ComplexBlockRadialG q rho p.2 : ℂ) *
          F (c +
            osiiStep4ComplexBlockPhaseRotation q (Circle.exp p.1) p.2))
      (((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
        (volume : Measure (Fin q → ℂ))) := by
  let G : (Fin q → ℂ) → ℝ := osiiStep4ComplexBlockRadialG q rho
  let Q : ℝ × (Fin q → ℂ) → ℂ := fun p =>
    (G p.2 : ℂ) *
      F (c + osiiStep4ComplexBlockPhaseRotation q (Circle.exp p.1) p.2)
  have hQ : Continuous Q := by
    have hphase : Continuous
        (fun p : ℝ × (Fin q → ℂ) =>
          osiiStep4ComplexBlockPhaseRotation q (Circle.exp p.1) p.2) := by
      apply continuous_pi
      intro i
      exact
        (continuous_subtype_val.comp
          (Circle.exp.continuous.comp continuous_fst)).mul
            ((continuous_apply i).comp continuous_snd)
    exact
      (Complex.continuous_ofReal.comp
        ((osiiStep4ComplexBlockRadialG_contDiff q hrho).continuous.comp
          continuous_snd)).mul
        (hF.comp (continuous_const.add hphase))
  let K : Set (ℝ × (Fin q → ℂ)) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
      tsupport (osiiStep4ComplexBlockRadialG q rho)
  have hK : IsCompact K :=
    isCompact_Icc.prod
      (osiiStep4ComplexBlockRadialG_hasCompactSupport q hrho)
  have hKint : IntegrableOn Q K :=
    hQ.continuousOn.integrableOn_compact hK
  have hQon : IntegrableOn Q
      (Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ
        (Set.univ : Set (Fin q → ℂ))) := by
    apply hKint.of_forall_diff_eq_zero
      (measurableSet_Ioc.prod MeasurableSet.univ)
    intro p hp
    have hthetaIoc : p.1 ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := hp.1.1
    have htheta : p.1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
      ⟨hthetaIoc.1.le, hthetaIoc.2⟩
    have hznot : p.2 ∉ tsupport (osiiStep4ComplexBlockRadialG q rho) := by
      intro hz
      exact hp.2 ⟨htheta, hz⟩
    have hGzero : osiiStep4ComplexBlockRadialG q rho p.2 = 0 := by
      by_contra hne
      exact hznot (subset_tsupport _ (Function.mem_support.mpr hne))
    simp [Q, G, hGzero]
  change Integrable Q
    (((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
      (volume : Measure (Fin q → ℂ)))
  rw [← Measure.restrict_univ (μ := (volume : Measure (Fin q → ℂ))),
    Measure.prod_restrict]
  exact hQon

/-- A block-radial probability density represents evaluation at the center
when the function is holomorphic on a neighborhood of the closed support
ball.  Global continuity is sufficient for the compact-support integrability
bookkeeping and can later be supplied by a cutoff extension. -/
theorem osiiStep4ComplexBlockRadialG_weighted_meanValue_of_differentiableOn
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin q → ℂ) → ℂ) (c : Fin q → ℂ)
    (hF_cont : Continuous F)
    (U : Set (Fin q → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z : Fin q → ℂ,
      ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ ≤ rho / 8 →
        c + z ∈ U) :
    (∫ z : Fin q → ℂ,
        (osiiStep4ComplexBlockRadialG q rho z : ℂ) * F (c + z)) =
      F c := by
  let G : (Fin q → ℂ) → ℝ := osiiStep4ComplexBlockRadialG q rho
  let Q : ℝ × (Fin q → ℂ) → ℂ := fun p =>
    (G p.2 : ℂ) *
      F (c + osiiStep4ComplexBlockPhaseRotation q (Circle.exp p.1) p.2)
  let I : ℂ := ∫ z : Fin q → ℂ, (G z : ℂ) * F (c + z)
  have hQint : Integrable Q
      (((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
        (volume : Measure (Fin q → ℂ))) := by
    simpa [Q, G] using
      osiiStep4ComplexBlockRadialG_phase_integrable q hrho F c hF_cont
  have hswap := integral_integral_swap
    (μ := (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))
    (ν := (volume : Measure (Fin q → ℂ)))
    (f := fun theta z => Q (theta, z)) (by
      simpa [Function.uncurry] using hQint)
  have hmeasure :
      (volume : Measure ℝ).real (Set.Ioc 0 (2 * Real.pi)) =
        2 * Real.pi := by
    simp [measureReal_def, Real.pi_pos.le]
  have hscaled : (2 * Real.pi : ℝ) • I = (2 * Real.pi : ℝ) • F c := by
    calc
      (2 * Real.pi : ℝ) • I =
          ∫ _theta in Set.Ioc (0 : ℝ) (2 * Real.pi), I := by
        rw [setIntegral_const, hmeasure]
        rfl
      _ = ∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
          ∫ z : Fin q → ℂ, Q (theta, z) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro theta _htheta
        exact
          (osiiStep4ComplexBlockRadialG_weighted_phaseRotation
            q hrho F c (Circle.exp theta)).symm
      _ = ∫ z : Fin q → ℂ,
          ∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi), Q (theta, z) := hswap
      _ = ∫ z : Fin q → ℂ,
          (G z : ℂ) * ((2 * Real.pi : ℝ) • F c) := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : G z = 0
        · simp [Q, hz]
        · have hzsupport : z ∈ osiiStep4ComplexBlockBall q rho := by
            apply osiiStep4ComplexBlockRadialG_support_subset q hrho
            exact Function.mem_support.mpr hz
          have hline : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
              c + w • z ∈ U := by
            intro w hw
            apply hsupport
            rw [Metric.mem_closedBall, dist_zero_right] at hw
            have heq :
                osiiStep4ComplexBlockToEuclideanCLE q (w • z) =
                  w • osiiStep4ComplexBlockToEuclideanCLE q z := by
              rfl
            rw [heq, norm_smul]
            exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans
              (le_of_lt hzsupport)
          have hlineMean :
              (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
                F (c + osiiStep4ComplexBlockPhaseRotation q
                  (Circle.exp theta) z)) =
                (2 * Real.pi : ℝ) • F c := by
            simpa [intervalIntegral.integral_of_le Real.two_pi_pos.le] using
              osiiStep4_intervalIntegral_phaseLine_eq_center_of_differentiableOn
                F c z U hF hline
          calc
            (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi), Q (theta, z)) =
                ∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
                  (G z : ℂ) *
                    F (c + osiiStep4ComplexBlockPhaseRotation q
                      (Circle.exp theta) z) := rfl
            _ = (G z : ℂ) *
                (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
                  F (c + osiiStep4ComplexBlockPhaseRotation q
                    (Circle.exp theta) z)) := by
              exact integral_const_mul (G z : ℂ) _
            _ = (G z : ℂ) * ((2 * Real.pi : ℝ) • F c) := by
              rw [hlineMean]
      _ = (2 * Real.pi : ℝ) • F c := by
        calc
          (∫ z : Fin q → ℂ,
              (G z : ℂ) * ((2 * Real.pi : ℝ) • F c)) =
              (∫ z : Fin q → ℂ, (G z : ℂ)) *
                ((2 * Real.pi : ℝ) • F c) := by
            exact integral_mul_const ((2 * Real.pi : ℝ) • F c)
              (fun z : Fin q → ℂ => (G z : ℂ))
          _ = (2 * Real.pi : ℝ) • F c := by
            rw [integral_complex_ofReal,
              osiiStep4ComplexBlockRadialG_integral_one q hrho]
            simp
  exact smul_right_injective ℂ
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hscaled



/-- The product block-radial mean value under holomorphy only on a set
containing the closed product support. -/
theorem osiiStep4_nestedBlockRadialG_weighted_meanValue_zero_of_differentiableOn
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin k → Fin q → ℂ) → ℂ)
    (hF_cont : Continuous F)
    (U : Set (Fin k → Fin q → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z : Fin k → Fin q → ℂ,
      (∀ i : Fin k,
        ‖osiiStep4ComplexBlockToEuclideanCLE q (z i)‖ ≤ rho / 8) →
      z ∈ U) :
    (∫ z : Fin k → Fin q → ℂ,
        ((∏ i : Fin k, osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) *
          F z) =
      F 0 := by
  induction k with
  | zero =>
      have hvol :
          (volume : Measure (Fin 0 → Fin q → ℂ)) = Measure.dirac 0 := by
        simpa using
          (Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => Fin q → ℂ) (x := 0))
      rw [hvol, integral_dirac]
      simp
  | succ n ih =>
      let eFlat := osiiStep4ComplexBlockFlattenMeasurableEquiv (n + 1) q
      let FFlat : (Fin ((n + 1) * q) → ℂ) → ℂ := fun z => F (eFlat.symm z)
      have hFFlat_cont : Continuous FFlat := by
        exact hF_cont.comp
          (osiiStep4ComplexBlockFlattenMeasurableEquiv_symm_differentiable
            (n + 1) q).continuous
      have hFlatInt : Integrable
          (fun z : Fin ((n + 1) * q) → ℂ =>
            (osiiStep4FullBlockRadialG q (n + 1) rho z : ℂ) * FFlat z)
          (volume : Measure (Fin ((n + 1) * q) → ℂ)) :=
        osiiStep4FullBlockRadialG_weighted_integrable
          q (n + 1) hrho FFlat hFFlat_cont
      have heFlat : MeasurePreserving eFlat
          (volume : Measure (Fin (n + 1) → Fin q → ℂ))
          (volume : Measure (Fin ((n + 1) * q) → ℂ)) :=
        osiiStep4ComplexBlockFlattenMeasurableEquiv_measurePreserving
          (n + 1) q
      have hNestedInt : Integrable
          (fun z : Fin (n + 1) → Fin q → ℂ =>
            ((∏ i : Fin (n + 1),
              osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) * F z)
          (volume : Measure (Fin (n + 1) → Fin q → ℂ)) := by
        have hcomp := heFlat.integrable_comp_of_integrable hFlatInt
        simpa [Function.comp_def, eFlat, FFlat,
          osiiStep4FullBlockRadialG] using hcomp
      let e : (Fin (n + 1) → Fin q → ℂ) ≃ᵐ
          ((Fin q → ℂ) × (Fin n → Fin q → ℂ)) :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Fin q → ℂ) 0
      have he : MeasurePreserving e
          (volume : Measure (Fin (n + 1) → Fin q → ℂ))
          ((volume : Measure (Fin q → ℂ)).prod
            (volume : Measure (Fin n → Fin q → ℂ))) := by
        simpa [e] using
          (volume_preserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => Fin q → ℂ) 0)
      have he_symm (p : (Fin q → ℂ) × (Fin n → Fin q → ℂ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl
      let A : (Fin n → Fin q → ℂ) → ℝ := fun y =>
        ∏ i : Fin n, osiiStep4ComplexBlockRadialG q rho (y i)
      let P : (Fin q → ℂ) × (Fin n → Fin q → ℂ) → ℂ := fun p =>
        ((osiiStep4ComplexBlockRadialG q rho p.1 * A p.2 : ℝ) : ℂ) *
          F (Fin.cons p.1 p.2)
      have hPint : Integrable P
          ((volume : Measure (Fin q → ℂ)).prod
            (volume : Measure (Fin n → Fin q → ℂ))) := by
        have hcomp : Integrable
            ((fun z : Fin (n + 1) → Fin q → ℂ =>
              ((∏ i : Fin (n + 1),
                osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) * F z) ∘
              e.symm)
            ((volume : Measure (Fin q → ℂ)).prod
              (volume : Measure (Fin n → Fin q → ℂ))) :=
          he.symm.integrable_comp_of_integrable hNestedInt
        simpa [P, A, Function.comp_def, he_symm, Fin.prod_univ_succ] using hcomp
      have hinner : ∀ y : Fin n → Fin q → ℂ,
          (∫ w : Fin q → ℂ, P (w, y)) =
            (A y : ℂ) * F (Fin.cons 0 y) := by
        intro y
        by_cases hAy : A y = 0
        · simp [P, hAy]
        · have hy : ∀ i : Fin n,
              ‖osiiStep4ComplexBlockToEuclideanCLE q (y i)‖ ≤ rho / 8 := by
            intro i
            have hGi : osiiStep4ComplexBlockRadialG q rho (y i) ≠ 0 := by
              intro hzero
              apply hAy
              exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
            exact (osiiStep4ComplexBlockRadialG_support_subset q hrho
              (Function.mem_support.mpr hGi)).le
          let f : (Fin q → ℂ) → ℂ := fun w => F (Fin.cons w y)
          let Ublock : Set (Fin q → ℂ) := {w | Fin.cons w y ∈ U}
          have hcons_cont : Continuous (fun w : Fin q → ℂ =>
              (Fin.cons w y : Fin (n + 1) → Fin q → ℂ)) := by
            apply continuous_pi
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using (continuous_id : Continuous (fun w : Fin q → ℂ => w))
            · simpa using
                (continuous_const : Continuous (fun _w : Fin q → ℂ => y j))
          have hf_cont : Continuous f := hF_cont.comp hcons_cont
          have hcons_diff : Differentiable ℂ
              (fun w : Fin q → ℂ =>
                (Fin.cons w y : Fin (n + 1) → Fin q → ℂ)) := by
            rw [differentiable_pi]
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using
                (differentiable_id : Differentiable ℂ (fun w : Fin q → ℂ => w))
            · simpa using
                (differentiable_const (c := y j) :
                  Differentiable ℂ (fun _w : Fin q → ℂ => y j))
          have hf_diff : DifferentiableOn ℂ f Ublock := by
            exact hF.comp hcons_diff.differentiableOn
              (by intro w hw; exact hw)
          have hblock_support : ∀ w : Fin q → ℂ,
              ‖osiiStep4ComplexBlockToEuclideanCLE q w‖ ≤ rho / 8 →
                (0 : Fin q → ℂ) + w ∈ Ublock := by
            intro w hw
            change Fin.cons (0 + w) y ∈ U
            apply hsupport
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hw
            · simpa using hy j
          have hmean :=
            osiiStep4ComplexBlockRadialG_weighted_meanValue_of_differentiableOn
              q hrho f 0 hf_cont Ublock hf_diff hblock_support
          calc
            (∫ w : Fin q → ℂ, P (w, y)) =
                ∫ w : Fin q → ℂ,
                  (A y : ℂ) *
                    ((osiiStep4ComplexBlockRadialG q rho w : ℂ) * f w) := by
              apply integral_congr_ae
              filter_upwards with w
              simp [P, A, f, mul_assoc, mul_left_comm, mul_comm]
            _ = (A y : ℂ) *
                (∫ w : Fin q → ℂ,
                  (osiiStep4ComplexBlockRadialG q rho w : ℂ) * f w) := by
              exact integral_const_mul (A y : ℂ) _
            _ = (A y : ℂ) * F (Fin.cons 0 y) := by
              simpa [f] using congrArg (fun u => (A y : ℂ) * u) hmean
      let H : (Fin n → Fin q → ℂ) → ℂ := fun y => F (Fin.cons 0 y)
      let Utail : Set (Fin n → Fin q → ℂ) := {y | Fin.cons 0 y ∈ U}
      have htail_cont : Continuous (fun y : Fin n → Fin q → ℂ =>
          (Fin.cons (0 : Fin q → ℂ) y : Fin (n + 1) → Fin q → ℂ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using
            (continuous_const : Continuous
              (fun _y : Fin n → Fin q → ℂ => (0 : Fin q → ℂ)))
        · simpa using
            (continuous_apply j : Continuous
              (fun y : Fin n → Fin q → ℂ => y j))
      have hH_cont : Continuous H := hF_cont.comp htail_cont
      have htail_diff : Differentiable ℂ
          (fun y : Fin n → Fin q → ℂ =>
            (Fin.cons (0 : Fin q → ℂ) y : Fin (n + 1) → Fin q → ℂ)) := by
        rw [differentiable_pi]
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using
            (differentiable_const (c := (0 : Fin q → ℂ)) :
              Differentiable ℂ
                (fun _y : Fin n → Fin q → ℂ => (0 : Fin q → ℂ)))
        · simpa using
            (differentiable_apply j : Differentiable ℂ
              (fun y : Fin n → Fin q → ℂ => y j))
      have hH_diff : DifferentiableOn ℂ H Utail := by
        exact hF.comp htail_diff.differentiableOn
          (by intro y hy; exact hy)
      have htail_support : ∀ y : Fin n → Fin q → ℂ,
          (∀ i : Fin n,
            ‖osiiStep4ComplexBlockToEuclideanCLE q (y i)‖ ≤ rho / 8) →
          y ∈ Utail := by
        intro y hy
        apply hsupport
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using (show (0 : ℝ) ≤ rho / 8 by positivity)
        · simpa using hy j
      calc
        (∫ z : Fin (n + 1) → Fin q → ℂ,
            ((∏ i : Fin (n + 1),
              osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) * F z) =
            ∫ p : (Fin q → ℂ) × (Fin n → Fin q → ℂ), P p := by
          have hchange := he.symm.integral_comp'
            (f := e.symm)
            (fun z : Fin (n + 1) → Fin q → ℂ =>
              ((∏ i : Fin (n + 1),
                osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) * F z)
          simpa [P, A, Function.comp_def, he_symm,
            Fin.prod_univ_succ] using hchange.symm
        _ = ∫ y : Fin n → Fin q → ℂ,
              ∫ w : Fin q → ℂ, P (w, y) := by
          exact integral_prod_symm P hPint
        _ = ∫ y : Fin n → Fin q → ℂ,
              (A y : ℂ) * F (Fin.cons 0 y) := by
          apply integral_congr_ae
          filter_upwards with y
          exact hinner y
        _ = H 0 := by
          simpa [A, H] using
            ih H hH_cont Utail hH_diff htail_support
        _ = F 0 := by
          apply congrArg F
          ext i
          cases i using Fin.cases <;> rfl

/-- The closed block polydisc containing the support of the full block-radial
regularizer.  It is the precise local holomorphy region needed by mean value. -/
def osiiStep4FullBlockRadialClosedSupport
    (q k : ℕ) (rho : ℝ) : Set (Fin (k * q) → ℂ) :=
  {z | ∀ i : Fin k,
    ‖osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)‖ ≤
        rho / 8}

/-- The full block-radial mean value needs holomorphy only on a neighborhood
of the translated closed regularizer support. -/
theorem osiiStep4FullBlockRadialG_weighted_meanValue_of_differentiableOn
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF_cont : Continuous F)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k rho,
      c + z ∈ U) :
    (∫ z : Fin (k * q) → ℂ,
        (osiiStep4FullBlockRadialG q k rho z : ℂ) * F (c + z)) =
      F c := by
  let e := osiiStep4ComplexBlockFlattenMeasurableEquiv k q
  let g : (Fin k → Fin q → ℂ) → (Fin (k * q) → ℂ) := fun z => c + e z
  let H : (Fin k → Fin q → ℂ) → ℂ := fun z => F (g z)
  let Unested : Set (Fin k → Fin q → ℂ) := g ⁻¹' U
  have hg_cont : Continuous g := by
    exact continuous_const.add
      (osiiStep4ComplexBlockFlattenMeasurableEquiv_differentiable k q).continuous
  have hH_cont : Continuous H := hF_cont.comp hg_cont
  have hg_diff : Differentiable ℂ g := by
    exact
      (differentiable_const (c := c) : Differentiable ℂ
        (fun _ : Fin k → Fin q → ℂ => c)).add
      (osiiStep4ComplexBlockFlattenMeasurableEquiv_differentiable k q)
  have hH_diff : DifferentiableOn ℂ H Unested := by
    exact hF.comp hg_diff.differentiableOn (Set.mapsTo_preimage g U)
  have hNestedSupport : ∀ z : Fin k → Fin q → ℂ,
      (∀ i : Fin k,
        ‖osiiStep4ComplexBlockToEuclideanCLE q (z i)‖ ≤ rho / 8) →
      z ∈ Unested := by
    intro z hz
    exact hsupport (e z) (by
      intro i
      simpa [osiiStep4FullBlockRadialClosedSupport, e] using hz i)
  have he : MeasurePreserving e
      (volume : Measure (Fin k → Fin q → ℂ))
      (volume : Measure (Fin (k * q) → ℂ)) :=
    osiiStep4ComplexBlockFlattenMeasurableEquiv_measurePreserving k q
  calc
    (∫ z : Fin (k * q) → ℂ,
        (osiiStep4FullBlockRadialG q k rho z : ℂ) * F (c + z)) =
        ∫ z : Fin k → Fin q → ℂ,
          ((∏ i : Fin k,
            osiiStep4ComplexBlockRadialG q rho (z i) : ℝ) : ℂ) * H z := by
      have hchange := he.integral_comp'
        (fun z : Fin (k * q) → ℂ =>
          (osiiStep4FullBlockRadialG q k rho z : ℂ) * F (c + z))
      simpa [H, g, e, osiiStep4FullBlockRadialG] using hchange.symm
    _ = H 0 :=
      osiiStep4_nestedBlockRadialG_weighted_meanValue_zero_of_differentiableOn
        q k hrho H hH_cont Unested hH_diff hNestedSupport
    _ = F c := by
      apply congrArg F
      ext a
      simp [g, e]

end OSReconstruction
