import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OS24KernelComparison

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- The Borchers-ordered OS phase integral factors into the two one-sided
Fourier-Laplace integrals and the normalized OS I `(4.24)` damping factor. -/
theorem section43OSBorchersPhaseIntegral_factorizes_succRight
    (d n m : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
    let qL :=
      section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ
    let qR := section43RightTailBlock d n (m + 1) qξ
    let lamξ : ℝ :=
      ∑ i : Fin ((n + (m + 1)) * (d + 1)),
        (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
          (zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    (∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) a *
              (ξ a : ℂ)) *
        (f.1.osConjTensorProduct g.1) y) =
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
        (star (section43FourierLaplaceIntegral d n f qL) *
          section43FourierLaplaceIntegral d (m + 1) g qR) := by
  classical
  let _ht : 0 < t := ht
  let e := section43NPointProductSplitMeasurableEquiv d n (m + 1)
  let μP : Measure (NPointDomain d n × NPointDomain d (m + 1)) :=
    (volume : Measure (NPointDomain d n)).prod
      (volume : Measure (NPointDomain d (m + 1)))
  let qξ : NPointDomain d (n + (m + 1)) :=
    section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
  let qL : NPointDomain d n :=
    section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ
  let qR : NPointDomain d (m + 1) :=
    section43RightTailBlock d n (m + 1) qξ
  let lamξ : ℝ :=
    ∑ i : Fin ((n + (m + 1)) * (d + 1)),
      (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  let ηξ : ℝ := -lamξ / (2 * Real.pi)
  let tail : ℂ :=
    ∑ j : Fin (m + 1),
      (t : ℂ) *
        (ξ (finProdFinEquiv
          (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
  let Lphase : NPointDomain d n → ℂ := fun xL =>
    ∑ a : Fin (n * (d + 1)),
      flattenCLEquiv n (d + 1)
        (fun k => wickRotatePoint (xL k)) a *
      (section43NegRevFlat d n
        (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)
  let Rphase : NPointDomain d (m + 1) → ℂ := fun xR =>
    ∑ a : Fin ((m + 1) * (d + 1)),
      flattenCLEquiv (m + 1) (d + 1)
        (fun k => wickRotatePoint (xR k)) a *
      (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
  let leftFactor : NPointDomain d n → ℂ := fun xL =>
    Complex.exp (Complex.I * Lphase xL) * f.1 xL
  let rightFactor : NPointDomain d (m + 1) → ℂ := fun xR =>
    Complex.exp (Complex.I * Rphase xR) * g.1 xR
  let H : NPointDomain d n × NPointDomain d (m + 1) → ℂ := fun p =>
    Complex.exp (-tail) * (star (leftFactor p.1) * rightFactor p.2)
  let F : NPointDomain d (n + (m + 1)) → ℂ := fun y =>
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) *
      (f.1.osConjTensorProduct g.1) y
  let θe : NPointDomain d n ≃ᵐ NPointDomain d n :=
    MeasurableEquiv.ofInvolutive
      (timeReflectionN (d := d) (n := n))
      (fun x => section43TimeReflectionN_involutive d x)
      (timeReflectionN_measurePreserving (d := d) (n := n)).measurable
  let eR : NPointDomain d (n + (m + 1)) ≃ᵐ
      NPointDomain d n × NPointDomain d (m + 1) :=
    e.trans (MeasurableEquiv.prodCongr θe
      (MeasurableEquiv.refl (NPointDomain d (m + 1))))
  have he :
      MeasurePreserving e
        (volume : Measure (NPointDomain d (n + (m + 1)))) μP := by
    simpa [e, μP] using
      section43NPointProductSplitMeasurableEquiv_measurePreserving d n (m + 1)
  have hprod_reflect :
      MeasurePreserving
        (Prod.map (timeReflectionN d) id) μP μP := by
    simpa [μP] using
      (timeReflectionN_measurePreserving (d := d) (n := n)).prod
        (MeasurePreserving.id (volume : Measure (NPointDomain d (m + 1))))
  have heR :
      MeasurePreserving eR
        (volume : Measure (NPointDomain d (n + (m + 1)))) μP := by
    change MeasurePreserving
      ((MeasurableEquiv.prodCongr θe
        (MeasurableEquiv.refl (NPointDomain d (m + 1)))) ∘ e)
      (volume : Measure (NPointDomain d (n + (m + 1)))) μP
    convert hprod_reflect.comp he using 1
    rfl
  have hF_factor :
      ∀ y : NPointDomain d (n + (m + 1)), F y = H (eR y) := by
    intro y
    rcases hsplit_y : e y with ⟨yL, xR⟩
    have hy : e.symm (yL, xR) = y := by
      calc
        e.symm (yL, xR) = e.symm (e y) := by rw [hsplit_y]
        _ = y := e.symm_apply_apply y
    have heR_y : eR y = (timeReflectionN d yL, xR) := by
      change
        (MeasurableEquiv.prodCongr θe
          (MeasurableEquiv.refl (NPointDomain d (m + 1)))) (e y) = _
      rw [hsplit_y]
      rfl
    have hpoint :=
      section43OSBorchersPhase_splitIntegrand_factorized_succRight
        (d := d) (n := n) (m := m) (f := f.1) (g := g.1)
        (t := t) ξ (timeReflectionN d yL) xR
    rw [heR_y]
    simpa [F, H, leftFactor, rightFactor, Lphase, Rphase, tail, e,
      hsplit_y, hy, section43TimeReflectionN_involutive] using hpoint
  have hsplit :
      (∫ y : NPointDomain d (n + (m + 1)), F y) =
        ∫ p : NPointDomain d n × NPointDomain d (m + 1), H p ∂μP := by
    calc
      (∫ y : NPointDomain d (n + (m + 1)), F y)
          =
        ∫ y : NPointDomain d (n + (m + 1)), H (eR y) := by
          apply integral_congr_ae
          filter_upwards with y
          exact hF_factor y
      _ = ∫ p : NPointDomain d n × NPointDomain d (m + 1), H p ∂μP := by
          exact heR.integral_comp eR.measurableEmbedding H
  have hfactor :
      (∫ p : NPointDomain d n × NPointDomain d (m + 1), H p ∂μP) =
        Complex.exp (-tail) *
          ((∫ xL : NPointDomain d n, star (leftFactor xL)) *
            ∫ xR : NPointDomain d (m + 1), rightFactor xR) := by
    calc
      (∫ p : NPointDomain d n × NPointDomain d (m + 1), H p ∂μP)
          =
        ∫ p : NPointDomain d n × NPointDomain d (m + 1),
          Complex.exp (-tail) *
            (star (leftFactor p.1) * rightFactor p.2) ∂μP := by
          rfl
      _ =
        Complex.exp (-tail) *
          ∫ p : NPointDomain d n × NPointDomain d (m + 1),
            star (leftFactor p.1) * rightFactor p.2 ∂μP := by
          exact
            MeasureTheory.integral_const_mul
              (μ := μP) (Complex.exp (-tail))
              (fun p : NPointDomain d n × NPointDomain d (m + 1) =>
                star (leftFactor p.1) * rightFactor p.2)
      _ =
        Complex.exp (-tail) *
          ((∫ xL : NPointDomain d n, star (leftFactor xL)) *
            ∫ xR : NPointDomain d (m + 1), rightFactor xR) := by
          congr 1
          simpa [μP] using
            (MeasureTheory.integral_prod_mul
              (μ := (volume : Measure (NPointDomain d n)))
              (ν := (volume : Measure (NPointDomain d (m + 1))))
              (f := fun xL : NPointDomain d n => star (leftFactor xL))
              (g := fun xR : NPointDomain d (m + 1) => rightFactor xR))
  have hleft :
      (∫ xL : NPointDomain d n, star (leftFactor xL)) =
        star (section43FourierLaplaceIntegral d n f qL) := by
    simpa [leftFactor, Lphase, qL, qξ] using
      section43OSBorchersPhase_leftFactor_eq_star_fourierLaplaceIntegral_succRight
        (d := d) (n := n) (m := m) f ξ hξ
  have hright :
      (∫ xR : NPointDomain d (m + 1), rightFactor xR) =
        section43FourierLaplaceIntegral d (m + 1) g qR := by
    simpa [rightFactor, Rphase, qR, qξ] using
      section43OSBorchersPhase_rightFactor_eq_fourierLaplaceIntegral_succRight
        (d := d) (n := n) (m := m) g ξ hξ
  have htail :
      Complex.exp (-tail) =
        Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) := by
    simpa [tail, lamξ, ηξ, Finset.mul_sum] using
      section43OSBorchersPhase_tailFactor_eq_eta_succRight
        (d := d) (n := n) (m := m) t ξ
  change (∫ y : NPointDomain d (n + (m + 1)), F y) =
    Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
      (star (section43FourierLaplaceIntegral d n f qL) *
        section43FourierLaplaceIntegral d (m + 1) g qR)
  calc
    (∫ y : NPointDomain d (n + (m + 1)), F y)
        =
      ∫ p : NPointDomain d n × NPointDomain d (m + 1), H p ∂μP := hsplit
    _ =
      Complex.exp (-tail) *
        ((∫ xL : NPointDomain d n, star (leftFactor xL)) *
          ∫ xR : NPointDomain d (m + 1), rightFactor xR) := hfactor
    _ =
      Complex.exp (-tail) *
        (star (section43FourierLaplaceIntegral d n f qL) *
          section43FourierLaplaceIntegral d (m + 1) g qR) := by
          rw [hleft, hright]
    _ =
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
        (star (section43FourierLaplaceIntegral d n f qL) *
          section43FourierLaplaceIntegral d (m + 1) g qR) := by
          rw [htail]

/-- On the Wightman spectral region, the Borchers-ordered OS phase integral is
the visible OS I `(4.24)` kernel. -/
theorem section43OSBorchersPhaseKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) a *
              (ξ a : ℂ)) *
        (f.1.osConjTensorProduct g.1) y) =
      section43OS24Kernel_succRight d n m φ ψ t ht ξ := by
  classical
  let qξ : NPointDomain d (n + (m + 1)) :=
    section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
  let qL : NPointDomain d n :=
    section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ
  let qR : NPointDomain d (m + 1) :=
    section43RightTailBlock d n (m + 1) qξ
  let lamξ : ℝ :=
    ∑ i : Fin ((n + (m + 1)) * (d + 1)),
      (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  let ηξ : ℝ := -lamξ / (2 * Real.pi)
  have hq : qξ ∈ section43PositiveEnergyRegion d (n + (m + 1)) :=
    section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
      d (n + (m + 1)) hξ.1
  have hqL : qL ∈ section43PositiveEnergyRegion d n := by
    simpa [qL, qξ] using
      section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ)
        (Nat.succ_pos m) hξ
  have hqR : qR ∈ section43PositiveEnergyRegion d (m + 1) := by
    simpa [qR, qξ] using
      section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ) hξ
  have hleftFL :
      section43FourierLaplaceIntegral d n f qL =
        (section43FrequencyRepresentative (d := d) n φ) qL := by
    exact
      (section43_leftBorchers_frequencyRepresentative_eq_fourierLaplaceIntegral
        (d := d) (n := n) (m := m) φ f hφ_rep
        (q := qξ) hq hqL).symm
  have hrightFL :
      section43FourierLaplaceIntegral d (m + 1) g qR =
        (section43FrequencyRepresentative (d := d) (m + 1) ψ) qR := by
    exact
      (section43_rightTail_frequencyRepresentative_eq_fourierLaplaceIntegral
        (d := d) (n := n) (m := m) ψ g hψ_rep
        (q := qξ) hq hqR).symm
  have heta :
      section43SuccRightEtaCLM d n m ξ = ηξ := by
    dsimp [ηξ, lamξ]
    exact section43SuccRightEtaCLM_eq_timeShiftFlatOrbit_eta d n m ξ
  have htail :
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) =
        section43PsiZTimeTest t ht ηξ := by
    simpa [lamξ, ηξ] using
      section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight
        (d := d) (n := n) (m := m) ht ξ hξ
  calc
    (∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) a *
              (ξ a : ℂ)) *
        (f.1.osConjTensorProduct g.1) y)
        =
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
        (star (section43FourierLaplaceIntegral d n f qL) *
          section43FourierLaplaceIntegral d (m + 1) g qR) := by
        simpa [qξ, qL, qR, lamξ, ηξ] using
          section43OSBorchersPhaseIntegral_factorizes_succRight
            (d := d) (n := n) (m := m) f g ht ξ hξ
    _ =
      section43PsiZTimeTest t ht ηξ *
        (star ((section43FrequencyRepresentative (d := d) n φ) qL) *
          (section43FrequencyRepresentative (d := d) (m + 1) ψ) qR) := by
        rw [htail, hleftFL, hrightFL]
    _ = section43OS24Kernel_succRight d n m φ ψ t ht ξ := by
        rw [section43OS24Kernel_succRight_apply_of_mem_spectralRegion
          (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) ht ξ hξ]
        dsimp [section43OS24VisibleKernel_succRight, qξ, qL, qR]
        rw [heta]

end OSReconstruction
