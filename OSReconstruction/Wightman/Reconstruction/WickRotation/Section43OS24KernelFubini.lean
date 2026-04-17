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
    simpa [eR, θe, μP] using hprod_reflect.comp he
  have hF_factor :
      ∀ y : NPointDomain d (n + (m + 1)), F y = H (eR y) := by
    intro y
    rcases hsplit_y : e y with ⟨yL, xR⟩
    have hy : e.symm (yL, xR) = y := by
      calc
        e.symm (yL, xR) = e.symm (e y) := by rw [hsplit_y]
        _ = y := e.symm_apply_apply y
    have hpoint :=
      section43OSBorchersPhase_splitIntegrand_factorized_succRight
        (d := d) (n := n) (m := m) (f := f.1) (g := g.1)
        (t := t) ξ (timeReflectionN d yL) xR
    simpa [F, H, leftFactor, rightFactor, Lphase, Rphase, tail, eR, θe, e,
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

/-- Replacing the forward-tube lift kernel by its spectral-region exponential
evaluation turns the lift integral into the visible OS I `(4.24)` kernel. -/
theorem section43OSForwardTubeLiftKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
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
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
            ForwardConeAbs d (n + (m + 1)))
          hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
          hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
          (flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        (f.1.osConjTensorProduct g.1) y) =
      section43OS24Kernel_succRight d n m φ ψ t ht ξ := by
  classical
  have hpoint :
      ∀ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
            ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
              ForwardConeAbs d (n + (m + 1)))
            hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
            hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
            (flattenCLEquiv (n + (m + 1)) (d + 1)
              (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
          (f.1.osConjTensorProduct g.1) y =
        Complex.exp
            (Complex.I *
              ∑ a : Fin ((n + (m + 1)) * (d + 1)),
                flattenCLEquiv (n + (m + 1)) (d + 1)
                  (section43OSBorchersTimeShiftConfig_succRight
                    (d := d) t y) a *
                (ξ a : ℂ)) *
          (f.1.osConjTensorProduct g.1) y := by
    intro y
    by_cases hzero : (f.1.osConjTensorProduct g.1) y = 0
    · simp [hzero]
    · have hy :
          y ∈ Function.support
            ((f.1.osConjTensorProduct g.1) :
              NPointDomain d (n + (m + 1)) → ℂ) := by
        simpa [Function.mem_support] using hzero
      rw [section43OSForwardTubeLift_multiDimPsiZExt_apply_of_spectralRegion_succRight
        (d := d) OS lgc f g ht Tflat hTflat_FL ξ hξ y hy]
  calc
    (∫ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
            ForwardConeAbs d (n + (m + 1)))
          hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
          hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
          (flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        (f.1.osConjTensorProduct g.1) y)
        =
      ∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) a *
              (ξ a : ℂ)) *
        (f.1.osConjTensorProduct g.1) y := by
        apply integral_congr_ae
        filter_upwards with y
        exact hpoint y
    _ = section43OS24Kernel_succRight d n m φ ψ t ht ξ :=
        section43OSBorchersPhaseKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
          (d := d) (n := n) (m := m) φ ψ f g hφ_rep hψ_rep ht ξ hξ

/-- The real-time horizontal Fubini kernel obtained by testing against
`𝓕(section43PsiZTimeTest t ht)` is the same spectral-region Schwartz kernel as
the OS I `(4.24)` witness, and its `Tflat` pairing is the corresponding
real-time `bvt_W` horizontal integral. -/
theorem exists_section43TimeShiftKernel_psiZ_pairing_eq_OS24Kernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap
          (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + (m + 1))
            (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ KψZ_t : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ) ∧
      Set.EqOn
        (fun ξ => KψZ_t ξ)
        (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
        (section43WightmanSpectralRegion d (n + (m + 1))) ∧
      (∫ τ : ℝ,
        bvt_W OS lgc (n + (m + 1))
          (φ.conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (section43PsiZTimeTest t ht)) τ) =
        Tflat KψZ_t := by
  classical
  obtain ⟨KψZ_t, hK_eval, hK_pair⟩ :=
    exists_timeShiftKernel_pairing_fourierTest
      (d := d) (OS := OS) (lgc := lgc) (hm := Nat.succ_pos m)
      (φ := φ) (ψ := ψ)
      (χ := (SchwartzMap.fourierTransformCLM ℂ)
        (section43PsiZTimeTest t ht))
      (Tflat := Tflat) hTflat_bv
  refine ⟨KψZ_t, hK_eval, ?_, hK_pair⟩
  exact
    section43_timeShiftKernel_psiZ_eq_OS24Kernel_on_spectralRegion_succRight
      (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ)
      ht KψZ_t hK_eval

/-- If the flattened distribution is supported in the Section 4.3 Wightman
spectral region, the real-time horizontal `bvt_W` pairing against
`𝓕(section43PsiZTimeTest t ht)` is obtained by applying `Tflat` directly to
the OS I `(4.24)` Schwartz kernel. -/
theorem section43TimeShiftKernel_psiZ_pairing_eq_Tflat_OS24Kernel_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap
          (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + (m + 1))
            (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) := by
  classical
  obtain ⟨KψZ_t, _hK_eval, hK_eqOn, hK_pair⟩ :=
    exists_section43TimeShiftKernel_psiZ_pairing_eq_OS24Kernel_on_spectralRegion_succRight
      (d := d) (n := n) (m := m) (OS := OS) (lgc := lgc)
      (φ := φ) (ψ := ψ) ht Tflat hTflat_bv
  calc
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ)
        = Tflat KψZ_t := hK_pair
    _ = Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) := by
        exact hasFourierSupportIn_eqOn hTflat_supp
          (fun ξ hξ => hK_eqOn hξ)

end OSReconstruction
