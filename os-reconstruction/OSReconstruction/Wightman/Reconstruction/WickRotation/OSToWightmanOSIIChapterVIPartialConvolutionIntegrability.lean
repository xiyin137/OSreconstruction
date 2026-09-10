import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIPartialConvolutionKernel

/-!
# Integrability of the OS-II partial-convolution transform

The weighted full-complex convolution hypothesis naturally lives on
`z x y'`.  Splitting `z = x + i y`, permuting the three real factors, and
integrating out `x` proves joint integrability of the paper's transform on
`(y', y)`.  This is the Fubini input needed for norm and support estimates
after equation `(6.6)`.
-/

noncomputable section

open MeasureTheory

namespace OSReconstruction

theorem osiiStep4PartialConvolutionTransform_integrable
    {m : ℕ}
    (g : (Fin m → ℂ) → ℝ)
    (F : (Fin m → ℂ) → ℂ)
    (c : Fin m → ℂ)
    (hweighted : Integrable
      (fun p : (Fin m → ℂ) × (Fin m → ℝ) =>
        F (c + p.1) *
          (osiiStep4PartialConvolutionKernel g p.1 p.2 : ℂ))
      ((volume : Measure (Fin m → ℂ)).prod
        (volume : Measure (Fin m → ℝ)))) :
    Integrable
      (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        osiiStep4PartialConvolutionTransform g F c p.2 p.1)
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) := by
  let e := osiiStep4ComplexRealImagMeasurableEquiv m
  have he : MeasurePreserving e
      (volume : Measure (Fin m → ℂ))
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) :=
    osiiStep4ComplexRealImagMeasurableEquiv_measurePreserving m
  let H : ((Fin m → ℂ) × (Fin m → ℝ)) → ℂ := fun p =>
    F (c + p.1) *
      (osiiStep4PartialConvolutionKernel g p.1 p.2 : ℂ)
  let Q : (((Fin m → ℝ) × (Fin m → ℝ)) ×
      (Fin m → ℝ)) → ℂ := fun p => H (e.symm p.1, p.2)
  have hsplit : MeasurePreserving
      (Prod.map e.symm id)
      (((volume : Measure (Fin m → ℝ)).prod
          (volume : Measure (Fin m → ℝ))).prod
        (volume : Measure (Fin m → ℝ)))
      ((volume : Measure (Fin m → ℂ)).prod
        (volume : Measure (Fin m → ℝ))) :=
    he.symm.prod (MeasurePreserving.id
      (volume : Measure (Fin m → ℝ)))
  have hQint : Integrable Q
      (((volume : Measure (Fin m → ℝ)).prod
          (volume : Measure (Fin m → ℝ))).prod
        (volume : Measure (Fin m → ℝ))) := by
    have hcomp := hsplit.integrable_comp_of_integrable hweighted
    simpa [Q, H, Function.comp_def] using hcomp
  let R : (((Fin m → ℝ) × (Fin m → ℝ)) ×
      (Fin m → ℝ)) → ℂ := fun p => Q ((p.2, p.1.2), p.1.1)
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ)))
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) :=
    Measure.measurePreserving_swap
  have hassoc := measurePreserving_prodAssoc
    (volume : Measure (Fin m → ℝ))
    (volume : Measure (Fin m → ℝ))
    (volume : Measure (Fin m → ℝ))
  have hinnerSwap :=
    (MeasurePreserving.id
      (volume : Measure (Fin m → ℝ))).prod hswap
  have hreorder : MeasurePreserving
      (fun p : (((Fin m → ℝ) × (Fin m → ℝ)) ×
          (Fin m → ℝ)) => ((p.2, p.1.2), p.1.1))
      (((volume : Measure (Fin m → ℝ)).prod
          (volume : Measure (Fin m → ℝ))).prod
        (volume : Measure (Fin m → ℝ)))
      (((volume : Measure (Fin m → ℝ)).prod
          (volume : Measure (Fin m → ℝ))).prod
        (volume : Measure (Fin m → ℝ))) := by
    have houterSwap : MeasurePreserving Prod.swap
        ((volume : Measure (Fin m → ℝ)).prod
          ((volume : Measure (Fin m → ℝ)).prod
            (volume : Measure (Fin m → ℝ))))
        (((volume : Measure (Fin m → ℝ)).prod
            (volume : Measure (Fin m → ℝ))).prod
          (volume : Measure (Fin m → ℝ))) :=
      Measure.measurePreserving_swap
    simpa [Function.comp_def] using
      houterSwap.comp (hinnerSwap.comp hassoc)
  have hRint : Integrable R
      (((volume : Measure (Fin m → ℝ)).prod
          (volume : Measure (Fin m → ℝ))).prod
        (volume : Measure (Fin m → ℝ))) := by
    have hcomp := hreorder.integrable_comp_of_integrable hQint
    simpa [R, Function.comp_def] using hcomp
  simpa [R, Q, H, e, osiiStep4PartialConvolutionTransform] using
    hRint.integral_prod_left

end OSReconstruction
