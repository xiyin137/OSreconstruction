import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1Support

noncomputable section

open Complex Filter MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- If the fixed-strip diagonal matrix elements are represented by a common
one-variable difference kernel against the descended center-shear test, then
the exact center factorization needed for VI.1 Input A is automatic from the
existing difference-kernel factorization theorem. -/
theorem fixed_strip_diagonal_eq_center_factorization_of_difference_kernel_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (K_s : SpacetimeDim d → ℂ)
    (hpair : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            (twoPointDifferenceLift χ₀
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) x)) :
    ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * K_s ξ := by
  intro n
  let χn : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n))
  let I_n : ℂ :=
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ)
  have hpair_n :
      I_n =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ χn x := by
    simpa [I_n, χn] using (hpair n)
  have hmain : I_n = ∫ ξ : SpacetimeDim d, χn ξ * K_s ξ := by
    calc
      I_n = ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ χn x := hpair_n
      _ = (∫ u : SpacetimeDim d, χ₀ u) * ∫ ξ : SpacetimeDim d, K_s ξ * χn ξ := by
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K_s χ₀ χn
      _ = ∫ ξ : SpacetimeDim d, K_s ξ * χn ξ := by
          simp [hχ₀]
      _ = ∫ ξ : SpacetimeDim d, χn ξ * K_s ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          ring
  simpa [I_n, χn] using hmain

/-- So the only genuine remaining content of VI.1 Input A can be taken to be a
fixed-strip common difference-kernel pairing theorem. Once that is available,
the existing descended-center approximate-identity theorem closes the diagonal
convergence immediately. -/
theorem exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (_hs : 0 < s)
    (K_s : SpacetimeDim d → ℂ)
    (hK_cont : Continuous K_s)
    (hpair : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            (twoPointDifferenceLift χ₀
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) x)) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun n =>
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ))
        Filter.atTop
        (nhds z) := by
  refine ⟨K_s 0, ?_⟩
  have happrox :=
    descended_center_approxIdentity_integral_tendsto_of_continuousAt_zero_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hK_cont
  refine Filter.Tendsto.congr' ?_ happrox
  filter_upwards with n
  exact (fixed_strip_diagonal_eq_center_factorization_of_difference_kernel_pairing_local
    (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_compact hφ_neg s K_s hpair n).symm

end OSReconstruction
