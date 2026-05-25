import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent

/-!
# Section 4.3 product-source transform carriers

This companion consumes the product-source ordered representative packet and
the transform-component carrier theorem.  It records the scalar statement
needed downstream: product one-sided Laplace time factors and compact spatial
Fourier factors determine compact ordered OS sources whose transform-component
Wightman pairing is the corresponding Schwinger scalar.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

/-- The explicit ordered source generated from a compact time/spatial product
source is the ordered-pullback source current evaluated at the compact time
source. -/
theorem section43OrderedSourceOfTimeSpatialProductSource_f_eq_orderedPullback
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n) :
    (section43OrderedSourceOfTimeSpatialSource d n
        (section43TimeSpatialProductSource d n g κ)).f =
      section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 g.f := by
  rfl

/-- Product-source specialization of
`section43OrderedSourceOfTimeSpatialProductSource_f_eq_orderedPullback`. -/
theorem section43OrderedSourceOfTimeSpatialProductSource_product_f_eq_orderedPullback
    (d n : ℕ) [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (κ : Section43SpatialCompactSource d n) :
    (section43OrderedSourceOfTimeSpatialSource d n
        (section43TimeSpatialProductSource d n (section43TimeProductSource gs) κ)).f =
      section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
        (section43TimeProductSource gs).f := by
  rfl

/-- The descended Wightman pairing of two product-source Section 4.3
components is the OS Schwinger scalar of the concrete compact ordered sources
produced by the product-source representative packet. -/
theorem bvt_pairing_productSource_eq_osScalar_orderedSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (chi1 : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hchi1 : chi1 ∈ section43SpatialFourierCompactRange d n)
    (gs2 : Fin k → Section43CompactPositiveTimeSource1D)
    (chi2 : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hchi2 : chi2 ∈ section43SpatialFourierCompactRange d k) :
    ∃ (src1 : Section43CompactOrderedSource d n)
      (src2 : Section43CompactOrderedSource d k),
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
          chi1) =
        section43FourierLaplaceTransformComponent d n
          src1.f src1.ordered src1.compact ∧
      section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
          chi2) =
        section43FourierLaplaceTransformComponent d k
          src2.f src2.ordered src2.compact ∧
      bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
            chi1))
        (section43PositiveEnergyQuotientMap (d := d) k
          (section43NPointTimeSpatialTensor d k
            (section43TimeProductTensor
              (fun i : Fin k =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
            chi2)) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src1.f.osConjTensorProduct src2.f)) := by
  let Phi1 : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n
      (section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
      chi1
  let Phi2 : SchwartzNPoint d k :=
    section43NPointTimeSpatialTensor d k
      (section43TimeProductTensor
        (fun i : Fin k =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
      chi2
  rcases
    section43NPointTimeSpatialTensor_productSource_eq_orderedTransformComponent
      d n gs1 chi1 hchi1 with
    ⟨src1, hsrc1⟩
  rcases
    section43NPointTimeSpatialTensor_productSource_eq_orderedTransformComponent
      d k gs2 chi2 hchi2 with
    ⟨src2, hsrc2⟩
  refine ⟨src1, src2, hsrc1, hsrc2, ?_⟩
  have hfreq1 :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Phi1) =
        section43FourierLaplaceTransformComponent d n
          src1.f src1.ordered src1.compact := by
    simpa [Phi1, section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hsrc1
  have hfreq2 :
      section43FrequencyProjection (d := d) k
          (section43FrequencyRepresentativeInv d k Phi2) =
        section43FourierLaplaceTransformComponent d k
          src2.f src2.ordered src2.compact := by
    simpa [Phi2, section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hsrc2
  change
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n Phi1)
        (section43PositiveEnergyQuotientMap (d := d) k Phi2) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (src1.f.osConjTensorProduct src2.f))
  rw [show
      bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
          (section43PositiveEnergyQuotientMap (d := d) n Phi1)
          (section43PositiveEnergyQuotientMap (d := d) k Phi2) =
        bvt_W OS lgc (n + k)
          ((section43FrequencyRepresentativeInv d n Phi1).conjTensorProduct
            (section43FrequencyRepresentativeInv d k Phi2)) by
      rfl]
  exact
    bvt_W_kernel_eq_osScalar_of_transformComponent_allDegrees
      d n k OS lgc
      (section43FrequencyRepresentativeInv d n Phi1)
      (section43FrequencyRepresentativeInv d k Phi2)
      src1.f src1.ordered src1.compact
      src2.f src2.ordered src2.compact
      hfreq1 hfreq2

/-- Explicit compact-source version of
`bvt_pairing_productSource_eq_osScalar_orderedSources`: if the spatial factors
are given as Fourier transforms of compact Schwartz sources, the descended BVT
pairing is the OS scalar of the concrete ordered sources built from those
product data. -/
theorem bvt_pairing_productSource_eq_osScalar_explicitOrderedSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (gs2 : Fin k → Section43CompactPositiveTimeSource1D)
    (kappa2 : Section43SpatialCompactSource d k) :
    let src1 : Section43CompactOrderedSource d n :=
      section43OrderedSourceOfTimeSpatialSource d n
        (section43TimeSpatialProductSource d n
          (section43TimeProductSource gs1) kappa1)
    let src2 : Section43CompactOrderedSource d k :=
      section43OrderedSourceOfTimeSpatialSource d k
        (section43TimeSpatialProductSource d k
          (section43TimeProductSource gs2) kappa2)
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
      (section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
          (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
      (section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
          (SchwartzMap.fourierTransformCLM ℂ kappa2.1))) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src1.f.osConjTensorProduct src2.f)) := by
  intro src1 src2
  let Phi1 : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n
      (section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
      (SchwartzMap.fourierTransformCLM ℂ kappa1.1)
  let Phi2 : SchwartzNPoint d k :=
    section43NPointTimeSpatialTensor d k
      (section43TimeProductTensor
        (fun i : Fin k =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
      (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
  have hsrc1 :
      section43PositiveEnergyQuotientMap (d := d) n Phi1 =
        section43FourierLaplaceTransformComponent d n
          src1.f src1.ordered src1.compact := by
    simpa [Phi1, src1] using
      section43NPointTimeSpatialTensor_productSource_eq_explicitOrderedTransformComponent
        d n gs1 kappa1
  have hsrc2 :
      section43PositiveEnergyQuotientMap (d := d) k Phi2 =
        section43FourierLaplaceTransformComponent d k
          src2.f src2.ordered src2.compact := by
    simpa [Phi2, src2] using
      section43NPointTimeSpatialTensor_productSource_eq_explicitOrderedTransformComponent
        d k gs2 kappa2
  have hfreq1 :
      section43FrequencyProjection (d := d) n
          (section43FrequencyRepresentativeInv d n Phi1) =
        section43FourierLaplaceTransformComponent d n
          src1.f src1.ordered src1.compact := by
    simpa [Phi1, section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hsrc1
  have hfreq2 :
      section43FrequencyProjection (d := d) k
          (section43FrequencyRepresentativeInv d k Phi2) =
        section43FourierLaplaceTransformComponent d k
          src2.f src2.ordered src2.compact := by
    simpa [Phi2, section43FrequencyProjection,
      section43FrequencyRepresentativeInv_right] using hsrc2
  change
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n Phi1)
        (section43PositiveEnergyQuotientMap (d := d) k Phi2) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (src1.f.osConjTensorProduct src2.f))
  rw [show
      bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
          (section43PositiveEnergyQuotientMap (d := d) n Phi1)
          (section43PositiveEnergyQuotientMap (d := d) k Phi2) =
        bvt_W OS lgc (n + k)
          ((section43FrequencyRepresentativeInv d n Phi1).conjTensorProduct
            (section43FrequencyRepresentativeInv d k Phi2)) by
      rfl]
  exact
    bvt_W_kernel_eq_osScalar_of_transformComponent_allDegrees
      d n k OS lgc
      (section43FrequencyRepresentativeInv d n Phi1)
      (section43FrequencyRepresentativeInv d k Phi2)
      src1.f src1.ordered src1.compact
      src2.f src2.ordered src2.compact
      hfreq1 hfreq2

/-- The explicit product-source carrier, rewritten in source-current form:
the descended BVT pairing of product Laplace/Fourier representatives is the OS
Schwinger scalar of the ordered-pullback compact source currents. -/
theorem bvt_pairing_productSource_eq_osScalar_orderedPullbackSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (gs2 : Fin k → Section43CompactPositiveTimeSource1D)
    (kappa2 : Section43SpatialCompactSource d k) :
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k
      (section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
          (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
      (section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
          (SchwartzMap.fourierTransformCLM ℂ kappa2.1))) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f).osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                (section43TimeProductSource gs2).f))) := by
  simpa [section43OrderedSourceOfTimeSpatialProductSource_product_f_eq_orderedPullback]
    using
      bvt_pairing_productSource_eq_osScalar_explicitOrderedSources
        d n k OS lgc gs1 kappa1 gs2 kappa2

end OSReconstruction
