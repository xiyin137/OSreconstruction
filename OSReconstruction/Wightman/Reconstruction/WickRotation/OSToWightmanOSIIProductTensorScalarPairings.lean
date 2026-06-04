import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional

/-!
# OS-II Product-Tensor Scalar Pairing Handoffs

This companion keeps scalar-pairing consequences of the OS-II V.2 product-source
argument out of the already-large Schwinger functional file.  The main theorem
below is the direct `(5.2)` form used by the local A0-to-P0 route: once the
selected scalar real-edge representative has the compact product-source
pairings of the local A0 cutoff shell, and the BVT shell has the semigroup
kernel, positive-orthant smearing selects the Schwinger value.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Local scalar-pairing `(A0)->(P0)` Schwinger value.

This is the product-value component of OS II V.2 in pairing form.  It avoids the
stronger local `RepresentsDistributionOn` package: the only A0-side input is
the compact positive product-source pairing identity for `S_real`. -/
theorem osiiA0LocalCutoffTimeShell_pairings_eq_schwinger_of_bvt_semigroup_kernel
    (n k : ℕ) [Nonempty (Fin k)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d k)
    (χ : SchwartzNPoint d (n + k))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + k) → ℂ))
        (CoincidenceLocus d (n + k)))
    (S_real : (Fin k → ℝ) → ℂ)
    (τ0 : Fin k → ℝ) (hτ0 : ∀ i : Fin k, 0 < τ0 i)
    (U : Set (Fin k → ℝ)) (hU_nhds : U ∈ 𝓝 τ0)
    (hU_pos : U ⊆ section43TimeStrictPositiveRegion k)
    (hS_cont : ContinuousAt S_real τ0)
    (hS_contOn_U : ContinuousOn S_real U)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d k)
    (hg_ord : tsupport (g : NPointDomain d k → ℂ) ⊆
      OrderedPositiveTimeRegion d k)
    (hS_pair :
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin k → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                  (section43TimeProductSource gs2).f)))
    (hBVT_semigroup_kernel :
      ∀ ξ : Fin k → ℝ, ξ ∈ section43TimeStrictPositiveRegion k →
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n k
            (section43PositiveEnergyQuotientMap (d := d) n
              (section43NPointTimeSpatialTensor d n
                (section43TimeProductTensor
                  (fun i : Fin n =>
                    section43OneSidedLaplaceSchwartzRepresentative1D
                      (gs1 i)))
                (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
            (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
            (section43TimeImagAxisProductKernel ξ) =
          OSInnerProduct d OS.S
            (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin k, ξ p)
              (PositiveTimeBorchersSequence.single k g hg_ord :
                BorchersSequence d)))
    (hpairBVT :
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin k → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n k
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                  (section43TimeProductSource gs2).f))) :
    S_real τ0 =
      OS.S (n + k) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin k, τ0 p) g))) := by
  let u : Section43PositiveEnergyComponent (d := d) n :=
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D
              (gs1 i)))
        (SchwartzMap.fourierTransformCLM ℂ kappa1.1))
  let chiRight : SchwartzMap (Section43SpatialSpace d k) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ kappa2.1
  have hBVT :
      S_real τ0 =
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u chiRight
          (fun i : Fin k => section43ImagAxisPsiKernel (τ0 i)) :=
    osiiA0LocalCutoffTimeShell_pairings_eq_bvt_imagAxis
      (d := d) n k OS lgc gs1 kappa1 kappa2 χ hχ_disj
      S_real τ0 hτ0 U hU_nhds hU_pos hS_cont hS_contOn_U
      hS_pair hpairBVT
  have hbvt_semigroup :
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u chiRight
          (fun i : Fin k => section43ImagAxisPsiKernel (τ0 i)) =
        OSInnerProduct d OS.S
          (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin k, τ0 p)
            (PositiveTimeBorchersSequence.single k g hg_ord :
              BorchersSequence d)) := by
    simpa [u, chiRight, bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
      section43TimeImagAxisProductKernel, section43TimeStrictPositiveRegion] using
      hBVT_semigroup_kernel τ0
        (by simpa [section43TimeStrictPositiveRegion] using hτ0)
  have hinner :
      OSInnerProduct d OS.S
          (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin k, τ0 p)
            (PositiveTimeBorchersSequence.single k g hg_ord :
              BorchersSequence d)) =
        OS.S (n + k) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (∑ p : Fin k, τ0 p) g))) := by
    simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
      OSInnerProduct_single_right_timeShift (d := d) OS f g (∑ p : Fin k, τ0 p)
  exact hBVT.trans (hbvt_semigroup.trans hinner)

end OSReconstruction
