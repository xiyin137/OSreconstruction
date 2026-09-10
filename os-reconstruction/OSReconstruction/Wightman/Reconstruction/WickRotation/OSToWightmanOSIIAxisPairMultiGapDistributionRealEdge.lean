/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionFamily
















noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d]

namespace OSIIAxisPairMultiGapSourcewiseMZFamily

/-- The unique full Schwartz distribution extending the continuous
multilinear real edge at one real multi-gap logarithmic point. -/
noncomputable def realEdgeDistribution
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d n →L[ℂ] ℂ :=
  Classical.choose (schwartz_nuclear_extension d n (P.realEdge x))

@[simp]
theorem realEdgeDistribution_productTensor
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin n → SchwartzSpacetime d) :
    P.realEdgeDistribution x (SchwartzMap.productTensor fs) =
      P.realEdge x fs :=
  (Classical.choose_spec
    (schwartz_nuclear_extension d n (P.realEdge x))).1 fs

namespace SchwartzDistributionFamily

variable {P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k}

/-- The canonical full Schwartz distribution family restricts on the real
multi-gap slice to the nuclear extension of the prescribed Schwinger edge. -/
theorem distribution_realEdge
    (A : P.SchwartzDistributionFamily)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    A.distribution
        ⟨osiiAxisPairSimultaneousLogRealEmbed x,
          osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap x⟩ =
      P.realEdgeDistribution x := by
  apply
    (Classical.choose_spec
      (schwartz_nuclear_extension d n (P.realEdge x))).2
  intro fs
  rw [A.productTensor]
  exact P.realEdge_eq fs x

/-- Totalized pairings therefore have the full Schwartz Schwinger real edge
at every real multi-gap logarithmic point. -/
theorem pairing_realEdge
    (A : P.SchwartzDistributionFamily)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (f : SchwartzNPoint d n) :
    A.pairing f (osiiAxisPairSimultaneousLogRealEmbed x) =
      P.realEdgeDistribution x f := by
  rw [A.pairing_of_mem _ _
    (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap x)]
  rw [A.distribution_realEdge x]

end SchwartzDistributionFamily

end OSIIAxisPairMultiGapSourcewiseMZFamily

namespace OSIIChronologicalCompactFactors

variable [NeZero k]

section OriginalOSSourceFamily

variable (F : OSIIChronologicalCompactFactors d k)
  (OS : OsterwalderSchraderAxioms d)
  (T : ℝ) (hT : 1 < T)
  (hordered :
    ∀ a : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)

end OriginalOSSourceFamily

end OSIIChronologicalCompactFactors

namespace OSIIChronologicalSourcewisePacketData

variable {OS : OsterwalderSchraderAxioms d}
  {lgc : OSLinearGrowthCondition d OS} [NeZero k]

end OSIIChronologicalSourcewisePacketData

end OSReconstruction
