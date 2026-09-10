/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
















noncomputable section

open Complex Set Topology Filter
open scoped Classical

namespace OSReconstruction

open OSIIChapterV.Section43ProductTimeApproximateIdentity
open OSIIChapterV.Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- One side of a fixed-axis ranked generator, retaining exactly the data
used by the scalar semigroup candidate and its positive-real source edge. -/
structure FixedAxisSplitRankFieldData
    {d : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (depth rank n : Nat) where
  particle_pos : 0 < n
  domain : Set (Fin (n - 1) -> Complex)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : Fin (n - 1) -> Complex) ∈ domain
  field : (Fin (n - 1) -> Complex) -> OSHilbertSpace OS
  field_differentiable : DifferentiableOn Complex field domain
  baseSource : euclideanPositiveTimeSubmodule (d := d) n
  source : (Fin (n - 1) -> Real) ->
    euclideanPositiveTimeSubmodule (d := d) n
  source_zero : source 0 = baseSource
  source_translation_germ :
    (fun u => (source u).1) =ᶠ[nhds 0]
      (fun u =>
        translateSchwartzConfiguration
          (OSIIChapterV.sourceParameterDisplacementCLM
            (fun j : Fin (n - 1) =>
              OSIIChapterV.chronologicalTimeSourceDirectionOfPositive
                (d := d) particle_pos j) u)
          baseSource.1)
  realRegion : Set (Fin (n - 1) -> Real)
  realRegion_open : IsOpen realRegion
  zero_mem_realRegion : (0 : Fin (n - 1) -> Real) ∈ realRegion
  realEdge : OSIIChapterV.HasPositiveTimeSourceRealEdge
    OS field source realRegion
  rankedFiber_subset : forall left : Fin n -> Real,
    OSIIChapterV.OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n depth left ->
      OSIIChapterV.osiiTimeArgumentCarrier
          ({OSIIChapterV.osiiMixedArgumentTail left} :
            Set (Fin (n - 1) -> Real)) ⊆ domain

namespace FixedAxisSplitRankFieldData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {depth rank : Nat}

variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

end FixedAxisSplitRankFieldData

namespace OSIIChapterV.GeneratorIndex

variable {k : Nat}

/-- Native fixed-axis left source arity equals generator left arity. -/
theorem rotatedFrozenLeftArity (i : GeneratorIndex k) :
    i.toGap.val + 1 = i.n :=
  i.n_eq_toGap_add_one.symm

/-- Native fixed-axis right source arity equals generator right arity. -/
theorem rotatedFrozenRightArity (i : GeneratorIndex k) :
    osiiStep4MultiGapAfterCount i.toGap + 1 = i.m := by
  rw [osiiStep4MultiGapAfterCount, i.m_eq_k_sub_toGap]
  omega

end OSIIChapterV.GeneratorIndex

namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]

end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
