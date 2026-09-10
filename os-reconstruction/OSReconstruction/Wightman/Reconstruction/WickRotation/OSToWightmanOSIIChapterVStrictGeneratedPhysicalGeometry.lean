/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Convex.Topology
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedLogarithmicDomains
import OSReconstruction.SCV.GaussianSolidShift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedScalarSeeds

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A convex combination of a right-half-plane point with a positive real
point cannot increase the absolute principal argument. -/
theorem abs_arg_positiveReal_combo_le
    {z : Complex}
    (hz : 0 < z.re)
    {a b tau : Real}
    (ha : 0 <= a)
    (hb : 0 <= b)
    (htau : 0 < tau) :
    |Complex.arg ((b : Complex) * z + (a * tau : Real))| <=
      |Complex.arg z| := by
  by_cases hb0 : b = 0
  · subst b
    rw [ofReal_zero, zero_mul, zero_add,
      Complex.arg_ofReal_of_nonneg (mul_nonneg ha htau.le)]
    simp
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    calc
      |Complex.arg ((b : Complex) * z + (a * tau : Real))| <=
          |Complex.arg ((b : Complex) * z)| :=
        abs_arg_add_ofReal_le
          (by simpa using mul_pos hbpos hz)
          (mul_nonneg ha htau.le)
      _ = |Complex.arg z| := by
        rw [Complex.arg_real_mul z hbpos]

/-- A coordinatewise-solid principal-argument carrier is star-convex about
every strictly positive real point. -/
theorem starConvex_osiiTimeArgumentCarrier_of_coordinatewiseSolid
    {k : Nat}
    {base : Set (Fin k -> Real)}
    (hsolid : SCV.IsCoordinatewiseSolid base)
    (tau : Fin k -> Real)
    (htau : forall i, 0 < tau i) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed tau)
      (osiiTimeArgumentCarrier base) := by
  intro z hz a b ha hb hab
  refine ⟨?_, hsolid hz.2 _ ?_⟩
  · intro i
    have hpositive :=
      (convex_Ioi (𝕜 := Real) (0 : Real))
        (htau i) (hz.1 i) ha hb hab
    simpa [osiiPositiveRealTimeEmbed, Complex.real_smul] using
      hpositive
  · intro i
    simpa [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
      Complex.real_smul, add_comm, mul_comm, mul_left_comm,
      mul_assoc] using
        abs_arg_positiveReal_combo_le
          (hz.1 i) ha hb (htau i)

namespace GeneratorStagePointedConvexAtlas

/-- A stage covered by convex charts through one common point is itself
star-convex about that point. -/
theorem carrier_starConvex
    {d k : Nat}
    {stage : OSIITimeContinuationStage d k}
    {point : OSIITimeGapSpace k}
    {ι : Type*}
    (atlas : GeneratorStagePointedConvexAtlas stage point ι) :
    StarConvex Real point stage.carrier := by
  intro z hz a b ha hb hab
  obtain ⟨i, hzi⟩ :=
    Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hz)
  exact
    atlas.domain_subset_carrier i
      (atlas.domain_convex i
        (atlas.point_mem i) hzi ha hb hab)

/-- Every open stage carrier star-convex about one point admits a pointed
convex atlas through that point.  The chart assigned to `z` is a small convex
thickening of the compact segment from the distinguished point to `z`. -/
noncomputable def ofOpenStarConvex
    {d k : Nat}
    {stage : OSIITimeContinuationStage d k}
    {point : OSIITimeGapSpace k}
    (hstar : StarConvex Real point stage.carrier) :
    GeneratorStagePointedConvexAtlas
      stage point {z // z ∈ stage.carrier} := by
  let core :
      ∀ z : {z // z ∈ stage.carrier},
        RelativelyCompactConvexCoreData
          stage.carrier point z.1 :=
    fun z =>
      RelativelyCompactConvexCoreData.selectedOfSegmentSubsetOpen
        stage.carrier_open
        (hstar.segment_subset z.2)
  exact
    {
      domain := fun z => (core z).carrier
      domain_open := fun z => (core z).carrier_open
      domain_convex := fun z => (core z).carrier_convex
      domain_subset_carrier := by
        intro z w hw
        exact
          (core z).carrier_closure_subset
            (subset_closure hw)
      carrier_subset_iUnion := by
        intro z hz
        let a : {w // w ∈ stage.carrier} := ⟨z, hz⟩
        exact
          Set.mem_iUnion_of_mem a
            (core a).right_mem
      point_mem := fun z => (core z).left_mem
    }

end GeneratorStagePointedConvexAtlas

end OSIIChapterV
end OSReconstruction
