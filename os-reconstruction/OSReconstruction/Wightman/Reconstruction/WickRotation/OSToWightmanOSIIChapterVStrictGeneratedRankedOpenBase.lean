/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPhysicalGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarSeeds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicStagePushforward














noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A bridge-only generator with zero mixed inputs gives one coordinate
direction in the rank-successor seed base. -/
theorem strictGeneratedScalarRankSuccessorSeed_piSingle
    (rank k N : Nat)
    (i : Fin k)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2) :
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank k (N + 1)
      (theta • (Pi.single i (1 : Real) : Fin k -> Real)) := by
  let g : GeneratorIndex k := GeneratorIndex.ofGap i
  have hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed g.n N (0 : Fin g.n -> Real) :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_zero_mem
      rank g.n N g.hn
  have hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed g.m N (0 : Fin g.m -> Real) :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_zero_mem
      rank g.m N g.hm
  have hseed :=
    OSIIStrictGeneratedScalarRankSuccessorSeed.generatorMemSucc
      g N (0 : Fin g.n -> Real) theta
      (0 : Fin g.m -> Real) hleft hright htheta
  have hgap : g.toGap = i :=
    GeneratorIndex.toGap_ofGap i
  have hbridge : g.bridgeGlobalIndex = i := by
    rw [GeneratorIndex.bridgeGlobalIndex_eq_toGap]
    exact hgap
  have hpoint :
      osiiArgumentGeneratorPoint g
          (0 : Fin g.n -> Real) theta
          (0 : Fin g.m -> Real) =
        theta •
          (Pi.single i (1 : Real) : Fin k -> Real) := by
    funext j
    by_cases hj : j = g.bridgeGlobalIndex
    · subst j
      rw [osiiArgumentGeneratorPoint_bridge]
      simp [hgap]
    · have hji : j ≠ i := by
        intro h
        apply hj
        exact h.trans hbridge.symm
      by_cases hleftBlock : j.val < g.n - 1
      · rw [osiiArgumentGeneratorPoint, dif_pos hleftBlock]
        simp [hji]
      · rw [osiiArgumentGeneratorPoint, dif_neg hleftBlock]
        by_cases hbridgeVal : j.val = g.n - 1
        · exfalso
          apply hj
          apply Fin.ext
          simpa [GeneratorIndex.bridgeGlobalIndex] using hbridgeVal
        · rw [dif_neg hbridgeVal]
          simp [hji]
  rw [hpoint] at hseed
  exact hseed

/-- At every positive target depth, rank-successor scalar seeds span the
complete real logarithmic argument space. -/
theorem span_strictGeneratedScalarRankSuccessorSeedBase_eq_top
    (rank k N : Nat) :
    Submodule.span Real
        (osiiStrictGeneratedScalarRankSuccessorSeedBase
          k (N + 1) rank) =
      (⊤ : Submodule Real (Fin k -> Real)) := by
  rw [eq_top_iff]
  intro x _hx
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i _hi
  have hsingle_x :
      Pi.single i (x i) =
        x i • (Pi.single i (1 : Real) : Fin k -> Real) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hsingle_x]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simpa using
    (strictGeneratedScalarRankSuccessorSeed_piSingle
      rank k N i 1 (by
        rw [abs_one]
        nlinarith [Real.pi_gt_three]))

/-- Every ranked scalar stratum is coordinatewise solid. -/
theorem strictGeneratedScalarBaseAtRank_isCoordinatewiseSolid
    (k N rank : Nat) :
    SCV.IsCoordinatewiseSolid
      (osiiStrictGeneratedLogarithmicBaseAtRank
        k N rank) := by
  intro x hx y hy
  exact hx.scalar_hyperrectangle y hy

/-- At positive depth the next-rank scalar base affinely spans the complete
real logarithmic argument space. -/
theorem affineSpan_rankSuccessorScalarBase_eq_top
    (rank k N : Nat) :
    affineSpan Real
        (osiiStrictGeneratedLogarithmicBaseAtRank
          k (N + 1) (rank + 1)) =
      (⊤ : AffineSubspace Real (Fin k -> Real)) := by
  let base : Set (Fin k -> Real) :=
    osiiStrictGeneratedLogarithmicBaseAtRank
      k (N + 1) (rank + 1)
  have hzero : (0 : Fin k -> Real) ∈ base := by
    exact
      OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
        (rank + 1) k (N + 1)
  have hseed_subset :
      osiiStrictGeneratedScalarRankSuccessorSeedBase
          k (N + 1) rank ⊆
        base := by
    intro x hx
    exact hx.toRankSucc
  have hspan :
      Submodule.span Real base =
        (⊤ : Submodule Real (Fin k -> Real)) := by
    apply le_antisymm le_top
    rw [← span_strictGeneratedScalarRankSuccessorSeedBase_eq_top
      rank k N]
    exact Submodule.span_mono hseed_subset
  have himage :
      ((fun x : Fin k -> Real =>
          x -ᵥ (0 : Fin k -> Real)) '' base) =
        base := by
    ext x
    simp
  have hvector :
      vectorSpan Real base =
        (⊤ : Submodule Real (Fin k -> Real)) := by
    rw [vectorSpan_eq_span_vsub_set_right Real hzero,
      himage]
    exact hspan
  exact
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
        Real (Fin k -> Real) (Fin k -> Real)
        ⟨0, hzero⟩).2 hvector

/-- Full-dimensionality and coordinatewise solidity put zero in the interior
of every positive-depth next-rank scalar base. -/
theorem zero_mem_interior_rankSuccessorScalarBase
    (rank k N : Nat) :
    (0 : Fin k -> Real) ∈
      interior
        (osiiStrictGeneratedLogarithmicBaseAtRank
          k (N + 1) (rank + 1)) := by
  let base : Set (Fin k -> Real) :=
    osiiStrictGeneratedLogarithmicBaseAtRank
      k (N + 1) (rank + 1)
  have hconv : Convex Real base :=
    convex_osiiStrictGeneratedLogarithmicBaseAtRank
      k (N + 1) (rank + 1)
  obtain ⟨y, hy⟩ :=
    (hconv.interior_nonempty_iff_affineSpan_eq_top).2
      (affineSpan_rankSuccessorScalarBase_eq_top
        rank k N)
  have hneg : -y ∈ base := by
    exact
      (strictGeneratedScalarBaseAtRank_isCoordinatewiseSolid
        k (N + 1) (rank + 1))
        (interior_subset hy) (-y) (by
          intro i
          simp)
  have hmid :=
    hconv.combo_interior_self_mem_interior
      hy hneg
      (a := (1 / 2 : Real))
      (b := (1 / 2 : Real))
      (by norm_num)
      (by norm_num)
      (by norm_num)
  simpa using hmid

/-- Ranked radial slack upgrades the interior at zero to openness of the
complete positive-depth next-rank scalar base. -/
theorem isOpen_rankSuccessorScalarBase
    (rank k N : Nat) :
    IsOpen
      (osiiStrictGeneratedLogarithmicBaseAtRank
        k (N + 1) (rank + 1)) := by
  rw [← subset_interior_iff_isOpen]
  intro x hx
  obtain ⟨r, hr_pos, hr_lt, y, hy, hxy⟩ :=
    hx.exists_radial_expansion
  have hmem :=
    (convex_osiiStrictGeneratedLogarithmicBaseAtRank
      k (N + 1) (rank + 1))
      |>.combo_interior_self_mem_interior
        (zero_mem_interior_rankSuccessorScalarBase
          rank k N)
        hy
        (sub_pos.mpr hr_lt)
        hr_pos.le
        (by ring : (1 - r) + r = (1 : Real))
  simpa [hxy] using hmem

/-- An open real logarithmic base has an open physical
principal-argument carrier.

The argument map is only continuous on the product right half-plane.  Writing
the carrier as the right-half-plane intersection with the principal-log
preimage keeps that domain restriction explicit. -/
theorem isOpen_timeArgumentCarrier_of_isOpen
    {k : Nat}
    {base : Set (Fin k -> Real)}
    (hbase : IsOpen base) :
    IsOpen (osiiTimeArgumentCarrier base) := by
  let imagVector : (Fin k -> Complex) -> (Fin k -> Real) :=
    fun z i => (z i).im
  have himag : Continuous imagVector := by
    fun_prop
  have himag_preimage : IsOpen (imagVector ⁻¹' base) :=
    hbase.preimage himag
  have hopen :
      IsOpen
        (osiiTimeRightHalfPlane k ∩
          osiiPrincipalLog ⁻¹' (imagVector ⁻¹' base)) :=
    (osiiPrincipalLog_differentiableOn_rightHalfPlane k).continuousOn
      |>.isOpen_inter_preimage
        (isOpen_osiiTimeRightHalfPlane k) himag_preimage
  have hcarrier :
      osiiTimeArgumentCarrier base =
        osiiTimeRightHalfPlane k ∩
          osiiPrincipalLog ⁻¹' (imagVector ⁻¹' base) := by
    ext z
    constructor
    · intro hz
      refine ⟨hz.1, ?_⟩
      change imagVector (osiiPrincipalLog z) ∈ base
      rw [show imagVector (osiiPrincipalLog z) =
          osiiTimeArgumentVector z by
        simpa [imagVector] using osiiPrincipalLog_im z]
      exact hz.2
    · intro hz
      refine ⟨hz.1, ?_⟩
      have hzbase : imagVector (osiiPrincipalLog z) ∈ base := hz.2
      rw [show imagVector (osiiPrincipalLog z) =
          osiiTimeArgumentVector z by
        simpa [imagVector] using osiiPrincipalLog_im z] at hzbase
      exact hzbase
  rw [hcarrier]
  exact hopen

/-- Positive-depth next-rank physical targets are open. -/
theorem isOpen_rankSuccessorTimeArgumentCarrier
    (rank k N : Nat) :
    IsOpen
      (osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          k (N + 1) (rank + 1))) :=
  isOpen_timeArgumentCarrier_of_isOpen
    (isOpen_rankSuccessorScalarBase rank k N)

end OSIIChapterV
end OSReconstruction
