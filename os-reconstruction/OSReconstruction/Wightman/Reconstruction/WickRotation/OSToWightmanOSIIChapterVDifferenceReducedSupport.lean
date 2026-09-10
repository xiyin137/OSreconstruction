import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger

/-!
# Full difference-time support versus reduced-time support

The reduced consecutive-gap coordinate is the tail of the full ordered
difference-time coordinate. Consequently, a uniform compact carrier for the
full coordinate induces one for the reduced coordinate.
-/

open Set Topology
open scoped Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

/-- The reduced-time coordinate of an ordered time/spatial tensor belongs to
the tail of the full ordered time support. -/
theorem orderedPullback_reducedTimeProjection_mem_tail_tsupport
    (φ : SchwartzMap (Fin (m + 1) → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (m + 1)) ℂ)
    (x : NPointDomain d (m + 1))
    (hx :
      x ∈ tsupport
        ((section43OrderedPullbackTimeSpatialTensorCLM
          d (m + 1) χ φ : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) → ℂ)) :
    reducedTimeProjectionCLM d m x ∈
      Fin.tail '' tsupport (φ : (Fin (m + 1) → ℝ) → ℂ) := by
  have htime :
      section43QTime (d := d) (n := m + 1)
          (section43DiffCoordRealCLE d (m + 1) x) ∈
        tsupport (φ : (Fin (m + 1) → ℝ) → ℂ) := by
    exact
      tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d (m + 1) φ χ
        (tsupport_comp_subset_preimage
          ((section43NPointTimeSpatialTensor d (m + 1) φ χ :
            SchwartzNPoint d (m + 1)) :
              NPointDomain d (m + 1) → ℂ)
          (section43DiffCoordRealCLE d (m + 1)).continuous hx)
  rw [reducedTimeProjectionCLM_eq_tail_section43QTime]
  exact ⟨_, htime, rfl⟩

/-- Chronological translation fixes a prepended absolute-time head and
translates only the physical reduced-time tail. -/
theorem translateSchwartz_prependField_chronological
    (u : Fin m → ℝ)
    (head : SchwartzMap ℝ ℂ)
    (tail : SchwartzMap (Fin m → ℝ) ℂ) :
    SCV.translateSchwartz
        (fun j : Fin (m + 1) => -Fin.cases 0 u j)
        (SCV.prependField head tail) =
      SCV.prependField head
        (SCV.translateSchwartz (-u) tail) := by
  ext q
  rw [SCV.translateSchwartz_apply, SCV.prependField_apply,
    SCV.prependField_apply, SCV.translateSchwartz_apply]
  congr 2
  simp [Pi.add_apply]

/-- A prepended product cannot have time support above a tail point outside
the support of its tail factor. -/
theorem tsupport_prependField_subset_tail_preimage
    (head : SchwartzMap ℝ ℂ)
    (tail : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport
        (SCV.prependField head tail :
          (Fin (m + 1) → ℝ) → ℂ) ⊆
      Fin.tail ⁻¹' tsupport (tail : (Fin m → ℝ) → ℂ) := by
  have htail_continuous :
      Continuous (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) := by
    apply continuous_pi
    intro i
    exact continuous_apply i.succ
  refine closure_minimal ?_
    ((isClosed_tsupport _).preimage htail_continuous)
  intro q hq
  rw [Function.mem_support] at hq
  apply subset_tsupport
  rw [Function.mem_support]
  intro hzero
  apply hq
  have hzero' : tail (fun i : Fin m => q i.succ) = 0 := by
    simpa only using hzero
  simp [SCV.prependField_apply, hzero']

/-- A common compact carrier for all full ordered difference-time coordinates
induces a common compact carrier for the consecutive-gap projection by
discarding the absolute-time head coordinate. -/
theorem
    HasUniformCompactStrictPositiveDifferenceTimeSupport.toReducedTimeSupport
    {ι : Type*}
    {φ : ι → SchwartzNPoint d (m + 1)}
    (hφ :
      HasUniformCompactStrictPositiveDifferenceTimeSupport φ) :
    HasUniformCompactStrictPositiveReducedTimeSupport φ := by
  obtain ⟨K, hK_compact, hK_positive, hφK⟩ := hφ
  let Ktail : Set (Fin m → ℝ) := Fin.tail '' K
  have htail_continuous :
      Continuous (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) := by
    apply continuous_pi
    intro i
    exact continuous_apply i.succ
  have hKtail_compact : IsCompact Ktail :=
    hK_compact.image htail_continuous
  have hKtail_positive :
      Ktail ⊆ section43TimeStrictPositiveRegion m := by
    rintro τ ⟨q, hq, rfl⟩ i
    exact hK_positive hq i.succ
  refine ⟨Ktail, hKtail_compact, hKtail_positive, ?_⟩
  intro a x hx
  rw [reducedTimeProjectionCLM_eq_tail_section43QTime]
  exact ⟨_, hφK a x hx, rfl⟩

/-- Chronological source-parameter translation descends to the pure reduced
time displacement `-u`, with no reduced spatial displacement. -/
theorem reducedConfigurationDisplacement_chronologicalSourceParameter
    (u : Fin m → ℝ) :
    reducedConfigurationDisplacement
        (sourceParameterDisplacementCLM
          (fun i : Fin m =>
            chronologicalTimeSourceDirection (d := d) i) u) =
      fun i μ => Fin.cases (-u i) (fun _ => 0) μ := by
  funext i μ
  refine Fin.cases ?_ (fun ν => ?_) μ
  · have htime :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) u (0 : NPointDomain d (m + 1)) i.succ
    rw [reducedConfigurationDisplacement_apply]
    change
      section43QTime (d := d) (n := m + 1)
          (section43DiffCoordRealCLE d (m + 1)
            (sourceParameterDisplacementCLM
              (fun r : Fin m =>
                chronologicalTimeSourceDirection (d := d) r) u)) i.succ =
        -u i
    have hzero :
        section43QTime (d := d) (n := m + 1)
            (section43DiffCoordRealCLE d (m + 1)
              (0 : NPointDomain d (m + 1))) i.succ = 0 := by
      rw [map_zero]
      rfl
    rw [zero_add, hzero, Fin.cases_succ, zero_sub] at htime
    exact htime
  · have hspatial :=
      chronologicalSourceParameterDisplacement_diff_spatial
        (d := d) u (0 : NPointDomain d (m + 1))
    have hcoord :=
      congrArg
        (fun z : Section43SpatialSpace d (m + 1) => z (i.succ, ν))
        hspatial
    rw [reducedConfigurationDisplacement_apply]
    change
      section43QSpatial (d := d) (n := m + 1)
          (section43DiffCoordRealCLE d (m + 1)
            (sourceParameterDisplacementCLM
              (fun r : Fin m =>
                chronologicalTimeSourceDirection (d := d) r) u))
          (i.succ, ν) =
        0
    simpa using hcoord

/-- After basepoint reduction, chronological full-source translation is
exactly translation of the reduced time factor by `-u`; the reduced spatial
factor is unchanged. -/
theorem translate_reducedTimeSpatialTensor_chronological
    (u : Fin m → ℝ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    translateSchwartzConfiguration
        (reducedConfigurationDisplacement
          (sourceParameterDisplacementCLM
            (fun i : Fin m =>
              chronologicalTimeSourceDirection (d := d) i) u))
        (section43NPointTimeSpatialTensor d m ψ χ) =
      section43NPointTimeSpatialTensor d m
        (SCV.translateSchwartz (-u) ψ) χ := by
  rw [reducedConfigurationDisplacement_chronologicalSourceParameter]
  ext q
  rw [translateSchwartzConfiguration_apply,
    section43NPointTimeSpatialTensor_apply,
    section43NPointTimeSpatialTensor_apply,
    SCV.translateSchwartz_apply]
  have htime :
      section43QTime (d := d) (n := m)
          (q + fun i μ => Fin.cases (-u i) (fun _ => 0) μ) =
        section43QTime (d := d) (n := m) q + -u := by
    ext i
    rfl
  have hspatial :
      section43QSpatial (d := d) (n := m)
          (q + fun i μ => Fin.cases (-u i) (fun _ => 0) μ) =
        section43QSpatial (d := d) (n := m) q := by
    apply PiLp.ext
    intro i
    change
      q i.1 i.2.succ +
          Fin.cases (-u i.1) (fun _ => 0) i.2.succ =
        q i.1 i.2.succ
    simp
  rw [htime, hspatial]

end OSIIChapterV
end OSReconstruction
