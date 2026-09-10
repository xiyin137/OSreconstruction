/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMixedTimeSplit

open Set Topology Filter
open scoped Classical Pointwise

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

noncomputable section

/-- One compact strict-positive carrier for translated approximate identities
whose centers range over a compact strict-positive set. -/
structure CompactCenterFamilyTimeCarrierData
    {n : Nat}
    (I : Section43ProductTimeApproximateIdentity n)
    (centers : Set (Fin n -> Real)) where
  carrier : Set (Fin n -> Real)
  carrier_compact : IsCompact carrier
  carrier_positive : carrier ⊆ section43TimeStrictPositiveRegion n
  centers_subset_carrier : centers ⊆ carrier
  carrier_above_center : forall xi, xi ∈ carrier ->
    exists tau, tau ∈ centers ∧ forall i, tau i <= xi i
  translated_support : forall
    (tau : Fin n -> Real), tau ∈ centers ->
    (htau : tau ∈ section43TimeStrictPositiveRegion n) ->
    forall scale : Nat,
    tsupport
        (SCV.translateSchwartz (-tau) (I.test scale) :
          (Fin n -> Real) -> Complex) ⊆
      carrier

theorem exists_compactCenterFamilyTimeCarrierData
    {n : Nat}
    (I : Section43ProductTimeApproximateIdentity n)
    (centers : Set (Fin n -> Real))
    (hcenters_compact : IsCompact centers)
    (hcenters_positive :
      centers ⊆ section43TimeStrictPositiveRegion n) :
    Nonempty (CompactCenterFamilyTimeCarrierData I centers) := by
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_range_of_tendsto I.radius I.radius_tendsto
      ).subset_closedBall (0 : Real)
  let R : Real := |R0| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let offsets : Set (Fin n -> Real) :=
    Metric.closedBall 0 R ∩ {u | forall i, 0 <= u i}
  have hoffsets_closed : IsClosed offsets := by
    apply Metric.isClosed_closedBall.inter
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_le continuous_const (continuous_apply i)
  have hoffsets_compact : IsCompact offsets := by
    exact (isCompact_closedBall (0 : Fin n -> Real) R).inter_right
      (by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i : Fin n =>
          isClosed_le continuous_const (continuous_apply i))
  let carrier := centers + offsets
  have hcarrier_compact : IsCompact carrier :=
    hcenters_compact.add hoffsets_compact
  have hcarrier_positive :
      carrier ⊆ section43TimeStrictPositiveRegion n := by
    intro xi hxi i
    obtain ⟨tau, htau, u, hu, rfl⟩ := Set.mem_add.mp hxi
    have htau_pos := hcenters_positive htau i
    have hu_nonneg : 0 <= u i := hu.2 i
    simpa only [Pi.add_apply] using add_pos_of_pos_of_nonneg htau_pos hu_nonneg
  refine ⟨{
    carrier := carrier
    carrier_compact := hcarrier_compact
    carrier_positive := hcarrier_positive
    centers_subset_carrier := ?_
    carrier_above_center := ?_
    translated_support := ?_ }⟩
  · intro tau htau
    apply Set.mem_add.mpr
    refine ⟨tau, htau, 0, ?_, by simp⟩
    constructor
    · simpa [R] using hR.le
    · simp
  · intro xi hxi
    obtain ⟨tau, htau, u, hu, rfl⟩ := Set.mem_add.mp hxi
    refine ⟨tau, htau, ?_⟩
    intro i
    exact le_add_of_nonneg_right (hu.2 i)
  intro tau htau htau_pos scale
  apply closure_minimal
  · intro xi hxi
    have hxi_source :
        xi - tau ∈ Function.support (I.test scale : (Fin n -> Real) -> Complex) := by
      simpa [sub_eq_add_neg] using
        (SCV.mem_support_translateSchwartz_iff
          (-tau) (I.test scale) xi).mp hxi
    have hrange : I.radius scale ∈ Set.range I.radius := ⟨scale, rfl⟩
    have hradius_abs : |I.radius scale| <= R0 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hR0 hrange
    have hradius : I.radius scale <= R := by
      calc
        I.radius scale <= |I.radius scale| := le_abs_self _
        _ <= R0 := hradius_abs
        _ <= |R0| := le_abs_self _
        _ <= R := by dsimp [R]; linarith
    have hxi_radius : ‖xi - tau‖ < I.radius scale := by
      simpa [Metric.mem_ball, dist_zero_right] using I.support scale hxi_source
    apply Set.mem_add.mpr
    refine ⟨tau, htau, xi - tau, ?_, by simp⟩
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_of_lt hxi_radius).trans hradius
    · intro i
      have hpositive :=
        I.test_positive scale (subset_tsupport (I.test scale) hxi_source) i
      dsimp [section43TimeStrictPositiveRegion] at hpositive
      simpa only [Pi.sub_apply] using le_of_lt hpositive
  · exact hcarrier_compact.isClosed

theorem CompactCenterFamilyTimeCarrierData.translatedPositiveTimeSpatialSource_mem_carrier
    {d n : Nat} [NeZero d]
    {I : Section43ProductTimeApproximateIdentity n}
    {centers : Set (Fin n -> Real)}
    (C : CompactCenterFamilyTimeCarrierData I centers)
    (tau : Fin n -> Real)
    (htau_centers : tau ∈ centers)
    (htau : tau ∈ section43TimeStrictPositiveRegion n)
    (chi : SchwartzMap (Section43SpatialSpace d n) Complex)
    (scale : Nat) :
    I.translatedPositiveTimeSpatialSource tau htau chi scale ∈
      uniformCompactTimeSourceSubmodule d n C.carrier := by
  intro x hx
  have htime :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n x) ∈
        tsupport
          (SCV.translateSchwartz (-tau) (I.test scale) :
            (Fin n -> Real) -> Complex) := by
    exact
      osiiA0_orderedPullback_tsupport_subset_timeSet
        (d := d) chi
        (SCV.translateSchwartz (-tau) (I.test scale))
        (tsupport
          (SCV.translateSchwartz (-tau) (I.test scale) :
            (Fin n -> Real) -> Complex))
        (Subset.refl _)
        (by
          simpa [translatedPositiveTimeSpatialSource_coe] using hx)
  exact C.translated_support tau htau_centers htau scale htime

/-- The translated source at any center in the compact family, with its
codomain restricted to the common carrier. -/
noncomputable def CompactCenterFamilyTimeCarrierData.sourceCLM
    {d n : Nat} [NeZero d]
    {I : Section43ProductTimeApproximateIdentity n}
    {centers : Set (Fin n -> Real)}
    (C : CompactCenterFamilyTimeCarrierData I centers)
    (tau : Fin n -> Real)
    (htau_centers : tau ∈ centers)
    (htau : tau ∈ section43TimeStrictPositiveRegion n)
    (scale : Nat) :
    SchwartzMap (Section43SpatialSpace d n) Complex →L[Complex]
      UniformCompactTimeSource d n C.carrier :=
  (section43PositiveTimeSpatialSourceCLM
      d n (I.translatedSource tau htau scale)).codRestrict
    (uniformCompactTimeSourceSubmodule d n C.carrier)
    (fun chi =>
      C.translatedPositiveTimeSpatialSource_mem_carrier
        tau htau_centers htau chi scale)

@[simp] theorem CompactCenterFamilyTimeCarrierData.sourceCLM_source
    {d n : Nat} [NeZero d]
    {I : Section43ProductTimeApproximateIdentity n}
    {centers : Set (Fin n -> Real)}
    (C : CompactCenterFamilyTimeCarrierData I centers)
    (tau : Fin n -> Real)
    (htau_centers : tau ∈ centers)
    (htau : tau ∈ section43TimeStrictPositiveRegion n)
    (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d n) Complex) :
    UniformCompactTimeSource.source
        (C.sourceCLM (d := d) tau htau_centers htau scale chi) =
      I.translatedPositiveTimeSpatialSource tau htau chi scale :=
  rfl

end

end Section43ProductTimeApproximateIdentity

/-- Linear form of the canonical left reflected time split. -/
noncomputable def reflectedMixedLeftTimeSplitLM
    {k : Nat} :
    (Fin (k + (k + 1)) -> Real) →ₗ[Real] (Fin (k + 1) -> Real) where
  toFun := reflectedMixedLeftTimeSplit
  map_add' tau sigma := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [reflectedMixedLeftTimeSplit]
      ring
    · simp [reflectedMixedLeftTimeSplit]
  map_smul' c tau := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [reflectedMixedLeftTimeSplit]
      ring
    · simp [reflectedMixedLeftTimeSplit]

/-- Continuous-linear form of the canonical left reflected time split. -/
noncomputable def reflectedMixedLeftTimeSplitCLM
    {k : Nat} :
    (Fin (k + (k + 1)) -> Real) →L[Real] (Fin (k + 1) -> Real) :=
  ⟨reflectedMixedLeftTimeSplitLM,
    reflectedMixedLeftTimeSplitLM.continuous_of_finiteDimensional⟩

@[simp] theorem reflectedMixedLeftTimeSplitCLM_apply
    {k : Nat}
    (tau : Fin (k + (k + 1)) -> Real) :
    reflectedMixedLeftTimeSplitCLM tau =
      reflectedMixedLeftTimeSplit tau :=
  rfl

/-- Linear form of the canonical right reflected time split. -/
noncomputable def reflectedMixedRightTimeSplitLM
    {k : Nat} :
    (Fin (k + (k + 1)) -> Real) →ₗ[Real] (Fin (k + 1) -> Real) where
  toFun := reflectedMixedRightTimeSplit
  map_add' tau sigma := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [reflectedMixedRightTimeSplit]
      ring
    · simp [reflectedMixedRightTimeSplit]
  map_smul' c tau := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [reflectedMixedRightTimeSplit]
      ring
    · simp [reflectedMixedRightTimeSplit]

/-- Continuous-linear form of the canonical right reflected time split. -/
noncomputable def reflectedMixedRightTimeSplitCLM
    {k : Nat} :
    (Fin (k + (k + 1)) -> Real) →L[Real] (Fin (k + 1) -> Real) :=
  ⟨reflectedMixedRightTimeSplitLM,
    reflectedMixedRightTimeSplitLM.continuous_of_finiteDimensional⟩

@[simp] theorem reflectedMixedRightTimeSplitCLM_apply
    {k : Nat}
    (tau : Fin (k + (k + 1)) -> Real) :
    reflectedMixedRightTimeSplitCLM tau =
      reflectedMixedRightTimeSplit tau :=
  rfl

end OSIIChapterV
end OSReconstruction
