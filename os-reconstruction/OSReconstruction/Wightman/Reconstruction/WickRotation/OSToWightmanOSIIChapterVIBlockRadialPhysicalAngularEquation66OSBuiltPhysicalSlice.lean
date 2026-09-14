/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltPhysicalAtlas

/-!
# OS-II Equation (6.6) Physical Spatial Slice

Identifies the canonical Chapter V positive-real stage distribution with
integration against the non-circular OS-built physical density.  The proof
passes through the exact time/spatial tensor and Fubini identity on compactly
supported tests, then extends to every native spatial Schwartz test using the
proved polynomial density bound.
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

variable {d k : Nat} [NeZero d] [NeZero k]

/-- The standard spatial flattening preserves Lebesgue measure. -/
theorem osiiEquation66_section43SpatialFlatCLE_measurePreserving (d n : ℕ) :
    MeasurePreserving
      (section43SpatialFlatCLE d n)
      (volume : Measure (Section43SpatialSpace d n))
      (volume : Measure (Fin (n * d) → ℝ)) := by
  let h := (section43EuclideanSpaceMeasurableEquiv_measurePreserving
      (Fin n × Fin d)).trans
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin (n * d) ↦ ℝ) finProdFinEquiv)
  convert h using 1
  funext eta i
  rw [section43SpatialFlatCLE_apply]
  change
    (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) eta)
        (finProdFinEquiv.symm i) =
      (Equiv.piCongrLeft (fun _ : Fin (n * d) ↦ ℝ) finProdFinEquiv
        (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) eta)) i
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

/-- The equation-(6.6) mixed point is the flattened inverse of the standard
time/spatial product chart. -/
theorem flattenCLEquivReal_timeSpatial_symm_eq_mixed
    (tau : Fin k → ℝ)
    (eta : Section43SpatialSpace d k) :
    flattenCLEquivReal k (d + 1)
        ((section43NPointTimeSpatialMeasurableEquiv d k).symm (tau, eta)) =
      osiiStep4MixedSpatialRealPoint d k tau
        (section43SpatialFlatCLE d k eta) := by
  funext q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simp [osiiStep4MixedSpatialRealPoint]
  | succ j =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (section43NPointTimeSpatialMeasurableEquiv_symm_apply_spatial
          d k (tau, eta) (i, j))

/-- Joint continuity of the mixed time/spatial coordinate insertion. -/
theorem continuous_osiiStep4MixedSpatialRealPoint_uncurry :
    Continuous
      (fun p : (Fin k → ℝ) × (Fin (k * d) → ℝ) ↦
        osiiStep4MixedSpatialRealPoint d k p.1 p.2) := by
  apply continuous_pi
  intro q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (continuous_apply i).comp continuous_fst
  | succ j =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (continuous_apply (finProdFinEquiv (i, j))).comp continuous_snd

@[simp] theorem osiiEquation66FlatTime_mixedSpatialRealPoint
    (tau : Fin k → ℝ) (x : Fin (k * d) → ℝ) :
    osiiEquation66FlatTime (d := d)
        (osiiStep4MixedSpatialRealPoint d k tau x) = tau := by
  funext i
  simp [osiiEquation66FlatTime, osiiStep4MixedSpatialRealPoint]

/-- A Section 4.3 tensor written in the interleaved flat coordinates used by
the equation-(6.6) density. -/
noncomputable def osiiEquation66FlatTimeSpatialTensor
    (phi : SchwartzMap (Fin k → ℝ) ℂ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin (k * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenCLEquivReal k (d + 1)).symm
    (section43NPointTimeSpatialTensor d k phi chi)

@[simp] theorem osiiEquation66FlatTimeSpatialTensor_mixed
    (phi : SchwartzMap (Fin k → ℝ) ℂ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (tau : Fin k → ℝ)
    (x : Fin (k * d) → ℝ) :
    osiiEquation66FlatTimeSpatialTensor (d := d) phi chi
        (osiiStep4MixedSpatialRealPoint d k tau x) =
      phi tau * section43SpatialFlatSchwartzCLE d k chi x := by
  let eta : Section43SpatialSpace d k :=
    (section43SpatialFlatCLE d k).symm x
  have hcoord :
      (flattenCLEquivReal k (d + 1)).symm
          (osiiStep4MixedSpatialRealPoint d k tau x) =
        (section43NPointTimeSpatialMeasurableEquiv d k).symm
          (tau, eta) := by
    apply (flattenCLEquivReal k (d + 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply,
      flattenCLEquivReal_timeSpatial_symm_eq_mixed]
    simp [eta]
  rw [osiiEquation66FlatTimeSpatialTensor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change section43NPointTimeSpatialTensor d k phi chi
      ((flattenCLEquivReal k (d + 1)).symm
        (osiiStep4MixedSpatialRealPoint d k tau x)) = _
  rw [hcoord]
  have hp :=
    (section43NPointTimeSpatialMeasurableEquiv d k).apply_symm_apply
      (tau, eta)
  rw [section43NPointTimeSpatialTensor_apply]
  change phi
      (nPointTimeSpatialCLE (d := d) k
        ((section43NPointTimeSpatialMeasurableEquiv d k).symm
          (tau, eta))).1 *
      chi
        (nPointTimeSpatialCLE (d := d) k
          ((section43NPointTimeSpatialMeasurableEquiv d k).symm
            (tau, eta))).2 = _
  rw [section43NPointTimeSpatialMeasurableEquiv_apply] at hp
  rw [hp]
  simp [eta]

theorem hasCompactSupport_osiiEquation66FlatTimeSpatialTensor
    (phi : SchwartzMap (Fin k → ℝ) ℂ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hphi : HasCompactSupport (phi : (Fin k → ℝ) → ℂ))
    (hchi : HasCompactSupport
      (chi : Section43SpatialSpace d k → ℂ)) :
    HasCompactSupport
      (osiiEquation66FlatTimeSpatialTensor (d := d) phi chi :
        (Fin (k * (d + 1)) → ℝ) → ℂ) := by
  have htensor :=
    hasCompactSupport_section43NPointTimeSpatialTensor d k phi chi hphi hchi
  simpa [osiiEquation66FlatTimeSpatialTensor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    htensor.comp_homeomorph
      (flattenCLEquivReal k (d + 1)).symm.toHomeomorph

theorem tsupport_osiiEquation66FlatTimeSpatialTensor_subset_time_preimage
    (phi : SchwartzMap (Fin k → ℝ) ℂ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    tsupport
        (osiiEquation66FlatTimeSpatialTensor (d := d) phi chi :
          (Fin (k * (d + 1)) → ℝ) → ℂ) ⊆
      {y | osiiEquation66FlatTime (d := d) y ∈
        tsupport (phi : (Fin k → ℝ) → ℂ)} := by
  intro y hy
  have hq :
      (flattenCLEquivReal k (d + 1)).symm y ∈
        tsupport
          (section43NPointTimeSpatialTensor d k phi chi :
            NPointDomain d k → ℂ) := by
    apply tsupport_comp_subset_preimage
      (section43NPointTimeSpatialTensor d k phi chi :
        NPointDomain d k → ℂ)
      (flattenCLEquivReal k (d + 1)).symm.continuous
    simpa [osiiEquation66FlatTimeSpatialTensor,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hy
  have ht :=
    tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
      d k phi chi hq
  simpa [osiiAxisPairUnflattenRealBlocks] using ht

@[simp] theorem unflattenSchwartzNPoint_osiiEquation66FlatTimeSpatialTensor
    (phi : SchwartzMap (Fin k → ℝ) ℂ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    unflattenSchwartzNPoint (d := d)
        (osiiEquation66FlatTimeSpatialTensor (d := d) phi chi) =
      section43NPointTimeSpatialTensor d k phi chi := by
  ext q
  rw [unflattenSchwartzNPoint_apply]
  change section43NPointTimeSpatialTensor d k phi chi
      ((flattenCLEquivReal k (d + 1)).symm _) =
    section43NPointTimeSpatialTensor d k phi chi q
  apply congrArg
  funext i mu
  simp [flattenCLEquivReal_symm_apply]

/-- Fubini in the interleaved equation-(6.6) coordinates.  Integrability is
requested only after passing to the natural time/spatial product chart. -/
theorem integral_eq_iterated_integral_osiiStep4MixedSpatialRealPoint
    (f : (Fin (k * (d + 1)) → ℝ) → ℂ)
    (hsplit : Integrable
      (fun p : (Fin k → ℝ) × Section43SpatialSpace d k ↦
        f (osiiStep4MixedSpatialRealPoint d k p.1
          (section43SpatialFlatCLE d k p.2)))) :
    (∫ y : Fin (k * (d + 1)) → ℝ, f y) =
      ∫ tau : Fin k → ℝ,
        ∫ x : Fin (k * d) → ℝ,
          f (osiiStep4MixedSpatialRealPoint d k tau x) := by
  let eTS := section43NPointTimeSpatialMeasurableEquiv d k
  let g : NPointDomain d k → ℂ :=
    fun q ↦ f (flattenCLEquivReal k (d + 1) q)
  calc
    (∫ y : Fin (k * (d + 1)) → ℝ, f y) =
        ∫ q : NPointDomain d k, g q := by
      simpa [g] using integral_flatten_change_of_variables k (d + 1) f
    _ = ∫ p : (Fin k → ℝ) × Section43SpatialSpace d k,
          g (eTS.symm p) := by
      have hTSsymm : MeasurePreserving eTS.symm volume volume :=
        MeasurePreserving.symm eTS
          (by simpa [eTS] using
            section43NPointTimeSpatialCLE_measurePreserving d k)
      exact (hTSsymm.integral_comp' g).symm
    _ = ∫ p : (Fin k → ℝ) × Section43SpatialSpace d k,
          f (osiiStep4MixedSpatialRealPoint d k p.1
            (section43SpatialFlatCLE d k p.2)) := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [g, eTS]
      rw [flattenCLEquivReal_timeSpatial_symm_eq_mixed]
    _ = ∫ tau : Fin k → ℝ,
          ∫ eta : Section43SpatialSpace d k,
            f (osiiStep4MixedSpatialRealPoint d k tau
              (section43SpatialFlatCLE d k eta)) := by
      exact integral_prod _ hsplit
    _ = ∫ tau : Fin k → ℝ,
          ∫ x : Fin (k * d) → ℝ,
            f (osiiStep4MixedSpatialRealPoint d k tau x) := by
      apply integral_congr_ae
      filter_upwards with tau
      exact
        (osiiEquation66_section43SpatialFlatCLE_measurePreserving d k).integral_comp
          (section43SpatialFlatCLE d k).toHomeomorph.measurableEmbedding
          (fun x ↦ f (osiiStep4MixedSpatialRealPoint d k tau x))

/-- Pair the globally glued physical density with one spatial Schwartz test. -/
noncomputable def osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (tau : Fin k → ℝ)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) : ℂ :=
  ∫ x : Fin (k * d) → ℝ,
    osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
        (osiiStep4MixedSpatialRealPoint d k tau x) *
      section43SpatialFlatSchwartzCLE d k chi x

/-- Compactly supported spatial tests give continuous real-time pairings of
the glued physical density. -/
theorem continuousOn_osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hchi : HasCompactSupport
      (chi : Section43SpatialSpace d k → ℂ)) :
    ContinuousOn
      (fun tau ↦
        osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing lgc D tau chi)
      D.realRegion := by
  let flatChi := section43SpatialFlatSchwartzCLE d k chi
  let K : Set (Fin (k * d) → ℝ) :=
    tsupport (flatChi : (Fin (k * d) → ℝ) → ℂ)
  have hflatChi : HasCompactSupport
      (flatChi : (Fin (k * d) → ℝ) → ℂ) := by
    simpa [flatChi, section43SpatialFlatSchwartzCLE_apply] using
      hchi.comp_homeomorph
        (section43SpatialFlatCLE d k).symm.toHomeomorph
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport] using hflatChi
  let f : (Fin k → ℝ) → (Fin (k * d) → ℝ) → ℂ :=
    fun tau x ↦
      osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
          (osiiStep4MixedSpatialRealPoint d k tau x) * flatChi x
  have hmap : MapsTo
      (fun p : (Fin k → ℝ) × (Fin (k * d) → ℝ) ↦
        osiiStep4MixedSpatialRealPoint d k p.1 p.2)
      (D.realRegion ×ˢ (Set.univ : Set (Fin (k * d) → ℝ)))
      {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
    intro p hp
    simpa using hp.1
  have hleft : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin (k * d) → ℝ) ↦
        osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
          (osiiStep4MixedSpatialRealPoint d k p.1 p.2))
      (D.realRegion ×ˢ (Set.univ : Set (Fin (k * d) → ℝ))) :=
    (continuousOn_osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D).comp
      continuous_osiiStep4MixedSpatialRealPoint_uncurry.continuousOn hmap
  have hright : Continuous
      (fun p : (Fin k → ℝ) × (Fin (k * d) → ℝ) ↦
        flatChi p.2) :=
    flatChi.continuous.comp continuous_snd
  have hf : ContinuousOn (Function.uncurry f)
      (D.realRegion ×ˢ (Set.univ : Set (Fin (k * d) → ℝ))) := by
    simpa [f] using hleft.mul hright.continuousOn
  have hzero : ∀ tau x, tau ∈ D.realRegion → x ∉ K → f tau x = 0 := by
    intro tau x _ hx
    have hxzero : flatChi x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    simp [f, hxzero]
  simpa [osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing, f, flatChi]
    using continuousOn_integral_of_compact_support
      (μ := (volume : Measure (Fin (k * d) → ℝ))) hK hf hzero

/-- For compactly supported spatial tests, the physical-density pairing
represents the same scalar time distribution as the canonical Chapter V
stage edge. -/
theorem osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_represents
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hchi : HasCompactSupport
      (chi : Section43SpatialSpace d k → ℂ)) :
    SCV.RepresentsDistributionOn
      ((OSIIChapterV.orderedTransportDistribution
          (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
            OS D.cutoff D.cutoff_support)).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k chi))
      (fun tau ↦
        osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing lgc D tau chi)
      D.realRegion := by
  intro phi hphi
  let H := osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
  let psi := osiiEquation66FlatTimeSpatialTensor (d := d) phi chi
  let fflat : (Fin (k * (d + 1)) → ℝ) → ℂ :=
    fun y ↦ H y * psi y
  have hpsi_compact : HasCompactSupport
      (psi : (Fin (k * (d + 1)) → ℝ) → ℂ) := by
    exact hasCompactSupport_osiiEquation66FlatTimeSpatialTensor
      phi chi hphi.1 hchi
  have hpsi_support :
      tsupport (psi : (Fin (k * (d + 1)) → ℝ) → ℂ) ⊆
        {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion} :=
    (tsupport_osiiEquation66FlatTimeSpatialTensor_subset_time_preimage
      phi chi).trans (fun _ hy ↦ hphi.2 hy)
  have hfull :=
    osiiEquation66OSBuiltCanonicalPhysicalDensity_represents lgc D
      psi ⟨hpsi_compact, hpsi_support⟩
  let mix : (Fin k → ℝ) × Section43SpatialSpace d k →
      (Fin (k * (d + 1)) → ℝ) :=
    fun p ↦ osiiStep4MixedSpatialRealPoint d k p.1
      (section43SpatialFlatCLE d k p.2)
  let Fprod : (Fin k → ℝ) × Section43SpatialSpace d k → ℂ :=
    fun p ↦ fflat (mix p)
  let K : Set ((Fin k → ℝ) × Section43SpatialSpace d k) :=
    tsupport (phi : (Fin k → ℝ) → ℂ) ×ˢ
      tsupport (chi : Section43SpatialSpace d k → ℂ)
  have hK : IsCompact K := by
    exact hphi.1.isCompact.prod hchi.isCompact
  have hmix_cont : Continuous mix := by
    simpa [mix, Function.comp_def] using
      continuous_osiiStep4MixedSpatialRealPoint_uncurry.comp
        (continuous_fst.prodMk
          ((section43SpatialFlatCLE d k).continuous.comp continuous_snd))
  have hmix_map : MapsTo mix K
      {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
    intro p hp
    change osiiEquation66FlatTime (d := d) (mix p) ∈ D.realRegion
    simpa [mix] using hphi.2 hp.1
  have hFprod_cont : ContinuousOn Fprod K := by
    have hHcont : ContinuousOn (fun p ↦ H (mix p)) K :=
      (continuousOn_osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D).comp
        hmix_cont.continuousOn hmix_map
    have hpsicont : Continuous (fun p ↦ psi (mix p)) :=
      psi.continuous.comp hmix_cont
    simpa [Fprod, fflat] using hHcont.mul hpsicont.continuousOn
  have hFprod_support : Function.support Fprod ⊆ K := by
    intro p hp
    constructor
    · by_contra hpt
      have hzero : phi p.1 = 0 :=
        image_eq_zero_of_notMem_tsupport hpt
      apply hp
      have hpsi_zero : psi (mix p) = 0 := by
        change osiiEquation66FlatTimeSpatialTensor (d := d) phi chi
            (osiiStep4MixedSpatialRealPoint d k p.1
              (section43SpatialFlatCLE d k p.2)) = 0
        rw [osiiEquation66FlatTimeSpatialTensor_mixed, hzero, zero_mul]
      simp [Fprod, fflat, hpsi_zero]
    · by_contra hpx
      have hzero : chi p.2 = 0 :=
        image_eq_zero_of_notMem_tsupport hpx
      apply hp
      have hpsi_zero : psi (mix p) = 0 := by
        change osiiEquation66FlatTimeSpatialTensor (d := d) phi chi
            (osiiStep4MixedSpatialRealPoint d k p.1
              (section43SpatialFlatCLE d k p.2)) = 0
        rw [osiiEquation66FlatTimeSpatialTensor_mixed]
        simp [section43SpatialFlatSchwartzCLE_apply, hzero]
      simp [Fprod, fflat, hpsi_zero]
  have hsplit : Integrable Fprod := by
    exact (integrableOn_iff_integrable_of_support_subset hFprod_support).mp
      (hFprod_cont.integrableOn_compact hK)
  calc
    (((OSIIChapterV.orderedTransportDistribution
          (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
            OS D.cutoff D.cutoff_support)).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k chi)) phi) =
        OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support
            (section43NPointTimeSpatialTensor d k phi chi) := by
      rw [ContinuousLinearMap.comp_apply,
        OSIIChapterV.orderedTransportDistribution_orderedPullbackTimeSpatialTensor,
        section43TimeSpatialTensorCLM_apply]
    _ = ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d))) psi := by
      rw [ContinuousLinearMap.comp_apply,
        unflattenSchwartzNPoint_osiiEquation66FlatTimeSpatialTensor]
    _ = ∫ y : Fin (k * (d + 1)) → ℝ, fflat y := by
      simpa [fflat, H] using hfull
    _ = ∫ tau : Fin k → ℝ,
          ∫ x : Fin (k * d) → ℝ,
            fflat (osiiStep4MixedSpatialRealPoint d k tau x) := by
      exact integral_eq_iterated_integral_osiiStep4MixedSpatialRealPoint
        fflat (by simpa [Fprod, mix] using hsplit)
    _ = ∫ tau : Fin k → ℝ,
          osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing
            lgc D tau chi * phi tau := by
      apply integral_congr_ae
      filter_upwards with tau
      calc
        (∫ x : Fin (k * d) → ℝ,
            fflat (osiiStep4MixedSpatialRealPoint d k tau x)) =
            ∫ x : Fin (k * d) → ℝ,
              (H (osiiStep4MixedSpatialRealPoint d k tau x) *
                section43SpatialFlatSchwartzCLE d k chi x) * phi tau := by
          apply integral_congr_ae
          filter_upwards with x
          simp [fflat, psi]
          ring
        _ = (∫ x : Fin (k * d) → ℝ,
              H (osiiStep4MixedSpatialRealPoint d k tau x) *
                section43SpatialFlatSchwartzCLE d k chi x) * phi tau :=
          integral_mul_const (μ :=
            (volume : Measure (Fin (k * d) → ℝ))) (phi tau)
              (fun x ↦ H (osiiStep4MixedSpatialRealPoint d k tau x) *
                section43SpatialFlatSchwartzCLE d k chi x)

/-- Distributional uniqueness identifies the compact spatial pairing with
the canonical stage orbit throughout the retained real-time region. -/
theorem osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_eq_edgeOrbit
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hchi : HasCompactSupport
      (chi : Section43SpatialSpace d k → ℂ)) :
    Set.EqOn
      (fun tau ↦
        osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing lgc D tau chi)
      (fun tau ↦ D.edge.orbit tau chi)
      D.realRegion := by
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    ((OSIIChapterV.orderedTransportDistribution
        (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support)).comp
      (section43OrderedPullbackTimeSpatialTensorCLM d k chi))
  have hcandidate :=
    osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_represents
      lgc D chi hchi
  have horbit := D.edge.represents chi
  have hcandidate_cont :=
    continuousOn_osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing
      lgc D chi hchi
  have horbit_cont : ContinuousOn
      (fun tau ↦ D.edge.orbit tau chi) D.realRegion :=
    stage.continuousOn_positiveRealEdge
      D.edge.orbit D.realRegion D.edge.stageEdge chi
  have heq := SCV.eqOn_inter_of_representsDistributionOn
    T D.realRegion D.realRegion
    (fun tau ↦
      osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing lgc D tau chi)
    (fun tau ↦ D.edge.orbit tau chi)
    D.realRegion_open D.realRegion_open
    hcandidate_cont horbit_cont hcandidate horbit
  intro tau htau
  exact heq ⟨htau, htau⟩

/-- On a retained real-time slice, the physical spatial pairing is exactly
the equation-(6.6) mixed-spatial density pairing. -/
theorem osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_eq_mixed
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (tau : Fin k → ℝ) (htau : tau ∈ D.realRegion)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing lgc D tau chi =
      ∫ x : Fin (k * d) → ℝ,
        osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
            (D.realRegion_subset_strictPositive htau) x *
          section43SpatialFlatSchwartzCLE d k chi x := by
  apply integral_congr_ae
  filter_upwards with x
  rw [osiiEquation66OSBuiltCanonicalPhysicalDensity_mixedSpatialRealPoint
    lgc D tau htau x]

/-- Compactly supported spatial tests satisfy the exact VI.1 real-edge
representation formula on every retained canonical edge. -/
theorem osiiEquation66OSBuiltMixedSpatialDensity_stageDistribution_eq
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (tau : Fin k → ℝ) (htau : tau ∈ D.realRegion)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hchi : HasCompactSupport
      (chi : Section43SpatialSpace d k → ℂ)) :
    stage.distribution (osiiPositiveRealTimeEmbed tau) chi =
      ∫ x : Fin (k * d) → ℝ,
        osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
            (D.realRegion_subset_strictPositive htau) x *
          section43SpatialFlatSchwartzCLE d k chi x := by
  have hstage := congrArg
    (fun R : OSIISpatialDistribution d k ↦ R chi)
    (D.edge.stageEdge tau htau).2
  change stage.distribution (osiiPositiveRealTimeEmbed tau) chi =
    D.edge.orbit tau chi at hstage
  calc
    stage.distribution (osiiPositiveRealTimeEmbed tau) chi =
        D.edge.orbit tau chi := hstage
    _ = osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing
          lgc D tau chi :=
      (osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_eq_edgeOrbit
        lgc D chi hchi htau).symm
    _ = _ :=
      osiiEquation66OSBuiltCanonicalPhysicalSpatialPairing_eq_mixed
        lgc D tau htau chi

/-- At a fixed positive real time, integration against the polynomially
bounded OS-built density is a continuous functional on the full native
spatial Schwartz space. -/
theorem exists_osiiEquation66OSBuiltMixedSpatialDensity_integralCLM
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    (tau : Fin k → ℝ)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    ∃ T : SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ,
      ∀ chi : SchwartzMap (Section43SpatialSpace d k) ℂ,
        T chi =
          ∫ x : Fin (k * d) → ℝ,
            osiiEquation66OSBuiltMixedSpatialDensity
                d OS lgc tau htau x *
              section43SpatialFlatSchwartzCLE d k chi x := by
  let F : (Fin (k * d) → ℝ) → ℂ :=
    osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau
  let N : ℕ := G.scaleDegree + G.growthDegree
  let A : ℝ :=
    (equation66E0PolynomialConstant G *
        16 ^ (2 * G.scaleDegree)) *
      (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^
        (G.scaleDegree + G.growthDegree) *
      (1 + (osiiTimeBoundaryDistance k
        (osiiPositiveRealTimeEmbed tau))⁻¹) ^
        (2 * G.scaleDegree)
  have hF : Continuous F := by
    exact continuous_osiiEquation66OSBuiltMixedSpatialDensity
      d OS lgc tau htau
  have hA : 0 ≤ A := by
    have hC : 0 ≤ equation66E0PolynomialConstant G :=
      equation66E0PolynomialConstant_nonneg G
    have hzeta :
        osiiPositiveRealTimeEmbed tau ∈ osiiTimeRightHalfPlane k :=
      (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
    have hdist : 0 < osiiTimeBoundaryDistance k
        (osiiPositiveRealTimeEmbed tau) :=
      osiiTimeBoundaryDistance_pos
        (Nat.pos_of_ne_zero (NeZero.ne k)) hzeta
    have hboundary : 0 ≤
        (1 + (osiiTimeBoundaryDistance k
          (osiiPositiveRealTimeEmbed tau))⁻¹) ^
            (2 * G.scaleDegree) :=
      pow_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hdist.le)) _
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (pow_nonneg (by norm_num) _))
        (pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _))
      hboundary
  have hgrowth : ∀ x : Fin (k * d) → ℝ,
      ‖F x‖ ≤ A * (1 + ‖x‖) ^ N := by
    intro x
    simpa [F, A, N, mul_assoc] using
      osiiEquation66OSBuiltMixedSpatialDensity_norm_le
        d OS lgc G tau htau x
  have hint : ∀ phi : SchwartzMap (Fin (k * d) → ℝ) ℂ,
      Integrable (fun x ↦ F x * phi x) := by
    intro phi
    exact SCV.integrable_poly_growth_schwartz F
      hF.aestronglyMeasurable A N hgrowth phi
  obtain ⟨s, K, hK, hpoly⟩ :=
    exists_polynomialGrowth_integral_schwartz_bound (k * d) N
  let Tflat : SchwartzMap (Fin (k * d) → ℝ) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun phi ↦ ∫ x, F x * phi x)
      (by
        intro phi psi
        simp only [SchwartzMap.add_apply, mul_add]
        exact integral_add (hint phi) (hint psi))
      (by
        intro a phi
        simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [show ∀ x : Fin (k * d) → ℝ,
          F x * (a * phi x) = a * (F x * phi x) by
            intro x
            ring]
        exact integral_const_mul a _)
      (by
        refine ⟨s, A * K, mul_nonneg hA hK.le, ?_⟩
        intro phi
        simpa [mul_assoc] using hpoly F hF A hA hgrowth phi)
  let T : SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ :=
    Tflat.comp (section43SpatialFlatSchwartzCLE d k).toContinuousLinearMap
  refine ⟨T, ?_⟩
  intro chi
  rfl

/-- The compact-support restriction is removable: the exact density formula
holds for every spatial Schwartz test. -/
theorem osiiEquation66OSBuiltMixedSpatialDensity_stageDistribution_eq_all
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k → ℝ)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (tau : Fin k → ℝ) (htau : tau ∈ D.realRegion)
    (chi : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    stage.distribution (osiiPositiveRealTimeEmbed tau) chi =
      ∫ x : Fin (k * d) → ℝ,
        osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
            (D.realRegion_subset_strictPositive htau) x *
          section43SpatialFlatSchwartzCLE d k chi x := by
  obtain ⟨T, hT⟩ :=
    exists_osiiEquation66OSBuiltMixedSpatialDensity_integralCLM
      lgc G tau (D.realRegion_subset_strictPositive htau)
  have heq :
      stage.distribution (osiiPositiveRealTimeEmbed tau) = T := by
    apply ContinuousLinearMap.eq_of_eq_on_dense
      (stage.distribution (osiiPositiveRealTimeEmbed tau)) T
      (dense_section43Spatial_hasCompactSupport d k)
    intro psi hpsi
    rw [hT]
    exact osiiEquation66OSBuiltMixedSpatialDensity_stageDistribution_eq
      lgc D tau htau psi hpsi
  rw [heq, hT]

end OSReconstruction

