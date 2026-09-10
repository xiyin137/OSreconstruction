/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltSpatialAtlasCoherence
import OSReconstruction.SCV.DistributionalRepresentationGluing











noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Classical
namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

variable {d k : Nat} [NeZero d] [NeZero k]

/-- The half-time reduced displacement used to recenter a local Weyl chart at
its physical spacetime center. -/
def osiiEquation66PhysicalChartGap
    (tau : Fin k -> Real) : Fin (k * (d + 1)) -> Real :=
  osiiEquation66SpatialChartGap d k tau

/-- Physical carrier obtained by shifting the local Weyl carrier from `XiHat`
to the original mixed spacetime center. -/
def osiiEquation66OSBuiltPhysicalFullCarrier
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    Set (Fin (k * (d + 1)) -> Real) :=
  {y | y - osiiEquation66PhysicalChartGap (d := d) tau ∈
    osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base}

/-- The local Weyl density in physical reduced-spacetime coordinates. -/
noncomputable def osiiEquation66OSBuiltPhysicalFullDensity
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real)
    (y : Fin (k * (d + 1)) -> Real) : Complex :=
  osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base
    (y - osiiEquation66PhysicalChartGap (d := d) tau)

/-- Time projection of flattened reduced spacetime coordinates. -/
def osiiEquation66FlatTime
    (y : Fin (k * (d + 1)) -> Real) : Fin k -> Real :=
  fun i => y (finProdFinEquiv (i, (0 : Fin (d + 1))))

/-- The cumulative half-time point translation descends to the corresponding
negative reduced gap translation. -/
theorem reducedConfigurationDisplacement_neg_osiiEquation66SpatialChartPointTranslation
    (tau : Fin k -> Real) :
    OSIIChapterV.reducedConfigurationDisplacement
        (fun j => -osiiEquation66SpatialChartPointTranslation d k tau j) =
      fun i => -osiiAxisPairUnflattenRealBlocks (d := d)
        (osiiEquation66PhysicalChartGap (d := d) tau) i := by
  funext i mu
  rw [OSIIChapterV.reducedConfigurationDisplacement_apply]
  simp only [Pi.neg_apply]
  have hsucc := diffVarSection_succ (d := d) k
    (fun i mu => osiiEquation66SpatialChartGap d k tau
      (finProdFinEquiv (i, mu))) i mu
  change
    -(osiiEquation66SpatialChartPointTranslation d k tau i.succ mu) -
        -(osiiEquation66SpatialChartPointTranslation d k tau i.castSucc mu) = _
  rw [show osiiEquation66SpatialChartPointTranslation d k tau i.succ mu =
      osiiEquation66SpatialChartPointTranslation d k tau i.castSucc mu +
        osiiEquation66SpatialChartGap d k tau
          (finProdFinEquiv (i, mu)) by
    simpa [osiiEquation66SpatialChartPointTranslation] using hsucc]
  simp [osiiEquation66PhysicalChartGap,
    osiiAxisPairUnflattenRealBlocks_apply]

/-- In flattened coordinates, translating by the negative physical chart gap
is the reduction of the negative cumulative point translation. -/
theorem diffVarReduction_translate_neg_osiiEquation66Point
    (tau : Fin k -> Real)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    diffVarReduction d k
        (translateSchwartzConfiguration
          (fun j => -osiiEquation66SpatialChartPointTranslation d k tau j)
          (BHW.reducedTestLift k d
            (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
            (unflattenSchwartzNPoint (d := d) phi))) =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz
          (-osiiEquation66PhysicalChartGap (d := d) tau) phi) := by
  rw [OSIIChapterV.diffVarReduction_translateSchwartzConfiguration,
    OSIIChapterV.diffVarReduction_reducedTestLift,
    reducedConfigurationDisplacement_neg_osiiEquation66SpatialChartPointTranslation]
  calc
    translateSchwartzConfiguration
          (fun i => -osiiAxisPairUnflattenRealBlocks (d := d)
            (osiiEquation66PhysicalChartGap (d := d) tau) i)
          (unflattenSchwartzNPoint (d := d) phi) =
        translateSchwartzConfiguration
          (osiiAxisPairUnflattenRealBlocks (d := d)
            (-osiiEquation66PhysicalChartGap (d := d) tau))
          (unflattenSchwartzNPoint (d := d) phi) := by
      congr 2
    _ = unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz
            (-osiiEquation66PhysicalChartGap (d := d) tau) phi) :=
      (unflattenSchwartzNPoint_translateSchwartz
        (-osiiEquation66PhysicalChartGap (d := d) tau) phi).symm

/-- A test translated from local-Weyl coordinates to physical coordinates has
reduced time in `V` whenever its original support lies over `V`. -/
theorem translatedEquation66ReducedTestLift_reducedTimeSupport
    (tau : Fin k -> Real)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (V : Set (Fin k -> Real))
    (hphi : tsupport (phi : (Fin (k * (d + 1)) -> Real) -> Complex) ⊆
      {x | osiiEquation66FlatTime (d := d)
        (x + osiiEquation66PhysicalChartGap (d := d) tau) ∈ V}) :
    forall x,
      x ∈ tsupport
        ((translateSchwartzConfiguration
            (fun j => -osiiEquation66SpatialChartPointTranslation d k tau j)
            (BHW.reducedTestLift k d
              (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
              (unflattenSchwartzNPoint (d := d) phi)) :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) -> Complex) ->
        OSIIChapterV.reducedTimeProjectionCLM d k x ∈ V := by
  apply OSIIChapterV.translatedReducedTestLift_reducedTimeSupport
  intro xi hxi
  rw [reducedConfigurationDisplacement_neg_osiiEquation66SpatialChartPointTranslation]
    at hxi
  have hunflat :
      translateSchwartzConfiguration
          (fun i => -osiiAxisPairUnflattenRealBlocks (d := d)
            (osiiEquation66PhysicalChartGap (d := d) tau) i)
          (unflattenSchwartzNPoint (d := d) phi) =
        unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz
            (-osiiEquation66PhysicalChartGap (d := d) tau) phi) := by
    calc
      translateSchwartzConfiguration
            (fun i => -osiiAxisPairUnflattenRealBlocks (d := d)
              (osiiEquation66PhysicalChartGap (d := d) tau) i)
            (unflattenSchwartzNPoint (d := d) phi) =
          translateSchwartzConfiguration
            (osiiAxisPairUnflattenRealBlocks (d := d)
              (-osiiEquation66PhysicalChartGap (d := d) tau))
            (unflattenSchwartzNPoint (d := d) phi) := by
        congr 2
      _ = unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz
              (-osiiEquation66PhysicalChartGap (d := d) tau) phi) :=
        (unflattenSchwartzNPoint_translateSchwartz
          (-osiiEquation66PhysicalChartGap (d := d) tau) phi).symm
  rw [hunflat] at hxi
  have hflat :
      flattenCLEquivReal k (d + 1) xi ∈
        tsupport
          (SCV.translateSchwartz
            (-osiiEquation66PhysicalChartGap (d := d) tau) phi :
              (Fin (k * (d + 1)) -> Real) -> Complex) := by
    have hpre := tsupport_comp_subset_preimage
      (SCV.translateSchwartz
        (-osiiEquation66PhysicalChartGap (d := d) tau) phi :
          (Fin (k * (d + 1)) -> Real) -> Complex)
      (flattenCLEquivReal k (d + 1)).continuous hxi
    simpa [unflattenSchwartzNPoint_apply] using hpre
  rw [OSIIChapterV.tsupport_translateSchwartz_eq_preimage] at hflat
  change flattenCLEquivReal k (d + 1) xi +
      (-osiiEquation66PhysicalChartGap (d := d) tau) ∈
        tsupport (phi : (Fin (k * (d + 1)) -> Real) -> Complex) at hflat
  have hlocal := hphi hflat
  have htime :
      osiiEquation66FlatTime (d := d)
          (flattenCLEquivReal k (d + 1) xi) =
        fun i => xi i 0 := by
    funext i
    simp [osiiEquation66FlatTime, flattenCLEquivReal_apply]
  change osiiEquation66FlatTime (d := d)
      ((flattenCLEquivReal k (d + 1) xi +
        -osiiEquation66PhysicalChartGap (d := d) tau) +
          osiiEquation66PhysicalChartGap (d := d) tau) ∈ V at hlocal
  have hcancel :
      (flattenCLEquivReal k (d + 1) xi +
        -osiiEquation66PhysicalChartGap (d := d) tau) +
          osiiEquation66PhysicalChartGap (d := d) tau =
        flattenCLEquivReal k (d + 1) xi := by
    abel
  rw [hcancel, htime] at hlocal
  simpa [section43QTime, nPointTimeSpatialCLE] using hlocal

/-- Before shifting back to physical coordinates, one local Weyl density
represents the canonical reduced Schwinger distribution with the negative
half-time test translation. -/
theorem osiiEquation66OSBuiltSpatialFullDensity_represents_canonicalTranslated
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {compactCarrier : Set (Fin k -> Real)}
    (C : OSIIChapterV.CanonicalReducedCompactCutoffData compactCarrier)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    SCV.RepresentsDistributionOn
      (((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d))).comp
          (SCV.translateSchwartzCLM
            (-osiiEquation66PhysicalChartGap (d := d) tau)))
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base ∩
        {x | osiiEquation66FlatTime (d := d)
          (x + osiiEquation66PhysicalChartGap (d := d) tau) ∈
            C.realRegion}) := by
  intro phi hphi
  let rho := osiiChapterVIRegularizationRadius k
    (osiiPositiveRealTimeEmbed tau)
  have hrho : 0 < rho := by
    exact osiiChapterVIRegularizationRadius_pos
      (Nat.pos_of_ne_zero (NeZero.ne k))
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau)
  have hsupp :
      Function.support
          (flattenSchwartzNPoint (d := d)
            (unflattenSchwartzNPoint (d := d) phi)) ⊆
        Metric.closedBall
          (osiiStep4MultiGapXiHatCenter d k
            (osiiStep4MixedSpatialRealPoint d k tau base)) (rho / 4) := by
    rw [flattenSchwartzNPoint_unflattenSchwartzNPoint,
      osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]
    intro x hx
    have hxchart := (hphi.2 (subset_tsupport _ hx)).1
    change dist x (osiiEquation66SpatialLocalPoint d k tau base) <
      osiiEquation66OSBuiltSpatialLocalScale
        d OS lgc tau htau base / 4 at hxchart
    rw [Metric.mem_closedBall]
    have hscale :=
      (osiiEquation66OSBuiltSpatialLocalWeylData
        d OS lgc tau htau base).data.scale_le
    change osiiEquation66OSBuiltSpatialLocalScale
      d OS lgc tau htau base <= rho / 2 at hscale
    exact hxchart.le.trans (by linarith)
  have hsch :=
    (osiiEquation66OSBuiltSpatialAngularData d OS lgc tau htau base
      ).imaginarySliceFamily_zero_apply_eq_schwinger_translate_of_flatSupport
        (unflattenSchwartzNPoint (d := d) phi) hsupp
  let Z := osiiEquation66QuantitativeSynchronizedData
    d k hrho (osiiStep4MixedSpatialRealPoint d k tau base)
      (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
        d k tau htau base)
  have htrans :
      (fun i => -osiiAxisPairChronologicalPointTranslation Z.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Z.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 j a).re) i) =
        fun i => -osiiEquation66SpatialChartPointTranslation d k tau i := by
    funext i
    have hpoint := osiiEquation66SpatialZeroTargetPointTranslation
      d k Z.uniform.T (lt_trans zero_lt_one Z.uniform.hT)
        tau htau base
    have hT : Z.coherent.T = Z.uniform.T := rfl
    rw [hT, hpoint]
  let f : SchwartzNPoint d (k + 1) :=
    translateSchwartzConfiguration
      (fun j => -osiiEquation66SpatialChartPointTranslation d k tau j)
      (BHW.reducedTestLift k d
        (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
        (unflattenSchwartzNPoint (d := d) phi))
  have hregion :
      forall x, x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
        OSIIChapterV.reducedTimeProjectionCLM d k x ∈ C.realRegion := by
    exact translatedEquation66ReducedTestLift_reducedTimeSupport
      tau phi C.realRegion (fun x hx => (hphi.2 hx).2)
  have hone :
      forall x, x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
        OSIIChapterV.reducedTimeCutoffWeight (d := d) C.cutoff x = 1 := by
    intro x hx
    rw [OSIIChapterV.reducedTimeCutoffWeight]
    exact C.cutoff_one_on _ (hregion x hx)
  have hf_disjoint :
      Disjoint (tsupport (f : NPointDomain d (k + 1) -> Complex))
        (CoincidenceLocus d (k + 1)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hxweight :
        x ∈ tsupport
          (OSIIChapterV.reducedTimeCutoffWeight (d := d) C.cutoff) :=
      subset_tsupport
        (OSIIChapterV.reducedTimeCutoffWeight (d := d) C.cutoff)
        (by
          change OSIIChapterV.reducedTimeCutoffWeight
            (d := d) C.cutoff x ≠ 0
          rw [hone x hx]
          exact one_ne_zero)
    exact Set.disjoint_left.mp
      (OSIIChapterV.reducedTimeCutoffWeight_tsupport_disjoint
        C.cutoff C.cutoff_support) hxweight hcoin
  have hf : VanishesToInfiniteOrderOnCoincidence f :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint f hf_disjoint
  have hred :
      diffVarReduction d k f =
        unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz
            (-osiiEquation66PhysicalChartGap (d := d) tau) phi) := by
    exact diffVarReduction_translate_neg_osiiEquation66Point tau phi
  have hcanonical :
      OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support (diffVarReduction d k f) =
        OS.S (k + 1) ⟨f, hf⟩ :=
    C.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport_realRegion
      f hf hregion
  have hsch' :
      osiiEquation66OSBuiltSpatialFlatZeroDistribution
          d OS lgc tau htau base phi =
        OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical f) := by
    rw [show (fun i => -osiiAxisPairChronologicalPointTranslation Z.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Z.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 j a).re) i) =
      fun i => -osiiEquation66SpatialChartPointTranslation d k tau i from htrans]
      at hsch
    simpa [osiiEquation66OSBuiltSpatialFlatZeroDistribution, f] using hsch
  calc
    (((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d))).comp
          (SCV.translateSchwartzCLM
            (-osiiEquation66PhysicalChartGap (d := d) tau))) phi =
        OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support (diffVarReduction d k f) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        SCV.translateSchwartzCLM_apply, hred]
    _ = OS.S (k + 1) ⟨f, hf⟩ := hcanonical
    _ = OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical f) := by
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes f hf]
    _ = osiiEquation66OSBuiltSpatialFlatZeroDistribution
          d OS lgc tau htau base phi := hsch'.symm
    _ = ∫ x, osiiEquation66OSBuiltSpatialFullDensity
          d OS lgc tau htau base x * phi x :=
      osiiEquation66OSBuiltSpatialFullDensity_represents
        d OS lgc tau htau base phi
          ⟨hphi.1, hphi.2.trans Set.inter_subset_left⟩

/-- After shifting the chart from `XiHat` to its physical center, the local
density represents the unshifted canonical reduced Schwinger distribution. -/
theorem osiiEquation66OSBuiltPhysicalFullDensity_represents_canonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {compactCarrier : Set (Fin k -> Real)}
    (C : OSIIChapterV.CanonicalReducedCompactCutoffData compactCarrier)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    SCV.RepresentsDistributionOn
      ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d)))
      (osiiEquation66OSBuiltPhysicalFullDensity OS lgc tau htau base)
      (osiiEquation66OSBuiltPhysicalFullCarrier OS lgc tau htau base ∩
        {y | osiiEquation66FlatTime (d := d) y ∈ C.realRegion}) := by
  have htranslated :=
    osiiEquation66OSBuiltSpatialFullDensity_represents_canonicalTranslated
      OS lgc C tau htau base
  have hphysical := SCV.representsDistributionOn_of_translate
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C.cutoff C.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d)))
    (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
    (osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base ∩
      {x | osiiEquation66FlatTime (d := d)
        (x + osiiEquation66PhysicalChartGap (d := d) tau) ∈ C.realRegion})
    (osiiEquation66PhysicalChartGap (d := d) tau) htranslated
  intro psi hpsi
  apply hphysical psi
  constructor
  · exact hpsi.1
  · intro y hy
    have hyphysical := hpsi.2 hy
    constructor
    · exact hyphysical.1
    · change osiiEquation66FlatTime (d := d)
        ((y - osiiEquation66PhysicalChartGap (d := d) tau) +
          osiiEquation66PhysicalChartGap (d := d) tau) ∈ C.realRegion
      simpa using hyphysical.2

/-- Subtracting the half-time chart gap from a physical mixed point gives its
local Weyl coordinate. -/
theorem osiiStep4MixedSpatialRealPoint_sub_physicalChartGap
    (tau : Fin k -> Real)
    (x : Fin (k * d) -> Real) :
    osiiStep4MixedSpatialRealPoint d k tau x -
        osiiEquation66PhysicalChartGap (d := d) tau =
      osiiEquation66SpatialLocalPoint d k tau x := by
  funext q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simp [osiiStep4MixedSpatialRealPoint,
        osiiEquation66PhysicalChartGap, osiiEquation66SpatialChartGap,
        osiiEquation66SpatialLocalPoint]
      ring
  | succ j =>
      simp [osiiStep4MixedSpatialRealPoint,
        osiiEquation66PhysicalChartGap, osiiEquation66SpatialChartGap,
        osiiEquation66SpatialLocalPoint]

/-- The physical chart restricted to its named time slice is exactly the
fixed-time local spatial chart. -/
theorem osiiEquation66OSBuiltPhysicalFullDensity_mixedSpatialRealPoint
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base x : Fin (k * d) -> Real) :
    osiiEquation66OSBuiltPhysicalFullDensity OS lgc tau htau base
        (osiiStep4MixedSpatialRealPoint d k tau x) =
      osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base x := by
  simp only [osiiEquation66OSBuiltPhysicalFullDensity,
    osiiEquation66OSBuiltSpatialFullDensity,
    osiiEquation66OSBuiltSpatialLocalDensity]
  rw [osiiStep4MixedSpatialRealPoint_sub_physicalChartGap]

/-- Spatial coordinates extracted from a flattened reduced-spacetime point. -/
def osiiEquation66FlatSpatial
    (y : Fin (k * (d + 1)) -> Real) : Fin (k * d) -> Real :=
  fun q =>
    y (finProdFinEquiv
      ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2.succ))

/-- Flat time and spatial extraction reconstructs the original point. -/
theorem osiiStep4MixedSpatialRealPoint_flatTime_flatSpatial
    (y : Fin (k * (d + 1)) -> Real) :
    osiiStep4MixedSpatialRealPoint d k
        (osiiEquation66FlatTime (d := d) y)
        (osiiEquation66FlatSpatial (d := d) y) = y := by
  funext q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simp [osiiStep4MixedSpatialRealPoint, osiiEquation66FlatTime]
  | succ j =>
      simp [osiiStep4MixedSpatialRealPoint, osiiEquation66FlatSpatial]

theorem continuous_osiiEquation66FlatTime :
    Continuous (osiiEquation66FlatTime (d := d) (k := k)) :=
  continuous_pi fun i => continuous_apply _

theorem isOpen_osiiEquation66OSBuiltPhysicalFullCarrier
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    IsOpen (osiiEquation66OSBuiltPhysicalFullCarrier
      OS lgc tau htau base) := by
  exact Metric.isOpen_ball.preimage
    (continuous_id.sub continuous_const)

theorem continuousOn_osiiEquation66OSBuiltPhysicalFullDensity
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    ContinuousOn
      (osiiEquation66OSBuiltPhysicalFullDensity OS lgc tau htau base)
      (osiiEquation66OSBuiltPhysicalFullCarrier OS lgc tau htau base) := by
  exact
    (continuousOn_osiiEquation66OSBuiltSpatialFullDensity
      d OS lgc tau htau base).comp
        (continuous_id.sub continuous_const).continuousOn
        (fun _ hy => hy)

theorem osiiEquation66OSBuiltPhysicalFullCarrier_center
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    osiiStep4MixedSpatialRealPoint d k tau base ∈
      osiiEquation66OSBuiltPhysicalFullCarrier OS lgc tau htau base := by
  change osiiStep4MixedSpatialRealPoint d k tau base -
      osiiEquation66PhysicalChartGap (d := d) tau ∈
    Metric.ball (osiiEquation66SpatialLocalPoint d k tau base)
      (osiiEquation66OSBuiltSpatialLocalScale
        d OS lgc tau htau base / 4)
  rw [osiiStep4MixedSpatialRealPoint_sub_physicalChartGap,
    Metric.mem_ball, dist_self]
  exact div_pos
    (osiiEquation66OSBuiltSpatialLocalScale_pos
      d OS lgc tau htau base) (by norm_num)

/-- Chart indices over one canonical Chapter V real-time region. -/
def osiiEquation66OSBuiltPhysicalAtlasIndex
    {OS : OsterwalderSchraderAxioms d}
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :=
  {tau : Fin k -> Real // tau ∈ D.realRegion} ×
    (Fin (k * d) -> Real)

def osiiEquation66OSBuiltPhysicalAtlasCarrier
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    Set (Fin (k * (d + 1)) -> Real) :=
  osiiEquation66OSBuiltPhysicalFullCarrier OS lgc a.1.1
      (D.realRegion_subset_strictPositive a.1.2) a.2 ∩
    {y | osiiEquation66FlatTime (d := d) y ∈ D.realRegion}

noncomputable def osiiEquation66OSBuiltPhysicalAtlasDensity
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    (Fin (k * (d + 1)) -> Real) -> Complex :=
  osiiEquation66OSBuiltPhysicalFullDensity OS lgc a.1.1
    (D.realRegion_subset_strictPositive a.1.2) a.2

theorem isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    IsOpen (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a) := by
  exact
    (isOpen_osiiEquation66OSBuiltPhysicalFullCarrier
      OS lgc a.1.1 (D.realRegion_subset_strictPositive a.1.2) a.2).inter
        (D.realRegion_open.preimage continuous_osiiEquation66FlatTime)

theorem continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    ContinuousOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a)
      (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a) :=
  (continuousOn_osiiEquation66OSBuiltPhysicalFullDensity
    OS lgc a.1.1 (D.realRegion_subset_strictPositive a.1.2) a.2).mono
      Set.inter_subset_left

theorem osiiEquation66OSBuiltPhysicalAtlasDensity_represents
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    SCV.RepresentsDistributionOn
      ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d)))
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a)
      (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a) :=
  osiiEquation66OSBuiltPhysicalFullDensity_represents_canonical
    OS lgc D.toCutoffData a.1.1
      (D.realRegion_subset_strictPositive a.1.2) a.2

theorem osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (a b : osiiEquation66OSBuiltPhysicalAtlasIndex D) :
    Set.EqOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a)
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D b)
      (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a ∩
        osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D b) := by
  exact SCV.eqOn_inter_of_representsDistributionOn
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D.cutoff D.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d)))
    (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a)
    (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D b)
    (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a)
    (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D b)
    (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a)
    (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D b)
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a)
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D b)
    (osiiEquation66OSBuiltPhysicalAtlasDensity_represents lgc D a)
    (osiiEquation66OSBuiltPhysicalAtlasDensity_represents lgc D b)

/-- The physical atlas covers every reduced-spacetime point over the canonical
real-time region. -/
theorem osiiEquation66OSBuiltPhysicalAtlas_covers
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈ D.realRegion} ⊆
      Set.iUnion (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D) := by
  intro y hy
  let tau : {tau : Fin k -> Real // tau ∈ D.realRegion} :=
    ⟨osiiEquation66FlatTime (d := d) y, hy⟩
  let base := osiiEquation66FlatSpatial (d := d) y
  let a : osiiEquation66OSBuiltPhysicalAtlasIndex D := (tau, base)
  apply Set.mem_iUnion_of_mem a
  constructor
  · rw [← osiiStep4MixedSpatialRealPoint_flatTime_flatSpatial (d := d) y]
    exact osiiEquation66OSBuiltPhysicalFullCarrier_center OS lgc tau.1
      (D.realRegion_subset_strictPositive tau.2) base
  · exact hy

/-- The canonical physical density obtained by gluing all local Weyl charts
over one retained Chapter V real-time region. -/
noncomputable def osiiEquation66OSBuiltCanonicalPhysicalDensity
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    (Fin (k * (d + 1)) -> Real) -> Complex :=
  SCV.glued_iUnion
    (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D)
    (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D)

/-- The glued physical density represents the canonical reduced Schwinger
distribution throughout the complete retained real-time region. -/
theorem osiiEquation66OSBuiltCanonicalPhysicalDensity_represents
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    SCV.RepresentsDistributionOn
      ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d)))
      (osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D)
      {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
  exact SCV.representsDistributionOn_glued_iUnion
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D.cutoff D.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d)))
    (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D)
    (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D)
    {y : Fin (k * (d + 1)) -> Real |
      osiiEquation66FlatTime (d := d) y ∈ D.realRegion}
    (osiiEquation66OSBuiltPhysicalAtlas_covers lgc D)
    (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D)
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D)
    (osiiEquation66OSBuiltPhysicalAtlasDensity_represents lgc D)
    (osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter lgc D)

theorem continuousOn_osiiEquation66OSBuiltCanonicalPhysicalDensity
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    ContinuousOn
      (osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D)
      {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
  intro y hy
  rcases Set.mem_iUnion.mp
      (osiiEquation66OSBuiltPhysicalAtlas_covers lgc D hy) with
    ⟨a, hya⟩
  have hlocal :=
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a y hya
      ).continuousAt
      ((isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a).mem_nhds hya)
  have heq :
      osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D =ᶠ[nhds y]
        osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a := by
    filter_upwards [
      (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a).mem_nhds hya]
      with z hz
    exact SCV.glued_iUnion_eqOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter lgc D) a hz
  exact (hlocal.congr_of_eventuallyEq heq).continuousWithinAt

/-- On every retained positive-real slice, the glued physical density is the
canonical mixed-spatial density constructed by equation `(6.6)`. -/
theorem osiiEquation66OSBuiltCanonicalPhysicalDensity_mixedSpatialRealPoint
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSLinearGrowthCondition d OS)
    {stage : OSIITimeContinuationStage d k}
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (tau : Fin k -> Real)
    (htau : tau ∈ D.realRegion)
    (x : Fin (k * d) -> Real) :
    osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
        (osiiStep4MixedSpatialRealPoint d k tau x) =
      osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
        (D.realRegion_subset_strictPositive htau) x := by
  let a : osiiEquation66OSBuiltPhysicalAtlasIndex D := (⟨tau, htau⟩, x)
  have htime :
      osiiEquation66FlatTime (d := d)
          (osiiStep4MixedSpatialRealPoint d k tau x) = tau := by
    funext i
    simp [osiiEquation66FlatTime, osiiStep4MixedSpatialRealPoint]
  have hy : osiiStep4MixedSpatialRealPoint d k tau x ∈
      osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D a := by
    constructor
    · exact osiiEquation66OSBuiltPhysicalFullCarrier_center OS lgc tau
        (D.realRegion_subset_strictPositive htau) x
    · simpa [htime]
  calc
    osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D
          (osiiStep4MixedSpatialRealPoint d k tau x) =
        osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a
          (osiiStep4MixedSpatialRealPoint d k tau x) :=
      SCV.glued_iUnion_eqOn
        (osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter lgc D) a hy
    _ = osiiEquation66OSBuiltSpatialLocalDensity d OS lgc tau
          (D.realRegion_subset_strictPositive htau) x x :=
      osiiEquation66OSBuiltPhysicalFullDensity_mixedSpatialRealPoint
        OS lgc tau (D.realRegion_subset_strictPositive htau) x x
    _ = osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau
          (D.realRegion_subset_strictPositive htau) x :=
      osiiEquation66OSBuiltSpatialLocalDensity_self
        d OS lgc tau (D.realRegion_subset_strictPositive htau) x

end OSReconstruction
