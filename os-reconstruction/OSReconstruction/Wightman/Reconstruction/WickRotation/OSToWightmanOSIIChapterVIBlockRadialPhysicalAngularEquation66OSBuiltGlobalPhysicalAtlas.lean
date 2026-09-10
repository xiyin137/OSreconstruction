import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltPhysicalAtlas

/-!
# Global positive-real equation-(6.6) atlas

One canonical Chapter V cutoff only represents the Schwinger edge on its
local positive-time region.  This module ranges over every canonical compact
edge instead.  The local equation-(6.6) densities then glue on the complete
strict-positive Euclidean time region because different cutoffs agree on
tests supported where both cutoffs are one.

This is still a real-edge atlas.  It does not claim that the local Euclidean
charts cover the complex forward tube; that later continuation step is a
separate Malgrange-Zerner obligation.
-/

noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {stage : OSIITimeContinuationStage d k}

/-- Two canonical reduced cutoff distributions agree on a flat test whose
time support lies where both cutoffs are one. -/
theorem canonicalReducedTimeCutoffSchwingerCLM_comp_unflatten_eq_of_flatSupport
    {K1 K2 : Set (Fin k -> Real)}
    (C1 : OSIIChapterV.CanonicalReducedCompactCutoffData K1)
    (C2 : OSIIChapterV.CanonicalReducedCompactCutoffData K2)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (hphi :
      tsupport (phi : (Fin (k * (d + 1)) -> Real) -> Complex) ⊆
        {x | osiiEquation66FlatTime (d := d) x ∈
          C1.realRegion ∩ C2.realRegion}) :
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C1.cutoff C1.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d))) phi =
      ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS C2.cutoff C2.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d))) phi := by
  let tau0 : Fin k -> Real := 0
  let f : SchwartzNPoint d (k + 1) :=
    translateSchwartzConfiguration
      (fun j => -osiiEquation66SpatialChartPointTranslation d k tau0 j)
      (BHW.reducedTestLift k d
        (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
        (unflattenSchwartzNPoint (d := d) phi))
  have hgap0 :
      osiiEquation66PhysicalChartGap (d := d) tau0 = 0 := by
    funext q
    obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
    cases mu using Fin.cases <;>
      simp [tau0, osiiEquation66PhysicalChartGap,
        osiiEquation66SpatialChartGap, osiiStep4MixedSpatialRealPoint]
  have hregion :
      forall x,
        x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
          OSIIChapterV.reducedTimeProjectionCLM d k x ∈
            C1.realRegion ∩ C2.realRegion := by
    apply translatedEquation66ReducedTestLift_reducedTimeSupport
      (d := d) (k := k) tau0 phi
        (C1.realRegion ∩ C2.realRegion)
    intro x hx
    rw [hgap0]
    simpa [osiiEquation66FlatTime] using hphi hx
  have hred :
      diffVarReduction d k f =
        unflattenSchwartzNPoint (d := d) phi := by
    simpa [f, hgap0] using
        (diffVarReduction_translate_neg_osiiEquation66Point
          (d := d) (k := k) tau0 phi)
  have hf_disjoint :
      Disjoint
        (tsupport (f : NPointDomain d (k + 1) -> Complex))
        (CoincidenceLocus d (k + 1)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hxweight :
        x ∈ tsupport
          (OSIIChapterV.reducedTimeCutoffWeight (d := d) C1.cutoff) :=
      subset_tsupport
        (OSIIChapterV.reducedTimeCutoffWeight (d := d) C1.cutoff)
        (by
          change OSIIChapterV.reducedTimeCutoffWeight
            (d := d) C1.cutoff x ≠ 0
          have hxregion :
              section43QTime (d := d) (n := k)
                  (BHW.reducedDiffMapReal (k + 1) d x) ∈
                C1.realRegion := by
            simpa [OSIIChapterV.reducedTimeProjectionCLM_apply] using
              (hregion x hx).1
          rw [OSIIChapterV.reducedTimeCutoffWeight,
            C1.cutoff_one_on _ hxregion]
          exact one_ne_zero)
    exact Set.disjoint_left.mp
      (OSIIChapterV.reducedTimeCutoffWeight_tsupport_disjoint
        C1.cutoff C1.cutoff_support) hxweight hcoin
  have hf : VanishesToInfiniteOrderOnCoincidence f :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint f hf_disjoint
  calc
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C1.cutoff C1.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d))) phi =
      OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C1.cutoff C1.cutoff_support (diffVarReduction d k f) := by
      rw [ContinuousLinearMap.comp_apply, hred]
    _ = OS.S (k + 1) ⟨f, hf⟩ :=
      C1.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport_realRegion
        f hf (fun x hx => (hregion x hx).1)
    _ = OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C2.cutoff C2.cutoff_support (diffVarReduction d k f) :=
      (C2.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport_realRegion
        f hf (fun x hx => (hregion x hx).2)).symm
    _ = ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS C2.cutoff C2.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d))) phi := by
      rw [ContinuousLinearMap.comp_apply, hred]

/- Physical local-Weyl densities selected from two different canonical
compact edges agree on their common real carrier. -/
set_option maxHeartbeats 2000000 in
theorem osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter_of_edges
    {K1 K2 : Set (Fin k -> Real)}
    (D1 : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage K1)
    (D2 : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage K2)
    (a1 : osiiEquation66OSBuiltPhysicalAtlasIndex D1)
    (a2 : osiiEquation66OSBuiltPhysicalAtlasIndex D2) :
    Set.EqOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D1 a1)
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2)
      (osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D1 a1 ∩
        osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D2 a2) := by
  let U :=
    osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D1 a1 ∩
      osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D2 a2
  let T1 :=
    (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D1.cutoff D1.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d))
  let T2 :=
    (OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D2.cutoff D2.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d))
  have hUopen : IsOpen U :=
    (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D1 a1).inter
      (isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc D2 a2)
  have h1cont : ContinuousOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D1 a1) U :=
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D1 a1).mono
      Set.inter_subset_left
  have h2cont : ContinuousOn
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2) U :=
    (continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2).mono
      Set.inter_subset_right
  have h1rep : SCV.RepresentsDistributionOn T1
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D1 a1) U := by
    intro phi hphi
    exact osiiEquation66OSBuiltPhysicalAtlasDensity_represents
      lgc D1 a1 phi
        ⟨hphi.1, hphi.2.trans Set.inter_subset_left⟩
  have h2rep : SCV.RepresentsDistributionOn T1
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2) U := by
    intro phi hphi
    calc
      T1 phi = T2 phi := by
        apply canonicalReducedTimeCutoffSchwingerCLM_comp_unflatten_eq_of_flatSupport
          (d := d) (k := k) (OS := OS)
          D1.toCutoffData D2.toCutoffData phi
        intro x hx
        have hxU := hphi.2 hx
        exact ⟨hxU.1.2, hxU.2.2⟩
      _ = ∫ x, osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2 x *
          phi x := by
        exact osiiEquation66OSBuiltPhysicalAtlasDensity_represents
          lgc D2 a2 phi
            ⟨hphi.1, hphi.2.trans Set.inter_subset_right⟩
  have hEq := SCV.eqOn_inter_of_representsDistributionOn
    T1 U U
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D1 a1)
      (osiiEquation66OSBuiltPhysicalAtlasDensity lgc D2 a2)
      hUopen hUopen h1cont h2cont h1rep h2rep
  simpa [U] using hEq

/-- One local equation-(6.6) chart together with the canonical compact edge
on which its positive-time real representation is valid. -/
def osiiEquation66OSBuiltGlobalPhysicalAtlasIndex
    (OS : OsterwalderSchraderAxioms d)
    (stage : OSIITimeContinuationStage d k) : Type :=
  Sigma fun compactCarrier : Set (Fin k -> Real) =>
    Sigma fun D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier =>
      osiiEquation66OSBuiltPhysicalAtlasIndex D

/-- Carrier of a chart in the all-compact-edge positive-real atlas. -/
def osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier
    (lgc : OSLinearGrowthCondition d OS)
    (stage : OSIITimeContinuationStage d k)
    (a : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage) :
    Set (Fin (k * (d + 1)) -> Real) :=
  osiiEquation66OSBuiltPhysicalAtlasCarrier lgc a.2.1 a.2.2

/-- Density of a chart in the all-compact-edge positive-real atlas. -/
noncomputable def osiiEquation66OSBuiltGlobalPhysicalAtlasDensity
    (lgc : OSLinearGrowthCondition d OS)
    (stage : OSIITimeContinuationStage d k)
    (a : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage) :
    (Fin (k * (d + 1)) -> Real) -> Complex :=
  osiiEquation66OSBuiltPhysicalAtlasDensity lgc a.2.1 a.2.2

theorem isOpen_osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier
    (a : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage) :
    IsOpen
      (osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage a) :=
  isOpen_osiiEquation66OSBuiltPhysicalAtlasCarrier lgc a.2.1 a.2.2

theorem continuousOn_osiiEquation66OSBuiltGlobalPhysicalAtlasDensity
    (a : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage) :
    ContinuousOn
      (osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage a)
      (osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage a) :=
  continuousOn_osiiEquation66OSBuiltPhysicalAtlasDensity lgc a.2.1 a.2.2

/-- All local densities in the all-compact-edge atlas agree on overlaps. -/
theorem osiiEquation66OSBuiltGlobalPhysicalAtlasDensity_eqOn_inter
    (a b : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage) :
    Set.EqOn
      (osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage a)
      (osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage b)
      (osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage a ∩
        osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage b) := by
  exact osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter_of_edges
    (d := d) (k := k) (OS := OS) (lgc := lgc) (stage := stage)
    a.2.1 b.2.1 a.2.2 b.2.2

/-- Canonical compact edges make the global equation-(6.6) atlas cover every
flattened Euclidean point with strict-positive reduced time. -/
theorem osiiEquation66OSBuiltGlobalPhysicalAtlas_covers
    (H : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage) :
    {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈
          section43TimeStrictPositiveRegion k} ⊆
      Set.iUnion
        (osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage) := by
  intro y hy
  let tau := osiiEquation66FlatTime (d := d) y
  obtain ⟨D⟩ := H {tau} isCompact_singleton (by
    intro sigma hsigma
    simpa only [Set.mem_singleton_iff] using hsigma ▸ hy)
  have htau : tau ∈ D.realRegion :=
    D.compactCarrier_subset (Set.mem_singleton tau)
  rcases Set.mem_iUnion.mp
      (osiiEquation66OSBuiltPhysicalAtlas_covers lgc D htau) with
    ⟨a, ha⟩
  exact Set.mem_iUnion.mpr ⟨⟨{tau}, D, a⟩, ha⟩

/-- The canonical positive-real equation-(6.6) density obtained by gluing all
compact-edge local charts. -/
noncomputable def osiiEquation66OSBuiltGlobalPhysicalDensity
    (lgc : OSLinearGrowthCondition d OS)
    (stage : OSIITimeContinuationStage d k) :
    (Fin (k * (d + 1)) -> Real) -> Complex :=
  SCV.glued_iUnion
    (osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage)
    (osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage)

/-- On each local chart, the globally glued positive-real density is the
original equation-(6.6) local Weyl density. -/
theorem osiiEquation66OSBuiltGlobalPhysicalDensity_eqOn_chart
    (a : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage)
    {y : Fin (k * (d + 1)) -> Real}
    (hy : y ∈ osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier lgc stage a) :
    osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage y =
      osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage a y :=
  SCV.glued_iUnion_eqOn
    (osiiEquation66OSBuiltGlobalPhysicalAtlasDensity_eqOn_inter
      (lgc := lgc) (stage := stage)) a hy

/-- On the real-time region retained by one canonical compact edge, the
all-edge global density is exactly the density glued from that edge alone. -/
theorem osiiEquation66OSBuiltGlobalPhysicalDensity_eq_canonicalPhysicalDensity_of_mem
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    {y : Fin (k * (d + 1)) -> Real}
    (hy : osiiEquation66FlatTime (d := d) y ∈ D.realRegion) :
    osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage y =
      osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D y := by
  rcases Set.mem_iUnion.mp
      (osiiEquation66OSBuiltPhysicalAtlas_covers lgc D hy) with
    ⟨a, hya⟩
  let ga : osiiEquation66OSBuiltGlobalPhysicalAtlasIndex OS stage :=
    ⟨compactCarrier, D, a⟩
  calc
    osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage y =
        osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage ga y := by
          apply osiiEquation66OSBuiltGlobalPhysicalDensity_eqOn_chart
            (lgc := lgc) (stage := stage) ga
          exact hya
    _ = osiiEquation66OSBuiltPhysicalAtlasDensity lgc D a y := by
          rfl
    _ = osiiEquation66OSBuiltCanonicalPhysicalDensity lgc D y := by
          symm
          exact SCV.glued_iUnion_eqOn
            (osiiEquation66OSBuiltPhysicalAtlasDensity_eqOn_inter lgc D)
            a hya

/-- The all-edge global density represents the canonical reduced Schwinger
distribution on every retained positive-real region.  This is the
distributional form of the previous pointwise compatibility theorem. -/
theorem osiiEquation66OSBuiltGlobalPhysicalDensity_represents
    {compactCarrier : Set (Fin k -> Real)}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    SCV.RepresentsDistributionOn
      ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
          OS D.cutoff D.cutoff_support).comp
        (unflattenSchwartzNPoint (d := d)))
      (osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage)
      {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈ D.realRegion} := by
  apply SCV.representsDistributionOn_congr_on_subset
    ((OSIIChapterV.canonicalReducedTimeCutoffSchwingerCLM
        OS D.cutoff D.cutoff_support).comp
      (unflattenSchwartzNPoint (d := d)))
    (osiiEquation66OSBuiltCanonicalPhysicalDensity_represents lgc D)
  · intro y hy
    exact
      (osiiEquation66OSBuiltGlobalPhysicalDensity_eq_canonicalPhysicalDensity_of_mem
        (lgc := lgc) (stage := stage) D hy).symm
  · exact Set.Subset.rfl

/-- The globally glued equation-(6.6) density is continuous throughout the
strict-positive Euclidean time region. -/
theorem continuousOn_osiiEquation66OSBuiltGlobalPhysicalDensity
    (H : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage) :
    ContinuousOn
      (osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage)
      {y : Fin (k * (d + 1)) -> Real |
        osiiEquation66FlatTime (d := d) y ∈
          section43TimeStrictPositiveRegion k} := by
  intro y hy
  rcases Set.mem_iUnion.mp
      (osiiEquation66OSBuiltGlobalPhysicalAtlas_covers
        (lgc := lgc) H hy) with
    ⟨a, hya⟩
  have hlocal :=
    (continuousOn_osiiEquation66OSBuiltGlobalPhysicalAtlasDensity
      (lgc := lgc) (stage := stage) a y hya).continuousAt
      ((isOpen_osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier
        (lgc := lgc) (stage := stage) a).mem_nhds hya)
  have heq :
      osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage =ᶠ[nhds y]
        osiiEquation66OSBuiltGlobalPhysicalAtlasDensity lgc stage a := by
    filter_upwards [
      (isOpen_osiiEquation66OSBuiltGlobalPhysicalAtlasCarrier
        (lgc := lgc) (stage := stage) a).mem_nhds hya]
      with z hz
    exact osiiEquation66OSBuiltGlobalPhysicalDensity_eqOn_chart
      (lgc := lgc) (stage := stage) a hz
  exact (hlocal.congr_of_eventuallyEq heq).continuousWithinAt

end OSReconstruction
