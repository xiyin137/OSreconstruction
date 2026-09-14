import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltMixedSpatialDensity
import OSReconstruction.SCV.DistributionalRepresentationUniqueness

/-!
# OS-built equation-(6.6) spatial density atlas

At a fixed positive real time, every spatial base point supplies one
quantitative local-Weyl representative.  This module exposes its spatial
restriction, open carrier, continuity, and center-value normalization.  The
remaining gluing theorem is exactly pairwise agreement of these charts on
overlaps, obtained by identifying their represented distribution.
-/

noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- Local Weyl coordinates for physical time `tau`: the chart anchor carries
half of each time center and leaves all spatial coordinates unchanged. -/
def osiiEquation66SpatialLocalPoint
    (d k : Nat)
    (tau : Fin k -> Real)
    (x : Fin (k * d) -> Real) :
    Fin (k * (d + 1)) -> Real :=
  osiiStep4MixedSpatialRealPoint d k (fun i => tau i / 2) x

/-- The equation-(6.6) `XiHat` anchor of a physical mixed center is exactly
its half-time local coordinate. -/
theorem osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint
    (d k : Nat)
    (tau : Fin k -> Real)
    (x : Fin (k * d) -> Real) :
    osiiStep4MultiGapXiHatCenter d k
        (osiiStep4MixedSpatialRealPoint d k tau x) =
      osiiEquation66SpatialLocalPoint d k tau x := by
  funext q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      simp [osiiEquation66SpatialLocalPoint,
        osiiStep4MixedSpatialRealPoint,
        osiiAxisPairPhysicalChartAnchor,
        osiiStep4MultiGapRealBlock]
  | succ j =>
      simp [osiiEquation66SpatialLocalPoint,
        osiiStep4MixedSpatialRealPoint,
        osiiAxisPairPhysicalChartAnchor,
        osiiStep4MultiGapRealBlock]

/-- The quantitative local-Weyl package selected at one physical mixed
spacetime point. -/
noncomputable def osiiEquation66OSBuiltSpatialLocalWeylData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :=
  osiiEquation66FirstLocalWeylData d k OS lgc
    (osiiChapterVIRegularizationRadius_pos
      (Nat.pos_of_ne_zero (NeZero.ne k))
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau))
    (osiiChapterVIRegularizationRadius_le_sixteen k
      (osiiPositiveRealTimeEmbed tau))
    (osiiStep4MixedSpatialRealPoint d k tau base)
    (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
      d k tau htau base)

/-- The full local-Weyl scale at one spatial base point. -/
noncomputable def osiiEquation66OSBuiltSpatialLocalScale
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) : Real :=
  (osiiEquation66OSBuiltSpatialLocalWeylData
    d OS lgc tau htau base).data.scale

/-- Spatial points retained by the support-local representation at one base
point. -/
def osiiEquation66OSBuiltSpatialLocalCarrier
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) : Set (Fin (k * d) -> Real) :=
  Metric.ball base
    (osiiEquation66OSBuiltSpatialLocalScale
      d OS lgc tau htau base / 4)

/-- Restrict the fixed local-Weyl representative at `base` to the physical
time slice while allowing the spatial point to vary. -/
noncomputable def osiiEquation66OSBuiltSpatialLocalDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base x : Fin (k * d) -> Real) : Complex :=
  (osiiEquation66OSBuiltSpatialLocalWeylData
    d OS lgc tau htau base).data.density
      (osiiStep4ComplexOfRealImag
        (osiiEquation66SpatialLocalPoint d k tau x) 0)

theorem osiiEquation66OSBuiltSpatialLocalScale_pos
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    0 < osiiEquation66OSBuiltSpatialLocalScale
      d OS lgc tau htau base := by
  exact
    (osiiEquation66OSBuiltSpatialLocalWeylData
      d OS lgc tau htau base).data.scale_pos

theorem isOpen_osiiEquation66OSBuiltSpatialLocalCarrier
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    IsOpen (osiiEquation66OSBuiltSpatialLocalCarrier
      d OS lgc tau htau base) :=
  Metric.isOpen_ball

theorem osiiEquation66OSBuiltSpatialLocalCarrier_self
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    base ∈ osiiEquation66OSBuiltSpatialLocalCarrier
      d OS lgc tau htau base := by
  rw [osiiEquation66OSBuiltSpatialLocalCarrier, Metric.mem_ball,
    dist_self]
  exact div_pos
    (osiiEquation66OSBuiltSpatialLocalScale_pos
      d OS lgc tau htau base) (by norm_num)

/-- Every point in the spatial chart maps into the holomorphy ball of its
fixed local-Weyl representative. -/
theorem osiiEquation66OSBuiltSpatialLocalPoint_mem_densityBall
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base x : Fin (k * d) -> Real)
    (hx : x ∈ osiiEquation66OSBuiltSpatialLocalCarrier
      d OS lgc tau htau base) :
    osiiStep4ComplexOfRealImag
        (osiiEquation66SpatialLocalPoint d k tau x) 0 ∈
      Metric.ball
        (SCV.realEmbed
          (osiiStep4MultiGapXiHatCenter d k
            (osiiStep4MixedSpatialRealPoint d k tau base)))
        (osiiEquation66OSBuiltSpatialLocalScale
          d OS lgc tau htau base) := by
  rw [osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]
  have hcenterComplex :
      SCV.realEmbed (osiiEquation66SpatialLocalPoint d k tau base) =
        osiiStep4ComplexOfRealImag
          (osiiEquation66SpatialLocalPoint d k tau base) 0 := by
    ext q
    simp [SCV.realEmbed, osiiStep4ComplexOfRealImag]
  rw [hcenterComplex, Metric.mem_ball,
    show dist
        (osiiStep4ComplexOfRealImag
          (osiiEquation66SpatialLocalPoint d k tau x) 0)
        (osiiStep4ComplexOfRealImag
          (osiiEquation66SpatialLocalPoint d k tau base) 0) =
          dist x base by
      exact osiiStep4MixedSpatialComplexRealPoint_dist
        d k (fun i => tau i / 2) x base]
  rw [osiiEquation66OSBuiltSpatialLocalCarrier,
    Metric.mem_ball] at hx
  exact hx.trans (by
    have hs := osiiEquation66OSBuiltSpatialLocalScale_pos
      d OS lgc tau htau base
    linarith)

/-- Each fixed local-Weyl spatial chart is continuous on its open carrier. -/
theorem continuousOn_osiiEquation66OSBuiltSpatialLocalDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    ContinuousOn
      (osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialLocalCarrier
        d OS lgc tau htau base) := by
  exact
    (osiiEquation66OSBuiltSpatialLocalWeylData
      d OS lgc tau htau base).data.holomorphic.continuousOn.comp
        (continuous_osiiStep4MixedSpatialComplexRealPoint
          d k (fun i => tau i / 2)).continuousOn
        (fun x hx =>
          osiiEquation66OSBuiltSpatialLocalPoint_mem_densityBall
            d OS lgc tau htau base x hx)

/-- The spatial chart selected at `base` has the canonical OS-built mixed
density as its center value. -/
theorem osiiEquation66OSBuiltSpatialLocalDensity_self
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base base =
      osiiEquation66OSBuiltMixedSpatialDensity
        d OS lgc tau htau base := by
  unfold osiiEquation66OSBuiltSpatialLocalDensity
    osiiEquation66OSBuiltSpatialLocalWeylData
    osiiEquation66OSBuiltMixedSpatialDensity
    osiiEquation66OSBuiltCenterValue
  rw [osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]

end OSReconstruction
