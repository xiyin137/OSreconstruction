import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltSpatialAtlas

/-!
# Coherence of the OS-built equation-(6.6) spatial atlas

At fixed positive real time, the zero-slice chronological translation of
every local equation-(6.6) chart is the same canonical half-time translation.
Consequently two chart distributions agree on tests supported in their
overlap. Distributional uniqueness then identifies the full local densities,
and hence their spatial restrictions, on overlaps. This proves continuity of
the canonical mixed-spatial density without choosing a global local-Weyl
scale.
-/

noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- Chronological point translations are partial sums of their gap
translations. -/
theorem osiiAxisPairChronologicalPointTranslation_eq_diffVarSection
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    osiiAxisPairChronologicalPointTranslation T x =
      diffVarSection d k
        (fun i => osiiAxisPairChronologicalGapTranslation T x i) := by
  funext j
  induction j using Fin.induction with
  | zero =>
      rw [osiiAxisPairChronologicalPointTranslation_zero]
      ext mu
      symm
      exact diffVarSection_zero (d := d) k
        (fun i => osiiAxisPairChronologicalGapTranslation T x i) mu
  | succ j ih =>
      have hdiff :=
        osiiAxisPairChronologicalPointTranslation_sub_castSucc T x j
      have hsum :
          diffVarSection d k
              (fun i => osiiAxisPairChronologicalGapTranslation T x i) j.succ =
            diffVarSection d k
              (fun i => osiiAxisPairChronologicalGapTranslation T x i) j.castSucc +
                osiiAxisPairChronologicalGapTranslation T x j := by
        ext mu
        exact diffVarSection_succ (d := d) k
          (fun i => osiiAxisPairChronologicalGapTranslation T x i) j mu
      rw [hsum, ← ih, ← hdiff]
      abel

/-- The fixed reduced-gap translation from the half-time Weyl anchor to the
physical time slice. It has zero spatial component. -/
def osiiEquation66SpatialChartGap
    (d k : Nat)
    (tau : Fin k -> Real) :
    Fin (k * (d + 1)) -> Real :=
  osiiStep4MixedSpatialRealPoint d k (fun i => tau i / 2) 0

/-- At zero imaginary displacement, the axis-pair logarithms reconstruct the
same half-time gap independently of the spatial chart center and auxiliary
slope. -/
theorem osiiEquation66SpatialZeroTargetGapTranslation
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    osiiStep4AxisPairGapTranslationFlat d T
        (fun i a => Real.log
          (osiiStep4MultiGapTargetCoeff d k T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 i a).re) =
      osiiEquation66SpatialChartGap d k tau := by
  funext q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  unfold osiiAxisPairChronologicalGapTranslation
    osiiAxisPairPositiveCoefficients
  have hcoeffPos (a : osiiAxisPairIndex d) :
      0 < (osiiStep4MultiGapTargetCoeff d k T
        (osiiStep4MixedSpatialRealPoint d k tau base) 0 i a).re :=
    osiiStep4MultiGapTargetCoeff_re_pos d k T hT
      (osiiStep4MixedSpatialRealPoint d k tau base) 0
      (fun j => by
        simpa [osiiStep4MixedSpatialRealPoint] using htau j) i a
  simp_rw [Real.exp_log (hcoeffPos _)]
  have hsum := osiiAxisPairCoeffMap_real_sum_smul_dir
    (d := d) T hT.ne'
    (osiiStep4MultiGapRealBlock (d + 1) k
      (osiiStep4MixedSpatialRealPoint d k tau base) i)
    (0 : Fin (d + 1) -> Real)
  have happ := congrFun hsum mu
  have hzeroCoeff :
      (fun nu : Fin (d + 1) =>
        (((0 : Fin (d + 1) -> Real) nu : Real) : Complex)) = 0 := by
    funext nu
    simp
  rw [hzeroCoeff] at happ
  have hzero :
      osiiStep4ComplexOfRealImag 0
          (osiiStep4MultiGapRealBlock (d + 1) k
            (0 : Fin (k * (d + 1)) -> Real) i) = 0 := by
    funext nu
    simp [osiiStep4ComplexOfRealImag, osiiStep4MultiGapRealBlock]
  simpa [osiiStep4MultiGapTargetCoeff,
    osiiStep4MultiGapImaginaryBlock,
    osiiStep4MultiGapRealBlock,
    osiiStep4MixedSpatialRealPoint,
    osiiEquation66SpatialChartGap,
    osiiAxisPairPhysicalShift, hzero] using happ

/-- Canonical absolute-point translation associated to the fixed positive
time tuple. -/
def osiiEquation66SpatialChartPointTranslation
    (d k : Nat)
    (tau : Fin k -> Real) :
    NPointDomain d (k + 1) :=
  diffVarSection d k
    (fun i mu => osiiEquation66SpatialChartGap d k tau
      (finProdFinEquiv (i, mu)))

/-- The complete zero-target chronological point translation is canonical at
fixed time. -/
theorem osiiEquation66SpatialZeroTargetPointTranslation
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) (hT : 0 < T)
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    osiiAxisPairChronologicalPointTranslation T
        (fun i a => Real.log
          (osiiStep4MultiGapTargetCoeff d k T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 i a).re) =
      osiiEquation66SpatialChartPointTranslation d k tau := by
  rw [osiiAxisPairChronologicalPointTranslation_eq_diffVarSection]
  congr 1
  funext i mu
  simpa using congrFun
    (osiiEquation66SpatialZeroTargetGapTranslation
      d k T hT tau htau base) (finProdFinEquiv (i, mu))

/-- The first-carrier angular continuation underlying one spatial chart. -/
noncomputable def osiiEquation66OSBuiltSpatialAngularData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :=
  osiiEquation66FirstAngularData d k OS lgc
    (osiiChapterVIRegularizationRadius_pos
      (Nat.pos_of_ne_zero (NeZero.ne k))
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau))
    (osiiStep4MixedSpatialRealPoint d k tau base)
    (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
      d k tau htau base)

/-- Full flat-real carrier of one fixed local-Weyl chart. -/
def osiiEquation66OSBuiltSpatialFullCarrier
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    Set (Fin (k * (d + 1)) -> Real) :=
  Metric.ball (osiiEquation66SpatialLocalPoint d k tau base)
    (osiiEquation66OSBuiltSpatialLocalScale d OS lgc tau htau base / 4)

/-- Full real restriction of one local-Weyl density. -/
noncomputable def osiiEquation66OSBuiltSpatialFullDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real)
    (x : Fin (k * (d + 1)) -> Real) : Complex :=
  (osiiEquation66OSBuiltSpatialLocalWeylData
    d OS lgc tau htau base).data.density
      (osiiStep4ComplexOfRealImag x 0)

/-- Flatten the zero imaginary-slice distribution of one chart. -/
noncomputable def osiiEquation66OSBuiltSpatialFlatZeroDistribution
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex :=
  ((osiiEquation66OSBuiltSpatialAngularData
      d OS lgc tau htau base).imaginarySliceFamily 0).comp
    (unflattenSchwartzNPoint (d := d))

@[simp] theorem flattenSchwartzNPoint_unflattenSchwartzNPoint
    (d k : Nat)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    flattenSchwartzNPoint (d := d)
        (unflattenSchwartzNPoint (d := d) phi) = phi := by
  ext x
  simp

theorem continuousOn_osiiEquation66OSBuiltSpatialFullDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    ContinuousOn
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base) := by
  have hmap : Continuous
      (fun x : Fin (k * (d + 1)) -> Real =>
        osiiStep4ComplexOfRealImag x 0) := by
    exact continuous_pi fun q => by
      simpa [osiiStep4ComplexOfRealImag, Function.comp_def] using
        (Complex.continuous_ofReal.comp (continuous_apply q))
  exact
    (osiiEquation66OSBuiltSpatialLocalWeylData
      d OS lgc tau htau base).data.holomorphic.continuousOn.comp
        hmap.continuousOn
        (fun x hx => by
          change dist x (osiiEquation66SpatialLocalPoint d k tau base) <
            osiiEquation66OSBuiltSpatialLocalScale
              d OS lgc tau htau base / 4 at hx
          rw [Metric.mem_ball,
            osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]
          calc
            dist (osiiStep4ComplexOfRealImag x 0)
                (SCV.realEmbed
                  (osiiEquation66SpatialLocalPoint d k tau base)) ≤
                dist x (osiiEquation66SpatialLocalPoint d k tau base) +
                  ‖(0 : Fin (k * (d + 1)) -> Real)‖ :=
              osiiStep4ComplexOfRealImag_dist_realEmbed_le x 0 _
            _ < (osiiEquation66OSBuiltSpatialLocalWeylData
                  d OS lgc tau htau base).data.scale := by
              rw [norm_zero, add_zero]
              have hs := osiiEquation66OSBuiltSpatialLocalScale_pos
                d OS lgc tau htau base
              change dist x _ <
                osiiEquation66OSBuiltSpatialLocalScale
                  d OS lgc tau htau base
              exact hx.trans (by linarith))

/-- The full real chart represents its own flattened zero-slice distribution
on the open quarter-scale ball. -/
theorem osiiEquation66OSBuiltSpatialFullDensity_represents
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base : Fin (k * d) -> Real) :
    SCV.RepresentsDistributionOn
      (osiiEquation66OSBuiltSpatialFlatZeroDistribution
        d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullCarrier
        d OS lgc tau htau base) := by
  intro phi hphi
  have hzero :
      (0 : Fin (k * (d + 1)) -> Real) ∈
        Metric.closedBall 0
          (osiiEquation66OSBuiltSpatialLocalScale
            d OS lgc tau htau base / 4) := by
    rw [Metric.mem_closedBall, dist_self]
    exact div_nonneg
      (osiiEquation66OSBuiltSpatialLocalScale_pos
        d OS lgc tau htau base).le (by norm_num)
  have hsupp :
      Function.support
          (flattenSchwartzNPoint (d := d)
            (unflattenSchwartzNPoint (d := d) phi)) ⊆
        Metric.closedBall
          (osiiStep4MultiGapXiHatCenter d k
            (osiiStep4MixedSpatialRealPoint d k tau base))
          (osiiEquation66OSBuiltSpatialLocalScale
            d OS lgc tau htau base / 4) := by
    rw [flattenSchwartzNPoint_unflattenSchwartzNPoint,
      osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]
    intro x hx
    exact Metric.ball_subset_closedBall
      (hphi.2 (subset_closure hx))
  have hrep :=
    (osiiEquation66OSBuiltSpatialLocalWeylData
      d OS lgc tau htau base).data.represents 0 hzero
        (unflattenSchwartzNPoint (d := d) phi) hsupp
  simpa [osiiEquation66OSBuiltSpatialFlatZeroDistribution,
    osiiEquation66OSBuiltSpatialAngularData,
    osiiEquation66OSBuiltSpatialFullDensity] using hrep

/-- Two flattened chart distributions agree on tests supported in their
overlap. The chosen extensions may differ away from that support. -/
theorem osiiEquation66OSBuiltSpatialFlatZeroDistribution_agreeOn_inter
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base other : Fin (k * d) -> Real)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (hphi : Function.support phi ⊆
      osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base ∩
        osiiEquation66OSBuiltSpatialFullCarrier
          d OS lgc tau htau other) :
    osiiEquation66OSBuiltSpatialFlatZeroDistribution
        d OS lgc tau htau base phi =
      osiiEquation66OSBuiltSpatialFlatZeroDistribution
        d OS lgc tau htau other phi := by
  let rho := osiiChapterVIRegularizationRadius k
    (osiiPositiveRealTimeEmbed tau)
  have hrho : 0 < rho := by
    exact osiiChapterVIRegularizationRadius_pos
      (Nat.pos_of_ne_zero (NeZero.ne k))
      ((osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau)
  have hsupp (b : Fin (k * d) -> Real)
      (hb : Function.support phi ⊆
        osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau b) :
      Function.support
          (flattenSchwartzNPoint (d := d)
            (unflattenSchwartzNPoint (d := d) phi)) ⊆
        Metric.closedBall
          (osiiStep4MultiGapXiHatCenter d k
            (osiiStep4MixedSpatialRealPoint d k tau b)) (rho / 4) := by
    rw [flattenSchwartzNPoint_unflattenSchwartzNPoint,
      osiiStep4MultiGapXiHatCenter_mixedSpatialRealPoint]
    intro x hx
    have hxball := hb hx
    change dist x (osiiEquation66SpatialLocalPoint d k tau b) <
      osiiEquation66OSBuiltSpatialLocalScale
        d OS lgc tau htau b / 4 at hxball
    rw [Metric.mem_closedBall]
    have hscale :=
      (osiiEquation66OSBuiltSpatialLocalWeylData
        d OS lgc tau htau b).data.scale_le
    change osiiEquation66OSBuiltSpatialLocalScale
      d OS lgc tau htau b ≤ rho / 2 at hscale
    exact hxball.le.trans (by linarith)
  have hsuppBase := hsupp base (fun x hx => (hphi hx).1)
  have hsuppOther := hsupp other (fun x hx => (hphi hx).2)
  have hbase :=
    (osiiEquation66OSBuiltSpatialAngularData d OS lgc tau htau base
      ).imaginarySliceFamily_zero_apply_eq_schwinger_translate_of_flatSupport
        (unflattenSchwartzNPoint (d := d) phi) hsuppBase
  have hother :=
    (osiiEquation66OSBuiltSpatialAngularData d OS lgc tau htau other
      ).imaginarySliceFamily_zero_apply_eq_schwinger_translate_of_flatSupport
        (unflattenSchwartzNPoint (d := d) phi) hsuppOther
  let Zbase := osiiEquation66QuantitativeSynchronizedData
    d k hrho (osiiStep4MixedSpatialRealPoint d k tau base)
      (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
        d k tau htau base)
  let Zother := osiiEquation66QuantitativeSynchronizedData
    d k hrho (osiiStep4MixedSpatialRealPoint d k tau other)
      (osiiChapterVIRegularizationRadius_le_mixedSpatialRealPoint
        d k tau htau other)
  have htransBase :
      (fun i => -osiiAxisPairChronologicalPointTranslation Zbase.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Zbase.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 j a).re) i) =
        fun i => -osiiEquation66SpatialChartPointTranslation d k tau i := by
    funext i
    have hpoint := osiiEquation66SpatialZeroTargetPointTranslation
      d k Zbase.uniform.T (lt_trans zero_lt_one Zbase.uniform.hT)
        tau htau base
    have hT : Zbase.coherent.T = Zbase.uniform.T := rfl
    rw [hT, hpoint]
  have htransOther :
      (fun i => -osiiAxisPairChronologicalPointTranslation Zother.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Zother.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau other) 0 j a).re) i) =
        fun i => -osiiEquation66SpatialChartPointTranslation d k tau i := by
    funext i
    have hpoint := osiiEquation66SpatialZeroTargetPointTranslation
      d k Zother.uniform.T (lt_trans zero_lt_one Zother.uniform.hT)
        tau htau other
    have hT : Zother.coherent.T = Zother.uniform.T := rfl
    rw [hT, hpoint]
  unfold osiiEquation66OSBuiltSpatialFlatZeroDistribution
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hbase, hother]
  change OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
      (translateSchwartzConfiguration _ _)) =
    OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
      (translateSchwartzConfiguration _ _))
  rw [show (fun i => -osiiAxisPairChronologicalPointTranslation
      Zbase.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Zbase.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau base) 0 j a).re) i) =
      fun i => -osiiEquation66SpatialChartPointTranslation
        d k tau i from htransBase]
  rw [show (fun i => -osiiAxisPairChronologicalPointTranslation
      Zother.coherent.T
        (fun j a => Real.log
          (osiiStep4MultiGapTargetCoeff d k Zother.uniform.T
            (osiiStep4MixedSpatialRealPoint d k tau other) 0 j a).re) i) =
      fun i => -osiiEquation66SpatialChartPointTranslation
        d k tau i from htransOther]

/-- Full local-Weyl real densities agree on chart overlaps. -/
theorem osiiEquation66OSBuiltSpatialFullDensity_eqOn_inter
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base other : Fin (k * d) -> Real) :
    Set.EqOn
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau other)
      (osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau base ∩
        osiiEquation66OSBuiltSpatialFullCarrier
          d OS lgc tau htau other) := by
  let U := osiiEquation66OSBuiltSpatialFullCarrier
      d OS lgc tau htau base ∩
    osiiEquation66OSBuiltSpatialFullCarrier d OS lgc tau htau other
  let T := osiiEquation66OSBuiltSpatialFlatZeroDistribution
    d OS lgc tau htau base
  have hU_open : IsOpen U := by
    exact Metric.isOpen_ball.inter Metric.isOpen_ball
  have hbase_cont : ContinuousOn
      (osiiEquation66OSBuiltSpatialFullDensity
        d OS lgc tau htau base) U :=
    (continuousOn_osiiEquation66OSBuiltSpatialFullDensity
      d OS lgc tau htau base).mono Set.inter_subset_left
  have hother_cont : ContinuousOn
      (osiiEquation66OSBuiltSpatialFullDensity
        d OS lgc tau htau other) U :=
    (continuousOn_osiiEquation66OSBuiltSpatialFullDensity
      d OS lgc tau htau other).mono Set.inter_subset_right
  have hbase_rep : SCV.RepresentsDistributionOn T
      (osiiEquation66OSBuiltSpatialFullDensity
        d OS lgc tau htau base) U := by
    intro phi hphi
    exact osiiEquation66OSBuiltSpatialFullDensity_represents
      d OS lgc tau htau base phi
        ⟨hphi.1, hphi.2.trans Set.inter_subset_left⟩
  have hother_rep : SCV.RepresentsDistributionOn T
      (osiiEquation66OSBuiltSpatialFullDensity
        d OS lgc tau htau other) U := by
    intro phi hphi
    calc
      T phi = osiiEquation66OSBuiltSpatialFlatZeroDistribution
          d OS lgc tau htau other phi := by
        exact
          osiiEquation66OSBuiltSpatialFlatZeroDistribution_agreeOn_inter
            d OS lgc tau htau base other phi
              (fun x hx => hphi.2 (subset_closure hx))
      _ = ∫ x, osiiEquation66OSBuiltSpatialFullDensity
          d OS lgc tau htau other x * phi x := by
        exact osiiEquation66OSBuiltSpatialFullDensity_represents
          d OS lgc tau htau other phi
            ⟨hphi.1, hphi.2.trans Set.inter_subset_right⟩
  have hEq := SCV.eqOn_inter_of_representsDistributionOn
    T U U
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialFullDensity d OS lgc tau htau other)
      hU_open hU_open hbase_cont hother_cont hbase_rep hother_rep
  simpa [U] using hEq

/-- Spatial restrictions of the local-Weyl densities agree on overlaps. -/
theorem osiiEquation66OSBuiltSpatialLocalDensity_eqOn_inter
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base other : Fin (k * d) -> Real) :
    Set.EqOn
      (osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base)
      (osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau other)
      (osiiEquation66OSBuiltSpatialLocalCarrier
          d OS lgc tau htau base ∩
        osiiEquation66OSBuiltSpatialLocalCarrier
          d OS lgc tau htau other) := by
  intro x hx
  apply osiiEquation66OSBuiltSpatialFullDensity_eqOn_inter
    d OS lgc tau htau base other
  constructor
  · change dist (osiiEquation66SpatialLocalPoint d k tau x)
        (osiiEquation66SpatialLocalPoint d k tau base) <
      osiiEquation66OSBuiltSpatialLocalScale
        d OS lgc tau htau base / 4
    rw [show dist (osiiEquation66SpatialLocalPoint d k tau x)
        (osiiEquation66SpatialLocalPoint d k tau base) = dist x base by
      exact osiiStep4MixedSpatialRealPoint_dist
        d k (fun i => tau i / 2) x base]
    exact hx.1
  · change dist (osiiEquation66SpatialLocalPoint d k tau x)
        (osiiEquation66SpatialLocalPoint d k tau other) <
      osiiEquation66OSBuiltSpatialLocalScale
        d OS lgc tau htau other / 4
    rw [show dist (osiiEquation66SpatialLocalPoint d k tau x)
        (osiiEquation66SpatialLocalPoint d k tau other) = dist x other by
      exact osiiStep4MixedSpatialRealPoint_dist
        d k (fun i => tau i / 2) x other]
    exact hx.2

/-- On every chart carrier, the fixed chart equals the canonical OS-built
mixed-spatial density. -/
theorem osiiEquation66OSBuiltSpatialLocalDensity_eq_mixed_of_mem
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (base x : Fin (k * d) -> Real)
    (hx : x ∈ osiiEquation66OSBuiltSpatialLocalCarrier
      d OS lgc tau htau base) :
    osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base x =
      osiiEquation66OSBuiltMixedSpatialDensity
        d OS lgc tau htau x := by
  calc
    osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau base x =
      osiiEquation66OSBuiltSpatialLocalDensity
        d OS lgc tau htau x x :=
      osiiEquation66OSBuiltSpatialLocalDensity_eqOn_inter
        d OS lgc tau htau base x
          ⟨hx, osiiEquation66OSBuiltSpatialLocalCarrier_self
            d OS lgc tau htau x⟩
    _ = osiiEquation66OSBuiltMixedSpatialDensity
        d OS lgc tau htau x :=
      osiiEquation66OSBuiltSpatialLocalDensity_self
        d OS lgc tau htau x

/- The canonical OS-built mixed-spatial density is continuous at every
positive real time. -/
set_option maxHeartbeats 800000 in
theorem continuous_osiiEquation66OSBuiltMixedSpatialDensity
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {k : Nat} [NeZero k]
    (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    Continuous (osiiEquation66OSBuiltMixedSpatialDensity
      d OS lgc tau htau) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hlocal :=
    (continuousOn_osiiEquation66OSBuiltSpatialLocalDensity
      d OS lgc tau htau x x
        (osiiEquation66OSBuiltSpatialLocalCarrier_self
          d OS lgc tau htau x)).continuousAt
      ((isOpen_osiiEquation66OSBuiltSpatialLocalCarrier
        d OS lgc tau htau x).mem_nhds
          (osiiEquation66OSBuiltSpatialLocalCarrier_self
            d OS lgc tau htau x))
  have heq :
      osiiEquation66OSBuiltSpatialLocalDensity
          d OS lgc tau htau x =ᶠ[𝓝 x]
        osiiEquation66OSBuiltMixedSpatialDensity
          d OS lgc tau htau := by
    filter_upwards [
      (isOpen_osiiEquation66OSBuiltSpatialLocalCarrier
        d OS lgc tau htau x).mem_nhds
          (osiiEquation66OSBuiltSpatialLocalCarrier_self
            d OS lgc tau htau x)] with y hy
    exact osiiEquation66OSBuiltSpatialLocalDensity_eq_mixed_of_mem
      d OS lgc tau htau x y hy
  exact hlocal.congr_of_eventuallyEq heq.symm

end OSReconstruction
