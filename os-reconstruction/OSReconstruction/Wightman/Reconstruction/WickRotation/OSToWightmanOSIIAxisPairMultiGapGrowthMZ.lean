/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFlatCross
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairGrowthMZ









noncomputable section

open Complex Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

/-- Multi-gap cosh growth is measured after the canonical finite flattening.
This makes the contract invariant under the reindexing used by MZ. -/
abbrev OSIIAxisPairMultiGapFlatCrossCoshGrowthData
    (P : OSIIAxisPairMultiGapFlatCrossData d k) :=
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  OSIIAxisPairFlatCrossCoshGrowthData P.toFlattenedFlatCrossData

namespace OSIIAxisPairMultiGapFlatCrossCoshGrowthData

/-- A growth-admissible multi-gap flat cross continues holomorphically to the
global Chapter V.1 `l1` carrier. -/
theorem exists_holomorphic_realEdge_extension
    (P : OSIIAxisPairMultiGapFlatCrossData d k)
    (G : OSIIAxisPairMultiGapFlatCrossCoshGrowthData P) :
    ∃ Gamma : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ,
      DifferentiableOn ℂ Gamma
        (osiiAxisPairMultiGapLogDomain d k) ∧
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          P.realEdge x := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := P.toFlattenedFlatCrossData
  obtain ⟨Gamma, hGamma, hGamma_real⟩ :=
    OSIIAxisPairFlatCrossCoshGrowthData.exists_holomorphic_realEdge_extension G
  refine
    ⟨fun z => Gamma (osiiAxisPairMultiGapFlatten z), ?_, ?_⟩
  · apply hGamma.comp
      (osiiAxisPairMultiGapFlattenCLE
        (d := d) (k := k)).differentiable.differentiableOn
    intro z hz
    exact
      (osiiAxisPairMultiGapFlatten_mem_logDomain_iff z).2 hz
  · intro x
    change
      Gamma
          (osiiAxisPairMultiGapFlatten
            (osiiAxisPairSimultaneousLogRealEmbed x)) =
        P.realEdge x
    rw [osiiAxisPairMultiGapFlatten_realEmbed]
    simpa [X,
      OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData] using
      hGamma_real (osiiAxisPairMultiGapFlatten x)

end OSIIAxisPairMultiGapFlatCrossCoshGrowthData

/-- Source-parametric multi-gap crosses with one continuous multilinear real
edge and sourcewise cosh-growth data. -/
structure OSIIAxisPairMultiGapSourcewiseCoshGrowthData
    (d n k : ℕ) [NeZero d] [NeZero k] where
  flatCross :
    (Fin n → SchwartzSpacetime d) →
      OSIIAxisPairMultiGapFlatCrossData d k
  realEdge :
    (Fin k → osiiAxisPairIndex d → ℝ) →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ
  flatCross_realEdge :
    ∀ (fs : Fin n → SchwartzSpacetime d)
      (x : Fin k → osiiAxisPairIndex d → ℝ),
      (flatCross fs).realEdge x = realEdge x fs
  growth :
    ∀ fs : Fin n → SchwartzSpacetime d,
      OSIIAxisPairMultiGapFlatCrossCoshGrowthData (flatCross fs)

namespace OSIIAxisPairMultiGapSourcewiseCoshGrowthData

/-- A sourcewise cosh-growth family has a common rate when its damping
exponent is independent of the Schwartz source tuple.  The multiplicative
growth constants may still depend on the sources. -/
structure CommonRate
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k) where
  rate : ℝ
  growth_rate :
    ∀ fs : Fin n → SchwartzSpacetime d,
      (P.growth fs).rate = rate

/-- Select the sourcewise growth-admissible MZ continuation. -/
noncomputable def toMZFamily
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k) :
    OSIIAxisPairMultiGapSourcewiseMZFamily d n k where
  toFun := fun fs =>
    Classical.choose
      ((P.growth fs).exists_holomorphic_realEdge_extension
        (P.flatCross fs))
  holomorphic := by
    intro fs
    exact
      (Classical.choose_spec
        ((P.growth fs).exists_holomorphic_realEdge_extension
          (P.flatCross fs))).1
  realEdge := P.realEdge
  realEdge_eq := by
    intro fs x
    exact
      ((Classical.choose_spec
        ((P.growth fs).exists_holomorphic_realEdge_extension
          (P.flatCross fs))).2 x).trans
        (P.flatCross_realEdge fs x)

/-- Canonical damped Gaussian approximant, divided by the nonvanishing
damping weight after finite flattening. -/
def gaussianApproximant
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (fs : Fin n → SchwartzSpacetime d)
    (q : ℕ)
    (z : Fin k → osiiAxisPairIndex d → ℂ) : ℂ := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := (P.flatCross fs).toFlattenedFlatCrossData
  let G := P.growth fs
  exact
    (X.coshDamped G.rate).gaussianApproximant q
        (osiiAxisPairMultiGapFlatten z) /
      SCV.logCoshDamping G.rate
        (osiiAxisPairMultiGapFlatten z)

/-- The divided damped Gaussian sequence converges to the selected
growth-admissible sourcewise continuation. -/
theorem gaussianApproximant_tendsto_toMZFamily
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k)
    (fs : Fin n → SchwartzSpacetime d) :
    Tendsto
      (fun q => P.gaussianApproximant fs q z)
      atTop (nhds (P.toMZFamily.toFun fs z)) := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := (P.flatCross fs).toFlattenedFlatCrossData
  let G := P.growth fs
  let Gamma :
      (osiiAxisPairIndex (k * d) → ℂ) → ℂ :=
    fun w =>
      P.toMZFamily.toFun fs
          (osiiAxisPairMultiGapUnflatten w) *
        SCV.logCoshDamping G.rate w
  have hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairLogDomain (d := k * d)) := by
    exact
      ((P.toMZFamily.holomorphic fs).comp
        (osiiAxisPairMultiGapFlattenCLE
          (d := d) (k := k)).symm.differentiable.differentiableOn
        (by
          intro w hw
          apply
            (osiiAxisPairMultiGapFlatten_mem_logDomain_iff
              (osiiAxisPairMultiGapUnflatten w)).1
          simpa using hw)).mul
        (SCV.differentiable_logCoshDamping G.rate
          |>.differentiableOn)
  have hGamma_real :
      ∀ x : osiiAxisPairIndex (k * d) → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) =
          (X.coshDamped G.rate).family.realEdge x := by
    intro x
    rw [OSIIAxisPairFlatCrossData.coshDamped_realEdge]
    dsimp [Gamma]
    rw [osiiAxisPairMultiGapUnflatten_realEmbed]
    rw [P.toMZFamily.realEdge_eq]
    have hedge :
        P.toMZFamily.realEdge
            (osiiAxisPairMultiGapUnflatten x) fs =
          X.family.realEdge x := by
      simpa [toMZFamily, X,
        OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData] using
        (P.flatCross_realEdge fs
          (osiiAxisPairMultiGapUnflatten x)).symm
    rw [hedge]
    exact mul_comm _ _
  have hconv :=
    (X.coshDamped G.rate).gaussianApproximant_tendsto_extension
      G.realEdgeConstant G.coshDamped_realEdge_bound
      G.chartConstant G.chartConstant_pos
      G.coshDamped_chart_bound
      Gamma hGamma hGamma_real
      (osiiAxisPairMultiGapFlatten z)
      ((osiiAxisPairMultiGapFlatten_mem_logDomain_iff z).2 hz)
  have hdiv :=
    hconv.div_const
      (SCV.logCoshDamping G.rate
        (osiiAxisPairMultiGapFlatten z))
  have hne :
      SCV.logCoshDamping G.rate
          (osiiAxisPairMultiGapFlatten z) ≠ 0 :=
    SCV.logCoshDamping_ne_zero _ _
  simpa [gaussianApproximant, X, G, Gamma, hne] using hdiv

/-- The selected growth-admissible continuation is quantitatively controlled
after multiplication by its common nonvanishing damping weight. -/
theorem norm_toMZFamily_mul_logCoshDamping_le_chartConstant
    (P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k)
    (fs : Fin n → SchwartzSpacetime d) :
    ‖P.toMZFamily.toFun fs z *
        SCV.logCoshDamping (P.growth fs).rate
          (osiiAxisPairMultiGapFlatten z)‖ ≤
      (P.growth fs).chartConstant := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X := (P.flatCross fs).toFlattenedFlatCrossData
  let G := P.growth fs
  have hhol :
      DifferentiableOn ℂ
        (fun w =>
          P.toMZFamily.toFun fs
            (osiiAxisPairMultiGapUnflatten w))
        (osiiAxisPairLogDomain (d := k * d)) := by
    apply (P.toMZFamily.holomorphic fs).comp
      (osiiAxisPairMultiGapFlattenCLE
        (d := d) (k := k)).symm.differentiable.differentiableOn
    intro w hw
    apply
      (osiiAxisPairMultiGapFlatten_mem_logDomain_iff
        (osiiAxisPairMultiGapUnflatten w)).1
    simpa using hw
  have hreal :
      ∀ x : osiiAxisPairIndex (k * d) → ℝ,
        P.toMZFamily.toFun fs
            (osiiAxisPairMultiGapUnflatten
              (osiiAxisPairLogRealEmbed x)) =
          X.family.realEdge x := by
    intro x
    change
      P.toMZFamily.toFun fs
          (osiiAxisPairMultiGapUnflatten
            (osiiAxisPairLogRealEmbed x)) =
        X.family.realEdge x
    rw [osiiAxisPairMultiGapUnflatten_realEmbed]
    rw [P.toMZFamily.realEdge_eq]
    simpa [X,
      OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData] using
      (P.flatCross_realEdge fs
        (osiiAxisPairMultiGapUnflatten x)).symm
  have hbound :=
    G.norm_holomorphic_realEdge_extension_mul_logCoshDamping_le
      (fun w =>
        P.toMZFamily.toFun fs
          (osiiAxisPairMultiGapUnflatten w))
      hhol hreal
      (osiiAxisPairMultiGapFlatten z)
      ((osiiAxisPairMultiGapFlatten_mem_logDomain_iff z).2 hz)
  simpa using hbound

namespace CommonRate

/-- The damped common real edge remains a continuous multilinear map in all
Schwartz source slots. -/
noncomputable def dampedRealEdgeCMM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d))) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d) ℂ :=
  SCV.logCoshDamping U.rate
      (osiiAxisPairLogRealEmbed (fun a => y a)) •
    P.realEdge (osiiAxisPairMultiGapUnflatten (fun a => y a))

@[simp]
theorem dampedRealEdgeCMM_apply
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)))
    (fs : Fin n → SchwartzSpacetime d) :
    U.dampedRealEdgeCMM y fs =
      SCV.logCoshDamping U.rate
          (osiiAxisPairLogRealEmbed (fun a => y a)) *
        P.realEdge (osiiAxisPairMultiGapUnflatten (fun a => y a)) fs := by
  simp [dampedRealEdgeCMM, smul_eq_mul]

/-- The sourcewise damped CMM is exactly the real-edge input of the flattened
damped flat cross selected for that source tuple. -/
theorem dampedRealEdgeCMM_apply_eq_gaussianRealEdgeInput
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)))
    (fs : Fin n → SchwartzSpacetime d) :
    U.dampedRealEdgeCMM y fs =
      (((P.flatCross fs).toFlattenedFlatCrossData).coshDamped
          (P.growth fs).rate).gaussianRealEdgeInput y := by
  rw [dampedRealEdgeCMM_apply]
  change
    SCV.logCoshDamping U.rate
          (osiiAxisPairLogRealEmbed (fun a => y a)) *
        P.realEdge (osiiAxisPairMultiGapUnflatten (fun a => y a)) fs =
      SCV.logCoshDamping (P.growth fs).rate
          (osiiAxisPairLogRealEmbed (fun a => y a)) *
        (P.flatCross fs).realEdge
          (osiiAxisPairMultiGapUnflatten (fun a => y a))
  rw [U.growth_rate fs, P.flatCross_realEdge]

/-- Every scalar evaluation of the common-rate damped real edge is integrable
against a positive-scale complex Gaussian kernel. -/
theorem integrable_gaussianKernel_mul_dampedRealEdgeCMM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (c : ℝ) (hc : 0 < c)
    (z : osiiAxisPairIndex (k * d) → ℂ)
    (fs : Fin n → SchwartzSpacetime d) :
    Integrable
      (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
        SCV.gaussianKernel c z y * U.dampedRealEdgeCMM y fs) := by
  let X := (P.flatCross fs).toFlattenedFlatCrossData
  let G := P.growth fs
  have heq :
      (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
        U.dampedRealEdgeCMM y fs) =
        (X.coshDamped G.rate).gaussianRealEdgeInput := by
    funext y
    exact U.dampedRealEdgeCMM_apply_eq_gaussianRealEdgeInput y fs
  have hmeas :
      AEStronglyMeasurable
        (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
          U.dampedRealEdgeCMM y fs) := by
    rw [heq]
    exact
      (X.coshDamped G.rate).continuous_gaussianRealEdgeInput
        |>.aestronglyMeasurable
  have hbound :
      ∀ y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)),
        ‖U.dampedRealEdgeCMM y fs‖ ≤ G.realEdgeConstant := by
    intro y
    rw [congrFun heq y]
    exact G.coshDamped_realEdge_bound (fun a => y a)
  exact
    SCV.integrable_gaussianKernel_mul_of_bounded
      c hc z hmeas G.realEdgeConstant hbound

/-- Algebraic Gaussian regularization of a common-rate damped sourcewise real
edge.  Joint continuity is proved below from separate continuity. -/
noncomputable def dampedGaussianMLM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (c : ℝ) (hc : 0 < c)
    (z : osiiAxisPairIndex (k * d) → ℂ) :
    MultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d) ℂ :=
  OSIIAxisPairSourcewiseMZFamily.integralMultilinearMap
    volume (SCV.gaussianKernel c z)
    (fun y => (U.dampedRealEdgeCMM y).toMultilinearMap)
    (U.integrable_gaussianKernel_mul_dampedRealEdgeCMM c hc z)

@[simp]
theorem dampedGaussianMLM_apply
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (c : ℝ) (hc : 0 < c)
    (z : osiiAxisPairIndex (k * d) → ℂ)
    (fs : Fin n → SchwartzSpacetime d) :
    U.dampedGaussianMLM c hc z fs =
      SCV.gaussianRegularization c
        (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
          U.dampedRealEdgeCMM y fs) z :=
  rfl

/-- The damped Gaussian multilinear map is continuous in one varying source
slot. -/
theorem continuous_dampedGaussianMLM_update
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (c : ℝ) (hc : 0 < c)
    (z : osiiAxisPairIndex (k * d) → ℂ)
    (i : Fin n)
    (fs : Fin n → SchwartzSpacetime d) :
    Continuous
      (fun f : SchwartzSpacetime d =>
        U.dampedGaussianMLM c hc z (Function.update fs i f)) := by
  let T :
      EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) →
        SchwartzSpacetime d →L[ℂ] ℂ :=
    fun y => (U.dampedRealEdgeCMM y).toContinuousLinearMap fs i
  have hT_apply :
      ∀ (y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)))
        (f : SchwartzSpacetime d),
        T y f =
          U.dampedRealEdgeCMM y (Function.update fs i f) := by
    intro y f
    simp [T, ContinuousMultilinearMap.toContinuousLinearMap_apply]
  have heq :
      (fun f : SchwartzSpacetime d =>
        U.dampedGaussianMLM c hc z (Function.update fs i f)) =
        fun f =>
          SCV.gaussianRegularization c (fun y => T y f) z := by
    funext f
    rw [dampedGaussianMLM_apply]
    apply congrArg
      (fun g : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) → ℂ =>
        SCV.gaussianRegularization c g z)
    funext y
    exact (hT_apply y f).symm
  rw [heq]
  apply
    OSIIAxisPairSourcewiseMZFamily.continuous_gaussianRegularization_of_pointwise_bounded_clm
      c hc z T
  · intro f
    let X :=
      (P.flatCross (Function.update fs i f)).toFlattenedFlatCrossData
    let G := P.growth (Function.update fs i f)
    have hfun :
        (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
          T y f) =
          (X.coshDamped G.rate).gaussianRealEdgeInput := by
      funext y
      rw [hT_apply]
      exact
        U.dampedRealEdgeCMM_apply_eq_gaussianRealEdgeInput
          y (Function.update fs i f)
    rw [hfun]
    exact
      (X.coshDamped G.rate).continuous_gaussianRealEdgeInput
        |>.aestronglyMeasurable
  · intro f
    let X :=
      (P.flatCross (Function.update fs i f)).toFlattenedFlatCrossData
    let G := P.growth (Function.update fs i f)
    refine ⟨G.realEdgeConstant, fun y => ?_⟩
    rw [hT_apply]
    rw [U.dampedRealEdgeCMM_apply_eq_gaussianRealEdgeInput
      y (Function.update fs i f)]
    exact G.coshDamped_realEdge_bound (fun a => y a)

/-- The Gaussian regularization of the common-rate damped real edge is jointly
continuous multilinear in all Schwartz source slots. -/
theorem exists_dampedGaussianCMM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (c : ℝ) (hc : 0 < c)
    (z : osiiAxisPairIndex (k * d) → ℂ) :
    ∃ A : ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        A fs = U.dampedGaussianMLM c hc z fs :=
  exists_continuousMultilinear_ofSeparatelyContinuous
    (d := d) (U.dampedGaussianMLM c hc z)
    (U.continuous_dampedGaussianMLM_update c hc z)

/-- At every Gaussian level, division by the common nonvanishing damping
weight preserves continuous multilinearity and yields the canonical
growth-admissible approximant. -/
theorem exists_gaussianApproximantCMM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (q : ℕ)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    ∃ A : ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        A fs = P.gaussianApproximant fs q z := by
  let zflat := osiiAxisPairMultiGapFlatten z
  let weight := SCV.logCoshDamping U.rate zflat
  obtain ⟨A, hA⟩ :=
    U.exists_dampedGaussianCMM
      ((q + 1 : ℕ) : ℝ) (by positivity) zflat
  refine ⟨weight⁻¹ • A, fun fs => ?_⟩
  rw [ContinuousMultilinearMap.smul_apply, hA]
  let X := (P.flatCross fs).toFlattenedFlatCrossData
  let G := P.growth fs
  have hinput :
      (fun y : EuclideanSpace ℝ (osiiAxisPairIndex (k * d)) =>
        U.dampedRealEdgeCMM y fs) =
        (X.coshDamped G.rate).gaussianRealEdgeInput := by
    funext y
    exact U.dampedRealEdgeCMM_apply_eq_gaussianRealEdgeInput y fs
  rw [dampedGaussianMLM_apply]
  rw [hinput]
  change
    weight⁻¹ *
        (X.coshDamped G.rate).gaussianApproximant q zflat =
      (X.coshDamped G.rate).gaussianApproximant q zflat /
        SCV.logCoshDamping G.rate zflat
  rw [U.growth_rate fs]
  simp only [weight, div_eq_mul_inv]
  ring

/-- Canonical continuous multilinear representative of the divided damped
Gaussian approximant. -/
noncomputable def gaussianApproximantCMM
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (q : ℕ)
    (z : Fin k → osiiAxisPairIndex d → ℂ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d) ℂ :=
  Classical.choose (U.exists_gaussianApproximantCMM q z)

@[simp]
theorem gaussianApproximantCMM_apply
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (q : ℕ)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (fs : Fin n → SchwartzSpacetime d) :
    U.gaussianApproximantCMM q z fs =
      P.gaussianApproximant fs q z :=
  Classical.choose_spec (U.exists_gaussianApproximantCMM q z) fs

/-- A common source-independent damping rate closes the full fixed-carrier
Schwartz-distribution handoff automatically. -/
theorem existsUnique_schwartzDistributionAt
    {P : OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k}
    (U : P.CommonRate)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    ∃! W : SchwartzNPoint d n →L[ℂ] ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        W (SchwartzMap.productTensor fs) =
          P.toMZFamily.toFun fs z := by
  apply
    P.toMZFamily.existsUnique_schwartzDistributionAt_of_pointwise_cmm_approximants
      z hz (fun q => U.gaussianApproximantCMM q z)
  intro fs
  exact
    (P.gaussianApproximant_tendsto_toMZFamily z hz fs).congr'
      (Filter.Eventually.of_forall fun q =>
        (U.gaussianApproximantCMM_apply q z fs).symm)

end CommonRate

end OSIIAxisPairMultiGapSourcewiseCoshGrowthData

end OSReconstruction
