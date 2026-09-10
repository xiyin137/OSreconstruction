/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.LocallyConvex.Barrelled
import Init
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.SCV.SchwartzPartialEval
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeParametricContinuation
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity














noncomputable section

open Complex Topology Filter MeasureTheory
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- A full spacetime Schwartz distribution, smeared by a fixed difference-time
test, becomes a spatial Schwartz distribution. -/
noncomputable def osiiTimeSmearedSpatialDistribution
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    OSIISpatialDistribution d k :=
  W.comp (section43OrderedPullbackTimeSpatialTensorSpatialCLM d k φ)

@[simp] theorem osiiTimeSmearedSpatialDistribution_apply
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    osiiTimeSmearedSpatialDistribution W φ χ =
      W (section43OrderedPullbackTimeSpatialTensorSpatialCLM d k φ χ) :=
  rfl

/-- Delta smearing centered at a real time-gap point.  The sign convention
matches the positive-orthant approximate identities in
`OSToWightmanOSIIDeltaSmearing`. -/
noncomputable def osiiTranslatedTimeSmearedSpatialDistribution
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (τ : Fin k → ℝ) :
    OSIISpatialDistribution d k :=
  osiiTimeSmearedSpatialDistribution W
    (SCV.translateSchwartz (-τ) φ)

@[simp] theorem osiiTranslatedTimeSmearedSpatialDistribution_apply
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (τ : Fin k → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    osiiTranslatedTimeSmearedSpatialDistribution W φ τ χ =
      W (section43OrderedPullbackTimeSpatialTensorSpatialCLM d k
        (SCV.translateSchwartz (-τ) φ) χ) :=
  rfl

/-- A spatial-distribution-valued time orbit represents a full spacetime
distribution on `U` when every fixed spatial test gives the corresponding
local scalar distributional representative. -/
def OSIITimeSpatialRepresentsDistributionOn
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ)) : Prop :=
  ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
    SCV.RepresentsDistributionOn
      (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
      (fun τ => R τ χ) U

/-- Pointwise boundedness of a spatial-distribution-valued time orbit on a
fixed time region.  The bound may depend on the spatial Schwartz test. -/
def OSIITimeSpatialPointwiseBoundedOn
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ)) : Prop :=
  ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
    ∃ C : ℝ, ∀ τ ∈ U, ‖R τ χ‖ ≤ C

/-- Compact-local pointwise boundedness of a complex-time family of spatial
distributions.  This is the Banach-Steinhaus hypothesis needed to extend
weak holomorphy from a dense class of spatial tests. -/
def OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k)) : Prop :=
  ∀ K : Set (OSIITimeGapSpace k), IsCompact K → K ⊆ U →
    ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ∃ C : ℝ, ∀ ζ ∈ K, ‖F ζ χ‖ ≤ C

/-- The spatial Schwartz slice of a full difference-coordinate source at a
fixed family of difference times. -/
noncomputable def osiiFullSourceSpatialSlice
    (F : SchwartzNPoint d k) (τ : Fin k → ℝ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ :=
  SCV.schwartzPartialEval₁
    (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) τ

omit [NeZero d] in
@[simp] theorem osiiFullSourceSpatialSlice_apply
    (F : SchwartzNPoint d k) (τ : Fin k → ℝ)
    (η : Section43SpatialSpace d k) :
    osiiFullSourceSpatialSlice F τ η =
      F ((nPointTimeSpatialCLE (d := d) k).symm (τ, η)) := by
  rfl

@[simp] theorem osiiFullSourceSpatialSlice_timeSpatialTensor
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (τ : Fin k → ℝ) :
    osiiFullSourceSpatialSlice
        (section43NPointTimeSpatialTensor d k φ χ) τ =
      φ τ • χ := by
  ext η
  simp [osiiFullSourceSpatialSlice, section43NPointTimeSpatialTensor,
    section43TimeSpatialTensor]

omit [NeZero d] in
theorem continuous_osiiFullSourceSpatialSlice
    (F : SchwartzNPoint d k) :
    Continuous (osiiFullSourceSpatialSlice F) :=
  SCV.continuous_schwartzPartialEval₁
    (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F)

omit [NeZero d] in
/-- Banach-Steinhaus turns pointwise boundedness of an arbitrary family of
spatial distributions into one finite Schwartz-seminorm bound, uniform over
the whole index type. -/
theorem exists_uniform_schwartz_bound_osiiSpatial
    {ι : Type*}
    (R : ι → OSIISpatialDistribution d k)
    (hbounded :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ i, ‖R i χ‖ ≤ C) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ i, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ‖R i χ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d k) ℂ) χ := by
  have hT :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ i,
          ‖((R i).restrictScalars ℝ) χ‖ ≤ C := hbounded
  obtain ⟨s, Cnn, hCnn, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Section43SpatialSpace d k) (F := ℂ) (G := ℂ)
      (T := fun i => (R i).restrictScalars ℝ) hT
  have hsup :
      ∀ (s' : Finset (ℕ × ℕ))
        (χ : SchwartzMap (Section43SpatialSpace d k) ℂ),
        (s'.sup
            (schwartzSeminormFamily ℝ
              (Section43SpatialSpace d k) ℂ)) χ =
          (s'.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d k) ℂ)) χ := by
    intro s' χ
    induction s' using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have ha_eq :
            (schwartzSeminormFamily ℝ
                (Section43SpatialSpace d k) ℂ a) χ =
              (schwartzSeminormFamily ℂ
                (Section43SpatialSpace d k) ℂ a) χ := by
          cases a
          rfl
        simp [Finset.sup_insert, ih, ha_eq]
  refine ⟨s, (Cnn : ℝ), ?_, ?_⟩
  · exact_mod_cast (show 0 < Cnn from pos_iff_ne_zero.mpr hCnn)
  · intro i χ
    have h := hbound i χ
    calc
      ‖R i χ‖ = ‖((R i).restrictScalars ℝ) χ‖ := rfl
      _ ≤ (Cnn •
          s.sup (schwartzSeminormFamily ℝ
            (Section43SpatialSpace d k) ℂ)) χ := h
      _ = (Cnn : ℝ) *
          s.sup (schwartzSeminormFamily ℂ
            (Section43SpatialSpace d k) ℂ) χ := by
        rw [Seminorm.smul_apply, hsup s χ]
        rfl

omit [NeZero d] in
/-- Banach-Steinhaus turns pointwise boundedness of the time-indexed spatial
distributions into one finite Schwartz-seminorm bound, uniform on the whole
declared time region. -/
theorem exists_uniform_schwartz_bound_osiiTimeSpatial_of_pointwiseBoundedOn
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hbounded : OSIITimeSpatialPointwiseBoundedOn R U) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ τ ∈ U, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ‖R τ χ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ := by
  let K := {τ : Fin k → ℝ // τ ∈ U}
  have hK :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ τ : K, ‖R τ.1 χ‖ ≤ C := by
    intro χ
    obtain ⟨C, hC⟩ := hbounded χ
    exact ⟨C, fun τ => hC τ.1 τ.2⟩
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiSpatial
      (R := fun τ : K => R τ.1) hK
  exact ⟨s, C, hC, fun τ hτ χ => hbound ⟨τ, hτ⟩ χ⟩

omit [NeZero d] in
/-- Weak holomorphy gives a finite Schwartz-seminorm bound for a continuation
stage, uniform on every compact subset of its carrier. -/
theorem exists_uniform_schwartz_bound_osiiStage_on_compact
    (A : OSIITimeContinuationStage d k)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ A.carrier) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ ζ ∈ K, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ‖A.distribution ζ χ‖ ≤
          C * s.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d k) ℂ) χ := by
  have hbounded :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ ζ : K, ‖A.distribution ζ.1 χ‖ ≤ C := by
    intro χ
    obtain ⟨C, hC⟩ :=
      hK_compact.exists_bound_of_continuousOn
        ((A.weaklyHolomorphic χ).continuousOn.mono hK_subset)
    exact ⟨C, fun ζ => hC ζ.1 ζ.2⟩
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiSpatial
      (R := fun ζ : K => A.distribution ζ.1) hbounded
  exact ⟨s, C, hC, fun ζ hζ χ => hbound ⟨ζ, hζ⟩ χ⟩

omit [NeZero d] in
/-- Compact-local pointwise boundedness makes a complex-time family of
spatial distributions uniformly equicontinuous on each compact carrier. -/
theorem uniformEquicontinuous_osiiSpatialDistribution_on_compact
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hF : OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    UniformEquicontinuous
      (fun ζ : K => fun χ : SchwartzMap (Section43SpatialSpace d k) ℂ =>
        F ζ.1 χ) := by
  let T :
      K →
        SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℝ] ℂ :=
    fun ζ => (F ζ.1).restrictScalars ℝ
  have hT :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ ζ : K, ‖T ζ χ‖ ≤ C := by
    intro χ
    obtain ⟨C, hC⟩ := hF K hK_compact hK_subset χ
    exact ⟨C, fun ζ => by simpa [T] using hC ζ.1 ζ.2⟩
  simpa [T] using
    (SchwartzMap.tempered_equicontinuous
      (E := Section43SpatialSpace d k) (F := ℂ) (G := ℂ)
      (T := T) hT)

omit [NeZero d] in
/-- Convergent spatial Schwartz tests converge uniformly after pairing with a
compact-locally pointwise bounded complex-time distribution family. -/
theorem tendstoUniformlyOn_osiiSpatialPairing_of_tendsto
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hF : OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U)
    {χN : ℕ → SchwartzMap (Section43SpatialSpace d k) ℂ}
    {χ : SchwartzMap (Section43SpatialSpace d k) ℂ}
    (hχN : Tendsto χN atTop (nhds χ))
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    TendstoUniformlyOn
      (fun q ζ => F ζ (χN q))
      (fun ζ => F ζ χ) atTop K := by
  have hequi :=
    uniformEquicontinuous_osiiSpatialDistribution_on_compact
      F U hF K hK_compact hK_subset
  intro V hV
  have hpair :
      Tendsto (fun q => (χ, χN q)) atTop
        (uniformity
          (SchwartzMap (Section43SpatialSpace d k) ℂ)) :=
    Uniform.tendsto_nhds_right.mp hχN
  filter_upwards [hpair (hequi V hV)] with q hq
  intro ζ hζ
  simpa using hq ⟨ζ, hζ⟩

omit [NeZero d] in
/-- The preceding convergence is locally uniform throughout an open complex
time carrier. -/
theorem tendstoLocallyUniformlyOn_osiiSpatialPairing_of_tendsto
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hU : IsOpen U)
    (hF : OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U)
    {χN : ℕ → SchwartzMap (Section43SpatialSpace d k) ℂ}
    {χ : SchwartzMap (Section43SpatialSpace d k) ℂ}
    (hχN : Tendsto χN atTop (nhds χ)) :
    TendstoLocallyUniformlyOn
      (fun q ζ => F ζ (χN q))
      (fun ζ => F ζ χ) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hK_subset hK_compact
  exact tendstoUniformlyOn_osiiSpatialPairing_of_tendsto
    F U hF hχN K hK_compact hK_subset

omit [NeZero d] in
/-- Weak holomorphy on compactly supported spatial tests extends to all
spatial Schwartz tests under compact-local pointwise boundedness. -/
theorem osiiWeaklyHolomorphicOn_of_compactSupport
    (F : OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hU : IsOpen U)
    (hF : OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U)
    (hcompact :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          DifferentiableOn ℂ (fun ζ => F ζ χ) U) :
    OSIIWeaklyHolomorphicOn F U := by
  intro χ
  let D : Set (SchwartzMap (Section43SpatialSpace d k) ℂ) :=
    {ψ | HasCompactSupport
      (ψ : Section43SpatialSpace d k → ℂ)}
  have hχ_closure :
      χ ∈ closure D := by
    have hD : Dense D := by
      simpa [D] using dense_section43Spatial_hasCompactSupport d k
    simpa [hD.closure_eq]
  obtain ⟨χN, hχN_compact, hχN⟩ :=
    mem_closure_iff_seq_limit.mp hχ_closure
  have hlocally :=
    tendstoLocallyUniformlyOn_osiiSpatialPairing_of_tendsto
      F U hU hF hχN
  apply hlocally.differentiableOn_finite
  · exact Filter.Eventually.of_forall fun q =>
      hcompact (χN q) (by simpa [D] using hχN_compact q)
  · exact hU

omit [NeZero d] in
/-- Weak scalar continuity plus the uniform Schwartz-seminorm bound makes the
pairing with a time-dependent spatial slice continuous. -/
theorem continuousOn_osiiMovingSpatialSlicePairing
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hscalar : ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ContinuousOn (fun τ => R τ χ) U)
    (s : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ τ ∈ U, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ‖R τ χ‖ ≤
        C * s.sup
          (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ)
    (F : SchwartzNPoint d k) :
    ContinuousOn
      (fun τ => R τ (osiiFullSourceSpatialSlice F τ)) U := by
  let p : Seminorm ℂ
      (SchwartzMap (Section43SpatialSpace d k) ℂ) :=
    s.sup (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ)
  have hp_cont : Continuous p := by
    refine Seminorm.continuous_of_le ?_
      (show p ≤ ∑ i ∈ s,
          schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ i by
        simpa [p] using Seminorm.finset_sup_le_sum
          (schwartzSeminormFamily ℂ
            (Section43SpatialSpace d k) ℂ) s)
    change Continuous
      (fun x =>
        Seminorm.coeFnAddMonoidHom ℂ
          (SchwartzMap (Section43SpatialSpace d k) ℂ)
          (∑ i ∈ s,
            schwartzSeminormFamily ℂ
              (Section43SpatialSpace d k) ℂ i) x)
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      (schwartz_withSeminorms ℂ
        (Section43SpatialSpace d k) ℂ).continuous_seminorm i
  intro τ hτ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hscalarδ⟩ :=
    (Metric.continuousWithinAt_iff.mp
      ((hscalar (osiiFullSourceSpatialSlice F τ)) τ hτ)) (ε / 2) hε2
  have hsemi_cont :
      ContinuousAt
        (fun υ => p
          (osiiFullSourceSpatialSlice F υ -
            osiiFullSourceSpatialSlice F τ)) τ := by
    have hsub :
        Continuous
          (fun υ => osiiFullSourceSpatialSlice F υ -
            osiiFullSourceSpatialSlice F τ) :=
      (continuous_osiiFullSourceSpatialSlice F).sub continuous_const
    exact hp_cont.continuousAt.comp hsub.continuousAt
  obtain ⟨δ₂, hδ₂, hsemiδ⟩ :=
    (Metric.continuousAt_iff.mp hsemi_cont)
      (ε / (2 * C)) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro υ hυ hdist
  have hdist₁ : dist υ τ < δ₁ :=
    hdist.trans_le (min_le_left _ _)
  have hdist₂ : dist υ τ < δ₂ :=
    hdist.trans_le (min_le_right _ _)
  have hscalar_lt :
      dist
          (R υ (osiiFullSourceSpatialSlice F τ))
          (R τ (osiiFullSourceSpatialSlice F τ)) < ε / 2 :=
    hscalarδ hυ hdist₁
  have hsemi_lt :
      p (osiiFullSourceSpatialSlice F υ -
          osiiFullSourceSpatialSlice F τ) < ε / (2 * C) := by
    have h := hsemiδ hdist₂
    simpa [p, Real.dist_eq, abs_of_nonneg (apply_nonneg p _)] using h
  have hfirst :
      ‖R υ (osiiFullSourceSpatialSlice F υ -
        osiiFullSourceSpatialSlice F τ)‖ < ε / 2 := by
    calc
      ‖R υ (osiiFullSourceSpatialSlice F υ -
          osiiFullSourceSpatialSlice F τ)‖
          ≤ C * p (osiiFullSourceSpatialSlice F υ -
              osiiFullSourceSpatialSlice F τ) := by
            simpa [p] using
              hbound υ hυ
                (osiiFullSourceSpatialSlice F υ -
                  osiiFullSourceSpatialSlice F τ)
      _ < C * (ε / (2 * C)) := by
            exact mul_lt_mul_of_pos_left hsemi_lt hC
      _ = ε / 2 := by field_simp [hC.ne']
  calc
    dist
        (R υ (osiiFullSourceSpatialSlice F υ))
        (R τ (osiiFullSourceSpatialSlice F τ))
        =
      ‖R υ (osiiFullSourceSpatialSlice F υ) -
        R τ (osiiFullSourceSpatialSlice F τ)‖ := by
          rw [dist_eq_norm]
    _ = ‖R υ
          (osiiFullSourceSpatialSlice F υ -
            osiiFullSourceSpatialSlice F τ) +
          (R υ (osiiFullSourceSpatialSlice F τ) -
            R τ (osiiFullSourceSpatialSlice F τ))‖ := by
        congr 1
        rw [map_sub]
        abel
    _ ≤ ‖R υ
          (osiiFullSourceSpatialSlice F υ -
            osiiFullSourceSpatialSlice F τ)‖ +
          ‖R υ (osiiFullSourceSpatialSlice F τ) -
            R τ (osiiFullSourceSpatialSlice F τ)‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add hfirst
          (by simpa [dist_eq_norm] using hscalar_lt)
    _ = ε := by ring

/-- Scalar convolution of a time-indexed spatial distribution against the
moving spatial slices of a full difference-coordinate Schwartz source. -/
noncomputable def osiiMovingSpatialSliceIntegral
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (F : SchwartzNPoint d k) : ℂ :=
  ∫ τ : Fin k → ℝ,
    ρ τ * R τ (osiiFullSourceSpatialSlice F τ)

omit [NeZero d] in
theorem integrable_osiiMovingSpatialSlicePairing
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (hscalar : ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ContinuousOn (fun τ => R τ χ) U)
    (hbounded : OSIITimeSpatialPointwiseBoundedOn R U)
    (F : SchwartzNPoint d k) :
    Integrable (fun τ : Fin k → ℝ =>
      ρ τ * R τ (osiiFullSourceSpatialSlice F τ)) := by
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiTimeSpatial_of_pointwiseBoundedOn
      R U hbounded
  have hmove :
      ContinuousOn
        (fun τ => R τ (osiiFullSourceSpatialSlice F τ)) U :=
    continuousOn_osiiMovingSpatialSlicePairing
      R U hscalar s C hC hbound F
  have hmaps :
      Set.MapsTo (fun y : Fin k → ℝ => 0 + y)
        (tsupport (ρ : (Fin k → ℝ) → ℂ)) U := by
    intro y hy
    simpa using hρ_support hy
  simpa using
    integrable_schwartz_mul_continuousOn_shift_of_tsupport_mapsTo
      ρ (fun τ => R τ (osiiFullSourceSpatialSlice F τ)) 0 U
      hρ_compact hmaps hmove

/-- On an elementary time/spatial tensor, the moving-slice convolution is
exactly the existing cutoff/ordered-pullback full-source functional. -/
theorem osiiMovingSpatialSliceIntegral_timeSpatialTensor_eq
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (ρ φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (hrep : OSIITimeSpatialRepresentsDistributionOn W R U) :
    osiiMovingSpatialSliceIntegral ρ R
        (section43NPointTimeSpatialTensor d k φ χ) =
      W (section43OrderedPullbackFullCutoffCLM d k ρ
        (section43NPointTimeSpatialTensor d k φ χ)) := by
  let ρφ : SchwartzMap (Fin k → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ρ : (Fin k → ℝ) → ℂ) φ
  have hρφ_compact :
      HasCompactSupport (ρφ : (Fin k → ℝ) → ℂ) := by
    have hfun :
        (ρφ : (Fin k → ℝ) → ℂ) =
          (ρ : (Fin k → ℝ) → ℂ) * (φ : (Fin k → ℝ) → ℂ) := by
      funext τ
      simp [ρφ, SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth]
    rw [hfun]
    exact hρ_compact.mul_right
  have hρφ_support :
      tsupport (ρφ : (Fin k → ℝ) → ℂ) ⊆ U := by
    intro τ hτ
    exact hρ_support
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ) (g := (ρ : (Fin k → ℝ) → ℂ)) (f := φ) hτ).2)
  have hrepresented :=
    hrep χ ρφ ⟨hρφ_compact, hρφ_support⟩
  rw [section43OrderedPullbackFullCutoffCLM_timeSpatialTensor]
  change (∫ τ : Fin k → ℝ,
      ρ τ * R τ (osiiFullSourceSpatialSlice
        (section43NPointTimeSpatialTensor d k φ χ) τ)) =
    W (section43OrderedPullbackTimeSpatialTensorCLM d k χ ρφ)
  rw [show
      W (section43OrderedPullbackTimeSpatialTensorCLM d k χ ρφ) =
        ∫ τ : Fin k → ℝ, R τ χ * ρφ τ from hrepresented]
  apply integral_congr_ae
  filter_upwards [] with τ
  simp [osiiFullSourceSpatialSlice_timeSpatialTensor, ρφ,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
    mul_comm, mul_assoc]

omit [NeZero d] in
/-- A spatial slice is bounded by the corresponding time/spatial Schwartz
seminorm of the full source. -/
theorem osiiFullSourceSpatialSlice_seminorm_le
    (F : SchwartzNPoint d k) (τ : Fin k → ℝ) (p l : ℕ) :
    SchwartzMap.seminorm ℂ p l (osiiFullSourceSpatialSlice F τ) ≤
      SchwartzMap.seminorm ℂ p l
        (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) := by
  apply SchwartzMap.seminorm_le_bound ℂ p l _ (apply_nonneg _ _)
  intro η
  calc
    ‖η‖ ^ p *
        ‖iteratedFDeriv ℝ l
          (fun x => osiiFullSourceSpatialSlice F τ x) η‖
        ≤ ‖η‖ ^ p *
          ‖iteratedFDeriv ℝ l
            (⇑(nPointTimeSpatialSchwartzCLE (d := d) (n := k) F))
            (τ, η)‖ := by
          apply mul_le_mul_of_nonneg_left
          · simpa [osiiFullSourceSpatialSlice] using
              SCV.norm_iteratedFDeriv_partialEval₁_le
                (f := nPointTimeSpatialSchwartzCLE
                  (d := d) (n := k) F) τ l η
          · positivity
    _ ≤ ‖(τ, η)‖ ^ p *
          ‖iteratedFDeriv ℝ l
            (⇑(nPointTimeSpatialSchwartzCLE (d := d) (n := k) F))
            (τ, η)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          gcongr
          exact le_max_right _ _
    _ ≤ SchwartzMap.seminorm ℂ p l
          (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) :=
      SchwartzMap.le_seminorm ℂ p l
        (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) (τ, η)

omit [NeZero d] in
theorem osiiFullSourceSpatialSlice_finsetSeminorm_le
    (F : SchwartzNPoint d k) (τ : Fin k → ℝ)
    (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ
        (Section43SpatialSpace d k) ℂ)
        (osiiFullSourceSpatialSlice F τ) ≤
      s.sup (schwartzSeminormFamily ℂ
        (Section43TimeSpatialSpace d k) ℂ)
        (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) := by
  apply Seminorm.finset_sup_apply_le
  · exact apply_nonneg _ _
  · intro a ha
    exact (osiiFullSourceSpatialSlice_seminorm_le F τ a.1 a.2).trans
      (Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily ℂ
          (Section43TimeSpatialSpace d k) ℂ)
        (s := s)
        (x := nPointTimeSpatialSchwartzCLE (d := d) (n := k) F)
        ha)

omit [NeZero d] in
/-- Uniform finite-seminorm bound for the moving-slice scalar convolution. -/
theorem norm_osiiMovingSpatialSliceIntegral_le
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (s : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ τ ∈ U, ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ‖R τ χ‖ ≤
        C * s.sup
          (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ)
    (F : SchwartzNPoint d k) :
    ‖osiiMovingSpatialSliceIntegral ρ R F‖ ≤
      (∫ τ : Fin k → ℝ, ‖ρ τ‖) * C *
        s.sup (schwartzSeminormFamily ℂ
          (Section43TimeSpatialSpace d k) ℂ)
          (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F) := by
  let S : ℝ :=
    s.sup (schwartzSeminormFamily ℂ
      (Section43TimeSpatialSpace d k) ℂ)
      (nPointTimeSpatialSchwartzCLE (d := d) (n := k) F)
  have hS : 0 ≤ S := apply_nonneg _ _
  have hdom :
      Integrable (fun τ : Fin k → ℝ => ‖ρ τ‖ * (C * S)) := by
    simpa using (SchwartzMap.integrable ρ).norm.mul_const (C * S)
  have hpoint :
      ∀ τ : Fin k → ℝ,
        ‖ρ τ * R τ (osiiFullSourceSpatialSlice F τ)‖ ≤
          ‖ρ τ‖ * (C * S) := by
    intro τ
    by_cases hρτ : ρ τ = 0
    · simp [hρτ]
    · have hτU : τ ∈ U := by
        apply hρ_support
        exact subset_tsupport _
          (by simpa [Function.mem_support] using hρτ)
      calc
        ‖ρ τ * R τ (osiiFullSourceSpatialSlice F τ)‖ =
            ‖ρ τ‖ * ‖R τ (osiiFullSourceSpatialSlice F τ)‖ := norm_mul _ _
        _ ≤ ‖ρ τ‖ *
            (C * s.sup
              (schwartzSeminormFamily ℂ
                (Section43SpatialSpace d k) ℂ)
              (osiiFullSourceSpatialSlice F τ)) := by
          exact mul_le_mul_of_nonneg_left
            (hbound τ hτU (osiiFullSourceSpatialSlice F τ))
            (norm_nonneg _)
        _ ≤ ‖ρ τ‖ * (C * S) := by
          gcongr
          exact osiiFullSourceSpatialSlice_finsetSeminorm_le F τ s
  calc
    ‖osiiMovingSpatialSliceIntegral ρ R F‖
        ≤ ∫ τ : Fin k → ℝ,
          ‖ρ τ * R τ (osiiFullSourceSpatialSlice F τ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ τ : Fin k → ℝ, ‖ρ τ‖ * (C * S) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hdom
        (Filter.Eventually.of_forall hpoint)
    _ = (∫ τ : Fin k → ℝ, ‖ρ τ‖) * C * S := by
      rw [integral_mul_const]
      ring

omit [NeZero d] in
/-- The moving-slice convolution is a continuous complex-linear functional of
the full difference-coordinate Schwartz source. -/
theorem exists_osiiMovingSpatialSliceIntegralCLM
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (hscalar : ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ContinuousOn (fun τ => R τ χ) U)
    (hbounded : OSIITimeSpatialPointwiseBoundedOn R U) :
    ∃ L : SchwartzNPoint d k →L[ℂ] ℂ,
      ∀ F, L F = osiiMovingSpatialSliceIntegral ρ R F := by
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiTimeSpatial_of_pointwiseBoundedOn
      R U hbounded
  let e := nPointTimeSpatialSchwartzCLE (d := d) (n := k)
  let A :
      SchwartzMap (Section43TimeSpatialSpace d k) ℂ → ℂ :=
    fun G => osiiMovingSpatialSliceIntegral ρ R (e.symm G)
  have hint :
      ∀ G : SchwartzMap (Section43TimeSpatialSpace d k) ℂ,
        Integrable (fun τ : Fin k → ℝ =>
          ρ τ * R τ (SCV.schwartzPartialEval₁ G τ)) := by
    intro G
    simpa [e, osiiFullSourceSpatialSlice] using
      integrable_osiiMovingSpatialSlicePairing
        ρ R U hρ_compact hρ_support hscalar hbounded (e.symm G)
  let L₀ :
      SchwartzMap (Section43TimeSpatialSpace d k) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) A
      (fun G H => by
        change
          (∫ τ : Fin k → ℝ,
              ρ τ * R τ
                (SCV.schwartzPartialEval₁ (G + H) τ)) =
            (∫ τ : Fin k → ℝ,
              ρ τ * R τ (SCV.schwartzPartialEval₁ G τ)) +
            ∫ τ : Fin k → ℝ,
              ρ τ * R τ (SCV.schwartzPartialEval₁ H τ)
        rw [← integral_add (hint G) (hint H)]
        apply integral_congr_ae
        filter_upwards [] with τ
        have hslice :
            SCV.schwartzPartialEval₁ (G + H) τ =
              SCV.schwartzPartialEval₁ G τ +
                SCV.schwartzPartialEval₁ H τ := by
          ext η
          rfl
        rw [hslice, map_add, mul_add])
      (fun a G => by
        change
          (∫ τ : Fin k → ℝ,
              ρ τ * R τ
                (SCV.schwartzPartialEval₁ (a • G) τ)) =
            a • ∫ τ : Fin k → ℝ,
              ρ τ * R τ (SCV.schwartzPartialEval₁ G τ)
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with τ
        have hslice :
            SCV.schwartzPartialEval₁ (a • G) τ =
              a • SCV.schwartzPartialEval₁ G τ := by
          ext η
          rfl
        rw [hslice, map_smul]
        simp only [smul_eq_mul]
        ring)
      (by
        refine ⟨s, (∫ τ : Fin k → ℝ, ‖ρ τ‖) * C, ?_, ?_⟩
        · exact mul_nonneg
            (integral_nonneg fun _ => norm_nonneg _) hC.le
        · intro G
          simpa [A, e] using
            norm_osiiMovingSpatialSliceIntegral_le
              ρ R U hρ_support s C hC.le hbound (e.symm G))
  refine ⟨L₀.comp e.toContinuousLinearMap, ?_⟩
  intro F
  rfl

/-- Fixed-spatial local representation extends to the moving spatial slices
of every full Schwartz source.  This is the full-source real-edge bridge used
by the Chapter V scalar chart. -/
theorem osiiMovingSpatialSliceIntegral_eq_orderedPullbackFullCutoff
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (hscalar : ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
      ContinuousOn (fun τ => R τ χ) U)
    (hbounded : OSIITimeSpatialPointwiseBoundedOn R U)
    (hrep : OSIITimeSpatialRepresentsDistributionOn W R U)
    (F : SchwartzNPoint d k) :
    osiiMovingSpatialSliceIntegral ρ R F =
      W (section43OrderedPullbackFullCutoffCLM d k ρ F) := by
  obtain ⟨L, hL⟩ :=
    exists_osiiMovingSpatialSliceIntegralCLM
      ρ R U hρ_compact hρ_support hscalar hbounded
  let S : Set (SchwartzNPoint d k) :=
    {G | ∃ φ : SchwartzMap (Fin k → ℝ) ℂ,
      ∃ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        G = section43NPointTimeSpatialTensor d k φ χ}
  have hS :
      Dense
        (((Submodule.span ℂ S) :
          Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k)) := by
    simpa [S] using
      (dense_section43NPointTimeSpatialTensor_span_of_factor_dense
        (d := d) (n := k)
        (St := Set.univ) (Sx := Set.univ) dense_univ dense_univ)
  have hEq :
      L = W.comp (section43OrderedPullbackFullCutoffCLM d k ρ) := by
    apply ContinuousLinearMap.ext_on hS
    intro G hG
    rcases hG with ⟨φ, χ, rfl⟩
    rw [hL]
    exact osiiMovingSpatialSliceIntegral_timeSpatialTensor_eq
      W ρ φ χ R U hρ_compact hρ_support hrep
  calc
    osiiMovingSpatialSliceIntegral ρ R F = L F := (hL F).symm
    _ = W (section43OrderedPullbackFullCutoffCLM d k ρ F) := by
      rw [hEq]
      rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero d] in
/-- Pointwise limits of spatial Schwartz distributions are again spatial
Schwartz distributions.

Algebraic complex linearity follows by uniqueness of scalar limits.
Continuity is the Banach-Steinhaus conclusion for the underlying real-linear
maps on the barrelled Schwartz space. -/
theorem existsUnique_osiiSpatialDistribution_of_pointwise_tendsto
    (T : ℕ → OSIISpatialDistribution d k)
    (F : SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ)
    (hT : ∀ χ,
      Tendsto (fun n => T n χ) atTop (nhds (F χ))) :
    ∃! S : OSIISpatialDistribution d k, ∀ χ, S χ = F χ := by
  have hfun :
      Tendsto (fun n χ => T n χ) atTop (nhds F) := by
    rw [tendsto_pi_nhds]
    exact hT
  have hF_add :
      ∀ χ ψ, F (χ + ψ) = F χ + F ψ := by
    intro χ ψ
    apply tendsto_nhds_unique (hT (χ + ψ))
    simpa only [map_add] using (hT χ).add (hT ψ)
  have hF_smul :
      ∀ c : ℂ, ∀ χ, F (c • χ) = c • F χ := by
    intro c χ
    apply tendsto_nhds_unique (hT (c • χ))
    simpa only [map_smul] using
      (tendsto_const_nhds.smul (hT χ))
  let LR :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℝ] ℂ :=
    continuousLinearMapOfTendsto
      (fun n => (T n).restrictScalars ℝ) hfun
  have hF_cont : Continuous F := by
    simpa [LR, continuousLinearMapOfTendsto] using LR.continuous
  let S : OSIISpatialDistribution d k :=
    { toLinearMap :=
        { toFun := F
          map_add' := hF_add
          map_smul' := hF_smul }
      cont := hF_cont }
  refine ⟨S, ?_, ?_⟩
  · intro χ
    rfl
  · intro S' hS'
    ext χ
    exact (hS' χ).trans rfl

/-- The canonical spatial distribution obtained from a pointwise-convergent
sequence of spatial-distribution approximants. -/
noncomputable def osiiSpatialDistributionOfPointwiseLimit
    (T : ℕ → OSIISpatialDistribution d k)
    (F : SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ)
    (hT : ∀ χ,
      Tendsto (fun n => T n χ) atTop (nhds (F χ))) :
    OSIISpatialDistribution d k :=
  Classical.choose
    (existsUnique_osiiSpatialDistribution_of_pointwise_tendsto T F hT)

omit [NeZero d] in
@[simp] theorem osiiSpatialDistributionOfPointwiseLimit_apply
    (T : ℕ → OSIISpatialDistribution d k)
    (F : SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ)
    (hT : ∀ χ,
      Tendsto (fun n => T n χ) atTop (nhds (F χ)))
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    osiiSpatialDistributionOfPointwiseLimit T F hT χ = F χ :=
  (Classical.choose_spec
    (existsUnique_osiiSpatialDistribution_of_pointwise_tendsto T F hT)).1 χ

omit [NeZero d] in
/-- Compact-source convergence plus pointwise boundedness of the approximating
spatial distributions constructs the limiting spatial distribution.

This is stronger than the target-relative extension theorem below: no
pre-existing candidate `S` is required.  Banach-Steinhaus gives a common
Schwartz-seminorm bound for the approximants, density of compactly supported
spatial tests makes every scalar orbit Cauchy, and completeness of `ℂ`
supplies the pointwise limits. -/
theorem existsUnique_osiiSpatialDistribution_of_compactSupport_tendsto_of_pointwiseBounded
    (T : ℕ → OSIISpatialDistribution d k)
    (F : SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ)
    (hcompact :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          Tendsto (fun n => T n χ) atTop (nhds (F χ)))
    (hbounded :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∃ C : ℝ, ∀ n, ‖T n χ‖ ≤ C) :
    ∃! S : OSIISpatialDistribution d k,
      (∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          S χ = F χ) ∧
      ∀ χ, Tendsto (fun n => T n χ) atTop (nhds (S χ)) := by
  let pFamily :=
    schwartzSeminormFamily ℝ (Section43SpatialSpace d k) ℂ
  obtain ⟨s, C, hCne, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Section43SpatialSpace d k) (F := ℂ) (G := ℂ)
      (T := fun n => (T n).restrictScalars ℝ)
      hbounded
  let p : Seminorm ℝ
      (SchwartzMap (Section43SpatialSpace d k) ℂ) :=
    s.sup pFamily
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast (show 0 < C from pos_iff_ne_zero.mpr hCne)
  have hp_cont : Continuous p := by
    refine Seminorm.continuous_of_le ?_
      (show p ≤ ∑ i ∈ s, pFamily i by
        simpa [p, pFamily] using
          Seminorm.finset_sup_le_sum pFamily s)
    change Continuous
      (fun x =>
        Seminorm.coeFnAddMonoidHom ℝ
          (SchwartzMap (Section43SpatialSpace d k) ℂ)
          (∑ i ∈ s, pFamily i) x)
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      (schwartz_withSeminorms ℝ
        (Section43SpatialSpace d k) ℂ).continuous_seminorm i
  have hcauchy :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        CauchySeq (fun n => T n χ) := by
    intro χ
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let δ : ℝ := ε / (4 * (C : ℝ))
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hnear :
        {ψ : SchwartzMap (Section43SpatialSpace d k) ℂ |
          p (χ - ψ) < δ} ∈ nhds χ := by
      have hcont :
          ContinuousAt
            (fun ψ : SchwartzMap (Section43SpatialSpace d k) ℂ =>
              p (χ - ψ)) χ :=
        hp_cont.continuousAt.comp
          (continuousAt_const.sub continuousAt_id)
      have hpre :=
        hcont.preimage_mem_nhds
          (Metric.ball_mem_nhds (p (χ - χ)) hδpos)
      filter_upwards [hpre] with ψ hψ
      change dist (p (χ - ψ)) (p (χ - χ)) < δ at hψ
      simpa [Real.dist_eq, abs_of_nonneg (apply_nonneg p _)] using hψ
    rcases
      (dense_section43Spatial_hasCompactSupport d k).inter_nhds_nonempty
        hnear with
      ⟨ψ, hψcompact, hψnear⟩
    have hψcauchy : CauchySeq (fun n => T n ψ) :=
      (hcompact ψ hψcompact).cauchySeq
    rcases
      Metric.cauchySeq_iff.mp hψcauchy (ε / 2) (by linarith) with
      ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm_bound :
        ‖T m (χ - ψ)‖ ≤ (C : ℝ) * p (χ - ψ) := by
      simpa [p, pFamily, smul_eq_mul] using hbound m (χ - ψ)
    have hn_bound :
        ‖T n (χ - ψ)‖ ≤ (C : ℝ) * p (χ - ψ) := by
      simpa [p, pFamily, smul_eq_mul] using hbound n (χ - ψ)
    have hsmall :
        (C : ℝ) * p (χ - ψ) < ε / 4 := by
      have := hψnear
      dsimp [δ] at this
      calc
        (C : ℝ) * p (χ - ψ) <
            (C : ℝ) * (ε / (4 * (C : ℝ))) :=
          mul_lt_mul_of_pos_left this hCpos
        _ = ε / 4 := by field_simp [ne_of_gt hCpos]
    have hmiddle :
        ‖T m ψ - T n ψ‖ < ε / 2 := by
      simpa [dist_eq_norm] using hN m hm n hn
    have hsplit :
        T m χ - T n χ =
          T m (χ - ψ) + (T m ψ - T n ψ) - T n (χ - ψ) := by
      rw [map_sub, map_sub]
      abel
    rw [dist_eq_norm, hsplit]
    calc
      ‖T m (χ - ψ) + (T m ψ - T n ψ) - T n (χ - ψ)‖
          ≤ ‖T m (χ - ψ) + (T m ψ - T n ψ)‖ +
              ‖T n (χ - ψ)‖ := norm_sub_le _ _
      _ ≤ (‖T m (χ - ψ)‖ + ‖T m ψ - T n ψ‖) +
              ‖T n (χ - ψ)‖ := by
            gcongr
            exact norm_add_le _ _
      _ < ε := by linarith
  let L :
      SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ :=
    fun χ => Classical.choose
      (cauchySeq_tendsto_of_complete (hcauchy χ))
  have hL :
      ∀ χ, Tendsto (fun n => T n χ) atTop (nhds (L χ)) := by
    intro χ
    exact Classical.choose_spec
      (cauchySeq_tendsto_of_complete (hcauchy χ))
  obtain ⟨S, hS, hS_unique⟩ :=
    existsUnique_osiiSpatialDistribution_of_pointwise_tendsto T L hL
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro χ hχcompact
      exact (hS χ).trans
        (tendsto_nhds_unique (hL χ) (hcompact χ hχcompact))
    · intro χ
      simpa [hS χ] using hL χ
  · intro S' hS'
    ext χ
    have hTS :
        Tendsto (fun n => T n χ) atTop (nhds (S χ)) := by
      simpa [hS χ] using hL χ
    exact tendsto_nhds_unique (hS'.2 χ) hTS

end OSReconstruction
