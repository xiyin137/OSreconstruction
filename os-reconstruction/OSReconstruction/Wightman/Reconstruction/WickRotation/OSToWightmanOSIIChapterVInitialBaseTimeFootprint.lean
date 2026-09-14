/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource















noncomputable section

open Complex Set Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The coordinates of the initial source which remain compact independently
of the reduced spatial test and its truncation level. -/
abbrev InitialBaseTimeSpace (d k : ℕ) :=
  SpacetimeDim d × (Fin k → ℝ)

/-- Extract the absolute basepoint and the consecutive Euclidean time gaps
from a full configuration. -/
noncomputable def initialBaseTimeProjectionCLM (d k : ℕ) [NeZero d] :
    NPointDomain d (k + 1) →L[ℝ] InitialBaseTimeSpace d k :=
  (ContinuousLinearMap.proj
      (R := ℝ) (ι := Fin (k + 1))
      (φ := fun _ => SpacetimeDim d) 0).prod
    (reducedTimeProjectionCLM d k)

@[simp] theorem initialBaseTimeProjectionCLM_apply
    (x : NPointDomain d (k + 1)) :
    initialBaseTimeProjectionCLM d k x =
      (x 0, reducedTimeProjectionCLM d k x) :=
  rfl

/-- The compact base/time footprint determined only by the fixed normalized
basepoint cutoff and the fixed reduced-time factor. -/
def initialBaseTimeFootprint
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    Set (InitialBaseTimeSpace d k) :=
  tsupport
      ((BHW.normalizedCutoffOfBump d).toSchwartz :
        SpacetimeDim d → ℂ) ×ˢ
    tsupport (φ : (Fin k → ℝ) → ℂ)

/-- The base/time footprint is compact whenever the reduced-time factor is
compactly supported. -/
theorem isCompact_initialBaseTimeFootprint
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    IsCompact (initialBaseTimeFootprint (d := d) φ) :=
  (BHW.normalizedCutoffOfBump_hasCompactSupport d).isCompact.prod
    hφ.isCompact

/-- Every point in the support of the canonical full source has basepoint in
the support of the fixed normalized cutoff. -/
theorem basepoint_mem_tsupport_of_mem_initialReducedSpatialFullSource
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    x 0 ∈
      tsupport
        ((BHW.normalizedCutoffOfBump d).toSchwartz :
          SpacetimeDim d → ℂ) := by
  let f : NPointDomain d (k + 1) → ℂ :=
    ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
      SchwartzNPoint d (k + 1)) :
        NPointDomain d (k + 1) → ℂ)
  let p :
      NPointDomain d (k + 1) →L[ℝ] SpacetimeDim d :=
    ContinuousLinearMap.proj
      (R := ℝ) (ι := Fin (k + 1))
      (φ := fun _ => SpacetimeDim d) 0
  have hsupport :
      Function.support f ⊆
        p ⁻¹'
          tsupport
            ((BHW.normalizedCutoffOfBump d).toSchwartz :
              SpacetimeDim d → ℂ) := by
    intro y hy
    have hcutoff_ne :
        (BHW.normalizedCutoffOfBump d).toSchwartz (y 0) ≠ 0 := by
      intro hzero
      apply hy
      dsimp [f]
      rw [BHW.reducedTestLift_apply, hzero]
      simp
    simpa [p] using
      subset_tsupport
        ((BHW.normalizedCutoffOfBump d).toSchwartz :
          SpacetimeDim d → ℂ)
        (Function.mem_support.mpr hcutoff_ne)
  exact
    closure_minimal hsupport
      ((isClosed_tsupport
          ((BHW.normalizedCutoffOfBump d).toSchwartz :
            SpacetimeDim d → ℂ)).preimage p.continuous) hx

/-- The support of every canonical initial source projects into the same
compact base/time footprint, independently of the reduced spatial test. -/
theorem initialBaseTimeProjection_mem_footprint_of_mem_source
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    initialBaseTimeProjectionCLM d k x ∈
      initialBaseTimeFootprint (d := d) φ := by
  exact
    ⟨basepoint_mem_tsupport_of_mem_initialReducedSpatialFullSource
        φ χ x hx,
      reducedTimeProjection_mem_tsupport_of_mem_initialReducedSpatialFullSource
        φ χ x hx⟩

/-- Insert time gaps as reduced spacetime differences with zero spatial
components. -/
noncomputable def initialBaseTimeGapConfigurationCLM (d k : ℕ) :
    (Fin k → ℝ) →L[ℝ] NPointDomain d k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun τ i μ => if μ = 0 then τ i else 0
      map_add' := by
        intro τ σ
        ext i μ
        by_cases hμ : μ = 0
        · simp [hμ]
        · simp [hμ]
      map_smul' := by
        intro c τ
        ext i μ
        by_cases hμ : μ = 0
        · simp [hμ]
        · simp [hμ] }

@[simp] theorem initialBaseTimeGapConfigurationCLM_time
    (τ : Fin k → ℝ) (i : Fin k) :
    initialBaseTimeGapConfigurationCLM d k τ i 0 = τ i := by
  simp [initialBaseTimeGapConfigurationCLM]

/-- Reconstruct one absolute configuration from an absolute basepoint and
pure-time consecutive differences. Its spatial coordinates are irrelevant to
the natural chronological boxes, which depend only on Euclidean time. -/
noncomputable def initialBaseTimeConfigurationCLM (d k : ℕ) :
    InitialBaseTimeSpace d k →L[ℝ] NPointDomain d (k + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p i μ =>
        p.1 μ +
          diffVarSection d k
            (initialBaseTimeGapConfigurationCLM d k p.2) i μ
      map_add' := by
        intro p q
        ext i μ
        simp [map_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c p
        ext i μ
        simp [map_smul, mul_add] }

@[simp] theorem initialBaseTimeConfigurationCLM_apply
    (p : InitialBaseTimeSpace d k)
    (i : Fin (k + 1)) (μ : Fin (d + 1)) :
    initialBaseTimeConfigurationCLM d k p i μ =
      p.1 μ +
        diffVarSection d k
          (initialBaseTimeGapConfigurationCLM d k p.2) i μ :=
  rfl

/-- Consecutive absolute times in the reconstructed configuration differ by
the supplied gap coordinate. -/
theorem initialBaseTimeConfiguration_time_succ_sub
    (p : InitialBaseTimeSpace d k) (i : Fin k) :
    initialBaseTimeConfigurationCLM d k p i.succ 0 -
        initialBaseTimeConfigurationCLM d k p i.castSucc 0 =
      p.2 i := by
  rw [initialBaseTimeConfigurationCLM_apply,
    initialBaseTimeConfigurationCLM_apply,
    diffVarSection_succ]
  simp

/-- Positive gap coordinates reconstruct to strictly ordered absolute
Euclidean times. -/
theorem initialBaseTimeConfiguration_strictMono
    (p : InitialBaseTimeSpace d k)
    (hp : p.2 ∈ section43TimeStrictPositiveRegion k) :
    StrictMono
      (fun i : Fin (k + 1) =>
        initialBaseTimeConfigurationCLM d k p i 0) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hi := hp ⟨i.val, by omega⟩
  apply sub_pos.mp
  rw [initialBaseTimeConfiguration_time_succ_sub
    (d := d) p ⟨i.val, by omega⟩]
  exact hi

end OSIIChapterV
end OSReconstruction
