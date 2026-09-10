import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying

/-!
# Spatial-carrier exhaustion for the initial OS-II time stage

The sourcewise MZ continuation is constructed with compact spacetime
carriers, while the Chapter V initial stage must act on the full spatial
Schwartz space.  A single fixed carrier cannot give that unlocalized object.

This file records the neutral exhaustion passage.  If localized holomorphic
families converge on compactly supported spatial tests and are uniformly
pointwise bounded over both the carrier index and compact complex-time sets,
then Banach-Steinhaus constructs the full spatial distribution at every
complex time.  Compact-test holomorphy then extends to all spatial Schwartz
tests.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ}

/-- Localized spatial-distribution families converge to one weakly
holomorphic family on the full spatial Schwartz space.

The first hypothesis is the carrier-independence statement on compactly
supported spatial tests.  The second is the uniform estimate needed to pass
from those tests to arbitrary Schwartz tests.  No candidate limiting
distribution and no continuity of that candidate are assumed. -/
theorem exists_osiiSpatialDistributionFamily_of_compactSupport_exhaustion
    (T : ℕ → OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hU : IsOpen U)
    (hcompact :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          ∃ f : OSIITimeGapSpace k → ℂ,
            DifferentiableOn ℂ f U ∧
              ∀ ζ, ζ ∈ U →
                Tendsto (fun n => T n ζ χ) atTop (nhds (f ζ)))
    (hbounded :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K → K ⊆ U →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ∃ C : ℝ, ∀ n ζ, ζ ∈ K → ‖T n ζ χ‖ ≤ C) :
    ∃ F : OSIITimeGapSpace k → OSIISpatialDistribution d k,
      OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U ∧
        OSIIWeaklyHolomorphicOn F U ∧
          ∀ ζ, ζ ∈ U →
            ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
              Tendsto (fun n => T n ζ χ) atTop (nhds (F ζ χ)) := by
  let compactLimit :
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        OSIITimeGapSpace k → ℂ :=
    fun χ =>
      if hχ :
          HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) then
        Classical.choose (hcompact χ hχ)
      else
        0
  have hlimit :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∀ hχ :
          HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ),
          DifferentiableOn ℂ (compactLimit χ) U ∧
            ∀ ζ, ζ ∈ U →
              Tendsto
                (fun n => T n ζ χ) atTop
                (nhds (compactLimit χ ζ)) := by
    intro χ hχ
    simpa [compactLimit, hχ] using
      (Classical.choose_spec (hcompact χ hχ))
  have hexists :
      ∀ ζ, ζ ∈ U →
        ∃! S : OSIISpatialDistribution d k,
          (∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            HasCompactSupport
                (χ : Section43SpatialSpace d k → ℂ) →
              S χ = compactLimit χ ζ) ∧
            ∀ χ,
              Tendsto (fun n => T n ζ χ) atTop (nhds (S χ)) := by
    intro ζ hζ
    apply
      existsUnique_osiiSpatialDistribution_of_compactSupport_tendsto_of_pointwiseBounded
        (T := fun n => T n ζ)
        (F := fun χ => compactLimit χ ζ)
    · intro χ hχ
      exact (hlimit χ hχ).2 ζ hζ
    · intro χ
      obtain ⟨C, hC⟩ :=
        hbounded ({ζ} : Set (OSIITimeGapSpace k))
          isCompact_singleton (by simpa using hζ) χ
      exact ⟨C, fun n => hC n ζ (Set.mem_singleton ζ)⟩
  let S :
      {ζ : OSIITimeGapSpace k // ζ ∈ U} →
        OSIISpatialDistribution d k :=
    fun ζ => Classical.choose (hexists ζ.1 ζ.2)
  let F : OSIITimeGapSpace k → OSIISpatialDistribution d k :=
    fun ζ => if hζ : ζ ∈ U then S ⟨ζ, hζ⟩ else 0
  have hF_compact :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ∀ hχ :
          HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ),
          ∀ ζ, ζ ∈ U → F ζ χ = compactLimit χ ζ := by
    intro χ hχ ζ hζ
    simp only [F, dif_pos hζ]
    exact
      (Classical.choose_spec (hexists ζ hζ)).1.1 χ hχ
  have hF_tendsto :
      ∀ ζ, ζ ∈ U →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          Tendsto (fun n => T n ζ χ) atTop (nhds (F ζ χ)) := by
    intro ζ hζ χ
    simpa only [F, dif_pos hζ] using
      (Classical.choose_spec (hexists ζ hζ)).1.2 χ
  have hF_bounded :
      OSIIComplexTimeSpatialLocallyPointwiseBoundedOn F U := by
    intro K hK_compact hK_subset χ
    obtain ⟨C, hC⟩ := hbounded K hK_compact hK_subset χ
    refine ⟨C, ?_⟩
    intro ζ hζ
    apply le_of_tendsto
      (continuous_norm.continuousAt.tendsto.comp
        (hF_tendsto ζ (hK_subset hζ) χ))
    exact Filter.Eventually.of_forall fun n => hC n ζ hζ
  have hF_compact_holomorphic :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          DifferentiableOn ℂ (fun ζ => F ζ χ) U := by
    intro χ hχ
    exact
      (hlimit χ hχ).1.congr fun ζ hζ =>
        hF_compact χ hχ ζ hζ
  refine ⟨F, hF_bounded, ?_, hF_tendsto⟩
  exact
    osiiWeaklyHolomorphicOn_of_compactSupport
      F U hU hF_bounded hF_compact_holomorphic

/-- Route-facing form of the exhaustion theorem: the limiting family is
packaged directly as an OS-II time-continuation stage. -/
theorem exists_osiiTimeContinuationStage_of_compactSupport_exhaustion
    (T : ℕ → OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (U : Set (OSIITimeGapSpace k))
    (hU : IsOpen U)
    (hcompact :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        HasCompactSupport
            (χ : Section43SpatialSpace d k → ℂ) →
          ∃ f : OSIITimeGapSpace k → ℂ,
            DifferentiableOn ℂ f U ∧
              ∀ ζ, ζ ∈ U →
                Tendsto (fun n => T n ζ χ) atTop (nhds (f ζ)))
    (hbounded :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K → K ⊆ U →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ∃ C : ℝ, ∀ n ζ, ζ ∈ K → ‖T n ζ χ‖ ≤ C) :
    ∃ A : OSIITimeContinuationStage d k,
      A.carrier = U ∧
        OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
          A.distribution U ∧
        ∀ ζ, ζ ∈ U →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Tendsto (fun n => T n ζ χ) atTop
              (nhds (A.distribution ζ χ)) := by
  obtain ⟨F, hF_bounded, hF_holomorphic, hF_tendsto⟩ :=
    exists_osiiSpatialDistributionFamily_of_compactSupport_exhaustion
      T U hU hcompact hbounded
  let A : OSIITimeContinuationStage d k :=
    { carrier := U
      carrier_open := hU
      distribution := F
      weaklyHolomorphic := hF_holomorphic }
  exact ⟨A, rfl, hF_bounded, hF_tendsto⟩

end OSReconstruction
