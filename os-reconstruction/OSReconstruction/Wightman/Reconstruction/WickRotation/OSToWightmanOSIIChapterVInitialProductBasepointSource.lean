/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.HeadBlockDescent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialLift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTimeSpatialTensor
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct




















noncomputable section

open Complex MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

private theorem tsupport_precomp_subset_local
    {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

/-- Prepend one absolute spatial basepoint to a reduced Section 4.3 spatial
test, without applying a second difference-coordinate transform. -/
noncomputable def section43SpatialBasepointLiftCLM
    (d k : ℕ)
    (ρ : SchwartzMap (Fin d → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
  (section43SpatialSchwartzParticleCLE d (k + 1)).symm.toContinuousLinearMap.comp
    ((SchwartzMap.prependFieldCLMRight ρ).comp
      (section43SpatialSchwartzParticleCLE d k).toContinuousLinearMap)

@[simp]
theorem section43SpatialParticleCLE_prependBasepoint
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k) :
    section43SpatialParticleCLE d (k + 1)
        (section43SpatialPrependBasepoint x₀ η) =
      Fin.cons x₀ (section43SpatialParticleCLE d k η) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · simpa [section43SpatialParticleCLE_apply] using
      section43SpatialPrependBasepoint_zero
        (d := d) (k := k) x₀ η j
  · intro i
    simpa [section43SpatialParticleCLE_apply] using
      section43SpatialPrependBasepoint_succ
        (d := d) (k := k) x₀ η i j

@[simp]
theorem section43SpatialBasepointLiftCLM_apply_prependBasepoint
    (ρ : SchwartzMap (Fin d → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k) :
    section43SpatialBasepointLiftCLM d k ρ χ
        (section43SpatialPrependBasepoint x₀ η) =
      ρ x₀ * χ η := by
  change
    (SchwartzMap.prependFieldCLMRight ρ
      (section43SpatialSchwartzParticleCLE d k χ))
        (section43SpatialParticleCLE d (k + 1)
          (section43SpatialPrependBasepoint x₀ η)) =
      ρ x₀ * χ η
  rw [section43SpatialParticleCLE_prependBasepoint]
  simp [SchwartzMap.prependFieldCLMRight_apply,
    SchwartzMap.prependField_apply]

/-- Integrating the spatial basepoint out of the normalized product lift
recovers the original reduced spatial test. -/
theorem section43SpatialHeadMarginal_basepointLift_eq
    (ρ : NormalizedSpatialBasepointCutoff d)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    section43SpatialHeadMarginal
        (section43SpatialBasepointLiftCLM d k ρ.toSchwartz χ) =
      χ := by
  ext η
  rw [section43SpatialHeadMarginal_apply]
  simp_rw [section43SpatialBasepointLiftCLM_apply_prependBasepoint]
  have hfun :
      (fun x₀ : Fin d → ℝ => ρ.toSchwartz x₀ * χ η) =
        fun x₀ : Fin d → ℝ => (χ η) • ρ.toSchwartz x₀ := by
    funext x₀
    simp [smul_eq_mul, mul_comm]
  rw [hfun, integral_smul, ρ.integral_eq_one]
  simp

/-- Prepending a compact strict-positive one-dimensional source to a compact
strict-positive coupled time source preserves the same support properties.
The tail remains coupled; no product decomposition of `ψ` is used. -/
noncomputable def section43PrependCompactPositiveTimeSource
    (g : Section43CompactPositiveTimeSource1D)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin k → ℝ) → ℂ))
    (hψ_positive :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    Section43CompactStrictPositiveTimeSource (k + 1) where
  f := SCV.prependField g.f ψ
  positive := by
    intro τ hτ i
    have hfun :
        ((SCV.prependField g.f ψ :
          SchwartzMap (Fin (k + 1) → ℝ) ℂ) :
            (Fin (k + 1) → ℝ) → ℂ) =
          fun u : Fin (k + 1) → ℝ =>
            g.f (u 0) * ψ (fun j : Fin k => u j.succ) := by
      funext u
      exact SchwartzMap.prependField_apply g.f ψ u
    have hprod :
        τ ∈ tsupport
          (fun u : Fin (k + 1) → ℝ =>
            g.f (u 0) * ψ (fun j : Fin k => u j.succ)) := by
      rw [← hfun]
      exact hτ
    refine Fin.cases ?_ ?_ i
    · apply g.positive
      exact tsupport_precomp_subset_local
        (f := (g.f : ℝ → ℂ))
        (h := fun u : Fin (k + 1) → ℝ => u 0)
        (by simpa using
          (continuous_apply (0 : Fin (k + 1)) :
            Continuous (fun u : Fin (k + 1) → ℝ => u 0)))
        ((tsupport_mul_subset_left
          (f := fun u : Fin (k + 1) → ℝ => g.f (u 0))
          (g := fun u : Fin (k + 1) → ℝ =>
            ψ (fun j : Fin k => u j.succ))) hprod)
    · intro j
      have htail :
          (fun r : Fin k => τ r.succ) ∈
            tsupport (ψ : (Fin k → ℝ) → ℂ) :=
        tsupport_precomp_subset_local
        (f := (ψ : (Fin k → ℝ) → ℂ))
        (h := fun u : Fin (k + 1) → ℝ =>
          fun r : Fin k => u r.succ)
        (by
          apply continuous_pi
          intro r
          simpa using
            (continuous_apply r.succ :
              Continuous (fun u : Fin (k + 1) → ℝ => u r.succ)))
        ((tsupport_mul_subset_right
          (f := fun u : Fin (k + 1) → ℝ => g.f (u 0))
          (g := fun u : Fin (k + 1) → ℝ =>
            ψ (fun r : Fin k => u r.succ))) hprod)
      exact hψ_positive htail j
  compact :=
    hasCompactSupport_prependField g.f ψ g.compact hψ_compact

@[simp]
theorem section43PrependCompactPositiveTimeSource_f
    (g : Section43CompactPositiveTimeSource1D)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin k → ℝ) → ℂ))
    (hψ_positive :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    (section43PrependCompactPositiveTimeSource
      g ψ hψ_compact hψ_positive).f =
      SCV.prependField g.f ψ :=
  rfl

/-- A carrier for the coupled tail test lifts to the product of the head
support and that carrier under `Fin.cons`. -/
theorem section43PrependCompactPositiveTimeSource_tsupport_subset_carrier
    (g : Section43CompactPositiveTimeSource1D)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin k → ℝ) → ℂ))
    (hψ_positive :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (K : Set (Fin k → ℝ))
    (hψK : tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ K) :
    tsupport
        ((section43PrependCompactPositiveTimeSource
          g ψ hψ_compact hψ_positive).f :
          (Fin (k + 1) → ℝ) → ℂ) ⊆
      (fun p : ℝ × (Fin k → ℝ) =>
        (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) ''
        (tsupport (g.f : ℝ → ℂ) ×ˢ K) := by
  intro τ hτ
  have hfun :
      ((SCV.prependField g.f ψ :
        SchwartzMap (Fin (k + 1) → ℝ) ℂ) :
          (Fin (k + 1) → ℝ) → ℂ) =
        fun u : Fin (k + 1) → ℝ =>
          g.f (u 0) * ψ (fun j : Fin k => u j.succ) := by
    funext u
    exact SchwartzMap.prependField_apply g.f ψ u
  have hprod :
      τ ∈ tsupport
        (fun u : Fin (k + 1) → ℝ =>
          g.f (u 0) * ψ (fun j : Fin k => u j.succ)) := by
    rw [← hfun]
    exact hτ
  have hhead : τ 0 ∈ tsupport (g.f : ℝ → ℂ) :=
    tsupport_precomp_subset_local
      (f := (g.f : ℝ → ℂ))
      (h := fun u : Fin (k + 1) → ℝ => u 0)
      (by simpa using
        (continuous_apply (0 : Fin (k + 1)) :
          Continuous (fun u : Fin (k + 1) → ℝ => u 0)))
      ((tsupport_mul_subset_left
        (f := fun u : Fin (k + 1) → ℝ => g.f (u 0))
        (g := fun u : Fin (k + 1) → ℝ =>
          ψ (fun j : Fin k => u j.succ))) hprod)
  have htail :
      (fun j : Fin k => τ j.succ) ∈
        tsupport (ψ : (Fin k → ℝ) → ℂ) :=
    tsupport_precomp_subset_local
      (f := (ψ : (Fin k → ℝ) → ℂ))
      (h := fun u : Fin (k + 1) → ℝ =>
        fun j : Fin k => u j.succ)
      (by
        apply continuous_pi
        intro j
        simpa using
          (continuous_apply j.succ :
            Continuous (fun u : Fin (k + 1) → ℝ => u j.succ)))
      ((tsupport_mul_subset_right
        (f := fun u : Fin (k + 1) → ℝ => g.f (u 0))
        (g := fun u : Fin (k + 1) → ℝ =>
          ψ (fun j : Fin k => u j.succ))) hprod)
  refine ⟨(τ 0, fun j : Fin k => τ j.succ), ⟨hhead, hψK htail⟩, ?_⟩
  ext i
  refine Fin.cases ?_ ?_ i <;> simp

/-- A fixed normalized compact strict-positive head-time cutoff. -/
noncomputable def normalizedPositiveTimeBasepointCutoff :
    Section43CompactPositiveTimeSource1D :=
  Classical.choose
    (exists_section43CompactPositiveTimeSource1D_approx_identity
      1 zero_lt_one)

theorem normalizedPositiveTimeBasepointCutoff_integral_eq_one :
    ∫ t : ℝ, normalizedPositiveTimeBasepointCutoff.f t = 1 :=
  (Classical.choose_spec
    (exists_section43CompactPositiveTimeSource1D_approx_identity
      1 zero_lt_one)).2.2.1

/-- Full product-basepoint representative with an arbitrary head-time
Schwartz cutoff. -/
noncomputable def productBasepointSpatialFullSourceCLM
    (d k : ℕ) [NeZero d]
    (θ : SchwartzMap ℝ ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
    SchwartzNPoint d (k + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43DiffCoordRealCLE d (k + 1))).comp
    ((section43TimeSpatialTensorSpatialCLM d (k + 1)
      (SCV.prependField θ ψ)).comp
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz))

@[simp]
theorem productBasepointSpatialFullSourceCLM_apply
    (θ : SchwartzMap ℝ ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    productBasepointSpatialFullSourceCLM d k θ ψ χ =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ)
        (SCV.prependField θ ψ) :=
  rfl

/-- The initial full source with independent normalized time and spatial
basepoint factors.  The reduced-time input remains one coupled Schwartz test. -/
noncomputable def initialProductBasepointSpatialFullSourceCLM
    (d k : ℕ) [NeZero d]
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
    SchwartzNPoint d (k + 1) :=
  productBasepointSpatialFullSourceCLM d k
    SCV.normedUnitBumpSchwartz ψ

@[simp]
theorem initialProductBasepointSpatialFullSourceCLM_apply
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialProductBasepointSpatialFullSourceCLM d k ψ χ =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1)
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ)
        (SCV.prependField SCV.normedUnitBumpSchwartz ψ) :=
  rfl

end OSIIChapterV
end OSReconstruction
