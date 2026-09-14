import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedMixedMovingSlice

/-!
# Product-basepoint mixed moving slices

The product-basepoint representative has one fixed compact positive-time head
in each reflected Gram block.  The shrinking approximate identities live only
in the remaining internal-gap coordinates.

This file integrates the two fixed heads into the mixed moving-slice kernel.
The resulting kernel is jointly continuous in the continuation parameter and
the two internal-gap blocks.  It is the scalar kernel needed by the partial
two-index delta argument; the bridge coordinate remains in the continuation
parameter and is not split between the two Hilbert vectors.
-/

noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Insert two head times in front of the independent left and right internal
gap blocks. -/
def osiiMixedHeadTailDelta
    (heads : ℝ × ℝ)
    (tails : Fin (k + k) → ℝ) :
    Fin ((k + 1) + (k + 1)) → ℝ :=
  Fin.append
    (Fin.cons heads.1 (splitFirst k k tails))
    (Fin.cons heads.2 (splitLast k k tails))

theorem continuous_osiiMixedHeadTailDelta (k : ℕ) :
    Continuous
      (Function.uncurry
        (osiiMixedHeadTailDelta (k := k))) := by
  have hhead₁ :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) => p.1.1) :=
    continuous_fst.comp continuous_fst
  have htail₁ :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) =>
          splitFirst k k p.2) :=
    (splitFirst_continuousLinear k k).comp continuous_snd
  have hleft :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) =>
          (Fin.cons p.1.1 (splitFirst k k p.2) :
            Fin (k + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hhead₁
    · intro j
      simpa using (continuous_apply j).comp htail₁
  have hhead₂ :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) => p.1.2) :=
    continuous_snd.comp continuous_fst
  have htail₂ :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) =>
          splitLast k k p.2) :=
    (splitLast_continuousLinear k k).comp continuous_snd
  have hright :
      Continuous
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) =>
          (Fin.cons p.1.2 (splitLast k k p.2) :
            Fin (k + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hhead₂
    · intro j
      simpa using (continuous_apply j).comp htail₂
  exact
    (Fin.continuous_append (k + 1) (k + 1)).comp
      (hleft.prodMk hright)

/-- The mixed moving kernel after integrating the two fixed compact head-time
profiles.  The left head is conjugated, exactly as in the reflected block
scalar. -/
def osiiReflectedMixedProductBasepointKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (w : Fin (k + k) → ℂ)
    (tails : Fin (k + k) → ℝ) : ℂ :=
  ∫ heads : ℝ × ℝ,
    (star (θ₁ heads.1) * θ₂ heads.2) *
      osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ w
        (osiiMixedHeadTailDelta heads tails)

/-- Integrating compact fixed heads preserves joint continuity of the mixed
kernel on the reflected moving-slice carrier. -/
theorem continuousOn_osiiReflectedMixedProductBasepointKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ContinuousOn
      (Function.uncurry
        (osiiReflectedMixedProductBasepointKernel
          A ρ θ₁ θ₂ χ₁ χ₂))
      (reflectedMovingSliceCarrier A ρ ×ˢ
        (Set.univ : Set (Fin (k + k) → ℝ))) := by
  let K : Set (ℝ × ℝ) :=
    tsupport (θ₁ : ℝ → ℂ) ×ˢ tsupport (θ₂ : ℝ → ℂ)
  let f :
      ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) →
        (ℝ × ℝ) → ℂ :=
    fun p heads =>
      (star (θ₁ heads.1) * θ₂ heads.2) *
        osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ p.1
          (osiiMixedHeadTailDelta heads p.2)
  have hK : IsCompact K :=
    hθ₁.isCompact.prod hθ₂.isCompact
  have hf :
      ContinuousOn f.uncurry
        ((reflectedMovingSliceCarrier A ρ ×ˢ
            (Set.univ : Set (Fin (k + k) → ℝ))) ×ˢ
          Set.univ) := by
    intro p hp
    have hkernel :=
      continuousAt_osiiReflectedMixedMovingKernel
        A ρ χ₁ χ₂ hp.1.1
          (osiiMixedHeadTailDelta p.2 p.1.2)
    have hdelta :
        ContinuousAt
          (fun q :
            ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) ×
              (ℝ × ℝ) =>
            (q.1.1, osiiMixedHeadTailDelta q.2 q.1.2))
          p := by
      have htail :
          Continuous
            (fun q :
              ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) ×
                (ℝ × ℝ) =>
              osiiMixedHeadTailDelta q.2 q.1.2) :=
        (continuous_osiiMixedHeadTailDelta k).comp
          (continuous_snd.prodMk
            (continuous_snd.comp continuous_fst))
      exact
        ((continuous_fst.comp continuous_fst).prodMk htail).continuousAt
    have hkernel_comp :
        ContinuousAt
          (fun q :
            ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) ×
              (ℝ × ℝ) =>
            osiiReflectedMixedMovingKernel A ρ χ₁ χ₂ q.1.1
              (osiiMixedHeadTailDelta q.2 q.1.2))
          p :=
      ContinuousAt.comp'
        (f := fun q :
          ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) ×
            (ℝ × ℝ) =>
          (q.1.1, osiiMixedHeadTailDelta q.2 q.1.2))
        (g := Function.uncurry
          (osiiReflectedMixedMovingKernel A ρ χ₁ χ₂))
        hkernel hdelta
    have hweight :
        ContinuousAt
          (fun q :
            ((Fin (k + k) → ℂ) × (Fin (k + k) → ℝ)) ×
              (ℝ × ℝ) =>
            star (θ₁ q.2.1) * θ₂ q.2.2)
          p := by
      fun_prop
    exact (hweight.mul hkernel_comp).continuousWithinAt
  have hfs :
      ∀ p heads,
        p ∈ reflectedMovingSliceCarrier A ρ ×ˢ
            (Set.univ : Set (Fin (k + k) → ℝ)) →
        heads ∉ K →
        f p heads = 0 := by
    intro p heads _ hheads
    rcases not_and_or.mp hheads with hleft | hright
    · have hz : θ₁ heads.1 = 0 :=
        image_eq_zero_of_notMem_tsupport hleft
      simp [f, hz]
    · have hz : θ₂ heads.2 = 0 :=
        image_eq_zero_of_notMem_tsupport hright
      simp [f, hz]
  simpa [osiiReflectedMixedProductBasepointKernel, f] using
    (continuousOn_integral_of_compact_support
      (μ := (volume : Measure (ℝ × ℝ))) hK hf hfs)

/-- Joint continuity after inserting the Cauchy-reflected parameter and a
fixed internal-gap center. -/
theorem
    continuousAt_osiiReflectedMixedProductBasepointKernel_cauchyShift
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hρ :
      HasCompactSupport
        (ρ : (Fin (k + (k + 1)) → ℝ) → ℂ))
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    {z : Fin k → ℂ}
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ)
    (center y : Fin (k + k) → ℝ) :
    ContinuousAt
      (Function.uncurry fun w x =>
        osiiReflectedMixedProductBasepointKernel
          A ρ θ₁ θ₂ χ₁ χ₂
          (reflectedCauchyIncrement w) (center + x))
      (z, y) := by
  have hkernelWithin :=
    (continuousOn_osiiReflectedMixedProductBasepointKernel
      A ρ θ₁ θ₂ hθ₁ hθ₂ χ₁ χ₂)
      (reflectedCauchyIncrement z, center + y)
      ⟨hz, Set.mem_univ _⟩
  have hopen :
      IsOpen
        (reflectedMovingSliceCarrier A ρ ×ˢ
          (Set.univ : Set (Fin (k + k) → ℝ))) :=
    (isOpen_reflectedMovingSliceCarrier A ρ hρ).prod isOpen_univ
  have hkernel :
      ContinuousAt
        (Function.uncurry
          (osiiReflectedMixedProductBasepointKernel
            A ρ θ₁ θ₂ χ₁ χ₂))
        (reflectedCauchyIncrement z, center + y) :=
    hkernelWithin.continuousAt
      (hopen.mem_nhds ⟨hz, Set.mem_univ _⟩)
  have hinner :
      ContinuousAt
        (fun p :
          (Fin k → ℂ) × (Fin (k + k) → ℝ) =>
          (reflectedCauchyIncrement p.1, center + p.2))
        (z, y) :=
    (((continuous_reflectedCauchyIncrement_map k).comp
        continuous_fst).prodMk
      (continuous_const.add continuous_snd)).continuousAt
  exact
    ContinuousAt.comp'
      (f := fun p :
        (Fin k → ℂ) × (Fin (k + k) → ℝ) =>
        (reflectedCauchyIncrement p.1, center + p.2))
      (g := Function.uncurry
        (osiiReflectedMixedProductBasepointKernel
          A ρ θ₁ θ₂ χ₁ χ₂))
      hkernel hinner

/-- Compact tensor tests times a centered product-basepoint mixed kernel are
integrable in the two internal-gap blocks. -/
theorem
    integrable_tensorProduct_mul_osiiReflectedMixedProductBasepointKernel
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (χ₁ χ₂ :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (left right : SchwartzMap (Fin k → ℝ) ℂ)
    (hleft : HasCompactSupport
      (left : (Fin k → ℝ) → ℂ))
    (hright : HasCompactSupport
      (right : (Fin k → ℝ) → ℂ))
    {z : Fin k → ℂ}
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ)
    (center : Fin (k + k) → ℝ) :
    Integrable
      (fun y : Fin (k + k) → ℝ =>
        (left.tensorProduct right) y *
          osiiReflectedMixedProductBasepointKernel
            A ρ θ₁ θ₂ χ₁ χ₂
            (reflectedCauchyIncrement z) (center + y)) := by
  have hkernel :
      Continuous
        (fun y : Fin (k + k) → ℝ =>
          osiiReflectedMixedProductBasepointKernel
            A ρ θ₁ θ₂ χ₁ χ₂
            (reflectedCauchyIncrement z) (center + y)) := by
    rw [continuous_iff_continuousAt]
    intro y
    let g :
        (Fin (k + k) → ℝ) →
          (Fin (k + k) → ℂ) × (Fin (k + k) → ℝ) :=
      fun x => (reflectedCauchyIncrement z, center + x)
    have hg : ContinuousAt g y :=
      (continuous_const.prodMk
        (continuous_const.add continuous_id)).continuousAt
    have hmaps :
        Set.MapsTo g Set.univ
          (reflectedMovingSliceCarrier A ρ ×ˢ
            (Set.univ : Set (Fin (k + k) → ℝ))) := by
      intro x _
      exact ⟨hz, Set.mem_univ _⟩
    have hcomp :=
      ContinuousWithinAt.comp
        ((continuousOn_osiiReflectedMixedProductBasepointKernel
          A ρ θ₁ θ₂ hθ₁ hθ₂ χ₁ χ₂)
          (g y) (hmaps (Set.mem_univ y)))
        hg.continuousWithinAt hmaps
    apply (continuousWithinAt_univ _ _).mp
    simpa [g, Function.comp_def] using hcomp
  have hcompact :
      HasCompactSupport
        (left.tensorProduct right :
          (Fin (k + k) → ℝ) → ℂ) :=
    SchwartzMap.tensorProduct_hasCompactSupport
      k k left right hleft hright
  exact
    ((left.tensorProduct right).continuous.mul hkernel
      ).integrable_of_hasCompactSupport hcompact.mul_right

end OSIIChapterV
end OSReconstruction
