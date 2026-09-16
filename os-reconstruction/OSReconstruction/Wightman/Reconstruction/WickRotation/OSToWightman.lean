/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanE0FiniteSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanACRProducerPackage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedForwardTubeControl
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalMovingSliceCutoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductReducedSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFlatWickMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductSourceNormalization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeTimeSliceIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge
import OSReconstruction.SCV.DistributionalRepresentationGluing
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.SCV.Osgood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIFixedWindowSelectors
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceBranchLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductNeighborhood
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OSReconstruction.SCV.EuclideanWeylPairing
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.SchwartzTensorProduct
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.SCV.DistributionalEOWCutoff









set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal LineDeriv
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

/- The formal dense-extension step above factors through two separate analytic
inputs:
1. continuity of the Euclidean kernel functional on `SchwartzNPoint d k`,
2. density of the admissible product-tensor subset inside `ZeroDiagonalSchwartz`.

This helper packages the purely topological last mile once those two pieces are
available. -/

private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
    {d : ℕ} [NeZero d] {n : ℕ} {ψ : NPointDomain d n → ℂ} {f : SchwartzNPoint d n}
    (hψ : ψ.HasTemperateGrowth) (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply hψ f y)
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hψ.1 (f.smooth ⊤) x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
          ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x = 0 := hf (k - i) x hx
    simp [hfi]
  have hnonneg :
      0 ≤ ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ := norm_nonneg _
  have hzero_norm :
      ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      calc
        ‖iteratedFDeriv ℝ k (fun y : NPointDomain d n => ψ y * f y) x‖
            ≤
          ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
              ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ := hle
        _ = 0 := hsum_zero
    · exact hnonneg
  exact norm_eq_zero.mp hzero_norm

private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
    {d : ℕ} [NeZero d] {n : ℕ} {ψ f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) :=
  VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
    (ψ.hasTemperateGrowth) hf

omit [NeZero d] in
private theorem productTensor_cutoff_productTensor
    {d k : ℕ}
    (χs fs : Fin k → SchwartzSpacetime d) :
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs)
        (SchwartzMap.productTensor fs) =
      SchwartzMap.productTensor
        (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((SchwartzMap.productTensor χs : SchwartzNPoint d k) :
      NPointDomain d k → ℂ))
    (SchwartzMap.productTensor χs).hasTemperateGrowth
    (SchwartzMap.productTensor fs) x]
  rw [SchwartzMap.productTensor_apply]
  have hfactor :
      ∀ i : Fin k,
        (SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) (x i) =
          (χs i) (x i) * (fs i) (x i) := by
    intro i
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
      (χs i).hasTemperateGrowth (fs i) (x i)]
    simp [smul_eq_mul]
  simp [SchwartzMap.productTensor_apply, hfactor, smul_eq_mul, Finset.prod_mul_distrib]

private theorem exists_finite_schwartz_partitionOfUnity_on_compact_openCover
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let V : α → Set E := fun i => U i ∩ Metric.ball (0 : E) (R + 1)
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact (hU_open i).inter Metric.isOpen_ball
  have hV_relcompact : ∀ i, ∃ c r, V i ⊆ Metric.closedBall c r := by
    intro i
    refine ⟨(0 : E), R + 1, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hV_cover : K ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxR : dist x (0 : E) ≤ R := by
      simpa [dist_comm] using Metric.mem_closedBall.mp (hR hx)
    have hxball : x ∈ Metric.ball (0 : E) (R + 1) := by
      rw [Metric.mem_ball]
      linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, hxball⟩⟩
  obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      (E := E) hK hV_open hV_relcompact hV_cover
  refine ⟨χ, hχ_compact, ?_, hχ_sum⟩
  intro i
  exact (hχ_sub i).trans Set.inter_subset_left

private def pairCollisionSq {d : ℕ} (k : ℕ) (i j : Fin k) (x : NPointDomain d k) : ℝ :=
  ∑ μ : Fin (d + 1), (x i μ - x j μ) * (x i μ - x j μ)

private theorem coordinate_hasTemperateGrowth
    {d : ℕ} {k : ℕ} (i : Fin k) (μ : Fin (d + 1)) :
    (fun x : NPointDomain d k => x i μ).HasTemperateGrowth := by
  let πi : NPointDomain d k →L[ℝ] SpacetimeDim d :=
    ContinuousLinearMap.proj i
  let πμ : SpacetimeDim d →L[ℝ] ℝ :=
    ContinuousLinearMap.proj μ
  change (⇑πμ ∘ ⇑πi).HasTemperateGrowth
  exact πμ.hasTemperateGrowth.comp πi.hasTemperateGrowth

private theorem pairCollisionSq_hasTemperateGrowth
    {d : ℕ} {k : ℕ} (i j : Fin k) :
    (fun x : NPointDomain d k => pairCollisionSq (d := d) k i j x).HasTemperateGrowth := by
  have hterm :
      ∀ μ ∈ (Finset.univ : Finset (Fin (d + 1))),
        ((fun x : NPointDomain d k => (x i μ - x j μ) * (x i μ - x j μ)) :
          NPointDomain d k → ℝ).HasTemperateGrowth := by
    intro μ _hμ
    have hdiff :
        (fun x : NPointDomain d k => x i μ - x j μ).HasTemperateGrowth :=
      (coordinate_hasTemperateGrowth (d := d) i μ).sub
        (coordinate_hasTemperateGrowth (d := d) j μ)
    change ((fun x : NPointDomain d k => x i μ - x j μ) *
      (fun x : NPointDomain d k => x i μ - x j μ)).HasTemperateGrowth
    exact hdiff.mul hdiff
  simpa [pairCollisionSq] using
    Function.HasTemperateGrowth.sum (s := (Finset.univ : Finset (Fin (d + 1)))) hterm

private def pairCollisionFarFactor
    {d k : ℕ} (r : ℝ) (i j : Fin k) (x : NPointDomain d k) : ℂ :=
  (SCV.smoothCutoff ((r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2) : ℂ)

private theorem pairCollisionFarFactor_hasTemperateGrowth
    {d k : ℕ} (r : ℝ) (i j : Fin k) :
    (pairCollisionFarFactor (d := d) r i j).HasTemperateGrowth := by
  have hsq := pairCollisionSq_hasTemperateGrowth (d := d) (k := k) i j
  have harg :
      (fun x : NPointDomain d k =>
        (r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2).HasTemperateGrowth := by
    change (((fun _ : NPointDomain d k => (r * r)⁻¹) *
      pairCollisionSq (d := d) k i j) + (fun _ => (-2 : ℝ))).HasTemperateGrowth
    exact ((Function.HasTemperateGrowth.const ((r * r)⁻¹)).mul hsq).add
      (Function.HasTemperateGrowth.const (-2 : ℝ))
  change Function.HasTemperateGrowth
    (fun x : NPointDomain d k =>
      (SCV.smoothCutoff ((r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2) : ℂ))
  exact SCV.smoothCutoff_complex_hasTemperateGrowth.comp harg

private abbrev collisionPairIndex (k : ℕ) :=
  {p : Fin k × Fin k // p.1 ≠ p.2}

private theorem hasTemperateGrowth_finset_prod_complex
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ι → E → ℂ}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x : E => s.prod (fun i => f i x)).HasTemperateGrowth := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    simpa using (Function.HasTemperateGrowth.const (1 : ℂ))
  · intro a s has ih hf
    have hfa : (f a).HasTemperateGrowth := hf a (by simp)
    have hfs : (fun x : E => s.prod (fun i => f i x)).HasTemperateGrowth :=
      ih (fun i hi => hf i (by simp [has, hi]))
    rw [show (fun x : E => ∏ i ∈ insert a s, f i x) =
        fun x : E => f a x * ∏ i ∈ s, f i x by
      funext x
      rw [Finset.prod_insert has]]
    change (f a * fun x : E => s.prod (fun i => f i x)).HasTemperateGrowth
    exact hfa.mul hfs

private def collisionFarCutoff {d k : ℕ} (r : ℝ) : NPointDomain d k → ℂ :=
  fun x =>
    (Finset.univ : Finset (collisionPairIndex k)).prod
      (fun p => pairCollisionFarFactor (d := d) r p.1.1 p.1.2 x)

private theorem collisionFarCutoff_hasTemperateGrowth
    {d k : ℕ} (r : ℝ) :
    (collisionFarCutoff (d := d) (k := k) r).HasTemperateGrowth := by
  classical
  change (fun x : NPointDomain d k =>
    (Finset.univ : Finset (collisionPairIndex k)).prod
      (fun p => pairCollisionFarFactor (d := d) r p.1.1 p.1.2 x)).HasTemperateGrowth
  exact hasTemperateGrowth_finset_prod_complex
    (s := (Finset.univ : Finset (collisionPairIndex k)))
    (f := fun p x => pairCollisionFarFactor (d := d) r p.1.1 p.1.2 x)
    (fun p _hp => pairCollisionFarFactor_hasTemperateGrowth (d := d) r p.1.1 p.1.2)

private def collisionFarPart
    {d : ℕ} [NeZero d] {k : ℕ} (r : ℝ)
    (F : ZeroDiagonalSchwartz d k) : ZeroDiagonalSchwartz d k :=
  ⟨SchwartzMap.smulLeftCLM ℂ (collisionFarCutoff (d := d) (k := k) r) F.1,
    VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
      (collisionFarCutoff_hasTemperateGrowth (d := d) (k := k) r) F.2⟩

private noncomputable def unitBallBumpSchwartzNPointRadius
    {d : ℕ} [NeZero d] (n : ℕ) (R : ℝ) (hR : 0 < R) : SchwartzNPoint d n :=
  OSReconstruction.unflattenSchwartzNPoint (d := d)
    (OSReconstruction.unitBallBumpSchwartzPiRadius (n * (d + 1)) R hR)

private theorem unflatten_flattenSchwartzNPoint_local
    {d : ℕ} [NeZero d] {n : ℕ} (f : SchwartzNPoint d n) :
    OSReconstruction.unflattenSchwartzNPoint (d := d)
      (OSReconstruction.flattenSchwartzNPoint (d := d) f) = f := by
  ext x
  simp [OSReconstruction.flattenSchwartzNPoint_apply,
    OSReconstruction.unflattenSchwartzNPoint_apply]

private noncomputable def bumpTruncationRadiusNPoint
    {d : ℕ} [NeZero d] {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) : SchwartzNPoint d n :=
  SchwartzMap.smulLeftCLM ℂ
    (unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)) f

private theorem bumpTruncationRadiusNPoint_eq_unflatten
    {d : ℕ} [NeZero d] {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) :
    bumpTruncationRadiusNPoint (d := d) f N =
      OSReconstruction.unflattenSchwartzNPoint (d := d)
        (OSReconstruction.bumpTruncationRadius
          (OSReconstruction.flattenSchwartzNPoint (d := d) f) N) := by
  ext x
  rw [bumpTruncationRadiusNPoint]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N) : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)).hasTemperateGrowth
    f x]
  rw [unitBallBumpSchwartzNPointRadius, OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [OSReconstruction.flattenSchwartzNPoint_apply, smul_eq_mul]

private theorem dense_hasCompactSupport_zeroDiagonal
    {d : ℕ} [NeZero d] (k : ℕ) :
    Dense {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} := by
  intro F
  let v : ℕ → SchwartzNPoint d k := fun n =>
    bumpTruncationRadiusNPoint (d := d) F.1 n
  have hv_vanish :
      ∀ n, VanishesToInfiniteOrderOnCoincidence (v n) := by
    intro n
    simpa [v, bumpTruncationRadiusNPoint] using
      (VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (d := d) F.2
          (ψ := unitBallBumpSchwartzNPointRadius (d := d) k
            (OSReconstruction.bumpTruncationRadiusValue n)
            (OSReconstruction.bumpTruncationRadiusValue_pos n)))
  let u : ℕ → ZeroDiagonalSchwartz d k := fun n => ⟨v n, hv_vanish n⟩
  have hu_mem :
      ∀ n, u n ∈ {F : ZeroDiagonalSchwartz d k |
        HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} := by
    intro n
    have hflat_compact :
        HasCompactSupport
          (((OSReconstruction.bumpTruncationRadius
            (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n :
              SchwartzMap (Fin (k * (d + 1)) → ℝ) ℂ)) :
            (Fin (k * (d + 1)) → ℝ) → ℂ) := by
      simpa [OSReconstruction.bumpTruncationRadius, OSReconstruction.bumpTruncationRadiusValue] using
        OSReconstruction.hasCompactSupport_cutoff_mul_radius
          (m := k * (d + 1)) (R := OSReconstruction.bumpTruncationRadiusValue n)
          (OSReconstruction.bumpTruncationRadiusValue_pos n)
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)
    have hv_compact :
        HasCompactSupport ((v n : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
      simpa [v] using
        (show HasCompactSupport ((bumpTruncationRadiusNPoint (d := d) F.1 n :
            SchwartzNPoint d k) : NPointDomain d k → ℂ) from by
          rw [bumpTruncationRadiusNPoint_eq_unflatten (d := d)]
          convert hflat_compact.comp_homeomorph
            (flattenCLEquivReal k (d + 1)).toHomeomorph using 1 <;> rfl)
    simpa [u] using hv_compact
  have hu_tendsto :
      Filter.Tendsto u Filter.atTop (nhds F) := by
    rw [tendsto_subtype_rng]
    have hv_tendsto :
        Filter.Tendsto v Filter.atTop (nhds F.1) := by
      have hunflat :=
        ((OSReconstruction.unflattenSchwartzNPoint (d := d)).continuous.tendsto
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)).comp
            (SchwartzMap.tendsto_bump_truncation_nhds
              (OSReconstruction.flattenSchwartzNPoint (d := d) F.1))
      have hrew :
          v =
            fun n : ℕ =>
              OSReconstruction.unflattenSchwartzNPoint (d := d)
                (OSReconstruction.bumpTruncationRadius
                  (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n) := by
        funext n
        simpa [v] using bumpTruncationRadiusNPoint_eq_unflatten (d := d) F.1 n
      rw [hrew]
      change Filter.Tendsto
        ((⇑(OSReconstruction.unflattenSchwartzNPoint (d := d))) ∘
          fun n => OSReconstruction.bumpTruncationRadius
            (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n)
        Filter.atTop (nhds F.1)
      simpa [unflatten_flattenSchwartzNPoint_local (d := d) F.1] using hunflat
    simpa [u] using hv_tendsto
  exact isClosed_closure.mem_of_tendsto hu_tendsto
    (Filter.Eventually.of_forall fun n => subset_closure (hu_mem n))









private abbrev proofideas_spacetimeUnitBallBumpRadius
    (R : ℝ) (hR : 0 < R) : SchwartzSpacetime d :=
  OSReconstruction.unitBallBumpSchwartzPiRadius (d + 1) R hR

private theorem proofideas_unitBallBumpSchwartzPi_zero_of_two_le_norm {m : ℕ}
    {x : Fin m → ℝ} (hx : 2 ≤ ‖x‖) :
    OSReconstruction.unitBallBumpSchwartzPi m x = 0 := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      OSReconstruction.unitBallBumpSchwartzPi m x = f x := by
    change (HasCompactSupport.toSchwartzMap hf_compact hf_smooth :
      SchwartzMap (Fin m → ℝ) ℂ) x = f x
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [happly]
  rw [show f x = ((b x : ℝ) : ℂ) by rfl]
  refine congrArg (fun r : ℝ => (r : ℂ)) ?_
  have hdist : 2 ≤ dist x 0 := by simpa [dist_eq_norm] using hx
  exact b.zero_of_le_dist hdist

private theorem proofideas_spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm
    {R : ℝ} (hR : 0 < R) {x : SpacetimeDim d}
    (hx : 2 * R ≤ ‖x‖) :
    proofideas_spacetimeUnitBallBumpRadius (d := d) R hR x = 0 := by
  rw [proofideas_spacetimeUnitBallBumpRadius, OSReconstruction.unitBallBumpSchwartzPiRadius_apply]
  apply proofideas_unitBallBumpSchwartzPi_zero_of_two_le_norm
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  rw [le_inv_mul_iff₀ hR]
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hx

private abbrev proofideas_pairDiffCLM {k : ℕ} (i j : Fin k) :
    NPointDomain d k →L[ℝ] SpacetimeDim d :=
  ContinuousLinearMap.proj (R := ℝ) (ι := Fin k) (φ := fun _ => SpacetimeDim d) i -
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin k) (φ := fun _ => SpacetimeDim d) j

private theorem proofideas_pairDiffCLM_apply {k : ℕ} (i j : Fin k)
    (x : NPointDomain d k) :
    proofideas_pairDiffCLM (d := d) i j x = x i - x j := by
  ext μ
  rfl

private theorem proofideas_pairDiffCLM_opNorm_le_two {k : ℕ} (i j : Fin k) :
    ‖proofideas_pairDiffCLM (d := d) i j‖ ≤ (2 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  calc
    ‖proofideas_pairDiffCLM (d := d) i j x‖ = ‖x i - x j‖ := by
      rw [proofideas_pairDiffCLM_apply]
    _ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖x‖ := by
      exact add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm x j)
    _ = 2 * ‖x‖ := by ring

set_option maxHeartbeats 800000 in
private theorem proofideas_exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : SpacetimeDim d),
        ‖iteratedFDeriv ℝ n
            ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖ ≤
          C * (δ⁻¹) ^ n := by
  let ψ : SchwartzSpacetime d := OSReconstruction.unitBallBumpSchwartzPi (d + 1)
  obtain ⟨C, hC, hCbound⟩ := (ψ : SchwartzSpacetime d).decay 0 n
  refine ⟨C, le_of_lt hC, ?_⟩
  intro δ hδ x
  let e : SpacetimeDim d →L[ℝ] SpacetimeDim d :=
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
      (Units.mk0 δ hδ.ne')).symm) : SpacetimeDim d ≃L[ℝ] SpacetimeDim d).toContinuousLinearMap
  have he_apply (y : SpacetimeDim d) : e y = δ⁻¹ • y := by
    change
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) = δ⁻¹ • y
    rw [show
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) =
          ((↑((Units.mk0 δ hδ.ne')⁻¹) : ℝ) • y) by rfl]
    simp [Units.val_inv_eq_inv_val]
  have he_norm : ‖e‖ ≤ δ⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound e (inv_nonneg.mpr hδ.le) ?_
    intro y
    calc
      ‖e y‖ = ‖δ⁻¹ • y‖ := by rw [he_apply]
      _ = ‖δ⁻¹‖ * ‖y‖ := norm_smul _ _
      _ = δ⁻¹ * ‖y‖ := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
      _ ≤ δ⁻¹ * ‖y‖ := by rfl
  have hcomp :
      iteratedFDeriv ℝ n
          (((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ)) x =
        (((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e)) := by
    change iteratedFDeriv ℝ n
        (((OSReconstruction.unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) ∘ e) x = _
    exact e.iteratedFDeriv_comp_right
        (f := ((OSReconstruction.unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((OSReconstruction.unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) x‖
        =
      ‖(((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e))‖ := by
            rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x)‖ *
          ∏ _ : Fin n, ‖e‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _ : Fin n, ‖e‖ := by
            gcongr
            simpa using hCbound (e x)
    _ = C * ‖e‖ ^ n := by simp
    _ ≤ C * (δ⁻¹) ^ n := by
            gcongr

private theorem proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
    {k : ℕ} (i j : Fin k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d k),
        ‖iteratedFDeriv ℝ n
            (fun y : NPointDomain d k =>
              (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (proofideas_pairDiffCLM (d := d) i j y)) x‖ ≤
          C * (δ⁻¹) ^ n := by
  obtain ⟨C, hC_nonneg, hCbound⟩ :=
    proofideas_exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) n
  refine ⟨C * (2 : ℝ) ^ n, mul_nonneg hC_nonneg (pow_nonneg (by norm_num) n), ?_⟩
  intro δ hδ x
  have hcomp :
      iteratedFDeriv ℝ n
          (fun y : NPointDomain d k =>
            (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
              (proofideas_pairDiffCLM (d := d) i j y)) x =
        (iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)).compContinuousLinearMap
            (fun _ : Fin n => proofideas_pairDiffCLM (d := d) i j) := by
    change iteratedFDeriv ℝ n
        (((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) ∘ proofideas_pairDiffCLM (d := d) i j) x = _
    exact (proofideas_pairDiffCLM (d := d) i j).iteratedFDeriv_comp_right
        (f := ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (fun y : NPointDomain d k =>
          (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
            (proofideas_pairDiffCLM (d := d) i j y)) x‖
        =
      ‖(iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)).compContinuousLinearMap
            (fun _ : Fin n => proofideas_pairDiffCLM (d := d) i j)‖ := by
              rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)‖ *
          ∏ _ : Fin n, ‖proofideas_pairDiffCLM (d := d) i j‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, ‖proofideas_pairDiffCLM (d := d) i j‖ := by
          gcongr
          exact hCbound δ hδ (proofideas_pairDiffCLM (d := d) i j x)
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, (2 : ℝ) := by
          gcongr
          exact proofideas_pairDiffCLM_opNorm_le_two (d := d) i j
    _ = (C * (2 : ℝ) ^ n) * (δ⁻¹) ^ n := by
          simp [mul_assoc, mul_left_comm, mul_comm]

private theorem proofideas_pairSmallCutoff_support_pair_norm_le
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (i j : Fin k) :
    Function.support
        (fun x : NPointDomain d k =>
          (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
            (proofideas_pairDiffCLM (d := d) i j x)) ⊆
      {x : NPointDomain d k | ‖x i - x j‖ ≤ 2 * δ} := by
  intro x hx
  by_contra hxball
  have hnorm : 2 * δ ≤ ‖x i - x j‖ := le_of_not_ge hxball
  have hzero :
      (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
          (proofideas_pairDiffCLM (d := d) i j x) = 0 := by
    rw [proofideas_pairDiffCLM_apply]
    exact proofideas_spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm (d := d) hδ hnorm
  exact hx (by simpa [Function.mem_support] using hzero)

private theorem proofideas_iteratedFDeriv_lineDeriv_eq_snoc_npoint {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v x : NPointDomain d k)
    (u : Fin n → NPointDomain d k) :
    iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x u =
      iteratedFDeriv ℝ (n + 1) ((f : SchwartzNPoint d k) : NPointDomain d k → ℂ) x
        (Fin.snoc u v) := by
  have hsucc :
      (∂^{Fin.snoc u v} f : SchwartzNPoint d k) = ∂^{u} (∂_{v} f) := by
    simpa using (LineDeriv.iteratedLineDerivOp_succ_right (m := Fin.snoc u v) (f := f))
  have hsucc_apply := congrArg (fun g : SchwartzNPoint d k => g x) hsucc
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := f) (m := Fin.snoc u v) (x := x),
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := (∂_{v} f : SchwartzNPoint d k)) (m := u) (x := x)] using hsucc_apply.symm

private theorem proofideas_lineDerivOp_comm_npoint {k : ℕ}
    (f : SchwartzNPoint d k)
    (v w : NPointDomain d k) :
    ∂_{v} ((∂_{w} f : SchwartzNPoint d k)) =
      ∂_{w} ((∂_{v} f : SchwartzNPoint d k)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzNPoint d k))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d k → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d k → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzNPoint d k))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

private theorem proofideas_lineDerivOp_iterated_comm_npoint {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v : NPointDomain d k) (u : Fin n → NPointDomain d k) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact proofideas_lineDerivOp_comm_npoint f v (u (Fin.last n))

private theorem proofideas_fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint
    {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v x : NPointDomain d k) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : NPointDomain d k → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzNPoint d k => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [proofideas_lineDerivOp_iterated_comm_npoint (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzNPoint d k)) (m := u) (x := x))

private theorem proofideas_seminorm_zero_lineDeriv_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (v : NPointDomain d k) (n : ℕ) :
    SchwartzMap.seminorm ℝ 0 n (LineDeriv.lineDerivOp v f : SchwartzNPoint d k) ≤
      ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
  refine SchwartzMap.seminorm_le_bound ℝ 0 n
    (LineDeriv.lineDerivOp v f : SchwartzNPoint d k) (by positivity) ?_
  intro x
  calc
    ‖x‖ ^ 0 *
        ‖iteratedFDeriv ℝ n
            (((LineDeriv.lineDerivOp v f : SchwartzNPoint d k) : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) x‖
        =
      ‖iteratedFDeriv ℝ n
          (((LineDeriv.lineDerivOp v f : SchwartzNPoint d k) : SchwartzNPoint d k) :
            NPointDomain d k → ℂ) x‖ := by
            simp
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v‖ := by
          rw [← proofideas_fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (n + 1) (f : NPointDomain d k → ℂ) x‖ * ‖v‖ := by
          rw [norm_fderiv_iteratedFDeriv]
    _ ≤ (SchwartzMap.seminorm ℝ 0 (n + 1) f) * ‖v‖ := by
          gcongr
          exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f (n + 1) x
    _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
          ring

private theorem proofideas_iteratedLineDeriv_seminorm_zero_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (j n : ℕ) :
    ∀ u : Fin j → NPointDomain d k,
      SchwartzMap.seminorm ℝ 0 n (LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  induction j generalizing f n with
  | zero =>
      intro u
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      intro u
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      calc
        SchwartzMap.seminorm ℝ 0 n (∂_{u 0} (∂^{Fin.tail u} f) : SchwartzNPoint d k)
            ≤ ‖u 0‖ * SchwartzMap.seminorm ℝ 0 (n + 1) (∂^{Fin.tail u} f : SchwartzNPoint d k) := by
              exact proofideas_seminorm_zero_lineDeriv_le_npoint
                (f := ∂^{Fin.tail u} f) (v := u 0) (n := n)
        _ ≤ ‖u 0‖ *
              ((∏ i, ‖Fin.tail u i‖) * SchwartzMap.seminorm ℝ 0 (n + 1 + j) f) := by
              gcongr
              exact ih (f := f) (n := n + 1) (u := Fin.tail u)
        _ = (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + (j + 1)) f := by
              rw [Fin.prod_univ_succ, add_assoc]
              have htail : (∏ i : Fin j, ‖Fin.tail u i‖) = ∏ i : Fin j, ‖u i.succ‖ := rfl
              rw [htail]
              ring

private theorem proofideas_norm_iteratedFDeriv_iteratedLineDeriv_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (j n : ℕ) :
    ∀ (u : Fin j → NPointDomain d k) (x : NPointDomain d k),
      ‖iteratedFDeriv ℝ n ((LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) x‖ ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  intro u x
  exact le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (∂^{u} f) n x)
    (proofideas_iteratedLineDeriv_seminorm_zero_le_npoint (f := f) (j := j) (n := n) u)

private theorem proofideas_iteratedLineDeriv_preserves_zeroDiagonal {k j : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (u : Fin j → NPointDomain d k) :
    VanishesToInfiniteOrderOnCoincidence (LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) := by
  induction j generalizing f with
  | zero =>
      simpa [LineDeriv.iteratedLineDerivOp_fin_zero] using hf
  | succ j ih =>
      have hu : u = Fin.snoc (Fin.init u) (u (Fin.last j)) := by
        exact (Fin.snoc_init_self u).symm
      rw [hu, LineDeriv.iteratedLineDerivOp_succ_right]
      simp only [Fin.init_snoc, Fin.snoc_last]
      have hline :
          VanishesToInfiniteOrderOnCoincidence
            (LineDeriv.lineDerivOp (u (Fin.last j)) f : SchwartzNPoint d k) := by
        intro q y hy
        ext w
        have hzero := hf (q + 1) y hy
        have hzero_apply :
            iteratedFDeriv ℝ (q + 1) (f : NPointDomain d k → ℂ) y
              (Fin.snoc w (u (Fin.last j))) = 0 := by
          simpa using congrArg
            (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => NPointDomain d k) ℂ =>
              T (Fin.snoc w (u (Fin.last j)))) hzero
        simpa using
          (proofideas_iteratedFDeriv_lineDeriv_eq_snoc_npoint
            (f := f) (v := u (Fin.last j)) (x := y) (u := w)).trans hzero_apply
      exact ih (f := LineDeriv.lineDerivOp (u (Fin.last j)) f) hline (Fin.init u)

private def proofideas_coincidenceCollapse {k : ℕ} (i j : Fin k) (x : NPointDomain d k) :
    NPointDomain d k :=
  fun q => if q = i ∨ q = j then midpoint ℝ (x i) (x j) else x q

private theorem proofideas_coincidenceCollapse_mem_CoincidenceLocus {k : ℕ}
    (x : NPointDomain d k) (i j : Fin k) (hij : i ≠ j) :
    proofideas_coincidenceCollapse (d := d) i j x ∈ CoincidenceLocus d k := by
  refine ⟨i, j, hij, ?_⟩
  ext μ
  simp [proofideas_coincidenceCollapse, hij]

private theorem proofideas_norm_sub_coincidenceCollapse_le_pairDifference {k : ℕ}
    (x : NPointDomain d k) (i j : Fin k) (hij : i ≠ j) :
    ‖x - proofideas_coincidenceCollapse (d := d) i j x‖ ≤ ‖x i - x j‖ := by
  change ↑(Finset.univ.sup fun q => ‖(x - proofideas_coincidenceCollapse (d := d) i j x) q‖₊) ≤
    ‖x i - x j‖
  have hdistNN :
      Finset.univ.sup
          (fun q => ‖(x - proofideas_coincidenceCollapse (d := d) i j x) q‖₊) ≤
        ‖x i - x j‖₊ := by
    refine Finset.sup_le_iff.mpr ?_
    intro q _hq
    by_cases hqi : q = i
    · subst q
      have hqreal :
          ‖(x - proofideas_coincidenceCollapse (d := d) i j x) i‖ ≤ ‖x i - x j‖ := by
        calc
          ‖(x - proofideas_coincidenceCollapse (d := d) i j x) i‖ =
              ‖x i - midpoint ℝ (x i) (x j)‖ := by
                simp [proofideas_coincidenceCollapse, hij]
          _ = ‖(⅟ (2 : ℝ)) • (x i - x j)‖ := by rw [left_sub_midpoint]
          _ = ‖(⅟ (2 : ℝ))‖ * ‖x i - x j‖ := norm_smul _ _
          _ ≤ 1 * ‖x i - x j‖ := by
              gcongr
              norm_num
          _ = ‖x i - x j‖ := by ring
      exact_mod_cast hqreal
    · by_cases hqj : q = j
      · subst q
        have hqreal :
            ‖(x - proofideas_coincidenceCollapse (d := d) i j x) j‖ ≤ ‖x i - x j‖ := by
          calc
            ‖(x - proofideas_coincidenceCollapse (d := d) i j x) j‖ =
                ‖x j - midpoint ℝ (x i) (x j)‖ := by
                  simp [proofideas_coincidenceCollapse, hqi]
            _ = ‖(⅟ (2 : ℝ)) • (x j - x i)‖ := by rw [right_sub_midpoint]
            _ = ‖(⅟ (2 : ℝ))‖ * ‖x j - x i‖ := norm_smul _ _
            _ ≤ 1 * ‖x j - x i‖ := by
                gcongr
                norm_num
            _ = ‖x i - x j‖ := by rw [norm_sub_rev, one_mul]
        exact_mod_cast hqreal
      · simp [proofideas_coincidenceCollapse, hqi, hqj]
  exact_mod_cast hdistNN

set_option maxHeartbeats 600000 in
private theorem proofideas_exists_iteratedLineDeriv_pair_flat_bound
    {k : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (j m : ℕ) (a b : Fin k) (hab : a ≠ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Fin j → NPointDomain d k) (x : NPointDomain d k),
        ‖(LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) x‖ ≤
          C * ‖x a - x b‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 (j + (m + 1)) f
  have hA_nonneg : 0 ≤ A := by positivity
  refine ⟨A / (((Nat.factorial m : ℕ) : ℝ)), by positivity, ?_⟩
  intro u x
  let F : SchwartzNPoint d k := ∂^{u} f
  let c : NPointDomain d k := proofideas_coincidenceCollapse (d := d) a b x
  let v : NPointDomain d k := x - c
  let L : ℝ →L[ℝ] NPointDomain d k :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c)) ∘ L
  have hF_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (F : NPointDomain d k → ℂ) := fun r => by
    simpa [F] using (F.smooth r)
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c)) :=
    fun r => by
      change ContDiff ℝ r ((F : NPointDomain d k → ℂ) ∘ fun z => z + c)
      exact (hF_contDiff r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_coin : c ∈ CoincidenceLocus d k := by
    simpa [c] using proofideas_coincidenceCollapse_mem_CoincidenceLocus (d := d) x a b hab
  have hF_vanish :
      VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F] using proofideas_iteratedLineDeriv_preserves_zeroDiagonal (f := f) hf u
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro q hq
    have hq_zero :
        iteratedDerivWithin q g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
          ((hg_contDiff q).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ q g 0 =
            (iteratedFDeriv ℝ q (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
              (L 0)).compContinuousLinearMap (fun _ : Fin q => L) := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
            (hshift_contDiff q) (x := 0) (i := q) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ q (F : NPointDomain d k → ℂ) (L 0 + c) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hF_vanish q c hc_coin
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hq_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      calc
        ‖L s‖ = ‖s • v‖ := by rfl
        _ = ‖s‖ * ‖v‖ := norm_smul s v
        _ = ‖v‖ * ‖s‖ := by ring
        _ ≤ ‖v‖ * ‖s‖ := le_rfl
    rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ)
            (z + c)) (L t)).compContinuousLinearMap (fun _ : Fin (m + 1) => L) := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    have hFbound :
        ‖iteratedFDeriv ℝ (m + 1) (F : NPointDomain d k → ℂ) (L t + c)‖ ≤
          A * ∏ i, ‖u i‖ := by
      simpa [A, F, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
        proofideas_norm_iteratedFDeriv_iteratedLineDeriv_le_npoint
          (f := f) (j := j) (n := m + 1) u (L t + c)
    have hprod_nonneg : 0 ≤ ∏ _ : Fin (m + 1), ‖L‖ := by positivity
    have huprod_nonneg : 0 ≤ ∏ i, ‖u i‖ := by
      simpa using Finset.prod_nonneg (fun i _ => norm_nonneg (u i))
    have hcoeff_nonneg : 0 ≤ A * ∏ i, ‖u i‖ := by
      exact mul_nonneg hA_nonneg huprod_nonneg
    have hLpow_all : ∀ n : ℕ, ‖L‖ ^ n ≤ ‖v‖ ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            ‖L‖ ^ (n + 1) = ‖L‖ ^ n * ‖L‖ := by ring_nf
            _ ≤ ‖v‖ ^ n * ‖v‖ := by
                  exact mul_le_mul ih hL (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
            _ = ‖v‖ ^ (n + 1) := by ring_nf
    let D :=
      iteratedFDeriv ℝ (m + 1) (F : NPointDomain d k → ℂ) (L t + c)
    have hDcomp :
        ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖ ≤
          ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := by
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    calc
      ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖
          ≤ ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := hDcomp
      _ ≤ (A * ∏ i, ‖u i‖) * ∏ _ : Fin (m + 1), ‖L‖ := by
            exact mul_le_mul_of_nonneg_right hFbound hprod_nonneg
      _ = (A * ∏ i, ‖u i‖) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_left (hLpow_all (m + 1)) hcoeff_nonneg
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hdist :
      ‖v‖ ≤ ‖x a - x b‖ := by
    simpa [v, c] using proofideas_norm_sub_coincidenceCollapse_le_pairDifference (d := d) x a b hab
  have hg_one : g 1 = F x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply]
  calc
    ‖(F : NPointDomain d k → ℂ) x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ ((A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
          simpa [hTaylor_zero] using hrem
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
          field_simp [Nat.cast_ne_zero]
          ring
    _ ≤ (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x a - x b‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
          gcongr

private theorem proofideas_exists_iteratedFDeriv_pair_flat_bound
    {k : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (q m : ℕ) (a b : Fin k) (hab : a ≠ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : NPointDomain d k,
        ‖iteratedFDeriv ℝ q (f : NPointDomain d k → ℂ) x‖ ≤
          C * ‖x a - x b‖ ^ (m + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    proofideas_exists_iteratedLineDeriv_pair_flat_bound
      (f := f) hf q m a b hab
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  have hCx : 0 ≤ C * ‖x a - x b‖ ^ (m + 1) := by positivity
  rw [ContinuousMultilinearMap.opNorm_le_iff hCx]
  intro u
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, mul_assoc, mul_left_comm, mul_comm]
    using hC u x

private theorem proofideas_pair_power_factor_le
    {k M q : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ_le : δ ≤ 1)
    {x : NPointDomain d k} {a b : Fin k} (hx : ‖x a - x b‖ ≤ 2 * δ)
    (hq : q ∈ Finset.range (M + 1)) :
    (δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1) ≤ (2 : ℝ) ^ (M + 1) * δ := by
  have hq_le : q ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hpow : ‖x a - x b‖ ^ (M + 1) ≤ (2 * δ) ^ (M + 1) := by
    gcongr
  have hδ_inv_ge_one : 1 ≤ δ⁻¹ := by
    rw [one_le_inv₀ hδ]
    exact hδ_le
  have hdelta_inv_mono : (δ⁻¹) ^ q ≤ (δ⁻¹) ^ M := by
    exact pow_le_pow_right₀ hδ_inv_ge_one hq_le
  have hcancel : (δ⁻¹) ^ M * δ ^ (M + 1) = δ := by
    calc
      (δ⁻¹) ^ M * δ ^ (M + 1) = ((δ⁻¹) ^ M * δ ^ M) * δ := by
            rw [pow_succ']
            ring
      _ = (((δ ^ M)⁻¹ * δ ^ M) * δ) := by rw [inv_pow]
      _ = δ := by simp [pow_ne_zero M hδ.ne']
  calc
    (δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1)
        ≤ (δ⁻¹) ^ q * (2 * δ) ^ (M + 1) := by
            gcongr
    _ ≤ (δ⁻¹) ^ M * (2 * δ) ^ (M + 1) := by
          gcongr
    _ = (2 : ℝ) ^ (M + 1) * ((δ⁻¹) ^ M * δ ^ (M + 1)) := by
          rw [mul_pow]
          ring
    _ = (2 : ℝ) ^ (M + 1) * δ := by rw [hcancel]

set_option maxHeartbeats 1000000 in
private theorem proofideas_pairSmallCutoff_seminorm_le_linear
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b) :
    ∀ (N M : ℕ),
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
          SchwartzMap.seminorm ℝ N M
            (SchwartzMap.smulLeftCLM ℂ
              (fun x : NPointDomain d k =>
                (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                  (proofideas_pairDiffCLM (d := d) a b x))
              F.1 : SchwartzNPoint d k) ≤
              A * δ := by
  intro N M
  let B : ℕ → ℝ := fun q =>
    Classical.choose (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
      (d := d) a b q)
  let H : ℕ → ℝ := fun q =>
    Classical.choose
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : NPointDomain d k)).1 hF_compact.isBounded
  let R : ℝ := max R0 1
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have htsupport_F :
      tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR0 hx)
  have hB_nonneg : ∀ q : ℕ, 0 ≤ B q := by
    intro q
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
        (d := d) a b q)).1
  have hB_bound :
      ∀ q : ℕ, ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d k),
        ‖iteratedFDeriv ℝ q
            (fun y : NPointDomain d k =>
              (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (proofideas_pairDiffCLM (d := d) a b y)) x‖ ≤
          B q * (δ⁻¹) ^ q := by
    intro q δ hδ x
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
        (d := d) a b q)).2 δ hδ x
  have hH_nonneg : ∀ q : ℕ, 0 ≤ H q := by
    intro q
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)).1
  have hH_bound :
      ∀ q : ℕ, ∀ x : NPointDomain d k,
        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
          H q * ‖x a - x b‖ ^ (M + 1) := by
    intro q x
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)).2 x
  let A : ℝ :=
    ∑ q ∈ Finset.range (M + 1),
      (M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro q hq
    have hBq : 0 ≤ B q := hB_nonneg q
    have hHq : 0 ≤ H q := hH_nonneg q
    have hRN : 0 ≤ R ^ N := pow_nonneg hR_nonneg N
    positivity
  refine ⟨A, hA_nonneg, ?_⟩
  intro δ hδ hδ_le_one
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let fδ : SchwartzNPoint d k := SchwartzMap.smulLeftCLM ℂ ηδ F.1
  have hη_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ηδ := by
    fun_prop
  have hF_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (F.1 : NPointDomain d k → ℂ) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (F.1 : SchwartzNPoint d k).toFun
    exact (F.1 : SchwartzNPoint d k).smooth'
  have hη_temp : ηδ.HasTemperateGrowth := by
    fun_prop
  have hfun :
      ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) = fun x => ηδ x * F.1 x := by
    funext x
    simpa [fδ, ηδ, smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply (g := ηδ) hη_temp F.1 x)
  have hsupp_eta :
      Function.support ηδ ⊆ {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    simpa [ηδ] using
      proofideas_pairSmallCutoff_support_pair_norm_le (d := d) hδ a b
  have hclosed_pair : IsClosed {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    have hclosed_raw :
        IsClosed {x : NPointDomain d k |
          ‖proofideas_pairDiffCLM (d := d) a b x‖ ≤ 2 * δ} :=
      isClosed_le ((proofideas_pairDiffCLM (d := d) a b).continuous.norm) continuous_const
    simpa [proofideas_pairDiffCLM_apply] using hclosed_raw
  have htsupport_eta :
      tsupport ηδ ⊆ {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} :=
    closure_minimal hsupp_eta hclosed_pair
  have htsupport_fδ_pair :
      tsupport ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_eta
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := F.1) hx).2)
  have htsupport_fδ_compact :
      tsupport ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact htsupport_F
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := F.1) hx).1)
  have hsupport_deriv_pair :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) ⊆
        {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_fδ_pair
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ)) hx)
  have hsupport_deriv_compact :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact htsupport_fδ_compact
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ)) hx)
  have hbound :
      ∀ x : NPointDomain d k,
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x‖ ≤
          A * δ := by
    intro x
    by_cases hx :
        x ∈ Function.support
          (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    · have hxpair : ‖x a - x b‖ ≤ 2 * δ := hsupport_deriv_pair hx
      have hxR : x ∈ Metric.closedBall (0 : NPointDomain d k) R :=
        hsupport_deriv_compact hx
      have hRN : ‖x‖ ^ N ≤ R ^ N := by
        gcongr
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
      have hsmul :=
        norm_iteratedFDeriv_smul_le (𝕜 := ℝ)
          hη_smooth hF_smooth x (n := M) (by exact_mod_cast le_top)
      calc
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x‖
            = ‖x‖ ^ N * ‖iteratedFDeriv ℝ M (fun y => ηδ y * F.1 y) x‖ := by
                rw [hfun]
        _ ≤ ‖x‖ ^ N *
              ∑ q ∈ Finset.range (M + 1),
                (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ := by
                exact mul_le_mul_of_nonneg_left hsmul (by positivity)
        _ = ∑ q ∈ Finset.range (M + 1),
              ‖x‖ ^ N *
                ((M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ q ∈ Finset.range (M + 1),
              ((M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                refine Finset.sum_le_sum ?_
                intro q hq
                have hBq := hB_bound q δ hδ x
                have hHq := hH_bound q x
                have hBq_nonneg : 0 ≤ B q := hB_nonneg q
                have hHq_nonneg : 0 ≤ H q := hH_nonneg q
                have hBq_rhs_nonneg : 0 ≤ B q * (δ⁻¹) ^ q := by positivity
                have hchoose_nonneg : 0 ≤ (M.choose q : ℝ) := by positivity
                have hprod :
                    ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
                      (B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1)) := by
                  exact mul_le_mul hBq hHq (norm_nonneg _) hBq_rhs_nonneg
                have hterm_coeff :
                    (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
                      (M.choose q : ℝ) *
                        ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1))) := by
                  calc
                    (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖
                        =
                      (M.choose q : ℝ) * (‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖) := by
                          ring
                    _ ≤ (M.choose q : ℝ) *
                          ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1))) := by
                          exact mul_le_mul_of_nonneg_left hprod hchoose_nonneg
                have hcoeff_nonneg : 0 ≤ (M.choose q : ℝ) * B q * H q := by
                  exact mul_nonneg (mul_nonneg hchoose_nonneg hBq_nonneg) hHq_nonneg
                have hpower :
                    ‖x‖ ^ N * ((δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1)) ≤
                      R ^ N * ((2 : ℝ) ^ (M + 1) * δ) := by
                  exact mul_le_mul hRN
                    (proofideas_pair_power_factor_le (d := d) (hδ := hδ)
                      (hδ_le := hδ_le_one) (x := x) (a := a) (b := b) hxpair hq)
                    (by positivity) (pow_nonneg hR_nonneg _)
                calc
                  ‖x‖ ^ N *
                      ((M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖)
                      ≤
                    ‖x‖ ^ N *
                      ((M.choose q : ℝ) *
                        ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1)))) := by
                          exact mul_le_mul_of_nonneg_left hterm_coeff (by positivity)
                  _ = ((M.choose q : ℝ) * B q * H q) *
                        (‖x‖ ^ N * ((δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1))) := by
                          ring
                  _ ≤ ((M.choose q : ℝ) * B q * H q) *
                        (R ^ N * ((2 : ℝ) ^ (M + 1) * δ)) := by
                          exact mul_le_mul_of_nonneg_left hpower hcoeff_nonneg
                  _ = ((M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                          ring
        _ = A * δ := by
              simp [A, Finset.sum_mul]
    · have hzero :
          iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x = 0 := by
        by_contra hne
        exact hx (by simpa [Function.mem_support] using hne)
      have hnonneg : 0 ≤ A * δ := by positivity
      simpa [hzero] using hnonneg
  simpa [fδ, ηδ] using
    SchwartzMap.seminorm_le_bound ℝ N M fδ (by positivity) hbound

private def proofideas_pairNearPart
    {k : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    ZeroDiagonalSchwartz d k :=
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  ⟨SchwartzMap.smulLeftCLM ℂ ηδ F.1, by
    have hη : ηδ.HasTemperateGrowth := by
      fun_prop
    exact VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth (d := d) hη F.2⟩

private theorem proofideas_pairNearPart_tendsto_zero
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le_one : ρ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        proofideas_pairNearPart (d := d) (ρ / (n + 1 : ℝ))
          (by positivity) F a b)
      Filter.atTop (nhds (0 : ZeroDiagonalSchwartz d k)) := by
  rw [tendsto_subtype_rng]
  rw [(schwartz_withSeminorms ℝ (NPointDomain d k) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  obtain ⟨A, hA_nonneg, hA_bound⟩ :=
    proofideas_pairSmallCutoff_seminorm_le_linear
      (d := d) F hF_compact a b hab p.1 p.2
  let Bnd : ℝ := A * ρ + 1
  have hBnd_pos : 0 < Bnd := by
    dsimp [Bnd]
    positivity
  have hBnd_nonneg : 0 ≤ Bnd := le_of_lt hBnd_pos
  rcases exists_nat_one_div_lt (show 0 < ε / Bnd by positivity) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let δn : ℝ := ρ / (n + 1 : ℝ)
  have hδn_pos : 0 < δn := by
    dsimp [δn]
    positivity
  have hδn_le_ρ : δn ≤ ρ := by
    have hfrac : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
      have hden : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hone_pos : 0 < (1 : ℝ) := by positivity
      simpa using (one_div_le_one_div_of_le hone_pos hden)
    calc
      δn = ρ * ((n + 1 : ℝ)⁻¹) := by simp [δn, div_eq_mul_inv]
      _ ≤ ρ * 1 := by
            simpa using (mul_le_mul_of_nonneg_left hfrac (le_of_lt hρ_pos))
      _ = ρ := by ring
  have hδn_le_one : δn ≤ 1 := le_trans hδn_le_ρ hρ_le_one
  have hsemi_le :
      schwartzSeminormFamily ℝ (NPointDomain d k) ℂ p
          (((proofideas_pairNearPart (d := d) δn hδn_pos F a b).1 : SchwartzNPoint d k) - 0) ≤
        A * δn := by
    change SchwartzMap.seminorm ℝ p.1 p.2
      ((((proofideas_pairNearPart (d := d) δn hδn_pos F a b).1 : SchwartzNPoint d k) - 0)) ≤
        A * δn
    simpa [proofideas_pairNearPart, δn] using hA_bound δn hδn_pos hδn_le_one
  have hAρ_le_Bnd : A * ρ ≤ Bnd := by
    dsimp [Bnd]
    linarith
  have hscale :
      A * δn ≤ Bnd / (n + 1 : ℝ) := by
    have hden_pos : 0 < (n + 1 : ℝ) := by positivity
    have hdiv :
        (A * ρ) / (n + 1 : ℝ) ≤ Bnd / (n + 1 : ℝ) := by
      exact div_le_div_of_nonneg_right hAρ_le_Bnd (le_of_lt hden_pos)
    simpa [δn, mul_div_assoc] using hdiv
  have hfrac_mono :
      Bnd / (n + 1 : ℝ) ≤ Bnd / (N + 1 : ℝ) := by
    have hone_div :
        (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hden : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      have hN_pos : 0 < (N + 1 : ℝ) := by positivity
      simpa using (one_div_le_one_div_of_le hN_pos hden)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hone_div hBnd_nonneg)
  have hsmall :
      Bnd / (N + 1 : ℝ) < ε := by
    have := mul_lt_mul_of_pos_left hN hBnd_pos
    calc
      Bnd / (N + 1 : ℝ) = Bnd * (1 / (N + 1 : ℝ)) := by ring
      _ < Bnd * (ε / Bnd) := this
      _ = ε := by
        field_simp [show Bnd ≠ 0 by positivity]
  exact lt_of_le_of_lt (le_trans hsemi_le (le_trans hscale hfrac_mono)) hsmall

private theorem proofideas_spacetimeUnitBallBumpRadius_one_of_norm_le
    {R : ℝ} (hR : 0 < R) {x : SpacetimeDim d}
    (hx : ‖x‖ ≤ R) :
    proofideas_spacetimeUnitBallBumpRadius (d := d) R hR x = 1 := by
  rw [proofideas_spacetimeUnitBallBumpRadius]
  apply OSReconstruction.unitBallBumpSchwartzPiRadius_one_of_mem_closedBall (m := d + 1) hR
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx

private def proofideas_pairFarPart
    {k : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    ZeroDiagonalSchwartz d k :=
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  ⟨SchwartzMap.smulLeftCLM ℂ φδ F.1, by
    have hφ : φδ.HasTemperateGrowth := by
      fun_prop
    exact VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth (d := d) hφ F.2⟩

private theorem proofideas_pairFarPart_support_pair_norm_ge
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    Function.support
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      {x : NPointDomain d k | δ ≤ ‖x a - x b‖} := by
  intro x hx
  by_contra hnot
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  have hη_one : ηδ x = 1 := by
    have hnorm : ‖x a - x b‖ ≤ δ := le_of_lt (lt_of_not_ge hnot)
    dsimp [ηδ]
    exact proofideas_spacetimeUnitBallBumpRadius_one_of_norm_le (d := d) hδ hnorm
  have hφ_temp : φδ.HasTemperateGrowth := by
    fun_prop
  have hzero :
      (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) x = 0 := by
    change (SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) x = 0
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
    simp [φδ, hη_one]
  exact hx hzero

private theorem proofideas_pairFarPart_tsupport_pair_norm_ge
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      {x : NPointDomain d k | δ ≤ ‖x a - x b‖} := by
  refine closure_minimal ?support ?closed
  · exact proofideas_pairFarPart_support_pair_norm_ge (d := d) hδ F a b
  · have hclosed_raw :
        IsClosed {x : NPointDomain d k |
          δ ≤ ‖proofideas_pairDiffCLM (d := d) a b x‖} :=
      isClosed_le continuous_const
        ((proofideas_pairDiffCLM (d := d) a b).continuous.norm)
    simpa [proofideas_pairDiffCLM_apply] using hclosed_raw

private theorem proofideas_pairFarPart_tsupport_disjoint_pair_diagonal
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    Disjoint
      (tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ))
      {x : NPointDomain d k | x a = x b} := by
  rw [Set.disjoint_left]
  intro x hx hEq
  have hle : δ ≤ ‖x a - x b‖ :=
    proofideas_pairFarPart_tsupport_pair_norm_ge (d := d) hδ F a b hx
  have hEq' : x a = x b := hEq
  have hzero : ‖x a - x b‖ = 0 := by simp [hEq']
  linarith

private theorem proofideas_pairFarPart_hasCompactSupport
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) :
    HasCompactSupport
      (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) := by
  refine hF_compact.mono' ?_
  intro x hx
  have hx_ts :
      x ∈ tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) :=
    subset_closure hx
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  change
    x ∈ tsupport
      ((SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) at hx_ts
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := φδ) (f := F.1) hx_ts).1

private theorem proofideas_pairFarPart_tsupport_subset_original
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
  intro x hx
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  change
    x ∈ tsupport
      ((SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) at hx
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := φδ) (f := F.1) hx).1

private theorem proofideas_pairFarPart_add_pairNearPart
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    proofideas_pairFarPart (d := d) δ hδ F a b +
      proofideas_pairNearPart (d := d) δ hδ F a b = F := by
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  have hη_temp : ηδ.HasTemperateGrowth := by
    fun_prop
  have hφ_temp : φδ.HasTemperateGrowth := by
    fun_prop
  apply Subtype.ext
  ext x
  change
    (SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) x +
      (SchwartzMap.smulLeftCLM ℂ ηδ F.1 : SchwartzNPoint d k) x = F.1 x
  rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp,
    SchwartzMap.smulLeftCLM_apply_apply hη_temp]
  simp only [φδ, smul_eq_mul]
  ring

private theorem proofideas_pairFarPart_tendsto
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le_one : ρ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        proofideas_pairFarPart (d := d) (ρ / (n + 1 : ℝ))
          (by positivity) F a b)
      Filter.atTop (nhds F) := by
  let near : ℕ → ZeroDiagonalSchwartz d k := fun n =>
    proofideas_pairNearPart (d := d) (ρ / (n + 1 : ℝ)) (by positivity) F a b
  let far : ℕ → ZeroDiagonalSchwartz d k := fun n =>
    proofideas_pairFarPart (d := d) (ρ / (n + 1 : ℝ)) (by positivity) F a b
  have hnear_tendsto :
      Filter.Tendsto near Filter.atTop (nhds (0 : ZeroDiagonalSchwartz d k)) :=
    proofideas_pairNearPart_tendsto_zero
      (d := d) F hF_compact a b hab hρ_pos hρ_le_one
  have hnear_val_tendsto :
      Filter.Tendsto (fun n : ℕ => (near n).1) Filter.atTop
        (nhds (0 : SchwartzNPoint d k)) := by
    rw [tendsto_subtype_rng] at hnear_tendsto
    simpa using hnear_tendsto
  have hval_tendsto :
      Filter.Tendsto (fun n : ℕ => (far n).1) Filter.atTop
        (nhds F.1) := by
    have hseq_eq :
        (fun n : ℕ => (far n).1) =
          (fun n : ℕ => F.1 - (near n).1) := by
      funext n
      have hδ : 0 < ρ / (n + 1 : ℝ) := by positivity
      have hsum_val : (far n).1 + (near n).1 = F.1 := by
        have hcoe :
            ((far n + near n : ZeroDiagonalSchwartz d k)).1 = F.1 := by
          simpa [far, near] using congrArg
            (fun z : ZeroDiagonalSchwartz d k => z.1)
            (proofideas_pairFarPart_add_pairNearPart
              (d := d) (δ := ρ / (n + 1 : ℝ)) hδ F a b)
        exact hcoe
      exact eq_sub_iff_add_eq.mpr hsum_val
    rw [hseq_eq]
    simpa [sub_eq_add_neg] using (tendsto_const_nhds.sub hnear_val_tendsto)
  rw [tendsto_subtype_rng]
  simpa [far]
    using hval_tendsto

private theorem compactlySupported_zeroDiagonal_subset_closure_of_coincidenceFree
    {d : ℕ} [NeZero d]
    (k : ℕ)
    (B : Submodule ℂ (ZeroDiagonalSchwartz d k))
    (hcoincidenceFree :
      ∀ F : ZeroDiagonalSchwartz d k,
        HasCompactSupport
          ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) →
        Disjoint
          (tsupport
            ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
          (CoincidenceLocus d k) →
        F ∈ closure
          ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
            Set (ZeroDiagonalSchwartz d k))) :
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} ⊆
      closure
        ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) := by
  classical
  let Pair := collisionPairIndex k
  let pairs : List Pair := (Finset.univ : Finset Pair).toList
  let C : Set (ZeroDiagonalSchwartz d k) := closure ((B : Set (ZeroDiagonalSchwartz d k)))
  let Avoid (F : ZeroDiagonalSchwartz d k) (p : Pair) : Prop :=
    Disjoint
      (tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
      {x : NPointDomain d k | x p.1.1 = x p.1.2}
  let Good (l : List Pair) : Prop :=
    ∀ F : ZeroDiagonalSchwartz d k,
      HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) →
      (∀ p : Pair, p ∈ l → Avoid F p) →
      F ∈ C
  have hbase : Good pairs := by
    intro F hF_comp havoid
    have hF_disj :
        Disjoint
          (tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
          (CoincidenceLocus d k) := by
      rw [Set.disjoint_left]
      intro x hx hcoin
      rcases hcoin with ⟨i, j, hij, hEq⟩
      let p : Pair := ⟨(i, j), hij⟩
      have hp_mem : p ∈ pairs := by
        simp [pairs]
      exact Set.disjoint_left.mp (havoid p hp_mem) hx (by simpa [p] using hEq)
    simpa [C] using hcoincidenceFree F hF_comp hF_disj
  have hstep : ∀ (p : Pair) (l : List Pair), Good (p :: l) → Good l := by
    intro p l hnext F hF_comp havoid
    let far : ℕ → ZeroDiagonalSchwartz d k := fun n =>
      proofideas_pairFarPart (d := d) (1 / (n + 1 : ℝ)) (by positivity)
        F p.1.1 p.1.2
    have hfar_tendsto : Filter.Tendsto far Filter.atTop (nhds F) := by
      simpa [far] using
        proofideas_pairFarPart_tendsto (d := d) F hF_comp p.1.1 p.1.2 p.2
          (ρ := 1) (by norm_num) (by norm_num)
    have hfar_mem : ∀ n : ℕ, far n ∈ C := by
      intro n
      refine hnext (far n) ?hcomp ?havoid
      · simpa [far] using
          proofideas_pairFarPart_hasCompactSupport
            (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
            F hF_comp p.1.1 p.1.2
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst q
          simpa [Avoid, far] using
            proofideas_pairFarPart_tsupport_disjoint_pair_diagonal
              (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
              F p.1.1 p.1.2
        · dsimp [Avoid]
          rw [Set.disjoint_left]
          intro x hx hdiag
          have hx_orig :
              x ∈ tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
            simpa [far] using
              proofideas_pairFarPart_tsupport_subset_original
                (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
                F p.1.1 p.1.2 hx
          exact Set.disjoint_left.mp (havoid q hq) hx_orig hdiag
    exact isClosed_closure.mem_of_tendsto hfar_tendsto
      (Filter.Eventually.of_forall hfar_mem)
  have hreduce : ∀ l : List Pair, Good l → Good [] := by
    intro l
    induction l with
    | nil =>
        intro h
        exact h
    | cons p l ih =>
        intro h
        exact ih (hstep p l h)
  intro F hF_comp
  have hempty : Good [] := hreduce pairs hbase
  simpa [C] using hempty F hF_comp (by intro p hp; cases hp)

/-- The physically useful dense generators: compact product sources carrying
one proper Euclidean rotation and one strict support ordering. -/
private def orderedCompactProductTensorSet
    {d : ℕ} [NeZero d] (k : ℕ) :
    Set (ZeroDiagonalSchwartz d k) :=
  {f |
    ∃ P : OSReconstruction.OSIIOrderedCompactProductSource d k,
      f = ⟨SchwartzMap.productTensor P.factors, P.vanishes⟩}

private def orderedCompactProductTensorSubmodule
    {d : ℕ} [NeZero d] (k : ℕ) :
    Submodule ℂ (ZeroDiagonalSchwartz d k) :=
  Submodule.span ℂ (orderedCompactProductTensorSet (d := d) k)

private theorem ordered_cutoff_productTensor_mem_submodule
    {d : ℕ} [NeZero d] {k : ℕ}
    {x : NPointDomain d k}
    (P : OSReconstruction.OSIIOrderedProductNeighborhood x)
    (χs fs : Fin k → SchwartzSpacetime d)
    (hχcompact :
      ∀ i, HasCompactSupport
        ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (hχsupport :
      ∀ i,
        tsupport
            ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i) :
    let gs : Fin k → SchwartzSpacetime d :=
      fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)
    ∃ hvanish :
        VanishesToInfiniteOrderOnCoincidence
          (SchwartzMap.productTensor gs),
      (⟨SchwartzMap.productTensor gs, hvanish⟩ :
          ZeroDiagonalSchwartz d k) ∈
        orderedCompactProductTensorSubmodule (d := d) k := by
  intro gs
  have hgs_compact :
      ∀ i, HasCompactSupport
        ((gs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    intro i
    refine (hχcompact i).mono' ?_
    intro y hy
    have hyts :
        y ∈ tsupport
          ((gs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
      subset_closure hy
    exact
      (SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (f := fs i) hyts).2
  have hgs_support :
      ∀ i,
        tsupport
            ((gs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i := by
    intro i y hy
    exact hχsupport i
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (f := fs i) hy).2)
  let Q : OSReconstruction.OSIIOrderedCompactProductSource d k :=
    OSReconstruction.OSIIOrderedCompactProductSource.ofNeighborhood
      P gs hgs_compact hgs_support
  refine ⟨Q.vanishes, ?_⟩
  exact Submodule.subset_span ⟨Q, rfl⟩

private theorem ordered_product_cutoff_fixed_mem_closure
    {d : ℕ} [NeZero d] {k : ℕ}
    {x : NPointDomain d k}
    (P : OSReconstruction.OSIIOrderedProductNeighborhood x)
    (χs : Fin k → SchwartzSpacetime d)
    (hχcompact :
      ∀ i, HasCompactSupport
        ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (hχsupport :
      ∀ i,
        tsupport
            ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i)
    (F : ZeroDiagonalSchwartz d k)
    (hfix :
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs) F.1 =
        F.1) :
    F ∈ closure
      ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
  let S_all : Set (SchwartzNPoint d k) :=
    {G | ∃ fs : Fin k → SchwartzSpacetime d,
      G = SchwartzMap.productTensor fs}
  let M_all : Submodule ℂ (SchwartzNPoint d k) :=
    Submodule.span ℂ S_all
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    orderedCompactProductTensorSubmodule (d := d) k
  let T : SchwartzNPoint d k →L[ℂ] SchwartzNPoint d k :=
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs)
  let coeZ : ZeroDiagonalSchwartz d k → SchwartzNPoint d k := fun z => z.1
  let coeL : ZeroDiagonalSchwartz d k →ₗ[ℂ] SchwartzNPoint d k :=
    { toFun := coeZ
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hT_maps :
      ∀ G ∈ (M_all : Set (SchwartzNPoint d k)), T G ∈ B.map coeL := by
    intro G hG
    change G ∈ M_all at hG
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
    · intro G hG
      rcases hG with ⟨fs, rfl⟩
      let gs : Fin k → SchwartzSpacetime d :=
        fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)
      obtain ⟨hvanish, hmem⟩ :=
        ordered_cutoff_productTensor_mem_submodule
          P χs fs hχcompact hχsupport
      refine ⟨⟨SchwartzMap.productTensor gs, hvanish⟩, hmem, ?_⟩
      change coeZ ⟨SchwartzMap.productTensor gs, hvanish⟩ =
        T (SchwartzMap.productTensor fs)
      dsimp [coeZ, T, gs]
      exact (productTensor_cutoff_productTensor χs fs).symm
    · simpa using (Submodule.zero_mem (B.map coeL))
    · intro G H _ _ hG_mem hH_mem
      simpa [map_add] using
        (Submodule.add_mem (B.map coeL) hG_mem hH_mem)
    · intro c G _ hG_mem
      simpa [map_smulₛₗ] using
        (Submodule.smul_mem (B.map coeL) c hG_mem)
  have hF_all :
      F.1 ∈ closure
        ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k)) := by
    simpa [M_all, S_all] using (productTensor_span_dense d k F.1)
  have hTF_image :
      T F.1 ∈ closure
        (T '' ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k))) := by
    have hmem_image_closure :
        T F.1 ∈
          T '' closure
            ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
              Set (SchwartzNPoint d k)) :=
      ⟨F.1, hF_all, rfl⟩
    exact image_closure_subset_closure_image T.continuous
      hmem_image_closure
  have hTF_closure_map :
      T F.1 ∈ closure
        ((B.map coeL : Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k)) := by
    exact closure_mono (by
      rintro _ ⟨G, hG, rfl⟩
      exact hT_maps G hG) hTF_image
  have hmap :
      ((B.map coeL : Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k)) =
        coeZ '' ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) :=
    Submodule.map_coe coeL B
  have hfull :
      F.1 ∈ closure
        (coeZ '' ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k))) := by
    rw [← hmap]
    simpa [T, hfix] using hTF_closure_map
  have hsub :
      F ∈ closure
        ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) := by
    exact
      (closure_subtype
        (x := (F : ↥(zeroDiagonalSubmodule d k)))
        (s := ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)))).mpr
        (by simpa [coeZ] using hfull)
  simpa [B] using hsub

private theorem ordered_product_box_supported_mem_closure
    {d : ℕ} [NeZero d] {k : ℕ}
    {x₀ : NPointDomain d k}
    (P : OSReconstruction.OSIIOrderedProductNeighborhood x₀)
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp :
      HasCompactSupport
        (F.1 : NPointDomain d k → ℂ))
    (hF_box :
      tsupport (F.1 : NPointDomain d k → ℂ) ⊆
        {x | ∀ i : Fin k, x i ∈ P.cell i}) :
    F ∈ closure
      ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
  let K : Fin k → Set (SpacetimeDim d) := fun i =>
    (fun x : NPointDomain d k => x i) ''
      tsupport (F.1 : NPointDomain d k → ℂ)
  have hK_compact : ∀ i, IsCompact (K i) := by
    intro i
    exact hF_comp.isCompact.image (continuous_apply i)
  have hK_sub : ∀ i, K i ⊆ P.cell i := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hF_box hx i
  have hcut_exists :
      ∀ i, ∃ χ : SchwartzSpacetime d,
        (∀ y ∈ K i, χ y = 1) ∧
        tsupport
            ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i ∧
        HasCompactSupport
          ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    intro i
    exact
      OSReconstruction.exists_schwartz_cutoff_eq_one_on_compact_subset_open_with_compactSupport_fin
        (m := d + 1) (K := K i) (U := P.cell i)
        (hK_compact i) (P.cell_open i) (hK_sub i)
  choose χs hχ_one hχ_sub hχ_compact using hcut_exists
  have hfix :
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs) F.1 =
        F.1 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((SchwartzMap.productTensor χs : SchwartzNPoint d k) :
        NPointDomain d k → ℂ))
      (SchwartzMap.productTensor χs).hasTemperateGrowth F.1 x]
    by_cases hx : x ∈ tsupport (F.1 : NPointDomain d k → ℂ)
    · have hprod_one :
          (SchwartzMap.productTensor χs : SchwartzNPoint d k) x = 1 := by
        rw [SchwartzMap.productTensor_apply]
        apply Finset.prod_eq_one
        intro i _hi
        exact hχ_one i (x i) ⟨x, hx, rfl⟩
      simp [hprod_one, smul_eq_mul]
    · have hzero : (F.1 : NPointDomain d k → ℂ) x = 0 :=
        image_eq_zero_of_notMem_tsupport hx
      simp [hzero, smul_eq_mul]
  exact
    ordered_product_cutoff_fixed_mem_closure
      P χs hχ_compact hχ_sub F hfix

private theorem finite_ordered_product_box_cover_mem_closure
    {d : ℕ} [NeZero d] {k : ℕ} {α : Type*} [Fintype α]
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ))
    (V : α → Set (NPointDomain d k))
    (hV_open : ∀ a, IsOpen (V a))
    (hcover : tsupport (F.1 : NPointDomain d k → ℂ) ⊆ ⋃ a, V a)
    (P : α → Σ x : NPointDomain d k,
      OSReconstruction.OSIIOrderedProductNeighborhood x)
    (hV_box :
      ∀ a, V a ⊆ {x | ∀ i : Fin k, x i ∈ (P a).2.cell i}) :
    F ∈ closure
      ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
  obtain ⟨θ, _hθ_compact, hθ_sub, hθ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d k) hF_comp.isCompact hV_open hcover
  let rawPiece : α → SchwartzNPoint d k := fun a =>
    SchwartzMap.smulLeftCLM ℂ (θ a : NPointDomain d k → ℂ) F.1
  have hrawPiece_vanish :
      ∀ a, VanishesToInfiniteOrderOnCoincidence (rawPiece a) := by
    intro a
    simpa [rawPiece] using
      VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (d := d) F.2 (ψ := θ a)
  let pieces : α → ZeroDiagonalSchwartz d k := fun a =>
    ⟨rawPiece a, hrawPiece_vanish a⟩
  have hraw_sum : F.1 = ∑ a, rawPiece a := by
    simpa [rawPiece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) θ F.1
        (by
          intro x hx
          simpa using hθ_sum x hx)
  have hdecomp : F = ∑ a, pieces a := by
    let coeL : ZeroDiagonalSchwartz d k →ₗ[ℂ] SchwartzNPoint d k :=
      { toFun := fun z => z.1
        map_add' := by intro a b; rfl
        map_smul' := by intro c a; rfl }
    have hsum_coe :
        (∑ a, pieces a).1 = ∑ a, (pieces a).1 := by
      change coeL (∑ a, pieces a) = ∑ a, coeL (pieces a)
      rw [map_sum]
    apply SetCoe.ext
    change F.1 = (∑ a, pieces a).1
    rw [hsum_coe]
    simpa [pieces, rawPiece] using hraw_sum
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    orderedCompactProductTensorSubmodule (d := d) k
  have hpiece_comp :
      ∀ a, HasCompactSupport ((pieces a).1 : NPointDomain d k → ℂ) := by
    intro a
    refine hF_comp.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport ((pieces a).1 : NPointDomain d k → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (θ a : NPointDomain d k → ℂ))
        (f := F.1)) hx_ts).1
  have hpiece_box :
      ∀ a, tsupport ((pieces a).1 : NPointDomain d k → ℂ) ⊆
        {x | ∀ i : Fin k, x i ∈ (P a).2.cell i} := by
    intro a x hx
    exact hV_box a
      (hθ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (θ a : NPointDomain d k → ℂ))
          (f := F.1)) hx).2)
  have hpieces :
      ∀ a, pieces a ∈ (B.topologicalClosure :
        Set (ZeroDiagonalSchwartz d k)) := by
    intro a
    simpa [B, Submodule.topologicalClosure_coe] using
      ordered_product_box_supported_mem_closure
        (d := d) (k := k) (P a).2 (pieces a)
        (hpiece_comp a) (hpiece_box a)
  have hsum :
      (∑ a, pieces a) ∈ (B.topologicalClosure :
        Set (ZeroDiagonalSchwartz d k)) := by
    exact Submodule.sum_mem B.topologicalClosure (fun a _ha => hpieces a)
  rw [hdecomp]
  simpa [B, Submodule.topologicalClosure_coe] using hsum

private theorem ordered_coincidence_free_compactSupport_mem_closure
    {d : ℕ} [NeZero d] {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ))
    (hF_disj :
      Disjoint
        (tsupport (F.1 : NPointDomain d k → ℂ))
        (CoincidenceLocus d k)) :
    F ∈ closure
      ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
  classical
  let K : Set (NPointDomain d k) :=
    tsupport (F.1 : NPointDomain d k → ℂ)
  let P : ∀ y : K, OSReconstruction.OSIIOrderedProductNeighborhood y.1 :=
    fun y =>
      Classical.choice
        (OSReconstruction.exists_osiiOrderedProductNeighborhood y.1
          (by
            intro hy
            exact Set.disjoint_left.mp hF_disj y.2 hy))
  let Vβ : K → Set (NPointDomain d k) := fun y =>
    {z | ∀ i : Fin k, z i ∈ (P y).cell i}
  have hVβ_open : ∀ y : K, IsOpen (Vβ y) := by
    intro y
    change IsOpen {z : NPointDomain d k |
      ∀ i : Fin k, z i ∈ (P y).cell i}
    have h :
        IsOpen (⋂ i : Fin k,
          {z : NPointDomain d k | z i ∈ (P y).cell i}) :=
      isOpen_iInter_of_finite (fun i : Fin k =>
        (P y).cell_open i |>.preimage
          (show Continuous (fun z : NPointDomain d k => z i) from
            continuous_apply i))
    convert h using 1
    ext z
    simp
  have hK_cover : K ⊆ ⋃ y : K, Vβ y := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact (P ⟨x, hx⟩).center_mem
  obtain ⟨s, hscover⟩ :=
    hF_comp.isCompact.elim_finite_subcover Vβ hVβ_open hK_cover
  let α := {y : K // y ∈ s}
  let V : α → Set (NPointDomain d k) := fun a => Vβ a.1
  let Q : α → Σ x : NPointDomain d k,
      OSReconstruction.OSIIOrderedProductNeighborhood x :=
    fun a => ⟨a.1.1, P a.1⟩
  have hV_open : ∀ a : α, IsOpen (V a) := by
    intro a
    exact hVβ_open a.1
  have hcover : K ⊆ ⋃ a : α, V a := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨y, hys, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  have hV_box :
      ∀ a : α, V a ⊆
        {x | ∀ i : Fin k, x i ∈ (Q a).2.cell i} := by
    intro a x hx
    exact hx
  exact
    finite_ordered_product_box_cover_mem_closure
      (d := d) (k := k) F hF_comp V hV_open hcover Q hV_box

private theorem compactlySupported_zeroDiagonal_subset_closure_orderedCompactProductTensorSubmodule
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport
        ((F : ZeroDiagonalSchwartz d k).1 :
          NPointDomain d k → ℂ)} ⊆
      closure
        ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) := by
  apply compactlySupported_zeroDiagonal_subset_closure_of_coincidenceFree
    (d := d) k (orderedCompactProductTensorSubmodule (d := d) k)
  intro F hF_comp hF_disj
  exact
    ordered_coincidence_free_compactSupport_mem_closure
      (d := d) (k := k) F hF_comp hF_disj

private theorem orderedCompactProductTensorSubmodule_dense_zeroDiagonal
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    Dense
      ((orderedCompactProductTensorSubmodule (d := d) k :
        Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
  let C : Set (ZeroDiagonalSchwartz d k) :=
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport
        ((F : ZeroDiagonalSchwartz d k).1 :
          NPointDomain d k → ℂ)}
  have hC_dense : Dense C := dense_hasCompactSupport_zeroDiagonal (d := d) k
  have hC_subset :
      C ⊆ closure
        ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) :=
    compactlySupported_zeroDiagonal_subset_closure_orderedCompactProductTensorSubmodule
      (d := d) k
  have hclosure_subset :
      closure C ⊆ closure
        ((orderedCompactProductTensorSubmodule (d := d) k :
          Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) := by
    exact closure_minimal hC_subset isClosed_closure
  intro F
  exact hclosure_subset (hC_dense F)

/-- Reproduction on ordered compact product sources is enough once the
candidate kernel has the pre-completion coincidence-weighted estimate.

This is the non-circular dense handoff for the Chapter VI route: the local
real-edge argument only has to handle compact chronologically normalized
products, while weighted control extends the identity to every zero-diagonal
Schwartz test. -/
theorem ACROneEuclideanWeightedKernelData.reproducesZeroDiagonal_of_orderedCompactProducts
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    {S : (Fin k → Fin (d + 1) → ℂ) → ℂ}
    (E : ACROneEuclideanWeightedKernelData S)
    (hcoin : (CoincidenceLocus d k).Nonempty)
    (hordered :
      ∀ P : OSReconstruction.OSIIOrderedCompactProductSource d k,
        OS.S k
            ⟨SchwartzMap.productTensor P.factors, P.vanishes⟩ =
          ∫ x : NPointDomain d k,
            S (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor P.factors) x) :
    ∀ f : ZeroDiagonalSchwartz d k,
      OS.S k f =
        ∫ x : NPointDomain d k,
          S (fun j => wickRotatePoint (x j)) * (f.1 x) := by
  have hDense :
      Dense
        (((Submodule.span ℂ
            (orderedCompactProductTensorSet (d := d) k) :
            Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k))) := by
    simpa [orderedCompactProductTensorSubmodule] using
      (orderedCompactProductTensorSubmodule_dense_zeroDiagonal
        (d := d) k)
  apply E.reproducesZeroDiagonal_of_eq_on_dense OS hcoin hDense
  rintro f ⟨P, rfl⟩
  exact hordered P

/-- **ξ-shift: the correct one-variable perturbation in the cumulative-sum structure.**

    In the cumulative-sum parametrization, the j-th new variable at level r is
      ξ[j] = z[j][r] - (if j = 0 then 0 else z[j-1][r])
    These k variables ξ[0], ..., ξ[k-1] are INDEPENDENT:
      C_k^(r+1) = C_k^(r) × UHP^k  (in the (z_base, ξ) parametrization).

    Moving ξ[j] by t (holding ξ[i] fixed for i ≠ j) requires shifting ALL z[i][r]
    for i ≥ j by +t simultaneously, since z[i][r] = ξ[0] + ... + ξ[i] (cumulative sum).

    WARNING: Updating only z[j][r] while keeping z[j+1][r],...,z[k-1][r] fixed changes
    BOTH ξ[j] (by +t) AND ξ[j+1] (by -t), which is NOT a single-variable extension.
    The test case in `test/acr_next_steps_test.lean` (d=1, k=2, r=1) confirms that a
    single-coordinate update can FAIL to land in ACR(r+1). -/
def xiShift {k d : ℕ} (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) : Fin k → Fin (d + 1) → ℂ :=
  fun i μ => if j.val ≤ i.val ∧ μ = r then z i μ + t else z i μ

/-- Shifting a cumulative-difference slice by zero does nothing. -/
private theorem xiShift_zero {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) :
    xiShift j r z 0 = z := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h]
  · simp [xiShift, h]

/-- Successive ξ-shifts in the same cumulative-difference coordinate add. -/
private theorem xiShift_add_same {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (s t : ℂ) :
    xiShift j r (xiShift j r z s) t = xiShift j r z (s + t) := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h, add_assoc]
  · simp [xiShift, h]

/-- In flattened difference coordinates, `xiShift` changes exactly one coordinate:
the `(j,r)` difference variable is translated by `t`, and all other difference
coordinates stay fixed. This is the concrete bookkeeping fact behind the
one-variable slice picture used in analytic continuation. -/
private theorem toDiffFlat_xiShift_eq_update {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.toDiffFlat k d (xiShift j r z t) =
      Function.update (BHW.toDiffFlat k d z) (finProdFinEquiv (j, r))
        (BHW.toDiffFlat k d z (finProdFinEquiv (j, r)) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  simp only [BHW.toDiffFlat, BHW.flattenCfg]
  simp only [finProdFinEquiv.symm_apply_apply]
  have hflat :
      BHW.flattenCfg k d (BHW.diffCoordEquiv k d z) (finProdFinEquiv (i, μ)) =
        BHW.diffCoordEquiv k d z i μ := by
    simp [BHW.flattenCfg]
  by_cases hμ : μ = r
  · subst hμ
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i.val = 0
      · simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0]
      · have hpred_not : ¬ i.val ≤ i.val - 1 := by omega
        simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0, hpred_not]
        ring
    · by_cases hij_lt : i.val < j.val
      · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
          intro h
          apply hij
          exact congrArg Prod.fst (finProdFinEquiv.injective h)
        have hj_not_le : ¬ j.val ≤ i.val := not_le.mpr hij_lt
        by_cases hi0 : i.val = 0
        · have hj0 : j.val ≠ 0 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj0]
        · have hpred_not : ¬ j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_not_le, hpred_not]
      · have hj_le : j.val ≤ i.val := le_of_not_gt hij_lt
        by_cases hi0 : i.val = 0
        · have : False := by
            apply hij
            exact Fin.ext (by omega)
          exact False.elim this
        · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
            intro h
            apply hij
            exact congrArg Prod.fst (finProdFinEquiv.injective h)
          have hpred : j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hpred]
  · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, r) := by
      intro h
      apply hμ
      exact congrArg Prod.snd (finProdFinEquiv.injective h)
    by_cases hi0 : i.val = 0
    · simp [Function.update, hneq]
      rw [hflat]
      simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
    · by_cases hj_le : j.val ≤ i.val
      · by_cases hpred : j.val ≤ i.val - 1
        · simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ, hj_le, hpred]
        · have hji : j = i := by
            apply Fin.ext
            omega
          subst hji
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
      · simp [Function.update, hneq]
        rw [hflat]
        simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hμ]

/-- Inverse-chart form of `toDiffFlat_xiShift_eq_update`: updating exactly the
flattened difference coordinate `(j,r)` by `+ t` reconstructs the configuration
obtained from `xiShift j r` by the same increment. -/
private theorem fromDiffFlat_update_eq_xiShift {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (u : Fin (k * (d + 1)) → ℂ) (t : ℂ) :
    BHW.fromDiffFlat k d
        (Function.update u (finProdFinEquiv (j, r))
          (u (finProdFinEquiv (j, r)) + t)) =
      xiShift j r (BHW.fromDiffFlat k d u) t := by
  have hinj : Function.Injective (BHW.toDiffFlat k d) := by
    intro z₁ z₂ h
    simpa [BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₁,
      BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₂] using
      congrArg (BHW.fromDiffFlat k d) h
  apply hinj
  rw [BHW.toDiffFlat_fromDiffFlat]
  rw [toDiffFlat_xiShift_eq_update]
  simp [BHW.toDiffFlat_fromDiffFlat]

/-- Tail Euclidean time shift starting at index `j`: points with index `i ≥ j`
are shifted by the real time vector `timeShiftVec d t`, earlier points are fixed. -/
private def tailTimeShiftConfig {d k : ℕ} (j : Fin k) (t : ℝ)
    (x : NPointDomain d k) : NPointDomain d k :=
  fun i => if j.val ≤ i.val then x i + timeShiftVec d t else x i

/-- Sign-correct inverse form of `osConjTensorProduct_timeShift_eq_tailShift`.
A positive tail shift of the right block corresponds to a negative time shift on
the right Schwartz factor. This fixes the sign convention needed when a flat
coordinate update by `+ t * I` is converted back to the OS semigroup picture. -/
private theorem osConjTensorProduct_tailTimeShift_eq_timeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x) =
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (-t) g)) x := by
  have htail :=
    osConjTensorProduct_timeShift_eq_tailShift (d := d) f g (-t) x
  have hneg_shift : -timeShiftVec d (-t) = timeShiftVec d t := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  have hcfg :
      (fun i => if h : n ≤ i.val then x i - timeShiftVec d (-t) else x i) =
        tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x := by
    funext i
    by_cases hi : n ≤ i.val
    · simp [tailTimeShiftConfig, hi, sub_eq_add_neg, hneg_shift]
    · simp [tailTimeShiftConfig, hi]
  rw [hcfg] at htail
  exact htail.symm

/-- Forward form of `osConjTensorProduct_tailTimeShift_eq_timeShift`: a positive
time shift on the right Schwartz factor is evaluation of the unshifted tensor
product on the configuration with the right block shifted by `- timeShiftVec d t`.
Written with `tailTimeShiftConfig`, this is the form that matches a flat update
by `- t * I`. -/
private theorem osConjTensorProduct_timeShift_eq_tailTimeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ (-t) x) := by
  simpa using
    (osConjTensorProduct_tailTimeShift_eq_timeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := -t) (x := x)).symm

/-- Tail translation of the right block preserves Lebesgue measure on configuration
space. This is the change-of-variables ingredient for converting the sign-correct
flat-update slice picture back to the Euclidean integral. -/
private theorem rightBlockTailShift_measurePreserving {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t)
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t =
      (fun (x : NPointDomain d (n + m)) (i : Fin (n + m)) =>
        (if h : n ≤ i.val then fun y : SpacetimeDim d => y + timeShiftVec d t else id) (x i)) by
      funext x i
      by_cases h : n ≤ i.val <;> simp [tailTimeShiftConfig, h]]
  exact MeasureTheory.volume_preserving_pi
    (fun i : Fin (n + m) => by
      by_cases h : n ≤ i.val
      · simpa [h] using
          (MeasureTheory.measurePreserving_add_right
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))
            (timeShiftVec d t))
      · simpa [h] using
          (MeasureTheory.MeasurePreserving.id
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))

/-- The right-block tail shift is a measurable equivalence, with inverse given by
shifting the same tail by `-t`. This packages the change of variables needed in
the Euclidean integral form of the slice identity. -/
private def rightBlockTailShiftMeasurableEquiv {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    NPointDomain d (n + m) ≃ᵐ NPointDomain d (n + m) where
  toEquiv :=
    { toFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t
      invFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ (-t)
      left_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi]
      right_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi] }
  measurable_toFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))
  measurable_invFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))

/-- Change of variables under the right-block tail shift. Combined with the
sign-correct pointwise bridge lemmas above, this is the generic integral shell
needed for the remaining `schwinger_continuation_base_step` slice theorem. -/
private theorem integral_comp_rightBlockTailShift {n m : ℕ}
    (hm : 0 < m) (t : ℝ)
    {e : NPointDomain d (n + m) → ℂ} :
    ∫ x, e (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t x) =
      ∫ x, e x := by
  let Ψ := rightBlockTailShiftMeasurableEquiv (d := d) (n := n) (m := m) hm t
  have hmp : MeasureTheory.MeasurePreserving
      (Ψ : NPointDomain d (n + m) → NPointDomain d (n + m))
      MeasureTheory.volume MeasureTheory.volume := by
    change MeasureTheory.MeasurePreserving
      (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t)
      MeasureTheory.volume MeasureTheory.volume
    exact rightBlockTailShift_measurePreserving (d := d) (n := n) (m := m) hm t
  exact hmp.integral_comp' (f := Ψ) e

/-- On Wick-rotated Euclidean configurations, the complex ξ-shift in the time
difference coordinate `(j,0)` is exactly the Wick rotation of a real tail time
shift on the underlying Euclidean configuration. -/
private theorem xiShift_wickRotate_eq_tailTimeShift {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    xiShift j 0 (fun i => wickRotatePoint (x i)) ((t : ℂ) * Complex.I) =
      fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i) := by
  ext i μ
  by_cases hji : j.val ≤ i.val
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec]
      ring
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec, hμ]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint]
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, hμ]

/-- Flattened-difference form of `xiShift_wickRotate_eq_tailTimeShift`: a flat
update by `+ t I` in the `(j,0)` coordinate is exactly the Wick-rotated tail
time shift on Euclidean configurations. This is the coordinate bridge from flat
slice updates back to the OS semigroup picture. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) + (t : ℂ) * Complex.I) := by
  rw [← xiShift_wickRotate_eq_tailTimeShift (d := d) (j := j) (x := x) (t := t)]
  simpa using
    toDiffFlat_xiShift_eq_update (j := j) (r := (0 : Fin (d + 1)))
      (z := fun i => wickRotatePoint (x i)) (t := (t : ℂ) * Complex.I)

/-- Sign-correct specialization of `toDiffFlat_wickRotate_tailTimeShift_eq_update`:
shifting the Euclidean tail by `-t` corresponds to updating the flattened time
difference coordinate by `- t * I`. This is the form aligned with the positive
OS semigroup parameter in `timeShiftSchwartzNPoint t`. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update_sub {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j (-t) x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    toDiffFlat_wickRotate_tailTimeShift_eq_update (d := d) (j := j) (x := x) (-t)

/-- Generic simple-tensor slice identity under the Euclidean integral. A positive
time shift on the right Schwartz factor is converted into a flat update by
`- t * I` in the split time-difference coordinate, with the intervening tail
translation absorbed by `integral_comp_rightBlockTailShift`. This is the core
integral shell for the remaining `schwinger_continuation_base_step` assembly. -/
private theorem simpleTensor_flatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Φ : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Φ (Function.update
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
          (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y *
          Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let e : NPointDomain d (n + m) → ℂ := fun y =>
    (f.osConjTensorProduct g) y *
      Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i)))
  have hshell :
      ∀ x : NPointDomain d (n + m),
        e (tailTimeShiftConfig (d := d) j (-t) x) =
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
            Φ (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) := by
    intro x
    unfold e
    rw [toDiffFlat_wickRotate_tailTimeShift_eq_update_sub (d := d) (j := j) (x := x) (t := t)]
    rw [osConjTensorProduct_timeShift_eq_tailTimeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := t) (x := x)]
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Φ (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m), e (tailTimeShiftConfig (d := d) j (-t) x) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simpa [j] using (hshell x).symm
    _ = ∫ x : NPointDomain d (n + m), e x := by
        simpa [j] using
          (integral_comp_rightBlockTailShift (d := d) (n := n) (m := m) (hm := hm)
            (t := -t) (e := e))
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
        rfl

/-- Configuration-space form of `simpleTensor_flatUpdate_integral_eq`: composing
the flat update with `fromDiffFlat` yields the same Euclidean slice identity. -/
private theorem simpleTensor_fromDiffFlatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I))) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  simpa [Function.comp_apply, BHW.fromDiffFlat_toDiffFlat] using
    (simpleTensor_flatUpdate_integral_eq (d := d) (n := n) (m := m)
      (hm := hm) (f := f) (g := g) (t := t)
      (Φ := Ψ ∘ BHW.fromDiffFlat (n + m) d))

/-- Integrated ξ-shift form of the simple-tensor slice identity. A flat update by
`- t * I` in the split time-difference coordinate is exactly the same Euclidean
integral as the positive right-factor time shift. -/
private theorem simpleTensor_xiShift_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hslice :
      ∀ x : NPointDomain d (n + m),
        BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (j, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) =
          xiShift j 0 (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I) := by
    intro x
    let u : Fin ((n + m) * (d + 1)) → ℂ :=
      BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
    simpa [u, sub_eq_add_neg, BHW.fromDiffFlat_toDiffFlat] using
      (fromDiffFlat_update_eq_xiShift (j := j) (r := (0 : Fin (d + 1)))
        (u := u) (t := -(t : ℂ) * Complex.I))
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (BHW.fromDiffFlat (n + m) d
            (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I))) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [hslice x]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
        simpa [j] using
          (simpleTensor_fromDiffFlatUpdate_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ))

/-- Witness-side version of `simpleTensor_xiShift_integral_eq`: moving the positive
right-factor time shift from the Schwartz tensor term to the Euclidean witness
changes the witness by `+ t * I` in the split time-difference coordinate. -/
theorem simpleTensor_timeShift_integral_eq_xiShift {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      Ψ (fun i => wickRotatePoint (x i)) *
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hcancel : (-(t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
    ring
  calc
    ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (fun i => wickRotatePoint (x i)) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simp [mul_comm]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
        simpa [j, xiShift_add_same, xiShift_zero, hcancel] using
          (simpleTensor_xiShift_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t)
            (Ψ := fun z =>
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z
                ((t : ℂ) * Complex.I))))
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        simp [mul_comm]

/-- If a Euclidean witness `Ψ` recovers `OS.S (n+m)` on zero-diagonal tests, then
the positive right-factor time shift of a simple tensor is recovered by the same
witness evaluated on the `+ t * I` ξ-shifted Euclidean configuration. This is the
direct `OS.S`-level slice identity needed before the finite-sum `ExpandBoth`
assembly in `schwinger_continuation_base_step`. -/
theorem schwinger_simpleTensor_timeShift_eq_xiShift {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  have hg_shift_ord :
      tsupport ((timeShiftSchwartzNPoint (d := d) t g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m := by
    exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  have hvanish_shift :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f) (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  calc
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          ((ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))).1 x) := by
        exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
        simp [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes, hvanish_shift]
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y := by
        exact simpleTensor_timeShift_integral_eq_xiShift
          (d := d) (n := n) (m := m) (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ)






















end
