/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylRepresentation
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Euclidean Weyl Open-Set Assembly

This file starts the open-set assembly layer for the Euclidean Weyl route.  The
checked smaller-ball theorem lives in `EuclideanWeylRepresentation`; the lemmas
here are the finite partition and support bookkeeping needed before the final
locally finite partition-of-unity theorem.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv Convolution BigOperators Manifold

namespace SCV

/-- Every point of an open metric set has a positive closed ball contained in
the set.  This is the radius-selection step used by the open-set Weyl cover. -/
theorem exists_pos_closedBall_subset_of_isOpen
    {E : Type*} [PseudoMetricSpace E]
    {V : Set E} (hV : IsOpen V) {x : E} (hx : x ∈ V) :
    ∃ R : ℝ, 0 < R ∧ Metric.closedBall x R ⊆ V := by
  exact Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)

/-- A positive radius chosen at a point of an open Euclidean set. -/
noncomputable def euclideanWeylOpenRadius
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (x : {x : EuclideanSpace ℝ ι // x ∈ V}) : ℝ :=
  Classical.choose (exists_pos_closedBall_subset_of_isOpen hV_open x.property)

theorem euclideanWeylOpenRadius_pos
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (x : {x : EuclideanSpace ℝ ι // x ∈ V}) :
    0 < euclideanWeylOpenRadius hV_open x :=
  (Classical.choose_spec (exists_pos_closedBall_subset_of_isOpen hV_open x.property)).1

theorem euclideanWeylOpenRadius_closedBall_subset
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (x : {x : EuclideanSpace ℝ ι // x ∈ V}) :
    Metric.closedBall (x : EuclideanSpace ℝ ι) (euclideanWeylOpenRadius hV_open x) ⊆ V :=
  (Classical.choose_spec (exists_pos_closedBall_subset_of_isOpen hV_open x.property)).2

/-- The canonical open-set Weyl representative: inside the open set, use the
canonical ball representative centered at the point with a radius supplied by
openness; outside the open set, set the auxiliary value to zero. -/
noncomputable def euclideanWeylOpenRepresentative
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (x : EuclideanSpace ℝ ι) : ℂ := by
  classical
  exact if hx : x ∈ V then
    euclideanWeylBallRepresentative T x (euclideanWeylOpenRadius hV_open ⟨x, hx⟩) x
  else 0

/-- Near any point of the open set, the canonical open representative agrees
with the fixed Weyl ball representative centered at that point.  This is the
overlap-patching step for the open-set Weyl assembly. -/
theorem euclideanWeylOpenRepresentative_eq_ballRepresentative_on_small_ball
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) V →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
    {c : EuclideanSpace ℝ ι} (hc : c ∈ V) :
    ∀ y ∈ Metric.ball c (euclideanWeylOpenRadius hV_open ⟨c, hc⟩ / 4),
      euclideanWeylOpenRepresentative T hV_open y =
        euclideanWeylBallRepresentative T c (euclideanWeylOpenRadius hV_open ⟨c, hc⟩) y := by
  intro y hy
  let R0 : ℝ := euclideanWeylOpenRadius hV_open ⟨c, hc⟩
  have hR0_pos : 0 < R0 := euclideanWeylOpenRadius_pos hV_open ⟨c, hc⟩
  have hR0_sub : Metric.closedBall c R0 ⊆ V :=
    euclideanWeylOpenRadius_closedBall_subset hV_open ⟨c, hc⟩
  have hy_ball_R0 : y ∈ Metric.ball c R0 := by
    rw [Metric.mem_ball] at hy ⊢
    nlinarith
  have hyV : y ∈ V := by
    exact hR0_sub (Metric.ball_subset_closedBall hy_ball_R0)
  let Ry : ℝ := euclideanWeylOpenRadius hV_open ⟨y, hyV⟩
  have hRy_pos : 0 < Ry := euclideanWeylOpenRadius_pos hV_open ⟨y, hyV⟩
  have hRy_sub : Metric.closedBall y Ry ⊆ V :=
    euclideanWeylOpenRadius_closedBall_subset hV_open ⟨y, hyV⟩
  let ε : ℝ := min ((R0 - dist y c) / 2) (Ry / 2)
  have hε_pos : 0 < ε := by
    have hmargin : 0 < (R0 - dist y c) / 2 := by
      rw [Metric.mem_ball] at hy_ball_R0
      linarith
    exact lt_min hmargin (by linarith)
  have hε_le_margin : ε ≤ (R0 - dist y c) / 2 := min_le_left _ _
  have hε_lt_Ry : ε < Ry := by
    calc
      ε ≤ Ry / 2 := min_le_right _ _
      _ < Ry := by linarith
  have hε_c : Metric.closedBall y ε ⊆ Metric.ball c R0 := by
    exact (Metric.closedBall_subset_closedBall hε_le_margin).trans
      (closedBall_subset_ball_of_half_margin hy_ball_R0)
  have hε_y : Metric.closedBall y ε ⊆ Metric.ball y Ry := by
    exact Metric.closedBall_subset_ball hε_lt_Ry
  have hΔc :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R0) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0 := by
    intro φ hφ
    exact hΔ φ ⟨hφ.1, hφ.2.trans (Metric.ball_subset_closedBall.trans hR0_sub)⟩
  have hΔy :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball y Ry) →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0 := by
    intro φ hφ
    exact hΔ φ ⟨hφ.1, hφ.2.trans (Metric.ball_subset_closedBall.trans hRy_sub)⟩
  have hleft :
      euclideanWeylBallRepresentative T y Ry y =
        T (euclideanReflectedTranslate y (euclideanWeylBump ε hε_pos)) := by
    exact euclideanWeylBallRepresentative_eq_regularized T hΔy hε_pos hε_y
  have hright :
      euclideanWeylBallRepresentative T c R0 y =
        T (euclideanReflectedTranslate y (euclideanWeylBump ε hε_pos)) := by
    exact euclideanWeylBallRepresentative_eq_regularized T hΔc hε_pos hε_c
  rw [euclideanWeylOpenRepresentative]
  rw [dif_pos hyV]
  change euclideanWeylBallRepresentative T y Ry y = euclideanWeylBallRepresentative T c R0 y
  exact hleft.trans hright.symm

/-- The canonical open-set Weyl representative is smooth on the open set. -/
theorem contDiffOn_euclideanWeylOpenRepresentative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {V : Set (EuclideanSpace ℝ ι)} (hV_open : IsOpen V)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) V →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanWeylOpenRepresentative T hV_open) V := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro c hc
  let R0 : ℝ := euclideanWeylOpenRadius hV_open ⟨c, hc⟩
  have hR0_pos : 0 < R0 := euclideanWeylOpenRadius_pos hV_open ⟨c, hc⟩
  have hR0_sub : Metric.closedBall c R0 ⊆ V :=
    euclideanWeylOpenRadius_closedBall_subset hV_open ⟨c, hc⟩
  refine ⟨Metric.ball c (R0 / 4), isOpen_ball, ?_, ?_⟩
  · simp [R0, hR0_pos]
  · have hΔc :
        ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
          SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R0) →
            T
              (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0 := by
      intro φ hφ
      exact hΔ φ ⟨hφ.1, hφ.2.trans (Metric.ball_subset_closedBall.trans hR0_sub)⟩
    have hsmooth_fixed :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (euclideanWeylBallRepresentative T c R0)
          (Metric.ball c (R0 / 4)) := by
      have hε : 0 < R0 / 8 := by linarith
      have hεR : R0 / 8 + R0 / 4 < R0 := by linarith
      exact contDiffOn_euclideanWeylBallRepresentative T hε hεR hΔc
    refine (hsmooth_fixed.mono inter_subset_right).congr ?_
    intro y hy
    exact euclideanWeylOpenRepresentative_eq_ballRepresentative_on_small_ball
      T hV_open hΔ hc y hy.2

/-- Multiplying a Schwartz test by a Schwartz partition factor keeps the
topological support inside the intersection of the two support regions. -/
theorem supportsInOpen_partition_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ φ : SchwartzMap E ℂ} {U V : Set E}
    (hχ : tsupport (χ : E → ℂ) ⊆ U)
    (hφ : SupportsInOpen (φ : E → ℂ) V) :
    SupportsInOpen
      ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ : SchwartzMap E ℂ) : E → ℂ)
      (U ∩ V) := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans
        (fun x hx =>
          (SchwartzMap.tsupport_smulLeftCLM_subset
            (F := ℂ) (g := (χ : E → ℂ)) (f := φ) hx).1))
  · intro x hx
    have hpair :=
      SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ) (g := (χ : E → ℂ)) (f := φ) hx
    exact ⟨hχ hpair.2, hφ.2 hpair.1⟩

/-- One-sided support form of `supportsInOpen_partition_mul`: this is the form
used when a partition factor is subordinate to the local ball on which a Weyl
representative is available. -/
theorem supportsInOpen_partition_mul_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ φ : SchwartzMap E ℂ} {U V : Set E}
    (hχ : tsupport (χ : E → ℂ) ⊆ U)
    (hφ : SupportsInOpen (φ : E → ℂ) V) :
    SupportsInOpen
      ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ : SchwartzMap E ℂ) : E → ℂ)
      U := by
  have hUV := supportsInOpen_partition_mul (χ := χ) (φ := φ) (U := U) (V := V) hχ hφ
  exact ⟨hUV.1, hUV.2.trans inter_subset_left⟩

/-- A finite smooth partition of unity on a compact set, converted into
complex-valued Schwartz functions.  The relative-compactness hypothesis is the
exact condition used later for finite ball covers of `tsupport φ`. -/
theorem exists_finite_schwartz_partitionOfUnity_on_compact
    {α : Type*} [Fintype α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hU_relcompact : ∀ i, ∃ c R, U i ⊆ Metric.closedBall c R)
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  obtain ⟨ρ, hρsub⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) hK.isClosed U hU_open hcover
  have hsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ((ρ i x : ℝ) : ℂ)) := by
    intro i
    exact Complex.ofRealCLM.contDiff.comp (ρ i).contMDiff.contDiff
  have hcompact_real : ∀ i, HasCompactSupport (fun x : E => ρ i x) := by
    intro i
    rcases hU_relcompact i with ⟨c, R, hUR⟩
    rw [HasCompactSupport]
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall c R) (isClosed_tsupport _)
      ((hρsub i).trans hUR)
  have hcompact_complex :
      ∀ i, HasCompactSupport (fun x : E => ((ρ i x : ℝ) : ℂ)) := by
    intro i
    simpa [HasCompactSupport, tsupport, Function.support] using hcompact_real i
  let χ : α → SchwartzMap E ℂ := fun i =>
    (hcompact_complex i).toSchwartzMap (hsmooth i)
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro i
    simpa [χ] using hcompact_complex i
  · intro i
    have happly : ∀ x : E, χ i x = ((ρ i x : ℝ) : ℂ) := by
      intro x
      exact HasCompactSupport.toSchwartzMap_toFun (hcompact_complex i) (hsmooth i) x
    intro x hx
    have hx' : x ∈ tsupport (fun x : E => ((ρ i x : ℝ) : ℂ)) := by
      simpa [happly] using hx
    have hxreal : x ∈ tsupport (fun x : E => ρ i x) := by
      simpa [tsupport, Function.support] using hx'
    exact hρsub i hxreal
  · intro x hxK
    have hsum_real : ∑ i, ρ i x = 1 := by
      have h := ρ.sum_eq_one hxK
      rwa [finsum_eq_sum_of_fintype] at h
    have hχ_apply : ∀ i, χ i x = ((ρ i x : ℝ) : ℂ) := by
      intro i
      exact HasCompactSupport.toSchwartzMap_toFun (hcompact_complex i) (hsmooth i) x
    calc
      ∑ i, χ i x = ∑ i, ((ρ i x : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hχ_apply i]
      _ = 1 := by
        rw [← Complex.ofReal_sum, hsum_real]
        norm_num

/-- If finitely many Schwartz partition factors add to one on the topological
support of `φ`, then the corresponding finite sum of localized tests is exactly
`φ` in Schwartz space. -/
theorem schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : Type*} (s : Finset α)
    (χ : α → SchwartzMap E ℂ) (φ : SchwartzMap E ℂ)
    (hpart : ∀ x ∈ tsupport (φ : E → ℂ), ∑ i ∈ s, χ i x = 1) :
    φ = ∑ i ∈ s, SchwartzMap.smulLeftCLM ℂ (χ i : E → ℂ) φ := by
  ext x
  by_cases hx : x ∈ tsupport (φ : E → ℂ)
  · have hsum : ∑ i ∈ s, χ i x = 1 := hpart x hx
    have hterm :
        ∑ i ∈ s, (SchwartzMap.smulLeftCLM ℂ (χ i : E → ℂ) φ) x =
          ∑ i ∈ s, χ i x * φ x := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [SchwartzMap.smulLeftCLM_apply_apply (χ i).hasTemperateGrowth]
    calc
      φ x = (1 : ℂ) * φ x := by simp
      _ = (∑ i ∈ s, χ i x) * φ x := by rw [hsum]
      _ = ∑ i ∈ s, χ i x * φ x := by rw [Finset.sum_mul]
      _ = (∑ i ∈ s, SchwartzMap.smulLeftCLM ℂ (χ i : E → ℂ) φ) x := by
        simp [hterm]
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hterm :
        ∑ i ∈ s, (SchwartzMap.smulLeftCLM ℂ (χ i : E → ℂ) φ) x = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      rw [SchwartzMap.smulLeftCLM_apply_apply (χ i).hasTemperateGrowth]
      simp [hφx]
    rw [hφx]
    simp [hterm]

/-- A function that is continuous on an open set is integrable after
multiplication by a Schwartz test whose topological support is compact and
contained in that open set.  This is the analytic bookkeeping needed for the
finite integral passage in the open-set Weyl assembly. -/
theorem integrable_continuousOn_mul_schwartz_of_supportsInOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    {H : E → ℂ} {ψ : SchwartzMap E ℂ} {U : Set E}
    (hU : IsOpen U)
    (hH : ContinuousOn H U)
    (hψ : SupportsInOpen (ψ : E → ℂ) U) :
    Integrable (fun x : E => H x * ψ x) := by
  have hcont : Continuous fun x : E => H x * ψ x := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxU : x ∈ U
    · have hH_at : ContinuousAt H x :=
        (hH x hxU).continuousAt (hU.mem_nhds hxU)
      exact hH_at.mul ψ.continuous.continuousAt
    · have hx_not_tsupport : x ∉ tsupport (ψ : E → ℂ) := by
        intro hx
        exact hxU (hψ.2 hx)
      have hψ_zero : (ψ : E → ℂ) =ᶠ[𝓝 x] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hx_not_tsupport
      have hprod_zero : (fun y : E => H y * ψ y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hψ_zero] with y hy
        simp [hy]
      exact hprod_zero.continuousAt
  have hcompact : HasCompactSupport fun x : E => H x * ψ x := by
    rw [HasCompactSupport]
    exact IsCompact.of_isClosed_subset hψ.1 (isClosed_tsupport _)
      (by
        intro x hx
        exact tsupport_mul_subset_right hx)
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Finite partition summation for a single compactly supported Euclidean test.
If `H` represents `T` on each member of a finite cover after localization by a
Schwartz partition of unity, then `H` represents `T` on the original test. -/
theorem euclideanDistribution_representation_of_finite_partition_for_test
    {ι : Type*} [Fintype ι]
    {α : Type*} [Fintype α]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (H : EuclideanSpace ℝ ι → ℂ)
    {U : α → Set (EuclideanSpace ℝ ι)}
    (hU_open : ∀ i, IsOpen (U i))
    (hH_cont : ∀ i, ContinuousOn H (U i))
    (hrep : ∀ i, RepresentsEuclideanDistributionOn T H (U i))
    (χ : α → SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hχ_support : ∀ i, tsupport (χ i : EuclideanSpace ℝ ι → ℂ) ⊆ U i)
    (hpart : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ ι → ℂ), ∑ i, χ i x = 1)
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ)) :
    T φ = ∫ x : EuclideanSpace ℝ ι, H x * φ x := by
  let localized : α → SchwartzMap (EuclideanSpace ℝ ι) ℂ := fun i =>
    SchwartzMap.smulLeftCLM ℂ (χ i : EuclideanSpace ℝ ι → ℂ) φ
  have hφ_decomp : φ = ∑ i, localized i := by
    simpa [localized] using
      schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ φ (by simpa using hpart)
  have hloc_support :
      ∀ i, SupportsInOpen (localized i : EuclideanSpace ℝ ι → ℂ) (U i) := by
    intro i
    simpa [localized] using
      supportsInOpen_partition_mul_left (χ := χ i) (φ := φ)
        (U := U i) (V := Set.univ) (hχ_support i)
        (⟨hφ_compact, subset_univ _⟩ :
          SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) Set.univ)
  have hloc_int :
      ∀ i, Integrable fun x : EuclideanSpace ℝ ι => H x * localized i x := by
    intro i
    exact integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (hU_open i) (hH_cont i) (hloc_support i)
  have hintegral_sum :
      (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
        ∑ i, ∫ x : EuclideanSpace ℝ ι, H x * localized i x := by
    calc
      (∫ x : EuclideanSpace ℝ ι, H x * φ x) =
          ∫ x : EuclideanSpace ℝ ι, H x * (∑ i, localized i) x := by
            rw [hφ_decomp]
      _ = ∫ x : EuclideanSpace ℝ ι, ∑ i, H x * localized i x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            simp [Finset.mul_sum]
      _ = ∑ i, ∫ x : EuclideanSpace ℝ ι, H x * localized i x := by
            simpa using
              (MeasureTheory.integral_finset_sum
                (s := (Finset.univ : Finset α))
                (f := fun i => fun x : EuclideanSpace ℝ ι => H x * localized i x)
                (by intro i _; exact hloc_int i))
  calc
    T φ = T (∑ i, localized i) := by rw [hφ_decomp]
    _ = ∑ i, T (localized i) := by simp
    _ = ∑ i, ∫ x : EuclideanSpace ℝ ι, H x * localized i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact hrep i (localized i) (hloc_support i)
    _ = ∫ x : EuclideanSpace ℝ ι, H x * φ x := hintegral_sum.symm

/-- Local Euclidean Weyl regularity on an arbitrary open set.  If a continuous
Schwartz functional annihilates the Euclidean Laplacian of every compactly
supported test in `V`, then it is represented on `V` by a smooth function. -/
theorem euclidean_weyl_laplacian_distribution_regular_on_open
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {V : Set (EuclideanSpace ℝ ι)}
    (hV_open : IsOpen V)
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) V →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
    ∃ H : EuclideanSpace ℝ ι → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
      RepresentsEuclideanDistributionOn T H V := by
  let H : EuclideanSpace ℝ ι → ℂ := euclideanWeylOpenRepresentative T hV_open
  have hHsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H V := by
    simpa [H] using contDiffOn_euclideanWeylOpenRepresentative T hV_open hΔ
  refine ⟨H, hHsmooth, ?_⟩
  intro φ hφ
  let K : Set (EuclideanSpace ℝ ι) := tsupport (φ : EuclideanSpace ℝ ι → ℂ)
  let β := {x : EuclideanSpace ℝ ι // x ∈ K}
  let Uβ : β → Set (EuclideanSpace ℝ ι) := fun a =>
    Metric.ball (a : EuclideanSpace ℝ ι)
      (euclideanWeylOpenRadius hV_open ⟨(a : EuclideanSpace ℝ ι), hφ.2 a.property⟩ / 4)
  have hUβ_open : ∀ a : β, IsOpen (Uβ a) := by
    intro a
    exact isOpen_ball
  have hK_cover : K ⊆ ⋃ a : β, Uβ a := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    have hRpos := euclideanWeylOpenRadius_pos hV_open ⟨x, hφ.2 hx⟩
    simp [Uβ, hRpos]
  obtain ⟨t, htcover⟩ := hφ.1.elim_finite_subcover Uβ hUβ_open hK_cover
  let α := {a : β // a ∈ t}
  let Uα : α → Set (EuclideanSpace ℝ ι) := fun a => Uβ a.1
  have hUα_open : ∀ a : α, IsOpen (Uα a) := by
    intro a
    exact hUβ_open a.1
  have hUα_relcompact : ∀ a : α, ∃ c R, Uα a ⊆ Metric.closedBall c R := by
    intro a
    refine ⟨(a.1 : EuclideanSpace ℝ ι),
      euclideanWeylOpenRadius hV_open ⟨(a.1 : EuclideanSpace ℝ ι), hφ.2 a.1.property⟩ / 4,
      ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx
  have hK_coverα : K ⊆ ⋃ a : α, Uα a := by
    intro x hx
    rcases mem_iUnion₂.mp (htcover hx) with ⟨a, hat, hxa⟩
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hxa⟩
  obtain ⟨χ, _hχ_compact, hχ_support, hχ_part⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact
      (α := α) hφ.1 hUα_open hUα_relcompact hK_coverα
  have hUα_subset_V : ∀ a : α, Uα a ⊆ V := by
    intro a x hx
    let R : ℝ :=
      euclideanWeylOpenRadius hV_open ⟨(a.1 : EuclideanSpace ℝ ι), hφ.2 a.1.property⟩
    have hRsub : Metric.closedBall (a.1 : EuclideanSpace ℝ ι) R ⊆ V :=
      euclideanWeylOpenRadius_closedBall_subset hV_open
        ⟨(a.1 : EuclideanSpace ℝ ι), hφ.2 a.1.property⟩
    have hxR : x ∈ Metric.closedBall (a.1 : EuclideanSpace ℝ ι) R := by
      have hRpos : 0 < R := euclideanWeylOpenRadius_pos hV_open
        ⟨(a.1 : EuclideanSpace ℝ ι), hφ.2 a.1.property⟩
      rw [Metric.mem_ball] at hx
      rw [Metric.mem_closedBall]
      nlinarith
    exact hRsub hxR
  have hH_cont : ∀ a : α, ContinuousOn H (Uα a) := by
    intro a
    exact hHsmooth.continuousOn.mono (hUα_subset_V a)
  have hrep_local : ∀ a : α, RepresentsEuclideanDistributionOn T H (Uα a) := by
    intro a ψ hψ
    let c : EuclideanSpace ℝ ι := a.1
    let R : ℝ := euclideanWeylOpenRadius hV_open ⟨c, hφ.2 a.1.property⟩
    have hRpos : 0 < R := euclideanWeylOpenRadius_pos hV_open ⟨c, hφ.2 a.1.property⟩
    have hRsub : Metric.closedBall c R ⊆ V :=
      euclideanWeylOpenRadius_closedBall_subset hV_open ⟨c, hφ.2 a.1.property⟩
    have hΔc :
        ∀ θ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
          SupportsInOpen (θ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c R) →
            T
              (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                (SchwartzMap (EuclideanSpace ℝ ι) ℂ) θ) = 0 := by
      intro θ hθ
      exact hΔ θ ⟨hθ.1, hθ.2.trans (Metric.ball_subset_closedBall.trans hRsub)⟩
    have hball_rep :
        RepresentsEuclideanDistributionOn T (euclideanWeylBallRepresentative T c R)
          (Metric.ball c (R / 4)) := by
      have hr : 0 < R / 4 := by linarith
      have hrR : R / 4 < R := by linarith
      exact euclideanWeylBallRepresentative_represents_on_ball T c hr hrR hΔc
    have hψ_ball : SupportsInOpen (ψ : EuclideanSpace ℝ ι → ℂ) (Metric.ball c (R / 4)) := by
      simpa [Uα, Uβ, c, R] using hψ
    have hEq := hball_rep ψ hψ_ball
    calc
      T ψ = ∫ x : EuclideanSpace ℝ ι,
          euclideanWeylBallRepresentative T c R x * ψ x := hEq
      _ = ∫ x : EuclideanSpace ℝ ι, H x * ψ x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport (ψ : EuclideanSpace ℝ ι → ℂ)
        · have hxU : x ∈ Uα a := hψ.2 hx
          have hlocal :=
            euclideanWeylOpenRepresentative_eq_ballRepresentative_on_small_ball
              T hV_open hΔ (hφ.2 a.1.property) x (by simpa [Uα, Uβ, R, c] using hxU)
          have hHx : H x = euclideanWeylBallRepresentative T c R x := by
            simpa [H, R, c] using hlocal
          rw [hHx]
        · have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
          simp [hψx]
  exact euclideanDistribution_representation_of_finite_partition_for_test
    T H hUα_open hH_cont hrep_local χ φ hχ_support
    (by simpa [K] using hχ_part) hφ.1

end SCV
