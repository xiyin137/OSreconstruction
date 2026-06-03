import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz
import OSReconstruction.SCV.LocalProductDescent
import Mathlib.Analysis.Distribution.Support

/-!
# Reduced Boundary Support for the Theorem-2 Locality Route

This file records the support-theoretic handoff needed after the closed-support
Jost/Ruelle boundary equality: the reduced adjacent swap-difference functional
vanishes on tests supported in the spacelike edge, so its distributional
support lies in the complement of that edge.
-/

open scoped Classical NNReal Topology

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Compactly supported reduced Schwartz tests, used as the test-function
domain for the local distributional support statement. -/
structure CompactSchwartzNPoint (d m : ℕ) [NeZero d] where
  toSchwartz : SchwartzNPoint d m
  hasCompactSupport :
    HasCompactSupport (toSchwartz : NPointDomain d m → ℂ)

instance compactSchwartzNPointFunLike (d m : ℕ) [NeZero d] :
    FunLike (CompactSchwartzNPoint d m) (NPointDomain d m) ℂ where
  coe φ := φ.toSchwartz
  coe_injective' := by
    intro φ ψ h
    cases φ
    cases ψ
    simp at h
    subst h
    rfl

namespace DistributionSupport

variable {α β V F : Type*} [TopologicalSpace α] [Zero β] [Zero V]
  [FunLike F α β]

/-- If a distribution-like functional vanishes on an open set, its
distributional support is contained in the closed complement. -/
theorem dsupport_subset_compl_of_isVanishingOn
    {T : F → V} {U : Set α}
    (hT : Distribution.IsVanishingOn T U)
    (hU_open : IsOpen U) :
    Distribution.dsupport T ⊆ Uᶜ := by
  intro x hxT hxU
  have hx_not : x ∉ Distribution.dsupport T := by
    rw [Distribution.notMem_dsupport_iff]
    exact ⟨U, hT, hU_open, hxU⟩
  exact hx_not hxT

variable {γ : Type*} [Zero γ]

/-- Ordinary support inside a set forces topological support inside its
closure. -/
theorem tsupport_subset_closure_of_support_subset
    {f : α → γ} {U : Set α}
    (hf : Function.support f ⊆ U) :
    tsupport f ⊆ closure U := by
  simpa [tsupport] using closure_mono hf

end DistributionSupport

/-- The reduced adjacent swap-difference functional on compact reduced tests. -/
def reducedBoundaryCLMSwapDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    CompactSchwartzNPoint d m → ℂ :=
  fun φ =>
    bvt_reducedWightmanCLM (d := d) OS lgc χ m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m
            (Equiv.swap i ⟨i.val + 1, hi⟩)) φ.toSchwartz) -
      bvt_reducedWightmanCLM (d := d) OS lgc χ m φ.toSchwartz

/-- The reduced adjacent swap-difference as a genuine continuous linear
Schwartz functional. -/
def reducedBoundaryCLMSwapDifferenceCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    SchwartzNPoint d m →L[ℂ] ℂ :=
  (bvt_reducedWightmanCLM (d := d) OS lgc χ m).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realPermOnReducedDiffCLE (d := d) m
          (Equiv.swap i ⟨i.val + 1, hi⟩))) -
    bvt_reducedWightmanCLM (d := d) OS lgc χ m

/-- The CLM version restricts to the compact-test swap-difference functional. -/
theorem reducedBoundaryCLMSwapDifferenceCLM_apply_compact
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : CompactSchwartzNPoint d m) :
    reducedBoundaryCLMSwapDifferenceCLM (d := d) OS lgc χ m i hi
        φ.toSchwartz =
      reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi φ := by
  rfl

/-- The reduced swap-difference has finite Schwartz seminorm order, as every
continuous Schwartz functional does.  This is the analytic finite-order
ingredient needed after the support of the defect is pushed to the edge
frontier. -/
theorem reducedBoundaryCLMSwapDifferenceCLM_finsetSeminormBound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzNPoint d m,
        ‖reducedBoundaryCLMSwapDifferenceCLM
            (d := d) OS lgc χ m i hi φ‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ (NPointDomain d m) ℂ) φ := by
  exact
    SCV.exists_schwartzFunctional_finsetSeminormBound
      (reducedBoundaryCLMSwapDifferenceCLM
        (d := d) OS lgc χ m i hi)

namespace OneSidedFlatness

/-- Ambient flatness principle: if a smooth function is supported in `U`, then
all iterated Frechet derivatives vanish at points approached through the
interior of `Uᶜ`. -/
theorem iteratedFDeriv_zero_of_support_subset_of_mem_closure_interior_compl
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} {x : E}
    (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hf_support : Function.support f ⊆ U)
    (hx : x ∈ closure (interior Uᶜ))
    (n : ℕ) :
    iteratedFDeriv ℝ n f x = 0 := by
  let Z : Set E := {y | iteratedFDeriv ℝ n f y = 0}
  have hZ_closed : IsClosed Z := by
    exact isClosed_eq
      (hf_smooth.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top))
      continuous_const
  have hinterior_subset : interior Uᶜ ⊆ Z := by
    intro y hy
    have hEq : f =ᶠ[𝓝 y] (fun _ : E => (0 : F)) := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      have hz_not_support : z ∉ Function.support f := by
        intro hz_support
        have hz_compl : z ∈ Uᶜ := interior_subset hz
        exact hz_compl (hf_support hz_support)
      simpa [Function.mem_support] using hz_not_support
    have hderiv_eventually :=
      Filter.EventuallyEq.iteratedFDeriv ℝ hEq n
    exact (hderiv_eventually.eq_of_nhds.trans (by simp) :
      iteratedFDeriv ℝ n f y = 0)
  have hclosure_subset : closure (interior Uᶜ) ⊆ Z :=
    hZ_closed.closure_subset_iff.mpr hinterior_subset
  exact hclosure_subset hx

/-- One-dimensional local model for the finite-order boundary step: a smooth
function whose ordinary support is contained in `(0, ∞)` is flat at the
boundary point `0`. -/
theorem iteratedDeriv_zero_at_boundary_of_support_subset_Ioi
    {f : ℝ → ℂ}
    (hf_smooth : ContDiff ℝ ⊤ f)
    (hf_support : Function.support f ⊆ Set.Ioi (0 : ℝ))
    (n : ℕ) :
    iteratedDeriv n f 0 = 0 := by
  let Z : Set ℝ := {x | iteratedDeriv n f x = 0}
  have hZ_closed : IsClosed Z := by
    exact isClosed_eq
      (hf_smooth.continuous_iteratedDeriv n (by simp))
      continuous_const
  have hIio_subset : Set.Iio (0 : ℝ) ⊆ Z := by
    intro y hy
    have hEq : f =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with x hx
      have hx_not_support : x ∉ Function.support f := by
        intro hx_support
        have hx_le : x ≤ 0 := le_of_lt hx
        have hx_pos : 0 < x := hf_support hx_support
        exact (not_lt_of_ge hx_le) hx_pos
      simpa [Function.mem_support] using hx_not_support
    have hderiv :=
      Filter.EventuallyEq.iteratedDeriv_eq n hEq
    change iteratedDeriv n f y = 0
    rw [hderiv]
    simp
  have h0_closure : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
    rw [closure_Iio]
    simp
  have hclosure_subset : closure (Set.Iio (0 : ℝ)) ⊆ Z :=
    hZ_closed.closure_subset_iff.mpr hIio_subset
  exact hclosure_subset h0_closure

end OneSidedFlatness

namespace MinkowskiEdge

omit [NeZero d] in
theorem continuous_minkowskiNormSq :
    Continuous (fun v : Fin (d + 1) → ℝ =>
      MinkowskiSpace.minkowskiNormSq d v) := by
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  exact continuous_finset_sum _ (fun μ _ =>
    (continuous_const.mul (continuous_apply μ)).mul (continuous_apply μ))

/-- Updating only the time coordinate changes the Minkowski square by the
expected one-dimensional quadratic expression. -/
theorem minkowskiNormSq_time_update
    (v : Fin (d + 1) → ℝ) (a : ℝ) :
    MinkowskiSpace.minkowskiNormSq d (Function.update v 0 a) =
      -(a ^ 2) + MinkowskiSpace.spatialNormSq d v := by
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  unfold MinkowskiSpace.spatialNormSq
  simp [Function.update, Fin.succ_ne_zero]

/-- A non-spacelike vector can be pushed to the timelike side by an arbitrarily
small time-coordinate perturbation, with the sign chosen from its time
coordinate. -/
theorem minkowskiNormSq_time_perturb_negative_of_nonpos
    (v : Fin (d + 1) → ℝ)
    (hv : MinkowskiSpace.minkowskiNormSq d v ≤ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    MinkowskiSpace.minkowskiNormSq d
        (Function.update v 0 (v 0 + (if v 0 < 0 then -δ else δ))) < 0 := by
  let σ : ℝ := if v 0 < 0 then -1 else 1
  have hσ_sq : σ ^ 2 = 1 := by
    by_cases h : v 0 < 0 <;> simp [σ, h]
  have hσv_nonneg : 0 ≤ σ * v 0 := by
    by_cases h : v 0 < 0
    · have hv0 : v 0 ≤ 0 := le_of_lt h
      simp [σ, h]
      exact hv0
    · have hv0 : 0 ≤ v 0 := le_of_not_gt h
      simp [σ, h, hv0]
  have hif : (if v 0 < 0 then -δ else δ) = σ * δ := by
    by_cases h : v 0 < 0 <;> simp [σ, h]
  have hbase :
      MinkowskiSpace.spatialNormSq d v ≤ (v 0) ^ 2 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp] at hv
    nlinarith
  rw [hif, minkowskiNormSq_time_update]
  have hsquare :
      (v 0 + σ * δ) ^ 2 =
        (v 0) ^ 2 + 2 * δ * (σ * v 0) + δ ^ 2 := by
    nlinarith [hσ_sq]
  rw [hsquare]
  nlinarith [sq_pos_of_pos hδ, hbase, hσv_nonneg, hδ]

/-- A spacelike Minkowski vector can be moved to the non-spacelike boundary by
changing only its time coordinate, at distance controlled by the square root of
its Minkowski quadratic. -/
theorem exists_nonspacelike_dist_le_sqrt_minkowskiNormSq
    (v : Fin (d + 1) → ℝ)
    (hv : 0 < MinkowskiSpace.minkowskiNormSq d v) :
    ∃ w : Fin (d + 1) → ℝ,
      ¬ MinkowskiSpace.IsSpacelike d w ∧
        dist v w ≤ Real.sqrt (MinkowskiSpace.minkowskiNormSq d v) := by
  let s : ℝ := MinkowskiSpace.spatialNormSq d v
  let a : ℝ := if v 0 < 0 then -Real.sqrt s else Real.sqrt s
  let w : Fin (d + 1) → ℝ := Function.update v 0 a
  have hs : 0 ≤ s := MinkowskiSpace.spatialNormSq_nonneg d v
  have hQ : MinkowskiSpace.minkowskiNormSq d v = s - (v 0) ^ 2 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp [s]
    ring
  have habs : |a - v 0| ≤ Real.sqrt (MinkowskiSpace.minkowskiNormSq d v) := by
    have hbase :
        |((Real.sqrt s) - |(v 0)|)| ≤ Real.sqrt (MinkowskiSpace.minkowskiNormSq d v) := by
      have ht_sq_le_s : (v 0) ^ 2 ≤ s := by nlinarith [hQ, hv]
      have habs_le_sqrt : |v 0| ≤ Real.sqrt s := by
        rw [← Real.sqrt_sq_eq_abs (v 0)]
        exact Real.sqrt_le_sqrt ht_sq_le_s
      have hleft_nonneg : 0 ≤ Real.sqrt s - |v 0| :=
        sub_nonneg.mpr habs_le_sqrt
      have hsq :
          (Real.sqrt s - |v 0|) ^ 2 ≤ MinkowskiSpace.minkowskiNormSq d v := by
        rw [hQ]
        have hsqrt_sq : (Real.sqrt s) ^ 2 = s := by
          rw [Real.sq_sqrt hs]
        have habs_sq : |v 0| ^ 2 = (v 0) ^ 2 := by
          exact sq_abs (v 0)
        have hcross : |v 0| * |v 0| ≤ Real.sqrt s * |v 0| :=
          mul_le_mul_of_nonneg_right habs_le_sqrt (abs_nonneg (v 0))
        nlinarith [hsqrt_sq, habs_sq, hcross]
      have hsq' :
          (Real.sqrt s - |v 0|) ^ 2 ≤
            (Real.sqrt (MinkowskiSpace.minkowskiNormSq d v)) ^ 2 := by
        simpa [Real.sq_sqrt (le_of_lt hv)] using hsq
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using
        (sq_le_sq.mp hsq')
    have hgoal_eq : |a - v 0| = |((Real.sqrt s) - |(v 0)|)| := by
      by_cases ht : v 0 < 0
      · have ht_abs : |v 0| = -(v 0) := abs_of_neg ht
        rw [show a = -Real.sqrt s by simp [a, ht], ht_abs]
        have h1 : -Real.sqrt s - v 0 = -(Real.sqrt s + v 0) := by ring
        have h2 : Real.sqrt s - -(v 0) = Real.sqrt s + v 0 := by ring
        rw [h1, h2, abs_neg]
      · have ht_abs : |v 0| = v 0 := abs_of_nonneg (le_of_not_gt ht)
        simp [a, ht, ht_abs]
    exact hgoal_eq.trans_le hbase
  have hwQ : MinkowskiSpace.minkowskiNormSq d w = 0 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    have hspatial : MinkowskiSpace.spatialNormSq d w = s := by
      unfold MinkowskiSpace.spatialNormSq s w
      apply Finset.sum_congr rfl
      intro i _hi
      simp [Function.update, Fin.succ_ne_zero]
    rw [hspatial]
    have ha_sq : a ^ 2 = s := by
      by_cases ht : v 0 < 0 <;> simp [a, ht, Real.sq_sqrt hs]
    have hw0 : w 0 = a := by simp [w]
    rw [hw0, ha_sq]
    ring
  have hdist : dist v w ≤ |v 0 - a| := by
    rw [dist_eq_norm]
    change ‖v - Function.update v 0 a‖ ≤ |v 0 - a|
    change
      ↑(Finset.univ.sup fun μ => ‖(v - Function.update v 0 a) μ‖₊) ≤
        |v 0 - a|
    have hsup :
        Finset.univ.sup (fun μ => ‖(v - Function.update v 0 a) μ‖₊) ≤
          ‖v 0 - a‖₊ := by
      refine Finset.sup_le_iff.mpr ?_
      intro μ _hμ
      by_cases hμ0 : μ = 0
      · subst μ
        simp
      · have hzero : (v - Function.update v 0 a) μ = 0 := by
          simp [Pi.sub_apply, Function.update, hμ0]
        simp [hzero]
    exact_mod_cast hsup
  refine ⟨w, ?_, ?_⟩
  · intro hsp
    change 0 < MinkowskiSpace.minkowskiNormSq d w at hsp
    linarith
  · exact hdist.trans (by simpa [abs_sub_comm] using habs)

/-- The non-spacelike side of the Minkowski quadratic cone is approached by
timelike vectors, hence belongs to the closure of the interior of the
spacelike cone's complement. -/
theorem nonspacelike_mem_closure_interior_spacelike_compl
    (v : Fin (d + 1) → ℝ)
    (hv : ¬ MinkowskiSpace.IsSpacelike d v) :
    v ∈ closure (interior ({w : Fin (d + 1) → ℝ |
      MinkowskiSpace.IsSpacelike d w}ᶜ)) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  rcases mem_nhds_iff.1 hU with ⟨V, hVU, hVopen, hvV⟩
  rcases Metric.isOpen_iff.1 hVopen v hvV with ⟨ε, hε, hball⟩
  let δ : ℝ := min (ε / 2) 1
  let σ : ℝ := if v 0 < 0 then -1 else 1
  let w : Fin (d + 1) → ℝ := Function.update v 0 (v 0 + σ * δ)
  have hδ_pos : 0 < δ := by
    simp [δ, hε]
  have hδ_lt : δ < ε := by
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hσ_abs : |σ| = 1 := by
    by_cases h : v 0 < 0 <;> simp [σ, h]
  have hwV : w ∈ V := by
    apply hball
    rw [Metric.mem_ball]
    rw [dist_pi_lt_iff hε]
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      simp [w, hσ_abs, abs_of_pos hδ_pos, hδ_lt]
    · simp [w, hμ, hε]
  have hv_nonpos :
      MinkowskiSpace.minkowskiNormSq d v ≤ 0 := by
    unfold MinkowskiSpace.IsSpacelike at hv
    exact le_of_not_gt hv
  have hw_neg :
      MinkowskiSpace.minkowskiNormSq d w < 0 := by
    have hneg :=
      minkowskiNormSq_time_perturb_negative_of_nonpos
        (d := d) v hv_nonpos hδ_pos
    simpa [w, σ, mul_comm] using hneg
  have hw_interior :
      w ∈ interior ({u : Fin (d + 1) → ℝ |
        MinkowskiSpace.IsSpacelike d u}ᶜ) := by
    let T : Set (Fin (d + 1) → ℝ) :=
      {u | MinkowskiSpace.minkowskiNormSq d u < 0}
    have hTopen : IsOpen T := by
      exact isOpen_lt continuous_minkowskiNormSq continuous_const
    have hTsub :
        T ⊆ ({u : Fin (d + 1) → ℝ |
          MinkowskiSpace.IsSpacelike d u}ᶜ) := by
      intro u hu hsp
      change MinkowskiSpace.minkowskiNormSq d u < 0 at hu
      change MinkowskiSpace.minkowskiNormSq d u > 0 at hsp
      linarith
    exact interior_maximal hTsub hTopen hw_neg
  exact ⟨w, hVU hwV, hw_interior⟩

end MinkowskiEdge

/-- The adjacent reduced spacelike edge has the right one-sided frontier
geometry: every frontier point is approached through the interior of the
edge-complement. -/
theorem frontier_adjacent_reducedSpacelikeSwapEdge_subset_closure_interior_compl
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    frontier (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) ⊆
      closure (interior
        (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) := by
  intro ξ hξ
  let q : Fin m := ⟨i.val, by omega⟩
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hUopen : IsOpen U :=
    isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hξ_notU : ξ ∉ U := by
    have hfront := hξ
    rw [hUopen.frontier_eq] at hfront
    exact hfront.2
  have hv_nonsp :
      ¬ MinkowskiSpace.IsSpacelike d (ξ q) := by
    intro hv
    exact hξ_notU (by
      rw [mem_reducedSpacelikeSwapEdge_adjacent_iff]
      simpa [q] using hv)
  have hv_closure :
      ξ q ∈ closure (interior ({w : Fin (d + 1) → ℝ |
        MinkowskiSpace.IsSpacelike d w}ᶜ)) :=
    MinkowskiEdge.nonspacelike_mem_closure_interior_spacelike_compl
      (d := d) (ξ q) hv_nonsp
  rw [mem_closure_iff_nhds] at hv_closure ⊢
  intro N hN
  let sec : (Fin (d + 1) → ℝ) → NPointDomain d m :=
    fun v => replaceReducedCoord (d := d) m q ξ v
  have hsec_cont : Continuous sec := by
    simpa [sec] using
      (continuous_replaceReducedCoord (d := d) m q).comp
        (continuous_const.prodMk continuous_id)
  have hsec_at : sec (ξ q) = ξ := by
    ext r μ
    by_cases hrq : r = q
    · subst r
      simp [sec, replaceReducedCoord]
    · simp [sec, replaceReducedCoord, hrq]
  have hpre : sec ⁻¹' N ∈ 𝓝 (ξ q) := by
    have htend := hsec_cont.tendsto (ξ q)
    rw [hsec_at] at htend
    exact htend hN
  obtain ⟨v, hvN, hvInterior⟩ := hv_closure (sec ⁻¹' N) hpre
  have hsecInterior :
      sec v ∈ interior Uᶜ := by
    let C : Set (Fin (d + 1) → ℝ) :=
      {w : Fin (d + 1) → ℝ | MinkowskiSpace.IsSpacelike d w}
    let W : Set (NPointDomain d m) := {η | η q ∈ interior Cᶜ}
    have hWopen : IsOpen W := by
      exact isOpen_interior.preimage (continuous_apply q)
    have hWsub : W ⊆ Uᶜ := by
      intro η hη hηU
      have hsp : MinkowskiSpace.IsSpacelike d (η q) := by
        rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hηU
        simpa [q] using hηU
      exact (interior_subset hη) hsp
    have hsecW : sec v ∈ W := by
      simpa [sec, W, C, replaceReducedCoord] using hvInterior
    exact interior_maximal hWsub hWopen hsecW
  exact ⟨sec v, hvN, hsecInterior⟩

/-- Public ordinary support in the adjacent reduced spacelike edge forces a
Schwartz test to be flat, to every Frechet order, on the actual edge
frontier.  This is the smooth-test side of the Jost/Vladimirov finite-order
boundary-annihilation step. -/
theorem reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_frontier
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    {ξ : NPointDomain d m}
    (hξ :
      ξ ∈ frontier (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩))
    (n : ℕ) :
    iteratedFDeriv ℝ n (φ : NPointDomain d m → ℂ) ξ = 0 := by
  exact
    OneSidedFlatness.iteratedFDeriv_zero_of_support_subset_of_mem_closure_interior_compl
      (hf_smooth := φ.smooth')
      hφ_support
      (frontier_adjacent_reducedSpacelikeSwapEdge_subset_closure_interior_compl
        (d := d) m i hi hξ)
      n

/-- Public ordinary support in the adjacent reduced spacelike edge forces a
Schwartz test to be flat, to every Frechet order, on the whole closed
complement of that open edge. -/
theorem reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_compl
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    {ξ : NPointDomain d m}
    (hξ : ξ ∈ (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ)
    (r : ℕ) :
    iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ = 0 := by
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hUopen : IsOpen U :=
    isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  by_cases hfront : ξ ∈ frontier U
  · exact
      reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_frontier
        (d := d) m i hi φ hφ_support (by simpa [U] using hfront) r
  · have hnot_closure : ξ ∉ closure U := by
      intro hcl
      exact hfront (by
        rw [hUopen.frontier_eq]
        exact ⟨hcl, by simpa [U] using hξ⟩)
    have hξ_interior : ξ ∈ interior Uᶜ := by
      have hopen_closure_compl : IsOpen ((closure U)ᶜ) :=
        isClosed_closure.isOpen_compl
      refine
        interior_maximal (s := Uᶜ) (t := (closure U)ᶜ) ?_
          hopen_closure_compl hnot_closure
      intro y hy hUy
      exact hy (subset_closure hUy)
    exact
      OneSidedFlatness.iteratedFDeriv_zero_of_support_subset_of_mem_closure_interior_compl
        (hf_smooth := φ.smooth') hφ_support (subset_closure hξ_interior) r

omit [NeZero d] in
/-- The Minkowski quadratic defining the adjacent reduced spacelike edge. -/
def reducedAdjacentEdgeQuadratic
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) : ℝ :=
  MinkowskiSpace.minkowskiNormSq d (ξ ⟨i.val, by omega⟩)

omit [NeZero d] in
/-- The adjacent-edge quadratic is a temperate-growth function.  This is the
finite-order input for the moving strict-inside cutoff estimates. -/
theorem reducedAdjacentEdgeQuadratic_hasTemperateGrowth
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (reducedAdjacentEdgeQuadratic d m i hi).HasTemperateGrowth := by
  let q : Fin m := ⟨i.val, by omega⟩
  have hcoord : ∀ μ : Fin (d + 1),
      (fun ξ : NPointDomain d m => ξ q μ).HasTemperateGrowth := by
    intro μ
    let Lq : NPointDomain d m →L[ℝ] SpacetimeDim d :=
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => SpacetimeDim d) q
    let Lμ : SpacetimeDim d →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin (d + 1))
        (φ := fun _ => ℝ) μ
    simpa [Lq, Lμ] using (Lμ.comp Lq).hasTemperateGrowth
  unfold reducedAdjacentEdgeQuadratic
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  exact Function.HasTemperateGrowth.sum (s := Finset.univ) (fun μ _ => by
    have hμ := hcoord μ
    simpa [mul_assoc] using
      ((Function.HasTemperateGrowth.const
        (MinkowskiSpace.metricSignature d μ)).mul hμ).mul hμ)

/-- The distance from a reduced configuration to the complement of the adjacent
spacelike edge is controlled by the square root of the edge quadratic.  This is
the quantitative geometry needed to convert boundary flatness into a rate on
the shrinking strict-inside collar. -/
theorem reducedAdjacentEdge_infDist_compl_le_sqrt_quadratic
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    Metric.infDist ξ
        ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ≤
      Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0) := by
  let q : Fin m := ⟨i.val, by omega⟩
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  let Q : ℝ := reducedAdjacentEdgeQuadratic d m i hi ξ
  by_cases hQpos : 0 < Q
  · obtain ⟨w, hw_nonsp, hw_dist⟩ :=
      MinkowskiEdge.exists_nonspacelike_dist_le_sqrt_minkowskiNormSq
        (d := d) (ξ q) (by
          simpa [Q, reducedAdjacentEdgeQuadratic, q] using hQpos)
    let η : NPointDomain d m := replaceReducedCoord (d := d) m q ξ w
    have hη_compl : η ∈ Uᶜ := by
      intro hηU
      have hsp : MinkowskiSpace.IsSpacelike d (η q) := by
        rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hηU
        simpa [q, U] using hηU
      exact hw_nonsp (by simpa [η, replaceReducedCoord] using hsp)
    have hdist_replace : dist ξ η ≤ dist (ξ q) w := by
      rw [dist_eq_norm, dist_eq_norm]
      change ‖ξ - Function.update ξ q w‖ ≤ ‖ξ q - w‖
      change
        ↑(Finset.univ.sup fun r => ‖(ξ - Function.update ξ q w) r‖₊) ≤
          ‖ξ q - w‖
      have hsup :
          Finset.univ.sup (fun r => ‖(ξ - Function.update ξ q w) r‖₊) ≤
            ‖ξ q - w‖₊ := by
        refine Finset.sup_le_iff.mpr ?_
        intro r _hr
        by_cases hrq : r = q
        · subst r
          simp
        · have hzero : (ξ - Function.update ξ q w) r = 0 := by
            simp [Pi.sub_apply, Function.update, hrq]
          simp [hzero]
      exact_mod_cast hsup
    calc
      Metric.infDist ξ Uᶜ ≤ dist ξ η := Metric.infDist_le_dist_of_mem hη_compl
      _ ≤ dist (ξ q) w := hdist_replace
      _ ≤ Real.sqrt (MinkowskiSpace.minkowskiNormSq d (ξ q)) := hw_dist
      _ = Real.sqrt (max Q 0) := by
        have hQeq : MinkowskiSpace.minkowskiNormSq d (ξ q) = Q := by
          simp [Q, reducedAdjacentEdgeQuadratic, q]
        rw [hQeq, max_eq_left (le_of_lt hQpos)]
  · have hξ_compl : ξ ∈ Uᶜ := by
      intro hξU
      have hsp : MinkowskiSpace.IsSpacelike d (ξ q) := by
        rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hξU
        simpa [q, U] using hξU
      have hQ : 0 < Q := by
        simpa [Q, reducedAdjacentEdgeQuadratic, q, MinkowskiSpace.IsSpacelike] using hsp
      exact hQpos hQ
    rw [Metric.infDist_zero_of_mem hξ_compl]
    exact Real.sqrt_nonneg (max Q 0)

omit [NeZero d] in
/-- A strict-inside edge cutoff: it is zero near and outside the edge boundary
and equals one after moving a distance `1 / (N + 1)` into the quadratic edge. -/
def reducedAdjacentEdgeInteriorCutoff
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) (ξ : NPointDomain d m) : ℂ :=
  (SCV.smoothCutoff
    (((2 * (N + 1) : ℝ) *
        reducedAdjacentEdgeQuadratic d m i hi ξ) - 2) : ℂ)

omit [NeZero d] in
/-- The strict-inside edge cutoff is a valid multiplier on Schwartz space. -/
theorem reducedAdjacentEdgeInteriorCutoff_hasTemperateGrowth
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) :
    (reducedAdjacentEdgeInteriorCutoff d m i hi N).HasTemperateGrowth := by
  have hquad :
      (reducedAdjacentEdgeQuadratic d m i hi).HasTemperateGrowth :=
    reducedAdjacentEdgeQuadratic_hasTemperateGrowth (d := d) m i hi
  have harg :
      (fun ξ : NPointDomain d m =>
        ((2 * (N + 1) : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ) - 2
        ).HasTemperateGrowth := by
    fun_prop
  simpa [reducedAdjacentEdgeInteriorCutoff] using
    SCV.smoothCutoff_complex_hasTemperateGrowth.comp harg

omit [NeZero d] in
/-- Nonzero cutoff values lie strictly inside the adjacent reduced spacelike
edge. -/
theorem reducedAdjacentEdgeInteriorCutoff_support_subset_edge
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) :
    Function.support (reducedAdjacentEdgeInteriorCutoff d m i hi N) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  intro ξ hξ
  rw [mem_reducedSpacelikeSwapEdge_adjacent_iff]
  unfold MinkowskiSpace.IsSpacelike
  have hcut_nonzero :
      reducedAdjacentEdgeInteriorCutoff d m i hi N ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  have harg_gt_neg_one :
      -1 < ((2 * (N + 1) : ℝ) *
        reducedAdjacentEdgeQuadratic d m i hi ξ) - 2 := by
    by_contra hnot
    have hle :
        ((2 * (N + 1) : ℝ) *
          reducedAdjacentEdgeQuadratic d m i hi ξ) - 2 ≤ -1 :=
      le_of_not_gt hnot
    have hzero : reducedAdjacentEdgeInteriorCutoff d m i hi N ξ = 0 := by
      simpa [reducedAdjacentEdgeInteriorCutoff] using
        (show ((SCV.smoothCutoff
          (((2 * (N + 1) : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ) - 2) : ℂ) =
            0) from by
              exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one hle)
    exact hcut_nonzero hzero
  have hscale_pos : 0 < (2 * (N + 1) : ℝ) := by positivity
  have hquad_pos : 0 < reducedAdjacentEdgeQuadratic d m i hi ξ := by
    nlinarith
  simpa [reducedAdjacentEdgeQuadratic] using hquad_pos

omit [NeZero d] in
/-- The topological support of the strict-inside edge cutoff stays inside the
open adjacent reduced spacelike edge, because the cutoff has a positive
quadratic collar away from the frontier. -/
theorem reducedAdjacentEdgeInteriorCutoff_tsupport_subset_edge
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) :
    tsupport (reducedAdjacentEdgeInteriorCutoff d m i hi N) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  let scale : ℝ := 2 * (N + 1)
  let q : Fin m := ⟨i.val, by omega⟩
  let Q : NPointDomain d m → ℝ := reducedAdjacentEdgeQuadratic d m i hi
  let C : Set (NPointDomain d m) := {ξ | 1 ≤ scale * Q ξ}
  have hscale_pos : 0 < scale := by positivity
  have hsupport_C :
      Function.support (reducedAdjacentEdgeInteriorCutoff d m i hi N) ⊆ C := by
    intro ξ hξ
    have hcut_nonzero :
        reducedAdjacentEdgeInteriorCutoff d m i hi N ξ ≠ 0 := by
      simpa [Function.mem_support] using hξ
    have harg_gt_neg_one : -1 < scale * Q ξ - 2 := by
      by_contra hnot
      have hle : scale * Q ξ - 2 ≤ -1 := le_of_not_gt hnot
      have hzero : reducedAdjacentEdgeInteriorCutoff d m i hi N ξ = 0 := by
        simpa [reducedAdjacentEdgeInteriorCutoff, Q, scale] using
          (show ((SCV.smoothCutoff (scale * Q ξ - 2) : ℂ) = 0) from by
            exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one hle)
      exact hcut_nonzero hzero
    show 1 ≤ scale * Q ξ
    nlinarith
  have hQ_cont : Continuous Q := by
    simpa [Q, reducedAdjacentEdgeQuadratic, q] using
      (MinkowskiEdge.continuous_minkowskiNormSq (d := d)).comp
        (continuous_apply q)
  have hC_closed : IsClosed C := by
    exact isClosed_le continuous_const (continuous_const.mul hQ_cont)
  have htsupport_C :
      tsupport (reducedAdjacentEdgeInteriorCutoff d m i hi N) ⊆ C :=
    closure_minimal hsupport_C hC_closed
  intro ξ hξ
  rw [mem_reducedSpacelikeSwapEdge_adjacent_iff]
  unfold MinkowskiSpace.IsSpacelike
  have hCξ : 1 ≤ scale * Q ξ := htsupport_C hξ
  have hQ_pos : 0 < Q ξ := by nlinarith
  simpa [Q, reducedAdjacentEdgeQuadratic, q] using hQ_pos

/-- Multiplication by the strict-inside edge cutoff as a Schwartz-space CLM. -/
def reducedAdjacentEdgeInteriorCutoffCLM
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) : SchwartzNPoint d m →L[ℂ] SchwartzNPoint d m :=
  SchwartzMap.smulLeftCLM ℂ
    (reducedAdjacentEdgeInteriorCutoff d m i hi N)

omit [NeZero d] in
/-- Pointwise form of the strict-inside edge cutoff CLM. -/
theorem reducedAdjacentEdgeInteriorCutoffCLM_apply
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) (φ : SchwartzNPoint d m) (ξ : NPointDomain d m) :
    reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ ξ =
      reducedAdjacentEdgeInteriorCutoff d m i hi N ξ * φ ξ := by
  change
    (SchwartzMap.smulLeftCLM ℂ
      (reducedAdjacentEdgeInteriorCutoff d m i hi N) φ) ξ =
      reducedAdjacentEdgeInteriorCutoff d m i hi N ξ * φ ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (reducedAdjacentEdgeInteriorCutoff_hasTemperateGrowth d m i hi N)]
  rfl

omit [NeZero d] in
/-- The cutoff approximant remains compactly supported whenever the original
test is compactly supported. -/
theorem reducedAdjacentEdgeInteriorCutoffCLM_hasCompactSupport
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ)) :
    HasCompactSupport
      (reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
        NPointDomain d m → ℂ) := by
  have hfun :
      (reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
        NPointDomain d m → ℂ) =
        reducedAdjacentEdgeInteriorCutoff d m i hi N •
          (φ : NPointDomain d m → ℂ) := by
    funext ξ
    simp [reducedAdjacentEdgeInteriorCutoffCLM_apply, smul_eq_mul]
  rw [hfun]
  exact HasCompactSupport.smul_left
    (f := reducedAdjacentEdgeInteriorCutoff d m i hi N)
    (f' := (φ : NPointDomain d m → ℂ)) hφ_compact

omit [NeZero d] in
/-- The cutoff approximant has topological support strictly inside the
adjacent reduced spacelike edge. -/
theorem reducedAdjacentEdgeInteriorCutoffCLM_tsupport_subset_edge
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) (φ : SchwartzNPoint d m) :
    tsupport
        (reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
          NPointDomain d m → ℂ) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  intro ξ hξ
  exact
    reducedAdjacentEdgeInteriorCutoff_tsupport_subset_edge
      (d := d) m i hi N
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := reducedAdjacentEdgeInteriorCutoff d m i hi N)
        (f := φ) hξ).2)

omit [NeZero d] in
/-- Deep inside the quadratic edge the strict-inside cutoff is identically
one. -/
theorem reducedAdjacentEdgeInteriorCutoff_eq_one_of_one_le_scaled_quadratic
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) {ξ : NPointDomain d m}
    (hdeep :
      1 ≤ (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ) :
    reducedAdjacentEdgeInteriorCutoff d m i hi N ξ = 1 := by
  have harg :
      0 ≤
        ((2 * (N + 1) : ℝ) *
          reducedAdjacentEdgeQuadratic d m i hi ξ) - 2 := by
    nlinarith
  change
    ((SCV.smoothCutoff
      (((2 * (N + 1) : ℝ) *
        reducedAdjacentEdgeQuadratic d m i hi ξ) - 2) : ℂ) = 1)
  exact_mod_cast SCV.smoothCutoff_one_of_nonneg harg

omit [NeZero d] in
/-- The cutoff error is localized in the thin positive quadratic collar next
to the adjacent edge frontier. -/
theorem reducedAdjacentEdgeInteriorCutoffCLM_error_support_subset_collar
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N : ℕ) (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Function.support
        ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
          SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      {ξ | 0 < reducedAdjacentEdgeQuadratic d m i hi ξ ∧
        (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ < 1} := by
  intro ξ hξ
  have hdiff_ne :
      ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
        SchwartzNPoint d m) : NPointDomain d m → ℂ) ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  have hφ_ne : φ ξ ≠ 0 := by
    intro hzero
    have hdiff_zero :
        ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
          SchwartzNPoint d m) : NPointDomain d m → ℂ) ξ = 0 := by
      simp [reducedAdjacentEdgeInteriorCutoffCLM_apply, hzero]
    exact hdiff_ne hdiff_zero
  have hedge := hφ_support (by simpa [Function.mem_support] using hφ_ne)
  have hQ_pos : 0 < reducedAdjacentEdgeQuadratic d m i hi ξ := by
    rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hedge
    simpa [reducedAdjacentEdgeQuadratic, MinkowskiSpace.IsSpacelike]
      using hedge
  have hcut_ne_one :
      reducedAdjacentEdgeInteriorCutoff d m i hi N ξ ≠ 1 := by
    intro hcut
    have hdiff_zero :
        ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
          SchwartzNPoint d m) : NPointDomain d m → ℂ) ξ = 0 := by
      simp [reducedAdjacentEdgeInteriorCutoffCLM_apply, hcut]
    exact hdiff_ne hdiff_zero
  have hnot_deep :
      ¬ 1 ≤ (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ := by
    intro hdeep
    exact hcut_ne_one
      (reducedAdjacentEdgeInteriorCutoff_eq_one_of_one_le_scaled_quadratic
        d m i hi N hdeep)
  exact ⟨hQ_pos, lt_of_not_ge hnot_deep⟩

omit [NeZero d] in
/-- Compact subsets already inside the adjacent reduced spacelike edge have a
uniform positive margin in the defining Minkowski quadratic.  This is the
compact-separation ingredient needed to localize the strict-inside cutoff error
to arbitrarily small neighborhoods of the edge frontier. -/
theorem exists_positive_quadratic_margin_of_compact_subset_reducedAdjacentEdge
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {K : Set (NPointDomain d m)}
    (hK_compact : IsCompact K)
    (hK_edge :
      K ⊆ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    ∃ δ > 0, ∀ ξ ∈ K, δ ≤ reducedAdjacentEdgeQuadratic d m i hi ξ := by
  classical
  let Q : NPointDomain d m → ℝ := reducedAdjacentEdgeQuadratic d m i hi
  have hQ_cont : Continuous Q := by
    let q : Fin m := ⟨i.val, by omega⟩
    simpa [Q, reducedAdjacentEdgeQuadratic, q] using
      (MinkowskiEdge.continuous_minkowskiNormSq (d := d)).comp
        (continuous_apply q)
  by_cases hne : K.Nonempty
  · obtain ⟨ξ0, hξ0, hξ0_min⟩ :=
      hK_compact.exists_isMinOn hne hQ_cont.continuousOn
    have hξ0_edge := hK_edge hξ0
    have hQ0_pos : 0 < Q ξ0 := by
      rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hξ0_edge
      simpa [Q, reducedAdjacentEdgeQuadratic, MinkowskiSpace.IsSpacelike]
        using hξ0_edge
    refine ⟨Q ξ0 / 2, by linarith, ?_⟩
    intro ξ hξ
    have hle : Q ξ0 ≤ Q ξ := isMinOn_iff.mp hξ0_min ξ hξ
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ξ hξ
    exact False.elim (hne ⟨ξ, hξ⟩)

/-- The thin quadratic collar supporting the strict-inside cutoff error
eventually lies in every open neighborhood of the edge frontier, restricted to
the compact topological support of the public test. -/
theorem eventually_collar_subset_open_frontier_neighborhood
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    {W : Set (NPointDomain d m)}
    (hW_open : IsOpen W)
    (hfrontierW :
      tsupport (φ : NPointDomain d m → ℂ) ∩
          frontier (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) ⊆
        W) :
    ∀ᶠ (N : ℕ) in Filter.atTop, ∀ ξ,
      ξ ∈ tsupport (φ : NPointDomain d m → ℂ) →
      0 < reducedAdjacentEdgeQuadratic d m i hi ξ →
      (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ < 1 →
      ξ ∈ W := by
  classical
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  let K : Set (NPointDomain d m) :=
    tsupport (φ : NPointDomain d m → ℂ) ∩ Wᶜ
  have hts_compact :
      IsCompact (tsupport (φ : NPointDomain d m → ℂ)) := by
    simpa [HasCompactSupport] using hφ_compact
  have hK_compact : IsCompact K := by
    simpa [K] using hts_compact.inter_right hW_open.isClosed_compl
  have hU_open : IsOpen U :=
    isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hts_closure :
      tsupport (φ : NPointDomain d m → ℂ) ⊆ closure U :=
    DistributionSupport.tsupport_subset_closure_of_support_subset
      (U := U) hφ_support
  have hK_edge : K ⊆ U := by
    intro ξ hξ
    by_contra hξ_notU
    have hξ_frontier : ξ ∈ frontier U := by
      rw [hU_open.frontier_eq]
      exact ⟨hts_closure hξ.1, hξ_notU⟩
    have hξW : ξ ∈ W := hfrontierW ⟨hξ.1, by simpa [U] using hξ_frontier⟩
    exact hξ.2 hξW
  obtain ⟨δ, hδ_pos, hδ_margin⟩ :=
    exists_positive_quadratic_margin_of_compact_subset_reducedAdjacentEdge
      (d := d) i hi hK_compact (by simpa [U, K] using hK_edge)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  refine Filter.eventually_atTop.mpr ⟨N0, ?_⟩
  intro N hN ξ hξ_ts hQ_pos hcollar
  by_contra hξ_notW
  have hξK : ξ ∈ K := ⟨hξ_ts, hξ_notW⟩
  have hδ_le_Q := hδ_margin ξ hξK
  have hN0δ : 1 < (N0 : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ_pos] at hN0
  have hN0_le_N : (N0 : ℝ) ≤ N := by
    exact_mod_cast hN
  have hNδ : 1 < (N + 1 : ℝ) * δ := by
    nlinarith [hδ_pos, hN0δ, hN0_le_N]
  nlinarith [hδ_le_Q, hNδ, hcollar]

/-- Fixed Frechet derivatives of a public test become uniformly small on the
shrinking quadratic collar.  This is the finite-order boundary-annihilation
form needed for the Schwartz-seminorm cutoff estimate. -/
theorem eventually_collar_iteratedFDeriv_norm_lt
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (N : ℕ) in Filter.atTop, ∀ ξ,
      ξ ∈ tsupport (φ : NPointDomain d m → ℂ) →
      0 < reducedAdjacentEdgeQuadratic d m i hi ξ →
      (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ < 1 →
      ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ < ε := by
  classical
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  let W : Set (NPointDomain d m) :=
    {ξ | ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ < ε}
  have hD_cont :
      Continuous (fun ξ : NPointDomain d m =>
        iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ) :=
    φ.smooth'.continuous_iteratedFDeriv (m := r) (by exact_mod_cast le_top)
  have hW_open : IsOpen W := by
    simpa [W] using isOpen_lt (continuous_norm.comp hD_cont) continuous_const
  have hfrontierW :
      tsupport (φ : NPointDomain d m → ℂ) ∩ frontier U ⊆ W := by
    intro ξ hξ
    have hzero :
        iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ = 0 :=
      reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_frontier
        (d := d) m i hi φ hφ_support (by simpa [U] using hξ.2) r
    simp [W, hzero, hε]
  filter_upwards
    [eventually_collar_subset_open_frontier_neighborhood
      (d := d) i hi φ hφ_compact hφ_support hW_open hfrontierW]
    with N hN
  intro ξ hξ_ts hQ_pos hcollar
  exact hN ξ hξ_ts hQ_pos hcollar

/-- On the actual cutoff-error support, fixed derivatives of the public test
are eventually small. -/
theorem eventually_error_support_iteratedFDeriv_norm_lt
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (N : ℕ) in Filter.atTop, ∀ ξ,
      ξ ∈ Function.support
          ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
            SchwartzNPoint d m) : NPointDomain d m → ℂ) →
      ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ < ε := by
  filter_upwards
    [eventually_collar_iteratedFDeriv_norm_lt
      (d := d) i hi φ hφ_compact hφ_support r hε]
    with N hN
  intro ξ hξ_error
  have hcollar :=
    reducedAdjacentEdgeInteriorCutoffCLM_error_support_subset_collar
      (d := d) m i hi N φ hφ_support hξ_error
  have hdiff_ne :
      ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
        SchwartzNPoint d m) : NPointDomain d m → ℂ) ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ_error
  have hφ_ne : φ ξ ≠ 0 := by
    intro hzero
    have hdiff_zero :
        ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
          SchwartzNPoint d m) : NPointDomain d m → ℂ) ξ = 0 := by
      simp [reducedAdjacentEdgeInteriorCutoffCLM_apply, hzero]
    exact hdiff_ne hdiff_zero
  have hξ_ts : ξ ∈ tsupport (φ : NPointDomain d m → ℂ) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hφ_ne)
  exact hN ξ hξ_ts hcollar.1 hcollar.2

omit [NeZero d] in
/-- Every positive-order derivative of the moving strict-inside cutoff is
supported in the same shrinking quadratic collar. -/
theorem reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_succ_support_subset_collar
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N r : ℕ) :
    Function.support
        (iteratedFDeriv ℝ (r + 1)
          (reducedAdjacentEdgeInteriorCutoff d m i hi N)) ⊆
      {ξ | 0 < reducedAdjacentEdgeQuadratic d m i hi ξ ∧
        (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ ≤ 1} := by
  classical
  let Q : NPointDomain d m → ℝ := reducedAdjacentEdgeQuadratic d m i hi
  let arg : NPointDomain d m → ℝ :=
    fun ξ => (2 * (N + 1) : ℝ) * Q ξ - 2
  let cut : NPointDomain d m → ℂ := reducedAdjacentEdgeInteriorCutoff d m i hi N
  have hQ_cont : Continuous Q := by
    let q : Fin m := ⟨i.val, by omega⟩
    simpa [Q, reducedAdjacentEdgeQuadratic, q] using
      (MinkowskiEdge.continuous_minkowskiNormSq (d := d)).comp
        (continuous_apply q)
  have harg_cont : Continuous arg := by
    simpa [arg] using (continuous_const.mul hQ_cont).sub continuous_const
  let A : Set (NPointDomain d m) := {ξ | 0 < arg ξ}
  let B : Set (NPointDomain d m) := {ξ | arg ξ < -1}
  have hA_open : IsOpen A := by
    simpa [A] using isOpen_lt continuous_const harg_cont
  have hB_open : IsOpen B := by
    simpa [B] using isOpen_lt harg_cont continuous_const
  intro ξ hξ
  have hderiv_ne :
      iteratedFDeriv ℝ (r + 1) cut ξ ≠ 0 := by
    simpa [Function.mem_support, cut] using hξ
  have hnotB : ξ ∉ B := by
    intro hξB
    have hEq : cut =ᶠ[𝓝 ξ] (fun _ : NPointDomain d m => (0 : ℂ)) := by
      filter_upwards [hB_open.mem_nhds hξB] with η hηB
      have hzero : reducedAdjacentEdgeInteriorCutoff d m i hi N η = 0 := by
        have hle : arg η ≤ -1 := le_of_lt hηB
        simpa [cut, arg, Q, reducedAdjacentEdgeInteriorCutoff] using
          (show ((SCV.smoothCutoff (arg η) : ℂ) = 0) from by
            exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one hle)
      simpa [cut] using hzero
    have hderiv_eventually :=
      Filter.EventuallyEq.iteratedFDeriv ℝ hEq (r + 1)
    have hzero :
        iteratedFDeriv ℝ (r + 1) cut ξ = 0 :=
      (hderiv_eventually.eq_of_nhds.trans (by simp) :
        iteratedFDeriv ℝ (r + 1) cut ξ = 0)
    exact hderiv_ne hzero
  have hnotA : ξ ∉ A := by
    intro hξA
    have hEq : cut =ᶠ[𝓝 ξ] (fun _ : NPointDomain d m => (1 : ℂ)) := by
      filter_upwards [hA_open.mem_nhds hξA] with η hηA
      have hone : reducedAdjacentEdgeInteriorCutoff d m i hi N η = 1 := by
        have hnonneg : 0 ≤ arg η := le_of_lt hηA
        simpa [cut, arg, Q, reducedAdjacentEdgeInteriorCutoff] using
          (show ((SCV.smoothCutoff (arg η) : ℂ) = 1) from by
            exact_mod_cast SCV.smoothCutoff_one_of_nonneg hnonneg)
      simpa [cut] using hone
    have hderiv_eventually :=
      Filter.EventuallyEq.iteratedFDeriv ℝ hEq (r + 1)
    have hzero :
        iteratedFDeriv ℝ (r + 1) cut ξ = 0 :=
      (hderiv_eventually.eq_of_nhds.trans
        (by
          simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ)
            (by omega : r + 1 ≠ 0) (1 : ℂ) (E := NPointDomain d m)]) :
        iteratedFDeriv ℝ (r + 1) cut ξ = 0)
    exact hderiv_ne hzero
  have harg_ge : -1 ≤ arg ξ := le_of_not_gt hnotB
  have harg_le : arg ξ ≤ 0 := le_of_not_gt hnotA
  constructor
  · have hscale_pos : 0 < (2 * (N + 1) : ℝ) := by positivity
    nlinarith [harg_ge, hscale_pos]
  · nlinarith [harg_le]

/-- The zero-order Leibniz term in the strict-inside cutoff error is supported
in the same shrinking quadratic collar. -/
theorem one_sub_reducedAdjacentEdgeInteriorCutoff_mul_iteratedFDeriv_support_subset_collar
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N r : ℕ) (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Function.support
        (fun ξ : NPointDomain d m =>
          (1 - reducedAdjacentEdgeInteriorCutoff d m i hi N ξ) •
            iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ) ⊆
      {ξ | 0 < reducedAdjacentEdgeQuadratic d m i hi ξ ∧
        (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ < 1} := by
  intro ξ hξ
  have hprod_ne :
      (1 - reducedAdjacentEdgeInteriorCutoff d m i hi N ξ) •
          iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  have hD_ne :
      iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ ≠ 0 := by
    intro hzero
    exact hprod_ne (by simp [hzero])
  have hcut_ne_one :
      reducedAdjacentEdgeInteriorCutoff d m i hi N ξ ≠ 1 := by
    intro hone
    exact hprod_ne (by simp [hone])
  have hξ_edge :
      ξ ∈ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
    by_contra hnot
    have hzero :
        iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ = 0 :=
      reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_compl
        (d := d) m i hi φ hφ_support (by simpa using hnot) r
    exact hD_ne hzero
  have hQ_pos : 0 < reducedAdjacentEdgeQuadratic d m i hi ξ := by
    rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hξ_edge
    simpa [reducedAdjacentEdgeQuadratic, MinkowskiSpace.IsSpacelike]
      using hξ_edge
  have hnot_deep :
      ¬ 1 ≤ (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ := by
    intro hdeep
    exact hcut_ne_one
      (reducedAdjacentEdgeInteriorCutoff_eq_one_of_one_le_scaled_quadratic
        d m i hi N hdeep)
  exact ⟨hQ_pos, lt_of_not_ge hnot_deep⟩

private theorem exists_iteratedFDeriv_bound_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ r f x‖ ≤ B := by
  have hcont :
      Continuous (fun x : E => iteratedFDeriv ℝ r f x) :=
    hf.continuous_iteratedFDeriv (m := r) (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ :=
    hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro x hx
  exact (hB x hx).trans (le_max_left B 0)

omit [NeZero d] in
/-- On a compact set, every fixed Frechet derivative of the adjacent-edge
quadratic is uniformly bounded. -/
theorem exists_reducedAdjacentEdgeQuadratic_iteratedFDeriv_bound_on_compact
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {K : Set (NPointDomain d m)} (hK : IsCompact K) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ ξ ∈ K,
        ‖iteratedFDeriv ℝ r (reducedAdjacentEdgeQuadratic d m i hi) ξ‖ ≤ B := by
  exact exists_iteratedFDeriv_bound_on_compact hK
    (reducedAdjacentEdgeQuadratic_hasTemperateGrowth
      (d := d) m i hi).1 r

omit [NeZero d] in
/-- The scaled quadratic cutoff argument has only linear growth in the cutoff
parameter, for every derivative order up to a fixed finite order, on each
compact set. -/
theorem exists_scaled_reducedAdjacentEdgeQuadratic_argument_iteratedFDeriv_bound_on_compact
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {K : Set (NPointDomain d m)} (hK : IsCompact K) (rmax : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (N r : ℕ), r ≤ rmax → ∀ ξ ∈ K,
        ‖iteratedFDeriv ℝ r
          (fun ξ : NPointDomain d m =>
            ((2 * (N + 1) : ℝ) *
              reducedAdjacentEdgeQuadratic d m i hi ξ) - 2) ξ‖ ≤
          B * (N + 1 : ℝ) := by
  classical
  choose B hB_nonneg hB_bound using
    fun r : ℕ =>
      exists_reducedAdjacentEdgeQuadratic_iteratedFDeriv_bound_on_compact
        (d := d) i hi hK r
  let B0 : ℝ := (∑ r ∈ Finset.range (rmax + 1), B r) + 2
  have hB0_nonneg : 0 ≤ B0 := by
    dsimp [B0]
    exact add_nonneg
      (Finset.sum_nonneg fun r _ => hB_nonneg r)
      (by norm_num)
  refine ⟨2 * B0, by positivity, ?_⟩
  intro N r hr ξ hξ
  let Q : NPointDomain d m → ℝ := reducedAdjacentEdgeQuadratic d m i hi
  let scale : ℝ := 2 * (N + 1)
  have hQ_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) Q :=
    (reducedAdjacentEdgeQuadratic_hasTemperateGrowth
      (d := d) m i hi).1
  have hBsum :
      B r ≤ ∑ s ∈ Finset.range (rmax + 1), B s := by
    exact Finset.single_le_sum (f := fun s => B s)
      (fun s _ => hB_nonneg s)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  have hB_le_B0 : B r ≤ B0 := by
    exact hBsum.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  by_cases hr0 : r = 0
  · subst r
    rw [norm_iteratedFDeriv_zero]
    have hQ_abs : |Q ξ| ≤ B 0 := by
      simpa [Real.norm_eq_abs, Q] using hB_bound 0 ξ hξ
    have hscale_nonneg : 0 ≤ scale := by positivity
    have hN1_nonneg : 0 ≤ (N + 1 : ℝ) := by positivity
    have hN1_ge_one : (1 : ℝ) ≤ N + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    calc
      ‖scale * Q ξ - 2‖ ≤ ‖scale * Q ξ‖ + ‖(2 : ℝ)‖ := by
        simpa [sub_eq_add_neg] using norm_add_le (scale * Q ξ) (-(2 : ℝ))
      _ = scale * |Q ξ| + 2 := by
        simp [Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
      _ ≤ scale * B 0 + 2 := by
        gcongr
      _ ≤ 2 * B0 * (N + 1 : ℝ) := by
        nlinarith [hB_le_B0, hB0_nonneg, hN1_nonneg, hN1_ge_one]
  · have hconst :
        iteratedFDeriv ℝ r (fun _ : NPointDomain d m => (2 : ℝ)) ξ = 0 := by
      simpa using
        congrFun
          (iteratedFDeriv_const_of_ne
            (𝕜 := ℝ) (E := NPointDomain d m) hr0 (2 : ℝ)) ξ
    have hscale :
        iteratedFDeriv ℝ r (fun ξ : NPointDomain d m => scale * Q ξ) ξ =
          scale • iteratedFDeriv ℝ r Q ξ := by
      simpa [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply
          (𝕜 := ℝ) (a := scale)
          (f := Q) (x := ξ)
          ((hQ_smooth.of_le (by exact_mod_cast le_top)).contDiffAt))
    have hsub :
        iteratedFDeriv ℝ r
            (fun ξ : NPointDomain d m => scale * Q ξ - 2) ξ =
          iteratedFDeriv ℝ r (fun ξ : NPointDomain d m => scale * Q ξ) ξ -
            iteratedFDeriv ℝ r (fun _ : NPointDomain d m => (2 : ℝ)) ξ := by
      exact iteratedFDeriv_sub_apply
        ((hQ_smooth.of_le (by exact_mod_cast le_top)).contDiffAt.const_smul scale)
        (contDiff_const.contDiffAt)
    rw [hsub, hconst, sub_zero, hscale]
    calc
      ‖scale • iteratedFDeriv ℝ r Q ξ‖ =
          |scale| * ‖iteratedFDeriv ℝ r Q ξ‖ := norm_smul scale _
      _ = scale * ‖iteratedFDeriv ℝ r Q ξ‖ := by
        rw [abs_of_nonneg (by positivity : 0 ≤ scale)]
      _ ≤ scale * B r := by
        gcongr
        exact hB_bound r ξ hξ
      _ ≤ 2 * B0 * (N + 1 : ℝ) := by
        have hscale_eq : scale = 2 * (N + 1 : ℝ) := rfl
        nlinarith [hB_le_B0, hB0_nonneg, show (0 : ℝ) ≤ N + 1 by positivity]

omit [NeZero d] in
/-- On a compact set, every fixed Frechet derivative of the moving
strict-inside cutoff is bounded by a fixed polynomial in the cutoff parameter.
This is the product-rule side of the strict-`tsupport` exhaustion estimate. -/
theorem exists_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_bound_on_compact
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {K : Set (NPointDomain d m)} (hK : IsCompact K) (r : ℕ) :
    ∃ (B : ℝ) (P : ℕ), 0 ≤ B ∧
      ∀ (N : ℕ) (ξ : NPointDomain d m), ξ ∈ K →
        ‖iteratedFDeriv ℝ r
          (reducedAdjacentEdgeInteriorCutoff d m i hi N) ξ‖ ≤
          B * (N + 1 : ℝ) ^ P := by
  classical
  let χ : ℝ → ℂ := fun t => (SCV.smoothCutoff t : ℂ)
  obtain ⟨kχ, Cχ, hCχ_nonneg, hCχ⟩ :=
    (SCV.smoothCutoff_complex_hasTemperateGrowth).norm_iteratedFDeriv_le_uniform r
  obtain ⟨A, hA_nonneg, hA⟩ :=
    exists_scaled_reducedAdjacentEdgeQuadratic_argument_iteratedFDeriv_bound_on_compact
      (d := d) i hi hK r
  let P : ℕ := kχ + r
  let B : ℝ := (r.factorial : ℝ) * Cχ * (A + 1) ^ P
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, P, hB_nonneg, ?_⟩
  intro N ξ hξ
  let Q : NPointDomain d m → ℝ := reducedAdjacentEdgeQuadratic d m i hi
  let arg : NPointDomain d m → ℝ :=
    fun ξ => ((2 * (N + 1) : ℝ) * Q ξ) - 2
  let D : ℝ := (A + 1) * (N + 1 : ℝ)
  have hN1_nonneg : 0 ≤ (N + 1 : ℝ) := by positivity
  have hN1_ge_one : (1 : ℝ) ≤ N + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hD_ge_one : 1 ≤ D := by
    dsimp [D]
    nlinarith [hA_nonneg, hN1_ge_one]
  have hQ_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) Q :=
    (reducedAdjacentEdgeQuadratic_hasTemperateGrowth
      (d := d) m i hi).1
  have harg_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) arg := by
    dsimp [arg]
    simpa [Q, smul_eq_mul] using
      ((hQ_smooth.const_smul (2 * (N + 1) : ℝ)).sub contDiff_const)
  have hχ_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ := by
    simpa [χ] using
      (Complex.ofRealCLM.contDiff.comp SCV.smoothCutoff_contDiff)
  have harg0 : ‖arg ξ‖ ≤ A * (N + 1 : ℝ) := by
    simpa [arg, Q, norm_iteratedFDeriv_zero] using
      hA N 0 (Nat.zero_le r) ξ hξ
  have hCcomp :
      ∀ j, j ≤ r → ‖iteratedFDeriv ℝ j χ (arg ξ)‖ ≤ Cχ * D ^ kχ := by
    intro j hj
    have hbase := hCχ j hj (arg ξ)
    have harg_le_D : 1 + ‖arg ξ‖ ≤ D := by
      dsimp [D]
      rw [Real.norm_eq_abs] at harg0
      nlinarith [harg0, hN1_ge_one]
    have hpow :
        (1 + ‖arg ξ‖) ^ kχ ≤ D ^ kχ := by
      exact pow_le_pow_left₀ (by positivity) harg_le_D _
    exact hbase.trans (mul_le_mul_of_nonneg_left hpow hCχ_nonneg)
  have hDcomp :
      ∀ j, 1 ≤ j → j ≤ r → ‖iteratedFDeriv ℝ j arg ξ‖ ≤ D ^ j := by
    intro j hj_pos hj
    have hargj : ‖iteratedFDeriv ℝ j arg ξ‖ ≤ A * (N + 1 : ℝ) := by
      simpa [arg, Q] using hA N j hj ξ hξ
    have hlin_le_D : A * (N + 1 : ℝ) ≤ D := by
      dsimp [D]
      nlinarith [hA_nonneg, hN1_nonneg]
    have hj_ne : j ≠ 0 := by omega
    exact hargj.trans (hlin_le_D.trans (le_self_pow₀ hD_ge_one hj_ne))
  have hcomp :
      ‖iteratedFDeriv ℝ r (χ ∘ arg) ξ‖ ≤
        (r.factorial : ℝ) * (Cχ * D ^ kχ) * D ^ r := by
    exact norm_iteratedFDeriv_comp_le
      (𝕜 := ℝ) (g := χ) (f := arg) (n := r)
      (N := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      hχ_smooth harg_smooth (by exact_mod_cast le_top) ξ hCcomp hDcomp
  calc
    ‖iteratedFDeriv ℝ r
        (reducedAdjacentEdgeInteriorCutoff d m i hi N) ξ‖ =
        ‖iteratedFDeriv ℝ r (χ ∘ arg) ξ‖ := by
          have hfun :
              reducedAdjacentEdgeInteriorCutoff d m i hi N = χ ∘ arg := by
            funext η
            simp [reducedAdjacentEdgeInteriorCutoff, χ, arg, Q]
          rw [hfun]
    _ ≤ (r.factorial : ℝ) * (Cχ * D ^ kχ) * D ^ r := hcomp
    _ = B * (N + 1 : ℝ) ^ P := by
      simp [B, D, P, pow_add, mul_pow]
      ring

omit [NeZero d] in
/-- The norm of an iterated derivative of an iterated derivative is the norm
of the corresponding total iterated Frechet derivative.  This lets the
boundary-flatness Taylor estimate apply directly to derivative-valued maps. -/
theorem norm_iteratedFDeriv_iteratedFDeriv_npoint
    {m : ℕ} (f : NPointDomain d m → ℂ)
    (r s : ℕ) (x : NPointDomain d m) :
    ‖iteratedFDeriv ℝ s (iteratedFDeriv ℝ r f) x‖ =
      ‖iteratedFDeriv ℝ (r + s) f x‖ := by
  induction s generalizing r with
  | zero =>
      simp [norm_iteratedFDeriv_zero]
  | succ s ih =>
      rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
        (f := iteratedFDeriv ℝ r f) (n := s) (x := x)]
      rw [fderiv_iteratedFDeriv]
      rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      have hnat : r + (s + 1) = r + 1 + s := by omega
      rw [hnat]
      exact ih (r + 1)

omit [NeZero d] in
/-- Quantitative Taylor flatness for a smooth map, stated with an explicit
uniform bound on the next derivative.  This is the derivative-valued form of
the Jost/Vladimirov boundary annihilation estimate. -/
theorem norm_le_infDist_pow_of_flat_on_closed_of_uniform_iteratedFDeriv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS_closed : IsClosed S) (hS_nonempty : S.Nonempty)
    {f : E → F}
    (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hflat : ∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k f y = 0)
    (m : ℕ) {A : ℝ} (hA_nonneg : 0 ≤ A)
    (hA : ∀ x : E, ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ A) :
    ∀ x : E, ‖f x‖ ≤
      (A / (((Nat.factorial m : ℕ) : ℝ))) * Metric.infDist x S ^ (m + 1) := by
  intro x
  obtain ⟨y, hyS, hyDist⟩ := hS_closed.exists_infDist_eq_dist hS_nonempty x
  let v : E := x - y
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → F := (fun z : E => f (z + y)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : E => f (z + y)) :=
    fun r => by
      simpa using (hf_smooth.of_le (by exact_mod_cast le_top)).comp
        (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : E => f (z + y))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : E => f (z + y))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k f (L 0 + y) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hflat k y hyS
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          A * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hL : ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simp [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul, mul_comm]
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : E => f (z + y))
            (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : E => f (z + y))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) f (L t + y)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) f (L t + y)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ A * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
          exact hA (L t + y)
      _ = A * ‖L‖ ^ (m + 1) := by simp
      _ ≤ A * ‖v‖ ^ (m + 1) := by
          gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := A * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hg_one : g 1 = f x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg,
      add_comm, add_left_comm]
  have hv_dist : ‖v‖ = Metric.infDist x S := by
    rw [hyDist, dist_eq_norm]
  calc
    ‖f x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ (A * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
      simpa [hTaylor_zero] using hrem
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) := by
      field_simp [Nat.cast_ne_zero]
      ring
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * Metric.infDist x S ^ (m + 1) := by
      rw [hv_dist]

omit [NeZero d] in
/-- Quantitative flatness in distance-to-a-closed-set form.  This is the
Taylor-remainder estimate used in the public-support handoff: if a Schwartz map
is flat to all orders on a closed set, then it is bounded by any prescribed
power of the distance to that set. -/
theorem schwartz_norm_le_infDist_pow_of_flat_on_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS_closed : IsClosed S) (hS_nonempty : S.Nonempty)
    (f : SchwartzMap E F)
    (hflat : ∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k (f : E → F) y = 0)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E, ‖f x‖ ≤ C * Metric.infDist x S ^ (m + 1) := by
  classical
  let sem : ℝ := SchwartzMap.seminorm ℝ 0 (m + 1) f
  let C : ℝ := sem / (((Nat.factorial m : ℕ) : ℝ))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, sem]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  obtain ⟨y, hyS, hyDist⟩ := hS_closed.exists_infDist_eq_dist hS_nonempty x
  let v : E := x - y
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → F := (fun z : E => (f : E → F) (z + y)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : E => (f : E → F) (z + y)) :=
    fun r => by
      simpa using (f.smooth r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : E => (f : E → F) (z + y))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : E => (f : E → F) (z + y))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k (f : E → F) (L 0 + y) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hflat k y hyS
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          sem * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hsem_bound :
        ‖iteratedFDeriv ℝ (m + 1) (f : E → F) (L t + y)‖ ≤ sem := by
      simpa [sem] using
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f (m + 1) (L t + y))
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simp [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul, mul_comm]
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : E => (f : E → F) (z + y))
            (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : E => (f : E → F) (z + y))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (f : E → F) (L t + y)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) (f : E → F) (L t + y)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ sem * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
      _ = sem * ‖L‖ ^ (m + 1) := by simp
      _ ≤ sem * ‖v‖ ^ (m + 1) := by
          gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := sem * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hg_one : g 1 = f x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg,
      add_comm, add_left_comm]
  have hv_dist : ‖v‖ = Metric.infDist x S := by
    rw [hyDist, dist_eq_norm]
  calc
    ‖f x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ (sem * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
      simpa [hTaylor_zero] using hrem
    _ = C * ‖v‖ ^ (m + 1) := by
      simp [C]
      ring
    _ = C * Metric.infDist x S ^ (m + 1) := by
      rw [hv_dist]

/-- A public test supported in the adjacent reduced spacelike edge is bounded by
an arbitrary power of its distance to the closed edge complement.  This is the
first quantitative form of the Jost/Vladimirov boundary-flatness step. -/
theorem exists_reducedSpacelikeSwapEdge_publicSupport_norm_le_infDist_compl_pow
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : NPointDomain d m,
        ‖φ ξ‖ ≤
          C *
            Metric.infDist ξ
              ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^
              (p + 1) := by
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hUopen : IsOpen U :=
    isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hS_nonempty : (Uᶜ).Nonempty := by
    refine ⟨0, ?_⟩
    intro hU0
    rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hU0
    change 0 < MinkowskiSpace.minkowskiNormSq d (0 : Fin (d + 1) → ℝ) at hU0
    simp [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner] at hU0
  simpa [U] using
    schwartz_norm_le_infDist_pow_of_flat_on_closed
      (hS_closed := hUopen.isClosed_compl)
      (hS_nonempty := hS_nonempty)
      (f := φ)
      (hflat := fun k y hy =>
        reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_compl
          (d := d) m i hi φ hφ_support (by simpa [U] using hy) k)
      p

/-- The public-support flatness bound can be read directly in terms of the
Minkowski quadratic defining the adjacent reduced spacelike edge. -/
theorem exists_reducedSpacelikeSwapEdge_publicSupport_norm_le_sqrt_quadratic_pow
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : NPointDomain d m,
        ‖φ ξ‖ ≤
          C *
            (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
              (p + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_reducedSpacelikeSwapEdge_publicSupport_norm_le_infDist_compl_pow
      (d := d) m i hi φ hφ_support p
  refine ⟨C, hC_nonneg, ?_⟩
  intro ξ
  have hdist :=
    reducedAdjacentEdge_infDist_compl_le_sqrt_quadratic (d := d) m i hi ξ
  have hpow :
      Metric.infDist ξ
          ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^ (p + 1) ≤
        (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
          (p + 1) := by
    exact pow_le_pow_left₀ Metric.infDist_nonneg hdist _
  calc
    ‖φ ξ‖ ≤
        C *
          Metric.infDist ξ
            ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^
            (p + 1) := hC ξ
    _ ≤
        C *
          (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
            (p + 1) := by
      exact mul_le_mul_of_nonneg_left hpow hC_nonneg

/-- Public support gives the same quantitative flatness rate for every fixed
Frechet derivative, measured by distance to the closed edge complement.  This
is the derivative half of the strict-inside cutoff exhaustion estimate. -/
theorem exists_reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_norm_le_infDist_compl_pow
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (r p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : NPointDomain d m,
        ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ ≤
          C *
            Metric.infDist ξ
              ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^
              (p + 1) := by
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  let A : ℝ := SchwartzMap.seminorm ℝ 0 (r + (p + 1)) φ
  refine ⟨A / (((Nat.factorial p : ℕ) : ℝ)), by positivity, ?_⟩
  have hUopen : IsOpen U :=
    isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hS_nonempty_actual :
      ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ).Nonempty := by
    refine ⟨0, ?_⟩
    intro hU0
    rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hU0
    change 0 < MinkowskiSpace.minkowskiNormSq d (0 : Fin (d + 1) → ℝ) at hU0
    simp [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner] at hU0
  have hS_nonempty : (Uᶜ).Nonempty := by
    simpa [U] using hS_nonempty_actual
  have hH_smooth :
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ)) := by
    refine φ.smooth'.iteratedFDeriv_right
      (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (i := r) ?_
    change (↑((⊤ : ℕ∞) + (r : ℕ∞)) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    simp [top_add]
  have hflatH :
      ∀ k : ℕ, ∀ y ∈ Uᶜ,
        iteratedFDeriv ℝ k
          (iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ)) y = 0 := by
    intro k y hy
    have hzero :
        iteratedFDeriv ℝ (r + k) (φ : NPointDomain d m → ℂ) y = 0 :=
      reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_zero_on_compl
        (d := d) m i hi φ hφ_support (by simpa [U] using hy) (r + k)
    have hnorm_zero :
        ‖iteratedFDeriv ℝ k
            (iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ)) y‖ = 0 := by
      rw [norm_iteratedFDeriv_iteratedFDeriv_npoint]
      simp [hzero]
    exact norm_eq_zero.mp hnorm_zero
  have hA_bound :
      ∀ ξ : NPointDomain d m,
        ‖iteratedFDeriv ℝ (p + 1)
            (iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ)) ξ‖ ≤ A := by
    intro ξ
    rw [norm_iteratedFDeriv_iteratedFDeriv_npoint]
    simpa [A, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ (r + (p + 1)) ξ)
  intro ξ
  simpa [U, A] using
    norm_le_infDist_pow_of_flat_on_closed_of_uniform_iteratedFDeriv_bound
      (hS_closed := hUopen.isClosed_compl)
      (hS_nonempty := hS_nonempty)
      (f := iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ))
      hH_smooth hflatH p (by positivity) hA_bound ξ

/-- The derivative flatness rate can be read directly in terms of the adjacent
Minkowski quadratic. -/
theorem exists_reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_norm_le_sqrt_quadratic_pow
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (r p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : NPointDomain d m,
        ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ ≤
          C *
            (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
              (p + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_norm_le_infDist_compl_pow
      (d := d) m i hi φ hφ_support r p
  refine ⟨C, hC_nonneg, ?_⟩
  intro ξ
  have hdist :=
    reducedAdjacentEdge_infDist_compl_le_sqrt_quadratic (d := d) m i hi ξ
  have hpow :
      Metric.infDist ξ
          ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^ (p + 1) ≤
        (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
          (p + 1) := by
    exact pow_le_pow_left₀ Metric.infDist_nonneg hdist _
  calc
    ‖iteratedFDeriv ℝ r (φ : NPointDomain d m → ℂ) ξ‖ ≤
        C *
          Metric.infDist ξ
            ((reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ) ^
            (p + 1) := hC ξ
    _ ≤
        C *
          (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
            (p + 1) := by
      exact mul_le_mul_of_nonneg_left hpow hC_nonneg

private theorem collar_quadratic_pow_decay_le_inv
    (N P : ℕ) {Q : ℝ} (hQ_nonneg : 0 ≤ Q)
    (hcollar : (N + 1 : ℝ) * Q ≤ 1) :
    (N + 1 : ℝ) ^ P * Q ^ (P + 1) ≤ (N + 1 : ℝ)⁻¹ := by
  let a : ℝ := N + 1
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have hprod_nonneg : 0 ≤ a * Q := mul_nonneg ha_nonneg hQ_nonneg
  have hpow_prod : (a * Q) ^ (P + 1) ≤ 1 := by
    exact pow_le_one₀ hprod_nonneg (by simpa [a] using hcollar)
  have hrewrite : a ^ P * Q ^ (P + 1) = (a * Q) ^ (P + 1) * a⁻¹ := by
    rw [mul_pow, pow_succ']
    field_simp [ne_of_gt ha_pos]
    ring
  rw [hrewrite]
  simpa [a] using
    mul_le_mul_of_nonneg_right hpow_prod (inv_nonneg.mpr ha_nonneg)

private theorem collar_sqrt_quadratic_pow_decay_le_inv
    (N P : ℕ) {Q : ℝ} (hQ_pos : 0 < Q)
    (hcollar : (N + 1 : ℝ) * Q ≤ 1) :
    (N + 1 : ℝ) ^ P *
        (Real.sqrt (max Q 0)) ^ (2 * (P + 1)) ≤
      (N + 1 : ℝ)⁻¹ := by
  have hQ_nonneg : 0 ≤ Q := le_of_lt hQ_pos
  have hsqrt_pow :
      (Real.sqrt (max Q 0)) ^ (2 * (P + 1)) = Q ^ (P + 1) := by
    rw [max_eq_left hQ_nonneg]
    rw [pow_mul]
    simp [Real.sq_sqrt hQ_nonneg]
  rw [hsqrt_pow]
  exact collar_quadratic_pow_decay_le_inv
    (N := N) (P := P) hQ_nonneg hcollar

omit [NeZero d] in
theorem exists_one_sub_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_bound_on_compact
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {K : Set (NPointDomain d m)} (hK : IsCompact K) (r : ℕ) :
    ∃ (B : ℝ) (P : ℕ), 0 ≤ B ∧
      ∀ (N : ℕ) (ξ : NPointDomain d m), ξ ∈ K →
        ‖iteratedFDeriv ℝ r
          (fun η : NPointDomain d m =>
            (1 : ℂ) - reducedAdjacentEdgeInteriorCutoff d m i hi N η) ξ‖ ≤
          B * (N + 1 : ℝ) ^ P := by
  classical
  obtain ⟨B, P, hB_nonneg, hB⟩ :=
    exists_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_bound_on_compact
      (d := d) i hi hK r
  refine ⟨B + 1, P + 1, by positivity, ?_⟩
  intro N ξ hξ
  let cut : NPointDomain d m → ℂ :=
    reducedAdjacentEdgeInteriorCutoff d m i hi N
  have hN1_ge_one : (1 : ℝ) ≤ N + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hpow_le :
      (N + 1 : ℝ) ^ P ≤ (N + 1 : ℝ) ^ (P + 1) :=
    pow_le_pow_right₀ hN1_ge_one (Nat.le_succ P)
  have hone_le_pow : (1 : ℝ) ≤ (N + 1 : ℝ) ^ (P + 1) :=
    one_le_pow₀ hN1_ge_one
  have hpow_nonneg : 0 ≤ (N + 1 : ℝ) ^ (P + 1) := by positivity
  by_cases hr : r = 0
  · subst r
    rw [norm_iteratedFDeriv_zero]
    have hcut_bound :
        ‖cut ξ‖ ≤ B * (N + 1 : ℝ) ^ P := by
      simpa [cut] using hB N ξ hξ
    calc
      ‖(1 : ℂ) - cut ξ‖ ≤ ‖(1 : ℂ)‖ + ‖cut ξ‖ := norm_sub_le _ _
      _ = 1 + ‖cut ξ‖ := by simp
      _ ≤ 1 + B * (N + 1 : ℝ) ^ P := by
        gcongr
      _ ≤ (B + 1) * (N + 1 : ℝ) ^ (P + 1) := by
        nlinarith [hB_nonneg, hpow_le, hone_le_pow, hpow_nonneg]
  · have hcut_smooth :
        ContDiff ℝ (↑(⊤ : ℕ∞)) cut :=
      (reducedAdjacentEdgeInteriorCutoff_hasTemperateGrowth
        (d := d) m i hi N).1
    have hsub :
        iteratedFDeriv ℝ r
            (fun η : NPointDomain d m => (1 : ℂ) - cut η) ξ =
          iteratedFDeriv ℝ r (fun _ : NPointDomain d m => (1 : ℂ)) ξ -
            iteratedFDeriv ℝ r cut ξ := by
      exact iteratedFDeriv_sub_apply
        (contDiff_const.contDiffAt)
        ((hcut_smooth.of_le (by exact_mod_cast le_top)).contDiffAt)
    have hconst :
        iteratedFDeriv ℝ r (fun _ : NPointDomain d m => (1 : ℂ)) ξ = 0 := by
      simpa using
        congrFun
          (iteratedFDeriv_const_of_ne
            (𝕜 := ℝ) (E := NPointDomain d m) hr (1 : ℂ)) ξ
    rw [hsub, hconst, zero_sub, norm_neg]
    calc
      ‖iteratedFDeriv ℝ r cut ξ‖ ≤ B * (N + 1 : ℝ) ^ P := by
        simpa [cut] using hB N ξ hξ
      _ ≤ (B + 1) * (N + 1 : ℝ) ^ (P + 1) := by
        nlinarith [hB_nonneg, hpow_le, hpow_nonneg]

theorem one_sub_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_norm_product_collar
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (N r s : ℕ) (φ : SchwartzNPoint d m) (ξ : NPointDomain d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (hprod :
      ‖iteratedFDeriv ℝ r
          (fun η : NPointDomain d m =>
            (1 : ℂ) - reducedAdjacentEdgeInteriorCutoff d m i hi N η) ξ‖ *
        ‖iteratedFDeriv ℝ s (φ : NPointDomain d m → ℂ) ξ‖ ≠ 0) :
    ξ ∈
      {ξ | 0 < reducedAdjacentEdgeQuadratic d m i hi ξ ∧
        (N + 1 : ℝ) * reducedAdjacentEdgeQuadratic d m i hi ξ ≤ 1} := by
  classical
  let cut : NPointDomain d m → ℂ :=
    reducedAdjacentEdgeInteriorCutoff d m i hi N
  have hone_norm_ne :
      ‖iteratedFDeriv ℝ r
          (fun η : NPointDomain d m => (1 : ℂ) - cut η) ξ‖ ≠ 0 := by
    intro hzero
    exact hprod (by simp [cut, hzero])
  have hφ_norm_ne :
      ‖iteratedFDeriv ℝ s (φ : NPointDomain d m → ℂ) ξ‖ ≠ 0 := by
    intro hzero
    exact hprod (by simp [hzero])
  by_cases hr : r = 0
  · subst r
    have hone_ne : (1 : ℂ) - cut ξ ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simpa [iteratedFDeriv_zero_apply] using hone_norm_ne)
    have hD_ne :
        iteratedFDeriv ℝ s (φ : NPointDomain d m → ℂ) ξ ≠ 0 :=
      norm_ne_zero_iff.mp hφ_norm_ne
    have hbase :
        ξ ∈ Function.support
          (fun ξ : NPointDomain d m =>
            (1 - reducedAdjacentEdgeInteriorCutoff d m i hi N ξ) •
              iteratedFDeriv ℝ s (φ : NPointDomain d m → ℂ) ξ) := by
      simpa [Function.mem_support, cut] using smul_ne_zero hone_ne hD_ne
    exact (one_sub_reducedAdjacentEdgeInteriorCutoff_mul_iteratedFDeriv_support_subset_collar
      (d := d) i hi N s φ hφ_support hbase
      |>.imp_right le_of_lt)
  · obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    have hone_sub_ne :
        iteratedFDeriv ℝ (r' + 1)
            (fun η : NPointDomain d m => (1 : ℂ) - cut η) ξ ≠ 0 := by
      exact norm_ne_zero_iff.mp hone_norm_ne
    have hcut_smooth :
        ContDiff ℝ (↑(⊤ : ℕ∞)) cut :=
      (reducedAdjacentEdgeInteriorCutoff_hasTemperateGrowth
        (d := d) m i hi N).1
    have hsub :
        iteratedFDeriv ℝ (r' + 1)
            (fun η : NPointDomain d m => (1 : ℂ) - cut η) ξ =
          iteratedFDeriv ℝ (r' + 1) (fun _ : NPointDomain d m => (1 : ℂ)) ξ -
            iteratedFDeriv ℝ (r' + 1) cut ξ := by
      exact iteratedFDeriv_sub_apply
        (contDiff_const.contDiffAt)
        ((hcut_smooth.of_le (by exact_mod_cast le_top)).contDiffAt)
    have hconst :
        iteratedFDeriv ℝ (r' + 1)
            (fun _ : NPointDomain d m => (1 : ℂ)) ξ = 0 := by
      simpa using
        congrFun
          (iteratedFDeriv_const_of_ne
            (𝕜 := ℝ) (E := NPointDomain d m) (by omega) (1 : ℂ)) ξ
    have hcut_ne : iteratedFDeriv ℝ (r' + 1) cut ξ ≠ 0 := by
      intro hcut_zero
      exact hone_sub_ne (by simp [hsub, hconst, hcut_zero])
    exact
      reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_succ_support_subset_collar
        (d := d) i hi N r' (by simpa [Function.mem_support, cut] using hcut_ne)

omit [NeZero d] in
private theorem exists_norm_pow_bound_on_tsupport_of_hasCompactSupport
    {m : ℕ} (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ)) (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ), ‖ξ‖ ^ k ≤ R := by
  have hK : IsCompact (tsupport (φ : NPointDomain d m → ℂ)) := by
    simpa [HasCompactSupport] using hφ_compact
  have hcont : Continuous (fun ξ : NPointDomain d m => ‖ξ‖ ^ k) :=
    continuous_norm.pow k
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max R 0, le_max_right R 0, ?_⟩
  intro ξ hξ
  have hnorm := hR ξ hξ
  have hnonneg : 0 ≤ ‖ξ‖ ^ k := pow_nonneg (norm_nonneg ξ) k
  have hleR : ‖ξ‖ ^ k ≤ R := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm
  exact hleR.trans (le_max_left R 0)

private theorem cutoff_error_leibniz_term_le_inv
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (k n j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ξ : NPointDomain d m),
      ‖ξ‖ ^ k *
          ((n.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j
              (fun η : NPointDomain d m =>
                (1 : ℂ) - reducedAdjacentEdgeInteriorCutoff d m i hi N η) ξ‖ *
            ‖iteratedFDeriv ℝ (n - j) (φ : NPointDomain d m → ℂ) ξ‖) ≤
        C * (N + 1 : ℝ)⁻¹ := by
  classical
  have hK_compact : IsCompact (tsupport (φ : NPointDomain d m → ℂ)) := by
    simpa [HasCompactSupport] using hφ_compact
  obtain ⟨R, hR_nonneg, hR⟩ :=
    exists_norm_pow_bound_on_tsupport_of_hasCompactSupport
      (d := d) φ hφ_compact k
  obtain ⟨B, P, hB_nonneg, hB⟩ :=
    exists_one_sub_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_bound_on_compact
      (d := d) i hi hK_compact j
  let pflat : ℕ := 2 * (P + 1) - 1
  have hpflat_succ : pflat + 1 = 2 * (P + 1) := by
    dsimp [pflat]
    omega
  obtain ⟨A, hA_nonneg, hA⟩ :=
    exists_reducedSpacelikeSwapEdge_publicSupport_iteratedFDeriv_norm_le_sqrt_quadratic_pow
      (d := d) m i hi φ hφ_support (n - j) pflat
  let C : ℝ := R * (n.choose j : ℝ) * B * A
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro N ξ
  let cutOne : NPointDomain d m → ℂ :=
    fun η => (1 : ℂ) - reducedAdjacentEdgeInteriorCutoff d m i hi N η
  let cutNorm : ℝ := ‖iteratedFDeriv ℝ j cutOne ξ‖
  let phiNorm : ℝ :=
    ‖iteratedFDeriv ℝ (n - j) (φ : NPointDomain d m → ℂ) ξ‖
  by_cases hprod_zero : cutNorm * phiNorm = 0
  · calc
      ‖ξ‖ ^ k * ((n.choose j : ℝ) * cutNorm * phiNorm) =
          ‖ξ‖ ^ k * (n.choose j : ℝ) * (cutNorm * phiNorm) := by ring
      _ = 0 := by rw [hprod_zero]; ring
      _ ≤ C * (N + 1 : ℝ)⁻¹ := by positivity
  · have hcollar :=
      one_sub_reducedAdjacentEdgeInteriorCutoff_iteratedFDeriv_norm_product_collar
        (d := d) i hi N j (n - j) φ ξ hφ_support (by
          change cutNorm * phiNorm ≠ 0
          exact hprod_zero)
    have hphiNorm_ne : phiNorm ≠ 0 := by
      intro hzero
      exact hprod_zero (by simp [hzero])
    have hD_ne :
        iteratedFDeriv ℝ (n - j) (φ : NPointDomain d m → ℂ) ξ ≠ 0 :=
      norm_ne_zero_iff.mp hphiNorm_ne
    have hξ_ts : ξ ∈ tsupport (φ : NPointDomain d m → ℂ) := by
      exact support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n - j)
        (by simpa [Function.mem_support] using hD_ne)
    have hcut_bound : cutNorm ≤ B * (N + 1 : ℝ) ^ P := by
      simpa [cutOne, cutNorm] using hB N ξ hξ_ts
    have hphi_bound :
        phiNorm ≤
          A *
            (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
              (2 * (P + 1)) := by
      have hraw := hA ξ
      simpa [phiNorm, hpflat_succ] using hraw
    have hrate :
        (N + 1 : ℝ) ^ P *
            (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
              (2 * (P + 1)) ≤
          (N + 1 : ℝ)⁻¹ :=
      collar_sqrt_quadratic_pow_decay_le_inv
        (N := N) (P := P) hcollar.1 hcollar.2
    calc
      ‖ξ‖ ^ k * ((n.choose j : ℝ) * cutNorm * phiNorm) ≤
          R * ((n.choose j : ℝ) *
            (B * (N + 1 : ℝ) ^ P) *
            (A *
              (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
                (2 * (P + 1)))) := by
        gcongr
        exact hR ξ hξ_ts
      _ = C *
          ((N + 1 : ℝ) ^ P *
            (Real.sqrt (max (reducedAdjacentEdgeQuadratic d m i hi ξ) 0)) ^
              (2 * (P + 1))) := by
        simp [C]
        ring
      _ ≤ C * (N + 1 : ℝ)⁻¹ := by
        gcongr

theorem reducedAdjacentEdgeInteriorCutoffCLM_error_seminorm_le_inv
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      SchwartzMap.seminorm ℝ k n
          (φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ) ≤
        C * (N + 1 : ℝ)⁻¹ := by
  classical
  choose C hC_nonneg hC_bound using
    fun j : ℕ =>
      cutoff_error_leibniz_term_le_inv
        (d := d) i hi φ hφ_compact hφ_support k n j
  let Ctot : ℝ := ∑ j ∈ Finset.range (n + 1), C j
  have hCtot_nonneg : 0 ≤ Ctot := by
    dsimp [Ctot]
    exact Finset.sum_nonneg fun j _ => hC_nonneg j
  refine ⟨Ctot, hCtot_nonneg, ?_⟩
  intro N
  apply SchwartzMap.seminorm_le_bound ℝ k n
    (φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ)
    (M := Ctot * (N + 1 : ℝ)⁻¹)
    (mul_nonneg hCtot_nonneg (inv_nonneg.mpr (by positivity)))
  intro ξ
  let cut : NPointDomain d m → ℂ :=
    reducedAdjacentEdgeInteriorCutoff d m i hi N
  let cutOne : NPointDomain d m → ℂ := fun η => (1 : ℂ) - cut η
  have hfun :
      ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
        SchwartzNPoint d m) : NPointDomain d m → ℂ) =
        fun η => cutOne η * φ η := by
    funext η
    simp [cutOne, cut, reducedAdjacentEdgeInteriorCutoffCLM_apply]
    ring
  have hcut_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutOne := by
    dsimp [cutOne, cut]
    exact contDiff_const.sub
      (reducedAdjacentEdgeInteriorCutoff_hasTemperateGrowth
        (d := d) m i hi N).1
  have hLeib :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℂ) (n := n)
      (f := cutOne) (g := (φ : NPointDomain d m → ℂ))
      hcut_smooth φ.smooth' ξ
      (by exact_mod_cast le_top)
  calc
    ‖ξ‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ :
            SchwartzNPoint d m) : NPointDomain d m → ℂ)) ξ‖
        = ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun η => cutOne η * φ η) ξ‖ := by
            rw [hfun]
    _ ≤
        ‖ξ‖ ^ k *
          ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j cutOne ξ‖ *
              ‖iteratedFDeriv ℝ (n - j)
                (φ : NPointDomain d m → ℂ) ξ‖ := by
      gcongr
      exact hLeib
    _ =
        ∑ j ∈ Finset.range (n + 1),
          ‖ξ‖ ^ k *
            ((n.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j cutOne ξ‖ *
              ‖iteratedFDeriv ℝ (n - j)
                (φ : NPointDomain d m → ℂ) ξ‖) := by
      rw [Finset.mul_sum]
    _ ≤
        ∑ j ∈ Finset.range (n + 1), C j * (N + 1 : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun j _ => by
        simpa [cutOne, cut] using hC_bound j N ξ
    _ = Ctot * (N + 1 : ℝ)⁻¹ := by
      simp [Ctot, Finset.sum_mul]

theorem reducedAdjacentEdgeInteriorCutoffCLM_error_tendsto_zero
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun N : ℕ =>
        φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ)
      Filter.atTop (nhds 0) := by
  rw [(schwartz_withSeminorms ℝ (NPointDomain d m) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  obtain ⟨k, n⟩ := p
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    reducedAdjacentEdgeInteriorCutoffCLM_error_seminorm_le_inv
      (d := d) i hi φ hφ_compact hφ_support k n
  have hplus :
      Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv :
      Filter.Tendsto (fun N : ℕ => (((N : ℝ) + 1)⁻¹ : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hplus
  have hlim :
      Filter.Tendsto (fun N : ℕ => C * (((N : ℝ) + 1)⁻¹ : ℝ))
        Filter.atTop (nhds 0) :=
    by simpa using tendsto_const_nhds.mul hinv
  have htarget_mem : {x : ℝ | x < ε} ∈ nhds (0 : ℝ) := by
    exact (isOpen_lt continuous_id continuous_const).mem_nhds hε
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hlim htarget_mem)
  refine ⟨N0, ?_⟩
  intro N hN
  have hsmall : C * (((N : ℝ) + 1)⁻¹ : ℝ) < ε := hN0 N hN
  have hbound := hC_bound N
  show schwartzSeminormFamily ℝ (NPointDomain d m) ℂ (k, n)
      ((φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ) - 0) < ε
  rw [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  exact lt_of_le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using hbound) hsmall

theorem reducedAdjacentEdgeInteriorCutoffCLM_tendsto
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun N : ℕ =>
        reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ)
      Filter.atTop (nhds φ) := by
  have herror :=
    reducedAdjacentEdgeInteriorCutoffCLM_error_tendsto_zero
      (d := d) i hi φ hφ_compact hφ_support
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          φ - (φ - reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ))
        Filter.atTop (nhds (φ - 0)) :=
    tendsto_const_nhds.sub herror
  simpa using hsub

theorem reducedSpacelikeSwapEdge_strictTSupport_exhaustion_of_publicSupport
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    ∃ φN : ℕ → SchwartzNPoint d m,
      (∀ N, HasCompactSupport (φN N : NPointDomain d m → ℂ)) ∧
      (∀ N,
        tsupport (φN N : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) ∧
      Filter.Tendsto φN Filter.atTop (nhds φ) := by
  refine
    ⟨fun N => reducedAdjacentEdgeInteriorCutoffCLM (d := d) m i hi N φ,
      ?_, ?_, ?_⟩
  · intro N
    exact
      reducedAdjacentEdgeInteriorCutoffCLM_hasCompactSupport
        (d := d) m i hi N φ hφ_compact
  · intro N
    exact
      reducedAdjacentEdgeInteriorCutoffCLM_tsupport_subset_edge
        (d := d) m i hi N φ
  · exact
      reducedAdjacentEdgeInteriorCutoffCLM_tendsto
        (d := d) i hi φ hφ_compact hφ_support

theorem reducedBoundaryCLM_invariant_of_closedSupportCanonicalInvariant_publicSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosed :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
        (d := d) OS lgc) :
    ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
      (φ : SchwartzNPoint d m),
      HasCompactSupport (φ : NPointDomain d m → ℂ) →
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m φ := by
  intro m i hi φ hφ_compact hφ_support
  obtain ⟨φN, hφN_compact, hφN_tsupport, hφN_tendsto⟩ :=
    reducedSpacelikeSwapEdge_strictTSupport_exhaustion_of_publicSupport
      (d := d) i hi φ hφ_compact hφ_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let P : SchwartzNPoint d m →L[ℂ] SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m τ)
  let L : SchwartzNPoint d m →L[ℂ] ℂ :=
    bvt_reducedWightmanCLM (d := d) OS lgc χ m
  have hpoint : ∀ N, L (P (φN N)) = L (φN N) := by
    intro N
    have hN :=
      reducedBoundaryCLM_invariant_of_closedSupportCanonicalInvariant
        (d := d) OS lgc χ hclosed m i hi (φN N)
        (hφN_compact N) (hφN_tsupport N)
    simpa [L, P, τ, j] using hN
  have hP_tendsto :
      Filter.Tendsto (fun N => P (φN N)) Filter.atTop (nhds (P φ)) :=
    (P.continuous.tendsto φ).comp hφN_tendsto
  have hleft :
      Filter.Tendsto (fun N => L (P (φN N))) Filter.atTop (nhds (L (P φ))) :=
    (L.continuous.tendsto (P φ)).comp hP_tendsto
  have hright :
      Filter.Tendsto (fun N => L (φN N)) Filter.atTop (nhds (L φ)) :=
    (L.continuous.tendsto φ).comp hφN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => L (P (φN N))) Filter.atTop (nhds (L φ)) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N => (hpoint N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_closedSupportCanonicalInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosed :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
        (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  exact
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_boundaryCLM_invariant
      (d := d) OS lgc χ
      (reducedBoundaryCLM_invariant_of_closedSupportCanonicalInvariant_publicSupport
        (d := d) OS lgc χ hclosed)

theorem bvt_W_swap_pairing_of_spacelike_from_closedSupportCanonicalInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosed :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
        (d := d) OS lgc) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    bvt_W_swap_pairing_of_spacelike_from_canonicalBoundaryInvariantSchwartz
      (d := d) OS lgc
      (reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_closedSupportCanonicalInvariant
        (d := d) OS lgc χ hclosed)

/-- Local reduced boundary-CLM invariance is enough for theorem-2 adjacent
locality.

This exposes the Path-2 last mile directly: Hdiff/source-representation
producers only need to build `ReducedLocalAdjacentBoundaryCLMInvariant`; the
closed-support canonical invariant and the boundary-value swap statement are
then obtained by the already checked support handoff. -/
theorem bvt_W_swap_pairing_of_spacelike_from_local_reducedBoundaryCLMInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocalCLM :
      ReducedLocalAdjacentBoundaryCLMInvariant (d := d) OS lgc χ) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    bvt_W_swap_pairing_of_spacelike_from_closedSupportCanonicalInvariant
      (d := d) OS lgc χ
      (reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_reducedBoundaryCLMInvariant
        (d := d) OS lgc χ hlocalCLM)

/-- Pointwise reduced-normal sign-flip convergence on the selected spacelike
collar is enough for theorem-2 locality.

This is the downstream surface matched to the OS-I source-transfer payload:
the remaining analytic theorem may prove the asymptotic sign-flip boundary
comparison directly, without first packaging exact ray representatives in
`ReducedNormalCanonicalRayEOWBranchDataOn`. -/
theorem bvt_W_swap_pairing_of_spacelike_from_pointwise_normalSignFlip
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hpoint :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ AdjacentNormal.reducedSelectedSpacelike
            (d := d) i ⟨i.val + 1, hi⟩ →
          Filter.Tendsto
            (fun ε : ℝ =>
              canonicalReducedBranch (d := d) OS lgc m ε
                  (AdjacentNormal.reducedCoordInv
                    (d := d) i ⟨i.val + 1, hi⟩
                    (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                    (AdjacentNormal.reducedSignFlip
                      (d := d) i ⟨i.val + 1, hi⟩ p)) -
                canonicalReducedBranch (d := d) OS lgc m ε
                  (AdjacentNormal.reducedCoordInv
                    (d := d) i ⟨i.val + 1, hi⟩
                    (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
            (nhds 0)) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  refine
    bvt_W_swap_pairing_of_spacelike_from_local_reducedBoundaryCLMInvariant
      (d := d) OS lgc χ ?_
  refine
    reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ ?_
  intro m i hi φ _hφ_compact hφ_tsupport ξ hξ
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let V : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i j
  refine
    ⟨V, by simpa [V] using isOpen_reducedSpacelikeSwapEdge (d := d) m i j,
      hφ_tsupport hξ, ?_⟩
  intro ψ _hψ_compact hψ_tsupport η hη
  have hη_ts :
      η ∈ tsupport (ψ : NPointDomain d m → ℂ) :=
    subset_tsupport (ψ : NPointDomain d m → ℂ)
      (Function.mem_support.mpr hη)
  have hη_edge :
      η ∈ reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [V] using hψ_tsupport hη_ts
  have hp :
      AdjacentNormal.reducedCoord (d := d) i j η ∈
        AdjacentNormal.reducedSelectedSpacelike (d := d) i j := by
    exact
      (AdjacentNormal.reducedCoord_mem_reducedSelectedSpacelike_iff
        (d := d) i j η).2 hη_edge
  simpa [j] using hpoint m i hi (AdjacentNormal.reducedCoord (d := d) i j η) hp

/-- Collar-local reduced-normal EOW branch data is the theorem-2 final-mile
input.

This is the corrected downstream surface for the OS-I Section 4.5
frozen-spectator producer: branch data on open reduced-normal collars gives
the local reduced boundary-CLM invariant, hence the closed-support canonical
swap invariant, and finally the adjacent locality statement for `bvt_W`. -/
theorem bvt_W_swap_pairing_of_spacelike_from_local_normalCanonicalRayEOWBranchDataOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                Nonempty
                  (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
                    (d := d) OS lgc i hi
                    (AdjacentNormal.reducedCoord
                      (d := d) i ⟨i.val + 1, hi⟩ η))) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    bvt_W_swap_pairing_of_spacelike_from_closedSupportCanonicalInvariant
      (d := d) OS lgc χ
      (reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_reducedBoundaryCLMInvariant
        (d := d) OS lgc χ
        (reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalCanonicalRayEOWBranchDataOn
          (d := d) OS lgc χ hbranchData))

/-- A pointwise reduced-normal EOW producer on the selected spacelike collar is
enough for theorem-2 locality.

This removes the support-local test-function bookkeeping from the remaining
analytic target: it suffices to construct
`ReducedNormalCanonicalRayEOWBranchDataOn` at every reduced normal point whose
selected coordinate is spacelike. -/
theorem bvt_W_swap_pairing_of_spacelike_from_pointwise_normalCanonicalRayEOWBranchDataOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hpoint :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ AdjacentNormal.reducedSelectedSpacelike
            (d := d) i ⟨i.val + 1, hi⟩ →
          Nonempty
            (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
              (d := d) OS lgc i hi p)) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  refine
    bvt_W_swap_pairing_of_spacelike_from_local_normalCanonicalRayEOWBranchDataOn
      (d := d) OS lgc χ ?_
  intro m i hi φ _hφ_compact hφ_tsupport ξ hξ
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let V : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i j
  refine
    ⟨V, by simpa [V] using isOpen_reducedSpacelikeSwapEdge (d := d) m i j,
      hφ_tsupport hξ, ?_⟩
  intro ψ _hψ_compact hψ_tsupport η hη
  have hη_ts :
      η ∈ tsupport (ψ : NPointDomain d m → ℂ) :=
    subset_tsupport (ψ : NPointDomain d m → ℂ)
      (Function.mem_support.mpr hη)
  have hη_edge :
      η ∈ reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [V] using hψ_tsupport hη_ts
  have hp :
      AdjacentNormal.reducedCoord (d := d) i j η ∈
        AdjacentNormal.reducedSelectedSpacelike (d := d) i j := by
    exact
      (AdjacentNormal.reducedCoord_mem_reducedSelectedSpacelike_iff
        (d := d) i j η).2 hη_edge
  exact hpoint m i hi (AdjacentNormal.reducedCoord (d := d) i j η) hp

/-- Closed-support reduced CLM invariance says exactly that the adjacent
swap-difference functional vanishes on the spacelike edge. -/
theorem reducedBoundaryCLMSwapDifference_isVanishingOn_edge_of_closedSupportInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosedInv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    Distribution.IsVanishingOn
      (reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi)
      (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) := by
  intro φ hφ_tsupport
  have h :=
    hclosedInv m i hi φ.toSchwartz φ.hasCompactSupport hφ_tsupport
  simpa [reducedBoundaryCLMSwapDifference, bvt_reducedWightmanCLM_apply] using
    sub_eq_zero.mpr h

/-- Closed-support reduced CLM invariance forces the adjacent swap-difference
functional's distributional support into the complement of the adjacent
spacelike edge.  This is the support-theoretic first half of the
Jost/Vladimirov finite-order public-support handoff. -/
theorem reducedBoundaryCLMSwapDifference_dsupport_subset_edge_compl_of_closedSupportInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosedInv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    Distribution.dsupport
        (reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi) ⊆
      (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)ᶜ := by
  exact
    DistributionSupport.dsupport_subset_compl_of_isVanishingOn
      (T := reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi)
      (reducedBoundaryCLMSwapDifference_isVanishingOn_edge_of_closedSupportInvariant
        (d := d) OS lgc χ hclosedInv m i hi)
      (isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)

/-- With only the public ordinary-support hypothesis, the possible
swap-difference defect is forced onto the frontier of the adjacent spacelike
edge.  This is the precise distribution-support locus for the remaining
finite-order boundary-annihilation step in the Jost/Vladimirov proof. -/
theorem reducedBoundaryCLMSwapDifference_publicSupport_inter_dsupport_subset_frontier_of_closedSupportInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosedInv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : CompactSchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    tsupport (φ : NPointDomain d m → ℂ) ∩
        Distribution.dsupport
          (reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi) ⊆
      frontier (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) := by
  let U : Set (NPointDomain d m) :=
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩
  have hφ_tsupport_closure :
      tsupport (φ : NPointDomain d m → ℂ) ⊆ closure U :=
    DistributionSupport.tsupport_subset_closure_of_support_subset
      (U := U) hφ_support
  have hdiff_dsupport_compl :
      Distribution.dsupport
          (reducedBoundaryCLMSwapDifference (d := d) OS lgc χ m i hi) ⊆ Uᶜ :=
    reducedBoundaryCLMSwapDifference_dsupport_subset_edge_compl_of_closedSupportInvariant
      (d := d) OS lgc χ hclosedInv m i hi
  intro x hx
  rw [(isOpen_reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩).frontier_eq]
  exact ⟨hφ_tsupport_closure hx.1, hdiff_dsupport_compl hx.2⟩

end OSReconstruction
