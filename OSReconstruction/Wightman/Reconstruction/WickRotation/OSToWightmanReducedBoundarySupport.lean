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

omit [NeZero d] in
/-- The Minkowski quadratic defining the adjacent reduced spacelike edge. -/
def reducedAdjacentEdgeQuadratic
    (d m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) : ℝ :=
  MinkowskiSpace.minkowskiNormSq d (ξ ⟨i.val, by omega⟩)

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
        ((Function.HasTemperateGrowth.const (MinkowskiSpace.metricSignature d μ)).mul hμ).mul hμ)
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
