import OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.Wightman.Reconstruction.WickRotation.OS45LocalOppositeWedge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity

noncomputable section

open Topology

namespace BHW

variable {d n : ℕ}

private theorem continuous_realEmbed :
    Continuous (realEmbed : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))

private theorem continuous_permNPoint (τ : Equiv.Perm (Fin n)) :
    Continuous (fun x : NPointDomain d n => fun k => x (τ k)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (τ k))

private theorem continuous_permComplexConfig (τ : Equiv.Perm (Fin n)) :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (τ k))

/-- The ordered positive-time region is open in the Euclidean configuration
space. -/
theorem isOpen_orderedPositiveTimeRegion :
    IsOpen (OrderedPositiveTimeRegion d n) := by
  suffices h :
      OrderedPositiveTimeRegion d n =
        (⋂ i : Fin n, {x : NPointDomain d n | 0 < x i 0}) ∩
          (⋂ i : Fin n, ⋂ j : Fin n,
            {x : NPointDomain d n | i < j → x i 0 < x j 0}) by
    rw [h]
    apply IsOpen.inter
    · exact isOpen_iInter_of_finite fun i => by
        have hcoord : Continuous (fun x : NPointDomain d n => x i 0) :=
          (continuous_apply 0).comp (continuous_apply i)
        exact isOpen_lt continuous_const hcoord
    · apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      by_cases hij : i < j
      · have hi : Continuous (fun x : NPointDomain d n => x i 0) :=
          (continuous_apply 0).comp (continuous_apply i)
        have hj : Continuous (fun x : NPointDomain d n => x j 0) :=
          (continuous_apply 0).comp (continuous_apply j)
        convert isOpen_lt hi hj using 1
        ext x
        simp [hij]
      · convert isOpen_univ using 1
        ext x
        simp [hij]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      exact (hx i).1
    · intro i j hij
      exact (hx i).2 j hij
  · rintro ⟨hx_pos, hx_lt⟩
    intro i
    exact ⟨hx_pos i, fun j hij => hx_lt i j hij⟩

/-- Each permuted ordered positive-time sector is open. -/
theorem isOpen_euclideanOrderedPositiveTimeSector
    (τ : Equiv.Perm (Fin n)) :
    IsOpen (EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) := by
  simpa [EuclideanOrderedPositiveTimeSector] using
    (isOpen_orderedPositiveTimeRegion (d := d) (n := n)).preimage
      (continuous_permNPoint (d := d) (n := n) τ)

private def adjacentTimePerturb
    (x : NPointDomain d n) (ε : ℝ) :
    NPointDomain d n :=
  fun k μ => if μ = 0 then x k 0 + ε * ((k : ℝ) + 1) else x k μ

@[simp] private theorem adjacentTimePerturb_zero
    (x : NPointDomain d n) :
    adjacentTimePerturb (d := d) (n := n) x 0 = x := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [adjacentTimePerturb]
  · simp [adjacentTimePerturb, hμ]

private theorem continuous_adjacentTimePerturb
    (x : NPointDomain d n) :
    Continuous (adjacentTimePerturb (d := d) (n := n) x) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [adjacentTimePerturb] using
      (continuous_const.add (continuous_id.mul continuous_const))
  · simpa [adjacentTimePerturb, hμ] using
      (continuous_const : Continuous fun ε : ℝ => x k μ)

private theorem adjacentTimePerturb_mem_identity_sector
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    {ε : ℝ} (hε_pos : 0 < ε) :
    adjacentTimePerturb (d := d) (n := n) x ε ∈
      EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) := by
  change adjacentTimePerturb (d := d) (n := n) x ε ∈ OrderedPositiveTimeRegion d n
  intro k
  constructor
  · have hk_pos : 0 < (k : ℝ) + 1 := by positivity
    have htarget : 0 < ε * ((k : ℝ) + 1) := mul_pos hε_pos hk_pos
    simpa [adjacentTimePerturb, hx_time0 k] using htarget
  · intro j hj
    have hk_lt_j : (k : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have hk1_lt_j1 : (k : ℝ) + 1 < (j : ℝ) + 1 := by linarith
    have htarget : ε * ((k : ℝ) + 1) < ε * ((j : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hk1_lt_j1 hε_pos
    simpa [adjacentTimePerturb, hx_time0 k, hx_time0 j] using htarget

/-- A sufficiently small positive time perturbation of a zero-time real point
inside an open adjacent overlap lands in the ordered positive-time sectors used
by the OS §4.5 adjacent-swap route. -/
theorem exists_ordered_small_time_perturb_in_adjacent_overlap
    (_hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (x : NPointDomain d n)
    (hxU : x ∈ U)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0) :
    ∃ (x0 : NPointDomain d n) (ρ : Equiv.Perm (Fin n)),
      x0 ∈ U ∧
      x0 ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ ∧
      (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hxU0 : adjacentTimePerturb (d := d) (n := n) x 0 ∈ U := by
    simpa using hxU
  have hpre :
      {ε : ℝ | adjacentTimePerturb (d := d) (n := n) x ε ∈ U} ∈ 𝓝 (0 : ℝ) := by
    exact (continuous_adjacentTimePerturb (d := d) (n := n) x).continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds hxU0)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hpre
  let ε : ℝ := δ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hε_mem : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    rw [show |ε - 0| = ε by simpa using abs_of_nonneg hε_nonneg]
    dsimp [ε]
    linarith
  refine ⟨adjacentTimePerturb (d := d) (n := n) x ε, 1, hδ_sub hε_mem, ?_, ?_⟩
  · exact adjacentTimePerturb_mem_identity_sector
      (d := d) (n := n) x hx_time0 hε_pos
  · simpa [EuclideanOrderedPositiveTimeSector, τ, Equiv.Perm.mul_apply] using
      (adjacentTimePerturb_mem_identity_sector
        (d := d) (n := n) x hx_time0 hε_pos)

/-- The raw real adjacent overlap used by the OS45 locality selector:
real Jost points whose real embeddings lie in the extended tube before and
after the adjacent swap. -/
def adjacentOS45RawOverlap
    (d n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Set (NPointDomain d n) :=
  {x | x ∈ JostSet d n ∧
      realEmbed x ∈ ExtendedTube d n ∧
      realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        ExtendedTube d n}

/-- The raw OS45 adjacent overlap is open. -/
theorem isOpen_adjacentOS45RawOverlap
    (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen (adjacentOS45RawOverlap d n i hi) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hswap_cont :
      Continuous (fun x : NPointDomain d n => realEmbed (fun k => x (τ k))) := by
    exact (continuous_realEmbed (d := d) (n := n)).comp (continuous_permNPoint (d := d) (n := n) τ)
  have h_eq :
      adjacentOS45RawOverlap d n i hi =
        JostSet d n ∩
          ({x : NPointDomain d n | realEmbed x ∈ ExtendedTube d n} ∩
            {x : NPointDomain d n | realEmbed (fun k => x (τ k)) ∈ ExtendedTube d n}) := by
    ext x
    simp [adjacentOS45RawOverlap, τ, and_left_comm]
  rw [h_eq]
  exact isOpen_jostSet.inter
    ((isOpen_extendedTube.preimage (continuous_realEmbed (d := d) (n := n))).inter
      (isOpen_extendedTube.preimage hswap_cont))

/-- In dimensions `d ≥ 2`, OS45 supplies a connected real-open edge slice on
which both adjacent ordered Wick seeds live in the forward tube. -/
theorem choose_os45_real_open_edge_for_adjacent_swap
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ JostSet d n) ∧
      (∀ x ∈ V, realEmbed x ∈ ExtendedTube d n) ∧
      (∀ x ∈ V,
        realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases adjacent_overlap_real_jost_witness_exists (d := d) (n := n) hd i hi with
    ⟨x, hxJ, _hsp, hx_time0, hxET, hxSwapET⟩
  have hxRaw : x ∈ adjacentOS45RawOverlap d n i hi := by
    exact ⟨hxJ, hxET, hxSwapET⟩
  rcases exists_ordered_small_time_perturb_in_adjacent_overlap
      (d := d) (n := n) hd i hi
      (adjacentOS45RawOverlap d n i hi)
      (isOpen_adjacentOS45RawOverlap (d := d) (n := n) i hi)
      x hxRaw hx_time0 with
    ⟨x0, ρ, hx0Raw, hx0Ord, hx0SwapOrd⟩
  let S : Set (NPointDomain d n) :=
    adjacentOS45RawOverlap d n i hi ∩
      (EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ ∩
        {x : NPointDomain d n |
          (fun k => x (τ k)) ∈
            EuclideanOrderedPositiveTimeSector (d := d) (n := n) (τ.symm * ρ)})
  have hS_open : IsOpen S := by
    dsimp [S]
    exact (isOpen_adjacentOS45RawOverlap (d := d) (n := n) i hi).inter
      ((isOpen_euclideanOrderedPositiveTimeSector (d := d) (n := n) ρ).inter
        ((isOpen_euclideanOrderedPositiveTimeSector (d := d) (n := n) (τ.symm * ρ)).preimage
          (continuous_permNPoint (d := d) (n := n) τ)))
  have hx0S : x0 ∈ S := by
    exact ⟨hx0Raw, ⟨hx0Ord, hx0SwapOrd⟩⟩
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp (hS_open.mem_nhds hx0S)
  refine ⟨Metric.ball x0 r, ρ, Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨x0, Metric.mem_ball_self hr_pos⟩, ?_⟩
    exact (convex_ball x0 r).isPreconnected
  · exact ⟨x0, Metric.mem_ball_self hr_pos⟩
  · intro y hy
    exact (hr_sub hy).1.1
  · intro y hy
    exact (hr_sub hy).1.2.1
  · intro y hy
    exact (hr_sub hy).1.2.2
  · intro y hy
    exact (hr_sub hy).2.1
  · intro y hy
    exact (hr_sub hy).2.2

/-- The ordered-Wick seed domain used by the OS45 locality route: the original
ordered Wick seed lies in the `ρ` PET sector, and the adjacent-swapped Wick
seed lies in the `τ.symm * ρ` PET sector. -/
def adjacentOS45WickSeedDomain
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  BHW.permutedExtendedTubeSector d n ρ ∩
    {z | BHW.permAct (d := d) τ z ∈
      BHW.permutedExtendedTubeSector d n (τ.symm * ρ)}

/-- The real adjacent edge domain used by the OS45 locality route:
real configurations whose two adjacent branches both lie in the extended
tube. -/
def adjacentOS45RealEdgeDomain
    (i : Fin n) (hi : i.val + 1 < n) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  BHW.ExtendedTube d n ∩
    {z | BHW.permAct (d := d) τ z ∈ BHW.ExtendedTube d n}

/-- The ordered-Wick seed domain is open. -/
theorem isOpen_adjacentOS45WickSeedDomain
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n)) :
    IsOpen (adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  dsimp [adjacentOS45WickSeedDomain]
  exact (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) ρ).inter
    ((BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) (τ.symm * ρ)).preimage
      (continuous_permComplexConfig (d := d) (n := n) τ))

/-- The real adjacent edge domain is open. -/
theorem isOpen_adjacentOS45RealEdgeDomain
    (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  dsimp [adjacentOS45RealEdgeDomain]
  exact BHW.isOpen_extendedTube.inter
    (BHW.isOpen_extendedTube.preimage
      (continuous_permComplexConfig (d := d) (n := n) τ))

/-- Ordered Euclidean time data places the Wick-rotated configuration in the
concrete adjacent OS45 Wick-seed domain. -/
theorem wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
    [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (ρ : Equiv.Perm (Fin n))
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hx_swap_ordered :
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    (fun k => wickRotatePoint (x k)) ∈
      adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.os45_adjacent_orderedWickSeeds_mem_forwardTube
      (d := d) (n := n) i hi x ρ hx_ordered hx_swap_ordered with
    ⟨hseed_id, hseed_swap⟩
  refine ⟨?_, ?_⟩
  · simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using
      BHW.forwardTube_subset_extendedTube hseed_id
  · simpa [BHW.permutedExtendedTubeSector] using
      BHW.forwardTube_subset_extendedTube hseed_swap

/-- ET overlap data places the real configuration in the concrete adjacent
OS45 real-edge domain. -/
theorem realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hx_swapET :
      BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n) :
    BHW.realEmbed x ∈
      adjacentOS45RealEdgeDomain (d := d) (n := n) i hi := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  refine ⟨hx_ET, ?_⟩
  simpa [BHW.permAct, τ, BHW.realEmbed] using hx_swapET

/-- Strengthened OS45 selector: the chosen real-open edge lies simultaneously
in the concrete real-edge domain and its Wick rotation lies in the concrete
ordered-seed domain used by the next local EOW step. -/
theorem choose_os45_real_open_edge_for_adjacent_swap_with_domains
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
      (∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ) ∧
      (∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) := by
  rcases choose_os45_real_open_edge_for_adjacent_swap
      (d := d) (n := n) hd i hi with
    ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET, hV_ordered,
      hV_swap_ordered⟩
  refine ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET,
    hV_ordered, hV_swap_ordered, ?_, ?_⟩
  · intro x hx
    exact wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
      (d := d) (n := n) i hi x ρ (hV_ordered x hx) (hV_swap_ordered x hx)
  · intro x hx
    exact realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
      (d := d) (n := n) i hi x (hV_ET x hx) (hV_swapET x hx)

/-- Fixed OS45 quarter-turn on the time coordinate.  This is the chart used to
exhibit the Wick and real traces as opposite-tube points over the same real
edge. -/
def os45QuarterTurnConfig
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => if μ = 0 then z k μ / 2 - (z k μ / 2) * Complex.I else z k μ

private theorem os45QuarterTurnScalar_ne_zero :
    (((1 : ℂ) - Complex.I) / 2 : ℂ) ≠ 0 := by
  refine div_ne_zero ?_ (by norm_num)
  intro h
  have hre := congrArg Complex.re h
  simp at hre

private noncomputable def os45QuarterTurnScalarUnit : ℂˣ :=
  Units.mk0 (((1 : ℂ) - Complex.I) / 2) os45QuarterTurnScalar_ne_zero

/-- The fixed time-coordinate quarter-turn as a continuous complex-linear
equivalence on `ℂ`.  This is the concrete chart used in the OS45 local EOW
formalization. -/
noncomputable def os45QuarterTurnTimeCLE : ℂ ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.smulLeft os45QuarterTurnScalarUnit

@[simp] theorem os45QuarterTurnTimeCLE_apply (z : ℂ) :
    os45QuarterTurnTimeCLE z = z / 2 - (z / 2) * Complex.I := by
  change ((((1 : ℂ) - Complex.I) / 2 : ℂ) * z) =
    z / 2 - (z / 2) * Complex.I
  ring

@[simp] theorem os45QuarterTurnTimeCLE_symm_apply (z : ℂ) :
    os45QuarterTurnTimeCLE.symm z = (1 + Complex.I) * z := by
  apply os45QuarterTurnTimeCLE.injective
  simp [os45QuarterTurnTimeCLE_apply]
  have hcoeff :
      (((1 : ℂ) + Complex.I) / 2 - (((1 : ℂ) + Complex.I) / 2) * Complex.I) = 1 := by
    calc
      (((1 : ℂ) + Complex.I) / 2 - (((1 : ℂ) + Complex.I) / 2) * Complex.I)
          = (1 / 2 : ℂ) + Complex.I ^ 2 * (-1 / 2) := by
              ring
      _ = (1 / 2 : ℂ) + (-1 : ℂ) * (-1 / 2) := by simp
      _ = 1 := by norm_num
  calc
    z = (1 : ℂ) * z := by ring
    _ = ((((1 : ℂ) + Complex.I) / 2 - (((1 : ℂ) + Complex.I) / 2) * Complex.I) * z) := by
          rw [hcoeff]
    _ = (1 + Complex.I) * z / 2 - (1 + Complex.I) * z / 2 * Complex.I := by
          ring

/-- The fixed quarter-turn on one spacetime point.  It only rotates/scales the
time coordinate; spatial coordinates are unchanged. -/
noncomputable def os45QuarterTurnSpacetimeCLE :
    (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun μ =>
    if _ : μ = 0 then os45QuarterTurnTimeCLE else ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem os45QuarterTurnSpacetimeCLE_apply
    (z : Fin (d + 1) → ℂ) :
    os45QuarterTurnSpacetimeCLE (d := d) z =
      fun μ => if μ = 0 then z μ / 2 - (z μ / 2) * Complex.I else z μ := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45QuarterTurnSpacetimeCLE, os45QuarterTurnTimeCLE_apply]
  · simp [os45QuarterTurnSpacetimeCLE, hμ]

@[simp] theorem os45QuarterTurnSpacetimeCLE_symm_apply
    (z : Fin (d + 1) → ℂ) :
    (os45QuarterTurnSpacetimeCLE (d := d)).symm z =
      fun μ => if μ = 0 then (1 + Complex.I) * z μ else z μ := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45QuarterTurnSpacetimeCLE, os45QuarterTurnTimeCLE_symm_apply]
  · simp [os45QuarterTurnSpacetimeCLE, hμ]

/-- The fixed quarter-turn chart on full `n`-point complexified configurations.
This packages the chosen OS45 chart as one global continuous linear
equivalence. -/
noncomputable def os45QuarterTurnCLE :
    (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun _ =>
    os45QuarterTurnSpacetimeCLE (d := d)

@[simp] theorem os45QuarterTurnCLE_apply
    (z : Fin n → Fin (d + 1) → ℂ) :
    os45QuarterTurnCLE (d := d) (n := n) z = os45QuarterTurnConfig (d := d) (n := n) z := by
  ext k μ
  simp [os45QuarterTurnCLE, os45QuarterTurnConfig, os45QuarterTurnSpacetimeCLE_apply]

@[simp] theorem os45QuarterTurnCLE_symm_apply
    (z : Fin n → Fin (d + 1) → ℂ) :
    (os45QuarterTurnCLE (d := d) (n := n)).symm z =
      fun k μ => if μ = 0 then (1 + Complex.I) * z k μ else z k μ := by
  ext k μ
  simp [os45QuarterTurnCLE, os45QuarterTurnSpacetimeCLE_symm_apply]

/-- Common real edge point for the OS45 quarter-turn chart. -/
def os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    NPointDomain d n :=
  fun k μ => if μ = 0 then x (σ k) 0 / 2 else x (σ k) μ

/-- Positive-tube direction produced by the OS45 quarter-turn chart. -/
def os45HalfTimeDirection
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ = 0 then x (σ k) 0 / 2 else 0

/-- For the adjacent OS45 pair, the swapped branch uses the same common real
edge point as the unswapped branch once the order label is changed from `ρ` to
`τ.symm * ρ`. -/
theorem os45CommonEdgeRealPoint_adjacent_swap_eq
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45CommonEdgeRealPoint (d := d) (n := n)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      os45CommonEdgeRealPoint (d := d) (n := n) ρ x := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45CommonEdgeRealPoint, Equiv.Perm.mul_apply]
  · simp [os45CommonEdgeRealPoint, hμ, Equiv.Perm.mul_apply]

/-- The adjacent swapped OS45 branch carries the same half-time direction as
the unswapped branch after the corresponding change of order label. -/
theorem os45HalfTimeDirection_adjacent_swap_eq
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45HalfTimeDirection (d := d) (n := n)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      os45HalfTimeDirection (d := d) (n := n) ρ x := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45HalfTimeDirection, Equiv.Perm.mul_apply]
  · simp [os45HalfTimeDirection, hμ]

private theorem os45HalfTimeDirection_mem_forwardCone_of_orderedPositiveTimeRegion
    [NeZero d]
    (x : NPointDomain d n)
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    InForwardCone d n (fun k μ => if μ = 0 then x k 0 / 2 else 0) := by
  intro k
  let η : Fin n → Fin (d + 1) → ℝ := fun j μ => if μ = 0 then x j 0 / 2 else 0
  let prev : Fin (d + 1) → ℝ :=
    if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩
  let diff : Fin (d + 1) → ℝ := fun μ => η k μ - prev μ
  have hdiff_time_pos : 0 < diff 0 := by
    by_cases hk : k.val = 0
    · have htime_pos : 0 < x k 0 / 2 := by
        nlinarith [(hx k).1]
      simpa [η, prev, diff, hk] using htime_pos
    · let j : Fin n := ⟨k.val - 1, by omega⟩
      have hj_lt_k : j < k := Fin.lt_def.mpr (by
        dsimp [j]
        omega)
      have htime_gap : x j 0 < x k 0 := (hx j).2 k hj_lt_k
      have hhalf_gap : 0 < x k 0 / 2 - x j 0 / 2 := by
        linarith
      simpa [η, prev, diff, hk, j] using hhalf_gap
  have hdiff_spatial_zero : ∀ i : Fin d, diff i.succ = 0 := by
    intro i
    by_cases hk : k.val = 0
    · simp [η, prev, diff, hk]
    · simp [η, prev, diff, hk]
  refine ⟨hdiff_time_pos, ?_⟩
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  have hspatial_zero : MinkowskiSpace.spatialNormSq d diff = 0 := by
    unfold MinkowskiSpace.spatialNormSq
    simp [hdiff_spatial_zero]
  rw [hspatial_zero]
  nlinarith [sq_pos_of_pos hdiff_time_pos]

/-- Ordered Euclidean time data turns the OS45 half-time direction into an
honest forward-cone direction after the chosen permutation. -/
theorem os45HalfTimeDirection_mem_forwardCone_of_ordered
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    InForwardCone d n (os45HalfTimeDirection (d := d) (n := n) σ x) := by
  let xσ : NPointDomain d n := fun k μ => x (σ k) μ
  have hxσ : xσ ∈ OrderedPositiveTimeRegion d n := hx
  simpa [os45HalfTimeDirection, xσ] using
    os45HalfTimeDirection_mem_forwardCone_of_orderedPositiveTimeRegion
      (d := d) (n := n) xσ hxσ

private theorem realEmbed_add_I_mem_forwardTube
    [NeZero d]
    (x : NPointDomain d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η) :
    (fun k μ => BHW.realEmbed x k μ + (η k μ : ℂ) * Complex.I) ∈
      BHW.ForwardTube d n := by
  have hη_bhw :
      ∀ k : Fin n,
        BHW.InOpenForwardCone d
          (fun μ =>
            η k μ -
              (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ) := by
    intro k
    exact (inOpenForwardCone_iff _).2 (hη k)
  intro k
  by_cases hk0 : k.val = 0
  · simpa [BHW.ForwardTube, hk0, BHW.realEmbed, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] using hη_bhw k
  · simpa [BHW.ForwardTube, hk0, BHW.realEmbed, Complex.add_im, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im] using hη_bhw k

/-- After the fixed OS45 quarter-turn, the real branch sits on the negative
tube over the common real edge. -/
theorem os45QuarterTurn_perm_realEmbed_eq_common_minus
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) =
      fun k μ =>
        BHW.realEmbed (os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ -
          (os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) * Complex.I := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45QuarterTurnConfig, os45CommonEdgeRealPoint, os45HalfTimeDirection, BHW.realEmbed]
  · simp [os45QuarterTurnConfig, os45CommonEdgeRealPoint, os45HalfTimeDirection,
      BHW.realEmbed, hμ]

/-- After the fixed OS45 quarter-turn, the Wick branch sits on the positive
tube over the same common real edge. -/
theorem os45QuarterTurn_perm_wickRotate_eq_common_plus
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45QuarterTurnConfig (fun k => wickRotatePoint (x (σ k))) =
      fun k μ =>
        BHW.realEmbed (os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ +
          (os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) * Complex.I := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45QuarterTurnConfig, os45CommonEdgeRealPoint, os45HalfTimeDirection,
      BHW.realEmbed, wickRotatePoint]
    let a : ℂ := x (σ k) 0
    calc
      Complex.I * a / 2 - Complex.I * a / 2 * Complex.I
          = Complex.I * a / 2 - (Complex.I * Complex.I) * a / 2 := by
              ring
      _ = Complex.I * a / 2 + a / 2 := by
            have hI : Complex.I * Complex.I = (-1 : ℂ) := by
              simp
            rw [hI]
            ring
      _ = a / 2 + a / 2 * Complex.I := by
            ring
  · simp [os45QuarterTurnConfig, os45CommonEdgeRealPoint, os45HalfTimeDirection,
      BHW.realEmbed, wickRotatePoint, hμ]

/-- In the fixed OS45 quarter-turn chart, the ordered Wick branch lands in the
ordinary forward tube over the common real edge. -/
theorem os45QuarterTurn_perm_wickRotate_mem_forwardTube_of_ordered
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    os45QuarterTurnConfig (fun k => wickRotatePoint (x (σ k))) ∈
      BHW.ForwardTube d n := by
  let xedge := os45CommonEdgeRealPoint (d := d) (n := n) σ x
  let η := os45HalfTimeDirection (d := d) (n := n) σ x
  have hη : InForwardCone d n η :=
    os45HalfTimeDirection_mem_forwardCone_of_ordered (d := d) (n := n) σ x hx
  have hmem :
      (fun k μ => BHW.realEmbed xedge k μ + (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n :=
    realEmbed_add_I_mem_forwardTube (d := d) (n := n) xedge η hη
  simpa [xedge, η] using
    (os45QuarterTurn_perm_wickRotate_eq_common_plus (d := d) (n := n) σ x).symm ▸ hmem

/-- In the fixed OS45 quarter-turn chart, negating the ordered real branch
puts it in the ordinary forward tube. This is the negative-tube half of the
common-boundary OS45 geometry. -/
theorem neg_os45QuarterTurn_perm_realEmbed_mem_forwardTube_of_ordered
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    (fun k μ => -os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) k μ) ∈
      BHW.ForwardTube d n := by
  let xedge := os45CommonEdgeRealPoint (d := d) (n := n) σ x
  let η := os45HalfTimeDirection (d := d) (n := n) σ x
  have hη : InForwardCone d n η :=
    os45HalfTimeDirection_mem_forwardCone_of_ordered (d := d) (n := n) σ x hx
  have hmem :
      (fun k μ =>
        BHW.realEmbed (fun j ν => -xedge j ν) k μ + (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n :=
    realEmbed_add_I_mem_forwardTube (d := d) (n := n) (fun j ν => -xedge j ν) η hη
  have hneg :
      (fun k μ => -os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) k μ) =
        fun k μ =>
          BHW.realEmbed (fun j ν => -xedge j ν) k μ + (η k μ : ℂ) * Complex.I := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [xedge, η, os45QuarterTurn_perm_realEmbed_eq_common_minus,
        os45CommonEdgeRealPoint, os45HalfTimeDirection, BHW.realEmbed]
      ring
    · simp [xedge, η, os45QuarterTurn_perm_realEmbed_eq_common_minus,
        os45CommonEdgeRealPoint, os45HalfTimeDirection, BHW.realEmbed, hμ]
  simpa [hneg] using hmem

/-- Branch-level OS45 geometry after the fixed quarter-turn chart: the real and
Wick traces become opposite-tube points over a common real edge. -/
structure OS45OppositeTubeBranchGeometry
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) : Prop where
  η_mem :
    InForwardCone d n (os45HalfTimeDirection (d := d) (n := n) σ x)
  real_eq :
    os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) =
      fun k μ =>
        BHW.realEmbed (os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ -
          (os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) * Complex.I
  wick_eq :
    os45QuarterTurnConfig (fun k => wickRotatePoint (x (σ k))) =
      fun k μ =>
        BHW.realEmbed (os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ +
          (os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) * Complex.I

/-- Ordered Euclidean time data gives the branch-level OS45 opposite-tube
geometry in the fixed quarter-turn chart. -/
theorem os45OppositeTubeBranchGeometry_of_ordered
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    OS45OppositeTubeBranchGeometry (d := d) (n := n) σ x := by
  refine ⟨?_, ?_, ?_⟩
  · exact os45HalfTimeDirection_mem_forwardCone_of_ordered
      (d := d) (n := n) σ x hx
  · exact os45QuarterTurn_perm_realEmbed_eq_common_minus
      (d := d) (n := n) σ x
  · exact os45QuarterTurn_perm_wickRotate_eq_common_plus
      (d := d) (n := n) σ x

/-- OS45 slot-1 geometry: on the selected real-open adjacent edge, the fixed
quarter-turn chart exhibits both adjacent branches as opposite-tube points over
common real edges with honest forward-cone directions. -/
theorem os45_adjacent_localEOWGeometry
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
      (∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ) ∧
      (∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) ∧
      (∀ x ∈ V,
        OS45OppositeTubeBranchGeometry (d := d) (n := n) ρ x) ∧
      (∀ x ∈ V,
        OS45OppositeTubeBranchGeometry (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases choose_os45_real_open_edge_for_adjacent_swap_with_domains
      (d := d) (n := n) hd i hi with
    ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET, hV_ordered,
      hV_swap_ordered, hV_wick, hV_real⟩
  refine ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET, hV_ordered,
    hV_swap_ordered, hV_wick, hV_real, ?_, ?_⟩
  · intro x hx
    exact os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) ρ x (hV_ordered x hx)
  · intro x hx
    exact os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) (τ.symm * ρ) (fun k => x (τ k))
      (hV_swap_ordered x hx)

/-- The real Jost set is disjoint from the Euclidean coincidence locus. -/
theorem jostSet_disjoint_coincidenceLocus :
    Disjoint (JostSet d n) (CoincidenceLocus d n) := by
  refine Set.disjoint_left.mpr ?_
  intro x hxJ hxCoin
  rcases hxCoin with ⟨i, j, hij, hij_eq⟩
  have hsp : IsSpacelike d (fun μ => x i μ - x j μ) := hxJ.2 i j hij
  have hzero : ∀ μ, x i μ - x j μ = 0 := by
    intro μ
    rw [hij_eq]
    simp
  have hsp0 := hsp
  simp [IsSpacelike, hzero] at hsp0

/-- Any Schwartz test whose topological support is contained in a real Jost
overlap vanishes to infinite order on the coincidence locus, hence belongs to
the OS-I zero-diagonal test space. -/
theorem zeroDiagonal_of_tsupport_subset_jostOverlap
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    VanishesToInfiniteOrderOnCoincidence φ := by
  have hdisj : Disjoint (tsupport (φ : NPointDomain d n → ℂ)) (CoincidenceLocus d n) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxSupp hxCoin
    have hxV : x ∈ V := hφ_tsupport hxSupp
    exact Set.disjoint_left.mp (jostSet_disjoint_coincidenceLocus (d := d) (n := n))
      (hV_jost x hxV) hxCoin
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint φ hdisj

/-- Reindexing a zero-diagonal Schwartz test by a finite permutation preserves
the zero-diagonal condition. -/
def permuteZeroDiagonalSchwartz
    (σ : Equiv.Perm (Fin n))
    (f : ZeroDiagonalSchwartz d n) :
    ZeroDiagonalSchwartz d n :=
  ⟨reindexSchwartz (d := d) σ f.1,
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      (d := d) f.2 σ⟩

@[simp] theorem permuteZeroDiagonalSchwartz_apply
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n)
    (x : NPointDomain d n) :
    (permuteZeroDiagonalSchwartz (d := d) σ f).1 x =
      f.1 (fun i => x (σ i)) := by
  rfl

private theorem integral_perm_eq_self_locality
    (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => x (σ i)) =
      ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- OS §4.5 Euclidean layer: on a real Jost edge slice, E3 symmetry and the
Euclidean boundary-value identification give equality of the adjacent Wick-edge
pairings against any compact test supported in that slice. -/
theorem os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ JostSet d n)
    (ρ : Equiv.Perm (Fin n))
    (_hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (_hV_swap_ordered : ∀ x ∈ V,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
    (φ : SchwartzNPoint d n)
    (hφ_tsupport :
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k => wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
          φ x
      =
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let φZ : ZeroDiagonalSchwartz d n :=
    ⟨φ, zeroDiagonal_of_tsupport_subset_jostOverlap
      (d := d) (n := n) V hV_jost φ hφ_tsupport⟩
  let ψZ : ZeroDiagonalSchwartz d n :=
    permuteZeroDiagonalSchwartz (d := d) (n := n) τ.symm φZ
  have hE3 : OS.S n φZ = OS.S n ψZ := by
    refine OS.E3_symmetric (n := n) (σ := τ.symm) φZ ψZ ?_
    intro x
    change (permuteZeroDiagonalSchwartz (d := d) (n := n) τ.symm φZ).1 x =
      φZ.1 (fun i => x (τ.symm i))
    simp
  have hφZ :
      OS.S n φZ =
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := by
    simpa [φZ] using bvt_euclidean_restriction (d := d) OS lgc n φZ
  have hψZ :
      OS.S n ψZ =
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
            φ (fun k => x (τ k)) := by
    simpa [ψZ, φZ, τ] using bvt_euclidean_restriction (d := d) OS lgc n ψZ
  have hperm :
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
            φ (fun k => x (τ k)) := by
    simpa [τ] using
      (integral_perm_eq_self_locality (d := d) (n := n) τ
        (fun x : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
            φ (fun k => x (τ k))))
  calc
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k => wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
          φ x
      = OS.S n ψZ := by
          rw [show Equiv.swap i ⟨i.val + 1, hi⟩ = τ by rfl, hperm, ← hψZ]
    _ = OS.S n φZ := by simpa using hE3.symm
    _ = ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := hφZ

/-- The sharp OS45 branch-difference envelope used by the theorem-2 adjacent
real-edge consumer.  This packages one connected holomorphic chart carrying the
Wick branch difference and the real-edge `extendF` difference on the same slice
`V`. -/
structure AdjacentOSEOWDifferenceEnvelope
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (τ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n)) where
  U : Set (Fin n → Fin (d + 1) → ℂ)
  U_open : IsOpen U
  U_connected : IsConnected U
  H : (Fin n → Fin (d + 1) → ℂ) → ℂ
  H_holo : DifferentiableOn ℂ H U
  wick_mem :
    ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U
  real_mem :
    ∀ x ∈ V, BHW.realEmbed x ∈ U
  wick_diff :
    ∀ x ∈ V,
      H (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) -
        bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  real_diff :
    ∀ x ∈ V,
      H (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (τ k))) -
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)

/-- If the test support is contained in `V` and the integrands agree on `V`,
then their pairings against the test function are equal. -/
theorem integral_eq_of_tsupport_subset_of_pointwise_on
    (V : Set (NPointDomain d n))
    (A B : NPointDomain d n → ℂ)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V)
    (hAB : ∀ x ∈ V, A x = B x) :
    ∫ x : NPointDomain d n, A x * φ x =
      ∫ x : NPointDomain d n, B x * φ x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  by_cases hxV : x ∈ V
  · simp [hAB x hxV]
  · have hx_not_tsupport : x ∉ tsupport (φ : NPointDomain d n → ℂ) := by
      intro hx
      exact hxV (hφ_tsupport hx)
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_tsupport
    simp [hφx]

/-- A connected holomorphic adjacent branch-difference envelope transports the
OS45 Wick-edge pairing equality to compact-test equality of the two adjacent
real-edge `extendF` traces on the chosen real-open slice. -/
theorem bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (E : AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V) :
    ∀ φ : SchwartzNPoint d n,
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hWickZero :
      ∀ x ∈ V, E.H (fun k => wickRotatePoint (x k)) = 0 := by
    intro x hx
    have hEq :
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
      simpa [τ] using
        (bvt_F_acrOne_package (d := d) OS lgc n).2.2.1 τ
          (fun k => wickRotatePoint (x k))
    have hsub :
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) = 0 :=
      sub_eq_zero.mpr hEq
    simpa [τ, E.wick_diff x hx] using hsub
  have hEqOn_H :
      Set.EqOn E.H (fun _ => 0) E.U := by
    refine eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
      (d := d) (n := n)
      E.U V E.U_open E.U_connected hV_open hV_nonempty E.wick_mem
      E.H (fun _ => 0) E.H_holo
      (by intro z hz; exact differentiableWithinAt_const (x := z) (c := (0 : ℂ))) ?_
    intro ψ _hψ_compact hψ_tsupport
    exact integral_eq_of_tsupport_subset_of_pointwise_on
      (d := d) (n := n) V
      (fun x => E.H (fun k => wickRotatePoint (x k)))
      (fun _ => 0)
      ψ hψ_tsupport hWickZero
  have hpoint :
      ∀ x ∈ V,
        BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (τ k))) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
    intro x hx
    have hHx : E.H (BHW.realEmbed x) = 0 := hEqOn_H (E.real_mem x hx)
    have hsub :
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) = 0 := by
      simpa [τ, E.real_diff x hx] using hHx
    exact sub_eq_zero.mp hsub
  intro φ _hφ_compact hφ_tsupport
  exact integral_eq_of_tsupport_subset_of_pointwise_on
    (d := d) (n := n) V
    (fun x =>
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))))
    (fun x =>
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))
    φ hφ_tsupport hpoint

end BHW
