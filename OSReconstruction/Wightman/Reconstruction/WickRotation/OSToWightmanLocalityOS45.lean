import OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
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

end BHW
