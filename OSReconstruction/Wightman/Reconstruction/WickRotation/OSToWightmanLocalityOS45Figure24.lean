import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45TraceMembership
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ}

/-- The real embedding of `n`-point configurations is continuous. -/
theorem continuous_realEmbedNPoint :
    Continuous
      (BHW.realEmbed :
        NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact Complex.continuous_ofReal.comp
    ((continuous_apply μ).comp (continuous_apply k))

/-- Permuting the point labels of a real `n`-point configuration is
continuous. -/
theorem continuous_permNPoint (τ : Equiv.Perm (Fin n)) :
    Continuous (fun x : NPointDomain d n => fun k => x (τ k)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (τ k))

/-- The OS45 horizontal common-edge real map is continuous. -/
theorem continuous_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n)) :
    Continuous
      (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [BHW.os45CommonEdgeRealPoint] using
      (((continuous_apply (0 : Fin (d + 1))).comp
        (continuous_apply (σ k))).div_const 2)
  · simpa [BHW.os45CommonEdgeRealPoint, hμ] using
      ((continuous_apply μ).comp (continuous_apply (σ k)))

/-- The embedded OS45 horizontal common-edge real map is continuous. -/
theorem continuous_realEmbed_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n)) :
    Continuous
      (fun x : NPointDomain d n =>
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ x)) :=
  BHW.continuous_realEmbedNPoint.comp
    (BHW.continuous_os45CommonEdgeRealPoint
      (d := d) (n := n) σ)

/-- The explicit small-time perturbation is continuous in the perturbation
parameter. -/
theorem continuous_adjacentTimePerturb_realParam
    (x : NPointDomain d n) :
    Continuous (BHW.adjacentTimePerturb (d := d) (n := n) x) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [BHW.adjacentTimePerturb] using
      (continuous_const.add (continuous_id.mul continuous_const))
  · simpa [BHW.adjacentTimePerturb, hμ] using
      (continuous_const : Continuous fun _ε : ℝ => x k μ)

/-- A positive perturbation of an equal-time configuration lies in the identity
ordered positive-time sector. -/
theorem adjacentTimePerturb_mem_identity_sector_of_pos
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    {ε : ℝ} (hε_pos : 0 < ε) :
    BHW.adjacentTimePerturb (d := d) (n := n) x ε ∈
      EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) := by
  change BHW.adjacentTimePerturb (d := d) (n := n) x ε ∈
    OrderedPositiveTimeRegion d n
  intro k
  constructor
  · have hk_pos : 0 < (k : ℝ) + 1 := by positivity
    have htarget : 0 < ε * ((k : ℝ) + 1) := mul_pos hε_pos hk_pos
    simpa [BHW.adjacentTimePerturb, hx_time0 k] using htarget
  · intro j hj
    have hk_lt_j : (k : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have hk1_lt_j1 : (k : ℝ) + 1 < (j : ℝ) + 1 := by linarith
    have htarget : ε * ((k : ℝ) + 1) < ε * ((j : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hk1_lt_j1 hε_pos
    simpa [BHW.adjacentTimePerturb, hx_time0 k, hx_time0 j] using htarget

/-- The identity common-edge map fixes equal-time real configurations. -/
theorem os45CommonEdgeRealPoint_one_eq_self_of_time_zero
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0) :
    BHW.os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x = x := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [BHW.os45CommonEdgeRealPoint, hx_time0 k]
  · simp [BHW.os45CommonEdgeRealPoint, hμ]

/-- Halving all Euclidean time coordinates by the identity common-edge map
preserves every ordered positive-time sector. -/
theorem os45CommonEdgeRealPoint_one_mem_orderedSector_of_mem
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx :
      x ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) σ) :
    BHW.os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x ∈
      EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) σ := by
  change
    (fun k =>
      BHW.os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x (σ k)) ∈
      OrderedPositiveTimeRegion d n
  change (fun k => x (σ k)) ∈ OrderedPositiveTimeRegion d n at hx
  intro k
  constructor
  · have hpos : 0 < x (σ k) 0 := (hx k).1
    have hhalf : 0 < x (σ k) 0 / 2 := by nlinarith
    simpa [BHW.os45CommonEdgeRealPoint] using hhalf
  · intro j hj
    have hlt : x (σ k) 0 < x (σ j) 0 := (hx k).2 j hj
    have hhalf : x (σ k) 0 / 2 < x (σ j) 0 / 2 := by nlinarith
    simpa [BHW.os45CommonEdgeRealPoint] using hhalf

/-- For an equal-time anchor, the identity common edge of the perturbation by
`ε` is the perturbation by `ε / 2`. -/
theorem os45CommonEdgeRealPoint_one_adjacentTimePerturb_eq_half
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    (ε : ℝ) :
    BHW.os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
        (BHW.adjacentTimePerturb (d := d) (n := n) x ε) =
      BHW.adjacentTimePerturb (d := d) (n := n) x (ε / 2) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [BHW.os45CommonEdgeRealPoint, BHW.adjacentTimePerturb,
      hx_time0 k]
    ring
  · simp [BHW.os45CommonEdgeRealPoint, BHW.adjacentTimePerturb, hμ]

/-- The segment from a perturbation to its identity common-edge contact stays on
the same explicit perturbation ray. -/
theorem adjacentTimePerturb_segment_commonEdge_subset_paramInterval
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) :
    segment ℝ
        (BHW.adjacentTimePerturb (d := d) (n := n) x ε)
        (BHW.os45CommonEdgeRealPoint
          (d := d) (n := n) (1 : Equiv.Perm (Fin n))
          (BHW.adjacentTimePerturb (d := d) (n := n) x ε)) ⊆
      {y : NPointDomain d n |
        ∃ s : ℝ, ε / 2 ≤ s ∧ s ≤ ε ∧
          y = BHW.adjacentTimePerturb (d := d) (n := n) x s} := by
  rw [segment_subset_iff]
  intro a b ha hb hab
  refine ⟨a * ε + b * (ε / 2), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45CommonEdgeRealPoint, BHW.adjacentTimePerturb,
        hx_time0 k]
      ring
    · simp [BHW.os45CommonEdgeRealPoint, BHW.adjacentTimePerturb, hμ]
      calc
        a * x k μ + b * x k μ = (a + b) * x k μ := by ring
        _ = x k μ := by rw [hab]; ring

/-- A bounded small-time perturbation can be chosen so that both the ordered
seed and its OS45 identity common-edge contact remain in a prescribed open
adjacent overlap.  This is the two-point source patch needed by the strict
OS II Figure-2-4 route. -/
theorem exists_ordered_small_time_perturb_with_commonEdge_in_adjacent_overlap_of_lt
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n)
    (U : Set (NPointDomain d n)) (hU_open : IsOpen U)
    (x0 : NPointDomain d n) (hx0U : x0 ∈ U)
    (hx0_time0 : ∀ k : Fin n, x0 k 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      let xseed := BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
      let xcontact :=
        BHW.os45CommonEdgeRealPoint
          (d := d) (n := n) (1 : Equiv.Perm (Fin n)) xseed
      xseed ∈ U ∧ xcontact ∈ U ∧
      xseed ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∧
      (fun k => xseed (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector
          (d := d) (n := n) (Equiv.swap i ⟨i.val + 1, hi⟩) ∧
      xcontact ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∧
      (fun k => xcontact (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector
          (d := d) (n := n) (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let common :
      NPointDomain d n → NPointDomain d n :=
    BHW.os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  let U' : Set (NPointDomain d n) := U ∩ {x | common x ∈ U}
  have hU'_open : IsOpen U' := by
    dsimp [U', common]
    exact hU_open.inter
      (hU_open.preimage
        (BHW.continuous_os45CommonEdgeRealPoint
          (d := d) (n := n) (1 : Equiv.Perm (Fin n))))
  have hx0_common :
      common x0 = x0 := by
    simpa [common] using
      BHW.os45CommonEdgeRealPoint_one_eq_self_of_time_zero
        (d := d) (n := n) x0 hx0_time0
  have hx0U' : x0 ∈ U' := by
    exact ⟨hx0U, by simpa [hx0_common] using hx0U⟩
  rcases
      BHW.exists_ordered_small_time_perturb_in_adjacent_overlap_of_lt
        (d := d) (n := n) hd i hi U' hU'_open
        x0 hx0U' hx0_time0 hδ with
    ⟨ε, hε_pos, hε_lt, hseedU', hseed_ordered,
      hseed_swap_ordered⟩
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let xcontact : NPointDomain d n := common xseed
  have hseedU : xseed ∈ U := hseedU'.1
  have hcontactU : xcontact ∈ U := hseedU'.2
  have hcontact_ordered :
      xcontact ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) := by
    simpa [xcontact, common] using
      BHW.os45CommonEdgeRealPoint_one_mem_orderedSector_of_mem
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) xseed
        hseed_ordered
  have hcontact_swap_ordered :
      (fun k => xcontact (τ k)) ∈
        EuclideanOrderedPositiveTimeSector
          (d := d) (n := n) τ := by
    have hraw :
        BHW.os45CommonEdgeRealPoint
            (d := d) (n := n) (1 : Equiv.Perm (Fin n))
            (fun k => xseed (τ k)) ∈
          EuclideanOrderedPositiveTimeSector
            (d := d) (n := n) τ :=
      BHW.os45CommonEdgeRealPoint_one_mem_orderedSector_of_mem
        (d := d) (n := n) τ (fun k => xseed (τ k))
        hseed_swap_ordered
    have heq :
        (fun k => xcontact (τ k)) =
          BHW.os45CommonEdgeRealPoint
            (d := d) (n := n) (1 : Equiv.Perm (Fin n))
            (fun k => xseed (τ k)) := by
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [xcontact, common, BHW.os45CommonEdgeRealPoint]
      · simp [xcontact, common, BHW.os45CommonEdgeRealPoint, hμ]
    simpa [heq] using hraw
  refine ⟨ε, hε_pos, hε_lt, ?_⟩
  simpa [xseed, xcontact, common, τ] using
    ⟨hseedU, hcontactU, hseed_ordered, hseed_swap_ordered,
      hcontact_ordered, hcontact_swap_ordered⟩

/-- Strengthened segment form of the two-point perturbation: the whole segment
from the ordered seed to its identity common-edge contact remains in the
prescribed open overlap and in both ordered sectors. -/
theorem exists_ordered_small_time_perturb_with_commonEdge_segment_in_adjacent_overlap_of_lt
    [NeZero d]
    (_hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n)
    (U : Set (NPointDomain d n)) (hU_open : IsOpen U)
    (x0 : NPointDomain d n) (hx0U : x0 ∈ U)
    (hx0_time0 : ∀ k : Fin n, x0 k 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
      let xseed := BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
      let xcontact :=
        BHW.os45CommonEdgeRealPoint
          (d := d) (n := n) (1 : Equiv.Perm (Fin n)) xseed
      xseed ∈ U ∧ xcontact ∈ U ∧
      xseed ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∧
      (fun k => xseed (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ ∧
      xcontact ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∧
      (fun k => xcontact (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ ∧
      segment ℝ xseed xcontact ⊆
        U ∩
          EuclideanOrderedPositiveTimeSector
            (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∩
          {x |
            (fun k => x (τ k)) ∈
              EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ} := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hxU0 :
      BHW.adjacentTimePerturb (d := d) (n := n) x0 0 ∈ U := by
    simpa [BHW.adjacentTimePerturb] using hx0U
  have hpre :
      {ε : ℝ | BHW.adjacentTimePerturb (d := d) (n := n) x0 ε ∈ U} ∈
        𝓝 (0 : ℝ) :=
    (BHW.continuous_adjacentTimePerturb_realParam
      (d := d) (n := n) x0).continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds hxU0)
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hpre
  let ε : ℝ := min r δ / 2
  have hmin_pos : 0 < min r δ := lt_min hr_pos hδ
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hε_lt_r : ε < r := by
    have hmin_le : min r δ ≤ r := min_le_left r δ
    dsimp [ε]
    nlinarith
  have hε_lt_δ : ε < δ := by
    have hmin_le : min r δ ≤ δ := min_le_right r δ
    dsimp [ε]
    nlinarith
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let xcontact : NPointDomain d n :=
    BHW.os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) xseed
  have hseg_param :
      segment ℝ xseed xcontact ⊆
        {y : NPointDomain d n |
          ∃ s : ℝ, ε / 2 ≤ s ∧ s ≤ ε ∧
            y = BHW.adjacentTimePerturb (d := d) (n := n) x0 s} := by
    simpa [xseed, xcontact] using
      BHW.adjacentTimePerturb_segment_commonEdge_subset_paramInterval
        (d := d) (n := n) x0 hx0_time0 (le_of_lt hε_pos)
  have hsegment_U : segment ℝ xseed xcontact ⊆ U := by
    intro y hy
    rcases hseg_param hy with ⟨s, hs_low, hs_high, rfl⟩
    have hs_nonneg : 0 ≤ s := by nlinarith
    have hs_lt_r : s < r := by nlinarith
    apply hr_sub
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |s| = s := abs_of_nonneg hs_nonneg
    simpa [habs] using hs_lt_r
  have hsegment_ordered :
      segment ℝ xseed xcontact ⊆
        EuclideanOrderedPositiveTimeSector
          (d := d) (n := n) (1 : Equiv.Perm (Fin n)) := by
    intro y hy
    rcases hseg_param hy with ⟨s, hs_low, _hs_high, rfl⟩
    have hs_pos : 0 < s := by nlinarith
    exact BHW.adjacentTimePerturb_mem_identity_sector_of_pos
      (d := d) (n := n) x0 hx0_time0 hs_pos
  have hsegment_swap_ordered :
      segment ℝ xseed xcontact ⊆
        {x |
          (fun k => x (τ k)) ∈
            EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ} := by
    intro y hy
    rcases hseg_param hy with ⟨s, hs_low, _hs_high, rfl⟩
    have hs_pos : 0 < s := by nlinarith
    have hordered :
        BHW.adjacentTimePerturb (d := d) (n := n) x0 s ∈
          EuclideanOrderedPositiveTimeSector
            (d := d) (n := n) (1 : Equiv.Perm (Fin n)) :=
      BHW.adjacentTimePerturb_mem_identity_sector_of_pos
        (d := d) (n := n) x0 hx0_time0 hs_pos
    simpa [EuclideanOrderedPositiveTimeSector, τ, Equiv.Perm.mul_apply]
      using hordered
  have hxseed_seg : xseed ∈ segment ℝ xseed xcontact :=
    left_mem_segment ℝ xseed xcontact
  have hxcontact_seg : xcontact ∈ segment ℝ xseed xcontact :=
    right_mem_segment ℝ xseed xcontact
  have hseedU : xseed ∈ U := hsegment_U hxseed_seg
  have hcontactU : xcontact ∈ U := hsegment_U hxcontact_seg
  have hseed_ordered :
      xseed ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) :=
    hsegment_ordered hxseed_seg
  have hcontact_ordered :
      xcontact ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) :=
    hsegment_ordered hxcontact_seg
  have hseed_swap_ordered :
      (fun k => xseed (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ :=
    hsegment_swap_ordered hxseed_seg
  have hcontact_swap_ordered :
      (fun k => xcontact (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ :=
    hsegment_swap_ordered hxcontact_seg
  have hseg_final :
      segment ℝ xseed xcontact ⊆
        U ∩
          EuclideanOrderedPositiveTimeSector
            (d := d) (n := n) (1 : Equiv.Perm (Fin n)) ∩
          {x |
            (fun k => x (τ k)) ∈
              EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ} := by
    intro y hy
    exact ⟨⟨hsegment_U hy, hsegment_ordered hy⟩,
      hsegment_swap_ordered hy⟩
  refine ⟨ε, hε_pos, hε_lt_δ, ?_⟩
  simpa [τ, xseed, xcontact] using
    ⟨hseedU, hcontactU, hseed_ordered, hseed_swap_ordered,
      hcontact_ordered, hcontact_swap_ordered,
      ⟨⟨hsegment_U, hsegment_ordered⟩, hsegment_swap_ordered⟩⟩

/-- Compact-parameter tube lemma: if a continuous family is inside an open set
along `{x0} × Y` and `Y` is compact, then a single open neighborhood of `x0`
works for all parameters. -/
theorem exists_open_nhds_forall_mem_of_compact_parameter
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace Y]
    {f : X × Y → Z} (hf : Continuous f)
    {x0 : X} {U : Set Z} (hU_open : IsOpen U)
    (hx0 : ∀ y : Y, f (x0, y) ∈ U) :
    ∃ V : Set X,
      IsOpen V ∧ x0 ∈ V ∧
        ∀ x ∈ V, ∀ y : Y, f (x, y) ∈ U := by
  have hP : ∀ y ∈ (Set.univ : Set Y),
      ∀ᶠ z : X × Y in 𝓝 (x0, y), f z ∈ U := by
    intro y _hy
    exact hf.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds (hx0 y))
  have hEventually :
      ∀ᶠ x in 𝓝 x0,
        ∀ y ∈ (Set.univ : Set Y), f (x, y) ∈ U :=
    (isCompact_univ : IsCompact (Set.univ : Set Y)).eventually_forall_of_forall_eventually
      hP
  rcases mem_nhds_iff.mp hEventually with
    ⟨V, hV_sub, hV_open, hx0V⟩
  refine ⟨V, hV_open, hx0V, ?_⟩
  intro x hx y
  exact hV_sub hx y trivial

/-- Time coefficient for the identity branch in the Streater-Wightman
Figure-2-4 path.  It interpolates from Wick time `I * τ` to the inverse OS45
quarter-turn time `(1 + I) * τ / 2`. -/
def os45Figure24TimeCoeff (t : unitInterval) : ℂ :=
  (((t : ℝ) / 2 : ℝ) : ℂ) +
    (((1 : ℝ) - (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I

theorem os45Figure24TimeCoeff_zero :
    os45Figure24TimeCoeff (0 : unitInterval) = Complex.I := by
  norm_num [os45Figure24TimeCoeff]

theorem os45Figure24TimeCoeff_one :
    os45Figure24TimeCoeff (1 : unitInterval) =
      ((1 : ℂ) + Complex.I) / 2 := by
  norm_num [os45Figure24TimeCoeff]
  ring

theorem continuous_os45Figure24TimeCoeff :
    Continuous BHW.os45Figure24TimeCoeff := by
  have ht : Continuous (fun t : unitInterval => (t : ℝ)) :=
    continuous_subtype_val
  have hhalf : Continuous (fun t : unitInterval => ((t : ℝ) / 2)) :=
    ht.div_const 2
  have hleft :
      Continuous (fun t : unitInterval => (((t : ℝ) / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hhalf
  have hrightCoeff :
      Continuous
        (fun t : unitInterval =>
          ((((1 : ℝ) - (t : ℝ) / 2 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub hhalf)
  have hI : Continuous (fun _ : unitInterval => Complex.I) :=
    continuous_const
  change Continuous
    (fun t : unitInterval =>
      (((t : ℝ) / 2 : ℝ) : ℂ) +
        ((((1 : ℝ) - (t : ℝ) / 2 : ℝ)) : ℂ) * Complex.I)
  exact hleft.add (hrightCoeff.mul hI)

/-- The identity-side Figure-2-4 path from the Wick configuration to the
inverse OS45 quarter-turn of the horizontal common edge. -/
def os45Figure24IdentityPath
    (x : NPointDomain d n)
    (t : unitInterval) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    if μ = 0 then os45Figure24TimeCoeff t * (x k 0 : ℂ)
    else (x k μ : ℂ)

theorem os45Figure24IdentityPath_zero
    (x : NPointDomain d n) :
    os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval) =
      (fun k => wickRotatePoint (x k)) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45Figure24IdentityPath, os45Figure24TimeCoeff_zero,
      wickRotatePoint]
  · simp [os45Figure24IdentityPath, wickRotatePoint, hμ]

theorem os45Figure24IdentityPath_one
    (x : NPointDomain d n) :
    let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
    let y := BHW.os45CommonEdgeRealPoint (d := d) (n := n)
      (1 : Equiv.Perm (Fin n)) x
    os45Figure24IdentityPath (d := d) (n := n) x (1 : unitInterval) =
      Q.symm (BHW.realEmbed y) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45Figure24IdentityPath, os45Figure24TimeCoeff_one,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.os45CommonEdgeRealPoint,
      BHW.realEmbed]
    ring
  · simp [os45Figure24IdentityPath, BHW.os45QuarterTurnCLE_symm_apply,
      BHW.os45CommonEdgeRealPoint, BHW.realEmbed, hμ]

theorem continuous_os45Figure24IdentityPath
    (x : NPointDomain d n) :
    Continuous (BHW.os45Figure24IdentityPath (d := d) (n := n) x) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [os45Figure24IdentityPath] using
      (BHW.continuous_os45Figure24TimeCoeff.mul continuous_const)
  · simpa [os45Figure24IdentityPath, hμ] using
      (continuous_const : Continuous
        (fun _ : unitInterval => (x k μ : ℂ)))

/-- If the real configuration has zero Euclidean time coordinates, the
Figure-2-4 identity path is constant and equal to its real embedding. -/
theorem os45Figure24IdentityPath_of_time_zero
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    (t : unitInterval) :
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t =
      BHW.realEmbed x := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [BHW.os45Figure24IdentityPath, BHW.realEmbed, hx_time0 k]
  · simp [BHW.os45Figure24IdentityPath, BHW.realEmbed, hμ]

/-- Joint continuity of the Figure-2-4 identity path in the real point and the
path parameter. -/
theorem continuous_os45Figure24IdentityPath_joint :
    Continuous
      (fun p : NPointDomain d n × unitInterval =>
        BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hcoord : Continuous
      (fun p : NPointDomain d n × unitInterval => (p.1 k μ : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp ((continuous_apply k).comp continuous_fst))
  by_cases hμ : μ = 0
  · subst hμ
    have htime :
        Continuous
          (fun p : NPointDomain d n × unitInterval =>
            BHW.os45Figure24TimeCoeff p.2) :=
      BHW.continuous_os45Figure24TimeCoeff.comp continuous_snd
    have htimeCoord : Continuous
        (fun p : NPointDomain d n × unitInterval => (p.1 k 0 : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ((continuous_apply (0 : Fin (d + 1))).comp
          ((continuous_apply k).comp continuous_fst))
    simpa [BHW.os45Figure24IdentityPath] using htime.mul htimeCoord
  · simpa [BHW.os45Figure24IdentityPath, hμ] using hcoord

/-- Along the identity ordered sector, the Figure-2-4 identity path stays in
the ordinary forward tube.  The imaginary time gaps are the positive scalar
`1 - t / 2` times the Euclidean ordered time gaps, and the spatial imaginary
gaps vanish. -/
theorem os45Figure24IdentityPath_mem_forwardTube
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))) :
    ∀ t,
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t ∈
        BHW.ForwardTube d n := by
  intro t k
  let coeff : ℝ := 1 - (t : ℝ) / 2
  let gap : ℝ :=
    if (k : ℕ) = 0 then x k 0
    else x k 0 - x ⟨(k : ℕ) - 1, by omega⟩ 0
  let η : Fin (d + 1) → ℝ := fun μ =>
    (BHW.os45Figure24IdentityPath (d := d) (n := n) x t k μ).im -
      ((if (k : ℕ) = 0 then 0 else
        BHW.os45Figure24IdentityPath (d := d) (n := n) x t
          ⟨(k : ℕ) - 1, by omega⟩) μ).im
  have hcoeff_pos : 0 < coeff := by
    have ht_le : (t : ℝ) ≤ 1 := t.property.2
    dsimp [coeff]
    nlinarith
  have hx_ord : x ∈ OrderedPositiveTimeRegion d n := by
    simpa [EuclideanOrderedPositiveTimeSector] using hx_ordered
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    by_cases hk : (k : ℕ) = 0
    · have hbase : 0 < x k 0 := (hx_ord k).1
      simpa [hk] using hbase
    · let j : Fin n := ⟨(k : ℕ) - 1, by omega⟩
      have hj_lt_k : j < k := Fin.lt_def.mpr (by
        dsimp [j]
        omega)
      have hlt : x j 0 < x k 0 := (hx_ord j).2 k hj_lt_k
      have hgap : 0 < x k 0 - x j 0 := sub_pos.mpr hlt
      simpa [hk, j] using hgap
  have hη0 : η 0 = coeff * gap := by
    dsimp [η, coeff, gap]
    by_cases hk : (k : ℕ) = 0
    · simp [BHW.os45Figure24IdentityPath, BHW.os45Figure24TimeCoeff, hk,
        Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
    · simp [BHW.os45Figure24IdentityPath, BHW.os45Figure24TimeCoeff, hk,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      ring
  have hη0_pos : 0 < η 0 := by
    rw [hη0]
    exact mul_pos hcoeff_pos hgap_pos
  have hspatial_zero : ∀ i : Fin d, η i.succ = 0 := by
    intro i
    dsimp [η]
    by_cases hk : (k : ℕ) = 0
    · simp [BHW.os45Figure24IdentityPath, hk]
    · simp [BHW.os45Figure24IdentityPath, hk]
  dsimp [BHW.ForwardTube, BHW.InOpenForwardCone]
  change η 0 > 0 ∧
    (∑ μ, LorentzLieGroup.minkowskiSignature d μ * η μ ^ 2) < 0
  constructor
  · exact hη0_pos
  · rw [BHW.minkowski_sum_decomp (d := d) (η := η)]
    have hsum_zero : (∑ i : Fin d, η i.succ ^ 2) = 0 := by
      simp [hspatial_zero]
    rw [hsum_zero]
    nlinarith [sq_pos_of_pos hη0_pos]

theorem continuous_figure24RotateAdjacentConfig
    (hd : 2 ≤ d) :
    Continuous (BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hcoord : ∀ ν : Fin (d + 1), Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ => z k ν) := by
    intro ν
    exact (continuous_apply ν).comp (continuous_apply k)
  by_cases h0 : μ = 0
  · simpa [figure24RotateAdjacentConfig, h0] using hcoord μ
  · by_cases h1 : μ = BHW.figure24Axis1 (d := d) hd
    · simpa [figure24RotateAdjacentConfig, h1] using
        (continuous_const.mul
          (hcoord (BHW.figure24Axis1 (d := d) hd))).sub
          (continuous_const.mul
            (hcoord (BHW.figure24Axis2 (d := d) hd)))
    · by_cases h2 : μ = BHW.figure24Axis2 (d := d) hd
      · simpa [figure24RotateAdjacentConfig, h1, h2] using
          (continuous_const.mul
            (hcoord (BHW.figure24Axis1 (d := d) hd))).add
            (continuous_const.mul
              (hcoord (BHW.figure24Axis2 (d := d) hd)))
      · simpa [figure24RotateAdjacentConfig, h0, h1, h2] using hcoord μ

/-- Continuity of the rotated adjacent Figure-2-4 path in the real point and
path parameter. -/
theorem continuous_figure24RotatedIdentityPath
    (hd : 2 ≤ d)
    (τ : Equiv.Perm (Fin n)) :
    Continuous
      (fun p : NPointDomain d n × unitInterval =>
        BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
          (BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2))) := by
  have hperm : Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.permAct (d := d) τ z) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (τ k))
  exact (BHW.continuous_figure24RotateAdjacentConfig (d := d) (n := n) hd).comp
    (hperm.comp BHW.continuous_os45Figure24IdentityPath_joint)

/-- Deterministic adjacent Figure-2-4 lift: rotate the permuted identity path
by the checked two-plane Figure-2-4 correction. -/
def os45Figure24AdjacentLift
    (hd : 2 ≤ d)
    (τ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (t : unitInterval) :
    Fin n → Fin (d + 1) → ℂ :=
  BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
    (BHW.permAct (d := d) τ
      (BHW.os45Figure24IdentityPath (d := d) (n := n) x t))

/-- Joint continuity of the deterministic adjacent Figure-2-4 lift. -/
theorem continuous_os45Figure24AdjacentLift
    (hd : 2 ≤ d)
    (τ : Equiv.Perm (Fin n)) :
    Continuous
      (fun p : NPointDomain d n × unitInterval =>
        BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ p.1 p.2) := by
  simpa [BHW.os45Figure24AdjacentLift] using
    BHW.continuous_figure24RotatedIdentityPath (d := d) (n := n) hd τ

/-- The deterministic adjacent Figure-2-4 lift has the source Gram of the
permuted identity path. -/
theorem os45Figure24AdjacentLift_sourceGram
    (hd : 2 ≤ d)
    (τ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (t : unitInterval) :
    BHW.sourceMinkowskiGram d n
        (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t) =
      BHW.sourcePermuteComplexGram n τ
        (BHW.sourceMinkowskiGram d n
          (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)) := by
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  have hInv :
      BHW.complexLorentzAction Λinv
          (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t) =
        BHW.permAct (d := d) τ Γ := by
    simpa [BHW.os45Figure24AdjacentLift, Γ] using
      hΛinv (BHW.permAct (d := d) τ Γ)
  have hLor :
      BHW.sourceMinkowskiGram d n
          (BHW.complexLorentzAction Λinv
            (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t)) =
        BHW.sourceMinkowskiGram d n
          (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t) :=
    BHW.sourceMinkowskiGram_complexLorentzAction
      (d := d) (n := n) Λinv
      (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t)
  calc
    BHW.sourceMinkowskiGram d n
        (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t)
        =
      BHW.sourceMinkowskiGram d n
        (BHW.complexLorentzAction Λinv
          (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t)) := hLor.symm
    _ = BHW.sourceMinkowskiGram d n
        (BHW.permAct (d := d) τ Γ) := by
          rw [hInv]
    _ = BHW.sourcePermuteComplexGram n τ
        (BHW.sourceMinkowskiGram d n Γ) := by
          simpa [BHW.permAct, Γ] using
            BHW.sourceMinkowskiGram_perm d n τ Γ

/-- Oriented Figure-2-4 path field for the adjacent horizontal corridor.  It
records equality of the full oriented source invariant, not only equality of
ordinary source Gram coordinates. -/
def OS45Figure24OrientedPathField
    [NeZero d]
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) : Prop :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let y :=
    BHW.os45CommonEdgeRealPoint (d := d) (n := n)
      (1 : Equiv.Perm (Fin n)) x
  ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
    Continuous Γ ∧
    Continuous Δ ∧
    Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
    Γ (1 : unitInterval) = Q.symm (BHW.realEmbed y) ∧
    (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
    (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
    (∀ t,
      BHW.sourceOrientedMinkowskiInvariant d n (Δ t) =
        BHW.sourcePermuteOrientedGram d n τ
          (BHW.sourceOrientedMinkowskiInvariant d n (Γ t)))

/-- The definitional rotated adjacent Figure-2-4 path exported before projecting
to ordinary source Gram coordinates. -/
def OS45Figure24RotatedPathFormulaField
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) : Prop :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  ∃ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ,
    Continuous Δ ∧
    (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
    (∀ t,
      Δ t =
        BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
          (BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)))

/-- The checked rotated Figure-2-4 formula implies equality of the full oriented
source invariant along the horizontal path. -/
theorem OS45Figure24OrientedPathField_of_checked_figure24
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)))
    (hRotated :
      BHW.OS45Figure24RotatedPathFormulaField (d := d) hd n i hi x) :
    BHW.OS45Figure24OrientedPathField (d := d) n i hi x := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let Γ : unitInterval → Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x
  rcases hRotated with ⟨Δ, hΔ_cont, hΔ_ET, hΔ_def⟩
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  refine ⟨Γ, Δ, ?_, hΔ_cont, ?_, ?_, ?_, hΔ_ET, ?_⟩
  · exact BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
  · simpa [Γ] using
      BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
  · simpa [Γ] using
      BHW.os45Figure24IdentityPath_one (d := d) (n := n) x
  · intro t
    exact BHW.forwardTube_subset_extendedTube
      (BHW.os45Figure24IdentityPath_mem_forwardTube
        (d := d) (n := n) hx_ordered t)
  · intro t
    have hInv :
        BHW.complexLorentzAction Λinv (Δ t) =
          BHW.permAct (d := d) τ (Γ t) := by
      rw [hΔ_def t]
      simpa [Γ] using
        hΛinv (BHW.permAct (d := d) τ (Γ t))
    calc
      BHW.sourceOrientedMinkowskiInvariant d n (Δ t)
          = BHW.sourceOrientedMinkowskiInvariant d n
              (BHW.complexLorentzAction Λinv (Δ t)) := by
            exact
              (BHW.sourceOrientedMinkowskiInvariant_complexLorentzAction
                (d := d) (n := n) Λinv (Δ t)).symm
      _ = BHW.sourceOrientedMinkowskiInvariant d n
              (BHW.permAct (d := d) τ (Γ t)) := by
            rw [hInv]
      _ = BHW.sourcePermuteOrientedGram d n τ
              (BHW.sourceOrientedMinkowskiInvariant d n (Γ t)) := by
            exact
              BHW.sourceOrientedMinkowskiInvariant_permAct
                (d := d) (n := n) τ (Γ t)

/-- Figure-2-4 path-stability neighborhood around the equal-time adjacent
support witness.  The adjacent path is the rotated two-plane realization, not
the bare adjacent relabelling of the identity path. -/
theorem swFigure24_adjacentPathStableNeighborhood_exists
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Upath : Set (NPointDomain d n))
      (xfig : NPointDomain d n),
      IsOpen Upath ∧ xfig ∈ Upath ∧
      (∀ k : Fin n, xfig k 0 = 0) ∧
      xfig ∈ BHW.JostSet d n ∧
      BHW.realEmbed xfig ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed (fun k => xfig (τ k)) ∈
        BHW.ExtendedTube d n ∧
      (∀ x ∈ Upath,
        ∃ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ,
          Continuous Δ ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n
                  (BHW.os45Figure24IdentityPath
                    (d := d) (n := n) x t)))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.figure24_adjacentTwoPlaneRotationSupport
      (d := d) (n := n) hd i hi with
    ⟨xfig, xrot, Λfig, hxfig_time0, hxfig_J, hxfig_ET,
      hrot_formula, hxrot_FJ, hΛfig⟩
  have hd1 : 1 ≤ d :=
    Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
  have hxrot_ET : BHW.realEmbed xrot ∈ BHW.ExtendedTube d n :=
    BHW.forwardJostSet_subset_extendedTube (d := d) (n := n) hd1 xrot hxrot_FJ
  have hxfig_swapET :
      BHW.realEmbed (fun k => xfig (τ k)) ∈ BHW.ExtendedTube d n := by
    have hact :
        BHW.complexLorentzAction Λfig (BHW.realEmbed xrot) ∈
          BHW.ExtendedTube d n :=
      BHW.complexLorentzAction_mem_extendedTube (d := d) n
        (z := BHW.realEmbed xrot) Λfig hxrot_ET
    exact hΛfig ▸ hact
  let H : NPointDomain d n × unitInterval → Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
        (BHW.permAct (d := d) τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2))
  have hH_cont : Continuous H := by
    simpa [H] using
      (BHW.continuous_figure24RotatedIdentityPath
        (d := d) (n := n) hd τ)
  have hH_base : ∀ t : unitInterval, H (xfig, t) ∈ BHW.ExtendedTube d n := by
    intro t
    have hpath_zero :
        BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t =
          BHW.realEmbed xfig :=
      BHW.os45Figure24IdentityPath_of_time_zero
        (d := d) (n := n) xfig hxfig_time0 t
    have hperm :
        BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t) =
          BHW.realEmbed (fun k => xfig (τ k)) := by
      ext k μ
      simp [BHW.permAct, hpath_zero, BHW.realEmbed]
    have hH_eq : H (xfig, t) = BHW.realEmbed xrot := by
      dsimp [H]
      rw [hperm]
      exact hrot_formula.symm
    simpa [hH_eq] using hxrot_ET
  rcases BHW.exists_open_nhds_forall_mem_of_compact_parameter
      (X := NPointDomain d n) (Y := unitInterval)
      (Z := Fin n → Fin (d + 1) → ℂ)
      (f := H) hH_cont BHW.isOpen_extendedTube hH_base with
    ⟨Upath, hUpath_open, hxfig_Upath, hUpath_path⟩
  refine ⟨Upath, xfig, hUpath_open, hxfig_Upath, hxfig_time0, hxfig_J,
    hxfig_ET, hxfig_swapET, ?_⟩
  intro x hxUpath
  let Δ : unitInterval → Fin n → Fin (d + 1) → ℂ := fun t => H (x, t)
  refine ⟨Δ, ?_, ?_, ?_⟩
  · exact hH_cont.comp (continuous_const.prodMk continuous_id)
  · intro t
    exact hUpath_path x hxUpath t
  · intro t
    let Γ : Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t
    rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
        (d := d) (n := n) hd with
      ⟨Λinv, hΛinv⟩
    have hInv :
        BHW.complexLorentzAction Λinv (Δ t) =
          BHW.permAct (d := d) τ Γ := by
      simpa [Δ, H, Γ] using
        hΛinv (BHW.permAct (d := d) τ Γ)
    have hLor :
        BHW.sourceMinkowskiGram d n
            (BHW.complexLorentzAction Λinv (Δ t)) =
          BHW.sourceMinkowskiGram d n (Δ t) :=
      BHW.sourceMinkowskiGram_complexLorentzAction
        (d := d) (n := n) Λinv (Δ t)
    calc
      BHW.sourceMinkowskiGram d n (Δ t)
          = BHW.sourceMinkowskiGram d n
              (BHW.complexLorentzAction Λinv (Δ t)) := hLor.symm
      _ = BHW.sourceMinkowskiGram d n (BHW.permAct (d := d) τ Γ) := by
            rw [hInv]
      _ = BHW.sourcePermuteComplexGram n τ
            (BHW.sourceMinkowskiGram d n Γ) := by
            simpa [BHW.permAct] using
              BHW.sourceMinkowskiGram_perm d n τ Γ

/-- Figure-2-4 path-stability neighborhood that preserves the actual rotated
path formula, before the checked geometry is projected to ordinary source Gram
coordinates. -/
theorem swFigure24_adjacentPathStableNeighborhood_rotated_exists
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Upath : Set (NPointDomain d n))
      (xfig : NPointDomain d n),
      IsOpen Upath ∧ xfig ∈ Upath ∧
      (∀ k : Fin n, xfig k 0 = 0) ∧
      xfig ∈ BHW.JostSet d n ∧
      BHW.realEmbed xfig ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed (fun k => xfig (τ k)) ∈
        BHW.ExtendedTube d n ∧
      (∀ x ∈ Upath,
        BHW.OS45Figure24RotatedPathFormulaField
          (d := d) hd n i hi x) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.figure24_adjacentTwoPlaneRotationSupport
      (d := d) (n := n) hd i hi with
    ⟨xfig, xrot, Λfig, hxfig_time0, hxfig_J, hxfig_ET,
      hrot_formula, hxrot_FJ, hΛfig⟩
  have hd1 : 1 ≤ d :=
    Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
  have hxrot_ET : BHW.realEmbed xrot ∈ BHW.ExtendedTube d n :=
    BHW.forwardJostSet_subset_extendedTube (d := d) (n := n) hd1 xrot hxrot_FJ
  have hxfig_swapET :
      BHW.realEmbed (fun k => xfig (τ k)) ∈ BHW.ExtendedTube d n := by
    have hact :
        BHW.complexLorentzAction Λfig (BHW.realEmbed xrot) ∈
          BHW.ExtendedTube d n :=
      BHW.complexLorentzAction_mem_extendedTube (d := d) n
        (z := BHW.realEmbed xrot) Λfig hxrot_ET
    exact hΛfig ▸ hact
  let H : NPointDomain d n × unitInterval → Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
        (BHW.permAct (d := d) τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2))
  have hH_cont : Continuous H := by
    simpa [H] using
      (BHW.continuous_figure24RotatedIdentityPath
        (d := d) (n := n) hd τ)
  have hH_base : ∀ t : unitInterval, H (xfig, t) ∈ BHW.ExtendedTube d n := by
    intro t
    have hpath_zero :
        BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t =
          BHW.realEmbed xfig :=
      BHW.os45Figure24IdentityPath_of_time_zero
        (d := d) (n := n) xfig hxfig_time0 t
    have hperm :
        BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t) =
          BHW.realEmbed (fun k => xfig (τ k)) := by
      ext k μ
      simp [BHW.permAct, hpath_zero, BHW.realEmbed]
    have hH_eq : H (xfig, t) = BHW.realEmbed xrot := by
      dsimp [H]
      rw [hperm]
      exact hrot_formula.symm
    simpa [hH_eq] using hxrot_ET
  rcases BHW.exists_open_nhds_forall_mem_of_compact_parameter
      (X := NPointDomain d n) (Y := unitInterval)
      (Z := Fin n → Fin (d + 1) → ℂ)
      (f := H) hH_cont BHW.isOpen_extendedTube hH_base with
    ⟨Upath, hUpath_open, hxfig_Upath, hUpath_path⟩
  refine ⟨Upath, xfig, hUpath_open, hxfig_Upath, hxfig_time0, hxfig_J,
    hxfig_ET, hxfig_swapET, ?_⟩
  intro x hxUpath
  let Δ : unitInterval → Fin n → Fin (d + 1) → ℂ := fun t => H (x, t)
  refine ⟨Δ, ?_, ?_, ?_⟩
  · exact hH_cont.comp (continuous_const.prodMk continuous_id)
  · intro t
    exact hUpath_path x hxUpath t
  · intro t
    rfl

/-- Figure-2-4 path-stability neighborhood for the deterministic adjacent lift.
The identity path appears only under the ordered-sector hypothesis needed to
keep it inside the forward tube. -/
theorem swFigure24_adjacentPathStableCanonicalLift_exists
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Upath : Set (NPointDomain d n))
      (xfig : NPointDomain d n),
      IsOpen Upath ∧ xfig ∈ Upath ∧
      (∀ k : Fin n, xfig k 0 = 0) ∧
      xfig ∈ BHW.JostSet d n ∧
      BHW.realEmbed xfig ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed (fun k => xfig (τ k)) ∈
        BHW.ExtendedTube d n ∧
      (∀ x ∈ Upath, ∀ t,
        BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ Upath,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) →
        ∃ Γ : unitInterval → Fin n → Fin (d + 1) → ℂ,
          Continuous Γ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n
                (BHW.os45Figure24AdjacentLift
                  (d := d) (n := n) hd τ x t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t)))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentPathStableNeighborhood_rotated_exists
      (d := d) (n := n) hd i hi with
    ⟨Upath, xfig, hUpath_open, hxfig_Upath, hxfig_time0, hxfig_J,
      hxfig_ET, hxfig_swapET, hUpath_rotated⟩
  refine ⟨Upath, xfig, hUpath_open, hxfig_Upath, hxfig_time0, hxfig_J,
    hxfig_ET, hxfig_swapET, ?_, ?_⟩
  · intro x hxUpath t
    rcases hUpath_rotated x hxUpath with
      ⟨Δ, _hΔ_cont, hΔ_ET, hΔ_def⟩
    have hΔ_lift :
        Δ t =
          BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t := by
      simpa [BHW.os45Figure24AdjacentLift, τ] using hΔ_def t
    simpa [hΔ_lift] using hΔ_ET t
  · intro x hxUpath hx_ordered
    let Γ : unitInterval → Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x
    refine ⟨Γ, ?_, ?_, ?_, ?_, ?_⟩
    · exact BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_one (d := d) (n := n) x
    · intro t
      exact BHW.forwardTube_subset_extendedTube
        (BHW.os45Figure24IdentityPath_mem_forwardTube
          (d := d) (n := n) hx_ordered t)
    · intro t
      simpa [Γ, τ] using
        BHW.os45Figure24AdjacentLift_sourceGram
          (d := d) (n := n) hd τ x t

/-- Anchored Figure-2-4 source environment with the compact-open
path-stability field.  The same equal-time witness supplies both the source
domain and the path-stability neighborhood. -/
theorem swFigure24_adjacentHorizontalEnvironmentWithPathStability
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Ufig Upath : Set (NPointDomain d n))
      (x0 : NPointDomain d n),
      IsOpen Ufig ∧ IsOpen Upath ∧
      x0 ∈ Ufig ∧ x0 ∈ Upath ∧
      (∀ k : Fin n, x0 k 0 = 0) ∧
      (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
      (∀ x ∈ Upath,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) →
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t)))) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentPathStableNeighborhood_exists
      (d := d) (n := n) hd i hi with
    ⟨Upath, x0, hUpath_open, hx0Upath, hx0_time0, hx0J, hx0ET,
      hx0SwapET, hUpath_path⟩
  let Ufig : Set (NPointDomain d n) :=
    BHW.JostSet d n ∩
      {x | BHW.realEmbed x ∈ BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n)
            (1 : Equiv.Perm (Fin n))} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ}
  have hswapReal_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed (fun k => x (τ k))) :=
    BHW.continuous_realEmbedNPoint.comp
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hcommon_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) :=
    BHW.continuous_realEmbed_os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  have hUfig_open : IsOpen Ufig := by
    dsimp [Ufig]
    exact (((BHW.isOpen_jostSet (d := d) (n := n)).inter
      (BHW.isOpen_extendedTube.preimage
        (BHW.continuous_realEmbedNPoint (d := d) (n := n)))).inter
      (BHW.isOpen_extendedTube.preimage hswapReal_cont)).inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))).preimage hcommon_cont) |>.inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n) τ).preimage
        hcommon_cont)
  have hx0_common :
      BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x0 = x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45CommonEdgeRealPoint, hx0_time0 k]
    · simp [BHW.os45CommonEdgeRealPoint, hμ]
  have hQsymm_x0 :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed x0) =
        BHW.realEmbed x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hx0_time0 k]
    · simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hμ]
  have hx0_pulled_id :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    change
      BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    simpa [BHW.permAct] using hx0ET
  have hx0_pulled_tau :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    change
      BHW.permAct (d := d) τ.symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    have hperm :
        BHW.permAct (d := d) τ.symm (BHW.realEmbed x0) =
          BHW.realEmbed (fun k => x0 (τ k)) := by
      ext k μ
      simp [BHW.permAct, BHW.realEmbed, τ]
    simpa [hperm] using hx0SwapET
  have hx0Ufig : x0 ∈ Ufig := by
    exact ⟨⟨⟨⟨hx0J, hx0ET⟩, hx0SwapET⟩, hx0_pulled_id⟩,
      hx0_pulled_tau⟩
  refine ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
    hx0_time0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1.1.1.1
  · intro x hx
    exact hx.1.1.1.2
  · intro x hx
    exact hx.1.1.2
  · intro x hx
    exact hx.1.2
  · intro x hx
    exact hx.2
  · intro x hxUpath hx_ordered
    let Γ : unitInterval → Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x
    rcases hUpath_path x hxUpath with
      ⟨Δ, hΔ_cont, hΔ_ET, hΔ_gram⟩
    refine ⟨Γ, Δ, ?_, hΔ_cont, ?_, ?_, ?_, hΔ_ET, ?_⟩
    · exact BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_one (d := d) (n := n) x
    · intro t
      exact BHW.forwardTube_subset_extendedTube
        (BHW.os45Figure24IdentityPath_mem_forwardTube
          (d := d) (n := n) hx_ordered t)
    · intro t
      simpa [Γ, τ] using hΔ_gram t

/-- Anchored Figure-2-4 source environment that preserves the rotated path
formula and the resulting oriented source-invariant path field. -/
theorem swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Ufig Upath : Set (NPointDomain d n))
      (x0 : NPointDomain d n),
      IsOpen Ufig ∧ IsOpen Upath ∧
      x0 ∈ Ufig ∧ x0 ∈ Upath ∧
      (∀ k : Fin n, x0 k 0 = 0) ∧
      (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
      (∀ x ∈ Upath,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) →
        BHW.OS45Figure24RotatedPathFormulaField (d := d) hd n i hi x ∧
        BHW.OS45Figure24OrientedPathField (d := d) n i hi x) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentPathStableNeighborhood_rotated_exists
      (d := d) (n := n) hd i hi with
    ⟨Upath, x0, hUpath_open, hx0Upath, hx0_time0, hx0J, hx0ET,
      hx0SwapET, hUpath_path⟩
  let Ufig : Set (NPointDomain d n) :=
    BHW.JostSet d n ∩
      {x | BHW.realEmbed x ∈ BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n)
            (1 : Equiv.Perm (Fin n))} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ}
  have hswapReal_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed (fun k => x (τ k))) :=
    BHW.continuous_realEmbedNPoint.comp
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hcommon_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) :=
    BHW.continuous_realEmbed_os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  have hUfig_open : IsOpen Ufig := by
    dsimp [Ufig]
    exact (((BHW.isOpen_jostSet (d := d) (n := n)).inter
      (BHW.isOpen_extendedTube.preimage
        (BHW.continuous_realEmbedNPoint (d := d) (n := n)))).inter
      (BHW.isOpen_extendedTube.preimage hswapReal_cont)).inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))).preimage hcommon_cont) |>.inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n) τ).preimage
        hcommon_cont)
  have hx0_common :
      BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x0 = x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45CommonEdgeRealPoint, hx0_time0 k]
    · simp [BHW.os45CommonEdgeRealPoint, hμ]
  have hQsymm_x0 :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed x0) =
        BHW.realEmbed x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hx0_time0 k]
    · simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hμ]
  have hx0_pulled_id :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    change
      BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    simpa [BHW.permAct] using hx0ET
  have hx0_pulled_tau :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    change
      BHW.permAct (d := d) τ.symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    have hperm :
        BHW.permAct (d := d) τ.symm (BHW.realEmbed x0) =
          BHW.realEmbed (fun k => x0 (τ k)) := by
      ext k μ
      simp [BHW.permAct, BHW.realEmbed, τ]
    simpa [hperm] using hx0SwapET
  have hx0Ufig : x0 ∈ Ufig := by
    exact ⟨⟨⟨⟨hx0J, hx0ET⟩, hx0SwapET⟩, hx0_pulled_id⟩,
      hx0_pulled_tau⟩
  refine ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
    hx0_time0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1.1.1.1
  · intro x hx
    exact hx.1.1.1.2
  · intro x hx
    exact hx.1.1.2
  · intro x hx
    exact hx.1.2
  · intro x hx
    exact hx.2
  · intro x hxUpath hx_ordered
    have hRotated :
        BHW.OS45Figure24RotatedPathFormulaField
          (d := d) hd n i hi x :=
      hUpath_path x hxUpath
    exact ⟨hRotated,
      BHW.OS45Figure24OrientedPathField_of_checked_figure24
        (d := d) hd n i hi x hx_ordered hRotated⟩

/-- Source patch for the identity-order adjacent OS45 horizontal edge.  The
selected connected patch has compact closure inside the anchored Figure-2-4
source environment and carries the closure-level horizontal edge and
path-stability fields needed by the branchwise boundary-value step. -/
theorem os45_adjacent_identity_horizontalEdge_sourcePatch
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (Ufig V : Set (NPointDomain d n)) (xseed : NPointDomain d n),
      IsOpen Ufig ∧
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧ xseed ∈ V ∧
      IsCompact (closure V) ∧
      closure V ⊆ Ufig ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
       (∀ x ∈ Ufig, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed (fun k => x (τ k)) ∈
           BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ)) ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            (Equiv.swap i ⟨i.val + 1, hi⟩)) ∧
      (∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
           (1 : Equiv.Perm (Fin n))) ∧
       (∀ x ∈ closure V,
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t))))) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability
      (d := d) (n := n) hd i hi with
    ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
      hx0_time0, hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau, hUpath_path⟩
  let Ubase : Set (NPointDomain d n) := Ufig ∩ Upath
  have hUbase_open : IsOpen Ubase := hUfig_open.inter hUpath_open
  have hx0Ubase : x0 ∈ Ubase := ⟨hx0Ufig, hx0Upath⟩
  rcases BHW.exists_ordered_small_time_perturb_in_adjacent_overlap_of_lt
      (d := d) (n := n) hd i hi Ubase hUbase_open x0 hx0Ubase
      hx0_time0 (by norm_num : (0 : ℝ) < 1) with
    ⟨ε, _hε_pos, _hε_lt, hxseed_Ubase, hxseed_ordered,
      hxseed_swap_ordered⟩
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let ordered : Set (NPointDomain d n) :=
    EuclideanOrderedPositiveTimeSector (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  let swappedOrdered : Set (NPointDomain d n) :=
    {x |
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ}
  let Ufinal : Set (NPointDomain d n) :=
    Ufig ∩ Upath ∩ ordered ∩ swappedOrdered
  have hswappedOrdered_open : IsOpen swappedOrdered := by
    dsimp [swappedOrdered]
    exact (BHW.isOpen_euclideanOrderedPositiveTimeSector
      (d := d) (n := n) τ).preimage
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hUfinal_open : IsOpen Ufinal := by
    dsimp [Ufinal, ordered]
    exact (((hUfig_open.inter hUpath_open).inter
      (BHW.isOpen_euclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))).inter
      hswappedOrdered_open)
  have hxseedUfinal : xseed ∈ Ufinal := by
    exact ⟨⟨⟨hxseed_Ubase.1, hxseed_Ubase.2⟩, hxseed_ordered⟩,
      by simpa [swappedOrdered, τ] using hxseed_swap_ordered⟩
  rcases BHW.exists_connected_open_precompact_subset
      (d := d) (n := n) (x0 := xseed) (U := Ufinal)
      hUfinal_open hxseedUfinal with
    ⟨V, hV_open, hV_connected, hxseedV, hV_compact, hclosureV_Ufinal⟩
  have hV_nonempty : V.Nonempty := ⟨xseed, hxseedV⟩
  have hclosureV_Ufig : closure V ⊆ Ufig := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.1
  have hclosureV_Upath : closure V ⊆ Upath := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.2
  have hclosureV_ordered :
      ∀ x ∈ closure V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.2
  have hclosureV_swap_ordered :
      ∀ x ∈ closure V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact (hclosureV_Ufinal hx).2
  have hV_Ufig : ∀ x ∈ V, x ∈ Ufig := by
    intro x hx
    exact hclosureV_Ufig (subset_closure hx)
  have hV_ordered :
      ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact hclosureV_ordered x (subset_closure hx)
  have hV_swap_ordered :
      ∀ x ∈ V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact hclosureV_swap_ordered x (subset_closure hx)
  have hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n := by
    intro x hx
    exact hUfig_jost x (hV_Ufig x hx)
  have hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_ET x (hV_Ufig x hx)
  have hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_swapET x (hV_Ufig x hx)
  have hV_wick :
      ∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact BHW.wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
      (d := d) (n := n) i hi x (1 : Equiv.Perm (Fin n))
      (hV_ordered x hx) (by simpa [τ] using hV_swap_ordered x hx)
  have hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi := by
    intro x hx
    exact BHW.realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
      (d := d) (n := n) i hi x (hV_ET x hx)
      (by simpa [τ] using hV_swapET x hx)
  have hV_geom_id :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x
      (hV_ordered x hx)
  have hV_geom_tau :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) τ
          (fun k => x (τ k)) := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) τ (fun k => x (τ k))
      (hV_swap_ordered x hx)
  have hV_pulled_id :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hV_Ufig x hx)
  have hV_pulled_tau :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hV_Ufig x hx)
  have hclosureV_pulled_id :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hclosureV_Ufig hx)
  have hclosureV_pulled_tau :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hclosureV_Ufig hx)
  have hclosureV_path :
      ∀ x ∈ closure V,
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t))) := by
    intro x hx
    exact hUpath_path x (hclosureV_Upath hx) (hclosureV_ordered x hx)
  refine ⟨Ufig, V, xseed, hUfig_open, hV_open, hV_connected,
    hV_nonempty, hxseedV, hV_compact, hclosureV_Ufig, ?_, hV_jost,
    hV_ET, ?_, hV_ordered, ?_, hV_wick, hV_real, hV_geom_id, ?_, ?_⟩
  · exact ⟨hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau⟩
  · intro x hx
    simpa [τ] using hV_swapET x hx
  · intro x hx
    simpa [τ] using hV_swap_ordered x hx
  · intro x hx
    simpa [τ] using hV_geom_tau x hx
  · exact ⟨hV_pulled_id, hV_pulled_tau, hclosureV_ordered,
      (by intro x hx; simpa [τ] using hclosureV_swap_ordered x hx),
      hclosureV_pulled_id, hclosureV_pulled_tau, hclosureV_path⟩

/-- Source patch for the identity-order adjacent OS45 horizontal edge, with the
closure-level Figure-2-4 path strengthened to the rotated and oriented source
invariant fields. -/
theorem os45_adjacent_identity_horizontalEdge_sourcePatch_with_orientedPath
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (Ufig V : Set (NPointDomain d n)) (xseed : NPointDomain d n),
      IsOpen Ufig ∧
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧ xseed ∈ V ∧
      IsCompact (closure V) ∧
      closure V ⊆ Ufig ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
       (∀ x ∈ Ufig, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed (fun k => x (τ k)) ∈
           BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ)) ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            (Equiv.swap i ⟨i.val + 1, hi⟩)) ∧
      (∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
           (1 : Equiv.Perm (Fin n))) ∧
       (∀ x ∈ closure V,
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         BHW.OS45Figure24RotatedPathFormulaField (d := d) hd n i hi x) ∧
       (∀ x ∈ closure V,
         BHW.OS45Figure24OrientedPathField (d := d) n i hi x)) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability
      (d := d) (n := n) hd i hi with
    ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
      hx0_time0, hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau, hUpath_path⟩
  let Ubase : Set (NPointDomain d n) := Ufig ∩ Upath
  have hUbase_open : IsOpen Ubase := hUfig_open.inter hUpath_open
  have hx0Ubase : x0 ∈ Ubase := ⟨hx0Ufig, hx0Upath⟩
  rcases BHW.exists_ordered_small_time_perturb_in_adjacent_overlap_of_lt
      (d := d) (n := n) hd i hi Ubase hUbase_open x0 hx0Ubase
      hx0_time0 (by norm_num : (0 : ℝ) < 1) with
    ⟨ε, _hε_pos, _hε_lt, hxseed_Ubase, hxseed_ordered,
      hxseed_swap_ordered⟩
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let ordered : Set (NPointDomain d n) :=
    EuclideanOrderedPositiveTimeSector (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  let swappedOrdered : Set (NPointDomain d n) :=
    {x |
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ}
  let Ufinal : Set (NPointDomain d n) :=
    Ufig ∩ Upath ∩ ordered ∩ swappedOrdered
  have hswappedOrdered_open : IsOpen swappedOrdered := by
    dsimp [swappedOrdered]
    exact (BHW.isOpen_euclideanOrderedPositiveTimeSector
      (d := d) (n := n) τ).preimage
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hUfinal_open : IsOpen Ufinal := by
    dsimp [Ufinal, ordered]
    exact (((hUfig_open.inter hUpath_open).inter
      (BHW.isOpen_euclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))).inter
      hswappedOrdered_open)
  have hxseedUfinal : xseed ∈ Ufinal := by
    exact ⟨⟨⟨hxseed_Ubase.1, hxseed_Ubase.2⟩, hxseed_ordered⟩,
      by simpa [swappedOrdered, τ] using hxseed_swap_ordered⟩
  rcases BHW.exists_connected_open_precompact_subset
      (d := d) (n := n) (x0 := xseed) (U := Ufinal)
      hUfinal_open hxseedUfinal with
    ⟨V, hV_open, hV_connected, hxseedV, hV_compact, hclosureV_Ufinal⟩
  have hV_nonempty : V.Nonempty := ⟨xseed, hxseedV⟩
  have hclosureV_Ufig : closure V ⊆ Ufig := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.1
  have hclosureV_Upath : closure V ⊆ Upath := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.2
  have hclosureV_ordered :
      ∀ x ∈ closure V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.2
  have hclosureV_swap_ordered :
      ∀ x ∈ closure V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact (hclosureV_Ufinal hx).2
  have hV_Ufig : ∀ x ∈ V, x ∈ Ufig := by
    intro x hx
    exact hclosureV_Ufig (subset_closure hx)
  have hV_ordered :
      ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact hclosureV_ordered x (subset_closure hx)
  have hV_swap_ordered :
      ∀ x ∈ V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact hclosureV_swap_ordered x (subset_closure hx)
  have hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n := by
    intro x hx
    exact hUfig_jost x (hV_Ufig x hx)
  have hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_ET x (hV_Ufig x hx)
  have hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_swapET x (hV_Ufig x hx)
  have hV_wick :
      ∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact BHW.wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
      (d := d) (n := n) i hi x (1 : Equiv.Perm (Fin n))
      (hV_ordered x hx) (by simpa [τ] using hV_swap_ordered x hx)
  have hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi := by
    intro x hx
    exact BHW.realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
      (d := d) (n := n) i hi x (hV_ET x hx)
      (by simpa [τ] using hV_swapET x hx)
  have hV_geom_id :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x
      (hV_ordered x hx)
  have hV_geom_tau :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) τ
          (fun k => x (τ k)) := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) τ (fun k => x (τ k))
      (hV_swap_ordered x hx)
  have hV_pulled_id :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hV_Ufig x hx)
  have hV_pulled_tau :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hV_Ufig x hx)
  have hclosureV_pulled_id :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hclosureV_Ufig hx)
  have hclosureV_pulled_tau :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hclosureV_Ufig hx)
  have hclosureV_rotated :
      ∀ x ∈ closure V,
        BHW.OS45Figure24RotatedPathFormulaField
          (d := d) hd n i hi x := by
    intro x hx
    exact (hUpath_path x (hclosureV_Upath hx)
      (hclosureV_ordered x hx)).1
  have hclosureV_oriented :
      ∀ x ∈ closure V,
        BHW.OS45Figure24OrientedPathField (d := d) n i hi x := by
    intro x hx
    exact (hUpath_path x (hclosureV_Upath hx)
      (hclosureV_ordered x hx)).2
  refine ⟨Ufig, V, xseed, hUfig_open, hV_open, hV_connected,
    hV_nonempty, hxseedV, hV_compact, hclosureV_Ufig, ?_, hV_jost,
    hV_ET, ?_, hV_ordered, ?_, hV_wick, hV_real, hV_geom_id, ?_, ?_⟩
  · exact ⟨hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau⟩
  · intro x hx
    simpa [τ] using hV_swapET x hx
  · intro x hx
    simpa [τ] using hV_swap_ordered x hx
  · intro x hx
    simpa [τ] using hV_geom_tau x hx
  · exact ⟨hV_pulled_id, hV_pulled_tau, hclosureV_ordered,
      (by intro x hx; simpa [τ] using hclosureV_swap_ordered x hx),
      hclosureV_pulled_id, hclosureV_pulled_tau, hclosureV_rotated,
      hclosureV_oriented⟩

/-- Canonical two-point Figure-2-4 source patch for the adjacent OS45
horizontal edge.  Besides the ordinary source-patch fields, this packet stores
the contact point on the identity common edge and the deterministic adjacent
Figure-2-4 lift used by the scalar-source descent. -/
structure OS45Figure24CanonicalSourcePatchData
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) where
  τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
  Ufig : Set (NPointDomain d n)
  V : Set (NPointDomain d n)
  xseed : NPointDomain d n
  Ufig_open : IsOpen Ufig
  Ufig_jost : ∀ x, x ∈ Ufig → x ∈ BHW.JostSet d n
  Ufig_ET : ∀ x, x ∈ Ufig → BHW.realEmbed x ∈ BHW.ExtendedTube d n
  Ufig_swapET :
    ∀ x, x ∈ Ufig →
      BHW.realEmbed (fun k => x (τ k)) ∈ BHW.ExtendedTube d n
  Ufig_pulled_id :
    ∀ x, x ∈ Ufig →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) 1
  Ufig_pulled_tau :
    ∀ x, x ∈ Ufig →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ
  V_open : IsOpen V
  V_connected : IsConnected V
  V_nonempty : V.Nonempty
  xseed_mem : xseed ∈ V
  xcontact : NPointDomain d n
  xcontact_mem : xcontact ∈ V
  xcontact_commonEdge :
    xcontact =
      BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 xseed
  closureV_compact : IsCompact (closure V)
  closureV_sub_Ufig : closure V ⊆ Ufig
  V_jost : ∀ x, x ∈ V → x ∈ BHW.JostSet d n
  V_ET : ∀ x, x ∈ V → BHW.realEmbed x ∈ BHW.ExtendedTube d n
  V_swapET :
    ∀ x, x ∈ V →
      BHW.realEmbed (fun k => x (τ k)) ∈ BHW.ExtendedTube d n
  V_ordered :
    ∀ x, x ∈ V →
      x ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  V_swap_ordered :
    ∀ x, x ∈ V →
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ
  V_wick :
    ∀ x, x ∈ V →
      (fun k => wickRotatePoint (x k)) ∈
        adjacentOS45WickSeedDomain (d := d) (n := n) i hi
          (1 : Equiv.Perm (Fin n))
  V_real :
    ∀ x, x ∈ V →
      BHW.realEmbed x ∈ adjacentOS45RealEdgeDomain (d := d) (n := n) i hi
  V_geom_id :
    ∀ x, x ∈ V →
      BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) x
  V_geom_tau :
    ∀ x, x ∈ V →
      BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) τ
        (fun k => x (τ k))
  V_pulled_id :
    ∀ x, x ∈ V →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) 1
  V_pulled_tau :
    ∀ x, x ∈ V →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ
  closure_ordered :
    ∀ x, x ∈ closure V →
      x ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  closure_swap_ordered :
    ∀ x, x ∈ closure V →
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ
  closure_pulled_id :
    ∀ x, x ∈ closure V →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) 1
  closure_pulled_tau :
    ∀ x, x ∈ closure V →
      BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ
  adjLift_mem_extendedTube :
    ∀ x, x ∈ V → ∀ t,
      BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
        BHW.ExtendedTube d n
  figPath_closure :
    ∀ x, x ∈ closure V →
      let y :=
        BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x
      ∃ Γ : unitInterval → Fin n → Fin (d + 1) → ℂ,
        Continuous Γ ∧
        Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
        Γ (1 : unitInterval) =
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed y) ∧
        (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
        (∀ t,
          BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
            BHW.ExtendedTube d n) ∧
        (∀ t,
          BHW.sourceMinkowskiGram d n
              (BHW.os45Figure24AdjacentLift
                (d := d) (n := n) hd τ x t) =
            BHW.sourcePermuteComplexGram n τ
              (BHW.sourceMinkowskiGram d n (Γ t)))

/-- Canonical Figure-2-4 source patch together with the oriented determinant
path data needed by the strict OS II adjacent `S'_n` corridor. -/
structure OS45Figure24OrientedCanonicalSourcePatchData
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) where
  toCanonical :
    BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi
  rotatedPath_closure :
    ∀ x, x ∈ closure toCanonical.V →
      BHW.OS45Figure24RotatedPathFormulaField (d := d) hd n i hi x
  orientedPath_closure :
    ∀ x, x ∈ closure toCanonical.V →
      BHW.OS45Figure24OrientedPathField (d := d) n i hi x

/-- Existence of the canonical two-point Figure-2-4 source patch with the
oriented path field.  The construction uses the checked two-point perturbation
segment, so the compact patch contains both the ordered seed and its identity
common-edge contact. -/
theorem exists_os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ _P : BHW.OS45Figure24OrientedCanonicalSourcePatchData
      (d := d) hd n i hi, True := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability
      (d := d) (n := n) hd i hi with
    ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
      hx0_time0, hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau, hUpath_path⟩
  let Ubase : Set (NPointDomain d n) := Ufig ∩ Upath
  have hUbase_open : IsOpen Ubase := hUfig_open.inter hUpath_open
  have hx0Ubase : x0 ∈ Ubase := ⟨hx0Ufig, hx0Upath⟩
  rcases BHW.exists_ordered_small_time_perturb_with_commonEdge_segment_in_adjacent_overlap_of_lt
      (d := d) (n := n) hd i hi Ubase hUbase_open x0 hx0Ubase
      hx0_time0 (by norm_num : (0 : ℝ) < 1) with
    ⟨ε, _hε_pos, _hε_lt, hxseed_Ubase, _hxcontact_Ubase,
      hxseed_ordered, hxseed_swap_ordered, _hxcontact_ordered,
      _hxcontact_swap_ordered, hsegment_base⟩
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let xcontact : NPointDomain d n :=
    BHW.os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) xseed
  let ordered : Set (NPointDomain d n) :=
    EuclideanOrderedPositiveTimeSector (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  let swappedOrdered : Set (NPointDomain d n) :=
    {x |
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ}
  let Ufinal : Set (NPointDomain d n) :=
    Ufig ∩ Upath ∩ ordered ∩ swappedOrdered
  have hswappedOrdered_open : IsOpen swappedOrdered := by
    dsimp [swappedOrdered]
    exact (BHW.isOpen_euclideanOrderedPositiveTimeSector
      (d := d) (n := n) τ).preimage
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hUfinal_open : IsOpen Ufinal := by
    dsimp [Ufinal, ordered]
    exact (((hUfig_open.inter hUpath_open).inter
      (BHW.isOpen_euclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))).inter
      hswappedOrdered_open)
  have hsegment_final :
      segment ℝ xseed xcontact ⊆ Ufinal := by
    intro y hy
    have hybase := hsegment_base hy
    exact ⟨⟨⟨hybase.1.1.1, hybase.1.1.2⟩, hybase.1.2⟩,
      hybase.2⟩
  rcases BHW.exists_connected_open_precompact_subset_pair
      (d := d) (n := n) (U := Ufinal)
      hUfinal_open hsegment_final with
    ⟨V, hV_open, hV_connected, hxseedV, hxcontactV, hV_compact,
      hclosureV_Ufinal⟩
  have hV_nonempty : V.Nonempty := ⟨xseed, hxseedV⟩
  have hclosureV_Ufig : closure V ⊆ Ufig := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.1
  have hclosureV_Upath : closure V ⊆ Upath := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.2
  have hclosureV_ordered :
      ∀ x ∈ closure V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.2
  have hclosureV_swap_ordered :
      ∀ x ∈ closure V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact (hclosureV_Ufinal hx).2
  have hV_Ufig : ∀ x ∈ V, x ∈ Ufig := by
    intro x hx
    exact hclosureV_Ufig (subset_closure hx)
  have hV_ordered :
      ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact hclosureV_ordered x (subset_closure hx)
  have hV_swap_ordered :
      ∀ x ∈ V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact hclosureV_swap_ordered x (subset_closure hx)
  have hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n := by
    intro x hx
    exact hUfig_jost x (hV_Ufig x hx)
  have hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_ET x (hV_Ufig x hx)
  have hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_swapET x (hV_Ufig x hx)
  have hV_wick :
      ∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact BHW.wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
      (d := d) (n := n) i hi x (1 : Equiv.Perm (Fin n))
      (hV_ordered x hx) (by simpa [τ] using hV_swap_ordered x hx)
  have hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi := by
    intro x hx
    exact BHW.realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
      (d := d) (n := n) i hi x (hV_ET x hx)
      (by simpa [τ] using hV_swapET x hx)
  have hV_geom_id :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x
      (hV_ordered x hx)
  have hV_geom_tau :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) τ
          (fun k => x (τ k)) := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) τ (fun k => x (τ k))
      (hV_swap_ordered x hx)
  have hV_pulled_id :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hV_Ufig x hx)
  have hV_pulled_tau :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hV_Ufig x hx)
  have hclosureV_pulled_id :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hclosureV_Ufig hx)
  have hclosureV_pulled_tau :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hclosureV_Ufig hx)
  have hV_adjLift :
      ∀ x ∈ V, ∀ t,
        BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
          BHW.ExtendedTube d n := by
    intro x hx t
    rcases (hUpath_path x (hclosureV_Upath (subset_closure hx))
        (hV_ordered x hx)).1 with
      ⟨Δ, _hΔ_cont, hΔ_ET, hΔ_def⟩
    have hΔ_lift :
        Δ t =
          BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t := by
      simpa [BHW.os45Figure24AdjacentLift, τ] using hΔ_def t
    simpa [hΔ_lift] using hΔ_ET t
  have hclosureV_figPath :
      ∀ x, x ∈ closure V →
        let y :=
          BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x
        ∃ Γ : unitInterval → Fin n → Fin (d + 1) → ℂ,
          Continuous Γ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed y) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
              BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n
                (BHW.os45Figure24AdjacentLift
                  (d := d) (n := n) hd τ x t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t))) := by
    intro x hx
    let Γ : unitInterval → Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x
    refine ⟨Γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_one (d := d) (n := n) x
    · intro t
      exact BHW.forwardTube_subset_extendedTube
        (BHW.os45Figure24IdentityPath_mem_forwardTube
          (d := d) (n := n) (hclosureV_ordered x hx) t)
    · intro t
      rcases (hUpath_path x (hclosureV_Upath hx)
          (hclosureV_ordered x hx)).1 with
        ⟨Δ, _hΔ_cont, hΔ_ET, hΔ_def⟩
      have hΔ_lift :
          Δ t =
            BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t := by
        simpa [BHW.os45Figure24AdjacentLift, τ] using hΔ_def t
      simpa [hΔ_lift] using hΔ_ET t
    · intro t
      simpa [Γ, τ] using
        BHW.os45Figure24AdjacentLift_sourceGram
          (d := d) (n := n) hd τ x t
  have hclosureV_rotated :
      ∀ x, x ∈ closure V →
        BHW.OS45Figure24RotatedPathFormulaField (d := d) hd n i hi x := by
    intro x hx
    exact (hUpath_path x (hclosureV_Upath hx)
      (hclosureV_ordered x hx)).1
  have hclosureV_oriented :
      ∀ x, x ∈ closure V →
        BHW.OS45Figure24OrientedPathField (d := d) n i hi x := by
    intro x hx
    exact (hUpath_path x (hclosureV_Upath hx)
      (hclosureV_ordered x hx)).2
  let P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi :=
    { τ := τ
      τ_eq := rfl
      Ufig := Ufig
      V := V
      xseed := xseed
      Ufig_open := hUfig_open
      Ufig_jost := hUfig_jost
      Ufig_ET := hUfig_ET
      Ufig_swapET := hUfig_swapET
      Ufig_pulled_id := hUfig_pulled_id
      Ufig_pulled_tau := hUfig_pulled_tau
      V_open := hV_open
      V_connected := hV_connected
      V_nonempty := hV_nonempty
      xseed_mem := hxseedV
      xcontact := xcontact
      xcontact_mem := hxcontactV
      xcontact_commonEdge := rfl
      closureV_compact := hV_compact
      closureV_sub_Ufig := hclosureV_Ufig
      V_jost := hV_jost
      V_ET := hV_ET
      V_swapET := hV_swapET
      V_ordered := hV_ordered
      V_swap_ordered := hV_swap_ordered
      V_wick := hV_wick
      V_real := hV_real
      V_geom_id := hV_geom_id
      V_geom_tau := hV_geom_tau
      V_pulled_id := hV_pulled_id
      V_pulled_tau := hV_pulled_tau
      closure_ordered := hclosureV_ordered
      closure_swap_ordered := hclosureV_swap_ordered
      closure_pulled_id := hclosureV_pulled_id
      closure_pulled_tau := hclosureV_pulled_tau
      adjLift_mem_extendedTube := hV_adjLift
      figPath_closure := hclosureV_figPath }
  exact
    ⟨{ toCanonical := P
       rotatedPath_closure := hclosureV_rotated
       orientedPath_closure := hclosureV_oriented },
      trivial⟩

/-- Canonical two-point Figure-2-4 source patch with the oriented path field,
chosen from the existence theorem above. -/
noncomputable def os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    BHW.OS45Figure24OrientedCanonicalSourcePatchData
      (d := d) hd n i hi :=
  Classical.choose
    (BHW.exists_os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
      (d := d) (n := n) hd i hi)

/-- Canonical two-point Figure-2-4 source patch for the adjacent OS45
horizontal edge, projected from the stronger oriented packet. -/
noncomputable def os45_adjacent_identity_canonicalSourcePatch
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi :=
  (BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
    (d := d) (n := n) hd i hi).toCanonical

/-- Canonical Figure-2-4 source patch used by the adjacent source corridor.
It is the canonical packet's `V` when `2 ≤ d`, expressed as a proof-irrelevant
union over the active dimension hypothesis. -/
noncomputable def os45Figure24SourcePatch
    [NeZero d]
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    Set (NPointDomain d n) :=
  ⋃ hd : 2 ≤ d,
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V

/-- Under the theorem-2 dimension hypothesis, the public source patch is the
canonical packet's selected source patch. -/
theorem os45Figure24SourcePatch_eq_canonical
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    BHW.os45Figure24SourcePatch (d := d) n i hi =
      (BHW.os45_adjacent_identity_canonicalSourcePatch
        (d := d) hd i hi).V := by
  classical
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨hd', hx'⟩
    have hhd : hd' = hd := Subsingleton.elim hd' hd
    simpa [BHW.os45Figure24SourcePatch, hhd] using hx'
  · intro hx
    exact Set.mem_iUnion.mpr ⟨hd, hx⟩

/-- The canonical Figure-2-4 source patch is open. -/
theorem isOpen_os45Figure24SourcePatch
    [NeZero d]
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    IsOpen (BHW.os45Figure24SourcePatch (d := d) n i hi) := by
  classical
  rw [BHW.os45Figure24SourcePatch]
  exact isOpen_iUnion fun hd =>
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V_open

/-- The canonical Figure-2-4 source patch is nonempty in the active dimension
range. -/
theorem nonempty_os45Figure24SourcePatch
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    (BHW.os45Figure24SourcePatch (d := d) n i hi).Nonempty := by
  classical
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  exact
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V_nonempty

/-- Every point of the canonical Figure-2-4 source patch is Jost. -/
theorem os45Figure24SourcePatch_jost
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    BHW.os45Figure24SourcePatch (d := d) n i hi ⊆
      BHW.JostSet d n := by
  classical
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  exact
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V_jost

/-- The real embedding of every point of the canonical Figure-2-4 source patch
lies in the ordinary extended tube. -/
theorem os45Figure24SourcePatch_realEmbed_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
  classical
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  exact
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V_ET

/-- The adjacent swapped real embedding of every point of the canonical
Figure-2-4 source patch lies in the ordinary extended tube. -/
theorem os45Figure24SourcePatch_swapRealEmbed_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      BHW.realEmbed
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n := by
  classical
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  intro x hx
  simpa [P.τ_eq] using P.V_swapET x hx

/-- The canonical Figure-2-4 source patch lies in the identity ordered
Euclidean time sector. -/
theorem os45Figure24SourcePatch_ordered
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      x ∈ EuclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) := by
  classical
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  exact
    (BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi).V_ordered

/-- The adjacent relabelled canonical Figure-2-4 source patch lies in the
adjacent ordered Euclidean time sector. -/
theorem os45Figure24SourcePatch_swap_ordered
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector
          (d := d) (n := n) (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  classical
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  intro x hx
  simpa [P.τ_eq] using P.V_swap_ordered x hx

/-- The Wick rotation of every point of the canonical Figure-2-4 source patch
lies in the ordinary extended tube. -/
theorem os45Figure24SourcePatch_wick_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n := by
  intro x hx
  have hft_eq : BHW.ForwardTube d n = _root_.ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hroot :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
      (BHW.os45Figure24SourcePatch_ordered
        (d := d) hd n i hi x hx)
  have hBHW :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        BHW.ForwardTube d n := by
    simpa [hft_eq] using hroot
  exact BHW.forwardTube_subset_extendedTube (by simpa using hBHW)

/-- The adjacent-permuted real embedding of every point of the canonical
Figure-2-4 source patch lies in the ordinary extended tube. -/
theorem os45Figure24SourcePatch_permAct_realEmbed_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
        (BHW.realEmbed x) ∈ BHW.ExtendedTube d n := by
  intro x hx
  simpa [BHW.permAct_realEmbed] using
    (BHW.os45Figure24SourcePatch_swapRealEmbed_mem_extendedTube
      (d := d) hd n i hi x hx)

/-- The deterministic adjacent Figure-2-4 lift of any source-patch point stays
in the ordinary extended tube. -/
theorem os45Figure24SourcePatch_adjLift_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∀ x ∈ BHW.os45Figure24SourcePatch (d := d) n i hi,
      ∀ t,
        BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd τ x t ∈
          BHW.ExtendedTube d n := by
  classical
  dsimp
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi
  rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
  intro x hx t
  simpa [P.τ_eq] using P.adjLift_mem_extendedTube x hx t

/-- The closure of the canonical Figure-2-4 source patch carries the oriented
Figure-2-4 path field. -/
theorem os45Figure24SourcePatch_closure_orientedPath
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ x ∈ closure (BHW.os45Figure24SourcePatch (d := d) n i hi),
      BHW.OS45Figure24OrientedPathField (d := d) n i hi x := by
  classical
  let Poriented :=
    BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
      (d := d) (n := n) hd i hi
  have hsource :
      BHW.os45Figure24SourcePatch (d := d) n i hi =
        Poriented.toCanonical.V :=
    BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi
  intro x hx
  exact Poriented.orientedPath_closure x (by simpa [hsource] using hx)

/-- Ambient Figure-2-4 source environment containing the closure of the
canonical source patch, with the source-domain fields used by the branch
suppliers. -/
theorem os45Figure24SourcePatch_sourceEnvironment
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ Ufig : Set (NPointDomain d n),
      IsOpen Ufig ∧
      closure (BHW.os45Figure24SourcePatch (d := d) n i hi) ⊆ Ufig ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
       (∀ x ∈ Ufig, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed (fun k => x (τ k)) ∈
           BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
             (1 : Equiv.Perm (Fin n)) x) ∈
           BHW.os45PulledRealBranchDomain
             (d := d) (n := n) (1 : Equiv.Perm (Fin n))) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
             (1 : Equiv.Perm (Fin n)) x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ)) := by
  classical
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi
  refine ⟨P.Ufig, P.Ufig_open, ?_, ?_⟩
  · rw [BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi]
    exact P.closureV_sub_Ufig
  · exact ⟨P.Ufig_jost, P.Ufig_ET,
      (by
        intro x hx
        simpa [P.τ_eq] using P.Ufig_swapET x hx),
      P.Ufig_pulled_id,
      (by
        intro x hx
        simpa [P.τ_eq] using P.Ufig_pulled_tau x hx)⟩

/-- Point-permutation homeomorphism from the canonical source patch to the
`π`-labelled real patch. -/
noncomputable def os45SourcePermutationHomeomorph
    (d n : Nat)
    (π : Equiv.Perm (Fin n)) :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toEquiv :=
    { toFun := fun u k μ => u (π.symm k) μ
      invFun := fun x k μ => x (π k) μ
      left_inv := by
        intro u
        ext k μ
        simp
      right_inv := by
        intro x
        ext k μ
        simp }
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- The `π`-labelled compact real patch associated to the canonical
Figure-2-4 source patch. -/
def os45Figure24CompactRealPatch
    [NeZero d]
    (n : Nat)
    (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    Set (NPointDomain d n) :=
  BHW.os45SourcePermutationHomeomorph d n π ''
    BHW.os45Figure24SourcePatch (d := d) (n := n) i hi

/-- The `π`-labelled Figure-2-4 real patch is open. -/
theorem os45Figure24CompactRealPatch_open
    [NeZero d]
    (n : Nat)
    (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    IsOpen
      (BHW.os45Figure24CompactRealPatch (d := d) n i hi π) := by
  rw [BHW.os45Figure24CompactRealPatch]
  exact
    (BHW.os45SourcePermutationHomeomorph d n π).isOpenMap _
      (BHW.isOpen_os45Figure24SourcePatch
        (d := d) (n := n) i hi)

/-- The `π`-labelled Figure-2-4 real patch is nonempty in the active
dimension range. -/
theorem os45Figure24CompactRealPatch_nonempty
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat)
    (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    (BHW.os45Figure24CompactRealPatch (d := d) n i hi π).Nonempty := by
  rcases BHW.nonempty_os45Figure24SourcePatch
      (d := d) hd n i hi with ⟨u, hu⟩
  exact
    ⟨BHW.os45SourcePermutationHomeomorph d n π u,
      u, hu, rfl⟩

/-- The `π`-labelled Figure-2-4 real patch contains the permuted checked
common-edge contact point. -/
theorem os45Figure24CompactRealPatch_commonEdge_contact
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat)
    (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    ∃ x0 ∈ BHW.os45Figure24CompactRealPatch (d := d) n i hi π,
      ∃ u ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi,
        (fun k => x0 (π k)) =
          BHW.os45CommonEdgeRealPoint
            (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u := by
  classical
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) hd i hi
  have hPsource :
      P.V =
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi := by
    exact
      (BHW.os45Figure24SourcePatch_eq_canonical
        (d := d) hd n i hi).symm
  let u := P.xseed
  let xcontact := P.xcontact
  have hu : u ∈
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi := by
    simpa [u, hPsource] using P.xseed_mem
  have hxcontact : xcontact ∈
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi := by
    simpa [xcontact, hPsource] using P.xcontact_mem
  have hcontact :
      xcontact =
        BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u := by
    simpa [xcontact, u] using P.xcontact_commonEdge
  refine
    ⟨BHW.os45SourcePermutationHomeomorph d n π xcontact,
      ⟨xcontact, hxcontact, rfl⟩, u, hu, ?_⟩
  ext k μ
  simp [BHW.os45SourcePermutationHomeomorph, hcontact]

/-- The `π`-labelled Figure-2-4 real patch stays in the Jost set. -/
theorem os45Figure24CompactRealPatch_jost
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    BHW.os45Figure24CompactRealPatch (d := d) n i hi π ⊆
      BHW.JostSet d n := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  simpa [BHW.os45SourcePermutationHomeomorph] using
    BHW.jostSet_permutation_invariant
      (d := d) (n := n) π.symm
      (BHW.os45Figure24SourcePatch_jost
        (d := d) hd n i hi hu)

/-- The `π`-labelled Figure-2-4 real patch is contained in the `π`
permuted extended-tube sector. -/
theorem os45Figure24CompactRealPatch_left_sector
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    ∀ x, x ∈ BHW.os45Figure24CompactRealPatch (d := d) n i hi π →
      BHW.realEmbed x ∈ BHW.permutedExtendedTubeSector d n π := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  rw [BHW.permutedExtendedTubeSector]
  change
    (fun k =>
      BHW.realEmbed
        ((BHW.os45SourcePermutationHomeomorph d n π) u) (π k)) ∈
      BHW.ExtendedTube d n
  have hfun :
      (fun k =>
        BHW.realEmbed
          ((BHW.os45SourcePermutationHomeomorph d n π) u) (π k)) =
        BHW.realEmbed u := by
    ext k μ
    simp [BHW.os45SourcePermutationHomeomorph, BHW.realEmbed]
  rw [hfun]
  exact
    BHW.os45Figure24SourcePatch_realEmbed_mem_extendedTube
      (d := d) hd n i hi u hu

/-- The `π`-labelled Figure-2-4 real patch is contained in the adjacent
`π * τ` permuted extended-tube sector. -/
theorem os45Figure24CompactRealPatch_right_sector
    [NeZero d]
    (hd : 2 ≤ d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n)) :
    ∀ x, x ∈ BHW.os45Figure24CompactRealPatch (d := d) n i hi π →
      BHW.realEmbed x ∈
        BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  rw [BHW.permutedExtendedTubeSector]
  change
    (fun k =>
      BHW.realEmbed
        ((BHW.os45SourcePermutationHomeomorph d n π) u)
        ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
      BHW.ExtendedTube d n
  have hfun :
      (fun k =>
        BHW.realEmbed
          ((BHW.os45SourcePermutationHomeomorph d n π) u)
          ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
        BHW.realEmbed
          (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
    ext k μ
    simp [BHW.os45SourcePermutationHomeomorph, BHW.realEmbed,
      Equiv.Perm.mul_apply]
  rw [hfun]
  exact
    BHW.os45Figure24SourcePatch_swapRealEmbed_mem_extendedTube
      (d := d) hd n i hi u hu

/-- Pull a compactly supported Schwartz test on the `π`-labelled Figure-2-4
real patch back to the canonical source patch.  This is only the finite
coordinate change of variables; it does not prove branch equality. -/
theorem os45CompactRealPatch_pullbackSchwartz
    [NeZero d]
    (n : Nat)
    (A : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (i : Fin n) (hi : i.val + 1 < n)
    (π : Equiv.Perm (Fin n))
    (φ : SchwartzMap (NPointDomain d n) ℂ)
    (hφ_comp :
      HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_supp :
      tsupport (φ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24CompactRealPatch (d := d) n i hi π) :
    ∃ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) ∧
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ∧
      (∀ u,
        ψ u =
          φ (BHW.os45SourcePermutationHomeomorph d n π u)) ∧
      (∫ x : NPointDomain d n,
          A (fun k => BHW.realEmbed x (π k)) * φ x)
        =
       ∫ u : NPointDomain d n,
          A (BHW.realEmbed u) * ψ u ∧
      (∫ x : NPointDomain d n,
          A (fun k => BHW.realEmbed x
            ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) * φ x)
        =
       ∫ u : NPointDomain d n,
          A (BHW.realEmbed
            (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * ψ u := by
  let ψ : SchwartzNPoint d n :=
    BHW.permuteSchwartz (d := d) π.symm φ
  have hψ_apply :
      ∀ u,
        ψ u =
          φ (BHW.os45SourcePermutationHomeomorph d n π u) := by
    intro u
    simp [ψ, BHW.os45SourcePermutationHomeomorph]
  have hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ) :=
    BHW.permuteSchwartz_hasCompactSupport
      (d := d) π.symm φ hφ_comp
  have hψ_supp :
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi := by
    intro u hu
    have hpre :
        (((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) π.symm).toContinuousLinearEquiv :
            NPointDomain d n ≃L[ℝ] NPointDomain d n).toHomeomorph u) ∈
          tsupport (φ : NPointDomain d n → ℂ) := by
      rw [BHW.tsupport_permuteSchwartz (d := d) π.symm φ] at hu
      exact hu
    have hHu :
        BHW.os45SourcePermutationHomeomorph d n π u ∈
          tsupport (φ : NPointDomain d n → ℂ) := by
      simpa [BHW.os45SourcePermutationHomeomorph] using hpre
    rcases hφ_supp hHu with ⟨v, hv, hv_eq⟩
    have hvu : v = u :=
      (BHW.os45SourcePermutationHomeomorph d n π).injective hv_eq
    simpa [hvu] using hv
  have hleft_pullback :
      (∫ x : NPointDomain d n,
          A (fun k => BHW.realEmbed x (π k)) * φ x)
        =
       ∫ u : NPointDomain d n,
          A (BHW.realEmbed u) * ψ u := by
    let h : NPointDomain d n → ℂ := fun x =>
      A (fun k => BHW.realEmbed x (π k)) * φ x
    have hp :=
      (BHW.integral_perm_eq_self (d := d) (n := n) π.symm h).symm
    have harg : ∀ x : NPointDomain d n,
        (fun k => BHW.realEmbed (fun k => x (π.symm k)) (π k)) =
          BHW.realEmbed x := by
      intro x
      ext k μ
      simp [BHW.realEmbed]
    simpa [h, ψ, BHW.os45SourcePermutationHomeomorph, harg] using hp
  have hright_pullback :
      (∫ x : NPointDomain d n,
          A (fun k => BHW.realEmbed x
            ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) * φ x)
        =
       ∫ u : NPointDomain d n,
          A (BHW.realEmbed
            (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * ψ u := by
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let h : NPointDomain d n → ℂ := fun x =>
      A (fun k => BHW.realEmbed x ((π * τ) k)) * φ x
    have hp :=
      (BHW.integral_perm_eq_self (d := d) (n := n) π.symm h).symm
    have harg : ∀ x : NPointDomain d n,
        (fun k =>
          BHW.realEmbed (fun k => x (π.symm k)) (π (τ k))) =
          BHW.realEmbed (fun k => x (τ k)) := by
      intro x
      ext k μ
      simp [BHW.realEmbed]
    simpa [h, ψ, τ, BHW.os45SourcePermutationHomeomorph, harg,
      Equiv.Perm.mul_apply] using hp
  exact
    ⟨ψ, hψ_comp, hψ_supp, hψ_apply,
      hleft_pullback, hright_pullback⟩

end BHW
