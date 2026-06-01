import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BranchPullback
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexDensity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ}

/-- Add a real imaginary edge direction to a horizontal real edge point. -/
def realEdgeAddImag
    (y η : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => (y k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I

theorem realEdgeAddImag_zero
    (y η : NPointDomain d n) :
    realEdgeAddImag (d := d) (n := n) y η 0 = BHW.realEmbed y := by
  ext k μ
  simp [realEdgeAddImag, BHW.realEmbed]

/-- Continuity of the real-edge imaginary perturbation under continuous
parameters. -/
theorem continuous_realEdgeAddImag_of_continuous
    {α : Type*} [TopologicalSpace α]
    {Y Η : α → NPointDomain d n} {eps : α → ℝ}
    (hY : Continuous Y) (hΗ : Continuous Η) (heps : Continuous eps) :
    Continuous
      (fun p : α => realEdgeAddImag (d := d) (n := n) (Y p) (Η p) (eps p)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hy : Continuous (fun p : α => Y p k μ) :=
    (continuous_apply μ).comp ((continuous_apply k).comp hY)
  have hη : Continuous (fun p : α => Η p k μ) :=
    (continuous_apply μ).comp ((continuous_apply k).comp hΗ)
  exact (Complex.continuous_ofReal.comp hy).add
    (((Complex.continuous_ofReal.comp heps).mul
      (Complex.continuous_ofReal.comp hη)).mul continuous_const)

theorem continuous_realEdgeAddImag :
    Continuous
      (fun p : (NPointDomain d n × NPointDomain d n) × ℝ =>
        realEdgeAddImag (d := d) (n := n) p.1.1 p.1.2 p.2) := by
  refine continuous_realEdgeAddImag_of_continuous
    (((continuous_fst.comp continuous_fst) : Continuous
      (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.1.1)))
    (((continuous_snd.comp continuous_fst) : Continuous
      (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.1.2)))
    (continuous_snd : Continuous
      (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.2))

/-- Every point of an open finite-dimensional real chart set has a connected
open neighborhood with compact closure still inside the set. -/
theorem exists_connected_open_precompact_subset
    {x0 : NPointDomain d n} {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U) (hx0 : x0 ∈ U) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧ IsConnected V ∧ x0 ∈ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.mem_nhds_iff.mp (hU_open.mem_nhds hx0)
  let V : Set (NPointDomain d n) := Metric.ball x0 (r / 2)
  have hr2_pos : 0 < r / 2 := by linarith
  refine ⟨V, Metric.isOpen_ball, ?_, Metric.mem_ball_self hr2_pos, ?_, ?_⟩
  · refine ⟨⟨x0, Metric.mem_ball_self hr2_pos⟩, ?_⟩
    exact (convex_ball x0 (r / 2)).isPreconnected
  · have hcl_subset : closure V ⊆ Metric.closedBall x0 (r / 2) := by
      simpa [V] using
        Metric.closure_ball_subset_closedBall (x := x0) (ε := r / 2)
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall (x := x0) (r := r / 2)) isClosed_closure
      hcl_subset
  · intro y hy
    have hcl_subset : closure V ⊆ Metric.closedBall x0 (r / 2) := by
      simpa [V] using
        Metric.closure_ball_subset_closedBall (x := x0) (ε := r / 2)
    have hydist : dist y x0 ≤ r / 2 := by
      simpa [Metric.mem_closedBall] using hcl_subset hy
    apply hr_sub
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hydist (by linarith)

/-- If the straight segment between two real configurations lies in an open
finite-dimensional chart set, then there is a connected open precompact
neighborhood inside the set containing both endpoints. -/
theorem exists_connected_open_precompact_subset_pair
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    {x y : NPointDomain d n}
    (hseg : segment ℝ x y ⊆ U) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧ IsConnected V ∧ x ∈ V ∧ y ∈ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U := by
  classical
  let K : Set (NPointDomain d n) := segment ℝ x y
  have hK_compact : IsCompact K := by
    have hpair_finite :
        ({x, y} : Set (NPointDomain d n)).Finite := by
      simp
    simpa [K, convexHull_pair] using
      hpair_finite.isCompact_convexHull ℝ
  have hK_convex : Convex ℝ K := by
    simpa [K] using convex_segment x y
  obtain ⟨r0, hr0_pos, hr0_sub⟩ :=
    hK_compact.exists_cthickening_subset_open
      hU_open (by simpa [K] using hseg)
  let r : ℝ := r0 / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  let V : Set (NPointDomain d n) := Metric.thickening r K
  have hV_open : IsOpen V := by
    simpa [V] using Metric.isOpen_thickening
  have hxV : x ∈ V :=
    Metric.self_subset_thickening hr_pos K
      (left_mem_segment ℝ x y)
  have hyV : y ∈ V :=
    Metric.self_subset_thickening hr_pos K
      (right_mem_segment ℝ x y)
  have hV_connected : IsConnected V := by
    refine ⟨⟨x, hxV⟩, ?_⟩
    exact (hK_convex.thickening r).isPreconnected
  have hclosure_cthick :
      closure V ⊆ Metric.cthickening r K := by
    simpa [V] using
      Metric.closure_thickening_subset_cthickening r K
  have hr_le_r0 : r ≤ r0 := by
    dsimp [r]
    linarith
  have hclosure_U : closure V ⊆ U :=
    hclosure_cthick.trans
      ((Metric.cthickening_mono hr_le_r0 K).trans hr0_sub)
  have hclosure_compact : IsCompact (closure V) :=
    IsCompact.of_isClosed_subset
      (hK_compact.cthickening) isClosed_closure hclosure_cthick
  exact ⟨V, hV_open, hV_connected, hxV, hyV,
    hclosure_compact, hclosure_U⟩

/-- Domain of the branch-specific ACR pullback in the OS45 horizontal chart.
The branch label is recorded so the theorem surface matches the branchwise
OS45 boundary packet, although the domain itself is the fixed quarter-turn
pullback of the ordinary forward tube. -/
def os45ACRBranchDomain
    (_σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | (os45QuarterTurnCLE (d := d) (n := n)).symm z ∈ BHW.ForwardTube d n}

/-- The OS45 ACR branch domain is open. -/
theorem isOpen_os45ACRBranchDomain
    (σ : Equiv.Perm (Fin n)) :
    IsOpen (os45ACRBranchDomain (d := d) (n := n) σ) := by
  change IsOpen
    ((fun z : Fin n → Fin (d + 1) → ℂ =>
        (os45QuarterTurnCLE (d := d) (n := n)).symm z) ⁻¹'
      BHW.ForwardTube d n)
  exact BHW.isOpen_forwardTube.preimage
    (os45QuarterTurnCLE (d := d) (n := n)).symm.continuous

variable [NeZero d]

/-- Ordered Euclidean time puts the OS45 horizontal common edge in the
ACR-side branch domain.  Equivalently, applying the inverse quarter-turn to the
horizontal edge gives the same forward-tube point as the ordered Wick trace. -/
theorem os45CommonEdge_mem_acrBranchDomain_of_ordered
    (σ : Equiv.Perm (Fin n)) {x : NPointDomain d n}
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
    BHW.realEmbed (os45CommonEdgeRealPoint (d := d) (n := n) σ x) ∈
      os45ACRBranchDomain (d := d) (n := n) σ := by
  have hwick :
      os45QuarterTurnConfig (d := d) (n := n)
          (fun k => wickRotatePoint (x (σ k))) ∈
        BHW.ForwardTube d n :=
    os45QuarterTurn_perm_wickRotate_mem_forwardTube_of_ordered
      (d := d) (n := n) σ x hx
  have hchart :
      (os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (os45CommonEdgeRealPoint (d := d) (n := n) σ x)) =
        os45QuarterTurnConfig (d := d) (n := n)
          (fun k => wickRotatePoint (x (σ k))) := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [os45QuarterTurnCLE_symm_apply, os45QuarterTurnConfig,
        os45CommonEdgeRealPoint, BHW.realEmbed, wickRotatePoint]
      let a : ℂ := x (σ k) 0
      change (1 + Complex.I) * (a / 2) =
        Complex.I * a / 2 - Complex.I * a / 2 * Complex.I
      ring_nf
      rw [Complex.I_sq]
      ring
    · simp [os45QuarterTurnCLE_symm_apply, os45QuarterTurnConfig,
        os45CommonEdgeRealPoint, BHW.realEmbed, wickRotatePoint, hμ]
  change
    (os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (os45CommonEdgeRealPoint (d := d) (n := n) σ x)) ∈
      BHW.ForwardTube d n
  rw [hchart]
  exact hwick

/-- Source-scalar corridor around the adjacent OS45 quarter-turn point, assuming
the Figure-2-4 scalar path inside the adjacent double scalar domain. -/
theorem os45AdjacentQuarterTurnScalarCorridor_of_figure24
    (hd : 2 <= d)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x, x ∈ V -> x ∈ BHW.JostSet d n)
    (hV_ordered :
      ∀ x, x ∈ V ->
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) 1)
    (hV_swap_ordered :
      ∀ x, x ∈ V ->
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            (Equiv.swap i ⟨i.val + 1, hi⟩))
    (hV_horiz_swap :
      ∀ x, x ∈ V ->
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n)
            (Equiv.swap i ⟨i.val + 1, hi⟩))
    {x0 : NPointDomain d n}
    (hx0V : x0 ∈ V)
    (Wseed : Set (Fin n -> Fin n -> ℂ))
    (hWseed_relOpen :
      BHW.IsRelOpenInSourceComplexGramVariety d n Wseed)
    (hWseed_connected : IsConnected Wseed)
    (hWseed_nonempty : Wseed.Nonempty)
    (hWseed_double :
      Wseed ⊆
        BHW.sourceDoublePermutationGramDomain d n
          (Equiv.swap i ⟨i.val + 1, hi⟩))
    (hDouble_rel :
      BHW.IsRelOpenInSourceComplexGramVariety d n
        (BHW.sourceDoublePermutationGramDomain d n
          (Equiv.swap i ⟨i.val + 1, hi⟩)))
    (γ : unitInterval -> Fin n -> Fin n -> ℂ)
    (hγ_cont : Continuous γ)
    (hγ_start : γ (0 : unitInterval) ∈ Wseed)
    (hγ_end :
      γ (1 : unitInterval) =
        BHW.sourceMinkowskiGram d n
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := n) 1 x0))))
    (hγ_double :
      ∀ t,
        γ t ∈
          BHW.sourceDoublePermutationGramDomain d n
            (Equiv.swap i ⟨i.val + 1, hi⟩)) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
    let y0 :=
      BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x0
    ∃ (Wscal : Set (Fin n -> Fin n -> ℂ))
      (Uy : Set (Fin n -> Fin (d + 1) -> ℂ)),
        BHW.IsRelOpenInSourceComplexGramVariety d n Wscal ∧
        IsConnected Wscal ∧
        Wseed ⊆ Wscal ∧
        IsOpen Uy ∧
        BHW.realEmbed y0 ∈ Uy ∧
        Uy ⊆ BHW.os45ACRBranchDomain (d := d) (n := n) τ ∩
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ ∧
        (∀ z, z ∈ Uy ->
          BHW.sourceMinkowskiGram d n (Q.symm z) ∈ Wscal) ∧
        Wscal ⊆ BHW.sourceDoublePermutationGramDomain d n τ := by
  classical
  have _hd : 2 <= d := hd
  have _hV_open : IsOpen V := hV_open
  have _hV_jost : ∀ x, x ∈ V -> x ∈ BHW.JostSet d n := hV_jost
  have _hV_ordered :
      ∀ x, x ∈ V ->
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) 1 :=
    hV_ordered
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let y0 := BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x0
  have hy_acr_swapped :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) τ
            (fun k => x0 (τ k))) ∈
        BHW.os45ACRBranchDomain (d := d) (n := n) τ := by
    exact BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered
      (d := d) (n := n) τ (hV_swap_ordered x0 hx0V)
  have hedge_eq :
      BHW.os45CommonEdgeRealPoint (d := d) (n := n) τ
          (fun k => x0 (τ k)) = y0 := by
    simpa [τ, y0] using
      BHW.os45CommonEdgeRealPoint_adjacent_swap_eq
        (d := d) (n := n) i hi 1 x0
  have hy_acr :
      BHW.realEmbed y0 ∈
        BHW.os45ACRBranchDomain (d := d) (n := n) τ := by
    simpa [hedge_eq] using hy_acr_swapped
  have hy_bhw :
      BHW.realEmbed y0 ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    simpa [τ, y0] using hV_horiz_swap x0 hx0V
  rcases BHW.sourceComplexGramVariety_connectedRelOpenTube_around_compactPath
      d n hDouble_rel hγ_cont hγ_double hWseed_relOpen hWseed_connected
      hWseed_nonempty hWseed_double hγ_start with
    ⟨Wtube, hWtube_rel, hWtube_conn, hWseed_Wtube, hWtube_double, hγ_Wtube⟩
  have hWtube_rel' : BHW.IsRelOpenInSourceComplexGramVariety d n Wtube :=
    hWtube_rel
  rcases hWtube_rel with ⟨O, hO_open, hWtube_eq⟩
  let Zend : Fin n → Fin n → ℂ :=
    BHW.sourceMinkowskiGram d n (Q.symm (BHW.realEmbed y0))
  have hZend_Wtube : Zend ∈ Wtube := by
    have hγ1 := hγ_Wtube (1 : unitInterval)
    simpa [Zend, Q, y0, hγ_end] using hγ1
  have hZend_O : Zend ∈ O := by
    rw [hWtube_eq] at hZend_Wtube
    exact hZend_Wtube.1
  let scalarMap : (Fin n → Fin (d + 1) → ℂ) → (Fin n → Fin n → ℂ) :=
    fun z => BHW.sourceMinkowskiGram d n (Q.symm z)
  let Uy : Set (Fin n → Fin (d + 1) → ℂ) :=
    (scalarMap ⁻¹' O) ∩
      BHW.os45ACRBranchDomain (d := d) (n := n) τ ∩
      BHW.os45PulledRealBranchDomain (d := d) (n := n) τ
  have hscalar_cont : Continuous scalarMap := by
    exact (BHW.contDiff_sourceMinkowskiGram d n).continuous.comp Q.symm.continuous
  have hUy_open : IsOpen Uy := by
    exact ((hO_open.preimage hscalar_cont).inter
      (BHW.isOpen_os45ACRBranchDomain (d := d) (n := n) τ)).inter
      (BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n) τ)
  have hy_Uy : BHW.realEmbed y0 ∈ Uy := by
    exact ⟨⟨hZend_O, hy_acr⟩, hy_bhw⟩
  refine
    ⟨Wtube, Uy, hWtube_rel', hWtube_conn, hWseed_Wtube,
      hUy_open, hy_Uy, ?_, ?_, hWtube_double⟩
  · intro z hz
    exact ⟨hz.1.2, hz.2⟩
  · intro z hz
    have hzO : scalarMap z ∈ O := hz.1.1
    have hzVar : scalarMap z ∈ BHW.sourceComplexGramVariety d n := by
      exact ⟨Q.symm z, rfl⟩
    rw [hWtube_eq]
    exact ⟨hzO, hzVar⟩

set_option maxHeartbeats 800000 in
/-- Compact edge and direction sets have a uniform side radius inside the two
open OS45 horizontal branch domains. -/
theorem os45BranchHorizontal_localWedge_of_edgeDomain
    (β : Equiv.Perm (Fin n))
    (E C : Set (NPointDomain d n))
    (hE_plus :
      ∀ y ∈ E,
        BHW.realEmbed y ∈
          BHW.os45ACRBranchDomain (d := d) (n := n) β)
    (hE_minus :
      ∀ y ∈ E,
        BHW.realEmbed y ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) β) :
    ∀ K : Set (NPointDomain d n), IsCompact K -> K ⊆ E ->
      ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ C ->
        ∃ r : ℝ, 0 < r ∧
          ∀ y ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
            BHW.realEdgeAddImag (d := d) (n := n) y η ε ∈
              BHW.os45ACRBranchDomain (d := d) (n := n) β ∧
            BHW.realEdgeAddImag (d := d) (n := n) y η (-ε) ∈
              BHW.os45PulledRealBranchDomain (d := d) (n := n) β := by
  intro K hK hKE Kη hKη _hKηC
  let S : Set ((NPointDomain d n × NPointDomain d n) × ℝ) :=
    (K ×ˢ Kη) ×ˢ ({0} : Set ℝ)
  let Fplus : ((NPointDomain d n × NPointDomain d n) × ℝ) →
      Fin n → Fin (d + 1) → ℂ :=
    fun p => realEdgeAddImag (d := d) (n := n) p.1.1 p.1.2 p.2
  let Fminus : ((NPointDomain d n × NPointDomain d n) × ℝ) →
      Fin n → Fin (d + 1) → ℂ :=
    fun p => realEdgeAddImag (d := d) (n := n) p.1.1 p.1.2 (-p.2)
  have hS_compact : IsCompact S := by
    exact (hK.prod hKη).prod isCompact_singleton
  have hFplus_cont : Continuous Fplus := by
    simpa [Fplus] using continuous_realEdgeAddImag (d := d) (n := n)
  have hFminus_cont : Continuous Fminus := by
    refine continuous_realEdgeAddImag_of_continuous
      (((continuous_fst.comp continuous_fst) : Continuous
        (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.1.1)))
      (((continuous_snd.comp continuous_fst) : Continuous
        (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.1.2)))
      ((continuous_snd : Continuous
        (fun p : (NPointDomain d n × NPointDomain d n) × ℝ => p.2)).neg)
  have hplus_open : IsOpen (Fplus ⁻¹'
      BHW.os45ACRBranchDomain (d := d) (n := n) β) :=
    (BHW.isOpen_os45ACRBranchDomain (d := d) (n := n) β).preimage hFplus_cont
  have hminus_open : IsOpen (Fminus ⁻¹'
      BHW.os45PulledRealBranchDomain (d := d) (n := n) β) :=
    (BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n) β).preimage
      hFminus_cont
  have hS_plus : S ⊆ Fplus ⁻¹'
      BHW.os45ACRBranchDomain (d := d) (n := n) β := by
    intro p hp
    rcases hp with ⟨hpK, hp0⟩
    rcases hpK with ⟨hyK, _hηK⟩
    have hzero : p.2 = 0 := by simpa using hp0
    have hbase := hE_plus p.1.1 (hKE hyK)
    simpa [Fplus, hzero, realEdgeAddImag_zero] using hbase
  have hS_minus : S ⊆ Fminus ⁻¹'
      BHW.os45PulledRealBranchDomain (d := d) (n := n) β := by
    intro p hp
    rcases hp with ⟨hpK, hp0⟩
    rcases hpK with ⟨hyK, _hηK⟩
    have hzero : p.2 = 0 := by simpa using hp0
    have hbase := hE_minus p.1.1 (hKE hyK)
    simpa [Fminus, hzero, realEdgeAddImag_zero] using hbase
  obtain ⟨rplus, hrplus_pos, hrplus_sub⟩ :=
    hS_compact.exists_cthickening_subset_open hplus_open hS_plus
  obtain ⟨rminus, hrminus_pos, hrminus_sub⟩ :=
    hS_compact.exists_cthickening_subset_open hminus_open hS_minus
  let r := min rplus rminus
  have hrpos : 0 < r := lt_min hrplus_pos hrminus_pos
  refine ⟨r, hrpos, ?_⟩
  intro y hyK η hηK ε hεpos hεlt
  have hr_le_plus : r ≤ rplus := min_le_left _ _
  have hr_le_minus : r ≤ rminus := min_le_right _ _
  have hdist : dist
      (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ)
      (((y, η), 0) : (NPointDomain d n × NPointDomain d n) × ℝ) < r := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq]
    simp [abs_of_nonneg hεpos.le, hεlt, hrpos]
  have hthick :
      (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ) ∈
        Metric.thickening r S := by
    rw [Metric.mem_thickening_iff]
    refine ⟨((y, η), 0), ?_, hdist⟩
    exact ⟨⟨hyK, hηK⟩, by simp⟩
  have hcthick_plus :
      (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ) ∈
        Metric.cthickening rplus S := by
    exact (Metric.thickening_subset_cthickening_of_le hr_le_plus S) hthick
  have hcthick_minus :
      (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ) ∈
        Metric.cthickening rminus S := by
    exact (Metric.thickening_subset_cthickening_of_le hr_le_minus S) hthick
  constructor
  · have hpre :
        (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ) ∈
          Fplus ⁻¹' BHW.os45ACRBranchDomain (d := d) (n := n) β :=
      hrplus_sub hcthick_plus
    simpa [Fplus] using hpre
  · have hpre :
        (((y, η), ε) : (NPointDomain d n × NPointDomain d n) × ℝ) ∈
          Fminus ⁻¹' BHW.os45PulledRealBranchDomain (d := d) (n := n) β :=
      hrminus_sub hcthick_minus
    simpa [Fminus] using hpre

/-- The two adjacent ordered Wick traces used in the OS45 common chart both lie
in the OS-II ACR-one domain. -/
theorem adjacent_wick_traces_mem_acrOne
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hx_swap_ordered :
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
        AnalyticContinuationRegion d n 1 ∧
    BHW.permAct (d := d) ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => wickRotatePoint (x k))) ∈
        AnalyticContinuationRegion d n 1 := by
  constructor
  · exact BHW.wickRotate_ordered_mem_acrOne (d := d) (n := n) ρ hx_ordered
  · simpa [BHW.permAct_wickRotatePoint] using
      BHW.wickRotate_ordered_mem_acrOne
        (d := d) (n := n)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        hx_swap_ordered

/-- The common OS45 real chart point lies in both pulled real-branch domains
for the original branch and the adjacent relabelled branch. -/
theorem os45CommonChart_real_mem_pulledRealBranchDomain_pair
    (τ ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hxτ_ET : BHW.realEmbed (fun k => x (τ k)) ∈ BHW.ExtendedTube d n) :
    BHW.os45CommonChartCLE (d := d) (n := n) ρ (BHW.realEmbed x) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
        BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
  constructor
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) ρ x hx_ET
    simpa using hmem
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) (τ.symm * ρ) (fun k => x (τ k)) hxτ_ET
    have hmem' :
        BHW.os45QuarterTurnConfig (d := d) (n := n)
            (fun k => BHW.realEmbed (fun j => x (τ j)) ((τ.symm * ρ) k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      simpa [Equiv.Perm.mul_apply] using hmem
    have hcommon :
        BHW.os45QuarterTurnConfig
            (d := d) (n := n) (fun k => BHW.realEmbed x (ρ k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      have hchart :=
        BHW.os45QuarterTurnConfig_reindexed_realBranch_eq
          (d := d) (n := n) τ ρ x
      exact hchart ▸ hmem'
    simpa [BHW.os45CommonChartCLE_apply] using hcommon

/-- Convert a common-chart OS45 branch-difference envelope into the direct
coordinate `AdjacentOSEOWDifferenceEnvelope` consumed by the real-edge
distributional equality theorem.

The hard EOW/common-boundary construction is deliberately an input here.  This
lemma only performs the checked coordinate pullback through the common chart and
packages the resulting direct Wick and real traces. -/
def adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (ρ : Equiv.Perm (Fin n))
    (Uc : Set (Fin n → Fin (d + 1) → ℂ))
    (Hc : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hUc_open : IsOpen Uc)
    (hUc_conn : IsConnected Uc)
    (hHc_holo : DifferentiableOn ℂ Hc Uc)
    (hwick_mem :
      ∀ x ∈ V,
        os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k)) ∈ Uc)
    (hreal_mem :
      ∀ x ∈ V,
        os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed x) ∈ Uc)
    (hwick_trace :
      ∀ x ∈ V,
        Hc (os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k))) =
          bvt_F OS lgc n
            (fun k => wickRotatePoint
              (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)))
    (hreal_trace :
      ∀ x ∈ V,
        Hc (os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed x)) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) :
    AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V := by
  let Qρe := os45CommonChartCLE (d := d) (n := n) ρ
  let U : Set (Fin n → Fin (d + 1) → ℂ) := Qρe ⁻¹' Uc
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => Hc (Qρe z)
  have hU_open : IsOpen U := by
    exact hUc_open.preimage Qρe.continuous
  have hU_eq : U = Qρe.symm '' Uc := by
    ext z
    constructor
    · intro hz
      refine ⟨Qρe z, hz, ?_⟩
      exact Qρe.symm_apply_apply z
    · rintro ⟨w, hw, rfl⟩
      have hq : Qρe (Qρe.symm w) = w := Qρe.apply_symm_apply w
      simpa [U, hq] using hw
  have hU_conn : IsConnected U := by
    rw [hU_eq]
    exact hUc_conn.image Qρe.symm Qρe.symm.continuous.continuousOn
  have hH_holo : DifferentiableOn ℂ H U := by
    intro z hz
    exact (hHc_holo (Qρe z) hz).comp z
      Qρe.differentiableAt.differentiableWithinAt
      (by
        intro y hy
        exact hy)
  refine
    { U := U
      U_open := hU_open
      U_connected := hU_conn
      H := H
      H_holo := hH_holo
      wick_mem := ?wick_mem
      real_mem := ?real_mem
      wick_diff := ?wick_diff
      real_diff := ?real_diff }
  · intro x hx
    exact hwick_mem x hx
  · intro x hx
    exact hreal_mem x hx
  · intro x hx
    simpa [H, Qρe] using hwick_trace x hx
  · intro x hx
    simpa [H, Qρe] using hreal_trace x hx

end BHW
