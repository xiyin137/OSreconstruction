import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedAdjacentNormalForm
import OSReconstruction.SCV.LocalEOWDistributionalEnvelope

/-!
# Reduced Normal Local EOW Bridge

This file records the local edge-of-the-wedge bridge used on the theorem-2
E-to-R locality path after freezing spectators and flattening the reduced
adjacent normal chart.  It does not prove a new EOW theorem; it specializes the
existing SCV theorem to the selected spacelike edge supplied by the reduced
normal-form module, and records the ray-limit consequence needed for the
Ruelle/Jost branch comparison.
-/

open scoped Classical NNReal

noncomputable section

namespace OSReconstruction
namespace AdjacentNormal

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Local branch data for the reduced normal EOW handoff at one selected
spacelike normal point.

The fields are deliberately concrete: two side domains, an edge cone, the two
holomorphic side branches, their common continuous boundary value, and the two
rays representing the canonical and sign-flipped reduced branches. -/
structure ReducedNormalLocalEOWBranchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) where
  Ωplus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  Ωminus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  C : Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ)
  hΩplus_open : IsOpen Ωplus
  hΩminus_open : IsOpen Ωminus
  hC_open : IsOpen C
  hC_conv : Convex ℝ C
  hC_ne : C.Nonempty
  hlocal_wedge :
    ∀ K : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ),
      IsCompact K →
      K ⊆ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩ →
      ∀ Kη : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact Kη → Kη ⊆ C →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωplus ∧
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωminus
  Fplus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  Fminus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  hFplus_diff : DifferentiableOn ℂ Fplus Ωplus
  hFminus_diff : DifferentiableOn ℂ Fminus Ωminus
  bv : (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) → ℂ
  hbv_cont : ContinuousOn bv
    (reducedNormalFlattenedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩)
  hFplus_bv :
    ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩,
      Filter.Tendsto Fplus
        (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x))
  hFminus_bv :
    ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩,
      Filter.Tendsto Fminus
        (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x))
  hplus_nhds :
    Ωplus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  hminus_nhds :
    Ωminus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  γplus : ℝ →
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1))
  γminus : ℝ →
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1))
  hγplus :
    Filter.Tendsto γplus
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
  hγminus :
    Filter.Tendsto γminus
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
  hplus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fplus (γplus ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi) p)
  hminus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fminus (γminus ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))

omit [NeZero d] in
/-- The reduced-coordinate chart followed by the flattened normal SCV chart. -/
noncomputable def reducedNormalCoordFlatCLE
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    NPointDomain d m ≃L[ℝ]
      (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) :=
  (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
    (reducedAdjacent_succ_ne i hi)).trans
    (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩)

omit [NeZero d] in
/-- The canonical imaginary direction in flattened reduced normal coordinates. -/
noncomputable def reducedNormalFlatCanonicalDirection
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ :=
  reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩
    ((reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi))
      (canonicalReducedDirection (d := d) m))

omit [NeZero d] in
/-- The forward cone transported to flattened reduced normal coordinates. -/
def reducedNormalFlatForwardCone
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :=
  {η | (reducedNormalCoordFlatCLE (d := d) i hi).symm η ∈
    BHW.ProductForwardConeReal d m}

theorem isOpen_reducedNormalFlatForwardCone
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    IsOpen (reducedNormalFlatForwardCone (d := d) i hi) := by
  simpa [reducedNormalFlatForwardCone] using
    (BHW.isOpen_productForwardConeReal (n := m) (d := d)).preimage
      (reducedNormalCoordFlatCLE (d := d) i hi).symm.continuous

omit [NeZero d] in
theorem convex_reducedNormalFlatForwardCone
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    Convex ℝ (reducedNormalFlatForwardCone (d := d) i hi) := by
  intro u hu v hv a b ha hb hab
  change
    (reducedNormalCoordFlatCLE (d := d) i hi).symm
        (a • u + b • v) ∈ BHW.ProductForwardConeReal d m
  rw [map_add, map_smul, map_smul]
  exact
    BHW.productForwardConeReal_convex (n := m) (d := d) hu hv ha hb hab

theorem reducedNormalFlatForwardCone_nonempty
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (reducedNormalFlatForwardCone (d := d) i hi).Nonempty := by
  rcases BHW.productForwardConeReal_nonempty (n := m) (d := d) with ⟨η, hη⟩
  refine ⟨(reducedNormalCoordFlatCLE (d := d) i hi) η, ?_⟩
  simpa [reducedNormalFlatForwardCone] using hη

theorem reducedNormalFlatCanonicalDirection_mem_forwardCone
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    reducedNormalFlatCanonicalDirection (d := d) i hi ∈
      reducedNormalFlatForwardCone (d := d) i hi := by
  simpa [reducedNormalFlatForwardCone, reducedNormalFlatCanonicalDirection,
    reducedNormalCoordFlatCLE] using
      canonicalReducedDirection_mem_productForwardConeReal (d := d) m

omit [NeZero d] in
theorem reducedNormalFlatForwardCone_smul_pos
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (t : ℝ) (ht : 0 < t)
    (η : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ)
    (hη : η ∈ reducedNormalFlatForwardCone (d := d) i hi) :
    t • η ∈ reducedNormalFlatForwardCone (d := d) i hi := by
  change
    (reducedNormalCoordFlatCLE (d := d) i hi).symm (t • η) ∈
      BHW.ProductForwardConeReal d m
  rw [map_smul]
  exact BHW.productForwardConeReal_smul_pos (n := m) (d := d) t ht _ hη

omit [NeZero d] in
/-- A compact real edge has a uniform two-sided wedge radius into open side
domains, in reduced normal flattened coordinates.

This discharges the topology-only part of the local EOW branch-data packet:
once both open side domains contain the real selected spacelike edge, compact
subsets of that edge have a uniform small positive-height wedge in the two
side domains. -/
theorem reducedNormalFlattened_localWedge_of_realEdge_mem
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hplus0 :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        SCV.realEmbed x ∈ Ωplus)
    (hminus0 :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        SCV.realEmbed x ∈ Ωminus) :
    ∀ K : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ),
      IsCompact K →
      K ⊆ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩ →
      ∀ Kη : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact Kη → Kη ⊆ C →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωplus ∧
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωminus := by
  intro K hK hK_edge Kη hKη _hKη_C
  let q :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let R := Fin q → ℝ
  let plusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace q :=
    fun p a => (p.1.1 a : ℂ) + (p.2 : ℂ) * (p.1.2 a : ℂ) * Complex.I
  let minusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace q :=
    fun p a => (p.1.1 a : ℂ) - (p.2 : ℂ) * (p.1.2 a : ℂ) * Complex.I
  let edgeDir : Set (R × R) := K ×ˢ Kη
  let zeroEdge : Set ((R × R) × ℝ) := edgeDir ×ˢ ({0} : Set ℝ)
  let sideWindow : Set ((R × R) × ℝ) :=
    plusMap ⁻¹' Ωplus ∩ minusMap ⁻¹' Ωminus
  have hplus_cont : Continuous plusMap := by
    refine continuous_pi ?_
    intro a
    have hx : Continuous fun p : (R × R) × ℝ => ((p.1.1 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_fst.comp continuous_fst))
    have hε : Continuous fun p : (R × R) × ℝ => ((p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    have hη : Continuous fun p : (R × R) × ℝ => ((p.1.2 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_snd.comp continuous_fst))
    simpa [plusMap] using hx.add ((hε.mul hη).mul continuous_const)
  have hminus_cont : Continuous minusMap := by
    refine continuous_pi ?_
    intro a
    have hx : Continuous fun p : (R × R) × ℝ => ((p.1.1 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_fst.comp continuous_fst))
    have hε : Continuous fun p : (R × R) × ℝ => ((p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    have hη : Continuous fun p : (R × R) × ℝ => ((p.1.2 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_snd.comp continuous_fst))
    simpa [minusMap] using hx.sub ((hε.mul hη).mul continuous_const)
  have hside_open : IsOpen sideWindow :=
    (hΩplus_open.preimage hplus_cont).inter
      (hΩminus_open.preimage hminus_cont)
  have hzero_compact : IsCompact zeroEdge :=
    (hK.prod hKη).prod isCompact_singleton
  have hzero_sub : zeroEdge ⊆ sideWindow := by
    rintro ⟨⟨x, η⟩, ε⟩ ⟨⟨hx, _hη⟩, hε0⟩
    have hε_eq : ε = 0 := by simpa using hε0
    subst ε
    constructor
    · simpa [plusMap, SCV.realEmbed, q] using hplus0 x (hK_edge hx)
    · simpa [minusMap, SCV.realEmbed, q] using hminus0 x (hK_edge hx)
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hzero_compact.exists_thickening_subset_open hside_open hzero_sub
  refine ⟨r, hr_pos, ?_⟩
  intro x hx η hη ε hε_pos hε_lt
  have hmem : (((x, η), ε) : (R × R) × ℝ) ∈
      Metric.thickening r zeroEdge := by
    rw [Metric.mem_thickening_iff]
    refine ⟨((x, η), (0 : ℝ)), ?_, ?_⟩
    · exact ⟨⟨hx, hη⟩, by simp⟩
    · simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hε_pos.le] using
        ⟨hr_pos, hε_lt⟩
  simpa [sideWindow, plusMap, minusMap, q] using hr_sub hmem

omit [NeZero d] in
/-- A compact subset of an arbitrary real collar has a uniform two-sided wedge
radius into open side domains.

This is the local version of
`reducedNormalFlattened_localWedge_of_realEdge_mem`: callers only need the
side domains to contain the real embedding of the collar `E`, not the whole
selected spacelike edge. -/
theorem reducedNormalFlattened_localWedge_of_openEdge_mem
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (E : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus)
    (hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus) :
    ∀ K : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ),
      IsCompact K →
      K ⊆ E →
      ∀ Kη : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact Kη → Kη ⊆ C →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωplus ∧
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωminus := by
  intro K hK hK_edge Kη hKη _hKη_C
  let q :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let R := Fin q → ℝ
  let plusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace q :=
    fun p a => (p.1.1 a : ℂ) + (p.2 : ℂ) * (p.1.2 a : ℂ) * Complex.I
  let minusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace q :=
    fun p a => (p.1.1 a : ℂ) - (p.2 : ℂ) * (p.1.2 a : ℂ) * Complex.I
  let edgeDir : Set (R × R) := K ×ˢ Kη
  let zeroEdge : Set ((R × R) × ℝ) := edgeDir ×ˢ ({0} : Set ℝ)
  let sideWindow : Set ((R × R) × ℝ) :=
    plusMap ⁻¹' Ωplus ∩ minusMap ⁻¹' Ωminus
  have hplus_cont : Continuous plusMap := by
    refine continuous_pi ?_
    intro a
    have hx : Continuous fun p : (R × R) × ℝ => ((p.1.1 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_fst.comp continuous_fst))
    have hε : Continuous fun p : (R × R) × ℝ => ((p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    have hη : Continuous fun p : (R × R) × ℝ => ((p.1.2 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_snd.comp continuous_fst))
    simpa [plusMap] using hx.add ((hε.mul hη).mul continuous_const)
  have hminus_cont : Continuous minusMap := by
    refine continuous_pi ?_
    intro a
    have hx : Continuous fun p : (R × R) × ℝ => ((p.1.1 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_fst.comp continuous_fst))
    have hε : Continuous fun p : (R × R) × ℝ => ((p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    have hη : Continuous fun p : (R × R) × ℝ => ((p.1.2 a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_snd.comp continuous_fst))
    simpa [minusMap] using hx.sub ((hε.mul hη).mul continuous_const)
  have hside_open : IsOpen sideWindow :=
    (hΩplus_open.preimage hplus_cont).inter
      (hΩminus_open.preimage hminus_cont)
  have hzero_compact : IsCompact zeroEdge :=
    (hK.prod hKη).prod isCompact_singleton
  have hzero_sub : zeroEdge ⊆ sideWindow := by
    rintro ⟨⟨x, η⟩, ε⟩ ⟨⟨hx, _hη⟩, hε0⟩
    have hε_eq : ε = 0 := by simpa using hε0
    subst ε
    constructor
    · simpa [plusMap, SCV.realEmbed, q] using hplus0 x (hK_edge hx)
    · simpa [minusMap, SCV.realEmbed, q] using hminus0 x (hK_edge hx)
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hzero_compact.exists_thickening_subset_open hside_open hzero_sub
  refine ⟨r, hr_pos, ?_⟩
  intro x hx η hη ε hε_pos hε_lt
  have hmem : (((x, η), ε) : (R × R) × ℝ) ∈
      Metric.thickening r zeroEdge := by
    rw [Metric.mem_thickening_iff]
    refine ⟨((x, η), (0 : ℝ)), ?_, ?_⟩
    · exact ⟨⟨hx, hη⟩, by simp⟩
    · simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hε_pos.le] using
        ⟨hr_pos, hε_lt⟩
  simpa [sideWindow, plusMap, minusMap, q] using hr_sub hmem

omit [NeZero d] in
/-- Upper canonical approach ray in the flattened reduced normal chart. -/
noncomputable def reducedNormalUpperCanonicalRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    ℝ → SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) :=
  fun ε a =>
    (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p a : ℂ) +
      (ε : ℂ) *
        (reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
        Complex.I

omit [NeZero d] in
/-- Lower canonical approach ray in the flattened reduced normal chart. -/
noncomputable def reducedNormalLowerCanonicalRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    ℝ → SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) :=
  fun ε a =>
    (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p a : ℂ) -
      (ε : ℂ) *
        (reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
        Complex.I

omit [NeZero d] in
theorem reducedNormalUpperCanonicalRay_tendsto
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (reducedNormalUpperCanonicalRay (d := d) i hi p)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))) := by
  rw [tendsto_pi_nhds]
  intro a
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hε : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (nhds 0) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) l (nhds (0 : ℝ)) :=
      Filter.tendsto_id'.2 nhdsWithin_le_nhds
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hid
  have hterm :
      Filter.Tendsto
        (fun ε : ℝ =>
          (ε : ℂ) *
            (reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
            Complex.I) l (nhds 0) := by
    simpa [mul_assoc] using
      (hε.mul_const
        ((reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
          Complex.I))
  simpa [reducedNormalUpperCanonicalRay, SCV.realEmbed, l] using
    (tendsto_const_nhds.add hterm)

omit [NeZero d] in
theorem reducedNormalLowerCanonicalRay_tendsto
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (reducedNormalLowerCanonicalRay (d := d) i hi p)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))) := by
  rw [tendsto_pi_nhds]
  intro a
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hε : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (nhds 0) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) l (nhds (0 : ℝ)) :=
      Filter.tendsto_id'.2 nhdsWithin_le_nhds
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hid
  have hterm :
      Filter.Tendsto
        (fun ε : ℝ =>
          (ε : ℂ) *
            (reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
            Complex.I) l (nhds 0) := by
    simpa [mul_assoc] using
      (hε.mul_const
        ((reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
          Complex.I))
  have hneg :
      Filter.Tendsto
        (fun ε : ℝ =>
          -((ε : ℂ) *
            (reducedNormalFlatCanonicalDirection (d := d) i hi a : ℂ) *
            Complex.I)) l (nhds 0) := by
    simpa using hterm.neg
  simpa [reducedNormalLowerCanonicalRay, SCV.realEmbed, sub_eq_add_neg, l] using
    (tendsto_const_nhds.add hneg)

/-- Concrete version of the reduced-normal local EOW data in which the two
approach rays are the canonical upper/lower imaginary rays in the flattened
normal chart. -/
structure ReducedNormalCanonicalRayEOWBranchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) where
  Ωplus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  Ωminus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  C : Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ)
  hΩplus_open : IsOpen Ωplus
  hΩminus_open : IsOpen Ωminus
  hC_open : IsOpen C
  hC_conv : Convex ℝ C
  hC_ne : C.Nonempty
  hlocal_wedge :
    ∀ K : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ),
      IsCompact K →
      K ⊆ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩ →
      ∀ Kη : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact Kη → Kη ⊆ C →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωplus ∧
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωminus
  Fplus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  Fminus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  hFplus_diff : DifferentiableOn ℂ Fplus Ωplus
  hFminus_diff : DifferentiableOn ℂ Fminus Ωminus
  bv : (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) → ℂ
  hbv_cont : ContinuousOn bv
    (reducedNormalFlattenedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩)
  hFplus_bv :
    ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩,
      Filter.Tendsto Fplus
        (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x))
  hFminus_bv :
    ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩,
      Filter.Tendsto Fminus
        (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x))
  hplus_nhds :
    Ωplus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  hminus_nhds :
    Ωminus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  hplus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi) p)
  hminus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))

/-- Collar-local canonical-ray EOW branch data.

This is the local form used by the Jost/Ruelle partition step: the common
boundary value and side-domain wedge only have to be supplied on one open real
edge collar `E` containing the point under consideration, not on the whole
selected spacelike edge. -/
structure ReducedNormalCanonicalRayEOWBranchDataOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) where
  E : Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ)
  hE_open : IsOpen E
  hpE :
    reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E
  Ωplus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  Ωminus : Set
    (SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)))
  C : Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ)
  hΩplus_open : IsOpen Ωplus
  hΩminus_open : IsOpen Ωminus
  hC_open : IsOpen C
  hC_conv : Convex ℝ C
  hC_ne : C.Nonempty
  hlocal_wedge :
    ∀ K : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ),
      IsCompact K →
      K ⊆ E →
      ∀ Kη : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact Kη → Kη ⊆ C →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωplus ∧
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                Ωminus
  Fplus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  Fminus :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℂ
  hFplus_diff : DifferentiableOn ℂ Fplus Ωplus
  hFminus_diff : DifferentiableOn ℂ Fminus Ωminus
  bv : (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) → ℂ
  hbv_cont : ContinuousOn bv E
  hFplus_bv :
    ∀ x ∈ E,
      Filter.Tendsto Fplus
        (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x))
  hFminus_bv :
    ∀ x ∈ E,
      Filter.Tendsto Fminus
        (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x))
  hplus_nhds :
    Ωplus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  hminus_nhds :
    Ωminus ∈ nhds
      (SCV.realEmbed
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))
  hplus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi) p)
  hminus_rep :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))

/-- Build collar-local canonical-ray branch data when the side domains are open
neighborhoods of the chosen real collar.

This discharges the topology-only `hlocal_wedge` field locally, matching the
partition-of-unity form of the Ruelle/Jost proof. -/
def ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {p : ReducedSpace d m i ⟨i.val + 1, hi⟩}
    (E : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hE_open : IsOpen E)
    (hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus)
    (hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p where
  E := E
  hE_open := hE_open
  hpE := hpE
  Ωplus := Ωplus
  Ωminus := Ωminus
  C := C
  hΩplus_open := hΩplus_open
  hΩminus_open := hΩminus_open
  hC_open := hC_open
  hC_conv := hC_conv
  hC_ne := hC_ne
  hlocal_wedge :=
    reducedNormalFlattened_localWedge_of_openEdge_mem
      (d := d) i hi E Ωplus Ωminus C hΩplus_open hΩminus_open
      hplus0 hminus0
  Fplus := Fplus
  Fminus := Fminus
  hFplus_diff := hFplus_diff
  hFminus_diff := hFminus_diff
  bv := bv
  hbv_cont := hbv_cont
  hFplus_bv := hFplus_bv
  hFminus_bv := hFminus_bv
  hplus_nhds := hplus_nhds
  hminus_nhds := hminus_nhds
  hplus_rep := hplus_rep
  hminus_rep := hminus_rep

/-- Build canonical-ray branch data when the side domains are open
neighborhoods of the whole reduced normal real edge.

The only field supplied here rather than assumed is `hlocal_wedge`, obtained
from compactness of the real edge slice and openness of the two side domains. -/
def ReducedNormalCanonicalRayEOWBranchData.ofRealEdgeMem
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {p : ReducedSpace d m i ⟨i.val + 1, hi⟩}
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hplus0 :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        SCV.realEmbed x ∈ Ωplus)
    (hminus0 :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        SCV.realEmbed x ∈ Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv
      (reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩))
    (hFplus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchData (d := d) OS lgc i hi p where
  Ωplus := Ωplus
  Ωminus := Ωminus
  C := C
  hΩplus_open := hΩplus_open
  hΩminus_open := hΩminus_open
  hC_open := hC_open
  hC_conv := hC_conv
  hC_ne := hC_ne
  hlocal_wedge :=
    reducedNormalFlattened_localWedge_of_realEdge_mem
      (d := d) i hi Ωplus Ωminus C hΩplus_open hΩminus_open
      hplus0 hminus0
  Fplus := Fplus
  Fminus := Fminus
  hFplus_diff := hFplus_diff
  hFminus_diff := hFminus_diff
  bv := bv
  hbv_cont := hbv_cont
  hFplus_bv := hFplus_bv
  hFminus_bv := hFminus_bv
  hplus_nhds := hplus_nhds
  hminus_nhds := hminus_nhds
  hplus_rep := hplus_rep
  hminus_rep := hminus_rep

/-- Forget the concrete canonical-ray presentation to the local EOW interface
used by the sign-flip pointwise comparison. -/
def ReducedNormalCanonicalRayEOWBranchData.toLocalEOWBranchData
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {p : ReducedSpace d m i ⟨i.val + 1, hi⟩}
    (D : ReducedNormalCanonicalRayEOWBranchData (d := d) OS lgc i hi p) :
    ReducedNormalLocalEOWBranchData (d := d) OS lgc i hi p where
  Ωplus := D.Ωplus
  Ωminus := D.Ωminus
  C := D.C
  hΩplus_open := D.hΩplus_open
  hΩminus_open := D.hΩminus_open
  hC_open := D.hC_open
  hC_conv := D.hC_conv
  hC_ne := D.hC_ne
  hlocal_wedge := D.hlocal_wedge
  Fplus := D.Fplus
  Fminus := D.Fminus
  hFplus_diff := D.hFplus_diff
  hFminus_diff := D.hFminus_diff
  bv := D.bv
  hbv_cont := D.hbv_cont
  hFplus_bv := D.hFplus_bv
  hFminus_bv := D.hFminus_bv
  hplus_nhds := D.hplus_nhds
  hminus_nhds := D.hminus_nhds
  γplus := reducedNormalUpperCanonicalRay (d := d) i hi p
  γminus := reducedNormalLowerCanonicalRay (d := d) i hi p
  hγplus := reducedNormalUpperCanonicalRay_tendsto (d := d) i hi p
  hγminus := reducedNormalLowerCanonicalRay_tendsto (d := d) i hi p
  hplus_rep := D.hplus_rep
  hminus_rep := D.hminus_rep

omit [NeZero d] in
/-- Reduced-normal local EOW on an arbitrary open real collar in flattened
coordinates.

This is the collar-local version used by the Jost/Ruelle partition step.  The
older selected-spacelike-edge theorem below is the special case
`E = reducedNormalFlattenedSelectedSpacelike`. -/
theorem reducedNormalFlattened_localEOW_eventuallyEq_at_open_edge
    {m : ℕ} (i j : Fin (m + 1))
    (E : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (u0 : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ)
    (hu0 : u0 ∈ E)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i j) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ E →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card (SpectatorIndex (m + 1) i j) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds : Ωplus ∈ nhds (SCV.realEmbed u0))
    (hminus_nhds : Ωminus ∈ nhds (SCV.realEmbed u0)) :
    Fplus =ᶠ[nhds (SCV.realEmbed u0)] Fminus := by
  have hq :
      0 < (d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1) := by
    omega
  exact
    SCV.local_continuous_edge_of_the_wedge_eventuallyEq_at_common_edge
      (m := (d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1))
      hq Ωplus Ωminus E C hΩplus_open hΩminus_open hE_open
      hC_open hC_conv hC_ne hlocal_wedge Fplus Fminus hFplus_diff
      hFminus_diff bv hbv_cont hFplus_bv hFminus_bv u0 hu0
      hplus_nhds hminus_nhds

omit [NeZero d] in
/-- Two-ray consequence of the collar-local reduced-normal EOW bridge. -/
theorem reducedNormalFlattened_localEOW_two_rays_tendsto_sub_zero_at_open_edge
    {m : ℕ} (i j : Fin (m + 1))
    (E : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (u0 : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ)
    (hu0 : u0 ∈ E)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i j) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ E →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card (SpectatorIndex (m + 1) i j) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds : Ωplus ∈ nhds (SCV.realEmbed u0))
    (hminus_nhds : Ωminus ∈ nhds (SCV.realEmbed u0))
    {l : Filter ℝ}
    (γplus γminus : ℝ →
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)))
    (hγplus : Filter.Tendsto γplus l (nhds (SCV.realEmbed u0)))
    (hγminus : Filter.Tendsto γminus l (nhds (SCV.realEmbed u0))) :
    Filter.Tendsto
      (fun ε : ℝ => Fminus (γminus ε) - Fplus (γplus ε))
      l (nhds 0) := by
  let z0 :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) :=
    SCV.realEmbed u0
  have heq :
      Fplus =ᶠ[nhds z0] Fminus := by
    simpa [z0] using
      reducedNormalFlattened_localEOW_eventuallyEq_at_open_edge
        (d := d) i j E u0 hu0 Ωplus Ωminus C
        hΩplus_open hΩminus_open hE_open hC_open hC_conv hC_ne
        hlocal_wedge Fplus Fminus hFplus_diff hFminus_diff bv
        hbv_cont hFplus_bv hFminus_bv hplus_nhds hminus_nhds
  have hzplus : z0 ∈ Ωplus := by
    simpa [z0] using mem_of_mem_nhds hplus_nhds
  have hzminus : z0 ∈ Ωminus := by
    simpa [z0] using mem_of_mem_nhds hminus_nhds
  have hFplus_cont :
      ContinuousAt Fplus z0 :=
    hFplus_diff.continuousOn.continuousAt
      (hΩplus_open.mem_nhds hzplus)
  have hFminus_cont :
      ContinuousAt Fminus z0 :=
    hFminus_diff.continuousOn.continuousAt
      (hΩminus_open.mem_nhds hzminus)
  have hvalue_eq : Fplus z0 = Fminus z0 := by
    rw [Filter.eventuallyEq_iff_exists_mem] at heq
    rcases heq with ⟨S, hS, hS_eq⟩
    exact hS_eq (mem_of_mem_nhds hS)
  have hplus_lim :
      Filter.Tendsto (fun ε : ℝ => Fplus (γplus ε))
        l (nhds (Fplus z0)) :=
    hFplus_cont.tendsto.comp (by simpa [z0] using hγplus)
  have hminus_lim :
      Filter.Tendsto (fun ε : ℝ => Fminus (γminus ε))
        l (nhds (Fplus z0)) := by
    have hraw :
        Filter.Tendsto (fun ε : ℝ => Fminus (γminus ε))
          l (nhds (Fminus z0)) :=
      hFminus_cont.tendsto.comp (by simpa [z0] using hγminus)
    simpa [hvalue_eq] using hraw
  simpa using hminus_lim.sub hplus_lim

omit [NeZero d] in
theorem reducedNormalFlattened_localEOW_eventuallyEq_at_spacelike_edge
    {m : ℕ} (i j : Fin (m + 1))
    (u0 : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ)
    (hu0 : u0 ∈
      reducedNormalFlattenedSelectedSpacelike (d := d) i j)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i j) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ reducedNormalFlattenedSelectedSpacelike (d := d) i j →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card (SpectatorIndex (m + 1) i j) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv
      (reducedNormalFlattenedSelectedSpacelike (d := d) i j))
    (hFplus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds : Ωplus ∈ nhds (SCV.realEmbed u0))
    (hminus_nhds : Ωminus ∈ nhds (SCV.realEmbed u0)) :
    Fplus =ᶠ[nhds (SCV.realEmbed u0)] Fminus := by
  have hq :
      0 < (d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1) := by
    omega
  exact
    SCV.local_continuous_edge_of_the_wedge_eventuallyEq_at_common_edge
      (m := (d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1))
      hq Ωplus Ωminus (reducedNormalFlattenedSelectedSpacelike (d := d) i j)
      C hΩplus_open hΩminus_open
      (isOpen_reducedNormalFlattenedSelectedSpacelike (d := d) i j)
      hC_open hC_conv hC_ne hlocal_wedge Fplus Fminus hFplus_diff
      hFminus_diff bv hbv_cont hFplus_bv hFminus_bv u0 hu0
      hplus_nhds hminus_nhds

omit [NeZero d] in
theorem reducedNormalFlattened_localEOW_two_rays_tendsto_sub_zero
    {m : ℕ} (i j : Fin (m + 1))
    (u0 : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ)
    (hu0 : u0 ∈
      reducedNormalFlattenedSelectedSpacelike (d := d) i j)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i j) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ reducedNormalFlattenedSelectedSpacelike (d := d) i j →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card (SpectatorIndex (m + 1) i j) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv
      (reducedNormalFlattenedSelectedSpacelike (d := d) i j))
    (hFplus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds : Ωplus ∈ nhds (SCV.realEmbed u0))
    (hminus_nhds : Ωminus ∈ nhds (SCV.realEmbed u0))
    {l : Filter ℝ}
    (γplus γminus : ℝ →
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)))
    (hγplus :
      Filter.Tendsto γplus l (nhds (SCV.realEmbed u0)))
    (hγminus :
      Filter.Tendsto γminus l (nhds (SCV.realEmbed u0))) :
    Filter.Tendsto
      (fun ε : ℝ => Fminus (γminus ε) - Fplus (γplus ε))
      l (nhds 0) := by
  let z0 :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) *
          (d + 1)) :=
    SCV.realEmbed u0
  have heq :
      Fplus =ᶠ[nhds z0] Fminus := by
    simpa [z0] using
      reducedNormalFlattened_localEOW_eventuallyEq_at_spacelike_edge
        (d := d) i j u0 hu0 Ωplus Ωminus C
        hΩplus_open hΩminus_open hC_open hC_conv hC_ne hlocal_wedge
        Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
        hFplus_bv hFminus_bv hplus_nhds hminus_nhds
  have hzplus : z0 ∈ Ωplus := by
    simpa [z0] using mem_of_mem_nhds hplus_nhds
  have hzminus : z0 ∈ Ωminus := by
    simpa [z0] using mem_of_mem_nhds hminus_nhds
  have hFplus_cont :
      ContinuousAt Fplus z0 :=
    hFplus_diff.continuousOn.continuousAt
      (hΩplus_open.mem_nhds hzplus)
  have hFminus_cont :
      ContinuousAt Fminus z0 :=
    hFminus_diff.continuousOn.continuousAt
      (hΩminus_open.mem_nhds hzminus)
  have hvalue_eq : Fplus z0 = Fminus z0 := by
    rw [Filter.eventuallyEq_iff_exists_mem] at heq
    rcases heq with ⟨S, hS, hS_eq⟩
    exact hS_eq (mem_of_mem_nhds hS)
  have hplus_lim :
      Filter.Tendsto (fun ε : ℝ => Fplus (γplus ε))
        l (nhds (Fplus z0)) :=
    hFplus_cont.tendsto.comp (by simpa [z0] using hγplus)
  have hminus_lim :
      Filter.Tendsto (fun ε : ℝ => Fminus (γminus ε))
        l (nhds (Fplus z0)) := by
    have hraw :
        Filter.Tendsto (fun ε : ℝ => Fminus (γminus ε))
          l (nhds (Fminus z0)) :=
      hFminus_cont.tendsto.comp (by simpa [z0] using hγminus)
    simpa [hvalue_eq] using hraw
  simpa using hminus_lim.sub hplus_lim

/-- Collar-local packaged canonical-ray branch data gives the pointwise
selected sign-flip boundary comparison.

Unlike `ReducedNormalLocalEOWBranchData.signFlip_pointwise`, this only uses
boundary data on the open collar carried by the packet.  This is the form
needed before the theorem-2 partition-of-unity step. -/
theorem ReducedNormalCanonicalRayEOWBranchDataOn.signFlip_pointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (D : ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let u0 :
      Fin ((d + 1) + Fintype.card (SpectatorIndex (m + 1) i j) *
        (d + 1)) → ℝ :=
    reducedNormalFlattenCLE (d := d) i j p
  have hEOW :
      Filter.Tendsto
        (fun ε : ℝ =>
          D.Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) -
            D.Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [u0, j] using
      reducedNormalFlattened_localEOW_two_rays_tendsto_sub_zero_at_open_edge
        (d := d) i j D.E u0 (by simpa [u0, j] using D.hpE)
        D.Ωplus D.Ωminus D.C D.hΩplus_open D.hΩminus_open
        D.hE_open D.hC_open D.hC_conv D.hC_ne D.hlocal_wedge
        D.Fplus D.Fminus D.hFplus_diff D.hFminus_diff D.bv
        D.hbv_cont D.hFplus_bv D.hFminus_bv
        D.hplus_nhds D.hminus_nhds
        (reducedNormalUpperCanonicalRay (d := d) i hi p)
        (reducedNormalLowerCanonicalRay (d := d) i hi p)
        (reducedNormalUpperCanonicalRay_tendsto (d := d) i hi p)
        (reducedNormalLowerCanonicalRay_tendsto (d := d) i hi p)
  refine Filter.Tendsto.congr' ?_ hEOW
  filter_upwards [D.hminus_rep, D.hplus_rep] with ε hminus hplus
  rw [hminus, hplus]

/-- Collar-local branch-specific reduced normal EOW handoff with asymptotic
branch transfer.

This is the local-collar version needed by the theorem-2 partition step: the
two side branches only have to live on an open real collar `E` around the
chosen reduced-normal point, and the OS-I `(4.14)` input is an asymptotic
transfer to the canonical reduced rays rather than finite-height equality. -/
theorem reducedNormalSignFlip_pointwise_of_localEOW_asymptoticBranchDataOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (E : Set (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hE_open : IsOpen E)
    (hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card
            (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ E →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card
              (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let u0 :
      Fin ((d + 1) + Fintype.card (SpectatorIndex (m + 1) i j) *
        (d + 1)) → ℝ :=
    reducedNormalFlattenCLE (d := d) i j p
  have hEOW :
      Filter.Tendsto
        (fun ε : ℝ =>
          Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) -
            Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [u0, j] using
      reducedNormalFlattened_localEOW_two_rays_tendsto_sub_zero_at_open_edge
        (d := d) i j E u0 (by simpa [u0, j] using hpE)
        Ωplus Ωminus C hΩplus_open hΩminus_open hE_open
        hC_open hC_conv hC_ne hlocal_wedge
        Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
        hFplus_bv hFminus_bv hplus_nhds hminus_nhds
        (reducedNormalUpperCanonicalRay (d := d) i hi p)
        (reducedNormalLowerCanonicalRay (d := d) i hi p)
        (reducedNormalUpperCanonicalRay_tendsto (d := d) i hi p)
        (reducedNormalLowerCanonicalRay_tendsto (d := d) i hi p)
  have hcombo :
      Filter.Tendsto
        (fun ε : ℝ =>
          (Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) -
              Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) -
              (Fminus (reducedNormalLowerCanonicalRay (d := d) i hi p ε) -
                canonicalReducedBranch (d := d) OS lgc m ε
                  (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                    (reducedAdjacent_succ_ne i hi)
                    (reducedSignFlip
                      (d := d) i ⟨i.val + 1, hi⟩ p)))) +
            (Fplus (reducedNormalUpperCanonicalRay (d := d) i hi p ε) -
              canonicalReducedBranch (d := d) OS lgc m ε
                (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi) p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa using (hEOW.sub hminus_transfer).add hplus_transfer
  refine Filter.Tendsto.congr' ?_ hcombo
  filter_upwards with ε
  ring

/-- Branch-specific reduced normal EOW handoff with asymptotic branch transfer.

This is the faithful OS-I `(4.14)` interface: the side branches supplied by the
local EOW argument need only have the same boundary approach as the canonical
reduced branches.  The older finite-height representation theorem below is the
special case where these transfer errors are eventually zero. -/
theorem reducedNormalSignFlip_pointwise_of_localEOW_asymptoticBranchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hp : p ∈ reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card
            (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card
              (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv
      (reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩))
    (hFplus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (γplus γminus : ℝ →
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)))
    (hγplus :
      Filter.Tendsto γplus
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds
          (SCV.realEmbed
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))))
    (hγminus :
      Filter.Tendsto γminus
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds
          (SCV.realEmbed
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          Fplus (γplus ε) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          Fminus (γminus ε) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let u0 :
      Fin ((d + 1) + Fintype.card (SpectatorIndex (m + 1) i j) *
        (d + 1)) → ℝ :=
    reducedNormalFlattenCLE (d := d) i j p
  have hu0 :
      u0 ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j := by
    rw [reducedNormalFlattenedSelectedSpacelike_iff]
    simpa [u0, j] using hp
  have hEOW :
      Filter.Tendsto
        (fun ε : ℝ => Fminus (γminus ε) - Fplus (γplus ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [u0, j] using
      reducedNormalFlattened_localEOW_two_rays_tendsto_sub_zero
        (d := d) i j u0 hu0 Ωplus Ωminus C
        hΩplus_open hΩminus_open hC_open hC_conv hC_ne hlocal_wedge
        Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
        hFplus_bv hFminus_bv hplus_nhds hminus_nhds
        γplus γminus hγplus hγminus
  have hcombo :
      Filter.Tendsto
        (fun ε : ℝ =>
          (Fminus (γminus ε) - Fplus (γplus ε) -
              (Fminus (γminus ε) -
                canonicalReducedBranch (d := d) OS lgc m ε
                  (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                    (reducedAdjacent_succ_ne i hi)
                    (reducedSignFlip
                      (d := d) i ⟨i.val + 1, hi⟩ p)))) +
            (Fplus (γplus ε) -
              canonicalReducedBranch (d := d) OS lgc m ε
                (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi) p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa using (hEOW.sub hminus_transfer).add hplus_transfer
  refine Filter.Tendsto.congr' ?_ hcombo
  filter_upwards with ε
  ring

/-- Branch-specific reduced normal EOW handoff.

This is the exact pointwise conclusion consumed by
`adjacentReducedRuelleDistributionalLimit_of_normalSignFlip_pointwise`, with
the remaining OS/Ruelle payload left visible: the side domains, holomorphy,
common boundary value, and concrete representation of the canonical and
sign-flipped reduced branches by the two approach rays. -/
theorem reducedNormalSignFlip_pointwise_of_localEOW_branchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hp : p ∈ reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩)
    (Ωplus Ωminus : Set
      (SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1))))
    (C : Set (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin ((d + 1) +
          Fintype.card
            (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
            (d + 1)) → ℝ),
        IsCompact K →
        K ⊆ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ →
        ∀ Kη : Set (Fin ((d + 1) +
            Fintype.card
              (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
              (d + 1)) → ℝ),
          IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  Ωminus)
    (Fplus Fminus :
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)) → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv
      (reducedNormalFlattenedSelectedSpacelike
        (d := d) i ⟨i.val + 1, hi⟩))
    (hFplus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ reducedNormalFlattenedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)))
    (hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)))
    (γplus γminus : ℝ →
      SCV.ComplexChartSpace ((d + 1) +
        Fintype.card
          (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
          (d + 1)))
    (hγplus :
      Filter.Tendsto γplus
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds
          (SCV.realEmbed
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))))
    (hγminus :
      Filter.Tendsto γminus
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds
          (SCV.realEmbed
            (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p))))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fplus (γplus ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fminus (γminus ε) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  refine
    reducedNormalSignFlip_pointwise_of_localEOW_asymptoticBranchData
      (d := d) OS lgc i hi p hp Ωplus Ωminus C
      hΩplus_open hΩminus_open hC_open hC_conv hC_ne hlocal_wedge
      Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
      hFplus_bv hFminus_bv hplus_nhds hminus_nhds
      γplus γminus hγplus hγminus ?_ ?_
  · refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0))
    filter_upwards [hplus_rep] with ε hplus
    simp [hplus]
  · refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0))
    filter_upwards [hminus_rep] with ε hminus
    simp [hminus]

/-- Packaged branch-data form of the reduced normal EOW handoff. -/
theorem ReducedNormalLocalEOWBranchData.signFlip_pointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hp : p ∈ reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩)
    (D : ReducedNormalLocalEOWBranchData (d := d) OS lgc i hi p) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  exact
    reducedNormalSignFlip_pointwise_of_localEOW_branchData
      (d := d) OS lgc i hi p hp
      D.Ωplus D.Ωminus D.C
      D.hΩplus_open D.hΩminus_open D.hC_open D.hC_conv D.hC_ne
      D.hlocal_wedge D.Fplus D.Fminus D.hFplus_diff D.hFminus_diff
      D.bv D.hbv_cont D.hFplus_bv D.hFminus_bv
      D.hplus_nhds D.hminus_nhds D.γplus D.γminus
      D.hγplus D.hγminus D.hplus_rep D.hminus_rep

end AdjacentNormal
end OSReconstruction
