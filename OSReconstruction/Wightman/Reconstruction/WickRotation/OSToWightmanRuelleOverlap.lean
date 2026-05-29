/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.JostRuelleStep5
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving

/-!
# Ruelle Overlap Surface for BHW Branches

This file records the OS-free domain surface for the Appendix-II Ruelle
patching step used by the Theorem-2 `E -> R` locality path.  The actual hard
uniqueness theorem is not hidden here; the definitions below expose the overlap
`T'_n ∩ πT'_n`, the patching union, and the already available holomorphy and
complex-Lorentz invariance inputs for the two BHW branches.
-/

noncomputable section

open Complex Topology MeasureTheory Filter Matrix LorentzLieGroup

namespace BHW

/-- The Ruelle overlap `T'_n ∩ πT'_n` for a single permutation sector. -/
def ruelleOverlapDomain (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n τ

/-- The Ruelle patching domain `T'_n ∪ πT'_n`. -/
def ruelleUnionDomain (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  BHW.ExtendedTube d n ∪ BHW.permutedExtendedTubeSector d n τ

theorem ruelleOverlap_subset_extendedTube
    {d n : ℕ} {τ : Equiv.Perm (Fin n)} :
    BHW.ruelleOverlapDomain d n τ ⊆ BHW.ExtendedTube d n := by
  intro z hz
  exact hz.1

theorem ruelleOverlap_subset_permutedSector
    {d n : ℕ} {τ : Equiv.Perm (Fin n)} :
    BHW.ruelleOverlapDomain d n τ ⊆
      BHW.permutedExtendedTubeSector d n τ := by
  intro z hz
  exact hz.2

theorem ruelleOverlap_subset_union
    {d n : ℕ} {τ : Equiv.Perm (Fin n)} :
    BHW.ruelleOverlapDomain d n τ ⊆ BHW.ruelleUnionDomain d n τ := by
  intro z hz
  exact Or.inl hz.1

/-- Adjacent Ruelle overlap domains are nonempty.

This is the nonemptiness half of the adjacent Ruelle connectedness input used
by the theorem-2 locality route.  The remaining geometric content is
preconnectedness of this same overlap; once that is supplied, the next theorem
turns it into the `IsConnected` hypothesis consumed by the local OS45/Ruelle
branch packets. -/
theorem ruelleOverlapDomain_adjacent_nonempty
    {d n : ℕ} [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n) :
    (BHW.ruelleOverlapDomain d n
      (Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty := by
  rcases BHW.permutedExtendedTubeSector_adjacent_overlap_nonempty
      (d := d) (n := n) (π := 1) i hi with
    ⟨z, hz_id, hz_swap⟩
  refine ⟨z, ?_⟩
  constructor
  · simpa [BHW.permutedExtendedTubeSector] using hz_id
  · simpa [BHW.ruelleOverlapDomain] using hz_swap

/-- Adjacent Ruelle overlap connectedness reduced to preconnectedness.

The explicit adjacent-overlap witness above supplies the point needed for
`IsConnected`; future Ruelle-geometry work only has to prove that the overlap
is preconnected. -/
theorem ruelleOverlapDomain_adjacent_isConnected_of_isPreconnected
    {d n : ℕ} [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n)
    (hpre :
      IsPreconnected
        (BHW.ruelleOverlapDomain d n
          (Equiv.swap i ⟨i.val + 1, hi⟩))) :
    IsConnected
      (BHW.ruelleOverlapDomain d n
        (Equiv.swap i ⟨i.val + 1, hi⟩)) :=
  ⟨BHW.ruelleOverlapDomain_adjacent_nonempty (d := d) (n := n) i hi, hpre⟩

/-- Adjacent Ruelle overlap nonemptiness in the exact `permAct` shape consumed
by the OS45/Ruelle branch-equality theorems. -/
theorem extendedTube_permAct_adjacent_overlap_nonempty
    {d n : ℕ} [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n) :
    ({z : Fin n → Fin (d + 1) → ℂ |
      z ∈ BHW.ExtendedTube d n ∧
        BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
          BHW.ExtendedTube d n}).Nonempty := by
  rcases BHW.ruelleOverlapDomain_adjacent_nonempty
      (d := d) (n := n) i hi with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa [BHW.ruelleOverlapDomain, BHW.permutedExtendedTubeSector,
    BHW.permAct] using hz

/-- Consumer-shape adjacent Ruelle connectedness reduced to preconnectedness. -/
theorem extendedTube_permAct_adjacent_overlap_isConnected_of_isPreconnected
    {d n : ℕ} [NeZero d]
    (i : Fin n) (hi : i.val + 1 < n)
    (hpre :
      IsPreconnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n}) :
    IsConnected
      {z : Fin n → Fin (d + 1) → ℂ |
        z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
            BHW.ExtendedTube d n} :=
  ⟨BHW.extendedTube_permAct_adjacent_overlap_nonempty
      (d := d) (n := n) i hi, hpre⟩

theorem isOpen_ruelleOverlapDomain
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    IsOpen (BHW.ruelleOverlapDomain d n τ) := by
  exact BHW.isOpen_extendedTube.inter
    (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) τ)

theorem isOpen_ruelleUnionDomain
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    IsOpen (BHW.ruelleUnionDomain d n τ) := by
  exact BHW.isOpen_extendedTube.union
    (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) τ)

/-- Analytic and complex-Lorentz-invariance inputs needed by the Ruelle
overlap theorem for an abstract pair of branches. -/
def RuelleOverlapAnalyticInputs
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ford Fperm : (Fin n → Fin (d + 1) → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ Ford (BHW.ruelleOverlapDomain d n τ) ∧
    DifferentiableOn ℂ Fperm (BHW.ruelleOverlapDomain d n τ) ∧
    BHW.ComplexLorentzInvariantOn d n
      (BHW.ruelleOverlapDomain d n τ) Ford ∧
    BHW.ComplexLorentzInvariantOn d n
      (BHW.ruelleOverlapDomain d n τ) Fperm

theorem ruelle_ordBranch_holomorphicOn_overlap
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (BHW.extendF (bvt_F OS lgc n))
      (BHW.ruelleOverlapDomain d n τ) := by
  exact
    (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).mono
      (BHW.ruelleOverlap_subset_extendedTube (d := d) (n := n) (τ := τ))

theorem ruelle_permBranch_holomorphicOn_overlap
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z))
      (BHW.ruelleOverlapDomain d n τ) := by
  exact
    (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
      (d := d) OS lgc n τ).mono
      (by
        intro z hz
        simpa [BHW.ruelleOverlapDomain,
          BHW.permutedExtendedTubeSector, BHW.permAct] using hz.2)

theorem ruelle_ordBranch_invariantOn_overlap
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    BHW.ComplexLorentzInvariantOn d n
      (BHW.ruelleOverlapDomain d n τ)
      (BHW.extendF (bvt_F OS lgc n)) := by
  intro Λ z hz hΛz
  exact
    BHW.complexLorentzInvariantOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n Λ z hz.1 hΛz.1

theorem ruelle_permBranch_invariantOn_overlap
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    BHW.ComplexLorentzInvariantOn d n
      (BHW.ruelleOverlapDomain d n τ)
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z)) := by
  intro Λ z hz hΛz
  exact
    BHW.complexLorentzInvariantOn_extendF_bvt_F_permAct_permutedSector
      (d := d) OS lgc n τ Λ z hz.2 hΛz.2

/-- The actual OS branch pair supplies all analytic and invariance inputs for
the Ruelle overlap theorem.  The missing production theorem is the
distributional-boundary-value uniqueness step that consumes these inputs. -/
theorem ruelleOverlapAnalyticInputs_extendF_pair
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    BHW.RuelleOverlapAnalyticInputs d n τ
      (BHW.extendF (bvt_F OS lgc n))
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z)) := by
  exact ⟨
    BHW.ruelle_ordBranch_holomorphicOn_overlap OS lgc n τ,
    BHW.ruelle_permBranch_holomorphicOn_overlap OS lgc n τ,
    BHW.ruelle_ordBranch_invariantOn_overlap OS lgc n τ,
    BHW.ruelle_permBranch_invariantOn_overlap OS lgc n τ⟩

/-- Real Schwartz test space for the Ruelle distributional boundary
hypothesis. -/
abbrev RuelleRealTestSpace (d n : ℕ) :=
  SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ

/-- Distributional agreement on a real-open patch.  This is the boundary input
Jost's Appendix II theorem should consume; pointwise equality on real points is
not the active OS-45 hypothesis. -/
def RuelleDistributionalBoundaryAgreementOn
    (d n : ℕ) (_τ : Equiv.Perm (Fin n))
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (Tord Tperm : BHW.RuelleRealTestSpace d n →L[ℂ] ℂ) : Prop :=
  ∀ ρ : BHW.RuelleRealTestSpace d n,
    tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ V →
      Tord ρ = Tperm ρ

/-- The analytic conclusion of Ruelle's overlap uniqueness theorem. -/
def RuelleOverlapConclusion
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ford Fperm : (Fin n → Fin (d + 1) → ℂ) → ℂ) : Prop :=
  Set.EqOn Ford Fperm (BHW.ruelleOverlapDomain d n τ)

/-- A local Wick-section distributional identity propagates through any
connected open subset of the Ruelle overlap.  This is the currently available
identity-theorem reducer; the full Ruelle Appendix-II theorem still has to
produce the real-open Wick-section hypothesis from the spacelike overlap
boundary data. -/
theorem ruelleOverlap_eqOn_of_distributional_wickSection_eq_on_realOpen
    {d n : ℕ} [NeZero d] {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (NPointDomain d n)}
    {Ford Fperm : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hU_sub : U ⊆ BHW.ruelleOverlapDomain d n τ)
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_wick : ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U)
    (hinputs : BHW.RuelleOverlapAnalyticInputs d n τ Ford Fperm)
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            Ford (fun k => wickRotatePoint (x k)) * φ x =
          ∫ x : NPointDomain d n,
            Fperm (fun k => wickRotatePoint (x k)) * φ x) :
    Set.EqOn Ford Fperm U := by
  exact eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
    (d := d) (n := n) U V hU_open hU_connected hV_open hV_nonempty
    hV_wick Ford Fperm
    ((hinputs.1).mono hU_sub)
    ((hinputs.2.1).mono hU_sub)
    hint

/-- Real-section form of the Ruelle overlap reducer.  This is the direct
Jost/Ruelle boundary shape: compact-test distributional agreement on a
real-open patch inside the overlap first gives pointwise agreement there, and
then the totally-real identity theorem propagates through the connected
complex overlap domain. -/
theorem ruelleOverlap_eqOn_of_distributional_realSection_eq_on_realOpen
    {d n : ℕ} [NeZero d] {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    {Ford Fperm : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hU_sub : U ⊆ BHW.ruelleOverlapDomain d n τ)
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_real : ∀ x ∈ V, SCV.realToComplexProduct x ∈ U)
    (hinputs : BHW.RuelleOverlapAnalyticInputs d n τ Ford Fperm)
    (hint :
      ∀ ρ : BHW.RuelleRealTestSpace d n,
        HasCompactSupport
          (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
        tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        ∫ x : Fin n → Fin (d + 1) → ℝ,
            Ford (SCV.realToComplexProduct x) * ρ x =
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            Fperm (SCV.realToComplexProduct x) * ρ x) :
    Set.EqOn Ford Fperm U := by
  let realSection : (Fin n → Fin (d + 1) → ℝ) →
      (Fin n → Fin (d + 1) → ℂ) := SCV.realToComplexProduct
  have hFord_holo : DifferentiableOn ℂ Ford U :=
    hinputs.1.mono hU_sub
  have hFperm_holo : DifferentiableOn ℂ Fperm U :=
    hinputs.2.1.mono hU_sub
  have hFord_cont : ContinuousOn Ford U := by
    intro z hz
    exact (hFord_holo z hz).continuousWithinAt
  have hFperm_cont : ContinuousOn Fperm U := by
    intro z hz
    exact (hFperm_holo z hz).continuousWithinAt
  have hreal_cont : Continuous realSection := by
    dsimp [realSection, SCV.realToComplexProduct]
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply k))
  have hFord_real_cont :
      ContinuousOn (fun x => Ford (realSection x)) V := by
    refine hFord_cont.comp hreal_cont.continuousOn ?_
    intro x hx
    exact hV_real x hx
  have hFperm_real_cont :
      ContinuousOn (fun x => Fperm (realSection x)) V := by
    refine hFperm_cont.comp hreal_cont.continuousOn ?_
    intro x hx
    exact hV_real x hx
  have hEqOn_real :
      Set.EqOn
        (fun x => Ford (realSection x))
        (fun x => Fperm (realSection x)) V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hFord_real_cont hFperm_real_cont ?_
    intro ρ hρ_compact hρ_tsupport
    exact hint ρ hρ_compact hρ_tsupport
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => Ford z - Fperm z
  have hHdiff_holo : DifferentiableOn ℂ Hdiff U :=
    hFord_holo.sub hFperm_holo
  have hHdiff_zero :
      ∀ x ∈ V, Hdiff (SCV.realToComplexProduct x) = 0 := by
    intro x hx
    exact sub_eq_zero.mpr (hEqOn_real hx)
  have hzero_on_U :=
    SCV.identity_theorem_totally_real_product
      (hD_open := hU_open) (hD_conn := hU_connected)
      (f := Hdiff) hHdiff_holo hV_open hV_nonempty hV_real
      hHdiff_zero
  intro z hz
  exact sub_eq_zero.mp (hzero_on_U z hz)

/-- Linear-section form of the Ruelle overlap reducer.  This is the coordinate
version needed for OS45 common-edge charts: a complex-linear change of
coordinates on the analytic variables and a real-linear change of coordinates
on the boundary variables reduce the boundary slice to the standard totally
real product section. -/
theorem ruelleOverlap_eqOn_of_distributional_linearRealSection_eq_on_realOpen
    {d n : ℕ} [NeZero d] {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    {Ford Fperm : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (L : ((Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ)))
    (R : ((Fin n → Fin (d + 1) → ℝ) ≃L[ℝ]
      (Fin n → Fin (d + 1) → ℝ)))
    (hU_sub : U ⊆ BHW.ruelleOverlapDomain d n τ)
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_section : ∀ x ∈ V,
      L (SCV.realToComplexProduct (R x)) ∈ U)
    (hinputs : BHW.RuelleOverlapAnalyticInputs d n τ Ford Fperm)
    (hint :
      ∀ ρ : BHW.RuelleRealTestSpace d n,
        HasCompactSupport
          (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
        tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        (∫ x : Fin n → Fin (d + 1) → ℝ,
            Ford (L (SCV.realToComplexProduct (R x))) * ρ x) =
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            Fperm (L (SCV.realToComplexProduct (R x))) * ρ x) :
    Set.EqOn Ford Fperm U := by
  let sectionMap : (Fin n → Fin (d + 1) → ℝ) →
      (Fin n → Fin (d + 1) → ℂ) := fun x =>
    L (SCV.realToComplexProduct (R x))
  have hFord_holo : DifferentiableOn ℂ Ford U :=
    hinputs.1.mono hU_sub
  have hFperm_holo : DifferentiableOn ℂ Fperm U :=
    hinputs.2.1.mono hU_sub
  have hFord_cont : ContinuousOn Ford U := by
    intro z hz
    exact (hFord_holo z hz).continuousWithinAt
  have hFperm_cont : ContinuousOn Fperm U := by
    intro z hz
    exact (hFperm_holo z hz).continuousWithinAt
  have hreal_cont : Continuous
      (fun x : Fin n → Fin (d + 1) → ℝ =>
        SCV.realToComplexProduct x) := by
    dsimp [SCV.realToComplexProduct]
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply k))
  have hsection_cont : Continuous sectionMap := by
    exact L.continuous.comp (hreal_cont.comp R.continuous)
  have hFord_real_cont :
      ContinuousOn (fun x => Ford (sectionMap x)) V := by
    refine hFord_cont.comp hsection_cont.continuousOn ?_
    intro x hx
    exact hV_section x hx
  have hFperm_real_cont :
      ContinuousOn (fun x => Fperm (sectionMap x)) V := by
    refine hFperm_cont.comp hsection_cont.continuousOn ?_
    intro x hx
    exact hV_section x hx
  have hEqOn_real :
      Set.EqOn
        (fun x => Ford (sectionMap x))
        (fun x => Fperm (sectionMap x)) V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hFord_real_cont hFperm_real_cont ?_
    intro ρ hρ_compact hρ_tsupport
    simpa [sectionMap] using hint ρ hρ_compact hρ_tsupport
  let Dpre : Set (Fin n → Fin (d + 1) → ℂ) := {z | L z ∈ U}
  have hDpre_open : IsOpen Dpre := by
    simpa [Dpre] using hU_open.preimage L.continuous
  have hDpre_connected : IsConnected Dpre := by
    have himage : L.symm '' U = Dpre := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [Dpre] using hw
      · intro hz
        refine ⟨L z, ?_, ?_⟩
        · simpa [Dpre] using hz
        · simp
    rw [← himage]
    exact hU_connected.image L.symm L.symm.continuous.continuousOn
  let Vpre : Set (Fin n → Fin (d + 1) → ℝ) := R '' V
  have hVpre_open : IsOpen Vpre := by
    simpa [Vpre] using R.toHomeomorph.isOpenMap V hV_open
  have hVpre_nonempty : Vpre.Nonempty := by
    rcases hV_nonempty with ⟨x, hx⟩
    exact ⟨R x, ⟨x, hx, rfl⟩⟩
  have hVpre_sub :
      ∀ y ∈ Vpre, SCV.realToComplexProduct y ∈ Dpre := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [Dpre] using hV_section x hx
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    Ford (L z) - Fperm (L z)
  have hHdiff_holo : DifferentiableOn ℂ Hdiff Dpre := by
    have hmaps : Set.MapsTo L Dpre U := by
      intro z hz
      simpa [Dpre] using hz
    exact (hFord_holo.comp L.differentiableOn hmaps).sub
      (hFperm_holo.comp L.differentiableOn hmaps)
  have hHdiff_zero :
      ∀ y ∈ Vpre, Hdiff (SCV.realToComplexProduct y) = 0 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact sub_eq_zero.mpr (hEqOn_real hx)
  have hzero_on_Dpre :=
    SCV.identity_theorem_totally_real_product
      (hD_open := hDpre_open) (hD_conn := hDpre_connected)
      (f := Hdiff) hHdiff_holo hVpre_open hVpre_nonempty
      hVpre_sub hHdiff_zero
  intro z hz
  have hzpre : L.symm z ∈ Dpre := by
    simpa [Dpre] using hz
  have hzero : Hdiff (L.symm z) = 0 :=
    hzero_on_Dpre (L.symm z) hzpre
  exact sub_eq_zero.mp (by simpa [Hdiff] using hzero)

/-- Concrete `extendF`/permuted-`extendF` specialization of the local Ruelle
overlap reducer. -/
theorem ruelleOverlap_extendF_pair_eqOn_of_distributional_wickSection_eq_on_realOpen
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (NPointDomain d n)}
    (hU_sub : U ⊆ BHW.ruelleOverlapDomain d n τ)
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_wick : ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U)
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (fun k => wickRotatePoint (x k)) * φ x =
          ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) τ
                (fun k => wickRotatePoint (x k))) * φ x) :
    Set.EqOn
      (BHW.extendF (bvt_F OS lgc n))
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ z)) U := by
  exact BHW.ruelleOverlap_eqOn_of_distributional_wickSection_eq_on_realOpen
    (d := d) (n := n) (τ := τ) (U := U) (V := V)
    (Ford := BHW.extendF (bvt_F OS lgc n))
    (Fperm := fun z : Fin n → Fin (d + 1) → ℂ =>
      BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z))
    hU_sub hU_open hU_connected hV_open hV_nonempty hV_wick
    (BHW.ruelleOverlapAnalyticInputs_extendF_pair OS lgc n τ)
    hint

/-- Concrete `extendF`/permuted-`extendF` specialization of the real-section
Ruelle overlap reducer. -/
theorem ruelleOverlap_extendF_pair_eqOn_of_distributional_realSection_eq_on_realOpen
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU_sub : U ⊆ BHW.ruelleOverlapDomain d n τ)
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_real : ∀ x ∈ V, SCV.realToComplexProduct x ∈ U)
    (hint :
      ∀ ρ : BHW.RuelleRealTestSpace d n,
        HasCompactSupport
          (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
        tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        ∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              (SCV.realToComplexProduct x) * ρ x =
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) τ
                (SCV.realToComplexProduct x)) * ρ x) :
    Set.EqOn
      (BHW.extendF (bvt_F OS lgc n))
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ z)) U := by
  exact BHW.ruelleOverlap_eqOn_of_distributional_realSection_eq_on_realOpen
    (d := d) (n := n) (τ := τ) (U := U) (V := V)
    (Ford := BHW.extendF (bvt_F OS lgc n))
    (Fperm := fun z : Fin n → Fin (d + 1) → ℂ =>
      BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z))
    hU_sub hU_open hU_connected hV_open hV_nonempty hV_real
    (BHW.ruelleOverlapAnalyticInputs_extendF_pair OS lgc n τ)
    hint

/-- If Ruelle/Jost supplies equality of the ordinary and selected permuted
`extendF` branches on a complex neighborhood containing the horizontal OS45
common-edge section, then the source common-edge pulled real branches agree on
the corresponding source window. -/
theorem os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hmem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        Ucx) :
    ∀ u ∈ U,
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  intro u hu
  let zc : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  have hbranch_eq :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ zc) =
        BHW.extendF (bvt_F OS lgc n) zc := by
    exact (heq (hmem u hu)).symm
  have hAdj :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ zc) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simpa [zc] using
      BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P) u
  have hOrd :
      BHW.extendF (bvt_F OS lgc n) zc =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simp [BHW.os45PulledRealBranch, zc]
  calc
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
        = BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) := hAdj.symm
    _ = BHW.extendF (bvt_F OS lgc n) zc := hbranch_eq
    _ = BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) := hOrd

/-- Ruelle overlap equality on a neighborhood of the horizontal OS45
common-edge section feeds the checked flat EOW bridge directly. -/
theorem os45_initialSectorEqOn_open_of_ruelleOverlap_extendF_pair_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hmem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        Ucx)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ U) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  have hsource_eq :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) :=
    BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
      (d := d) hd OS lgc (P := P) (U := U) (Ucx := Ucx)
      hmem heq
  exact
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn
      (d := d) hd OS lgc (P := P) hU_open hU_sub hsource_eq
      ys hys_mem hys_li u0 hu0

/-- Linear real-section form of the OS45 Ruelle-to-flat splice, with the
boundary-distribution equality left as the explicit remaining hypothesis. -/
theorem os45_initialSectorEqOn_open_of_ruelle_linearReal_boundary
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub : Usrc ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    (L : ((Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ)))
    (R : ((Fin n → Fin (d + 1) → ℝ) ≃L[ℝ]
      (Fin n → Fin (d + 1) → ℝ)))
    (hUcx_sub : Ucx ⊆ BHW.ruelleOverlapDomain d n P.τ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_section : ∀ x ∈ V,
      L (SCV.realToComplexProduct (R x)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ Usrc,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (hint :
      ∀ ρ : BHW.RuelleRealTestSpace d n,
        HasCompactSupport
          (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
        tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        (∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              (L (SCV.realToComplexProduct (R x))) * ρ x) =
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                (L (SCV.realToComplexProduct (R x)))) * ρ x)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ Usrc) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  have heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        Ucx :=
    BHW.ruelleOverlap_eqOn_of_distributional_linearRealSection_eq_on_realOpen
      (d := d) (n := n) (τ := P.τ) (U := Ucx) (V := V)
      (Ford := BHW.extendF (bvt_F OS lgc n))
      (Fperm := fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z))
      L R hUcx_sub hUcx_open hUcx_connected hV_open hV_nonempty
      hV_section
      (BHW.ruelleOverlapAnalyticInputs_extendF_pair OS lgc n P.τ)
      hint
  exact
    BHW.os45_initialSectorEqOn_open_of_ruelleOverlap_extendF_pair_eqOn
      (d := d) hd OS lgc (P := P) hUsrc_open hUsrc_sub
      (Ucx := Ucx) hcommon_mem heq ys hys_mem hys_li u0 hu0

/-- OS45 specialization of the Ruelle-to-flat splice.  The remaining `hint`
is the compact-test boundary equality on the Figure-2-4 real source window;
the theorem only wires that book-step hypothesis into the checked Ruelle
overlap reducer and flat EOW consumer. -/
theorem os45_initialSectorEqOn_open_of_ruelle_commonEdge_boundary
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub : Usrc ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hUcx_sub : Ucx ⊆ BHW.ruelleOverlapDomain d n P.τ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hcommon_mem :
      ∀ u ∈ Usrc,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (hint :
      ∀ ρ : BHW.RuelleRealTestSpace d n,
        HasCompactSupport
          (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
        tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ Usrc →
        (∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (SCV.realToComplexProduct
                  (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) x))) * ρ x) =
          ∫ x : Fin n → Fin (d + 1) → ℝ,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                  (SCV.realToComplexProduct
                    (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) x)))) * ρ x)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ Usrc) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  let L : ((Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ)) :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
  let R : ((Fin n → Fin (d + 1) → ℝ) ≃L[ℝ]
      (Fin n → Fin (d + 1) → ℝ)) :=
    BHW.os45CommonEdgeRealCLE (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  have hsection :
      ∀ x ∈ Usrc, L (SCV.realToComplexProduct (R x)) ∈ Ucx := by
    intro x hx
    simpa [L, R, BHW.realEmbed, SCV.realToComplexProduct] using
      hcommon_mem x hx
  exact
    BHW.os45_initialSectorEqOn_open_of_ruelle_linearReal_boundary
      (d := d) hd OS lgc (P := P) hUsrc_open hUsrc_sub
      (Ucx := Ucx) (V := Usrc) L R hUcx_sub hUcx_open
      hUcx_connected hUsrc_open ⟨u0, hu0⟩ hsection hcommon_mem
      (by
        intro ρ hρ_compact hρ_tsupport
        simpa [L, R] using hint ρ hρ_compact hρ_tsupport)
      ys hys_mem hys_li u0 hu0

/-- Selected distributional Jost anchor data supplies the concrete OS45
common-edge compact-test boundary packet consumed by the Ruelle splice.

This is the faithful selected-data form of the Appendix-II real-boundary
input: it produces equality of the ordinary and adjacent `extendF` branches
only after the test support is localized in the Figure-2-4 source window. -/
theorem os45_ruelle_commonEdge_boundary_hint_of_selectedJostData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      ∀ (j : Fin n) (hj : j.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_sub : Usrc ⊆ P.V) :
    ∀ ρ : BHW.RuelleRealTestSpace d n,
      HasCompactSupport
        (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
      tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ Usrc →
      (∫ x : Fin n → Fin (d + 1) → ℝ,
          BHW.extendF (bvt_F OS lgc n)
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (SCV.realToComplexProduct
                (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x))) * ρ x) =
        ∫ x : Fin n → Fin (d + 1) → ℝ,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (SCV.realToComplexProduct
                  (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) x)))) * ρ x := by
  intro ρ _hρ_compact hρ_tsupport
  let hEdge : SelectedAdjacentPermutationEdgeData OS lgc n :=
    bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData
      (d := d) OS lgc n hOverlap hData
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxU : x ∈ Usrc
  · have hxP : x ∈ P.V := hUsrc_sub hxU
    let z : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))
    have hz_overlap :
        z ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [z] using
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure hxP)
    have hz : z ∈ BHW.ExtendedTube d n := hz_overlap.1
    have hτz :
        BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n := by
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using
        hz_overlap.2
    have hpoint :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) =
          BHW.extendF (bvt_F OS lgc n) z := by
      simpa [P.τ_eq] using
        bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
          (d := d) OS lgc n hEdge i hi z hz
          (by simpa [P.τ_eq] using hτz)
    change
      BHW.extendF (bvt_F OS lgc n) z * ρ x =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) * ρ x
    rw [hpoint]
  · have hρ_zero : ρ x = 0 := by
      exact image_eq_zero_of_notMem_tsupport
        (fun hx_ts => hxU (hρ_tsupport hx_ts))
    simp [hρ_zero]

/-- Selected adjacent Jost data plus adjacent overlap connectedness supplies the
local initial-sector equality seed used by the Figure-2-4 flat common-chart
route.

This is the production version of the selected-data replacement for the long
fixed-selector proof: the hard inputs are the selected real-boundary packet and
the adjacent ET-overlap connectedness, and the conclusion is exactly the
connected open `EqOn` seed consumed by the Ruelle splice. -/
theorem os45_flat_seed_of_selectedJostData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      ∀ (j : Fin n) (hj : j.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub : Usrc ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hUcx_sub : Ucx ⊆ BHW.ruelleOverlapDomain d n P.τ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hcommon_mem :
      ∀ u ∈ Usrc,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ Usrc) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  exact
    os45_initialSectorEqOn_open_of_ruelle_commonEdge_boundary
      (d := d) hd OS lgc (P := P) hUsrc_open hUsrc_sub
      (Ucx := Ucx) hUcx_sub hUcx_open hUcx_connected
      hcommon_mem
      (os45_ruelle_commonEdge_boundary_hint_of_selectedJostData
        (d := d) hd OS lgc (P := P) hOverlap hData hUsrc_sub)
      ys hys_mem hys_li u0 hu0

/-- The post-Ruelle tail of the OS45 Hdiff producer.

Once a connected local initial-sector `EqOn` seed has been supplied at the flat
common edge, the existing `S'_n` local branch machinery produces the local
holomorphic difference germ.  This theorem intentionally leaves the seed as an
explicit input; the genuine producer for that input is
`os45_flat_seed_of_selectedJostData`, not an individual zero-height selector. -/
theorem os45_hdiff_of_flat_seed
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (U : Set (NPointDomain d n))
    (u0 : NPointDomain d n)
    (_hu0 : u0 ∈ U)
    (hU_sub : U ⊆ P.V)
    (hflat_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧
        IsPreconnected W ∧
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n))
                u0))) ∈ W ∧
        W ⊆
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  rcases hflat_seed with
    ⟨Wflat, hWflat_open, hWflat_pre, hzseedW, hWflat_sub,
      hWflat_eq⟩
  let zseed : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.unflattenCfg n d (SCV.realEmbed (e u0)))
  have hzseed_overlap :
      zseed ∈ H.ΩJ ∩ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    have hzET : zseed ∈ BHW.ExtendedTube d n := (hWflat_sub hzseedW).1
    have hzPerm : zseed ∈ BHW.permutedExtendedTubeSector d n P.τ :=
      (hWflat_sub hzseedW).2
    exact ⟨⟨H.extendedTube_subset_ΩJ hzET, hzET⟩, hzPerm⟩
  have hSPrime_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ IsPreconnected W ∧ zseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W := by
    refine
      ⟨Wflat, hWflat_open, hWflat_pre, by simpa [zseed, e] using hzseedW,
        ?_, hWflat_eq⟩
    intro z hz
    have hzET : z ∈ BHW.ExtendedTube d n := (hWflat_sub hz).1
    have hzPerm : z ∈ BHW.permutedExtendedTubeSector d n P.τ :=
      (hWflat_sub hz).2
    have hzΩ : z ∈ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase := by
      have hzΩJ : z ∈ H.ΩJ := H.extendedTube_subset_ΩJ hzET
      simpa [H.ΩJ_eq_localSPrimeTwoSectorHull] using hzΩJ
    exact ⟨⟨hzΩ, hzET⟩, hzPerm⟩
  let S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H :=
    BHW.os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt
      (d := d) hd OS lgc H zseed hzseed_overlap hSPrime_seed
  refine
    ⟨H.ΩJ, (fun _ => (0 : ℂ)), H.ΩJ_open, H.ΩJ_connected,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact H.ordinaryWick_mem u (hU_sub hu)
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      change
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ
      exact
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    exact H.extendedTube_subset_ΩJ hzc_overlap.1
  · exact differentiableOn_const (c := (0 : ℂ))
  · intro φ _hφ_compact _hφU
    simp
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      change
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ
      exact
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    have hzcΩ : zc ∈ H.ΩJ := H.extendedTube_subset_ΩJ hzc_overlap.1
    have hOrd :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n) zc :=
      S.eq_ordinary ⟨hzc_overlap.1, hzcΩ⟩
    have hAdj :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) :=
      S.eq_adjacent ⟨hzc_overlap.2, hzcΩ⟩
    have hEq :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.extendF (bvt_F OS lgc n) zc :=
      hAdj.symm.trans hOrd
    have hAdjBranch :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simpa [zc] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have hOrdBranch :
        BHW.extendF (bvt_F OS lgc n) zc =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simp [BHW.os45PulledRealBranch, zc]
    rw [← hAdjBranch, ← hOrdBranch]
    exact (sub_eq_zero.mpr hEq).symm

/-- Selected Jost/Ruelle data imply the local OS45 Hdiff germ.

This composes the faithful selected-data Ruelle seed
`os45_flat_seed_of_selectedJostData` with the checked post-seed Hdiff tail
`os45_hdiff_of_flat_seed`.  The theorem bypasses the individual fixed
zero-height selector: the remaining real mathematical inputs are the selected
distributional Jost anchor data and the adjacent extended-tube overlap
connectedness. -/
theorem os45_hdiff_of_selectedJostData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      ∀ (j : Fin n) (hj : j.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  rcases hU_nonempty with ⟨u0, hu0⟩
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  obtain ⟨ys, hys_mem, hys_li⟩ :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  let Uruelle : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d n P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d n P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d n P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    have hconn := hOverlap i hi
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, P.τ_eq, BHW.permAct] using hconn
  have hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈
        BHW.ruelleOverlapDomain d n P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure (hU_sub hu))
  have hflat_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧
        IsPreconnected W ∧
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
        W ⊆
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W :=
    BHW.os45_flat_seed_of_selectedJostData
      (d := d) hd OS lgc (P := P) hOverlap hData hU_open hU_sub
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 hu0
  exact
    BHW.os45_hdiff_of_flat_seed
      (d := d) hd OS lgc (P := P) H U u0 hu0 hU_sub hflat_seed

/-- A single adjacent compact edge pairing gives pointwise equality of the
selected `extendF` branches on the whole adjacent ET/swap-ET overlap.

This is the local one-edge version of
`bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`: it keeps only the
adjacent edge used by the OS45 Figure-2-4 patch. -/
theorem bvt_F_extendF_adjacent_overlap_of_localEdgePairing
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed
                (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n)
    (hswapz :
      BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
        BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) =
      BHW.extendF (bvt_F OS lgc n) z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.extendF_perm_overlap_of_edgePairingEquality
      (d := d) n (bvt_F OS lgc n) hF_holo hF_lorentz τ
      (by simpa [τ] using hOverlap)
      Vedge hVedge_open hVedge_nonempty
      hVedge_ET
      (by intro x hx; simpa [τ] using hVedge_swapET x hx)
      (by
        intro φ hφ_compact hφ_tsupport
        simpa [τ] using hPairing φ hφ_compact hφ_tsupport)
      z hz
      (by simpa [τ] using hswapz)

/-- Local edge pairing supplies the common-edge compact-test boundary packet
used by the Ruelle splice. -/
theorem os45_ruelle_commonEdge_boundary_hint_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_sub : Usrc ⊆ P.V) :
    ∀ ρ : BHW.RuelleRealTestSpace d n,
      HasCompactSupport
        (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
      tsupport (ρ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ Usrc →
      (∫ x : Fin n → Fin (d + 1) → ℝ,
          BHW.extendF (bvt_F OS lgc n)
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (SCV.realToComplexProduct
                (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x))) * ρ x) =
        ∫ x : Fin n → Fin (d + 1) → ℝ,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (SCV.realToComplexProduct
                  (BHW.os45CommonEdgeRealCLE (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) x)))) * ρ x := by
  intro ρ _hρ_compact hρ_tsupport
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxU : x ∈ Usrc
  · have hxP : x ∈ P.V := hUsrc_sub hxU
    let z : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))
    have hz_overlap :
        z ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [z] using
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure hxP)
    have hz : z ∈ BHW.ExtendedTube d n := hz_overlap.1
    have hτz :
        BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n := by
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using
        hz_overlap.2
    have hpoint :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) =
          BHW.extendF (bvt_F OS lgc n) z := by
      have hlocal :=
        BHW.bvt_F_extendF_adjacent_overlap_of_localEdgePairing
          (d := d) OS lgc n i hi
          (by simpa [P.τ_eq] using hOverlap)
          Vedge hVedge_open hVedge_nonempty
          hVedge_ET
          (by intro y hy; simpa [P.τ_eq] using hVedge_swapET y hy)
          (by
            intro φ hφ_compact hφ_tsupport
            simpa [P.τ_eq] using hPairing φ hφ_compact hφ_tsupport)
          z hz
          (by simpa [P.τ_eq] using hτz)
      simpa [P.τ_eq] using hlocal
    change
      BHW.extendF (bvt_F OS lgc n) z * ρ x =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) * ρ x
    rw [hpoint]
  · have hρ_zero : ρ x = 0 := by
      exact image_eq_zero_of_notMem_tsupport
        (fun hx_ts => hxU (hρ_tsupport hx_ts))
    simp [hρ_zero]

/-- Local edge pairing plus adjacent overlap connectedness identifies the two
pulled real branches on any source window inside the Figure-2-4 patch.

This is the pointwise common-edge form of
`os45_ruelle_commonEdge_boundary_hint_of_localEdgePairing`: the local
real-edge distributional equality first gives equality of the two `extendF`
branches on the Ruelle overlap, and the checked OS45 common-edge coordinate
rewrite turns that into source common-edge equality. -/
theorem os45_sourceCommonEdge_eqOn_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_sub : Usrc ⊆ P.V) :
    ∀ u ∈ Usrc,
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  intro u hu
  let z : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  have hz_overlap :
      z ∈ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [z] using
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure (hUsrc_sub hu))
  have hz : z ∈ BHW.ExtendedTube d n := hz_overlap.1
  have hτz :
      BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n := by
    simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using
      hz_overlap.2
  have hbranch_eq :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) =
        BHW.extendF (bvt_F OS lgc n) z := by
    have hlocal :=
      BHW.bvt_F_extendF_adjacent_overlap_of_localEdgePairing
        (d := d) OS lgc n i hi
        (by simpa [P.τ_eq] using hOverlap)
        Vedge hVedge_open hVedge_nonempty
        hVedge_ET
        (by intro y hy; simpa [P.τ_eq] using hVedge_swapET y hy)
        (by
          intro φ hφ_compact hφ_tsupport
          simpa [P.τ_eq] using hPairing φ hφ_compact hφ_tsupport)
        z hz
        (by simpa [P.τ_eq] using hτz)
    simpa [P.τ_eq] using hlocal
  have hAdj :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simpa [z] using
      BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P) u
  have hOrd :
      BHW.extendF (bvt_F OS lgc n) z =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simp [BHW.os45PulledRealBranch, z]
  calc
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
        = BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) := hAdj.symm
    _ = BHW.extendF (bvt_F OS lgc n) z := hbranch_eq
    _ = BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) := hOrd

/-- Pointwise source common-edge equality gives the zero distributional
representation of the horizontal adjacent-minus-ordinary branch difference on
the same source window. -/
theorem os45_sourceCommonEdge_representsZero_of_eqOn
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {hd : 2 ≤ d}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) :
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
      (fun u : NPointDomain d n =>
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) -
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) U := by
  let Ghoriz : NPointDomain d n → ℂ := fun u =>
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) -
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
  change
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ) Ghoriz U
  have hpoint : ∀ u ∈ U, Ghoriz u = 0 := by
    intro u hu
    exact sub_eq_zero.mpr (hsource u hu)
  intro φ hφU
  calc
    (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ) φ
        = ∫ u : NPointDomain d n, (0 : ℂ) * φ u := by simp
    _ = ∫ u : NPointDomain d n, Ghoriz u * φ u := by
        exact
          BHW.integral_eq_of_tsupport_subset_of_pointwise_on
            (d := d) (n := n) U (fun _ => 0) Ghoriz φ hφU.2
            (by
              intro u hu
              exact (hpoint u hu).symm)

/-- Local edge pairing supplies the zero source common-edge representation on
any source window contained in the Figure-2-4 patch. -/
theorem os45_sourceCommonEdge_representsZero_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_sub : Usrc ⊆ P.V) :
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
      (fun u : NPointDomain d n =>
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) -
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) Usrc := by
  refine
    BHW.os45_sourceCommonEdge_representsZero_of_eqOn
      (d := d) OS lgc ?_
  exact
    BHW.os45_sourceCommonEdge_eqOn_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing hUsrc_sub

/-- Local adjacent edge pairing supplies the flat Figure-2-4 branch-difference
limit.

This is the OS-I `(4.14)` moving-source transfer with the common-edge equality
no longer assumed as a separate input: the local real-edge distributional
pairing and adjacent connected overlap first identify the two pulled real
branches on the compact source carrier, and the checked source-side moving
lemma turns that into the flat plus/minus branch difference. -/
theorem OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (hKsrc_sub : Ksrc ⊆ P.V)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
    Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φ x) -
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φ x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 0) := by
  have hsource :
      ∀ u ∈ Ksrc,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) :=
    BHW.os45_sourceCommonEdge_eqOn_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing hKsrc_sub
  exact
    BHW.OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceCommonEdge
      (d := d) OS lgc D
      hΩplus_open hΩminus_open hFplus_cont hFminus_cont
      hUsrc_open hUsrc_sub_K hKsrc η hηC h0_plus h0_minus
      hsource φ hφ_compact hφE hφU

/-- Local adjacent edge pairing gives the initial-sector equality seed with no
extra Ruelle-neighborhood bookkeeping.

The only analytic input here is the local real-edge pairing on `Vedge`; the
source common-edge equality is produced pointwise by
`os45_sourceCommonEdge_eqOn_of_localEdgePairing` and then fed directly into the
checked flat common-chart EOW bridge. -/
theorem os45_flat_seed_of_localEdgePairing_sourceCommonEdge
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub : Usrc ⊆ P.V)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ Usrc) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  have hsource :
      ∀ u ∈ Usrc,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) :=
    BHW.os45_sourceCommonEdge_eqOn_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing hUsrc_sub
  exact
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn
      (d := d) hd OS lgc (P := P) hUsrc_open hUsrc_sub hsource
      ys hys_mem hys_li u0 hu0

/-- Local adjacent edge pairing plus adjacent overlap connectedness supplies the
local initial-sector equality seed used by the Figure-2-4 flat common-chart
route. -/
theorem os45_flat_seed_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    {Usrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub : Usrc ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hUcx_sub : Ucx ⊆ BHW.ruelleOverlapDomain d n P.τ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hcommon_mem :
      ∀ u ∈ Usrc,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n)
    (hu0 : u0 ∈ Usrc) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  exact
    os45_initialSectorEqOn_open_of_ruelle_commonEdge_boundary
      (d := d) hd OS lgc (P := P) hUsrc_open hUsrc_sub
      (Ucx := Ucx) hUcx_sub hUcx_open hUcx_connected
      hcommon_mem
      (BHW.os45_ruelle_commonEdge_boundary_hint_of_localEdgePairing
        (d := d) hd OS lgc (P := P) hOverlap
        Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
        hPairing hUsrc_sub)
      ys hys_mem hys_li u0 hu0

/-- Local adjacent edge pairing implies the local OS45 Hdiff germ. -/
theorem os45_hdiff_of_localEdgePairing
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Vedge : Set (NPointDomain d n))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n)
    (hPairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  rcases hU_nonempty with ⟨u0, hu0⟩
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  obtain ⟨ys, hys_mem, hys_li⟩ :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  let Uruelle : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d n P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d n P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d n P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, BHW.permAct] using hOverlap
  have hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈
        BHW.ruelleOverlapDomain d n P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure (hU_sub hu))
  have hflat_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧
        IsPreconnected W ∧
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) u0))) ∈ W ∧
        W ⊆
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W :=
    BHW.os45_flat_seed_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing hU_open hU_sub
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 hu0
  exact
    BHW.os45_hdiff_of_flat_seed
      (d := d) hd OS lgc (P := P) H U u0 hu0 hU_sub hflat_seed

/-- A single compact Figure-2-4 Wick-pairing packet is enough to feed the
local-edge Hdiff theorem. -/
theorem os45_hdiff_of_compactWickPairingEq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (hCompact :
      BHW.OS45CompactFigure24WickPairingEq (d := d) n i hi OS lgc)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  refine
    BHW.os45_hdiff_of_localEdgePairing
      (d := d) hd OS lgc (P := P) H hOverlap
      (hCompact.realPatch 1)
      (hCompact.realPatch_open 1)
      (hCompact.realPatch_nonempty 1)
      ?hET ?hSwapET ?hPairing
      U hU_open hU_nonempty hU_sub
  · intro x hx
    simpa [BHW.permutedExtendedTubeSector] using
      hCompact.realPatch_left_sector 1 x hx
  · intro x hx
    simpa [BHW.permutedExtendedTubeSector, P.τ_eq, BHW.realEmbed,
      Equiv.Perm.mul_apply] using
      hCompact.realPatch_right_sector 1 x hx
  · intro φ hφ_compact hφ_tsupport
    simpa [P.τ_eq, BHW.realEmbed, Equiv.Perm.mul_apply] using
      (hCompact.compact_branch_eq 1 φ hφ_compact hφ_tsupport).symm

/-- A BHW/Jost pair carrier on the canonical Figure-2-4 source patch supplies
the compact Wick-pairing packet, hence the local OS45 Hdiff germ.

This is the direct production surface for the faithful Jost/Ruelle route: the
remaining nontrivial inputs are the pair carrier itself and connectedness of
the adjacent ET overlap. -/
theorem os45_hdiff_of_pairData_on_figure24SourcePatch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (Pair : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi))
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  exact
    BHW.os45_hdiff_of_compactWickPairingEq
      (d := d) hd OS lgc (P := P) H hOverlap
      (BHW.os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch
        (d := d) hd OS lgc n i hi Pair)
      U hU_open hU_nonempty hU_sub

/-- A BHW/Jost pair carrier on a real patch containing the canonical
Figure-2-4 source patch supplies the compact Wick-pairing packet, hence the
local OS45 Hdiff germ. -/
theorem os45_hdiff_of_pairData_canonical
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    {V : Set (NPointDomain d n)}
    (Pair : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  exact
    BHW.os45_hdiff_of_compactWickPairingEq
      (d := d) hd OS lgc (P := P) H hOverlap
      (BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical
        (d := d) hd OS lgc n i hi Pair hsource_subset)
      U hU_open hU_nonempty hU_sub

/-- Once the local `S'_n` branch data is already available, the local OS45
Hdiff germ does not need the global connectedness of `T'_n ∩ s_i T'_n`.

This is the honest local consumer: the remaining producer is the local EOW
seed that constructs `S`, rather than an individual selector endpoint or a
global overlap shortcut. -/
theorem os45_hdiff_of_sPrimeBranchData_local
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H)
    (U : Set (NPointDomain d n))
    (_hU_open : IsOpen U)
    (_hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  refine
    ⟨H.ΩJ, (fun _ => (0 : ℂ)), H.ΩJ_open, H.ΩJ_connected,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact H.ordinaryWick_mem u (hU_sub hu)
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      change
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ
      exact
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    exact H.extendedTube_subset_ΩJ hzc_overlap.1
  · exact differentiableOn_const (c := (0 : ℂ))
  · intro φ _hφ_compact _hφU
    simp
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      change
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ
      exact
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    have hzcΩ : zc ∈ H.ΩJ := H.extendedTube_subset_ΩJ hzc_overlap.1
    have hOrd :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n) zc :=
      S.eq_ordinary ⟨hzc_overlap.1, hzcΩ⟩
    have hAdj :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) :=
      S.eq_adjacent ⟨hzc_overlap.2, hzcΩ⟩
    have hEq :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.extendF (bvt_F OS lgc n) zc :=
      hAdj.symm.trans hOrd
    have hAdjBranch :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simpa [zc] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have hOrdBranch :
        BHW.extendF (bvt_F OS lgc n) zc =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simp [BHW.os45PulledRealBranch, zc]
    rw [← hAdjBranch, ← hOrdBranch]
    exact (sub_eq_zero.mpr hEq).symm

/-- Local `S'_n` branch data supplies the local OS45 Hdiff germ once its real
patch contains the canonical Figure-2-4 source patch and the adjacent ET
overlap is connected. -/
theorem os45_hdiff_of_sPrimeBranchData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ P.V)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  exact
    BHW.os45_hdiff_of_pairData_canonical
      (d := d) hd OS lgc (P := P) H hOverlap
      S.toPairData hsource_subset U hU_open hU_nonempty hU_sub

end BHW
