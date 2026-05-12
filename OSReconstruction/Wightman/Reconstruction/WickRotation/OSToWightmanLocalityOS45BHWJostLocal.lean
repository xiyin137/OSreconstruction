import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJost
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonEdge

/-!
# OS45 local BHW/Jost hull geometry

This file starts the non-source-descent local BHW/Jost carrier for the strict
OS II / OS I §4.5 route.  It contains only the concrete proper-complex
Lorentz saturation and path-component geometry used by the later local
Bargmann-Hall-Wightman continuation theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Proper-complex Lorentz saturation of the identity extended tube and the
selected adjacent permuted extended-tube sector.  This is the local OS I §4.5
BHW/Jost ambient; it is not global PET branch independence. -/
def os45BHWJostAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
      u ∈ BHW.ExtendedTube d n ∧ z = BHW.complexLorentzAction Λ u} ∪
    {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
      u ∈ BHW.permutedExtendedTubeSector d n τ ∧
        z = BHW.complexLorentzAction Λ u}

/-- The local BHW/Jost hull is the path component of the concrete ambient. -/
def os45BHWJostHull
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (zbase : Fin n → Fin (d + 1) → ℂ) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  pathComponentIn (BHW.os45BHWJostAmbient d n τ) zbase

/-- Configuration space for the pure local `S'_n` two-sector theorem. -/
abbrev SPrimeConfig (d n : ℕ) :=
  Fin n → Fin (d + 1) → ℂ

/-- Pure BHW two-sector ambient: the ordinary extended tube union one selected
permuted extended-tube sector.  This is a neutral BHW/SCV object, not an OS45
carrier and not a proper-complex Lorentz sweep. -/
def localSPrimeTwoSectorAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (BHW.SPrimeConfig d n) :=
  BHW.ExtendedTube d n ∪ BHW.permutedExtendedTubeSector d n τ

/-- Pure local `S'_n` hull: the path component of the neutral two-sector
ambient through the chosen base point. -/
def localSPrimeTwoSectorHull
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (zbase : BHW.SPrimeConfig d n) :
    Set (BHW.SPrimeConfig d n) :=
  pathComponentIn (BHW.localSPrimeTwoSectorAmbient d n τ) zbase

/-- Complex-Lorentz invariance of a branch on a specified domain. -/
def ComplexLorentzInvariantOn
    (d n : ℕ) (Ω : Set (BHW.SPrimeConfig d n))
    (F : BHW.SPrimeConfig d n → ℂ) : Prop :=
  ∀ (Λ : ComplexLorentzGroup d) (z : BHW.SPrimeConfig d n),
    z ∈ Ω →
    BHW.complexLorentzAction Λ z ∈ Ω →
    F (BHW.complexLorentzAction Λ z) = F z

/-- **Local two-sector Bargmann-Hall-Wightman continuation theorem.**

This is the paper-classical BHW/Hall-Wightman analytic-continuation step used
in OS I section 4.5: two holomorphic initial-sector branches on the ordinary
extended tube and one selected permuted extended-tube sector, together with
proper-complex Lorentz invariance and one local edge-of-the-wedge overlap
seed, determine a single holomorphic branch on the path component of the
two-sector `S'_n` hull.  The theorem is intentionally local to the path
component and does not assert a global envelope theorem.

The `ComplexLorentzGroup d` used here is the project's determinant-one proper
complex Lorentz group (`proper : val.det = 1`).  This properness and the
explicit `ComplexLorentzInvariantOn` hypotheses are essential: the analogous
arbitrary-holomorphic statement is false because the sector intersection can
have several connected components.

References:
* V. Bargmann, "On unitary ray representations of continuous groups",
  Annals of Mathematics 59 (1954), and the Bargmann-Hall-Wightman
  tube-domain continuation theorem usually cited as BHW.
* D. Hall and A. Wightman, "A theorem on invariant analytic functions with
  applications to relativistic quantum field theory", Mat. Fys. Medd. Danske
  Vid. Selsk. 31, no. 5 (1957).
* R. F. Streater and A. S. Wightman, *PCT, Spin and Statistics, and All That*,
  Princeton University Press, section III.1.

Status: paper-classical SCV/BHW analytic-continuation infrastructure not yet
formalized in Mathlib.  Authorized by Xi on 2026-05-11 after Gemini/Claude
audits rejected the non-Lorentz-invariant version and verified the corrected
proper-complex-Lorentz-invariant statement, including the local repo checks
`BHW.lorentz_perm_commute` and
`BHW.permutedExtendedTubeSector_complexLorentzAction_iff`. -/
axiom localSPrime_twoSectorBranch_of_EOW_BHW
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} (τ : Equiv.Perm (Fin n))
    (zbase zseed : BHW.SPrimeConfig d n)
    (hzbase : zbase ∈ BHW.localSPrimeTwoSectorAmbient d n τ)
    (hzseed :
      zseed ∈ BHW.localSPrimeTwoSectorHull d n τ zbase ∩
        BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n τ)
    (Ford Fadj : BHW.SPrimeConfig d n → ℂ)
    (hFord_holo : DifferentiableOn ℂ Ford (BHW.ExtendedTube d n))
    (hFadj_holo :
      DifferentiableOn ℂ Fadj (BHW.permutedExtendedTubeSector d n τ))
    (hFord_cinv :
      BHW.ComplexLorentzInvariantOn d n (BHW.ExtendedTube d n) Ford)
    (hFadj_cinv :
      BHW.ComplexLorentzInvariantOn d n
        (BHW.permutedExtendedTubeSector d n τ) Fadj)
    (hEOW_seed :
      ∃ W : Set (BHW.SPrimeConfig d n),
        IsOpen W ∧ IsPreconnected W ∧
        zseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n τ zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n τ ∧
        Set.EqOn Ford Fadj W) :
    ∃ B : BHW.SPrimeConfig d n → ℂ,
      DifferentiableOn ℂ B (BHW.localSPrimeTwoSectorHull d n τ zbase) ∧
      Set.EqOn B Ford
        (BHW.ExtendedTube d n ∩
          BHW.localSPrimeTwoSectorHull d n τ zbase) ∧
      Set.EqOn B Fadj
        (BHW.permutedExtendedTubeSector d n τ ∩
          BHW.localSPrimeTwoSectorHull d n τ zbase)

/-- The OS/BHW ordinary initial branch satisfies the neutral
`ComplexLorentzInvariantOn` predicate required by the local `S'_n` theorem. -/
theorem complexLorentzInvariantOn_extendF_bvt_F_extendedTube
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    BHW.ComplexLorentzInvariantOn d n (BHW.ExtendedTube d n)
      (BHW.extendF (bvt_F OS lgc n)) := by
  intro Λ z hz _hΛz
  have hF_cinv_BHW :
      ∀ (Γ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Γ w ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Γ w) =
          bvt_F OS lgc n w := by
    intro Γ w hw hΓw
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Γ w
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hw)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΓw)
  exact
    BHW.extendF_complexLorentzInvariant_of_cinv
      (d := d) n (bvt_F OS lgc n) hF_cinv_BHW Λ z hz

/-- The adjacent permuted initial branch satisfies the neutral
`ComplexLorentzInvariantOn` predicate required by the local `S'_n` theorem. -/
theorem complexLorentzInvariantOn_extendF_bvt_F_permAct_permutedSector
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    BHW.ComplexLorentzInvariantOn d n
      (BHW.permutedExtendedTubeSector d n τ)
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z)) := by
  intro Λ z hz _hΛz
  have hF_cinv_BHW :
      ∀ (Γ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Γ w ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Γ w) =
          bvt_F OS lgc n w := by
    intro Γ w hw hΓw
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Γ w
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hw)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΓw)
  have hpz : BHW.permAct (d := d) τ z ∈ BHW.ExtendedTube d n := by
    simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using hz
  have hcomm :
      BHW.permAct (d := d) τ (BHW.complexLorentzAction Λ z) =
        BHW.complexLorentzAction Λ (BHW.permAct (d := d) τ z) := by
    simpa [BHW.permAct] using
      (BHW.lorentz_perm_commute (d := d) (n := n) Λ z τ).symm
  calc
    BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) τ (BHW.complexLorentzAction Λ z))
        = BHW.extendF (bvt_F OS lgc n)
            (BHW.complexLorentzAction Λ (BHW.permAct (d := d) τ z)) := by
          rw [hcomm]
    _ = BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z) :=
          BHW.extendF_complexLorentzInvariant_of_cinv
            (d := d) n (bvt_F OS lgc n) hF_cinv_BHW Λ
            (BHW.permAct (d := d) τ z) hpz

/-- Flattened common-chart dimension for the OS45 local EOW seed. -/
abbrev os45FlatCommonChartDim (d n : ℕ) : ℕ :=
  n * (d + 1)

/-- Complex coordinate space used by the flattened OS45 common-chart EOW call. -/
abbrev OS45FlatCommonChartSpace (d n : ℕ) :=
  SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d n)

/-- Real coordinate space underlying the flattened OS45 common-chart EOW call. -/
abbrev OS45FlatCommonChartReal (d n : ℕ) :=
  Fin (BHW.os45FlatCommonChartDim d n) → ℝ

/-- The branch-domain side of the flattened common chart. -/
def os45FlatCommonChartOmega
    (d n : ℕ) [NeZero d] (σ : Equiv.Perm (Fin n)) :
    Set (BHW.OS45FlatCommonChartSpace d n) :=
  {w |
    BHW.unflattenCfg n d w ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n) σ}

/-- The branch function pulled to flattened common-chart coordinates. -/
def os45FlatCommonChartBranch
    (d n : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n)) :
    BHW.OS45FlatCommonChartSpace d n → ℂ :=
  fun w =>
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc σ
      (BHW.unflattenCfg n d w)

/-- The Figure-2-4 real edge in flattened common-chart coordinates. -/
def os45FlatCommonChartEdgeSet
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n)) :
    Set (BHW.OS45FlatCommonChartReal d n) :=
  BHW.flattenCfgReal n d ''
    (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm '' P.V)

/-- The flattened product forward cone used for the OS45 common-chart EOW call. -/
def os45FlatCommonChartCone (d n : ℕ) :
    Set (BHW.OS45FlatCommonChartReal d n) :=
  BHW.FlatProductForwardConeReal d n

/-- The Figure-2-4 seed point in flattened common-chart real coordinates. -/
def os45FlatCommonChartSeed
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n)) :
    BHW.OS45FlatCommonChartReal d n :=
  BHW.flattenCfgReal n d
    (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm P.xseed)

/-- The flattened common-chart branch-domain side is open. -/
theorem isOpen_os45FlatCommonChartOmega
    (d n : ℕ) [NeZero d] (σ : Equiv.Perm (Fin n)) :
    IsOpen (BHW.os45FlatCommonChartOmega d n σ) := by
  exact
    (BHW.isOpen_os45PulledRealBranchDomain
      (d := d) (n := n) σ).preimage
      ((differentiable_unflattenCfg_local n d).continuous)

/-- The flattened common-chart branch is holomorphic on its natural side. -/
theorem differentiableOn_os45FlatCommonChartBranch
    (d n : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (BHW.os45FlatCommonChartBranch d n OS lgc σ)
      (BHW.os45FlatCommonChartOmega d n σ) := by
  exact
    (BHW.os45PulledRealBranch_holomorphicOn
      (d := d) (n := n) OS lgc σ).comp
      (differentiable_unflattenCfg_local n d).differentiableOn
      (by intro w hw; exact hw)

/-- The linear coordinate equivalence from source variables to flattened
common-edge coordinates. -/
def os45CommonEdgeFlatCLE
    (d n : ℕ) (ρperm : Equiv.Perm (Fin n)) :
    NPointDomain d n ≃L[ℝ] BHW.OS45FlatCommonChartReal d n :=
  (BHW.os45CommonEdgeRealCLE (d := d) (n := n) ρperm).trans
    (flattenCLEquivReal n (d + 1))

/-- Absolute Jacobian of the OS45 source-to-flat common-edge map.  The common
edge map halves the time coordinate of each source point; permutations and
flattening have absolute determinant `1`. -/
noncomputable def os45CommonEdgeFlatJacobianAbs (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

theorem os45CommonEdgeFlatJacobianAbs_pos (n : ℕ) :
    0 < BHW.os45CommonEdgeFlatJacobianAbs n := by
  dsimp [BHW.os45CommonEdgeFlatJacobianAbs]
  positivity

/-- Unflattening the complexification of a flattened real configuration
recovers its standard complex real embedding. -/
@[simp] theorem unflattenCfg_ofReal_flattenCfgReal
    (n d : ℕ) (x : Fin n → Fin (d + 1) → ℝ) :
    BHW.unflattenCfg n d
      (fun a => (BHW.flattenCfgReal n d x a : ℂ)) =
      BHW.realEmbed x := by
  funext k μ
  simp [BHW.unflattenCfg, BHW.flattenCfgReal, BHW.realEmbed]

/-- The flattened Figure-2-4 real edge is open. -/
theorem isOpen_os45FlatCommonChartEdgeSet
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n)) :
    IsOpen (BHW.os45FlatCommonChartEdgeSet d n P ρperm) := by
  have hE0 :
      IsOpen
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm '' P.V) :=
    BHW.isOpen_image_os45CommonEdgeRealPoint
      (d := d) (n := n) ρperm P.V_open
  have hflat :
      BHW.flattenCfgReal n d ''
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm '' P.V) =
        (flattenCLEquivReal n (d + 1)) ''
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm '' P.V) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by
        ext a
        simp [BHW.flattenCfgReal, flattenCLEquivReal_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by
        ext a
        simp [BHW.flattenCfgReal, flattenCLEquivReal_apply]⟩
  rw [BHW.os45FlatCommonChartEdgeSet, hflat]
  exact (flattenCLEquivReal n (d + 1)).toHomeomorph.isOpenMap _ hE0

/-- The stored Figure-2-4 seed point lies in the flattened real edge. -/
theorem os45FlatCommonChartSeed_mem_edgeSet
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n)) :
    BHW.os45FlatCommonChartSeed d n P ρperm ∈
      BHW.os45FlatCommonChartEdgeSet d n P ρperm := by
  exact
    ⟨BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm P.xseed,
      ⟨P.xseed, P.xseed_mem, rfl⟩, rfl⟩

/-- Membership in the flattened Figure-2-4 edge, restricted to the linear
source chart image, is exactly membership in the original source slice. -/
theorem os45CommonEdgeFlatCLE_mem_edgeSet_iff
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    BHW.os45CommonEdgeFlatCLE d n ρperm x ∈
        BHW.os45FlatCommonChartEdgeSet d n P ρperm ↔
      x ∈ P.V := by
  constructor
  · intro hx
    rcases hx with ⟨y, ⟨z, hzV, rfl⟩, hyx⟩
    have hflat_z :
        BHW.flattenCfgReal n d
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm z) =
          (flattenCLEquivReal n (d + 1))
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm z) := by
      ext a
      simp [BHW.flattenCfgReal, flattenCLEquivReal_apply]
    have hflat_eq :
        (flattenCLEquivReal n (d + 1))
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm z) =
          (flattenCLEquivReal n (d + 1))
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x) := by
      rw [← hflat_z]
      change
        BHW.flattenCfgReal n d
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm z) =
          BHW.os45CommonEdgeFlatCLE d n ρperm x
      exact hyx
    have hcommon :
        BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm z =
          BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x :=
      (flattenCLEquivReal n (d + 1)).injective hflat_eq
    have hz_eq_x : z = x :=
      (BHW.os45CommonEdgeRealCLE (d := d) (n := n) ρperm).injective
        (by simpa using hcommon)
    simpa [hz_eq_x] using hzV
  · intro hxV
    have hflat_x :
        BHW.flattenCfgReal n d
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x) =
          (flattenCLEquivReal n (d + 1))
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x) := by
      ext a
      simp [BHW.flattenCfgReal, flattenCLEquivReal_apply]
    exact
      ⟨BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x,
        ⟨x, hxV, rfl⟩, by
          rw [hflat_x]
          rfl⟩

/-- The flattened common-chart dimension is positive for an adjacent slot. -/
theorem os45FlatCommonChartDim_pos_of_adjacent
    (d n : ℕ) {i : Fin n} (hi : i.val + 1 < n) :
    0 < BHW.os45FlatCommonChartDim d n := by
  dsimp [BHW.os45FlatCommonChartDim]
  have hn : 0 < n := by omega
  exact Nat.mul_pos hn (Nat.succ_pos d)

/-- Cone hypotheses for the flattened common-chart EOW call. -/
theorem os45FlatCommonChartCone_eowReady
    (d n : ℕ) [NeZero d] [NeZero n] :
    IsOpen (BHW.os45FlatCommonChartCone d n) ∧
    Convex ℝ (BHW.os45FlatCommonChartCone d n) ∧
    ((0 : BHW.OS45FlatCommonChartReal d n) ∉
      BHW.os45FlatCommonChartCone d n) ∧
    (∀ (t : ℝ) (y : BHW.OS45FlatCommonChartReal d n),
      0 < t → y ∈ BHW.os45FlatCommonChartCone d n →
        t • y ∈ BHW.os45FlatCommonChartCone d n) ∧
    (BHW.os45FlatCommonChartCone d n).Nonempty := by
  simpa [BHW.os45FlatCommonChartCone, BHW.OS45FlatCommonChartReal,
    BHW.os45FlatCommonChartDim] using
    BHW.flatProductForwardConeReal_eowReady (n := n) (d := d)

/-- A compact real edge has a uniform positive side radius into two open
complex side domains. -/
theorem exists_uniform_side_radius_of_compact_real_edge
    {m : ℕ}
    {Ωplus Ωminus : Set (SCV.ComplexChartSpace m)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    {K Kη : Set (Fin m → ℝ)}
    (hK : IsCompact K) (hKη : IsCompact Kη)
    (hplus0 : ∀ x ∈ K, (fun a => (x a : ℂ)) ∈ Ωplus)
    (hminus0 : ∀ x ∈ K, (fun a => (x a : ℂ)) ∈ Ωminus) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
        (fun a => (x a : ℂ) +
          (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
        (fun a => (x a : ℂ) -
          (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus := by
  let R := Fin m → ℝ
  let plusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace m :=
    fun p a => (p.1.1 a : ℂ) + (p.2 : ℂ) * (p.1.2 a : ℂ) * Complex.I
  let minusMap : ((R × R) × ℝ) → SCV.ComplexChartSpace m :=
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
    · simpa [plusMap] using hplus0 x hx
    · simpa [minusMap] using hminus0 x hx
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
  exact hr_sub hmem

/-- The Figure-2-4 flattened common edge satisfies the local wedge hypothesis
required by the distributional EOW theorem. -/
theorem os45_BHWJost_flatCommonChart_localWedge_of_figure24
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K →
      K ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) →
      ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
        Kη ⊆ BHW.os45FlatCommonChartCone d n →
        ∃ r : ℝ, 0 < r ∧
          ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
            (fun a => (x a : ℂ) +
              (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                BHW.os45FlatCommonChartOmega d n
                  (1 : Equiv.Perm (Fin n)) ∧
            (fun a => (x a : ℂ) -
              (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                BHW.os45FlatCommonChartOmega d n
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
  intro K hK hK_sub Kη hKη _hKη_sub
  have hplus0 :
      ∀ x ∈ K, (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hK_sub hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨u, hu, rfl⟩
    change BHW.unflattenCfg n d
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))
    rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
    exact P.V_pulled_id u hu
  have hminus0 :
      ∀ x ∈ K, (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    intro x hx
    rcases hK_sub hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨u, hu, rfl⟩
    have hτ : P.τ.symm * (1 : Equiv.Perm (Fin n)) = P.τ := by
      simp [P.τ_eq]
    rw [hτ]
    change BHW.unflattenCfg n d
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n) P.τ
    rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
    exact P.V_pulled_tau u hu
  exact
    BHW.exists_uniform_side_radius_of_compact_real_edge
      (m := BHW.os45FlatCommonChartDim d n)
      (Ωplus := BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (Ωminus := BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (BHW.isOpen_os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.isOpen_os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hK hKη hplus0 hminus0

/-- Smooth compact-support cutoff adapted to the Figure-2-4 source patch. -/
structure OS45Figure24SourceCutoffData
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) where
  χ : NPointDomain d n → ℂ
  χ_temperate : Function.HasTemperateGrowth χ
  χ_eq_one_on_V : ∀ x ∈ P.V, χ x = 1
  tsupport_subset_Ufig : tsupport χ ⊆ P.Ufig

/-- Existence of the smooth compact-support cutoff adapted to the Figure-2-4
source patch. -/
theorem exists_os45Figure24SourceCutoffData
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    Nonempty (BHW.OS45Figure24SourceCutoffData P) := by
  classical
  obtain ⟨Ucut, hUcut_open, hclosureV_sub_Ucut, hclosureUcut_sub_Ufig,
      hclosureUcut_compact⟩ :=
    exists_open_between_and_isCompact_closure
      P.closureV_compact P.Ufig_open P.closureV_sub_Ufig
  have hclosureV_sub_interior : closure P.V ⊆ interior Ucut :=
    by simpa [hUcut_open.interior_eq] using hclosureV_sub_Ucut
  obtain ⟨χR, hχR_one_nhds, hχR_zero_off, _hχR_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (modelWithCornersSelf ℝ (NPointDomain d n))
      (n := (⊤ : ℕ∞))
      (s := closure P.V) (t := Ucut)
      isClosed_closure hclosureV_sub_interior
  let χ : NPointDomain d n → ℂ := fun x => (χR x : ℂ)
  have hχ_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ := by
    dsimp [χ]
    exact Complex.ofRealCLM.contDiff.comp χR.contMDiff.contDiff
  have hsupport_subset_Ucut : Function.support χ ⊆ Ucut := by
    intro x hx
    by_contra hxU
    have hχ_zero : χ x = 0 := by
      dsimp [χ]
      simp [hχR_zero_off x hxU]
    exact hx hχ_zero
  have hχ_compact : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact hclosureUcut_compact
      (hsupport_subset_Ucut.trans subset_closure)
  have hχ_temperate : Function.HasTemperateGrowth χ :=
    hχ_compact.hasTemperateGrowth hχ_contDiff
  have hχ_one_on_V : ∀ x ∈ P.V, χ x = 1 := by
    intro x hx
    have hχR_one : χR x = 1 :=
      hχR_one_nhds.self_of_nhdsSet x (subset_closure hx)
    simp [χ, hχR_one]
  have htsupport_subset_Ufig : tsupport χ ⊆ P.Ufig := by
    have htsupport_subset_closureUcut : tsupport χ ⊆ closure Ucut := by
      simpa [tsupport] using closure_mono hsupport_subset_Ucut
    exact htsupport_subset_closureUcut.trans hclosureUcut_sub_Ufig
  exact
    ⟨{ χ := χ
       χ_temperate := hχ_temperate
       χ_eq_one_on_V := hχ_one_on_V
       tsupport_subset_Ufig := htsupport_subset_Ufig }⟩

/-- Pull a flattened common-chart Schwartz test to the source variables and
multiply by the Figure-2-4 cutoff. -/
noncomputable def OS45Figure24SourceCutoffData.toSchwartzNPointCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n)) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      SchwartzNPoint d n :=
  (SchwartzMap.smulLeftCLM ℂ D.χ).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (BHW.os45CommonEdgeFlatCLE d n ρperm))

/-- The cutoff-pulled common-chart tests lie in the zero-diagonal OS test
space because their support is contained in the Figure-2-4 Jost neighborhood. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_mem_zeroDiagonal
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ) :
    VanishesToInfiniteOrderOnCoincidence
      (D.toSchwartzNPointCLM ρperm φ) := by
  apply BHW.zeroDiagonal_of_tsupport_subset_jostOverlap
    (V := P.Ufig) P.Ufig_jost
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d n ρperm)) φ)
  exact
    (by
      simpa [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM] using
        hsupport.trans (Set.inter_subset_right.trans D.tsupport_subset_Ufig))

/-- The cutoff-pulled common-chart tests as a continuous linear map into the
zero-diagonal OS test space. -/
noncomputable def OS45Figure24SourceCutoffData.toZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n)) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d n :=
  (D.toSchwartzNPointCLM ρperm).codRestrict
    (zeroDiagonalSubmodule d n)
    (D.toSchwartzNPointCLM_mem_zeroDiagonal ρperm)

/-- Shift a flat common-chart test before pulling it back to source variables
and multiplying by the Figure-2-4 cutoff.  This is the source-test family used
for the two one-sided OS I section 4.5 distributional boundary values. -/
noncomputable def OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      SchwartzNPoint d n :=
  (D.toSchwartzNPointCLM ρperm).comp (SCV.translateSchwartzCLM a)

/-- Shifted cutoff-pulled common-chart tests are supported inside the
Figure-2-4 Jost neighborhood controlled by the fixed source cutoff. -/
theorem OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_tsupport_subset_Ufig
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ) :
    tsupport (D.toShiftedSchwartzNPointCLM ρperm a φ :
      NPointDomain d n → ℂ) ⊆ P.Ufig := by
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d n ρperm))
        (SCV.translateSchwartzCLM a φ))
  exact
    (by
      simpa [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
        BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
        ContinuousLinearMap.comp_apply] using
        hsupport.trans (Set.inter_subset_right.trans D.tsupport_subset_Ufig))

/-- If the shifted flat test is supported on the flattened common edge, then
the shifted cutoff-pulled source test is supported in the original source
slice.  This is the source-side support conversion used in the OS I `4.12` /
`4.14` side-boundary rewrite. -/
theorem OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_tsupport_subset_V
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (SCV.translateSchwartz a φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm) :
    tsupport (D.toShiftedSchwartzNPointCLM ρperm a φ :
      NPointDomain d n → ℂ) ⊆ P.V := by
  intro x hx
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
    SCV.translateSchwartzCLM a φ
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ)
  have hx_smul :
      x ∈ tsupport
        (SchwartzMap.smulLeftCLM ℂ D.χ
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ) :
          NPointDomain d n → ℂ) := by
    simpa [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
      BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
      ContinuousLinearMap.comp_apply, e, ψ] using hx
  have hx_comp :
      x ∈ tsupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ) :
          NPointDomain d n → ℂ) :=
    (hsupport hx_smul).1
  have hcomp_support :
      tsupport ((ψ : BHW.OS45FlatCommonChartReal d n → ℂ) ∘
          fun y : NPointDomain d n => e y) ⊆
        e ⁻¹' tsupport (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) := by
    exact tsupport_comp_subset_preimage
      (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) e.continuous
  have hx_comp' :
      x ∈ tsupport ((ψ : BHW.OS45FlatCommonChartReal d n → ℂ) ∘
          fun y : NPointDomain d n => e y) := by
    simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hx_comp
  have hx_flat :
      e x ∈ tsupport
        (SCV.translateSchwartz a φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) := by
    simpa [ψ, SCV.translateSchwartzCLM_apply] using
      hcomp_support hx_comp'
  exact
    (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P ρperm x).mp
      (hφE hx_flat)

/-- Topological-support transport for real Schwartz translations in flattened
coordinates. -/
theorem tsupport_translateSchwartz_subset_preimage
    {m : ℕ} (a : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport (SCV.translateSchwartz a φ : (Fin m → ℝ) → ℂ) ⊆
      (fun x : Fin m → ℝ => x + a) ⁻¹'
        tsupport (φ : (Fin m → ℝ) → ℂ) := by
  have hsub :
      tsupport ((φ : (Fin m → ℝ) → ℂ) ∘
          fun x : Fin m → ℝ => x + a) ⊆
        (fun x : Fin m → ℝ => x + a) ⁻¹'
          tsupport (φ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage
      (φ : (Fin m → ℝ) → ℂ) (continuous_id.add continuous_const)
  intro x hx
  exact hsub (by simpa [SCV.translateSchwartz_apply] using hx)

/-- Compactly supported flat common-chart tests remain supported on the
Figure-2-4 common edge after sufficiently small positive and negative side
translations, uniformly over a compact set of side directions. -/
theorem os45FlatCommonChart_sideSupport_radius
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (_hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε < r →
      ∀ η ∈ Kη,
        tsupport
          (SCV.translateSchwartz ((ε : ℝ) • η) φ :
            BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) ∧
        tsupport
          (SCV.translateSchwartz ((-ε : ℝ) • η) φ :
            BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) := by
  let R := BHW.OS45FlatCommonChartReal d n
  let S : Set R := tsupport (φ : R → ℂ)
  let E : Set R :=
    BHW.os45FlatCommonChartEdgeSet d n P (1 : Equiv.Perm (Fin n))
  let zeroEdge : Set ((R × R) × ℝ) := (S ×ˢ Kη) ×ˢ ({0} : Set ℝ)
  let sideWindow : Set ((R × R) × ℝ) :=
    {p | p.1.1 - p.2 • p.1.2 ∈ E ∧ p.1.1 + p.2 • p.1.2 ∈ E}
  have hE_open : IsOpen E := by
    simpa [E] using
      BHW.isOpen_os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n))
  have hminus_cont :
      Continuous (fun p : (R × R) × ℝ => p.1.1 - p.2 • p.1.2) := by
    fun_prop
  have hplus_cont :
      Continuous (fun p : (R × R) × ℝ => p.1.1 + p.2 • p.1.2) := by
    fun_prop
  have hside_open : IsOpen sideWindow := by
    exact (hE_open.preimage hminus_cont).inter
      (hE_open.preimage hplus_cont)
  have hS_compact : IsCompact S := by
    simpa [S] using hφ_compact.isCompact
  have hzero_compact : IsCompact zeroEdge :=
    (hS_compact.prod hKη).prod isCompact_singleton
  have hzero_sub : zeroEdge ⊆ sideWindow := by
    rintro ⟨⟨x, η⟩, ε⟩ ⟨⟨hxS, _hη⟩, hε0⟩
    have hε : ε = 0 := by simpa using hε0
    subst ε
    constructor <;> simpa [sideWindow, E] using hφE hxS
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hzero_compact.exists_thickening_subset_open hside_open hzero_sub
  refine ⟨r, hr_pos, ?_⟩
  intro ε hε_pos hε_lt η hη
  have hside :
      ∀ x ∈ S, x - ε • η ∈ E ∧ x + ε • η ∈ E := by
    intro x hxS
    have hmem : (((x, η), ε) : (R × R) × ℝ) ∈
        Metric.thickening r zeroEdge := by
      rw [Metric.mem_thickening_iff]
      refine ⟨((x, η), (0 : ℝ)), ?_, ?_⟩
      · exact ⟨⟨hxS, hη⟩, by simp⟩
      · simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hε_pos.le] using
          ⟨hr_pos, hε_lt⟩
    exact hr_sub hmem
  constructor
  · intro y hy
    have hyS :
        y + ε • η ∈ S :=
      BHW.tsupport_translateSchwartz_subset_preimage
        ((ε : ℝ) • η) φ hy
    have hEminus : y + ε • η - ε • η ∈ E :=
      (hside (y + ε • η) hyS).1
    have hcancel : y + ε • η - ε • η = y := by
      simp
    simpa [E, hcancel] using hEminus
  · intro y hy
    have hyS :
        y + (-ε : ℝ) • η ∈ S :=
      BHW.tsupport_translateSchwartz_subset_preimage
        ((-ε : ℝ) • η) φ hy
    have hEplus : y + (-ε : ℝ) • η + ε • η ∈ E :=
      (hside (y + (-ε : ℝ) • η) hyS).2
    have hcancel : y + (-ε : ℝ) • η + ε • η = y := by
      rw [add_assoc, ← add_smul]
      simp
    simpa [E, hcancel] using hEplus

/-- Shifted cutoff-pulled common-chart tests still lie in the zero-diagonal OS
test space; the fixed source cutoff keeps their support inside the Figure-2-4
Jost neighborhood. -/
theorem OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_mem_zeroDiagonal
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ) :
    VanishesToInfiniteOrderOnCoincidence
      (D.toShiftedSchwartzNPointCLM ρperm a φ) := by
  exact
    BHW.zeroDiagonal_of_tsupport_subset_jostOverlap
      (V := P.Ufig) P.Ufig_jost
      (D.toShiftedSchwartzNPointCLM ρperm a φ)
      (D.toShiftedSchwartzNPointCLM_tsupport_subset_Ufig ρperm a φ)

/-- The shifted cutoff-pulled common-chart tests as a continuous linear map
into the zero-diagonal OS test space. -/
noncomputable def OS45Figure24SourceCutoffData.toShiftedZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d n :=
  (D.toShiftedSchwartzNPointCLM ρperm a).codRestrict
    (zeroDiagonalSubmodule d n)
    (D.toShiftedSchwartzNPointCLM_mem_zeroDiagonal ρperm a)

/-- The signed one-sided source-test family used by the OS45 distributional
boundary-value comparison. -/
noncomputable def OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d n :=
  D.toShiftedZeroDiagonalCLM ρperm ((sgn * ε) • η)

/-- Compactly supported side-shifted flat tests converge to the unshifted
pulled source test in the ambient Schwartz space. -/
theorem OS45Figure24SourceCutoffData.toSideSchwartzNPointCLM_tendsto_zero
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ)) :
    Tendsto
      (fun ε : ℝ =>
        D.toShiftedSchwartzNPointCLM ρperm ((sgn * ε) • η) φ)
      (𝓝 (0 : ℝ))
      (𝓝 (D.toSchwartzNPointCLM ρperm φ)) := by
  have hshift :
      Tendsto (fun ε : ℝ => (sgn * ε) • η)
        (𝓝 (0 : ℝ)) (𝓝 (0 : BHW.OS45FlatCommonChartReal d n)) := by
    have hcont : Continuous (fun ε : ℝ => (sgn * ε) • η) := by
      fun_prop
    simpa using hcont.tendsto (0 : ℝ)
  have htrans :
      Tendsto
        (fun ε : ℝ =>
          SCV.translateSchwartz ((sgn * ε) • η) φ)
        (𝓝 (0 : ℝ))
        (𝓝 (SCV.translateSchwartz
          (0 : BHW.OS45FlatCommonChartReal d n) φ)) :=
    (SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport
      φ hφ_compact (0 : BHW.OS45FlatCommonChartReal d n)).comp hshift
  have hmap :
      Tendsto
        (fun ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ =>
          D.toSchwartzNPointCLM ρperm ψ)
        (𝓝 (SCV.translateSchwartz
          (0 : BHW.OS45FlatCommonChartReal d n) φ))
        (𝓝 (D.toSchwartzNPointCLM ρperm
          (SCV.translateSchwartz
            (0 : BHW.OS45FlatCommonChartReal d n) φ))) :=
    (D.toSchwartzNPointCLM ρperm).continuous.tendsto
      (SCV.translateSchwartz
        (0 : BHW.OS45FlatCommonChartReal d n) φ)
  simpa [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply,
    SCV.translateSchwartz] using hmap.comp htrans

/-- Compactly supported side-shifted flat tests converge to the unshifted
zero-diagonal source test. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tendsto_zero
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ)) :
    Tendsto
      (fun ε : ℝ => D.toSideZeroDiagonalCLM ρperm sgn ε η φ)
      (𝓝 (0 : ℝ))
      (𝓝 (D.toZeroDiagonalCLM ρperm φ)) := by
  unfold ZeroDiagonalSchwartz
  refine tendsto_subtype_rng.2 ?_
  simpa [BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM,
    BHW.OS45Figure24SourceCutoffData.toShiftedZeroDiagonalCLM,
    BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM,
    ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply,
    SCV.translateSchwartz] using
    D.toSideSchwartzNPointCLM_tendsto_zero ρperm sgn η φ hφ_compact

/-- The shifted zero-diagonal source-test family is continuous in the side
height and direction parameters for compactly supported flat tests. -/
theorem OS45Figure24SourceCutoffData.continuous_toSideZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ)) :
    Continuous
      (fun p : ℝ × BHW.OS45FlatCommonChartReal d n =>
        D.toSideZeroDiagonalCLM ρperm sgn p.1 p.2 φ) := by
  unfold ZeroDiagonalSchwartz
  rw [continuous_iff_continuousAt]
  intro p0
  rw [ContinuousAt]
  refine tendsto_subtype_rng.2 ?_
  have hshift :
      Tendsto
        (fun p : ℝ × BHW.OS45FlatCommonChartReal d n =>
          (sgn * p.1) • p.2)
        (𝓝 p0)
        (𝓝 ((sgn * p0.1) • p0.2)) := by
    have hcont :
        Continuous
          (fun p : ℝ × BHW.OS45FlatCommonChartReal d n =>
            (sgn * p.1) • p.2) := by
      fun_prop
    exact hcont.tendsto p0
  have htrans :
      Tendsto
        (fun p : ℝ × BHW.OS45FlatCommonChartReal d n =>
          SCV.translateSchwartz ((sgn * p.1) • p.2) φ)
        (𝓝 p0)
        (𝓝 (SCV.translateSchwartz ((sgn * p0.1) • p0.2) φ)) :=
    (SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport
      φ hφ_compact ((sgn * p0.1) • p0.2)).comp hshift
  have hmap :
      Tendsto
        (fun ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ =>
          D.toSchwartzNPointCLM ρperm ψ)
        (𝓝 (SCV.translateSchwartz ((sgn * p0.1) • p0.2) φ))
        (𝓝 (D.toSchwartzNPointCLM ρperm
          (SCV.translateSchwartz ((sgn * p0.1) • p0.2) φ))) :=
    (D.toSchwartzNPointCLM ρperm).continuous.tendsto
      (SCV.translateSchwartz ((sgn * p0.1) • p0.2) φ)
  simpa [BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM,
    BHW.OS45Figure24SourceCutoffData.toShiftedZeroDiagonalCLM,
    BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using
    hmap.comp htrans

/-- After applying any continuous zero-diagonal functional, the side-test
family converges uniformly over compact direction sets as the side height
tends to zero from the positive side. -/
theorem OS45Figure24SourceCutoffData.apply_toSideZeroDiagonalCLM_tendstoUniformlyOn_zero
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (L : ZeroDiagonalSchwartz d n →L[ℂ] ℂ)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ)) :
    TendstoUniformlyOn
      (fun ε η => L (D.toSideZeroDiagonalCLM ρperm sgn ε η φ))
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        L (D.toZeroDiagonalCLM ρperm φ))
      (𝓝[Set.Ioi 0] (0 : ℝ))
      Kη := by
  let U : Set ℝ := Metric.closedBall (0 : ℝ) 1
  let F : ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
    fun ε η => L (D.toSideZeroDiagonalCLM ρperm sgn ε η φ)
  have hcont_pair :
      Continuous
        (fun p : ℝ × BHW.OS45FlatCommonChartReal d n =>
          F p.1 p.2) := by
    simpa [F] using
      L.continuous.comp
        (D.continuous_toSideZeroDiagonalCLM ρperm sgn φ hφ_compact)
  have hcompact : IsCompact (U ×ˢ Kη) := by
    exact (isCompact_closedBall (x := (0 : ℝ)) (r := 1)).prod hKη
  have hunif : UniformContinuousOn (Function.uncurry F) (U ×ˢ Kη) :=
    hcompact.uniformContinuousOn_of_continuous hcont_pair.continuousOn
  have h0U : (0 : ℝ) ∈ U := by
    simp [U]
  have hTU :
      TendstoUniformlyOn F (F (0 : ℝ)) (𝓝[U] (0 : ℝ)) Kη :=
    hunif.tendstoUniformlyOn (x := (0 : ℝ)) h0U
  have hU_mem : U ∈ 𝓝[Set.Ioi 0] (0 : ℝ) := by
    exact nhdsWithin_le_nhds
      (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  have hfilter : 𝓝[Set.Ioi 0] (0 : ℝ) ≤ 𝓝[U] (0 : ℝ) :=
    nhdsWithin_le_of_mem hU_mem
  have hTU' :
      TendstoUniformlyOn F (F (0 : ℝ)) (𝓝[Set.Ioi 0] (0 : ℝ)) Kη :=
    tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
      ((tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hTU).mono_left hfilter)
  have hF0 :
      F (0 : ℝ) =
        fun _ : BHW.OS45FlatCommonChartReal d n =>
          L (D.toZeroDiagonalCLM ρperm φ) := by
    funext η
    dsimp [F]
    congr 1
    apply Subtype.ext
    unfold BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM
    unfold BHW.OS45Figure24SourceCutoffData.toShiftedZeroDiagonalCLM
    unfold BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM
    unfold BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM
    change
      D.toSchwartzNPointCLM ρperm
          (SCV.translateSchwartzCLM ((sgn * (0 : ℝ)) • η) φ) =
        D.toSchwartzNPointCLM ρperm φ
    congr 1
    ext x
    simp [SCV.translateSchwartzCLM_apply, SCV.translateSchwartz_apply]
  have hTU'' :
      TendstoUniformlyOn F
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          L (D.toZeroDiagonalCLM ρperm φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    simpa [hF0] using hTU'
  simpa [F] using hTU''

/-- Canonical chosen source-test family for a Figure-2-4 patch.  The
noncomputable choice is exactly the same cutoff choice used by
`os45_BHWJost_flatCommonChart_schwingerCLM`. -/
noncomputable def os45FlatCommonChartSideTestCLM
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d n :=
  let D := Classical.choice
    (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  D.toSideZeroDiagonalCLM ρperm sgn ε η

/-- The common-boundary Schwinger functional in flattened common-chart
coordinates, including the absolute Jacobian for the source-to-flat real
change of variables. -/
noncomputable def os45_BHWJost_flatCommonChart_schwingerCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (_lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (ρperm : Equiv.Perm (Fin n)) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
  let D := Classical.choice
    (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  ((BHW.os45CommonEdgeFlatJacobianAbs n : ℂ)) •
    ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
      (D.toZeroDiagonalCLM ρperm))

/-- Points of the ordinary extended tube lie in the local BHW/Jost ambient. -/
theorem os45BHWJostAmbient_mem_identity
    (τ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ BHW.ExtendedTube d n) :
    z ∈ BHW.os45BHWJostAmbient d n τ := by
  exact Or.inl ⟨1, z, hz, (BHW.complexLorentzAction_one z).symm⟩

/-- Points of the selected adjacent permuted sector lie in the local
BHW/Jost ambient. -/
theorem os45BHWJostAmbient_mem_adjacent
    (τ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ BHW.permutedExtendedTubeSector d n τ) :
    z ∈ BHW.os45BHWJostAmbient d n τ := by
  exact Or.inr ⟨1, z, hz, (BHW.complexLorentzAction_one z).symm⟩

/-- The OS45 BHW/Jost ambient is exactly the union of the two initial sectors.

The definition stores proper-complex Lorentz saturations, but both initial
sectors are already invariant under the complex Lorentz action. -/
theorem os45BHWJostAmbient_eq_initialSector_union
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    BHW.os45BHWJostAmbient d n τ =
      BHW.ExtendedTube d n ∪ BHW.permutedExtendedTubeSector d n τ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨Λ, u, hu, rfl⟩ | ⟨Λ, u, hu, rfl⟩
    · exact Or.inl
        (BHW.complexLorentzAction_mem_extendedTube (d := d) n Λ hu)
    · exact Or.inr
        ((BHW.permutedExtendedTubeSector_complexLorentzAction_iff
          (d := d) (n := n) Λ τ u).2 hu)
  · intro hz
    rcases hz with hz | hz
    · exact BHW.os45BHWJostAmbient_mem_identity
        (d := d) (n := n) τ hz
    · exact BHW.os45BHWJostAmbient_mem_adjacent
        (d := d) (n := n) τ hz

private theorem isOpen_complexLorentz_saturation
    {S : Set (Fin n → Fin (d + 1) → ℂ)}
    (hS : IsOpen S) :
    IsOpen
      {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
        u ∈ S ∧ z = BHW.complexLorentzAction Λ u} := by
  have hset :
      {z | ∃ (Λ : ComplexLorentzGroup d) (u : Fin n → Fin (d + 1) → ℂ),
        u ∈ S ∧ z = BHW.complexLorentzAction Λ u} =
        ⋃ Λ : ComplexLorentzGroup d,
          (fun u : Fin n → Fin (d + 1) → ℂ =>
            BHW.complexLorentzAction Λ u) '' S := by
    ext z
    constructor
    · rintro ⟨Λ, u, hu, rfl⟩
      exact Set.mem_iUnion.mpr ⟨Λ, u, hu, rfl⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨Λ, u, hu, rfl⟩
      exact ⟨Λ, u, hu, rfl⟩
  rw [hset]
  exact isOpen_iUnion fun Λ =>
    (BHW.complexLorentzAction_isOpenMap Λ) S hS

/-- The local BHW/Jost ambient is open. -/
theorem os45BHWJostAmbient_open
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    IsOpen (BHW.os45BHWJostAmbient d n τ) := by
  exact
    (isOpen_complexLorentz_saturation
      (d := d) (n := n) BHW.isOpen_extendedTube).union
      (isOpen_complexLorentz_saturation
        (d := d) (n := n)
        (BHW.isOpen_permutedExtendedTubeSector
          (d := d) (n := n) τ))

/-- The base point belongs to its local BHW/Jost hull once it lies in the
ambient. -/
theorem mem_os45BHWJostHull_self
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    zbase ∈ BHW.os45BHWJostHull d n τ zbase := by
  simpa [BHW.os45BHWJostHull] using
    (mem_pathComponentIn_self hzbase)

/-- The local BHW/Jost hull is contained in its concrete ambient. -/
theorem os45BHWJostHull_subset_ambient
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ) :
    BHW.os45BHWJostHull d n τ zbase ⊆
      BHW.os45BHWJostAmbient d n τ := by
  intro z hz
  exact hz.target_mem

/-- The local BHW/Jost hull is nonempty when its base point lies in the
ambient. -/
theorem os45BHWJostHull_nonempty
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    (BHW.os45BHWJostHull d n τ zbase).Nonempty :=
  ⟨zbase, BHW.mem_os45BHWJostHull_self
    (d := d) (n := n) τ zbase hzbase⟩

/-- The local BHW/Jost hull is path-connected when its base point lies in the
ambient. -/
theorem os45BHWJostHull_isPathConnected
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsPathConnected (BHW.os45BHWJostHull d n τ zbase) := by
  simpa [BHW.os45BHWJostHull] using
    (isPathConnected_pathComponentIn hzbase)

/-- The local BHW/Jost hull is connected when its base point lies in the
ambient. -/
theorem os45BHWJostHull_connected
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsConnected (BHW.os45BHWJostHull d n τ zbase) :=
  (BHW.os45BHWJostHull_isPathConnected
    (d := d) (n := n) τ zbase hzbase).isConnected

/-- The local BHW/Jost hull is open when its base point lies in the
ambient. -/
theorem os45BHWJostHull_open
    (τ : Equiv.Perm (Fin n)) (zbase : Fin n → Fin (d + 1) → ℂ)
    (hzbase : zbase ∈ BHW.os45BHWJostAmbient d n τ) :
    IsOpen (BHW.os45BHWJostHull d n τ zbase) :=
  BHW.isOpen_pathComponentIn_of_isOpen_normed
    (BHW.os45BHWJostAmbient_open d n τ) hzbase

/-- Any ordinary extended-tube point lies in the local BHW/Jost hull based at
an ordinary extended-tube point. -/
theorem mem_os45BHWJostHull_of_extendedTube
    (τ : Equiv.Perm (Fin n))
    {zbase z : Fin n → Fin (d + 1) → ℂ}
    (hzbase : zbase ∈ BHW.ExtendedTube d n)
    (hz : z ∈ BHW.ExtendedTube d n) :
    z ∈ BHW.os45BHWJostHull d n τ zbase := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined : JoinedIn (BHW.ExtendedTube d n) zbase z :=
    hpath.joinedIn zbase hzbase z hz
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) τ hw)

/-- Any selected adjacent-sector point lies in the local BHW/Jost hull based
at a selected adjacent-sector point. -/
theorem mem_os45BHWJostHull_of_permutedExtendedTubeSector
    (τ : Equiv.Perm (Fin n))
    {zbase z : Fin n → Fin (d + 1) → ℂ}
    (hzbase : zbase ∈ BHW.permutedExtendedTubeSector d n τ)
    (hz : z ∈ BHW.permutedExtendedTubeSector d n τ) :
    z ∈ BHW.os45BHWJostHull d n τ zbase := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hconn :
      IsConnected (BHW.permutedExtendedTubeSector d n τ) :=
    ⟨⟨zbase, hzbase⟩,
      BHW.permutedExtendedTubeSector_isPreconnected
        (d := d) (n := n) τ⟩
  have hpath :
      IsPathConnected (BHW.permutedExtendedTubeSector d n τ) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.permutedExtendedTubeSector d n τ)
      (BHW.isOpen_permutedExtendedTubeSector
        (d := d) (n := n) τ)).mp hconn
  have hjoined :
      JoinedIn (BHW.permutedExtendedTubeSector d n τ) zbase z :=
    hpath.joinedIn zbase hzbase z hz
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_adjacent
      (d := d) (n := n) τ hw)

/-- The selected adjacent Wick edge is joined to the checked Figure-2-4
rotated lift inside the local BHW/Jost ambient. -/
theorem os45Figure24_joined_adjacentWick_to_adjLift0
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval)) := by
  classical
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  have hzlift_ET : zlift ∈ BHW.ExtendedTube d n := by
    simpa [zlift] using
      P.adjLift_mem_extendedTube x hx (0 : unitInterval)
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval)
  have hInv :
      BHW.complexLorentzAction Λinv zlift = zadj := by
    have hraw :
        BHW.complexLorentzAction Λinv zlift =
          BHW.permAct (d := d) P.τ Γ := by
      simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
        hΛinv (BHW.permAct (d := d) P.τ Γ)
    calc
      BHW.complexLorentzAction Λinv zlift
          = BHW.permAct (d := d) P.τ Γ := hraw
      _ = zadj := by
        ext k μ
        simp [zadj, Γ, BHW.os45Figure24IdentityPath_zero, BHW.permAct]
  have hgrp :
      JoinedIn (Set.univ : Set (ComplexLorentzGroup d)) Λinv 1 :=
    (ComplexLorentzGroup.isPathConnected (d := d)).joinedIn
      Λinv (Set.mem_univ _) 1 (Set.mem_univ _)
  refine
    ⟨{ toFun := fun t =>
          BHW.complexLorentzAction (hgrp.somePath t) zlift
       continuous_toFun :=
          (BHW.continuous_complexLorentzAction_fst
            (d := d) (n := n) zlift).comp
            hgrp.somePath.continuous_toFun
       source' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 0) zlift = zadj
          rw [hgrp.somePath.source]
          exact hInv
       target' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 1) zlift = zlift
          rw [hgrp.somePath.target]
          exact BHW.complexLorentzAction_one zlift },
      ?_⟩
  intro t
  exact Or.inl ⟨hgrp.somePath t, zlift, hzlift_ET, rfl⟩

/-- The checked Figure-2-4 lift at `0` is joined to the real source patch
inside the local BHW/Jost ambient through the ordinary extended tube. -/
theorem os45Figure24_joined_adjLift0_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval))
      (BHW.realEmbed x) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  have hzlift_ET : zlift ∈ BHW.ExtendedTube d n := by
    simpa [zlift] using
      P.adjLift_mem_extendedTube x hx (0 : unitInterval)
  have hreal_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n :=
    P.V_ET x hx
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n) zlift (BHW.realEmbed x) :=
    hpath.joinedIn zlift hzlift_ET (BHW.realEmbed x) hreal_ET
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- The inverse Figure-2-4 Lorentz rotation sends the checked lift at `0` to
the selected adjacent Wick edge. -/
theorem os45Figure24_exists_lorentz_adjLift0_to_adjacentWick
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) :
    ∃ Λ : ComplexLorentzGroup d,
      BHW.complexLorentzAction Λ
          (BHW.os45Figure24AdjacentLift
            (d := d) (n := n) hd P.τ x (0 : unitInterval)) =
        fun k => wickRotatePoint (x (P.τ k)) := by
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  refine ⟨Λinv, ?_⟩
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval)
  have hraw :
      BHW.complexLorentzAction Λinv zlift =
        BHW.permAct (d := d) P.τ Γ := by
    simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
      hΛinv (BHW.permAct (d := d) P.τ Γ)
  calc
    BHW.complexLorentzAction Λinv
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval))
        = BHW.complexLorentzAction Λinv zlift := by rfl
    _ = BHW.permAct (d := d) P.τ Γ := hraw
    _ = zadj := by
      ext k μ
      simp [zadj, Γ, BHW.os45Figure24IdentityPath_zero, BHW.permAct]
    _ = (fun k => wickRotatePoint (x (P.τ k))) := by rfl

/-- The selected adjacent Wick edge is joined to the real source patch inside
the local BHW/Jost ambient. -/
theorem os45Figure24_joined_adjacentWick_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.realEmbed x) :=
  (BHW.os45Figure24_joined_adjacentWick_to_adjLift0
    (d := d) (n := n) hd P x hx).trans
    (BHW.os45Figure24_joined_adjLift0_to_realPatch
      (d := d) (n := n) hd P x hx)

private theorem os45Figure24_joined_realPatch_to_realPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x y : NPointDomain d n} (hx : x ∈ P.V) (hy : y ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.realEmbed x) (BHW.realEmbed y) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n)
        (BHW.realEmbed x) (BHW.realEmbed y) :=
    hpath.joinedIn (BHW.realEmbed x) (P.V_ET x hx)
      (BHW.realEmbed y) (P.V_ET y hy)
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- A real point of the checked Figure-2-4 source patch is joined to its
ordinary Wick edge inside the local BHW/Jost ambient. -/
theorem os45Figure24_joined_realPatch_to_ordinaryWick
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    JoinedIn (BHW.os45BHWJostAmbient d n P.τ)
      (BHW.realEmbed x) (fun k => wickRotatePoint (x k)) := by
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  have hwick_ET :
      (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n := by
    have hroot :
        (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
          _root_.ForwardTube d n :=
      wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
        (P.V_ordered x hx)
    have hBHW :
        (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
          BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot
    exact BHW.forwardTube_subset_extendedTube (by simpa using hBHW)
  have hpath : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoined :
      JoinedIn (BHW.ExtendedTube d n)
        (BHW.realEmbed x) (fun k => wickRotatePoint (x k)) :=
    hpath.joinedIn (BHW.realEmbed x) (P.V_ET x hx)
      (fun k => wickRotatePoint (x k)) hwick_ET
  exact hjoined.mono (by
    intro w hw
    exact BHW.os45BHWJostAmbient_mem_identity
      (d := d) (n := n) P.τ hw)

/-- Every real point of the checked Figure-2-4 source patch lies in the local
BHW/Jost hull based at any selected adjacent Wick point of the same patch. -/
theorem mem_os45BHWJostHull_realPatch_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    BHW.realEmbed x ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      (BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx)

/-- The checked Figure-2-4 lift at `0` lies in the local BHW/Jost hull based
at any selected adjacent Wick point of the same source patch. -/
theorem mem_os45BHWJostHull_adjLift0_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        (BHW.os45Figure24_joined_adjLift0_to_realPatch
          (d := d) (n := n) hd P x hx).symm)

/-- Every ordinary Wick point of the checked Figure-2-4 source patch lies in
the local BHW/Jost hull based at any selected adjacent Wick point of the same
source patch. -/
theorem mem_os45BHWJostHull_ordinaryWick_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    (fun k => wickRotatePoint (x k)) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        (BHW.os45Figure24_joined_realPatch_to_ordinaryWick
          (d := d) (n := n) hd P hx))

/-- Every selected adjacent Wick point of the checked Figure-2-4 source patch
lies in the local BHW/Jost hull based at any selected adjacent Wick point of
the same patch. -/
theorem mem_os45BHWJostHull_adjacentWick_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {xbase x : NPointDomain d n}
    (hxbase : xbase ∈ P.V) (hx : x ∈ P.V) :
    (fun k => wickRotatePoint (x (P.τ k))) ∈
      BHW.os45BHWJostHull d n P.τ
        (fun k => wickRotatePoint (xbase (P.τ k))) := by
  exact
    (BHW.os45Figure24_joined_adjacentWick_to_realPatch
      (d := d) (n := n) hd P xbase hxbase).trans
      ((BHW.os45Figure24_joined_realPatch_to_realPatch
        (d := d) (n := n) hd P hxbase hx).trans
        ((BHW.os45Figure24_joined_adjLift0_to_realPatch
          (d := d) (n := n) hd P x hx).symm.trans
          (BHW.os45Figure24_joined_adjacentWick_to_adjLift0
            (d := d) (n := n) hd P x hx).symm))

/-- Checked local OS45/BHW/Jost hull geometry for one canonical Figure-2-4
source patch.  This record contains only the finite-dimensional path-component
carrier and pointwise membership fields; analytic branch continuation is the
next layer. -/
structure OS45BHWJostHullData
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) where
  zbase : Fin n → Fin (d + 1) → ℂ
  zbase_eq :
    zbase = fun k => wickRotatePoint (P.xseed (P.τ k))
  ΩJ : Set (Fin n → Fin (d + 1) → ℂ)
  ΩJ_eq :
    ΩJ = BHW.os45BHWJostHull d n P.τ zbase
  zbase_mem_ambient :
    zbase ∈ BHW.os45BHWJostAmbient d n P.τ
  ΩJ_open : IsOpen ΩJ
  ΩJ_connected : IsConnected ΩJ
  ΩJ_subset_hull :
    ΩJ ⊆ BHW.os45BHWJostHull d n P.τ zbase
  adjacentWick_mem :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x (P.τ k))) ∈ ΩJ
  realPatch_mem :
    ∀ x, x ∈ P.V → BHW.realEmbed x ∈ ΩJ
  adjLift0_mem :
    ∀ x, x ∈ P.V →
      BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval) ∈ ΩJ

/-- Producer for the pure local BHW/Jost hull attached to the canonical
Figure-2-4 source patch. -/
def os45_BHWJostHullData_of_figure24
    [NeZero d]
    (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n)
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    BHW.OS45BHWJostHullData (d := d) hd n i hi P := by
  classical
  let zbase : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (P.xseed (P.τ k))
  have hzbase_ambient :
      zbase ∈ BHW.os45BHWJostAmbient d n P.τ := by
    simpa [zbase] using
      (BHW.os45Figure24_joined_adjacentWick_to_realPatch
        (d := d) (n := n) hd P P.xseed P.xseed_mem).source_mem
  refine
    { zbase := zbase
      zbase_eq := rfl
      ΩJ := BHW.os45BHWJostHull d n P.τ zbase
      ΩJ_eq := rfl
      zbase_mem_ambient := hzbase_ambient
      ΩJ_open :=
        BHW.os45BHWJostHull_open
          (d := d) (n := n) P.τ zbase hzbase_ambient
      ΩJ_connected :=
        BHW.os45BHWJostHull_connected
          (d := d) (n := n) P.τ zbase hzbase_ambient
      ΩJ_subset_hull := ?_
      adjacentWick_mem := ?_
      realPatch_mem := ?_
      adjLift0_mem := ?_ }
  · intro z hz
    exact hz
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_adjacentWick_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_realPatch_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx
  · intro x hx
    simpa [zbase] using
      BHW.mem_os45BHWJostHull_adjLift0_of_figure24
        (d := d) (n := n) hd P P.xseed_mem hx

/-- The ordinary Wick edge of the checked source patch lies in the stored
local BHW/Jost hull. -/
theorem OS45BHWJostHullData.ordinaryWick_mem
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x k)) ∈ H.ΩJ := by
  intro x hx
  simpa [H.ΩJ_eq, H.zbase_eq] using
    BHW.mem_os45BHWJostHull_ordinaryWick_of_figure24
      (d := d) (n := n) hd P P.xseed_mem hx

/-- The stored base point belongs to the stored local BHW/Jost hull. -/
theorem OS45BHWJostHullData.zbase_mem_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.zbase ∈ H.ΩJ := by
  simpa [H.ΩJ_eq] using
    BHW.mem_os45BHWJostHull_self
      (d := d) (n := n) P.τ H.zbase H.zbase_mem_ambient

/-- The stored local BHW/Jost hull is nonempty. -/
theorem OS45BHWJostHullData.ΩJ_nonempty
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ΩJ.Nonempty :=
  ⟨H.zbase, H.zbase_mem_ΩJ⟩

/-- The stored local BHW/Jost hull is path-connected. -/
theorem OS45BHWJostHullData.ΩJ_isPathConnected
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    IsPathConnected H.ΩJ := by
  simpa [H.ΩJ_eq] using
    BHW.os45BHWJostHull_isPathConnected
      (d := d) (n := n) P.τ H.zbase H.zbase_mem_ambient

/-- The stored local hull is contained in the concrete local BHW/Jost
ambient. -/
theorem OS45BHWJostHullData.ΩJ_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ΩJ ⊆ BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact
    BHW.os45BHWJostHull_subset_ambient
      (d := d) (n := n) P.τ H.zbase
      (H.ΩJ_subset_hull hz)

/-- The ordinary extended tube is one initial domain for the local BHW/Jost
ambient. -/
theorem OS45BHWJostHullData.extendedTube_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.ExtendedTube d n ⊆ BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact BHW.os45BHWJostAmbient_mem_identity
    (d := d) (n := n) P.τ hz

/-- The selected adjacent permuted extended-tube sector is the other initial
domain for the local BHW/Jost ambient. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_subset_ambient
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.permutedExtendedTubeSector d n P.τ ⊆
      BHW.os45BHWJostAmbient d n P.τ := by
  intro z hz
  exact BHW.os45BHWJostAmbient_mem_adjacent
    (d := d) (n := n) P.τ hz

/-- Ordinary Wick rotations of the checked source patch lie in the ordinary
extended tube. -/
theorem OS45BHWJostHullData.ordinaryWick_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
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
      (P.V_ordered x hx)
  have hBHW :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        BHW.ForwardTube d n := by
    simpa [hft_eq] using hroot
  exact BHW.forwardTube_subset_extendedTube (by simpa using hBHW)

/-- Adjacent Wick rotations of the checked source patch lie in the selected
adjacent initial sector. -/
theorem OS45BHWJostHullData.adjacentWick_mem_permutedExtendedTubeSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x (P.τ k))) ∈
        BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  have hsector :
      (fun k => wickRotatePoint
        (x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) ∈
        BHW.permutedExtendedTubeSector d n
          (Equiv.swap i ⟨i.val + 1, hi⟩) :=
    BHW.os45_adjacentWick_mem_selectedAdjacentSector_of_ordered
      (d := d) (n := n) i hi x (P.V_ordered x hx)
  simpa [P.τ_eq] using hsector

/-- The real source patch lies in the ordinary extended tube. -/
theorem OS45BHWJostHullData.realPatch_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V → BHW.realEmbed x ∈ BHW.ExtendedTube d n :=
  P.V_ET

/-- The real source patch also lies in the selected adjacent initial sector
after applying the stored source permutation. -/
theorem OS45BHWJostHullData.realPatch_mem_permutedExtendedTubeSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      BHW.realEmbed x ∈ BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  rw [BHW.permutedExtendedTubeSector]
  simpa [BHW.permAct_realEmbed] using P.V_swapET x hx

/-- The ordinary initial extended tube meets the stored local hull at the
checked Figure-2-4 seed. -/
theorem OS45BHWJostHullData.extendedTube_meets_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    (BHW.ExtendedTube d n ∩ H.ΩJ).Nonempty := by
  refine ⟨fun k => wickRotatePoint (P.xseed k), ?_, ?_⟩
  · exact H.ordinaryWick_mem_extendedTube P.xseed P.xseed_mem
  · exact H.ordinaryWick_mem P.xseed P.xseed_mem

/-- The selected adjacent initial sector meets the stored local hull at the
checked Figure-2-4 adjacent Wick seed. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_meets_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ).Nonempty := by
  refine ⟨fun k => wickRotatePoint (P.xseed (P.τ k)), ?_, ?_⟩
  · exact H.adjacentWick_mem_permutedExtendedTubeSector P.xseed P.xseed_mem
  · exact H.adjacentWick_mem P.xseed P.xseed_mem

/-- A chosen base point in the ordinary initial sector and the stored
local hull. -/
noncomputable def OS45BHWJostHullData.ordinaryBase
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    Fin n → Fin (d + 1) → ℂ :=
  Classical.choose H.extendedTube_meets_ΩJ

/-- The ordinary chosen base lies in the ordinary extended tube. -/
theorem OS45BHWJostHullData.ordinaryBase_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ordinaryBase ∈ BHW.ExtendedTube d n :=
  (Classical.choose_spec H.extendedTube_meets_ΩJ).1

/-- The ordinary chosen base lies in the stored local BHW/Jost hull. -/
theorem OS45BHWJostHullData.ordinaryBase_mem_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ordinaryBase ∈ H.ΩJ :=
  (Classical.choose_spec H.extendedTube_meets_ΩJ).2

/-- The ordinary chosen base has the exact initial-domain membership needed
by continuation chains. -/
theorem OS45BHWJostHullData.ordinaryBase_mem_initial
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ordinaryBase ∈ BHW.ExtendedTube d n ∩ H.ΩJ :=
  ⟨H.ordinaryBase_mem_extendedTube, H.ordinaryBase_mem_ΩJ⟩

/-- The ordinary extended-tube sector lies in the OS I §4.5 Jost hull component
once the ordinary base point has been checked to lie in that component. -/
theorem OS45BHWJostHullData.extendedTube_subset_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.ExtendedTube d n ⊆ H.ΩJ := by
  classical
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  intro z hz
  have hOrd_mem : H.ordinaryBase ∈ H.ΩJ := H.ordinaryBase_mem_ΩJ
  have hOrd_base :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.zbase H.ordinaryBase := by
    simpa [H.ΩJ_eq, BHW.os45BHWJostHull] using hOrd_mem
  have hExt_path : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hOrd_to_z_ext :
      JoinedIn (BHW.ExtendedTube d n) H.ordinaryBase z :=
    hExt_path.joinedIn H.ordinaryBase H.ordinaryBase_mem_extendedTube z hz
  have hOrd_to_z :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.ordinaryBase z :=
    hOrd_to_z_ext.mono H.extendedTube_subset_ambient
  have hJoined :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.zbase z :=
    hOrd_base.trans hOrd_to_z
  simpa [H.ΩJ_eq, BHW.os45BHWJostHull] using hJoined

/-- The ordinary initial sector has unchanged intersection with the selected
local hull component. -/
theorem OS45BHWJostHullData.extendedTube_inter_ΩJ_eq
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.ExtendedTube d n ∩ H.ΩJ = BHW.ExtendedTube d n := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    exact ⟨hz, H.extendedTube_subset_ΩJ hz⟩

/-- The ordinary chosen base is joined inside the stored hull to any target
point of that hull. -/
theorem OS45BHWJostHullData.ordinaryBase_joinedIn
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ H.ΩJ) :
    JoinedIn H.ΩJ H.ordinaryBase z :=
  H.ΩJ_isPathConnected.joinedIn
    H.ordinaryBase H.ordinaryBase_mem_ΩJ z hz

/-- A chosen base point in the selected adjacent initial sector and the stored
local hull. -/
noncomputable def OS45BHWJostHullData.adjacentBase
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    Fin n → Fin (d + 1) → ℂ :=
  Classical.choose H.permutedExtendedTubeSector_meets_ΩJ

/-- The adjacent chosen base lies in the selected adjacent initial sector. -/
theorem OS45BHWJostHullData.adjacentBase_mem_permutedExtendedTubeSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.adjacentBase ∈ BHW.permutedExtendedTubeSector d n P.τ :=
  (Classical.choose_spec H.permutedExtendedTubeSector_meets_ΩJ).1

/-- The adjacent chosen base lies in the stored local BHW/Jost hull. -/
theorem OS45BHWJostHullData.adjacentBase_mem_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.adjacentBase ∈ H.ΩJ :=
  (Classical.choose_spec H.permutedExtendedTubeSector_meets_ΩJ).2

/-- The adjacent chosen base has the exact initial-domain membership needed
by continuation chains. -/
theorem OS45BHWJostHullData.adjacentBase_mem_initial
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.adjacentBase ∈ BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ :=
  ⟨H.adjacentBase_mem_permutedExtendedTubeSector, H.adjacentBase_mem_ΩJ⟩

/-- The adjacent permuted extended-tube sector lies in the OS I §4.5 Jost hull
component once the adjacent base point has been checked to lie there. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_subset_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.permutedExtendedTubeSector d n P.τ ⊆ H.ΩJ := by
  classical
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  intro z hz
  have hAdj_mem : H.adjacentBase ∈ H.ΩJ := H.adjacentBase_mem_ΩJ
  have hAdj_base :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.zbase H.adjacentBase := by
    simpa [H.ΩJ_eq, BHW.os45BHWJostHull] using hAdj_mem
  have hAdj_conn : IsConnected (BHW.permutedExtendedTubeSector d n P.τ) := by
    exact ⟨⟨H.adjacentBase, H.adjacentBase_mem_permutedExtendedTubeSector⟩,
      BHW.permutedExtendedTubeSector_isPreconnected (d := d) (n := n) P.τ⟩
  have hAdj_path :
      IsPathConnected (BHW.permutedExtendedTubeSector d n P.τ) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.permutedExtendedTubeSector d n P.τ)
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)).mp
      hAdj_conn
  have hAdj_to_z_sector :
      JoinedIn (BHW.permutedExtendedTubeSector d n P.τ) H.adjacentBase z :=
    hAdj_path.joinedIn H.adjacentBase H.adjacentBase_mem_permutedExtendedTubeSector z hz
  have hAdj_to_z :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.adjacentBase z :=
    hAdj_to_z_sector.mono H.permutedExtendedTubeSector_subset_ambient
  have hJoined :
      JoinedIn (BHW.os45BHWJostAmbient d n P.τ) H.zbase z :=
    hAdj_base.trans hAdj_to_z
  simpa [H.ΩJ_eq, BHW.os45BHWJostHull] using hJoined

/-- The stored OS45 local hull is exactly the union of the ordinary and
selected adjacent initial sectors. -/
theorem OS45BHWJostHullData.ΩJ_eq_initialSector_union
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ΩJ =
      BHW.ExtendedTube d n ∪ BHW.permutedExtendedTubeSector d n P.τ := by
  ext z
  constructor
  · intro hz
    have hzAmbient : z ∈ BHW.os45BHWJostAmbient d n P.τ :=
      H.ΩJ_subset_ambient hz
    simpa [BHW.os45BHWJostAmbient_eq_initialSector_union
      (d := d) (n := n) P.τ] using hzAmbient
  · intro hz
    rcases hz with hz | hz
    · exact H.extendedTube_subset_ΩJ hz
    · exact H.permutedExtendedTubeSector_subset_ΩJ hz

/-- The stored OS45 local hull is the neutral two-sector local `S'_n` hull
used by the pure BHW continuation axiom. -/
theorem OS45BHWJostHullData.ΩJ_eq_localSPrimeTwoSectorHull
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    H.ΩJ = BHW.localSPrimeTwoSectorHull d n P.τ H.zbase := by
  simp [BHW.localSPrimeTwoSectorHull, H.ΩJ_eq,
    BHW.os45BHWJostHull, BHW.localSPrimeTwoSectorAmbient,
    BHW.os45BHWJostAmbient_eq_initialSector_union
      (d := d) (n := n) P.τ]

/-- The single local `S'_n` reference branch produced on the checked OS45
BHW/Jost hull.  The two restriction fields are exactly the ordinary initial
formula and the selected adjacent initial formula. -/
structure OS45BHWJostSPrimeBranchData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) : Type where
  B : (Fin n → Fin (d + 1) → ℂ) → ℂ
  B_holo : DifferentiableOn ℂ B H.ΩJ
  eq_ordinary :
    Set.EqOn B (BHW.extendF (bvt_F OS lgc n))
      (BHW.ExtendedTube d n ∩ H.ΩJ)
  eq_adjacent :
    Set.EqOn B
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z))
      (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ)

/-- Once the OS I section 4.5 Figure-2-4 local EOW seed is available, the
authorized neutral local `S'_n` theorem mechanically produces the single
reference branch on the checked OS45 local hull. -/
noncomputable def os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeed
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hEOW_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ IsPreconnected W ∧
        BHW.realEmbed P.xseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W) :
    BHW.OS45BHWJostSPrimeBranchData hd OS lgc H := by
  let Ford : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    BHW.extendF (bvt_F OS lgc n)
  let Fadj : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ z)
  have hFord_holo :
      DifferentiableOn ℂ Ford (BHW.ExtendedTube d n) := by
    simpa [Ford] using
      BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n
  have hFadj_holo :
      DifferentiableOn ℂ Fadj
        (BHW.permutedExtendedTubeSector d n P.τ) := by
    simpa [Fadj, BHW.permutedExtendedTubeSector] using
      BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ
  have hFord_cinv :
      BHW.ComplexLorentzInvariantOn d n (BHW.ExtendedTube d n) Ford := by
    simpa [Ford] using
      BHW.complexLorentzInvariantOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n
  have hFadj_cinv :
      BHW.ComplexLorentzInvariantOn d n
        (BHW.permutedExtendedTubeSector d n P.τ) Fadj := by
    simpa [Fadj] using
      BHW.complexLorentzInvariantOn_extendF_bvt_F_permAct_permutedSector
        (d := d) OS lgc n P.τ
  have hbase :
      H.zbase ∈ BHW.localSPrimeTwoSectorAmbient d n P.τ := by
    have hbase_union :
        H.zbase ∈
          BHW.ExtendedTube d n ∪
            BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [BHW.os45BHWJostAmbient_eq_initialSector_union
        (d := d) (n := n) P.τ] using H.zbase_mem_ambient
    simpa [BHW.localSPrimeTwoSectorAmbient] using hbase_union
  have hΩ : H.ΩJ = BHW.localSPrimeTwoSectorHull d n P.τ H.zbase :=
    H.ΩJ_eq_localSPrimeTwoSectorHull
  have hseed :
      BHW.realEmbed P.xseed ∈
        BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [hΩ] using H.realPatch_mem P.xseed P.xseed_mem
    · exact H.realPatch_mem_extendedTube P.xseed P.xseed_mem
    · exact H.realPatch_mem_permutedExtendedTubeSector P.xseed P.xseed_mem
  have hEOW_seed' :
      ∃ W : Set (BHW.SPrimeConfig d n),
        IsOpen W ∧ IsPreconnected W ∧
        BHW.realEmbed P.xseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn Ford Fadj W := by
    simpa [Ford, Fadj] using hEOW_seed
  let hbranch :=
    BHW.localSPrime_twoSectorBranch_of_EOW_BHW
      (d := d) hd P.τ H.zbase (BHW.realEmbed P.xseed)
      hbase hseed Ford Fadj hFord_holo hFadj_holo
      hFord_cinv hFadj_cinv hEOW_seed'
  let B := Classical.choose hbranch
  have hB_spec := Classical.choose_spec hbranch
  have hB_holo :
      DifferentiableOn ℂ B
        (BHW.localSPrimeTwoSectorHull d n P.τ H.zbase) :=
    hB_spec.1
  have hB_ord :
      Set.EqOn B Ford
        (BHW.ExtendedTube d n ∩
          BHW.localSPrimeTwoSectorHull d n P.τ H.zbase) :=
    hB_spec.2.1
  have hB_adj :
      Set.EqOn B Fadj
        (BHW.permutedExtendedTubeSector d n P.τ ∩
          BHW.localSPrimeTwoSectorHull d n P.τ H.zbase) :=
    hB_spec.2.2
  refine
    { B := B
      B_holo := ?_
      eq_ordinary := ?_
      eq_adjacent := ?_ }
  · simpa [hΩ] using hB_holo
  · simpa [Ford, hΩ] using hB_ord
  · simpa [Fadj, hΩ] using hB_adj

/-- A two-open-cover holomorphy gluing lemma for an `if`-defined branch.

On the second open set, the overlap equality makes the `if_pos` branch agree
with the second function, so no closed-complement argument is needed. -/
theorem differentiableOn_if_mem_openCover_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U U1 U2 : Set E} {f1 f2 : E → F}
    [DecidablePred (fun z : E => z ∈ U1)]
    (hU1_open : IsOpen U1) (hU2_open : IsOpen U2)
    (hcover : U ⊆ U1 ∪ U2)
    (hf1 : DifferentiableOn ℂ f1 U1)
    (hf2 : DifferentiableOn ℂ f2 U2)
    (h12 : Set.EqOn f1 f2 (U1 ∩ U2)) :
    DifferentiableOn ℂ (fun z => if z ∈ U1 then f1 z else f2 z) U := by
  intro z hzU
  rcases hcover hzU with hz1 | hz2
  · have hzAt : DifferentiableAt ℂ f1 z :=
      (hf1 z hz1).differentiableAt (hU1_open.mem_nhds hz1)
    have hlocal :
        (fun y => if y ∈ U1 then f1 y else f2 y) =ᶠ[𝓝 z] f1 := by
      filter_upwards [hU1_open.mem_nhds hz1] with y hy1
      simp [hy1]
    exact
      hzAt.differentiableWithinAt.congr_of_eventuallyEq
        (hlocal.filter_mono nhdsWithin_le_nhds) (by simp [hz1])
  · have hzAt : DifferentiableAt ℂ f2 z :=
      (hf2 z hz2).differentiableAt (hU2_open.mem_nhds hz2)
    have hlocal :
        (fun y => if y ∈ U1 then f1 y else f2 y) =ᶠ[𝓝 z] f2 := by
      filter_upwards [hU2_open.mem_nhds hz2] with y hy2
      by_cases hy1 : y ∈ U1
      · simpa [hy1] using h12 ⟨hy1, hy2⟩
      · simp [hy1]
    have hzEq : (if z ∈ U1 then f1 z else f2 z) = f2 z := by
      by_cases hz1 : z ∈ U1
      · simpa [hz1] using h12 ⟨hz1, hz2⟩
      · simp [hz1]
    exact
      hzAt.differentiableWithinAt.congr_of_eventuallyEq
        (hlocal.filter_mono nhdsWithin_le_nhds) hzEq

/-- The selected adjacent initial sector has unchanged intersection with the
selected local hull component. -/
theorem OS45BHWJostHullData.permutedExtendedTubeSector_inter_ΩJ_eq
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ =
      BHW.permutedExtendedTubeSector d n P.τ := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    exact ⟨hz, H.permutedExtendedTubeSector_subset_ΩJ hz⟩

/-- The adjacent chosen base is joined inside the stored hull to any target
point of that hull. -/
theorem OS45BHWJostHullData.adjacentBase_joinedIn
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ H.ΩJ) :
    JoinedIn H.ΩJ H.adjacentBase z :=
  H.ΩJ_isPathConnected.joinedIn
    H.adjacentBase H.adjacentBase_mem_ΩJ z hz

/-- Assemble the existing source-patch BHW/Jost pair carrier from the strict
local BHW/Jost hull and two supplied branches on that hull.  The analytic
work is exactly the production of the branches and the four trace equations;
this constructor is only carrier bookkeeping. -/
noncomputable def OS45BHWJostHullData.toPairDataOfBranches
    [NeZero d]
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (Bord Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (Bord_holo : DifferentiableOn ℂ Bord H.ΩJ)
    (Btau_holo : DifferentiableOn ℂ Btau H.ΩJ)
    (Bord_wick_trace :
      ∀ x, x ∈ P.V →
        Bord (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)))
    (Btau_wick_trace :
      ∀ x, x ∈ P.V →
        Btau (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))))
    (Bord_real_trace :
      ∀ x, x ∈ P.V →
        Bord (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))
    (Btau_real_trace :
      ∀ x, x ∈ P.V →
        Btau (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (P.τ k)))) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V where
  τ := P.τ
  τ_eq := P.τ_eq
  U := H.ΩJ
  V_open := P.V_open
  V_nonempty := P.V_nonempty
  U_open := H.ΩJ_open
  U_connected := H.ΩJ_connected
  wick_mem := H.ordinaryWick_mem
  real_mem := H.realPatch_mem
  Bord := Bord
  Btau := Btau
  Bord_holo := Bord_holo
  Btau_holo := Btau_holo
  Bord_wick_trace := Bord_wick_trace
  Btau_wick_trace := Btau_wick_trace
  Bord_real_trace := Bord_real_trace
  Btau_real_trace := Btau_real_trace

/-- The checked pair carrier obtained from the single local `S'_n` reference
branch.  Both carrier branch slots are the same function; the selected
adjacent Wick trace uses the OS symmetric `S'_n` normalization
`bvt_F_perm`. -/
noncomputable def OS45BHWJostSPrimeBranchData.toPairData
    [NeZero d]
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {H : BHW.OS45BHWJostHullData (d := d) hd n i hi P}
    (S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V := by
  have hOrdWickTrace :
      ∀ x, x ∈ P.V →
        S.B (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
    intro x hx
    have hS :
        S.B (fun k => wickRotatePoint (x k)) =
          BHW.extendF (bvt_F OS lgc n)
            (fun k => wickRotatePoint (x k)) :=
      S.eq_ordinary
        ⟨H.ordinaryWick_mem_extendedTube x hx,
          H.ordinaryWick_mem x hx⟩
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
    have hx_forward :
        (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
      have hroot :
          (fun k => wickRotatePoint
            (x ((1 : Equiv.Perm (Fin n)) k))) ∈
            _root_.ForwardTube d n :=
        wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
          (d := d) (n := n) (1 : Equiv.Perm (Fin n))
          (P.V_ordered x hx)
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot
    exact hS.trans
      (BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_lorentz (fun k => wickRotatePoint (x k)) hx_forward)
  refine
    BHW.OS45BHWJostHullData.toPairDataOfBranches
      (d := d) (n := n) hd OS lgc H
      S.B S.B S.B_holo S.B_holo ?_ ?_ ?_ ?_
  · intro x hx
    exact hOrdWickTrace x hx
  · intro x hx
    have hOrd :
        S.B (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) :=
      hOrdWickTrace x hx
    exact hOrd.trans
      ((bvt_F_perm (d := d) OS lgc n P.τ
        (fun k => wickRotatePoint (x k))).symm)
  · intro x hx
    exact
      S.eq_ordinary
        ⟨H.realPatch_mem_extendedTube x hx,
          H.realPatch_mem x hx⟩
  · intro x hx
    have hS :
        S.B (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ (BHW.realEmbed x)) :=
      S.eq_adjacent
        ⟨H.realPatch_mem_permutedExtendedTubeSector x hx,
          H.realPatch_mem x hx⟩
    calc
      S.B (BHW.realEmbed x)
          = BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ (BHW.realEmbed x)) := hS
      _ = BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (P.τ k))) := by
          simp [BHW.permAct_realEmbed]

/-- Assemble the source-patch BHW/Jost pair carrier from two already-glued
direct continuation atlases on the checked local hull.

This is a strict-route reducer: the hard work remains the construction of the
two atlases and the adjacent ordinary-Wick boundary trace. -/
noncomputable def OS45BHWJostHullData.toPairDataOfContinuationAtlases
    [NeZero d]
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (Aord :
      BHW.BHWSourcePatchContinuationAtlas hd n P.τ
        (BHW.ExtendedTube d n) H.ΩJ
        (BHW.extendF (bvt_F OS lgc n)))
    (Aadj :
      BHW.BHWSourcePatchContinuationAtlas hd n P.τ
        (BHW.permutedExtendedTubeSector d n P.τ) H.ΩJ
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)))
    (Btau_wick_trace :
      ∀ x, x ∈ P.V →
        Aadj.glued (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k)))) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V := by
  refine
    BHW.OS45BHWJostHullData.toPairDataOfBranches
      (d := d) (n := n) hd OS lgc H
      Aord.glued Aadj.glued
      Aord.glued_differentiableOn
      Aadj.glued_differentiableOn
      ?_ Btau_wick_trace ?_ ?_
  · intro x hx
    have hxΩ : (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n :=
      H.ordinaryWick_mem_extendedTube x hx
    have hxH : (fun k => wickRotatePoint (x k)) ∈ H.ΩJ :=
      H.ordinaryWick_mem x hx
    have hagree :
        Aord.glued (fun k => wickRotatePoint (x k)) =
          BHW.extendF (bvt_F OS lgc n)
            (fun k => wickRotatePoint (x k)) :=
      Aord.glued_eq_B0_of_mem ⟨hxΩ, hxH⟩
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
    have hx_forward :
        (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
      have hroot :
          (fun k => wickRotatePoint
            (x ((1 : Equiv.Perm (Fin n)) k))) ∈
            _root_.ForwardTube d n :=
        wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
          (d := d) (n := n) (1 : Equiv.Perm (Fin n))
          (P.V_ordered x hx)
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot
    calc
      Aord.glued (fun k => wickRotatePoint (x k))
          = BHW.extendF (bvt_F OS lgc n)
              (fun k => wickRotatePoint (x k)) := hagree
      _ = bvt_F OS lgc n (fun k => wickRotatePoint (x k)) :=
          BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
            hF_holo hF_lorentz (fun k => wickRotatePoint (x k)) hx_forward
  · intro x hx
    exact
      Aord.glued_eq_B0_of_mem
        ⟨H.realPatch_mem_extendedTube x hx, H.realPatch_mem x hx⟩
  · intro x hx
    have hagree :
        Aadj.glued (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ (BHW.realEmbed x)) :=
      Aadj.glued_eq_B0_of_mem
        ⟨H.realPatch_mem_permutedExtendedTubeSector x hx,
          H.realPatch_mem x hx⟩
    calc
      Aadj.glued (BHW.realEmbed x)
          = BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ (BHW.realEmbed x)) := hagree
      _ = BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (P.τ k))) := by
          simp [BHW.permAct_realEmbed]

/-- Lorentz transport from the checked Figure-2-4 lift at `0` back to the
selected adjacent Wick edge, for any branch invariant on the checked local
hull. -/
theorem os45_BHWJostLiftTransport_onPatch
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {WJ branchτ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hW_inv :
      ∀ Λ z, z ∈ H.ΩJ →
        BHW.complexLorentzAction Λ z ∈ H.ΩJ →
          WJ (BHW.complexLorentzAction Λ z) = WJ z)
    (hW_adjacent :
      ∀ x, x ∈ P.V →
        WJ (fun k => wickRotatePoint (x (P.τ k))) =
          branchτ (fun k => wickRotatePoint (x (P.τ k)))) :
    ∀ x, x ∈ P.V →
      WJ
          (BHW.os45Figure24AdjacentLift
            (d := d) (n := n) hd P.τ x (0 : unitInterval)) =
        branchτ (fun k => wickRotatePoint (x (P.τ k))) := by
  intro x hx
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  rcases BHW.os45Figure24_exists_lorentz_adjLift0_to_adjacentWick
      (d := d) (n := n) hd P x with
    ⟨Λinv, hΛinv⟩
  have hzlift : zlift ∈ H.ΩJ := by
    simpa [zlift] using H.adjLift0_mem x hx
  have hΛ_mem : BHW.complexLorentzAction Λinv zlift ∈ H.ΩJ := by
    rw [show BHW.complexLorentzAction Λinv zlift = zadj by
      simpa [zlift, zadj] using hΛinv]
    exact H.adjacentWick_mem x hx
  calc
    WJ
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval))
        = WJ zlift := by rfl
    _ = WJ (BHW.complexLorentzAction Λinv zlift) := by
          exact (hW_inv Λinv zlift hzlift hΛ_mem).symm
    _ = WJ zadj := by
          rw [show BHW.complexLorentzAction Λinv zlift = zadj by
            simpa [zlift, zadj] using hΛinv]
    _ = branchτ zadj := hW_adjacent x hx
    _ = branchτ (fun k => wickRotatePoint (x (P.τ k))) := by rfl

end BHW
