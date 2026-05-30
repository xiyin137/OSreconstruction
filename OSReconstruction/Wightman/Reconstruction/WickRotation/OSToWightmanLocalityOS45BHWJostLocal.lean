import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJost
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonEdge
import OSReconstruction.SCV.CompactSupportIntegralCLM
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.OverlapIdentity
import OSReconstruction.SCV.LocalEOWSideContinuity
import OSReconstruction.SCV.LocalEOWDistributionalEnvelope
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWBranchLaw

/-!
# OS45 local BHW/Jost hull geometry

This file starts the non-source-descent local BHW/Jost carrier for the strict
OS II / OS I §4.5 route.  It contains only the concrete proper-complex
Lorentz saturation and path-component geometry used by the later local
Bargmann-Hall-Wightman continuation theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
  MeasureTheory

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

/-- The original `S'_n` point under the horizontal Figure-2-4 common edge.

The flat local EOW chart is centered at the real common-chart point
`os45CommonEdgeRealPoint 1 P.xseed`; undoing the OS45 quarter-turn gives the
actual point in the original extended-tube variables. -/
noncomputable def os45Figure24CommonEdgeSPrimeSeed
    (d n : ℕ) [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    Fin n → Fin (d + 1) → ℂ :=
  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
    (BHW.realEmbed
      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) P.xseed))

/-- The horizontal common-edge seed lies in the ordinary extended tube. -/
theorem os45Figure24CommonEdgeSPrimeSeed_mem_extendedTube
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P ∈
      BHW.ExtendedTube d n := by
  simpa [BHW.os45Figure24CommonEdgeSPrimeSeed,
    BHW.os45PulledRealBranchDomain] using
    P.V_pulled_id P.xseed P.xseed_mem

/-- The horizontal common-edge seed lies in the selected adjacent permuted
extended-tube sector. -/
theorem os45Figure24CommonEdgeSPrimeSeed_mem_permutedExtendedTubeSector
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P ∈
      BHW.permutedExtendedTubeSector d n P.τ := by
  have hτsymm : P.τ.symm = P.τ := by
    rw [P.τ_eq]
    simp
  simpa [BHW.os45Figure24CommonEdgeSPrimeSeed,
    BHW.os45PulledRealBranchDomain, BHW.permutedExtendedTubeSector,
    BHW.permAct, hτsymm] using
    P.V_pulled_tau P.xseed P.xseed_mem

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

/-- The positive Wick-section point in the flattened common chart evaluates to
the ordinary Wick branch after undoing the OS45 quarter-turn and branch label.

This is only the special anchor curve `commonEdge + i * halfTimeDirection`; it
does not identify a general side-height integral or any common-boundary CLM. -/
theorem os45FlatCommonChart_wickSection_plus_eq
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (BHW.flattenCfg n d
        (fun k μ =>
          BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ +
            (BHW.os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) *
              Complex.I)) =
      BHW.extendF (bvt_F OS lgc n)
        (fun k => wickRotatePoint (x k)) := by
  have hanchor :
      BHW.os45FlatCommonChartBranch d n OS lgc σ
        (BHW.flattenCfg n d
          (BHW.os45QuarterTurnConfig
            (fun k => wickRotatePoint (x (σ k))))) =
        BHW.extendF (bvt_F OS lgc n)
          (fun k => wickRotatePoint (x k)) := by
    have hQ :
        BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (x (σ k))) =
          (BHW.os45QuarterTurnCLE (d := d) (n := n))
            (fun k => wickRotatePoint (x (σ k))) := by
      exact
        (BHW.os45QuarterTurnCLE_apply (d := d) (n := n)
          (fun k => wickRotatePoint (x (σ k)))).symm
    rw [BHW.os45FlatCommonChartBranch, BHW.os45PulledRealBranch,
      BHW.unflatten_flatten_cfg]
    rw [hQ, ContinuousLinearEquiv.symm_apply_apply]
    congr 1
    ext k μ
    simp [BHW.permAct]
  rw [← BHW.os45QuarterTurn_perm_wickRotate_eq_common_plus
    (d := d) (n := n) σ x]
  exact hanchor

/-- On the identity ordered Euclidean sector, the positive common-chart Wick
anchor evaluates to the reconstructed Fourier-Laplace branch `bvt_F`.

This is the Wick-anchor normalization used before the OS I common-boundary
argument.  It does not assert equality with the adjacent branch. -/
theorem os45FlatCommonChart_wickSection_plus_eq_bvt_F
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n}
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))) :
    BHW.os45FlatCommonChartBranch d n OS lgc (1 : Equiv.Perm (Fin n))
      (BHW.flattenCfg n d
        (fun k μ =>
          BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x) k μ +
            (BHW.os45HalfTimeDirection (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x k μ : ℂ) *
              Complex.I)) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  have hbase :=
    BHW.os45FlatCommonChart_wickSection_plus_eq
      (d := d) (n := n) OS lgc (1 : Equiv.Perm (Fin n)) x
  rw [hbase]
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
  have hroot :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) hx
  have hforward : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot
  exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
    hF_holo hF_lorentz (fun k => wickRotatePoint (x k)) hforward

/-- The negative real-section point in the flattened common chart evaluates to
the ordinary real branch after undoing the OS45 quarter-turn and branch label.

This is a special anchor calculation, not a boundary-value equality between
the ordinary and adjacent flat branches. -/
theorem os45FlatCommonChart_realSection_minus_eq
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (BHW.flattenCfg n d
        (fun k μ =>
          BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ x) k μ -
            (BHW.os45HalfTimeDirection (d := d) (n := n) σ x k μ : ℂ) *
              Complex.I)) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  rw [← BHW.os45QuarterTurn_perm_realEmbed_eq_common_minus
    (d := d) (n := n) σ x]
  simpa [BHW.os45FlatCommonChartBranch, BHW.unflatten_flatten_cfg] using
    BHW.os45PulledRealBranch_apply_realBranch
      (d := d) (n := n) OS lgc σ x

/-- The linear coordinate equivalence from source variables to flattened
common-edge coordinates. -/
def os45CommonEdgeFlatCLE
    (d n : ℕ) (ρperm : Equiv.Perm (Fin n)) :
    NPointDomain d n ≃L[ℝ] BHW.OS45FlatCommonChartReal d n :=
  (BHW.os45CommonEdgeRealCLE (d := d) (n := n) ρperm).trans
    (flattenCLEquivReal n (d + 1))

/-- Source-side configuration seen by a signed flat side-height point after
undoing the OS45 quarter-turn chart.

This is only the coordinate term targeted by the OS-I `(4.14)` moving
boundary-value transfer.  It does not assert any branch/source asymptotic
comparison. -/
def os45FlatCommonChartSourceSide
    (d n : ℕ) [NeZero d]
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    Fin n → Fin (d + 1) → ℂ :=
  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
    (BHW.unflattenCfg n d
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η) a : ℂ) +
          (((sgn * ε) • η) a : ℂ) * Complex.I))

/-- A signed flat side-height branch evaluation is exactly `extendF` evaluated
on the source-side configuration obtained by undoing the OS45 quarter-turn and
then applying the branch label.

This is coordinate normal form for the proof-local `(4.14)` transfer; the
analytic boundary-value limit is the next, genuinely missing, step. -/
@[simp] theorem os45FlatCommonChartBranch_sourceSide_eq_extendF
    (d n : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η) a : ℂ) +
          (((sgn * ε) • η) a : ℂ) * Complex.I) =
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) σ.symm
          (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn ε η u)) := by
  rfl

/-- The signed flat side-height point lies in a selected flat branch domain
exactly when its source-side configuration, after the branch label is applied,
lies in the extended tube.

This is the checked sheet-domain normal form used before applying the OS-I
`(4.14)` boundary-value transfer. -/
@[simp] theorem os45FlatCommonChartSourceSide_mem_extendedTube_iff
    (d n : ℕ) [NeZero d]
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η) a : ℂ) +
          (((sgn * ε) • η) a : ℂ) * Complex.I) ∈
        BHW.os45FlatCommonChartOmega d n σ ↔
      BHW.permAct (d := d) σ.symm
        (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) ∈
          BHW.ExtendedTube d n := by
  rfl

/-- Absolute Jacobian of the OS45 source-to-flat common-edge map.  The common
edge map halves the time coordinate of each source point; permutations and
flattening have absolute determinant `1`. -/
noncomputable def os45CommonEdgeFlatJacobianAbs (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

theorem os45CommonEdgeFlatJacobianAbs_pos (n : ℕ) :
    0 < BHW.os45CommonEdgeFlatJacobianAbs n := by
  dsimp [BHW.os45CommonEdgeFlatJacobianAbs]
  positivity

/-- The flat diagonal map that halves exactly the time coordinate in each
common-edge source point. -/
noncomputable def os45CommonEdgeTimeHalfFlatLinearMap (d n : ℕ) :
    BHW.OS45FlatCommonChartReal d n →ₗ[ℝ]
      BHW.OS45FlatCommonChartReal d n :=
  Matrix.toLin' (Matrix.diagonal
    (fun a : Fin (BHW.os45FlatCommonChartDim d n) =>
      if (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
      then (1 / 2 : ℝ) else 1))

@[simp] theorem os45CommonEdgeTimeHalfFlatLinearMap_apply
    (d n : ℕ)
    (y : BHW.OS45FlatCommonChartReal d n)
    (a : Fin (BHW.os45FlatCommonChartDim d n)) :
    BHW.os45CommonEdgeTimeHalfFlatLinearMap d n y a =
      (if (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
      then (1 / 2 : ℝ) * y a else y a) := by
  simp [BHW.os45CommonEdgeTimeHalfFlatLinearMap, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal]

/-- The determinant of the flat common-edge time-halving map is `(1 / 2)^n`:
one halved time coordinate for each source point, and all spatial coordinates
unchanged. -/
theorem os45CommonEdgeTimeHalfFlatLinearMap_det (d n : ℕ) :
    LinearMap.det (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n) =
      (1 / 2 : ℝ) ^ n := by
  dsimp [BHW.os45CommonEdgeTimeHalfFlatLinearMap]
  rw [LinearMap.det_toLin', Matrix.det_diagonal]
  calc
    (∏ a : Fin (BHW.os45FlatCommonChartDim d n),
      (if (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
      then (1 / 2 : ℝ) else 1))
        = ∏ p : Fin n × Fin (d + 1),
            (if p.2 = (0 : Fin (d + 1)) then (1 / 2 : ℝ) else 1) := by
          rw [← Equiv.prod_comp finProdFinEquiv]
          simp
    _ = ∏ _k : Fin n, ∏ μ : Fin (d + 1),
            (if μ = (0 : Fin (d + 1)) then (1 / 2 : ℝ) else 1) := by
          simp [Fintype.prod_prod_type]
    _ = ∏ _k : Fin n, (1 / 2 : ℝ) := by
          congr
          ext k
          rw [Fin.prod_univ_succ]
          simp
    _ = (1 / 2 : ℝ) ^ n := by
          simp

/-- Change of variables for the flat time-halving map. -/
theorem os45CommonEdgeTimeHalfFlat_integral_comp
    (d n : ℕ)
    (g : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hg : Integrable g) :
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x =
      ((1 / 2 : ℝ) ^ n : ℂ) *
        ∫ y : BHW.OS45FlatCommonChartReal d n,
          g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n y) := by
  let L := BHW.os45CommonEdgeTimeHalfFlatLinearMap d n
  let J : ℝ := (1 / 2 : ℝ) ^ n
  have hJ_pos : 0 < J := by
    dsimp [J]
    positivity
  have hJ_ne : J ≠ 0 := ne_of_gt hJ_pos
  have hdet_ne : LinearMap.det L ≠ 0 := by
    rw [show LinearMap.det L = J by
      simpa [L, J] using
        BHW.os45CommonEdgeTimeHalfFlatLinearMap_det d n]
    exact hJ_ne
  have hmap :
      Measure.map L
          (volume : Measure (BHW.OS45FlatCommonChartReal d n)) =
        ENNReal.ofReal (J⁻¹) • volume := by
    have hraw :=
      Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := L) hdet_ne
    rw [hraw]
    congr 1
    rw [show LinearMap.det L = J by
      simpa [L, J] using
        BHW.os45CommonEdgeTimeHalfFlatLinearMap_det d n]
    rw [abs_of_pos (inv_pos.mpr hJ_pos)]
  have hg_map : AEStronglyMeasurable g
      (Measure.map L
        (volume : Measure (BHW.OS45FlatCommonChartReal d n))) := by
    rw [hmap]
    exact hg.aestronglyMeasurable.mono_ac
      Measure.smul_absolutelyContinuous
  have hmap_int :
      ∫ y : BHW.OS45FlatCommonChartReal d n, g (L y) =
        ∫ x : BHW.OS45FlatCommonChartReal d n, g x ∂
          (Measure.map L
            (volume : Measure (BHW.OS45FlatCommonChartReal d n))) := by
    exact
      (MeasureTheory.integral_map
        (LinearMap.continuous_of_finiteDimensional L).measurable.aemeasurable
        hg_map).symm
  have hscale :
      ∫ y : BHW.OS45FlatCommonChartReal d n, g (L y) =
        ((J : ℂ)⁻¹) *
          ∫ x : BHW.OS45FlatCommonChartReal d n, g x := by
    calc
      ∫ y : BHW.OS45FlatCommonChartReal d n, g (L y)
          = ∫ x : BHW.OS45FlatCommonChartReal d n, g x ∂
              (Measure.map L
                (volume : Measure (BHW.OS45FlatCommonChartReal d n))) := hmap_int
      _ = ∫ x : BHW.OS45FlatCommonChartReal d n, g x ∂
              (ENNReal.ofReal (J⁻¹) • volume) := by rw [hmap]
      _ = (ENNReal.ofReal (J⁻¹)).toReal •
              ∫ x : BHW.OS45FlatCommonChartReal d n, g x := by
            rw [integral_smul_measure]
            rfl
      _ = ((J : ℂ)⁻¹) *
              ∫ x : BHW.OS45FlatCommonChartReal d n, g x := by
            have hJinv_nonneg : 0 ≤ J⁻¹ :=
              le_of_lt (inv_pos.mpr hJ_pos)
            rw [ENNReal.toReal_ofReal hJinv_nonneg]
            simp [Complex.real_smul]
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x
        = (J : ℂ) * (((J : ℂ)⁻¹) *
            ∫ x : BHW.OS45FlatCommonChartReal d n, g x) := by
          field_simp [show (J : ℂ) ≠ 0 by exact_mod_cast hJ_ne]
    _ = (J : ℂ) *
          ∫ y : BHW.OS45FlatCommonChartReal d n, g (L y) := by
        rw [hscale]
    _ = ((1 / 2 : ℝ) ^ n : ℂ) *
          ∫ y : BHW.OS45FlatCommonChartReal d n,
            g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n y) := by
        simp [J, L]

/-- Reindexing source point labels by a permutation preserves the source
Lebesgue integral. -/
theorem integral_nPoint_perm_eq
    (d n : ℕ) (ρperm : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ y : NPointDomain d n, h y =
      ∫ x : NPointDomain d n, h (fun k μ => x (ρperm k) μ) := by
  let e : (Fin n → SpacetimeDim d) ≃ᵐ
      (Fin n → SpacetimeDim d) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin n => SpacetimeDim d) ρperm.symm
  have heq : (e : (Fin n → SpacetimeDim d) →
      (Fin n → SpacetimeDim d)) =
      (fun x : NPointDomain d n => fun k : Fin n => x (ρperm k)) := by
    funext x k μ
    let x' : (a : Fin n) →
        (fun _ : Fin n => SpacetimeDim d) (ρperm.symm a) := x
    have hk :=
      Equiv.piCongrLeft_apply
        (P := fun _ : Fin n => SpacetimeDim d)
        (e := ρperm.symm) x' k
    simpa [e] using congr_fun hk μ
  have hmp :=
    MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => SpacetimeDim d) ρperm.symm
  exact
    (by
      simpa [heq] using (hmp.integral_comp' (f := e) h).symm)

/-- Change of variables for the source-to-flat common-edge coordinate map. -/
theorem os45CommonEdgeFlatCLE_integral_comp
    (d n : ℕ) (ρperm : Equiv.Perm (Fin n))
    (g : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hg : Integrable g) :
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          g (BHW.os45CommonEdgeFlatCLE d n ρperm u) := by
  have hhalf :=
    BHW.os45CommonEdgeTimeHalfFlat_integral_comp d n g hg
  have hflat :=
    integral_flatten_change_of_variables n (d + 1)
      (fun y : BHW.OS45FlatCommonChartReal d n =>
        g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n y))
  have hperm :=
    BHW.integral_nPoint_perm_eq d n ρperm
      (fun y : NPointDomain d n =>
        g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n
          (flattenCLEquivReal n (d + 1) y)))
  have hpoint :
      (fun y : NPointDomain d n =>
        g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n
          (flattenCLEquivReal n (d + 1) y))) ∘
        (fun x : NPointDomain d n => fun k μ => x (ρperm k) μ) =
      fun x : NPointDomain d n =>
        g (BHW.os45CommonEdgeFlatCLE d n ρperm x) := by
    funext x
    have hxcoord :
        BHW.os45CommonEdgeTimeHalfFlatLinearMap d n
          (flattenCLEquivReal n (d + 1)
            (fun k μ => x (ρperm k) μ)) =
        BHW.os45CommonEdgeFlatCLE d n ρperm x := by
      ext a
      by_cases h0 : a.modNat = (0 : Fin (d + 1))
      · simp [BHW.os45CommonEdgeFlatCLE,
          BHW.os45CommonEdgeTimeHalfFlatLinearMap,
          BHW.os45FlatCommonChartDim, Matrix.toLin'_apply,
          Matrix.mulVec_diagonal, BHW.os45CommonEdgeRealPoint,
          div_eq_mul_inv, h0, mul_comm]
      · simp [BHW.os45CommonEdgeFlatCLE,
          BHW.os45CommonEdgeTimeHalfFlatLinearMap,
          BHW.os45FlatCommonChartDim, Matrix.toLin'_apply,
          Matrix.mulVec_diagonal, BHW.os45CommonEdgeRealPoint,
          div_eq_mul_inv, h0]
    simp [hxcoord]
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x
        = ((1 / 2 : ℝ) ^ n : ℂ) *
            ∫ y : BHW.OS45FlatCommonChartReal d n,
              g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n y) := hhalf
    _ = ((1 / 2 : ℝ) ^ n : ℂ) *
            ∫ y : NPointDomain d n,
              g (BHW.os45CommonEdgeTimeHalfFlatLinearMap d n
                (flattenCLEquivReal n (d + 1) y)) := by
          rw [hflat]
    _ = ((1 / 2 : ℝ) ^ n : ℂ) *
            ∫ x : NPointDomain d n,
              g (BHW.os45CommonEdgeFlatCLE d n ρperm x) := by
          rw [hperm]
          simp [Function.comp_def] at hpoint
          rw [hpoint]
    _ = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
            ∫ x : NPointDomain d n,
              g (BHW.os45CommonEdgeFlatCLE d n ρperm x) := by
          simp [BHW.os45CommonEdgeFlatJacobianAbs]

/-- Change of variables for the source-to-flat common-edge coordinate map after
a real translation in flat coordinates. -/
theorem os45CommonEdgeFlatCLE_integral_comp_shift
    (d n : ℕ) (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n)
    (g : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n => g (x + a))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          g (BHW.os45CommonEdgeFlatCLE d n ρperm u + a) := by
  have htranslate :
      ∫ x : BHW.OS45FlatCommonChartReal d n, g x =
        ∫ x : BHW.OS45FlatCommonChartReal d n, g (x + a) :=
    (MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (BHW.OS45FlatCommonChartReal d n))) g a).symm
  have hflat :=
    BHW.os45CommonEdgeFlatCLE_integral_comp d n ρperm
      (fun x : BHW.OS45FlatCommonChartReal d n => g (x + a)) hg_shift
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n, g x
        = ∫ x : BHW.OS45FlatCommonChartReal d n, g (x + a) := htranslate
    _ = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
          ∫ u : NPointDomain d n,
            g (BHW.os45CommonEdgeFlatCLE d n ρperm u + a) := hflat

/-- Translated source-to-flat change of variables for one flat branch with an
independent imaginary side shift.

This is the pure coordinate/Jacobian part of the side-height Figure-2-4
transfer.  It does not identify the branch with a Wick-section boundary value;
that is the separate OS I `(4.14)` boundary-value leaf. -/
theorem os45FlatCommonChart_branch_integral_eq_sourcePullback_shift
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (a b : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) *
          φ (x + a))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (b j : ℂ) * Complex.I) * φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((BHW.os45CommonEdgeFlatCLE d n ρperm u + a) j : ℂ) +
                (b j : ℂ) * Complex.I) *
            φ (BHW.os45CommonEdgeFlatCLE d n ρperm u + a) := by
  let g : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (fun j => (x j : ℂ) + (b j : ℂ) * Complex.I) * φ x
  have hcov :=
    BHW.os45CommonEdgeFlatCLE_integral_comp_shift d n ρperm a g hg_shift
  simpa [g] using hcov

/-- Compact support plus side-domain membership gives integrability of the
translated flat branch integrand.

This supplies the regularity input used by the side-height source pullback
lemmas.  The side-domain hypothesis is exactly the local wedge/domain check;
no boundary-value or Wick-normalization statement is used here. -/
theorem os45FlatCommonChart_branch_shifted_mul_integrable
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n))
    (a b : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hΩ :
      tsupport (SCV.translateSchwartz a φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        {x | (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) ∈
          BHW.os45FlatCommonChartOmega d n σ}) :
    Integrable
      (fun x : BHW.OS45FlatCommonChartReal d n =>
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) *
        φ (x + a)) := by
  let U : Set (BHW.OS45FlatCommonChartReal d n) :=
    {x | (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) ∈
      BHW.os45FlatCommonChartOmega d n σ}
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I)
  have hmap : Continuous
      (fun x : BHW.OS45FlatCommonChartReal d n =>
        fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) := by
    fun_prop
  have hU_open : IsOpen U := by
    simpa [U] using
      (BHW.isOpen_os45FlatCommonChartOmega d n σ).preimage hmap
  have hH_cont : ContinuousOn H U := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc σ).continuousOn.comp
        hmap.continuousOn
        (by intro x hx; simpa [U] using hx)
  have hχ_cont : Continuous
      (fun x : BHW.OS45FlatCommonChartReal d n => φ (x + a)) :=
    φ.continuous.comp (continuous_id.add continuous_const)
  have hχ_support :
      tsupport (fun x : BHW.OS45FlatCommonChartReal d n => φ (x + a)) ⊆ U := by
    simpa [U, SCV.translateSchwartz_apply] using hΩ
  have hχ_compact : HasCompactSupport
      (fun x : BHW.OS45FlatCommonChartReal d n => φ (x + a)) := by
    simpa [Function.comp] using
      hφ_compact.comp_homeomorph (Homeomorph.addRight a)
  have hχH_cont : Continuous
      (fun x : BHW.OS45FlatCommonChartReal d n => φ (x + a) * H x) :=
    SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
      hU_open hχ_cont hχ_support hH_cont
  have hHχ_cont : Continuous
      (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ (x + a)) := by
    simpa [mul_comm] using hχH_cont
  have hHχ_compact : HasCompactSupport
      (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ (x + a)) := by
    refine hχ_compact.mono' ?_
    intro x hx
    by_contra hxχ
    have hχx : φ (x + a) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : BHW.OS45FlatCommonChartReal d n => φ (y + a)) hxχ
    exact hx (by simp [hχx])
  exact hHχ_cont.integrable_of_hasCompactSupport hHχ_compact

/-- Unflattening the complexification of a flattened real configuration
recovers its standard complex real embedding. -/
@[simp] theorem unflattenCfg_ofReal_flattenCfgReal
    (n d : ℕ) (x : Fin n → Fin (d + 1) → ℝ) :
    BHW.unflattenCfg n d
      (fun a => (BHW.flattenCfgReal n d x a : ℂ)) =
      BHW.realEmbed x := by
  funext k μ
  simp [BHW.unflattenCfg, BHW.flattenCfgReal, BHW.realEmbed]

/-- In flattened coordinates, evaluating a flat branch on the linear common-edge
image is the same as evaluating the pulled source branch on the corresponding
real embedded common-edge point. -/
@[simp] theorem os45FlatCommonChartBranch_real_commonEdgeFlatCLE
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (fun a => (BHW.os45CommonEdgeFlatCLE d n ρperm x a : ℂ)) =
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc σ
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x)) := by
  rw [BHW.os45FlatCommonChartBranch]
  have harg :
      (fun a =>
        (BHW.os45CommonEdgeFlatCLE d n ρperm x a : ℂ)) =
        fun a =>
          (BHW.flattenCfgReal n d
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm x) a : ℂ) := by
    ext a
    simp [BHW.os45CommonEdgeFlatCLE, BHW.os45FlatCommonChartDim,
      BHW.flattenCfgReal]
  rw [harg, BHW.unflattenCfg_ofReal_flattenCfgReal]

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

/-- The zero of a flat local EOW chart pulls back to the horizontal
common-edge `S'_n` seed. -/
theorem os45Figure24CommonEdgeSPrimeSeed_eq_chart_zero
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {ys : Fin (BHW.os45FlatCommonChartDim d n) →
        Fin (BHW.os45FlatCommonChartDim d n) → ℝ} :
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.unflattenCfg n d
        (SCV.localEOWChart
          (BHW.os45FlatCommonChartSeed d n P
            (1 : Equiv.Perm (Fin n))) ys 0)) =
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P := by
  have hunflatten :
      BHW.unflattenCfg n d
        (SCV.realEmbed
          (BHW.flattenCfgReal n d
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) P.xseed))) =
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) P.xseed) := by
    funext k μ
    simp [BHW.unflattenCfg, BHW.flattenCfgReal, BHW.realEmbed,
      SCV.realEmbed]
  simp [BHW.os45Figure24CommonEdgeSPrimeSeed,
    BHW.os45FlatCommonChartSeed, SCV.localEOWChart_zero,
    hunflatten]

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

/-- Real points of the Figure-2-4 flattened common edge lie in the ordinary
flat branch domain. -/
theorem os45FlatCommonChart_real_mem_omega_id
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    ∀ x ∈
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)),
      (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases hy with ⟨u, hu, rfl⟩
  change BHW.unflattenCfg n d
      (fun a => (BHW.flattenCfgReal n d
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u) a : ℂ)) ∈
    BHW.os45PulledRealBranchDomain (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
  exact P.V_pulled_id u hu

/-- Real points of the Figure-2-4 flattened common edge lie in the adjacent
flat branch domain. -/
theorem os45FlatCommonChart_real_mem_omega_adjacent
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    ∀ x ∈
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)),
      (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
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

/-- Smooth compact-support cutoff adapted to the Figure-2-4 source patch. -/
structure OS45Figure24SourceCutoffData
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) where
  χ : NPointDomain d n → ℂ
  χ_temperate : Function.HasTemperateGrowth χ
  χ_compact : HasCompactSupport χ
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
       χ_compact := hχ_compact
       χ_eq_one_on_V := hχ_one_on_V
       tsupport_subset_Ufig := htsupport_subset_Ufig }⟩

/-- Ordinary common-edge multiplier in the flattened Figure-2-4 real chart. -/
noncomputable def os45FlatCommonChart_ordinaryEdgeMultiplier
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    BHW.OS45FlatCommonChartReal d n → ℂ :=
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData P)
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  fun x =>
    D.χ (e.symm x) *
      BHW.os45FlatCommonChartBranch d n OS lgc (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ))

/-- The ordinary common-edge multiplier is continuous. -/
theorem continuous_os45FlatCommonChart_ordinaryEdgeMultiplier
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    Continuous
      (BHW.os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P) := by
  classical
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData P)
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let χflat : BHW.OS45FlatCommonChartReal d n → ℂ := fun x => D.χ (e.symm x)
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc (1 : Equiv.Perm (Fin n))
      (fun a => (x a : ℂ))
  have hχ_cont : Continuous χflat := by
    dsimp [χflat]
    exact D.χ_temperate.1.continuous.comp e.symm.continuous
  have hU_open : IsOpen (e '' P.Ufig) := by
    simpa using e.toHomeomorph.isOpenMap P.Ufig P.Ufig_open
  have hχ_support : tsupport χflat ⊆ e '' P.Ufig := by
    intro x hx
    have hxpre : e.symm x ∈ tsupport D.χ := by
      exact (tsupport_comp_subset_preimage D.χ e.symm.continuous) hx
    exact ⟨e.symm x, D.tsupport_subset_Ufig hxpre, by simp [e]⟩
  have hmem : ∀ x ∈ e '' P.Ufig,
      (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    change BHW.unflattenCfg n d
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))
    rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
    exact P.Ufig_pulled_id u hu
  have hH_cont : ContinuousOn H (e '' P.Ufig) := by
    dsimp [H]
    have hreal :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            fun a => (x a : ℂ)) :=
      continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
        hreal.continuousOn hmem
  simpa [BHW.os45FlatCommonChart_ordinaryEdgeMultiplier, D, e, χflat, H] using
    SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
      hU_open hχ_cont hχ_support hH_cont

/-- The ordinary common-edge multiplier has compact support. -/
theorem hasCompactSupport_os45FlatCommonChart_ordinaryEdgeMultiplier
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    HasCompactSupport
      (BHW.os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P) := by
  classical
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData P)
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let χflat : BHW.OS45FlatCommonChartReal d n → ℂ := fun x => D.χ (e.symm x)
  have hχ_compact : HasCompactSupport χflat := by
    dsimp [χflat]
    simpa [Function.comp_def] using
      D.χ_compact.comp_homeomorph e.symm.toHomeomorph
  refine HasCompactSupport.of_support_subset_isCompact hχ_compact.isCompact ?_
  intro x hx
  by_contra hxχ
  have hxχ_support : x ∉ Function.support χflat := by
    intro hxsupp
    exact hxχ (subset_tsupport χflat hxsupp)
  have hχx : χflat x = 0 := by
    simpa [Function.mem_support] using hxχ_support
  exact hx (by simp [BHW.os45FlatCommonChart_ordinaryEdgeMultiplier, D, e,
    χflat, hχx])

/-- Compactly supported ordinary common-edge CLM in the flattened Figure-2-4
real chart.  This is the flat-coordinate version of the source-pulled integral;
the source Jacobian only appears when changing variables back to source tests. -/
noncomputable def os45FlatCommonChart_ordinaryEdgeCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
  Classical.choose
    (SCV.compactSupport_integralMultiplierCLM_fin
      (m := BHW.os45FlatCommonChartDim d n)
      (BHW.os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P)
      (BHW.continuous_os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P)
      (BHW.hasCompactSupport_os45FlatCommonChart_ordinaryEdgeMultiplier
        hd OS lgc P))

/-- Pointwise formula for the ordinary edge CLM. -/
theorem os45FlatCommonChart_ordinaryEdgeCLM_apply
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ) :
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ =
      ∫ x, BHW.os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P x *
        φ x := by
  exact
    Classical.choose_spec
      (SCV.compactSupport_integralMultiplierCLM_fin
        (m := BHW.os45FlatCommonChartDim d n)
        (BHW.os45FlatCommonChart_ordinaryEdgeMultiplier hd OS lgc P)
        (BHW.continuous_os45FlatCommonChart_ordinaryEdgeMultiplier
          hd OS lgc P)
        (BHW.hasCompactSupport_os45FlatCommonChart_ordinaryEdgeMultiplier
          hd OS lgc P)) φ

/-- The ordinary zero-height branch locally represents the ordinary edge CLM
on the Figure-2-4 real common chart. -/
theorem os45FlatCommonChart_ordinaryEdgeCLM_represents
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : Nat} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi} :
    ∀ x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)),
      ∃ U : Set (BHW.OS45FlatCommonChartReal d n),
        IsOpen U ∧ x0 ∈ U ∧
        ContinuousOn
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a => (x a : ℂ))) U ∧
        SCV.RepresentsDistributionOn
          (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a => (x a : ℂ)))
          U := by
  intro x0 hx0
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let U : Set (BHW.OS45FlatCommonChartReal d n) := e '' P.V
  have hx0U : x0 ∈ U := by
    rcases hx0 with ⟨y, hy, rfl⟩
    rcases hy with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  have hU_open : IsOpen U := by
    dsimp [U]
    simpa using e.toHomeomorph.isOpenMap P.V P.V_open
  have hmem : ∀ x ∈ U,
      (fun a => (x a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d n (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    change BHW.unflattenCfg n d
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))
    rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
    exact P.V_pulled_id u hu
  have hcont : ContinuousOn
      (fun x : BHW.OS45FlatCommonChartReal d n =>
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)) (fun a => (x a : ℂ))) U := by
    have hreal :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            fun a => (x a : ℂ)) :=
      continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
        hreal.continuousOn hmem
  refine ⟨U, hU_open, hx0U, hcont, ?_⟩
  intro φ hφ
  rw [BHW.os45FlatCommonChart_ordinaryEdgeCLM_apply hd OS lgc P φ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hxU : x ∈ U
  · rcases hxU with ⟨u, hu, rfl⟩
    have hχ :
        (Classical.choice (BHW.exists_os45Figure24SourceCutoffData P)).χ u =
          1 :=
      (Classical.choice
        (BHW.exists_os45Figure24SourceCutoffData P)).χ_eq_one_on_V u hu
    simp [BHW.os45FlatCommonChart_ordinaryEdgeMultiplier, e, hχ]
  · have hx_not_ts :
        x ∉ tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) := by
      intro hx
      exact hxU (hφ.2 hx)
    have hx_not_support :
        x ∉ Function.support
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) := by
      intro hsupp
      exact hx_not_ts (subset_tsupport _ hsupp)
    have hφx : φ x = 0 := by
      simpa [Function.mem_support] using hx_not_support
    simp [hφx]

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

/-- Pointwise formula for the source test obtained by pulling a flat common-chart
Schwartz test back through the common-edge map and multiplying by the source
cutoff. -/
@[simp] theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_apply
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (x : NPointDomain d n) :
    (D.toSchwartzNPointCLM ρperm φ : NPointDomain d n → ℂ) x =
      D.χ x * φ (BHW.os45CommonEdgeFlatCLE d n ρperm x) := by
  simp [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
    SchwartzMap.smulLeftCLM_apply_apply D.χ_temperate,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

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

/-- The cutoff-pulled common-chart tests have compact support in source
coordinates. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_hasCompactSupport
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ) :
    HasCompactSupport
      (D.toSchwartzNPointCLM ρperm φ : NPointDomain d n → ℂ) := by
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (BHW.os45CommonEdgeFlatCLE d n ρperm)) φ)
  refine HasCompactSupport.of_support_subset_isCompact D.χ_compact.isCompact ?_
  intro x hx
  have hx_ts :
      x ∈ tsupport
        (D.toSchwartzNPointCLM ρperm φ : NPointDomain d n → ℂ) :=
    subset_tsupport _ hx
  exact
    (by
      simpa [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM] using
        (hsupport hx_ts).2)

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

/-- If the flat test is supported on the flattened common edge, then the
cutoff-pulled source test is supported in the original source slice. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_tsupport_subset_V
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm) :
    tsupport (D.toSchwartzNPointCLM ρperm φ :
      NPointDomain d n → ℂ) ⊆ P.V := by
  intro x hx
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ := φ
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ)
  have hx_smul :
      x ∈ tsupport
        (SchwartzMap.smulLeftCLM ℂ D.χ
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ) :
          NPointDomain d n → ℂ) := by
    simpa [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
      e, ψ] using hx
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
      e x ∈ tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) := by
    simpa [ψ] using hcomp_support hx_comp'
  exact
    (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P ρperm x).mp
      (hφE hx_flat)

/-- If a flat common-chart test is supported in the linear image of a local
source neighborhood, then its cutoff-pulled source test is supported in that
same source neighborhood. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_tsupport_subset_image
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    {U : Set (NPointDomain d n)}
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n ρperm '' U) :
    tsupport (D.toSchwartzNPointCLM ρperm φ :
      NPointDomain d n → ℂ) ⊆ U := by
  intro x hx
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ := φ
  have hsupport :=
    SchwartzMap.tsupport_smulLeftCLM_subset D.χ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ)
  have hx_smul :
      x ∈ tsupport
        (SchwartzMap.smulLeftCLM ℂ D.χ
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ) :
          NPointDomain d n → ℂ) := by
    simpa [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
      e, ψ] using hx
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
      e x ∈ tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) := by
    simpa [ψ] using hcomp_support hx_comp'
  rcases hφU hx_flat with ⟨u, huU, hu_eq⟩
  have hx_eq : x = u := e.injective hu_eq.symm
  simpa [hx_eq] using huU

/-- Shifted flat tests supported in the image of a local source neighborhood
pull back to source tests supported in that same neighborhood. -/
theorem OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_tsupport_subset_image
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (a : BHW.OS45FlatCommonChartReal d n)
    {U : Set (NPointDomain d n)}
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφU :
      tsupport (SCV.translateSchwartz a φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n ρperm '' U) :
    tsupport (D.toShiftedSchwartzNPointCLM ρperm a φ :
      NPointDomain d n → ℂ) ⊆ U := by
  simpa [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using
    D.toSchwartzNPointCLM_tsupport_subset_image ρperm
      (SCV.translateSchwartzCLM a φ) hφU

/-- On flat tests whose topological support is contained in the flattened common
edge, the source cutoff is invisible after pullback. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (x : NPointDomain d n) :
    (D.toSchwartzNPointCLM ρperm φ : NPointDomain d n → ℂ) x =
      φ (BHW.os45CommonEdgeFlatCLE d n ρperm x) := by
  by_cases hxφ : BHW.os45CommonEdgeFlatCLE d n ρperm x ∈
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
  · have hxV : x ∈ P.V :=
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P ρperm x).mp
        (hφE hxφ)
    simp [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
      SchwartzMap.smulLeftCLM_apply_apply D.χ_temperate,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      D.χ_eq_one_on_V x hxV]
  · have hzero :
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm x) = 0 :=
      image_eq_zero_of_notMem_tsupport hxφ
    simp [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM,
      SchwartzMap.smulLeftCLM_apply_apply D.χ_temperate,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hzero]

/-- On shifted flat tests whose topological support remains in the flattened
common edge, the source cutoff is again invisible after pullback. -/
theorem OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
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
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (x : NPointDomain d n) :
    (D.toShiftedSchwartzNPointCLM ρperm a φ :
      NPointDomain d n → ℂ) x =
      φ (BHW.os45CommonEdgeFlatCLE d n ρperm x + a) := by
  have hplain :=
    D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge ρperm
      (SCV.translateSchwartzCLM a φ)
      (by
        simpa [SCV.translateSchwartzCLM_apply] using hφE) x
  simpa [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply,
    SCV.translateSchwartz_apply] using hplain

/-- Translated branch integral written against the shifted source test after
the Figure-2-4 cutoff has been removed by the shifted support hypothesis.

This closes the coordinate/cutoff part of the side-height pullback: the only
remaining analytic input for the E-to-R transfer is the OS I `(4.14)`
boundary-value comparison for the moving source test. -/
theorem os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM
    [NeZero d] {hd : 2 ≤ d}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (σ ρperm : Equiv.Perm (Fin n))
    (a b : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (SCV.translateSchwartz a φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j => ((x + a) j : ℂ) + (b j : ℂ) * Complex.I) *
          φ (x + a))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (b j : ℂ) * Complex.I) * φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((BHW.os45CommonEdgeFlatCLE d n ρperm u + a) j : ℂ) +
                (b j : ℂ) * Complex.I) *
            (D.toShiftedSchwartzNPointCLM ρperm a φ :
              NPointDomain d n → ℂ) u := by
  have hcov :=
    BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift
      (d := d) (n := n) OS lgc σ ρperm a b φ hg_shift
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (b j : ℂ) * Complex.I) * φ x
        = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
          ∫ u : NPointDomain d n,
            BHW.os45FlatCommonChartBranch d n OS lgc σ
              (fun j =>
                ((BHW.os45CommonEdgeFlatCLE d n ρperm u + a) j : ℂ) +
                  (b j : ℂ) * Complex.I) *
              φ (BHW.os45CommonEdgeFlatCLE d n ρperm u + a) := hcov
    _ = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
          ∫ u : NPointDomain d n,
            BHW.os45FlatCommonChartBranch d n OS lgc σ
              (fun j =>
                ((BHW.os45CommonEdgeFlatCLE d n ρperm u + a) j : ℂ) +
                  (b j : ℂ) * Complex.I) *
              (D.toShiftedSchwartzNPointCLM ρperm a φ :
                NPointDomain d n → ℂ) u := by
        congr 1
        apply integral_congr_ae
        filter_upwards with u
        have hplain :=
          D.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
            ρperm a φ hφE u
        rw [← hplain]

/-- Pointwise integrand identity that converts the flat ordinary-minus-adjacent
common-boundary difference into the source common-edge branch difference, after
the cutoff has been removed by the flat support hypothesis. -/
theorem os45FlatCommonChart_commonBoundaryDifference_sourceIntegrand_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (u : NPointDomain d n) :
    (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a =>
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u a : ℂ)) -
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a =>
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u a : ℂ))) *
      φ (BHW.os45CommonEdgeFlatCLE d n
        (1 : Equiv.Perm (Fin n)) u) =
    (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) -
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))) *
      (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
        NPointDomain d n → ℂ) u := by
  rw [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge D
    (1 : Equiv.Perm (Fin n)) φ hφE u]
  simp

/-- Pointwise integrand identity for the ordinary horizontal common-edge
branch alone, after the source cutoff has been removed by the flat support
hypothesis. -/
theorem os45FlatCommonChart_ordinaryCommonBoundary_sourceIntegrand_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a =>
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u a : ℂ)) *
      φ (BHW.os45CommonEdgeFlatCLE d n
        (1 : Equiv.Perm (Fin n)) u) =
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) *
      (D.toSchwartzNPointCLM
        (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
  rw [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge D
    (1 : Equiv.Perm (Fin n)) φ hφE u]
  simp

/-- Common-edge change of variables for the ordinary flat boundary branch
alone.  The right-hand side is in source common-edge variables, with the
Figure-2-4 cutoff removed by the flat support hypothesis. -/
theorem os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ)) * φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
  classical
  let E : Set (BHW.OS45FlatCommonChartReal d n) :=
    BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : ℂ))
  have hreal :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          fun a => (x a : ℂ)) :=
    continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
  have hH_cont : ContinuousOn H E := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
        hreal.continuousOn
        (by
          simpa [E] using
            (BHW.os45FlatCommonChart_real_mem_omega_id
              (d := d) hd (P := P)))
  have hg_cont :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    have hφH :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n => φ x * H x) :=
      SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
        (by
          simpa [E] using
            (BHW.isOpen_os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n))))
        φ.continuous
        (by
          simpa [E] using hφE)
        hH_cont
    simpa [mul_comm] using hφH
  have hg_compact :
      HasCompactSupport
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    refine hφ_compact.mono' ?_
    intro x hx
    by_contra hxφ
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
    exact hx (by simp [hφx])
  have hg_int :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hcov :=
    BHW.os45CommonEdgeFlatCLE_integral_comp d n
      (1 : Equiv.Perm (Fin n))
      (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x)
      hg_int
  simpa [H] using
    hcov.trans
      (congrArg
        (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
        (integral_congr_ae
          (Eventually.of_forall fun u =>
            BHW.os45FlatCommonChart_ordinaryCommonBoundary_sourceIntegrand_eq
              (d := d) hd OS lgc D φ hφE u)))

/-- Pointwise integrand identity for the selected adjacent horizontal
common-edge branch alone, after the source cutoff has been removed by the flat
support hypothesis. -/
theorem os45FlatCommonChart_adjacentCommonBoundary_sourceIntegrand_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a =>
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u a : ℂ)) *
      φ (BHW.os45CommonEdgeFlatCLE d n
        (1 : Equiv.Perm (Fin n)) u) =
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) *
      (D.toSchwartzNPointCLM
        (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
  rw [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge D
    (1 : Equiv.Perm (Fin n)) φ hφE u]
  simp

/-- Common-edge change of variables for the selected adjacent flat boundary
branch alone.  The right-hand side is in source common-edge variables, with the
Figure-2-4 cutoff removed by the flat support hypothesis. -/
theorem os45FlatCommonChart_adjacentCommonBoundary_integral_eq_sourcePullback
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ)) * φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
  classical
  let E : Set (BHW.OS45FlatCommonChartReal d n) :=
    BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : ℂ))
  have hreal :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          fun a => (x a : ℂ)) :=
    continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
  have hH_cont : ContinuousOn H E := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn.comp
        hreal.continuousOn
        (by
          simpa [E] using
            (BHW.os45FlatCommonChart_real_mem_omega_adjacent
              (d := d) hd (P := P)))
  have hg_cont :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    have hφH :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n => φ x * H x) :=
      SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
        (by
          simpa [E] using
            (BHW.isOpen_os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n))))
        φ.continuous
        (by
          simpa [E] using hφE)
        hH_cont
    simpa [mul_comm] using hφH
  have hg_compact :
      HasCompactSupport
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    refine hφ_compact.mono' ?_
    intro x hx
    by_contra hxφ
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
    exact hx (by simp [hφx])
  have hg_int :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hcov :=
    BHW.os45CommonEdgeFlatCLE_integral_comp d n
      (1 : Equiv.Perm (Fin n))
      (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x)
      hg_int
  simpa [H] using
    hcov.trans
      (congrArg
        (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
        (integral_congr_ae
          (Eventually.of_forall fun u =>
            BHW.os45FlatCommonChart_adjacentCommonBoundary_sourceIntegrand_eq
              (d := d) hd OS lgc D φ hφE u)))

/-- A pointwise source common-edge equality on a local Figure-2-4 source
window gives the corresponding zero-height flat compact-test equality on the
flattened image of that window.

This is the non-circular source-to-flat consumer for the eventual OS I
`h45_source_eqOn` step: it does not assume a common-boundary CLM, `Hdiff`, or a
local `S'_n` branch. -/
theorem os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V)
    (hsource_eq :
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
                (1 : Equiv.Perm (Fin n)) u)))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U) :
    (∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ)) * φ x) =
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x := by
  classical
  have hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hφU hx with ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hsource_support :
      tsupport
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) ⊆ U :=
    D.toSchwartzNPointCLM_tsupport_subset_image
      (1 : Equiv.Perm (Fin n)) φ hφU
  have hAdj :=
    BHW.os45FlatCommonChart_adjacentCommonBoundary_integral_eq_sourcePullback
      (d := d) hd OS lgc D φ hφ_compact hφE
  have hOrd :=
    BHW.os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback
      (d := d) hd OS lgc D φ hφ_compact hφE
  have hsource_integrals :
      (∫ u : NPointDomain d n,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) *
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u) =
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu :
        u ∈ tsupport
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ)
    · rw [hsource_eq u (hsource_support hu)]
    · have hzero :
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u = 0 :=
        image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x
        =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := hAdj
    _ =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
        rw [hsource_integrals]
    _ =
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x := hOrd.symm

/-- Common-edge change of variables for the ordinary-minus-adjacent flat
boundary difference.  The right-hand side is now entirely in the source
common-edge variables, with the Figure-2-4 cutoff removed by the flat support
hypothesis. -/
theorem os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ))) * φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) -
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
  classical
  let E : Set (BHW.OS45FlatCommonChartReal d n) :=
    BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : ℂ)) -
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : ℂ))
  have hreal :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          fun a => (x a : ℂ)) :=
    continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
  have hH_cont : ContinuousOn H E := by
    have hplus :
        ContinuousOn
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun a => (x a : ℂ))) E :=
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn.comp
        hreal.continuousOn
        (by
          simpa [E] using
            (BHW.os45FlatCommonChart_real_mem_omega_adjacent
              (d := d) hd (P := P)))
    have hminus :
        ContinuousOn
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a => (x a : ℂ))) E :=
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
        hreal.continuousOn
        (by
          simpa [E] using
            (BHW.os45FlatCommonChart_real_mem_omega_id
              (d := d) hd (P := P)))
    simpa [H] using hplus.sub hminus
  have hg_cont :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    have hφH :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n => φ x * H x) :=
      SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
        (by
          simpa [E] using
            (BHW.isOpen_os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n))))
        φ.continuous
        (by
          simpa [E] using hφE)
        hH_cont
    simpa [mul_comm] using hφH
  have hg_compact :
      HasCompactSupport
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) := by
    refine hφ_compact.mono' ?_
    intro x hx
    by_contra hxφ
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
    exact hx (by simp [hφx])
  have hg_int :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x) :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hcov :=
    BHW.os45CommonEdgeFlatCLE_integral_comp d n
      (1 : Equiv.Perm (Fin n))
      (fun x : BHW.OS45FlatCommonChartReal d n => H x * φ x)
      hg_int
  simpa [H] using
    hcov.trans
      (congrArg
        (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
        (integral_congr_ae
          (Eventually.of_forall fun u =>
            BHW.os45FlatCommonChart_commonBoundaryDifference_sourceIntegrand_eq
              (d := d) hd OS lgc D φ hφE u)))

/-- If the horizontal source common-edge branch difference represents the zero
distribution on the Figure-2-4 source patch, then the corresponding flat
ordinary-minus-adjacent common-boundary difference pairs to zero against every
compact test supported on the flattened common edge.

This is the source-to-flat distributional bridge used after the proof-local
`Hdiff` germ has been produced. -/
theorem os45FlatCommonChart_commonBoundaryDifference_integral_zero_of_sourceRepresents
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) P.V)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ))) * φ x = 0 := by
  classical
  let D := Classical.choice
    (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  have hcov :=
    BHW.os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback
      (d := d) hd OS lgc (P := P) D φ hφ_compact hφE
  have hsrc_supp :
      SCV.SupportsInOpen
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) P.V := by
    exact
      ⟨D.toSchwartzNPointCLM_hasCompactSupport
          (1 : Equiv.Perm (Fin n)) φ,
        D.toSchwartzNPointCLM_tsupport_subset_V
          (1 : Equiv.Perm (Fin n)) φ hφE⟩
  have hzero_src :=
    hrep (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ) hsrc_supp
  have hsrc_int_zero :
      ∫ u : NPointDomain d n,
          (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) -
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u = 0 := by
    simpa using hzero_src.symm
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ))) * φ x
        = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
            ∫ u : NPointDomain d n,
              (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u)) -
                BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u))) *
                (D.toSchwartzNPointCLM
                  (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := hcov
    _ = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * 0 := by
          exact congrArg
            (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
            hsrc_int_zero
    _ = 0 := by simp

/-- Local version of the source-to-flat distributional bridge.  A local
horizontal source common-edge zero representation on `U` is enough for flat
tests whose support lies in the flattened common-edge image of `U`. -/
theorem os45FlatCommonChart_commonBoundaryDifference_integral_zero_of_sourceRepresentsOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) U)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ))) * φ x = 0 := by
  classical
  let D := Classical.choice
    (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  have hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hφU hx with ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hcov :=
    BHW.os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback
      (d := d) hd OS lgc (P := P) D φ hφ_compact hφE
  have hsrc_supp :
      SCV.SupportsInOpen
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) U := by
    exact
      ⟨D.toSchwartzNPointCLM_hasCompactSupport
          (1 : Equiv.Perm (Fin n)) φ,
        D.toSchwartzNPointCLM_tsupport_subset_image
          (1 : Equiv.Perm (Fin n)) φ hφU⟩
  have hzero_src :=
    hrep (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ) hsrc_supp
  have hsrc_int_zero :
      ∫ u : NPointDomain d n,
          (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) -
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u = 0 := by
    simpa using hzero_src.symm
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ))) * φ x
        = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
            ∫ u : NPointDomain d n,
              (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u)) -
                BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u))) *
                (D.toSchwartzNPointCLM
                  (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := hcov
    _ = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * 0 := by
          exact congrArg
            (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
            hsrc_int_zero
    _ = 0 := by simp

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

/-- The ordinary plus and adjacent minus side-height branch integrands are
eventually integrable, uniformly over a compact set of side directions.

This packages only compact support plus the checked Figure-2-4 local wedge
domain membership.  It supplies the integrability hypotheses for the
side-height pullback theorem without using any boundary-value comparison. -/
theorem os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun j =>
              ((x + ε • η) j : ℂ) + ((ε • η) j : ℂ) * Complex.I) *
          φ (x + ε • η)) ∧
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun j =>
              ((x + (-ε : ℝ) • η) j : ℂ) +
                (((-ε : ℝ) • η) j : ℂ) * Complex.I) *
          φ (x + (-ε : ℝ) • η)) := by
  let K : Set (BHW.OS45FlatCommonChartReal d n) :=
    tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
  have hK : IsCompact K := by
    simpa [K] using hφ_compact.isCompact
  have hK_sub : K ⊆
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    simpa [K] using hφE
  obtain ⟨r, hr, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P) K hK hK_sub Kη hKη hKηC
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη
  constructor
  · refine
      BHW.os45FlatCommonChart_branch_shifted_mul_integrable
        (d := d) (n := n) OS lgc (1 : Equiv.Perm (Fin n))
        (ε • η) (ε • η) φ hφ_compact ?_
    intro x hx
    have hy : x + ε • η ∈ K :=
      BHW.tsupport_translateSchwartz_subset_preimage
        ((ε : ℝ) • η) φ hx
    have hmem := (hside (x + ε • η) hy η hη ε hε_pos hε_lt).1
    simpa using hmem
  · refine
      BHW.os45FlatCommonChart_branch_shifted_mul_integrable
        (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        ((-ε : ℝ) • η) ((-ε : ℝ) • η) φ hφ_compact ?_
    intro x hx
    have hy : x + (-ε : ℝ) • η ∈ K :=
      BHW.tsupport_translateSchwartz_subset_preimage
        ((-ε : ℝ) • η) φ hx
    have hmem := (hside (x + (-ε : ℝ) • η) hy η hη ε hε_pos hε_lt).2
    simpa [sub_eq_add_neg, neg_smul] using hmem

/-- For sufficiently small positive side height, every source point whose
shifted flat common-edge point lies in the compact flat test support is on the
corresponding outgoing source-side sheet.

This is the sheet-membership half of the proof-local `(4.14)` packet.  It is
extracted from the same Figure-2-4 local wedge used for integrability and does
not assert any branch/source boundary-value limit. -/
theorem os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      (∀ u : NPointDomain d n,
        BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u + ε • η ∈
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) ∈
          BHW.ExtendedTube d n) ∧
      (∀ u : NPointDomain d n,
        BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u + (-ε : ℝ) • η ∈
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u) ∈
          BHW.ExtendedTube d n) := by
  let K : Set (BHW.OS45FlatCommonChartReal d n) :=
    tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
  have hK : IsCompact K := by
    simpa [K] using hφ_compact.isCompact
  have hK_sub : K ⊆
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    simpa [K] using hφE
  obtain ⟨r, hr, hside⟩ :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P) K hK hK_sub Kη hKη hKηC
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη
  constructor
  · intro u hu
    have hmem :=
      (hside
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) u + ε • η)
        (by simpa [K] using hu) η hη ε hε_pos hε_lt).1
    exact
      (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
        d n (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
        (1 : ℝ) ε η u).mp (by simpa using hmem)
  · intro u hu
    have hmem :=
      (hside
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) u + (-ε : ℝ) • η)
        (by simpa [K] using hu) η hη ε hε_pos hε_lt).2
    exact
      (BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
        d n (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u).mp
        (by simpa [neg_smul] using hmem)

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

/-- Local source-window version of the side-support radius.  If a flat test is
supported in the flattened image of an open source window, then sufficiently
small positive and negative side shifts remain supported in that same image. -/
theorem os45FlatCommonChart_sideSupport_radius_sourceImage
    [NeZero d] {n : ℕ}
    (ρperm : Equiv.Perm (Fin n))
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n ρperm '' U) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε < r →
      ∀ η ∈ Kη,
        tsupport
          (SCV.translateSchwartz ((ε : ℝ) • η) φ :
            BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45CommonEdgeFlatCLE d n ρperm '' U ∧
        tsupport
          (SCV.translateSchwartz ((-ε : ℝ) • η) φ :
            BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45CommonEdgeFlatCLE d n ρperm '' U := by
  let R := BHW.OS45FlatCommonChartReal d n
  let S : Set R := tsupport (φ : R → ℂ)
  let E : Set R := BHW.os45CommonEdgeFlatCLE d n ρperm '' U
  let zeroEdge : Set ((R × R) × ℝ) := (S ×ˢ Kη) ×ˢ ({0} : Set ℝ)
  let sideWindow : Set ((R × R) × ℝ) :=
    {p | p.1.1 - p.2 • p.1.2 ∈ E ∧ p.1.1 + p.2 • p.1.2 ∈ E}
  have hE_open : IsOpen E := by
    simpa [E] using
      (BHW.os45CommonEdgeFlatCLE d n ρperm).toHomeomorph.isOpenMap
        U hU_open
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
    rintro ⟨⟨x, _η⟩, ε⟩ ⟨⟨hxS, _hη⟩, hε0⟩
    have hε : ε = 0 := by simpa using hε0
    subst ε
    constructor <;> simpa [sideWindow, E] using hφU hxS
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

/-- Pointwise formula for the signed one-sided source-test family. -/
@[simp] theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_apply
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (x : NPointDomain d n) :
    ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
      SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
      D.χ x *
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm x + (sgn * ε) • η) := by
  change
    (D.toShiftedSchwartzNPointCLM ρperm ((sgn * ε) • η) φ :
      NPointDomain d n → ℂ) x =
      D.χ x *
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm x + (sgn * ε) • η)
  rw [BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM,
    ContinuousLinearMap.comp_apply,
    BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_apply]
  congr 1

/-- Signed side-height version of cutoff removal for the zero-diagonal source
test family. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (SCV.translateSchwartz ((sgn * ε) • η) φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (x : NPointDomain d n) :
    ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
      SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
      φ (BHW.os45CommonEdgeFlatCLE d n ρperm x + (sgn * ε) • η) := by
  change
    (D.toShiftedSchwartzNPointCLM ρperm ((sgn * ε) • η) φ :
      NPointDomain d n → ℂ) x =
      φ (BHW.os45CommonEdgeFlatCLE d n ρperm x + (sgn * ε) • η)
  exact
    D.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
      ρperm ((sgn * ε) • η) φ hφE x

/-- Signed side-height branch integral written against the corresponding
zero-diagonal moving source test.

For `sgn = 1` this is the ordinary plus-side pullback with
`x = e u + eps • eta`; for `sgn = -1` it is the adjacent minus-side pullback
with `x = e u - eps • eta`.  The statement is only coordinate/Jacobian and
cutoff algebra; it does not assert the OS I `(4.14)` boundary-value limit. -/
theorem os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (SCV.translateSchwartz ((sgn * ε) • η) φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((x + (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ (x + (sgn * ε) • η))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((BHW.os45CommonEdgeFlatCLE d n ρperm u +
                    (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
            ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
  simpa [BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM,
    BHW.OS45Figure24SourceCutoffData.toShiftedZeroDiagonalCLM] using
    BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM
      (d := d) (n := n) OS lgc D σ ρperm
      ((sgn * ε) • η) ((sgn * ε) • η) φ hφE hg_shift

/-- Signed side-height branch integral pulled to source variables and unfolded
to the `extendF` value on the exact source-side side-sheet configuration.

This is the coordinate/Jacobian/cutoff normal form consumed by the proof-local
OS-I `(4.14)` transfer.  It deliberately stops before any branch/source
boundary-value asymptotic assertion. -/
theorem os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
    [NeZero d] {hd : 2 ≤ d}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (SCV.translateSchwartz ((sgn * ε) • η) φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((x + (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ (x + (sgn * ε) • η))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u)) *
            ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((BHW.os45CommonEdgeFlatCLE d n ρperm u +
                    (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
            ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) :=
        BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM
          (d := d) (n := n) OS lgc D σ ρperm sgn ε η φ hφE hg_shift
    _ =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u)) *
            ((((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
        congr 1

/-- For sufficiently small positive side height, both signed side source tests
have the cutoff removed pointwise. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη, ∀ x : NPointDomain d n,
      ((((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
          φ (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) x + ε • η) ∧
      ((((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
          φ (BHW.os45CommonEdgeFlatCLE d n
              (1 : Equiv.Perm (Fin n)) x - ε • η) := by
  rcases
    BHW.os45FlatCommonChart_sideSupport_radius
      (d := d) (n := n) (P := P)
      Kη hKη hKηC φ hφ_compact hφE with
    ⟨r, hr, hside⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη x
  have hsideε := hside ε hε_pos hε_lt η hη
  constructor
  · simpa using
      D.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ
        (by simpa using hsideε.1) x
  · have hplain :=
      D.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ
        (by simpa [neg_smul] using hsideε.2) x
    simpa [sub_eq_add_neg, neg_smul] using hplain

/-- Source-window version of the signed side support and cutoff-removal packet.
For sufficiently small positive side height, both signed side source tests are
supported in the prescribed source window, and the cutoff is pointwise
invisible. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U ∧
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U ∧
      ∀ x : NPointDomain d n,
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
            φ (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) x + ε • η) ∧
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) x) =
            φ (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) x - ε • η) := by
  rcases
    BHW.os45FlatCommonChart_sideSupport_radius_sourceImage
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) hU_open
      Kη hKη φ hφ_compact hφU with
    ⟨r, hr, hside⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη
  have hsideε := hside ε hε_pos hε_lt η hη
  have hplusU :
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U := by
    change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ U
    simpa using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ
        (by simpa using hsideε.1)
  have hminusU :
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U := by
    change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ U
    simpa [neg_smul] using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ
        (by simpa [neg_smul] using hsideε.2)
  have hplusE :
      tsupport (SCV.translateSchwartz (((1 : ℝ) * ε) • η) φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    intro y hy
    rcases hsideε.1 (by simpa using hy) with ⟨u, huU, hu_eq⟩
    simpa [hu_eq] using
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hminusE :
      tsupport (SCV.translateSchwartz (((-1 : ℝ) * ε) • η) φ :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    intro y hy
    rcases hsideε.2 (by simpa [neg_smul] using hy) with ⟨u, huU, hu_eq⟩
    simpa [hu_eq] using
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  refine ⟨hplusU, hminusU, ?_⟩
  intro x
  constructor
  · simpa using
      D.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ hplusE x
  · have hplain :=
      D.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ hminusE x
    simpa [sub_eq_add_neg, neg_smul] using hplain

/-- After shrinking to the one-sided height window supplied by the flat
support-radius lemma, both signed side-test families are supported in the
original Figure-2-4 source patch.

This is the support part of the proof-local `(4.14)` packet: it lets the OS
Euclidean edge identities be applied to the side-height tests, but it does not
assert the side-height equality itself. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_V_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ P.V ∧
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ P.V := by
  rcases
    BHW.os45FlatCommonChart_sideSupport_radius
      (d := d) (n := n) (P := P)
      Kη hKη hKηC φ hφ_compact hφE with
    ⟨r, hr, hside⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη
  have hsideε := hside ε hε_pos hε_lt η hη
  constructor
  · change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ P.V
    simpa using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_V
        (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ
        (by simpa using hsideε.1)
  · change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ P.V
    simpa using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_V
        (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ
        (by simpa [neg_smul] using hsideε.2)

/-- For sufficiently small positive side height, the signed cutoff-pulled
source tests are supported in a prescribed open source window, provided the
unshifted flat test is supported in the flattened image of that window. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U ∧
      tsupport (((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆ U := by
  rcases
    BHW.os45FlatCommonChart_sideSupport_radius_sourceImage
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) hU_open
      Kη hKη φ hφ_compact hφU with
    ⟨r, hr, hside⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr)]
    with ε hε_pos hε_lt η hη
  have hsideε := hside ε hε_pos hε_lt η hη
  constructor
  · change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ U
    simpa using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) (((1 : ℝ) * ε) • η) φ
        (by simpa using hsideε.1)
  · change
      tsupport
        (D.toShiftedSchwartzNPointCLM
          (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ :
            NPointDomain d n → ℂ) ⊆ U
    simpa [neg_smul] using
      D.toShiftedSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) (((-1 : ℝ) * ε) • η) φ
        (by simpa [neg_smul] using hsideε.2)

/-- For sufficiently small positive side height, the checked Euclidean
adjacent-edge identity applies to both signed side-height source tests.

This is the OS/E3 rewrite needed before the genuinely missing `(4.14)`
side-height comparison: the theorem identifies the adjacent and ordinary Wick
pairings for each fixed side test, but it does not compare the plus and minus
side tests with each other. -/
theorem OS45Figure24SourceCutoffData.sideZeroDiagonal_adjacentPairing_eq_eventually
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u) ∧
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
  have hsupport :=
    D.toSideZeroDiagonalCLM_tsupport_subset_V_eventually
      Kη hKη hKηC φ hφ_compact hφE
  have hV_swap_ordered :
      ∀ x ∈ P.V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm *
              (1 : Equiv.Perm (Fin n))) := by
    intro x hx
    simpa [P.τ_eq] using P.V_swap_ordered x hx
  filter_upwards [hsupport] with ε hε η hη
  constructor
  · have hpair_swap :=
      BHW.os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
        (d := d) OS lgc n i hi P.V P.V_jost
        (1 : Equiv.Perm (Fin n)) P.V_ordered hV_swap_ordered
        (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n))
        (hε η hη).1
    simpa [P.τ_eq] using hpair_swap
  · have hpair_swap :=
      BHW.os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
        (d := d) OS lgc n i hi P.V P.V_jost
        (1 : Equiv.Perm (Fin n)) P.V_ordered hV_swap_ordered
        (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n))
        (hε η hη).2
    simpa [P.τ_eq] using hpair_swap

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
    simp [SCV.translateSchwartzCLM_apply]
  have hTU'' :
      TendstoUniformlyOn F
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          L (D.toZeroDiagonalCLM ρperm φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    simpa [hF0] using hTU'
  simpa [F] using hTU''

/-- The signed source-side tests used in the OS I §4.14 flat transition have a
common Schwinger limit, uniformly over compact sets of side directions.

This is only the source-variable limit package.  It deliberately does not
identify arbitrary finite side-height flat integrals with Schwinger values; the
flat zero-height conclusion still has to pass through the local boundary-value
and EOW arguments. -/
theorem OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    TendstoUniformlyOn
      (fun ε η =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
      (𝓝[Set.Ioi 0] (0 : ℝ)) Kη ∧
    TendstoUniformlyOn
      (fun ε η =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
      (𝓝[Set.Ioi 0] (0 : ℝ)) Kη ∧
    TendstoUniformlyOn
      (fun ε η =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
      (𝓝[Set.Ioi 0] (0 : ℝ)) Kη ∧
    TendstoUniformlyOn
      (fun ε η =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
      (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
  have hS_plus :
      TendstoUniformlyOn
        (fun ε η =>
          OS.S n
            (D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη :=
    D.apply_toSideZeroDiagonalCLM_tendstoUniformlyOn_zero
      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n)
      Kη hKη φ hφ_compact
  have hS_minus :
      TendstoUniformlyOn
        (fun ε η =>
          OS.S n
            (D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη :=
    D.apply_toSideZeroDiagonalCLM_tendstoUniformlyOn_zero
      (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n)
      Kη hKη φ hφ_compact
  have hord_plus :
      TendstoUniformlyOn
        (fun ε η =>
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    refine hS_plus.congr ?_
    filter_upwards with ε
    intro η _hη
    exact
      bvt_euclidean_restriction (d := d) OS lgc n
        (D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ)
  have hord_minus :
      TendstoUniformlyOn
        (fun ε η =>
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    refine hS_minus.congr ?_
    filter_upwards with ε
    intro η _hη
    exact
      bvt_euclidean_restriction (d := d) OS lgc n
        (D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ)
  have hadj_event :=
    D.sideZeroDiagonal_adjacentPairing_eq_eventually
      OS lgc Kη hKη hKηC φ hφ_compact hφE
  have hadj_plus :
      TendstoUniformlyOn
        (fun ε η =>
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    refine hord_plus.congr ?_
    filter_upwards [hadj_event] with ε hε
    intro η hη
    exact (hε η hη).1.symm
  have hadj_minus :
      TendstoUniformlyOn
        (fun ε η =>
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (fun _ : BHW.OS45FlatCommonChartReal d n =>
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
    refine hord_minus.congr ?_
    filter_upwards [hadj_event] with ε hε
    intro η hη
    exact (hε η hη).2.symm
  exact ⟨hord_plus, hadj_plus, hord_minus, hadj_minus⟩

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

/-- The Wick-anchor Schwinger functional in flattened common-chart coordinates,
including the absolute Jacobian for the source-to-flat real change of variables.

This is an anchor-normalization functional.  The strict OS-II EOW seed uses an
independently constructed common-boundary CLM unless this functional is proved
to represent that boundary distribution. -/
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

/-- Source-coordinate Wick-anchor normalization for an explicit Figure-2-4
cutoff.  This is the unnormalized source-variable calculation behind the flat
Schwinger anchor: no flat Jacobian or chosen cutoff is hidden in the statement.
-/
theorem os45FlatCommonChart_wickSection_sourcePairing_eq_schwinger
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    (∫ u : NPointDomain d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.flattenCfg n d
          (fun k μ =>
            BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u) k μ +
              (BHW.os45HalfTimeDirection (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u k μ : ℂ) * Complex.I)) *
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) u) =
      OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
  rw [bvt_euclidean_restriction (d := d) OS lgc n
    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ tsupport
      (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
        NPointDomain d n → ℂ)
  · have huV : u ∈ P.V :=
      D.toSchwartzNPointCLM_tsupport_subset_V
        (1 : Equiv.Perm (Fin n)) φ hφE hu
    rw [BHW.os45FlatCommonChart_wickSection_plus_eq_bvt_F
      (d := d) (n := n) OS lgc (P.V_ordered u huV)]
    rfl
  · have hzero :
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) u = 0 :=
      image_eq_zero_of_notMem_tsupport hu
    have hzero_zero :
        (((D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ).1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) u = 0 := by
      change
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) u = 0
      exact hzero
    simp [hzero, hzero_zero]

/-- Source-coordinate adjacent Wick normalization for the same explicit
Figure-2-4 cutoff.  The proof is the OS Euclidean symmetry step applied to the
cutoff-pulled zero-diagonal test; it does not require the cutoff to commute
with the adjacent transposition. -/
theorem os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    (∫ u : NPointDomain d n,
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) u) =
      OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
  rw [bvt_euclidean_restriction (d := d) OS lgc n
    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)]
  have hψP :
      tsupport
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) ⊆ P.V :=
    D.toSchwartzNPointCLM_tsupport_subset_V
      (1 : Equiv.Perm (Fin n)) φ hφE
  have hV_swap_ordered :
      ∀ x ∈ P.V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm *
              (1 : Equiv.Perm (Fin n))) := by
    intro x hx
    simpa [P.τ_eq] using P.V_swap_ordered x hx
  have hpair_swap :=
    BHW.os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
      (d := d) OS lgc n i hi P.V P.V_jost
      (1 : Equiv.Perm (Fin n)) P.V_ordered hV_swap_ordered
      (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ) hψP
  have hpair :
      ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
              NPointDomain d n → ℂ) u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
              NPointDomain d n → ℂ) u := by
    simpa [P.τ_eq] using hpair_swap
  calc
    ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) u =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) u := hpair
    _ =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          (((D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u := by
        apply integral_congr_ae
        filter_upwards with u
        change
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
                NPointDomain d n → ℂ) u =
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
                NPointDomain d n → ℂ) u
        rfl

/-- Pre-`Hdiff` flat `(4.14)` source-pairing equality for the concrete
ordinary and genuine adjacent OS-I boundary distributions.

This is the compact-test equality used by the proof-local flat EOW step before
any common-boundary difference germ exists.  It compares the two OS boundary
fields against the same cutoff-pulled source test; it does not mention
`Hdiff`, a common-boundary CLM, or the downstream deterministic adjacent
branch. -/
theorem os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick
    [NeZero d] {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    (∫ u : NPointDomain d n,
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
        (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
          NPointDomain d n → ℂ) u) =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) u := by
  have hadj :
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) u) =
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) :=
    BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger
      (d := d) OS lgc D φ hφE
  have hord :
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
            NPointDomain d n → ℂ) u) =
        OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
    have hchange :
        (∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
              NPointDomain d n → ℂ) u) =
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              (((D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u := by
      apply integral_congr_ae
      filter_upwards with u
      change
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
              NPointDomain d n → ℂ) u =
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) φ :
              NPointDomain d n → ℂ) u
      rfl
    exact hchange.trans
      (bvt_euclidean_restriction (d := d) OS lgc n
        (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)).symm
  exact hadj.trans hord.symm

/-- Local representations of the ordinary flat branch assemble to the global
zero-height pairing against an arbitrary supplied common-boundary CLM. -/
theorem os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hlocal :
      ∀ x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        ∃ U : Set (BHW.OS45FlatCommonChartReal d n),
          IsOpen U ∧ x0 ∈ U ∧
            ContinuousOn
              (fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ))) U ∧
            SCV.RepresentsDistributionOn
              T
              (fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ)))
              U)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    (∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ)) * φ x)
      =
      T φ := by
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)) (fun a => (x a : ℂ))
  have hrep :
      T φ = ∫ x : BHW.OS45FlatCommonChartReal d n, H x * φ x := by
    exact
      SCV.distribution_representation_of_local_representations_for_test
        T H φ hφ_compact
        (by
          intro x hx
          simpa [H] using hlocal x (hφE hx))
  simpa [H] using hrep.symm

/-- Local representations of the adjacent flat branch assemble to the global
zero-height pairing against an arbitrary supplied common-boundary CLM. -/
theorem os45FlatCommonChart_minus_zeroHeight_pairing_eq_CLM_of_localRepresents
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hlocal :
      ∀ x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        ∃ U : Set (BHW.OS45FlatCommonChartReal d n),
          IsOpen U ∧ x0 ∈ U ∧
            ContinuousOn
              (fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a => (x a : ℂ))) U ∧
            SCV.RepresentsDistributionOn
              T
              (fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a => (x a : ℂ)))
              U)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :
    (∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ)) * φ x)
      =
      T φ := by
  let H : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n))) (fun a => (x a : ℂ))
  have hrep :
      T φ = ∫ x : BHW.OS45FlatCommonChartReal d n, H x * φ x := by
    exact
      SCV.distribution_representation_of_local_representations_for_test
        T H φ hφ_compact
        (by
          intro x hx
          simpa [H] using hlocal x (hφE hx))
  simpa [H] using hrep.symm

/-- A zero source common-edge distributional difference supplies a genuine
common zero-height CLM for the two flat common-chart boundary branches.

The CLM is the checked ordinary edge distribution; the adjacent pairing is
identified with it by the source-to-flat difference-zero bridge. -/
theorem os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresents
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) P.V) :
    (∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x) =
        BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ) ∧
    (∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x) =
        BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ) := by
  constructor
  · intro φ hφ_compact hφE
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc
        (P := P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact hφE
  · intro φ hφ_compact hφE
    let Fminus : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ))
    let Fplus : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ))
    let E : Set (BHW.OS45FlatCommonChartReal d n) :=
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n))
    have hE_open : IsOpen E := by
      simpa [E] using
        BHW.isOpen_os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))
    have hreal :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            fun a => (x a : ℂ)) :=
      continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
    have hminus_cont : ContinuousOn Fminus E := by
      exact
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn.comp
          hreal.continuousOn
          (by
            simpa [E] using
              (BHW.os45FlatCommonChart_real_mem_omega_adjacent
                (d := d) hd (P := P)))
    have hplus_cont : ContinuousOn Fplus E := by
      exact
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
          hreal.continuousOn
          (by
            simpa [E] using
              (BHW.os45FlatCommonChart_real_mem_omega_id
                (d := d) hd (P := P)))
    have hminus_mul_cont :
        Continuous (fun x => Fminus x * φ x) := by
      have h :=
        SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
          hE_open φ.continuous (by simpa [E] using hφE) hminus_cont
      simpa [mul_comm] using h
    have hplus_mul_cont :
        Continuous (fun x => Fplus x * φ x) := by
      have h :=
        SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
          hE_open φ.continuous (by simpa [E] using hφE) hplus_cont
      simpa [mul_comm] using h
    have hminus_mul_compact :
        HasCompactSupport (fun x => Fminus x * φ x) := by
      refine hφ_compact.mono' ?_
      intro x hx
      by_contra hxφ
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
      exact hx (by simp [hφx])
    have hplus_mul_compact :
        HasCompactSupport (fun x => Fplus x * φ x) := by
      refine hφ_compact.mono' ?_
      intro x hx
      by_contra hxφ
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
      exact hx (by simp [hφx])
    have hminus_int : Integrable (fun x => Fminus x * φ x) :=
      hminus_mul_cont.integrable_of_hasCompactSupport hminus_mul_compact
    have hplus_int : Integrable (fun x => Fplus x * φ x) :=
      hplus_mul_cont.integrable_of_hasCompactSupport hplus_mul_compact
    have hdiff_zero :=
      BHW.os45FlatCommonChart_commonBoundaryDifference_integral_zero_of_sourceRepresents
        (d := d) hd OS lgc (P := P) hrep φ hφ_compact hφE
    have hdiff_zero' :
        (∫ x, Fminus x * φ x) - (∫ x, Fplus x * φ x) = 0 := by
      calc
        (∫ x, Fminus x * φ x) - (∫ x, Fplus x * φ x)
            = ∫ x, Fminus x * φ x - Fplus x * φ x := by
              exact (MeasureTheory.integral_sub hminus_int hplus_int).symm
        _ = ∫ x, (Fminus x - Fplus x) * φ x := by
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ = 0 := by simpa [Fminus, Fplus] using hdiff_zero
    have hminus_eq_plus :
        (∫ x, Fminus x * φ x) = (∫ x, Fplus x * φ x) :=
      sub_eq_zero.mp hdiff_zero'
    have hplus_eq_T :=
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc
        (P := P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact hφE
    calc
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x
          = ∫ x, Fminus x * φ x := by rfl
      _ = ∫ x, Fplus x * φ x := hminus_eq_plus
      _ = BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ := by
            simpa [Fplus] using hplus_eq_T

/-- Local common-boundary CLM bridge.  A zero source representation on `U`
identifies the two zero-height flat boundary pairings with the ordinary edge
CLM for flat tests supported in the common-edge image of `U`. -/
theorem os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) U) :
    (∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x) =
        BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ) ∧
    (∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x) =
        BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ) := by
  have himage_sub_edge :
      BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  constructor
  · intro φ hφ_compact hφU
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc
        (P := P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact (hφU.trans himage_sub_edge)
  · intro φ hφ_compact hφU
    let Fminus : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ))
    let Fplus : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ))
    let E : Set (BHW.OS45FlatCommonChartReal d n) :=
      BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n))
    have hφEdge :
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E :=
      hφU.trans (by simpa [E] using himage_sub_edge)
    have hE_open : IsOpen E := by
      simpa [E] using
        BHW.isOpen_os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))
    have hreal :
        Continuous
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            fun a => (x a : ℂ)) :=
      continuous_pi fun a => Complex.continuous_ofReal.comp (continuous_apply a)
    have hminus_cont : ContinuousOn Fminus E := by
      exact
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn.comp
          hreal.continuousOn
          (by
            simpa [E] using
              (BHW.os45FlatCommonChart_real_mem_omega_adjacent
                (d := d) hd (P := P)))
    have hplus_cont : ContinuousOn Fplus E := by
      exact
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn.comp
          hreal.continuousOn
          (by
            simpa [E] using
              (BHW.os45FlatCommonChart_real_mem_omega_id
                (d := d) hd (P := P)))
    have hminus_mul_cont :
        Continuous (fun x => Fminus x * φ x) := by
      have h :=
        SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
          hE_open φ.continuous (by simpa [E] using hφEdge) hminus_cont
      simpa [mul_comm] using h
    have hplus_mul_cont :
        Continuous (fun x => Fplus x * φ x) := by
      have h :=
        SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
          hE_open φ.continuous (by simpa [E] using hφEdge) hplus_cont
      simpa [mul_comm] using h
    have hminus_mul_compact :
        HasCompactSupport (fun x => Fminus x * φ x) := by
      refine hφ_compact.mono' ?_
      intro x hx
      by_contra hxφ
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
      exact hx (by simp [hφx])
    have hplus_mul_compact :
        HasCompactSupport (fun x => Fplus x * φ x) := by
      refine hφ_compact.mono' ?_
      intro x hx
      by_contra hxφ
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
      exact hx (by simp [hφx])
    have hminus_int : Integrable (fun x => Fminus x * φ x) :=
      hminus_mul_cont.integrable_of_hasCompactSupport hminus_mul_compact
    have hplus_int : Integrable (fun x => Fplus x * φ x) :=
      hplus_mul_cont.integrable_of_hasCompactSupport hplus_mul_compact
    have hdiff_zero :=
      BHW.os45FlatCommonChart_commonBoundaryDifference_integral_zero_of_sourceRepresentsOn
        (d := d) hd OS lgc (P := P) hU_sub hrep φ hφ_compact hφU
    have hdiff_zero' :
        (∫ x, Fminus x * φ x) - (∫ x, Fplus x * φ x) = 0 := by
      calc
        (∫ x, Fminus x * φ x) - (∫ x, Fplus x * φ x)
            = ∫ x, Fminus x * φ x - Fplus x * φ x := by
              exact (MeasureTheory.integral_sub hminus_int hplus_int).symm
        _ = ∫ x, (Fminus x - Fplus x) * φ x := by
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ = 0 := by simpa [Fminus, Fplus] using hdiff_zero
    have hminus_eq_plus :
        (∫ x, Fminus x * φ x) = (∫ x, Fplus x * φ x) :=
      sub_eq_zero.mp hdiff_zero'
    have hplus_eq_T :=
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc
        (P := P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact (by simpa [E] using hφEdge)
    calc
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x
          = ∫ x, Fminus x * φ x := by rfl
      _ = ∫ x, Fplus x * φ x := hminus_eq_plus
      _ = BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P φ := by
            simpa [Fplus] using hplus_eq_T

/-- Distributional one-sided boundary value in the ordinary flat branch,
assuming a supplied zero-height common-chart boundary distribution. -/
theorem os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hzero :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (x a : ℂ)) * φ x)
      = T φ) :
    TendstoUniformlyOn
      (fun (ε : ℝ) η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ) +
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        T φ)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      Kη := by
  have hF_cont :
      ContinuousOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    (BHW.differentiableOn_os45FlatCommonChartBranch
      d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn
  have hside :
      ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K →
        K ⊆ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) →
        ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
          Kη ⊆ BHW.os45FlatCommonChartCone d n →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) +
                ((1 : ℝ) : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                BHW.os45FlatCommonChartOmega d n
                  (1 : Equiv.Perm (Fin n)) := by
    intro K hK hKE Kη hKη hKηC
    obtain ⟨r, hr_pos, hr_mem⟩ :=
      BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P) K hK hKE Kη hKη hKηC
    refine ⟨r, hr_pos, ?_⟩
    intro x hx η hη ε hε_pos hε_lt
    have hmem := (hr_mem x hx η hη ε hε_pos hε_lt).1
    simpa [one_mul] using hmem
  simpa [one_mul] using
    (SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
      (m := BHW.os45FlatCommonChartDim d n)
      (E := BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (C := BHW.os45FlatCommonChartCone d n)
      (Ωc := BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.isOpen_os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      hF_cont
      (BHW.os45FlatCommonChart_real_mem_omega_id (d := d) hd (P := P))
      (1 : ℝ) hside
      Kη hKη hKηC φ hφ_compact hφE
      (T φ)
      hzero)

/-- Distributional one-sided boundary value in the adjacent flat branch,
assuming a supplied zero-height common-chart boundary distribution. -/
theorem os45_BHWJost_flatCommonChart_distributionalBoundaryValue_minus_of_zeroHeight_pairingCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hzero :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : ℂ)) * φ x)
      = T φ) :
    TendstoUniformlyOn
      (fun (ε : ℝ) η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ) -
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        T φ)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      Kη := by
  have hF_cont :
      ContinuousOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    (BHW.differentiableOn_os45FlatCommonChartBranch
      d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
  have hside :
      ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K →
        K ⊆ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) →
        ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
          Kη ⊆ BHW.os45FlatCommonChartCone d n →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) +
                ((-1 : ℝ) : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                BHW.os45FlatCommonChartOmega d n
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    intro K hK hKE Kη hKη hKηC
    obtain ⟨r, hr_pos, hr_mem⟩ :=
      BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P) K hK hKE Kη hKη hKηC
    refine ⟨r, hr_pos, ?_⟩
    intro x hx η hη ε hε_pos hε_lt
    have hmem := (hr_mem x hx η hη ε hε_pos hε_lt).2
    simpa [sub_eq_add_neg, neg_mul, one_mul] using hmem
  simpa [sub_eq_add_neg, neg_mul, one_mul] using
    (SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
      (m := BHW.os45FlatCommonChartDim d n)
      (E := BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (C := BHW.os45FlatCommonChartCone d n)
      (Ωc := BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (BHW.isOpen_os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hF_cont
      (BHW.os45FlatCommonChart_real_mem_omega_adjacent
        (d := d) hd (P := P))
      (-1 : ℝ) hside
      Kη hKη hKηC φ hφ_compact hφE
      (T φ)
      hzero)

/-- Local flat common-chart EOW equality from the two zero-height boundary
pairings against the same CLM.

This is the direct analytic transfer used at the Figure-2-4 real common edge:
the ordinary and adjacent flat branches agree on a small fixed-basis local EOW
coordinate ball once their distributional zero-height boundary values have
both been identified with `T`. -/
theorem os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_zeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    ∃ R0 : ℝ,
      0 < R0 ∧
      Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0 ⊆
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) ∩
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∧
      Set.EqOn
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.localEOWChart x0 ys w))
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (SCV.localEOWChart x0 ys w))
        (Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0) := by
  classical
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  have hΩplus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (1 : Equiv.Perm (Fin n))
  have hΩminus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hE_open :
      IsOpen
        (BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  obtain ⟨hC_open, hC_conv, _hC_zero, hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  have hC_cone' :
      ∀ t : ℝ, 0 < t →
        ∀ y ∈ BHW.os45FlatCommonChartCone d n,
          t • y ∈ BHW.os45FlatCommonChartCone d n := by
    intro t ht y hy
    exact hC_cone t y ht hy
  have hFplus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
  have hFminus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hplus_bv :
      ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
        Kη ⊆ BHW.os45FlatCommonChartCone d n →
        ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
          HasCompactSupport
            (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ) +
                    (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : BHW.OS45FlatCommonChartReal d n => T φ)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            Kη := by
    intro Kη hKη hKηC φ hφ_compact hφE
    exact
      BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
        (d := d) hd OS lgc T Kη hKη hKηC φ hφ_compact hφE
        (hzero_plus φ hφ_compact hφE)
  have hminus_bv :
      ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
        Kη ⊆ BHW.os45FlatCommonChartCone d n →
        ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
          HasCompactSupport
            (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a => (x a : ℂ) -
                    (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : BHW.OS45FlatCommonChartReal d n => T φ)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            Kη := by
    intro Kη hKη hKηC φ hφ_compact hφE
    exact
      BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_minus_of_zeroHeight_pairingCLM
        (d := d) hd OS lgc T Kη hKη hKηC φ hφ_compact hφE
        (hzero_minus φ hφ_compact hφE)
  obtain ⟨_ρ, _r, _δ, R, Hcoord, _hρ, _hr, _hδ, hR,
      _hRle, _hEwin, _hpos_sub, _hneg_sub, _hplus_dom, _hminus_dom,
      hHcoord, hHplus, hHminus⟩ :=
    SCV.chartDistributionalEOW_local_envelope
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      (BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartCone d n)
      hΩplus_open hΩminus_open hE_open hC_open hC_conv hC_nonempty
      hC_cone'
      (BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P))
      ys hys_mem hys_li x0 hx0
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hFplus hFminus T hplus_bv hminus_bv
  have hzero_plus_mem :
      SCV.localEOWChart x0 ys 0 ∈
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) := by
    simpa [SCV.localEOWChart_zero] using
      BHW.os45FlatCommonChart_real_mem_omega_id
        (d := d) hd (P := P) x0 hx0
  have hzero_minus_mem :
      SCV.localEOWChart x0 ys 0 ∈
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    simpa [SCV.localEOWChart_zero] using
      BHW.os45FlatCommonChart_real_mem_omega_adjacent
        (d := d) hd (P := P) x0 hx0
  obtain ⟨R0, hR0, hball_sub, heq⟩ :=
    SCV.localEOW_envelope_eqOn_small_twoSector_ball
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      hΩplus_open hΩminus_open
      (x0 := x0) (ys := ys)
      (Fplus := BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (Fminus := BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (Hcoord := Hcoord)
      (R := R)
      hR hFplus hFminus hHcoord hHplus hHminus
      hzero_plus_mem hzero_minus_mem
  refine ⟨R0, hR0, ?_, heq⟩
  intro w hw
  have hw' := hball_sub hw
  exact ⟨hw'.1.2, hw'.2⟩

/-- Local flat common-chart EOW equality from two zero-height boundary
pairings against the same CLM on an open sub-neighborhood of the flattened
Figure-2-4 edge.

This is the genuinely local form used after a proof-local `Hdiff` germ:
boundary tests only need support in the chosen open real edge neighborhood
`E`, not in the whole canonical patch edge. -/
theorem os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_localZeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (E : Set (BHW.OS45FlatCommonChartReal d n))
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    ∃ R0 : ℝ,
      0 < R0 ∧
      Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0 ⊆
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) ∩
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∧
      Set.EqOn
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.localEOWChart x0 ys w))
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (SCV.localEOWChart x0 ys w))
        (Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0) := by
  classical
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  have hx0_edge :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) :=
    hE_sub hx0
  have hΩplus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (1 : Equiv.Perm (Fin n))
  have hΩminus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  obtain ⟨hC_open, hC_conv, _hC_zero, hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  have hC_cone' :
      ∀ t : ℝ, 0 < t →
        ∀ y ∈ BHW.os45FlatCommonChartCone d n,
          t • y ∈ BHW.os45FlatCommonChartCone d n := by
    intro t ht y hy
    exact hC_cone t y ht hy
  have hFplus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
  have hFminus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hplus_bv :
      ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
        Kη ⊆ BHW.os45FlatCommonChartCone d n →
        ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
          HasCompactSupport
            (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ) +
                    (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : BHW.OS45FlatCommonChartReal d n => T φ)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            Kη := by
    intro Kη hKη hKηC φ hφ_compact hφE
    exact
      BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
        (d := d) hd OS lgc T Kη hKη hKηC φ hφ_compact
        (hφE.trans hE_sub) (hzero_plus φ hφ_compact hφE)
  have hminus_bv :
      ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
        Kη ⊆ BHW.os45FlatCommonChartCone d n →
        ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
          HasCompactSupport
            (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
          tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a => (x a : ℂ) -
                    (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : BHW.OS45FlatCommonChartReal d n => T φ)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            Kη := by
    intro Kη hKη hKηC φ hφ_compact hφE
    exact
      BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_minus_of_zeroHeight_pairingCLM
        (d := d) hd OS lgc T Kη hKη hKηC φ hφ_compact
        (hφE.trans hE_sub) (hzero_minus φ hφ_compact hφE)
  obtain ⟨_ρ, _r, _δ, R, Hcoord, _hρ, _hr, _hδ, hR,
      _hRle, _hEwin, _hpos_sub, _hneg_sub, _hplus_dom, _hminus_dom,
      hHcoord, hHplus, hHminus⟩ :=
    SCV.chartDistributionalEOW_local_envelope
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      (BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      E
      (BHW.os45FlatCommonChartCone d n)
      hΩplus_open hΩminus_open hE_open hC_open hC_conv hC_nonempty
      hC_cone'
      (by
        intro K hK hK_sub Kη hKη hKηC
        exact
          BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
            (d := d) hd (P := P) K hK (hK_sub.trans hE_sub)
            Kη hKη hKηC)
      ys hys_mem hys_li x0 hx0
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hFplus hFminus T hplus_bv hminus_bv
  have hzero_plus_mem :
      SCV.localEOWChart x0 ys 0 ∈
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) := by
    simpa [SCV.localEOWChart_zero] using
      BHW.os45FlatCommonChart_real_mem_omega_id
        (d := d) hd (P := P) x0 hx0_edge
  have hzero_minus_mem :
      SCV.localEOWChart x0 ys 0 ∈
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    simpa [SCV.localEOWChart_zero] using
      BHW.os45FlatCommonChart_real_mem_omega_adjacent
        (d := d) hd (P := P) x0 hx0_edge
  obtain ⟨R0, hR0, hball_sub, heq⟩ :=
    SCV.localEOW_envelope_eqOn_small_twoSector_ball
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      hΩplus_open hΩminus_open
      (x0 := x0) (ys := ys)
      (Fplus := BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (Fminus := BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (Hcoord := Hcoord)
      (R := R)
      hR hFplus hFminus hHcoord hHplus hHminus
      hzero_plus_mem hzero_minus_mem
  refine ⟨R0, hR0, ?_, heq⟩
  intro w hw
  have hw' := hball_sub hw
  exact ⟨hw'.1.2, hw'.2⟩

/-- A local source zero representation of the horizontal common-edge
difference gives a genuine flat EOW equality ball at any point of that source
neighborhood.

This is the local consumer for the proof-local `Hdiff` germ: it uses only
tests supported in the image of `U` and then invokes the checked local EOW
envelope. -/
theorem os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_sourceRepresentsOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) U)
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (u0 : NPointDomain d n) (hu0 : u0 ∈ U) :
    ∃ R0 : ℝ,
      0 < R0 ∧
      Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0 ⊆
        (SCV.localEOWChart
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u0) ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) ∩
        (SCV.localEOWChart
          (BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) u0) ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∧
      Set.EqOn
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.localEOWChart
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) u0) ys w))
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (SCV.localEOWChart
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n)) u0) ys w))
        (Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0) := by
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hx0 : e u0 ∈ E := ⟨u0, hu0, rfl⟩
  have hpair :=
    BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
      (d := d) hd OS lgc (P := P) hU_sub hrep
  simpa [e, E] using
    BHW.os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_localZeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P)
      E hE_open hE_sub ys hys_mem hys_li (e u0) hx0
      (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
      hpair.1 hpair.2

/-- A source-coordinate equality of the two pulled real common-edge traces is
the same equality after flattening the common edge.

This is only the coordinate transport for the OS I `(4.14)` pointwise trace
statement; it does not prove that trace equality. -/
theorem os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hsource :
      ∀ u ∈ P.V,
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
    ∀ x ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)),
      BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x) =
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x) := by
  intro x hx
  rcases hx with ⟨_y, ⟨u, hu, rfl⟩, rfl⟩
  change
    BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) =
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ))
  rw [BHW.os45FlatCommonChartBranch]
  rw [BHW.os45FlatCommonChartBranch]
  rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
  exact hsource u hu

/-- Local version of
`os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eq`.

It transports a source common-edge equality known only on a local source
window `U` to the corresponding flattened common-edge image of `U`.  This is
the coordinate step needed inside the proof-local flat `(4.14)` EOW crossing;
it does not prove the source equality. -/
theorem os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
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
    ∀ x ∈ BHW.os45CommonEdgeFlatCLE d n
        (1 : Equiv.Perm (Fin n)) '' U,
      BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x) =
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x) := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  change
    BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ)) =
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n))
        (fun a => (BHW.flattenCfgReal n d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u) a : ℂ))
  rw [BHW.os45FlatCommonChartBranch]
  rw [BHW.os45FlatCommonChartBranch]
  rw [BHW.unflattenCfg_ofReal_flattenCfgReal]
  exact hsource u hu

/-- The source common-edge pulled-branch equality is exactly the equality of
the ordinary `extendF` endpoint and its selected permuted endpoint after
undoing the OS45 quarter-turn chart.

This is coordinate algebra for the OS I `(4.14)` target; it does not prove the
branch equality. -/
theorem os45_sourceCommonEdge_branch_eq_iff_permAct_extendF_commonEdge_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (u : NPointDomain d n) :
    (BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))) ↔
    (BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))) =
      BHW.extendF (bvt_F OS lgc n)
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)))) := by
  simp [BHW.os45PulledRealBranch]

/-- The restriction of any flat common-chart branch to a real common-edge
slice is continuous, once that slice is known to lie in the branch domain.

This is the regularity part of the OS I `(4.14)` side-boundary package; the
actual equality of the two real-edge traces is supplied separately by the
OS-I analytic argument. -/
theorem continuousOn_os45FlatCommonChartBranch_realEdge
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (σ ρperm : Equiv.Perm (Fin n))
    (hmem :
      ∀ x ∈ BHW.os45FlatCommonChartEdgeSet d n P ρperm,
        SCV.realEmbed x ∈ BHW.os45FlatCommonChartOmega d n σ) :
    ContinuousOn
      (fun x : BHW.OS45FlatCommonChartReal d n =>
        BHW.os45FlatCommonChartBranch d n OS lgc σ (SCV.realEmbed x))
      (BHW.os45FlatCommonChartEdgeSet d n P ρperm) := by
  have hreal :
      Continuous
        (fun x : BHW.OS45FlatCommonChartReal d n => SCV.realEmbed x) := by
    simpa [SCV.realEmbed] using
      (continuous_pi fun a =>
        Complex.continuous_ofReal.comp (continuous_apply a))
  exact
    (BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc σ).continuousOn.comp
      hreal.continuousOn hmem

/-- A flat common-chart branch tends to its real-edge trace from within its
side domain. -/
theorem tendsto_os45FlatCommonChartBranch_realEdge
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    {x : BHW.OS45FlatCommonChartReal d n}
    (hx :
      SCV.realEmbed x ∈ BHW.os45FlatCommonChartOmega d n σ) :
    Tendsto
      (BHW.os45FlatCommonChartBranch d n OS lgc σ)
      (nhdsWithin (SCV.realEmbed x)
        (BHW.os45FlatCommonChartOmega d n σ))
      (nhds
        (BHW.os45FlatCommonChartBranch d n OS lgc σ (SCV.realEmbed x))) := by
  have hcont :
      ContinuousOn
        (BHW.os45FlatCommonChartBranch d n OS lgc σ)
        (BHW.os45FlatCommonChartOmega d n σ) :=
    (BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc σ).continuousOn
  exact (hcont.continuousWithinAt hx).tendsto

/-- Local version of the flat common-chart continuous-boundary EOW seed.

The edge set `E` may be any open subset of the Figure-2-4 flattened real edge.
This is the form needed inside the proof-local `(4.14)` crossing, where the
boundary-value equality is available only on the current local edge window. -/
theorem os45_BHWJost_flatCommonChart_eqOn_open_of_continuousBoundaryOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {E : Set (BHW.OS45FlatCommonChartReal d n)}
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (bv : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bv x)))
    (hminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bv x)))
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E) :
    ∃ W : Set (BHW.OS45FlatCommonChartSpace d n),
      IsOpen W ∧
      IsPreconnected W ∧
      SCV.realEmbed x0 ∈ W ∧
      W ⊆
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∩
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∧
      Set.EqOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        W := by
  classical
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  have hΩplus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (1 : Equiv.Perm (Fin n))
  have hΩminus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  obtain ⟨hC_open, hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  have hFplus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
  have hFminus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hlocal_wedge :
      ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K → K ⊆ E →
        ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
          Kη ⊆ BHW.os45FlatCommonChartCone d n →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  BHW.os45FlatCommonChartOmega d n
                    (1 : Equiv.Perm (Fin n)) ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                  BHW.os45FlatCommonChartOmega d n
                    (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    intro K hK hK_E Kη hKη hKηC
    exact
      BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P) K hK
        (fun x hx => hE_sub (hK_E hx)) Kη hKη hKηC
  have hx0_edge :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) :=
    hE_sub hx0
  have hplus_nhds :
      BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∈
        nhds (SCV.realEmbed x0) := by
    exact hΩplus_open.mem_nhds
      (by
        simpa [SCV.realEmbed] using
          BHW.os45FlatCommonChart_real_mem_omega_id
            (d := d) hd (P := P) x0 hx0_edge)
  have hminus_nhds :
      BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∈
        nhds (SCV.realEmbed x0) := by
    exact hΩminus_open.mem_nhds
      (by
        simpa [SCV.realEmbed] using
          BHW.os45FlatCommonChart_real_mem_omega_adjacent
            (d := d) hd (P := P) x0 hx0_edge)
  exact
    SCV.local_continuous_edge_of_the_wedge_eqOn_open_at_common_edge
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      (BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      E
      (BHW.os45FlatCommonChartCone d n)
      hΩplus_open hΩminus_open hE_open hC_open hC_conv hC_nonempty
      hlocal_wedge
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hFplus hFminus bv hbv_cont hplus_bv hminus_bv x0 hx0
      hplus_nhds hminus_nhds

/-- Transport a flat common-chart equality neighborhood back to the ambient
initial-sector coordinates. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_eqOn_open
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {Wflat : Set (BHW.OS45FlatCommonChartSpace d n)}
    (hWflat_open : IsOpen Wflat)
    (hWflat_pre : IsPreconnected Wflat)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0Wflat : SCV.realEmbed x0 ∈ Wflat)
    (hWflat_sub :
      Wflat ⊆
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∩
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
    (hEqFlat :
      Set.EqOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        Wflat) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  classical
  let Q : (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    BHW.os45QuarterTurnCLE (d := d) (n := n)
  let Φ : BHW.OS45FlatCommonChartSpace d n ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    (flattenCLEquiv n (d + 1)).symm.trans Q.symm
  let W : Set (Fin n → Fin (d + 1) → ℂ) := Φ '' Wflat
  have hW_open : IsOpen W := by
    simpa [W] using Φ.toHomeomorph.isOpenMap Wflat hWflat_open
  have hW_pre : IsPreconnected W := by
    simpa [W] using hWflat_pre.image Φ Φ.continuous.continuousOn
  have hΦ_unflatten :
      ∀ w : BHW.OS45FlatCommonChartSpace d n,
        BHW.unflattenCfg n d w = Q (Φ w) := by
    intro w
    symm
    change
      Q (Q.symm ((flattenCLEquiv n (d + 1)).symm w)) =
        BHW.unflattenCfg n d w
    rw [Q.apply_symm_apply]
    ext k μ
    simp [BHW.unflattenCfg]
  have hseed_mem :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W := by
    refine ⟨SCV.realEmbed x0, hx0Wflat, ?_⟩
    have h := hΦ_unflatten (SCV.realEmbed x0)
    change
      Φ (SCV.realEmbed x0) =
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0))
    have hseed_eq :
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0)) =
          Φ (SCV.realEmbed x0) := by
      rw [h, Q.symm_apply_apply]
    exact hseed_eq.symm
  have hW_sub :
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    rintro z ⟨w, hw, rfl⟩
    have hdomains := hWflat_sub hw
    have hplus := hdomains.1
    have hminus := hdomains.2
    have hflat := hΦ_unflatten w
    change BHW.unflattenCfg n d w ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) at hplus
    rw [hflat] at hplus
    have hz_ET : Φ w ∈ BHW.ExtendedTube d n := by
      change
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hplus
      simpa [BHW.permAct] using hplus
    change BHW.unflattenCfg n d w ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) at hminus
    rw [hflat] at hminus
    have hz_perm :
        Φ w ∈ BHW.permutedExtendedTubeSector d n P.τ := by
      change
        BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hminus
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct, P.τ_eq]
        using hminus
    exact ⟨hz_ET, hz_perm⟩
  have hEqOn :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
    rintro z ⟨w, hw, rfl⟩
    have hflat := hΦ_unflatten w
    have heq_flat := hEqFlat hw
    have heq_pull :
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n)) (Q (Φ w)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) (Q (Φ w)) := by
      simpa [BHW.os45FlatCommonChartBranch, hflat] using heq_flat
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
            (Q.symm (Q (Φ w)))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
            (Q.symm (Q (Φ w)))) at heq_pull
    simpa [BHW.permAct, P.τ_eq] using heq_pull
  exact ⟨W, hW_open, hW_pre, hseed_mem, hW_sub, hEqOn⟩

/-- A flat local EOW equality ball gives the ambient initial-sector equality
seed at the same common-edge point. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localEOWBall
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (R0 : ℝ)
    (hR0 : 0 < R0)
    (hball_sub :
      Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0 ⊆
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) ∩
        (SCV.localEOWChart x0 ys) ⁻¹'
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
    (heq :
      Set.EqOn
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.localEOWChart x0 ys w))
        (fun w =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (SCV.localEOWChart x0 ys w))
        (Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0)) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  classical
  let A :=
    SCV.localEOWComplexAffineEquiv x0 ys hys_li
  let Wflat : Set (BHW.OS45FlatCommonChartSpace d n) :=
    A '' Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0
  have hWflat_open : IsOpen Wflat := by
    simpa [Wflat, A] using
      SCV.localEOWComplexAffineEquiv_image_open x0 ys hys_li
        (Metric.isOpen_ball)
  have hball_pre :
      IsPreconnected
        (Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0) :=
    (convex_ball (0 : BHW.OS45FlatCommonChartSpace d n) R0).isPreconnected
  have hWflat_pre : IsPreconnected Wflat := by
    simpa [Wflat, A] using
      hball_pre.image A A.continuous.continuousOn
  have hx0Wflat : SCV.realEmbed x0 ∈ Wflat := by
    refine ⟨0, Metric.mem_ball_self hR0, ?_⟩
    simp [A, SCV.localEOWChart_zero]
  have hWflat_sub :
      Wflat ⊆
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∩
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    rintro z ⟨w, hw, rfl⟩
    simpa [A] using hball_sub hw
  have hEqFlat :
      Set.EqOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        Wflat := by
    rintro z ⟨w, hw, rfl⟩
    simpa [A] using heq hw
  exact
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_eqOn_open
      (d := d) hd OS lgc (P := P)
      hWflat_open hWflat_pre x0 hx0Wflat hWflat_sub hEqFlat

/-- A local source representation of the zero horizontal common-edge
difference gives the ambient initial-sector equality seed. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) U)
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
  classical
  let x0 : BHW.OS45FlatCommonChartReal d n :=
    BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) u0
  obtain ⟨R0, hR0, hball_sub, heq⟩ :=
    BHW.os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_sourceRepresentsOn
      (d := d) hd OS lgc (P := P) hU_open hU_sub hrep
      ys hys_mem hys_li u0 hu0
  simpa [x0] using
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localEOWBall
      (d := d) hd OS lgc (P := P)
      ys hys_li x0 R0 hR0 hball_sub heq

/-- Local flat common-chart EOW equality, pulled back to the ambient
ordinary/selected-adjacent initial-sector overlap.

This is the concrete complex-open seed used by the proof-local Figure-2-4
real-Jost crossing.  It only transports the checked flat EOW seed through the
quarter-turn and flattening coordinates; it does not construct a common-boundary
CLM, a local `S'_n` branch, or an adjacent Wick trace. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {E : Set (BHW.OS45FlatCommonChartReal d n)}
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (bv : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bv x)))
    (hminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bv x)))
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  classical
  obtain ⟨Wflat, hWflat_open, hWflat_pre, hx0Wflat, hWflat_sub, hEqFlat⟩ :=
    BHW.os45_BHWJost_flatCommonChart_eqOn_open_of_continuousBoundaryOn
      (d := d) hd OS lgc (P := P) hE_open hE_sub bv hbv_cont
      hplus_bv hminus_bv x0 hx0
  let Q : (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    BHW.os45QuarterTurnCLE (d := d) (n := n)
  let Φ : BHW.OS45FlatCommonChartSpace d n ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    (flattenCLEquiv n (d + 1)).symm.trans Q.symm
  let W : Set (Fin n → Fin (d + 1) → ℂ) := Φ '' Wflat
  have hW_open : IsOpen W := by
    simpa [W] using Φ.toHomeomorph.isOpenMap Wflat hWflat_open
  have hW_pre : IsPreconnected W := by
    simpa [W] using hWflat_pre.image Φ Φ.continuous.continuousOn
  have hΦ_unflatten :
      ∀ w : BHW.OS45FlatCommonChartSpace d n,
        BHW.unflattenCfg n d w = Q (Φ w) := by
    intro w
    symm
    change
      Q (Q.symm ((flattenCLEquiv n (d + 1)).symm w)) =
        BHW.unflattenCfg n d w
    rw [Q.apply_symm_apply]
    ext k μ
    simp [BHW.unflattenCfg]
  have hseed_mem :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W := by
    refine ⟨SCV.realEmbed x0, hx0Wflat, ?_⟩
    have h := hΦ_unflatten (SCV.realEmbed x0)
    change
      Φ (SCV.realEmbed x0) =
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0))
    have hseed_eq :
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0)) =
          Φ (SCV.realEmbed x0) := by
      rw [h, Q.symm_apply_apply]
    exact hseed_eq.symm
  have hW_sub :
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    rintro z ⟨w, hw, rfl⟩
    have hdomains := hWflat_sub hw
    have hplus := hdomains.1
    have hminus := hdomains.2
    have hflat := hΦ_unflatten w
    change BHW.unflattenCfg n d w ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) at hplus
    rw [hflat] at hplus
    have hz_ET : Φ w ∈ BHW.ExtendedTube d n := by
      change
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hplus
      simpa [BHW.permAct] using hplus
    change BHW.unflattenCfg n d w ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) at hminus
    rw [hflat] at hminus
    have hz_perm :
        Φ w ∈ BHW.permutedExtendedTubeSector d n P.τ := by
      change
        BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hminus
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct, P.τ_eq]
        using hminus
    exact ⟨hz_ET, hz_perm⟩
  have hEqOn :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
    rintro z ⟨w, hw, rfl⟩
    have hflat := hΦ_unflatten w
    have heq_flat := hEqFlat hw
    have heq_pull :
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n)) (Q (Φ w)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) (Q (Φ w)) := by
      simpa [BHW.os45FlatCommonChartBranch, hflat] using heq_flat
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
            (Q.symm (Q (Φ w)))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
            (Q.symm (Q (Φ w)))) at heq_pull
    simpa [BHW.permAct, P.τ_eq] using heq_pull
  exact ⟨W, hW_open, hW_pre, hseed_mem, hW_sub, hEqOn⟩

/-- Local zero-height flat common-chart pairings give an ambient
ordinary/selected-adjacent initial-sector equality seed at the chosen flat
edge point.

This is the distributional counterpart of
`os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn`.
It consumes only the proof-local zero-height pairings on an open flat edge
window and transports the resulting local EOW ball through the OS45
quarter-turn and flattening coordinates. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {E : Set (BHW.OS45FlatCommonChartReal d n)}
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      IsPreconnected W ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  classical
  obtain ⟨R0, hR0, hball_sub, heq⟩ :=
    BHW.os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_localZeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P) E hE_open hE_sub
      ys hys_mem hys_li x0 hx0 T hzero_plus hzero_minus
  let U : Set (BHW.OS45FlatCommonChartSpace d n) :=
    Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0
  let Q : (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    BHW.os45QuarterTurnCLE (d := d) (n := n)
  let Ψ : BHW.SPrimeConfig d n ≃L[ℂ]
      BHW.OS45FlatCommonChartSpace d n :=
    Q.trans (flattenCLEquiv n (d + 1))
  let A : BHW.OS45FlatCommonChartSpace d n ≃ₜ
      BHW.OS45FlatCommonChartSpace d n :=
    SCV.localEOWComplexAffineEquiv x0 ys hys_li
  let Φ : BHW.OS45FlatCommonChartSpace d n ≃ₜ BHW.SPrimeConfig d n :=
    A.trans Ψ.symm.toHomeomorph
  let W : Set (Fin n → Fin (d + 1) → ℂ) := Φ '' U
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hW_open : IsOpen W := by
    simpa [W] using Φ.isOpenMap U hU_open
  have hU_pre : IsPreconnected U :=
    (convex_ball (0 : BHW.OS45FlatCommonChartSpace d n) R0).isPreconnected
  have hW_pre : IsPreconnected W := by
    simpa [W] using hU_pre.image Φ Φ.continuous.continuousOn
  have hΦ_flat :
      ∀ w : BHW.OS45FlatCommonChartSpace d n,
        BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) =
          Q (Φ w) := by
    intro w
    have hΨΦ_A : Ψ (Φ w) = A w := by
      change Ψ (Ψ.symm (A w)) = A w
      exact Ψ.apply_symm_apply (A w)
    have hA_apply : A w = SCV.localEOWChart x0 ys w := by
      simp [A]
    rw [← hA_apply, ← hΨΦ_A]
    ext k μ
    simp [Ψ, Q, BHW.unflattenCfg]
  have hseed_eq :
      Φ (0 : BHW.OS45FlatCommonChartSpace d n) =
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0)) := by
    have hflat0 := hΦ_flat (0 : BHW.OS45FlatCommonChartSpace d n)
    have hchart0 :
        SCV.localEOWChart x0 ys
            (0 : BHW.OS45FlatCommonChartSpace d n) =
          SCV.realEmbed x0 := by
      simpa using SCV.localEOWChart_zero x0 ys
    rw [hchart0] at hflat0
    have hseed_eq' :
        Q.symm (BHW.unflattenCfg n d (SCV.realEmbed x0)) =
          Φ (0 : BHW.OS45FlatCommonChartSpace d n) := by
      rw [hflat0, Q.symm_apply_apply]
    exact hseed_eq'.symm
  have hseed_mem :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W := by
    refine ⟨0, ?_, ?_⟩
    · simpa [U, Metric.mem_ball] using hR0
    · exact hseed_eq
  have hW_sub :
      W ⊆
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    rintro z ⟨w, hw, rfl⟩
    have hdomains := hball_sub hw
    have hplus := hdomains.1
    have hminus := hdomains.2
    have hflat := hΦ_flat w
    change BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) at hplus
    rw [hflat] at hplus
    have hz_ET : Φ w ∈ BHW.ExtendedTube d n := by
      change
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hplus
      simpa [BHW.permAct] using hplus
    change BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) at hminus
    rw [hflat] at hminus
    have hz_perm :
        Φ w ∈ BHW.permutedExtendedTubeSector d n P.τ := by
      change
        BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hminus
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct, P.τ_eq]
        using hminus
    exact ⟨hz_ET, hz_perm⟩
  have hEqOn :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
    rintro z ⟨w, hw, rfl⟩
    have hflat := hΦ_flat w
    have heq_flat := heq (x := w) hw
    have heq_pull :
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n)) (Q (Φ w)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) (Q (Φ w)) := by
      simpa [BHW.os45FlatCommonChartBranch, hflat] using heq_flat
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
            (Q.symm (Q (Φ w)))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
            (Q.symm (Q (Φ w)))) at heq_pull
    simpa [BHW.permAct, P.τ_eq] using heq_pull
  exact ⟨W, hW_open, hW_pre, hseed_mem, hW_sub, hEqOn⟩

/-- A pointwise source common-edge equality on a local source window gives the
ambient flat EOW equality seed at any point of that window.

This is the non-circular flat crossing used after the OS I `h45_source_eqOn`
step: it feeds the checked local EOW bridge with zero-height pairings obtained
directly from pointwise source equality, not from `Hdiff`, a common-boundary
CLM, or a local `S'_n` branch. -/
theorem os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hsource_eq :
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
                (1 : Equiv.Perm (Fin n)) u)))
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
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  let Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hx0 : e u0 ∈ E := ⟨u0, hu0, rfl⟩
  have hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc (P := P) Tlocal
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact (hφE.trans hE_sub)
  have hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    exact
      (BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn
        (d := d) hd OS lgc D hU_sub hsource_eq φ hφ_compact hφE).trans
        (hzero_plus φ hφ_compact hφE)
  exact
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P)
      hE_open hE_sub ys hys_mem hys_li (e u0) hx0
      Tlocal hzero_plus hzero_minus

/-- Continuous OS I §4.5 boundary values give a concrete flat common-chart
complex-open equality seed.

This is the flat real-Jost crossing used inside the direct Figure-2-4 local
transfer: the common boundary value is supplied as proof-local `(4.14)` data,
not as a downstream common-boundary CLM or local `S'_n` branch. -/
theorem os45_BHWJost_flatCommonChart_eqOn_open_of_continuousBoundary
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (bv : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbv_cont :
      ContinuousOn bv
        (BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))))
    (hplus_bv :
      ∀ x ∈ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bv x)))
    (hminus_bv :
      ∀ x ∈ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bv x)))
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n))) :
    ∃ W : Set (BHW.OS45FlatCommonChartSpace d n),
      IsOpen W ∧
      IsPreconnected W ∧
      SCV.realEmbed x0 ∈ W ∧
      W ⊆
        BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∩
        BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∧
      Set.EqOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        W := by
  classical
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  have hΩplus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (1 : Equiv.Perm (Fin n))
  have hΩminus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hE_open :
      IsOpen
        (BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  obtain ⟨hC_open, hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  have hFplus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
  have hFminus :
      DifferentiableOn ℂ
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.differentiableOn_os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hplus_nhds :
      BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n)) ∈
        nhds (SCV.realEmbed x0) := by
    exact hΩplus_open.mem_nhds
      (by
        simpa [SCV.realEmbed] using
          BHW.os45FlatCommonChart_real_mem_omega_id
            (d := d) hd (P := P) x0 hx0)
  have hminus_nhds :
      BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n))) ∈
        nhds (SCV.realEmbed x0) := by
    exact hΩminus_open.mem_nhds
      (by
        simpa [SCV.realEmbed] using
          BHW.os45FlatCommonChart_real_mem_omega_adjacent
            (d := d) hd (P := P) x0 hx0)
  exact
    SCV.local_continuous_edge_of_the_wedge_eqOn_open_at_common_edge
      (m := BHW.os45FlatCommonChartDim d n)
      hm
      (BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      (BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartCone d n)
      hΩplus_open hΩminus_open hE_open hC_open hC_conv hC_nonempty
      (BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hFplus hFminus bv hbv_cont hplus_bv hminus_bv x0 hx0
      hplus_nhds hminus_nhds

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

/-- The checked rotated adjacent lift has the same ordinary `extendF` value as
the permuted Figure-2-4 identity path.

This is only a Lorentz-normalization of the deterministic Figure-2-4 lift.  It
does not identify the `t = 0` specialization with the raw `bvt_F` adjacent
Wick branch; that is the separate OS I `(4.12)` analytic transport used in the
upstream `Hdiff` producer. -/
theorem os45Figure24AdjacentLift_extendF_eq_permActIdentityPath
    [NeZero d]
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    (t : unitInterval) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x t) =
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)) := by
  classical
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x t
  have hzlift_ET : zlift ∈ BHW.ExtendedTube d n := by
    simpa [zlift] using
      P.adjLift_mem_extendedTube x hx t
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t
  have hact :
      BHW.complexLorentzAction Λinv zlift =
        BHW.permAct (d := d) P.τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) x t) := by
    have hraw :
        BHW.complexLorentzAction Λinv zlift =
          BHW.permAct (d := d) P.τ Γ := by
      simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
        hΛinv (BHW.permAct (d := d) P.τ Γ)
    simpa [Γ] using hraw
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hLor :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λinv zlift) =
        BHW.extendF (bvt_F OS lgc n) zlift :=
    BHW.extendF_complexLorentzInvariant_of_cinv
      (d := d) n (bvt_F OS lgc n) hF_cinv Λinv zlift hzlift_ET
  calc
    BHW.extendF (bvt_F OS lgc n)
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x t)
        = BHW.extendF (bvt_F OS lgc n) zlift := by rfl
    _ = BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λinv zlift) := hLor.symm
    _ = BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)) := by
          rw [hact]

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
forward tube. -/
theorem os45Figure24_ordinaryWick_mem_forwardTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
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
  simpa using hBHW

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
  exact BHW.forwardTube_subset_extendedTube
    (BHW.os45Figure24_ordinaryWick_mem_forwardTube
      (d := d) (n := n) (hd := hd) (P := P) hx)

/-- Around an ordinary Wick endpoint there is a connected open chart inside any
prescribed open hull window on which the ordinary `(4.1)` branch
`extendF (bvt_F OS lgc n)` is available.

This is the ordinary counterpart of
`OS45BHWJostHullData.OS412SeedWindow_localChartInWindow`.  It supplies an
actual local analytic element and its Wick trace; it does not compare it with
the adjacent `(4.12)` element. -/
theorem OS45BHWJostHullData.ordinaryWick_localChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hwickW : (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      (fun k => wickRotatePoint (x k)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch (BHW.extendF (bvt_F OS lgc n)) C0 ∧
      C0branch (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x k)
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    BHW.extendF (bvt_F OS lgc n)
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨H.ordinaryWick_mem_extendedTube x hx, H.ordinaryWick_mem x hx⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using BHW.isOpen_extendedTube.inter H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hwickW⟩
  let K : Set (Fin n → Fin (d + 1) → ℂ) := {p0}
  have hK_compact : IsCompact K := by
    simp [K]
  have hK_connected : IsConnected K := by
    simpa [K] using isConnected_singleton
  have hK_sub : K ⊆ Ω0 ∩ W := by
    intro z hz
    simpa [K] using hz ▸ hp0ΩW
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ0W_open hK_sub with
    ⟨C0, hC0_open, hC0_connected, hK_C0, hC0_sub⟩
  refine ⟨C0, B0, ?_, hC0_open, hC0_connected.isPreconnected, ?_, ?_, ?_, ?_⟩
  · change p0 ∈ C0
    exact hK_C0 (by simp [K])
  · simpa [Ω0] using hC0_sub
  · exact (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).mono (by
        intro z hz
        exact (hC0_sub hz).1.1)
  · intro z hz
    rfl
  · have hF_holo :
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
    have hp0_forward : p0 ∈ BHW.ForwardTube d n := by
      simpa [p0] using
        BHW.os45Figure24_ordinaryWick_mem_forwardTube
          (d := d) (n := n) (hd := hd) (P := P) hx
    exact
      BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_lorentz p0 hp0_forward

/-- Metric-ball version of `ordinaryWick_localChartInWindow`.

The all-overlap branch-law proof needs the initial ordinary chart to carry a
stored metric-ball radius for the checked SCV overlap identity lemmas. -/
theorem OS45BHWJostHullData.ordinaryWick_metricBallChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hwickW : (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 = Metric.ball (fun k => wickRotatePoint (x k)) r ∧
      (fun k => wickRotatePoint (x k)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch (BHW.extendF (bvt_F OS lgc n)) C0 ∧
      C0branch (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x k)
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    BHW.extendF (bvt_F OS lgc n)
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨H.ordinaryWick_mem_extendedTube x hx, H.ordinaryWick_mem x hx⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using BHW.isOpen_extendedTube.inter H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hwickW⟩
  rcases Metric.mem_nhds_iff.mp (hΩ0W_open.mem_nhds hp0ΩW) with
    ⟨r, hr_pos, hball_sub⟩
  refine
    ⟨Metric.ball p0 r, B0, r, hr_pos, ?_, ?_, Metric.isOpen_ball, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · exact Metric.mem_ball_self hr_pos
  · exact (convex_ball p0 r).isPreconnected
  · simpa [p0, Ω0] using hball_sub
  · exact (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).mono (by
        intro z hz
        exact (hball_sub hz).1.1)
  · intro z hz
    rfl
  · have hF_holo :
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
    have hp0_forward : p0 ∈ BHW.ForwardTube d n := by
      simpa [p0] using
        BHW.os45Figure24_ordinaryWick_mem_forwardTube
          (d := d) (n := n) (hd := hd) (P := P) hx
    exact
      BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_lorentz p0 hp0_forward

/-- The selected adjacent swap sends the adjacent Wick edge back to the
ordinary Wick edge.  This is seed geometry for the OS I `(4.12)` transport; it
does not identify the adjacent branch value. -/
theorem os45Figure24_permAct_adjacentWick_eq_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (u : NPointDomain d n) :
    BHW.permAct (d := d) P.τ
        (fun k => wickRotatePoint (u (P.τ k))) =
      fun k => wickRotatePoint (u k) := by
  ext k μ
  simp [BHW.permAct, P.τ_eq]

/-- The selected adjacent swap sends the ordinary Wick edge to the adjacent
Wick seed used in the OS I `(4.12)` transport. -/
theorem os45Figure24_permAct_ordinaryWick_eq_adjacentWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (u : NPointDomain d n) :
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) =
      fun k => wickRotatePoint (u (P.τ k)) := by
  ext k μ
  simp [BHW.permAct]

/-- The selected Figure-2-4 adjacent transposition is nontrivial. -/
theorem OS45Figure24CanonicalSourcePatchData.tau_ne_one
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi) :
    P.τ ≠ (1 : Equiv.Perm (Fin n)) := by
  intro hτ
  have hswap : P.τ i = ⟨i.val + 1, hi⟩ := by
    rw [P.τ_eq]
    simp
  have hid : P.τ i = i := by
    rw [hτ]
    simp
  have hval : (⟨i.val + 1, hi⟩ : Fin n).val = i.val :=
    congrArg Fin.val (hswap.symm.trans hid)
  simp at hval

/-- The adjacent Wick edge lies in the concrete OS I `(4.12)` seed window:
after applying the selected adjacent swap it is in the ordinary forward tube,
and the point itself lies in the local BHW/Jost hull. -/
theorem OS45BHWJostHullData.adjacentWick_mem_OS412SeedWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x (P.τ k))) ∈
        ({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) := by
  intro x hx
  constructor
  · have hperm :=
      BHW.os45Figure24_permAct_adjacentWick_eq_ordinaryWick
        (d := d) (n := n) (hd := hd) (P := P) x
    simpa [hperm] using
      BHW.os45Figure24_ordinaryWick_mem_forwardTube
        (d := d) (n := n) (hd := hd) (P := P) hx
  · exact H.adjacentWick_mem x hx

/-- The same OS I `(4.12)` seed-window membership, phrased with the adjacent
seed written as `permAct P.τ` applied to the ordinary Wick edge. -/
theorem OS45BHWJostHullData.permAct_ordinaryWick_mem_OS412SeedWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        ({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) := by
  intro x hx
  have hseed :=
    H.adjacentWick_mem_OS412SeedWindow x hx
  have hEq :=
    BHW.os45Figure24_permAct_ordinaryWick_eq_adjacentWick
      (d := d) (n := n) (hd := hd) (P := P) x
  simpa [hEq] using hseed

/-- The ordinary Wick endpoint cannot itself be the raw OS I `(4.12)` seed
point.

The `(4.12)` seed window is the preimage of the ordinary forward tube under the
selected adjacent swap.  If the ordinary Wick endpoint lay in that window, it
would lie in both the ordinary and the selected permuted forward tubes, forcing
the adjacent swap to be trivial.  Thus the upstream `Hdiff` proof really needs
the OS-I seed-to-Wick transport; it cannot take `p0 := gamma 0` inside this
raw seed window. -/
theorem OS45BHWJostHullData.ordinaryWick_not_mem_OS412SeedWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x k)) ∉
        ({z : Fin n → Fin (d + 1) → ℂ |
          BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) := by
  intro x hx hmem
  have hFT :
      (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n :=
    BHW.os45Figure24_ordinaryWick_mem_forwardTube
      (d := d) (n := n) (hd := hd) (P := P) hx
  have hPFT :
      (fun k => wickRotatePoint (x k)) ∈
        BHW.PermutedForwardTube d n P.τ := by
    simpa [BHW.PermutedForwardTube, BHW.permAct] using hmem.1
  exact P.tau_ne_one
    (BHW.permutedForwardTube_forces_perm_one
      (d := d) (n := n) P.τ hFT hPFT)

/-- The concrete OS I `(4.12)` seed window is open. -/
theorem OS45BHWJostHullData.OS412SeedWindow_open
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    IsOpen ({z : Fin n → Fin (d + 1) → ℂ |
        BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) :=
  (BHW.isOpen_permAct_preimage_forwardTube
      (d := d) (n := n) P.τ).inter H.ΩJ_open

/-- The concrete OS I `(4.12)` seed window is contained in the selected
adjacent initial sheet of the local BHW/Jost hull. -/
theorem OS45BHWJostHullData.OS412SeedWindow_subset_permutedSector
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ({z : Fin n → Fin (d + 1) → ℂ |
        BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ _H.ΩJ) ⊆
      BHW.permutedExtendedTubeSector d n P.τ ∩ _H.ΩJ := by
  intro z hz
  constructor
  · simpa [BHW.permutedExtendedTubeSector, BHW.permAct] using
      BHW.forwardTube_subset_extendedTube (d := d) (n := n) hz.1
  · exact hz.2

/-- The concrete OS I `(4.12)` seed formula is holomorphic on its seed
window. -/
theorem OS45BHWJostHullData.differentiableOn_OS412SeedBranch
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        bvt_F OS lgc n (BHW.permAct (d := d) P.τ z))
      ({z : Fin n → Fin (d + 1) → ℂ |
        BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ _H.ΩJ) :=
  (BHW.differentiableOn_bvt_F_permAct_preimageForwardTube
      (d := d) OS lgc n P.τ).mono Set.inter_subset_left

/-- The OS I `(4.12)` seed formula evaluated at the adjacent Wick edge gives
the ordinary Wick value.  The nontrivial adjacent Wick value at the ordinary
Wick endpoint is still the later analytic-continuation trace. -/
theorem os45Figure24_OS412SeedBranch_adjacentWick_eq_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : NPointDomain d n) :
    (fun z : Fin n → Fin (d + 1) → ℂ =>
        bvt_F OS lgc n (BHW.permAct (d := d) P.τ z))
      (fun k => wickRotatePoint (x (P.τ k))) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  simp [BHW.os45Figure24_permAct_adjacentWick_eq_ordinaryWick
    (d := d) (n := n) (hd := hd) (P := P) x]

/-- The OS I `(4.12)` seed formula at the proof-local seed
`permAct P.τ` of the ordinary Wick endpoint gives the ordinary Wick value. -/
theorem os45Figure24_OS412SeedBranch_permAct_ordinaryWick_eq_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : NPointDomain d n) :
    (fun z : Fin n → Fin (d + 1) → ℂ =>
        bvt_F OS lgc n (BHW.permAct (d := d) P.τ z))
      (BHW.permAct (d := d) P.τ
        (fun k => wickRotatePoint (x k))) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  have hEq :=
    BHW.os45Figure24_permAct_ordinaryWick_eq_adjacentWick
      (d := d) (n := n) (hd := hd) (P := P) x
  simpa [hEq] using
    BHW.os45Figure24_OS412SeedBranch_adjacentWick_eq_ordinaryWick
      (d := d) (n := n) (hd := hd) (P := P) OS lgc x

/-- Around the genuine OS I `(4.12)` seed point
`permAct P.τ (wick x)`, there is a connected open chart inside any prescribed
open hull window on which the concrete `(4.12)` seed branch is available.

This is the proof-local initial chart for the adjacent one-branch
continuation.  It deliberately starts at the seed that actually belongs to the
preimage-forward-tube window; it does not put the ordinary Wick endpoint into
that raw seed window. -/
theorem OS45BHWJostHullData.OS412SeedWindow_localChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hseedW :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        ({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch (BHW.permAct (d := d) P.τ
          (fun k => wickRotatePoint (x k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z : Fin n → Fin (d + 1) → ℂ |
      BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
  have hp0Ω : p0 ∈ Ω0 := by
    simpa [p0, Ω0] using H.permAct_ordinaryWick_mem_OS412SeedWindow x hx
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using H.OS412SeedWindow_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hseedW⟩
  let K : Set (Fin n → Fin (d + 1) → ℂ) := {p0}
  have hK_compact : IsCompact K := by
    simp [K]
  have hK_connected : IsConnected K := by
    simpa [K] using isConnected_singleton
  have hK_sub : K ⊆ Ω0 ∩ W := by
    intro z hz
    simpa [K] using hz ▸ hp0ΩW
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ0W_open hK_sub with
    ⟨C0, hC0_open, hC0_connected, hK_C0, hC0_sub⟩
  refine ⟨C0, B0, ?_, hC0_open, hC0_connected.isPreconnected, ?_, ?_, ?_, ?_⟩
  · change p0 ∈ C0
    exact hK_C0 (by simp [K])
  · simpa [Ω0] using hC0_sub
  · exact (H.differentiableOn_OS412SeedBranch OS lgc).mono (by
      intro z hz
      exact (hC0_sub hz).1)
  · intro z hz
    rfl
  · have hseed_ord :
        B0 p0 =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
      simpa [B0, p0] using
        BHW.os45Figure24_OS412SeedBranch_permAct_ordinaryWick_eq_ordinaryWick
          (d := d) (n := n) (hd := hd) (P := P) OS lgc x
    have hperm :
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
      simpa [BHW.permAct] using
        bvt_F_perm (d := d) OS lgc n P.τ
          (fun k => wickRotatePoint (x k))
    exact hseed_ord.trans hperm.symm

/-- Metric-ball version of `OS412SeedWindow_localChartInWindow`.

The adjacent all-overlap gallery needs the corrected `(4.12)` initial chart to
retain the exact ball carrier used by the checked SCV identity theorem. -/
theorem OS45BHWJostHullData.OS412SeedWindow_metricBallChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hseedW :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          (BHW.permAct (d := d) P.τ
            (fun k => wickRotatePoint (x k))) r ∧
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        ({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch (BHW.permAct (d := d) P.τ
          (fun k => wickRotatePoint (x k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z : Fin n → Fin (d + 1) → ℂ |
      BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
  have hp0Ω : p0 ∈ Ω0 := by
    simpa [p0, Ω0] using H.permAct_ordinaryWick_mem_OS412SeedWindow x hx
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using H.OS412SeedWindow_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hseedW⟩
  rcases Metric.mem_nhds_iff.mp (hΩ0W_open.mem_nhds hp0ΩW) with
    ⟨r, hr_pos, hball_sub⟩
  refine
    ⟨Metric.ball p0 r, B0, r, hr_pos, ?_, ?_, Metric.isOpen_ball, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · exact Metric.mem_ball_self hr_pos
  · exact (convex_ball p0 r).isPreconnected
  · simpa [p0, Ω0] using hball_sub
  · exact (H.differentiableOn_OS412SeedBranch OS lgc).mono (by
      intro z hz
      exact (hball_sub hz).1)
  · intro z hz
    rfl
  · have hseed_ord :
        B0 p0 =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
      simpa [B0, p0] using
        BHW.os45Figure24_OS412SeedBranch_permAct_ordinaryWick_eq_ordinaryWick
          (d := d) (n := n) (hd := hd) (P := P) OS lgc x
    have hperm :
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
      simpa [BHW.permAct] using
        bvt_F_perm (d := d) OS lgc n P.τ
          (fun k => wickRotatePoint (x k))
    exact hseed_ord.trans hperm.symm

/-- The corrected OS I `(4.12)` seed point and the ordinary Wick endpoint lie
in the same checked local BHW/Jost hull component.  This is only geometric
carrier support for the seed-to-Wick transport; it does not identify branch
values. -/
theorem OS45BHWJostHullData.OS412Seed_joinedIn_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      JoinedIn H.ΩJ
        (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)))
        (fun k => wickRotatePoint (x k)) := by
  intro x hx
  have hseed :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ H.ΩJ :=
    (H.permAct_ordinaryWick_mem_OS412SeedWindow x hx).2
  have hwick : (fun k => wickRotatePoint (x k)) ∈ H.ΩJ :=
    H.ordinaryWick_mem x hx
  exact H.ΩJ_isPathConnected.joinedIn _ hseed _ hwick

/-- Adjacent Wick rotations of a checked Figure-2-4 source point lie in the
selected adjacent permuted forward tube.  This is the unfolded forward-tube
membership behind the OS I `(4.12)` trace normalization; it does not identify
the adjacent branch value. -/
theorem os45Figure24_adjacentWick_mem_permutedForwardTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) ∈
      BHW.PermutedForwardTube d n P.τ := by
  have hft_eq : BHW.ForwardTube d n = _root_.ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hroot :
      (fun k => wickRotatePoint (u ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
      (P.V_ordered u hu)
  have hBHW :
      (fun k => wickRotatePoint (u k)) ∈ BHW.ForwardTube d n := by
    simpa [hft_eq] using hroot
  simpa [BHW.PermutedForwardTube, BHW.permAct, P.τ_eq] using hBHW

/-- Applying the selected adjacent label permutation to an ordinary Wick edge
of the checked Figure-2-4 source patch lands in the ordinary extended tube.

The proof uses the `t = 0` endpoint of the checked adjacent Figure-2-4 lift
and the inverse proper-complex-Lorentz rotation of
`figure24RotateAdjacentConfig`; it is not a forward-tube normalization of the
adjacent Wick boundary value. -/
theorem os45Figure24_adjacentWick_mem_extendedTube
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) ∈
      BHW.ExtendedTube d n := by
  have hu_closure : u ∈ closure P.V := subset_closure hu
  rcases P.figPath_closure u hu_closure with
    ⟨_Γ, _hΓ_cont, _hΓ_zero, _hΓ_one, _hΓ_ET, hΔ_ET, _hgram⟩
  let Δ0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ u (0 : unitInterval)
  have hΔ0_ET : Δ0 ∈ BHW.ExtendedTube d n := by
    simpa [Δ0] using hΔ_ET (0 : unitInterval)
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  have hInv :
      BHW.complexLorentzAction Λinv Δ0 =
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) := by
    simpa [Δ0, BHW.os45Figure24AdjacentLift,
      BHW.os45Figure24IdentityPath_zero] using
      hΛinv
        (BHW.permAct (d := d) P.τ
          (BHW.os45Figure24IdentityPath
            (d := d) (n := n) u (0 : unitInterval)))
  have hact :
      BHW.complexLorentzAction Λinv Δ0 ∈ BHW.ExtendedTube d n :=
    BHW.complexLorentzAction_mem_extendedTube (d := d) n Λinv hΔ0_ET
  simpa [hInv] using hact

/-- The genuine OS I `(4.12)` seed point
`permAct P.τ (wick x)` lies in the same initial-sector overlap as the
Figure-2-4 corridor. -/
theorem OS45BHWJostHullData.OS412Seed_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  constructor
  · exact BHW.os45Figure24_adjacentWick_mem_extendedTube
      (d := d) (n := n) (hd := hd) (P := P) hx
  · exact
      (H.OS412SeedWindow_subset_permutedSector
        (H.permAct_ordinaryWick_mem_OS412SeedWindow x hx)).1

/-- The deterministic adjacent Figure-2-4 lift stays in the concrete overlap
of the ordinary extended tube with the selected adjacent sector.

This is geometric support for the OS I `(4.12)` seed-to-Wick transport: the
rotated adjacent corridor itself lies in the two initial sheets.  It does not
identify any branch values. -/
theorem os45Figure24AdjacentLift_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∀ t : unitInterval,
      BHW.os45Figure24AdjacentLift (d := d) (n := n) hd P.τ x t ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
  intro t
  constructor
  · simpa using P.adjLift_mem_extendedTube x hx t
  · let zlift : Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24AdjacentLift (d := d) (n := n) hd P.τ x t
    let Γ : Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t
    have hΓ_ET : Γ ∈ BHW.ExtendedTube d n := by
      exact BHW.forwardTube_subset_extendedTube
        (BHW.os45Figure24IdentityPath_mem_forwardTube
          (d := d) (n := n) (P.V_ordered x hx) t)
    rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
        (d := d) (n := n) hd with
      ⟨Λinv, hΛinv⟩
    have hInv :
        BHW.complexLorentzAction Λinv zlift =
          BHW.permAct (d := d) P.τ Γ := by
      simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
        hΛinv (BHW.permAct (d := d) P.τ Γ)
    have hperm_sector :
        BHW.permAct (d := d) P.τ Γ ∈
          BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct, P.τ_eq] using hΓ_ET
    have hzlift_sector :
        zlift ∈ BHW.permutedExtendedTubeSector d n P.τ :=
      (BHW.permutedExtendedTubeSector_complexLorentzAction_iff
        (d := d) (n := n) Λinv P.τ zlift).1
        (by simpa [hInv] using hperm_sector)
    simpa [zlift] using hzlift_sector

/-- The inverse Figure-2-4 Lorentz rotation joins the deterministic adjacent
lift to the permuted ordinary Figure-2-4 identity path while staying inside
the ordinary/adjacent initial-sector overlap.

This is still only corridor geometry: it certifies the two-sheet domain of the
Lorentz connector, but it does not compare branch values. -/
theorem os45Figure24_joined_adjLift_to_permActIdentityPath_initialSectorOverlap
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    (t : unitInterval) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (BHW.os45Figure24AdjacentLift (d := d) (n := n) hd P.τ x t)
      (BHW.permAct (d := d) P.τ
        (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)) := by
  classical
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift (d := d) (n := n) hd P.τ x t
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t
  have hzlift :
      zlift ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [zlift] using
      BHW.os45Figure24AdjacentLift_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) hx t
  rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
      (d := d) (n := n) hd with
    ⟨Λinv, hΛinv⟩
  have hInv :
      BHW.complexLorentzAction Λinv zlift =
        BHW.permAct (d := d) P.τ Γ := by
    simpa [zlift, BHW.os45Figure24AdjacentLift, Γ] using
      hΛinv (BHW.permAct (d := d) P.τ Γ)
  have hgrp :
      JoinedIn (Set.univ : Set (ComplexLorentzGroup d)) 1 Λinv :=
    (ComplexLorentzGroup.isPathConnected (d := d)).joinedIn
      1 (Set.mem_univ _) Λinv (Set.mem_univ _)
  refine
    ⟨{ toFun := fun s =>
          BHW.complexLorentzAction (hgrp.somePath s) zlift
       continuous_toFun :=
          (BHW.continuous_complexLorentzAction_fst
            (d := d) (n := n) zlift).comp
            hgrp.somePath.continuous_toFun
       source' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 0) zlift = zlift
          rw [hgrp.somePath.source]
          exact BHW.complexLorentzAction_one zlift
       target' := by
          change
            BHW.complexLorentzAction (hgrp.somePath 1) zlift =
              BHW.permAct (d := d) P.τ Γ
          rw [hgrp.somePath.target]
          exact hInv },
      ?_⟩
  intro s
  constructor
  · exact
      BHW.complexLorentzAction_mem_extendedTube
        (d := d) n (hgrp.somePath s) hzlift.1
  · exact
      (BHW.permutedExtendedTubeSector_complexLorentzAction_iff
        (d := d) (n := n) (hgrp.somePath s) P.τ zlift).2 hzlift.2

/-- The first adjacent Figure-2-4 corridor fragment, from the adjacent Wick
seed to the rotated lift at `0`, lies in the concrete ordinary/adjacent
initial-sector overlap. -/
theorem os45Figure24_joined_adjacentWick_to_adjLift0_initialSectorOverlap
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval)) := by
  classical
  let zlift : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24AdjacentLift
      (d := d) (n := n) hd P.τ x (0 : unitInterval)
  let zadj : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x (P.τ k))
  have hzlift :
      zlift ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [zlift] using
      BHW.os45Figure24AdjacentLift_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) hx (0 : unitInterval)
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
  constructor
  · exact
      BHW.complexLorentzAction_mem_extendedTube
        (d := d) n (hgrp.somePath t) hzlift.1
  · exact
      (BHW.permutedExtendedTubeSector_complexLorentzAction_iff
        (d := d) (n := n) (hgrp.somePath t) P.τ zlift).2 hzlift.2

/-- The rotated adjacent Figure-2-4 lift path from `0` to `1` lies in the
ordinary/adjacent initial-sector overlap. -/
theorem os45Figure24_joined_adjLift0_to_adjLift1_initialSectorOverlap
    [NeZero d]
    (hd : 2 ≤ d) {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi)
    (x : NPointDomain d n) (hx : x ∈ P.V) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (0 : unitInterval))
      (BHW.os45Figure24AdjacentLift
        (d := d) (n := n) hd P.τ x (1 : unitInterval)) := by
  refine
    ⟨{ toFun := fun t =>
          BHW.os45Figure24AdjacentLift
            (d := d) (n := n) hd P.τ x t
       continuous_toFun := by
          simpa using
            (BHW.continuous_os45Figure24AdjacentLift
              (d := d) (n := n) hd P.τ).comp
              (continuous_const.prodMk continuous_id)
       source' := rfl
       target' := rfl },
      ?_⟩
  intro t
  exact
    BHW.os45Figure24AdjacentLift_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P) hx t

/-- The checked identity Figure-2-4 path lies in the overlap of the ordinary
extended tube with the selected adjacent sector.

The ordinary component is direct forward-tube geometry.  The selected-sector
component comes from the rotated adjacent lift and the inverse
proper-complex-Lorentz rotation of `figure24RotateAdjacentConfig`. -/
theorem os45Figure24IdentityPath_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    ∀ t : unitInterval,
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
  intro t
  constructor
  · exact BHW.forwardTube_subset_extendedTube
      (BHW.os45Figure24IdentityPath_mem_forwardTube
        (d := d) (n := n) (P.closure_ordered x hx) t)
  · rcases P.figPath_closure x hx with
      ⟨_Γ, _hΓ_cont, _hΓ_zero, _hΓ_one, _hΓ_ET, hΔ_ET, _hgram⟩
    let Δ : Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24AdjacentLift (d := d) (n := n) hd P.τ x t
    have hΔ : Δ ∈ BHW.ExtendedTube d n := by
      simpa [Δ] using hΔ_ET t
    rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
        (d := d) (n := n) hd with
      ⟨Λinv, hΛinv⟩
    have hInv :
        BHW.complexLorentzAction Λinv Δ =
          BHW.permAct (d := d) P.τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) x t) := by
      simpa [Δ, BHW.os45Figure24AdjacentLift] using
        hΛinv
          (BHW.permAct (d := d) P.τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) x t))
    have hact :
        BHW.complexLorentzAction Λinv Δ ∈ BHW.ExtendedTube d n :=
      BHW.complexLorentzAction_mem_extendedTube (d := d) n Λinv hΔ
    simpa [BHW.permutedExtendedTubeSector, BHW.permAct, hInv] using hact

/-- Applying the selected adjacent transposition to the ordinary Figure-2-4
identity path again stays in the ordinary/adjacent initial-sector overlap. -/
theorem os45Figure24_permActIdentityPath_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    ∀ t : unitInterval,
      BHW.permAct (d := d) P.τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) x t) ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
  intro t
  let Γ : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t
  have hΓ :
      Γ ∈ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [Γ] using
      BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) hx t
  have hττ :
      BHW.permAct (d := d) P.τ
          (BHW.permAct (d := d) P.τ Γ) = Γ := by
    ext k μ
    simp [BHW.permAct, P.τ_eq]
  constructor
  · simpa [Γ, BHW.permutedExtendedTubeSector] using hΓ.2
  · have hdouble :
        BHW.permAct (d := d) P.τ
            (BHW.permAct (d := d) P.τ Γ) ∈
        BHW.ExtendedTube d n := by
      simpa [hττ] using hΓ.1
    simpa [BHW.permutedExtendedTubeSector, BHW.permAct, Γ] using hdouble

/-- The permuted ordinary Figure-2-4 identity path gives a two-sheet corridor
from the adjacent Wick seed to the permuted horizontal common-edge
representative. -/
theorem os45Figure24_joined_permActOrdinaryWick_to_permActCommonEdge_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)))
      (BHW.permAct (d := d) P.τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))) := by
  refine
    ⟨{ toFun := fun t =>
          BHW.permAct (d := d) P.τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) x t)
       continuous_toFun :=
          (BHW.differentiable_permAct (d := d) (n := n) P.τ).continuous.comp
            (BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x)
       source' := by
          rw [BHW.os45Figure24IdentityPath_zero]
       target' := by
          rw [BHW.os45Figure24IdentityPath_one] },
      ?_⟩
  intro t
  exact
    BHW.os45Figure24_permActIdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P) hx t

/-- The permuted horizontal common-edge endpoint lies in the concrete
ordinary/adjacent initial-sector overlap.  This names the `padj` endpoint used
by the proof-local `(4.12)` seed-to-Wick circuit; it is only carrier geometry,
not a branch-value comparison. -/
theorem os45Figure24_permActCommonEdge_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    BHW.permAct (d := d) P.τ
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))) ∈
      BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
  simpa [BHW.os45Figure24IdentityPath_one (d := d) (n := n) x] using
    BHW.os45Figure24_permActIdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P) hx (1 : unitInterval)

/-- The horizontal common-edge endpoint of the checked identity Figure-2-4
path lies in the same initial-sector overlap. -/
theorem os45Figure24_commonEdge_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x)) ∈
      BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
  simpa [BHW.os45Figure24IdentityPath_one (d := d) (n := n) x] using
    BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P) hx (1 : unitInterval)

/-- The ordinary common-edge `extendF` trace is continuous on any source window
inside the checked Figure-2-4 patch.

This is a regularity input for the proof-local `h45_source_eqOn` comparison; it
does not assert equality with the adjacent trace. -/
theorem continuousOn_os45CommonEdge_ordinary_extendF_trace
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V) :
    ContinuousOn
      (fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))) U := by
  have hbranch_cont :
      ContinuousOn (BHW.extendF (bvt_F OS lgc n))
        (BHW.ExtendedTube d n) :=
    (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).continuousOn
  have hmap_cont :
      Continuous
        (fun u : NPointDomain d n =>
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm.continuous.comp
      (BHW.continuous_realEmbed_os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))
  refine hbranch_cont.comp hmap_cont.continuousOn ?_
  intro u hu
  exact
    (BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P)
      (subset_closure (hU_sub hu))).1

/-- The selected adjacent common-edge `extendF ∘ permAct` trace is continuous
on any source window inside the checked Figure-2-4 patch.

This supplies the adjacent-side regularity for the proof-local
`h45_source_eqOn` comparison; it does not prove that comparison. -/
theorem continuousOn_os45CommonEdge_adjacent_extendF_trace
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V) :
    ContinuousOn
      (fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))))) U := by
  have hbranch_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        {z | BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n} :=
    (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
      (d := d) OS lgc n P.τ).continuousOn
  have hmap_cont :
      Continuous
        (fun u : NPointDomain d n =>
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm.continuous.comp
      (BHW.continuous_realEmbed_os45CommonEdgeRealPoint
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))
  refine hbranch_cont.comp hmap_cont.continuousOn ?_
  intro u hu
  exact
    (BHW.os45Figure24_permActCommonEdge_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P)
      (subset_closure (hU_sub hu))).1

/-- The horizontal common-edge pulled-branch difference is continuous on any
source window contained in the checked Figure-2-4 patch.

This is the regularity input needed when the local source zero representation
is assembled from compact source-window pieces; it does not assert the
distributional zero itself. -/
theorem continuousOn_os45CommonEdge_pulledRealBranchDifference_trace
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V) :
    ContinuousOn
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
  have hadj :=
    BHW.continuousOn_os45CommonEdge_adjacent_extendF_trace
      (d := d) hd OS lgc (P := P) hU_sub
  have hord :=
    BHW.continuousOn_os45CommonEdge_ordinary_extendF_trace
      (d := d) hd OS lgc (P := P) hU_sub
  simpa [BHW.os45PulledRealBranch, P.τ_eq] using hadj.sub hord

/-- The ordinary Figure-2-4 Wick-to-common-edge path lies in the concrete
ordinary/adjacent initial-sector overlap. -/
theorem os45Figure24_joined_ordinaryWick_to_commonEdge_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ closure P.V) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (fun k => wickRotatePoint (x k))
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))) := by
  refine
    ⟨{ toFun := fun t =>
          BHW.os45Figure24IdentityPath (d := d) (n := n) x t
       continuous_toFun :=
          BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
       source' := by
          simpa using BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
       target' := by
          simpa using BHW.os45Figure24IdentityPath_one (d := d) (n := n) x },
      ?_⟩
  intro t
  exact
    BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P) hx t

/-- Ordinary Wick rotations of the checked source patch lie in the initial
ordinary/adjacent sector overlap used by the Figure-2-4 corridor. -/
theorem OS45BHWJostHullData.ordinaryWick_mem_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    ∀ x, x ∈ P.V →
      (fun k => wickRotatePoint (x k)) ∈
        BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
  intro x hx
  simpa [BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x] using
    BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P)
      (subset_closure hx) (0 : unitInterval)

/-- A compact connected source window in a checked Figure-2-4 patch has an
open connected complex chart contained in the initial-sector overlap and
containing both the Wick section and the horizontal common-edge section.

This is the topology/geometry part of the local two-branch Figure-2-4 germ
producer.  It does not construct or identify branch values. -/
theorem os45Figure24_initialSectorOverlap_chartNeighborhood
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧ IsConnected Ucx ∧
      (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
      Ucx ⊆ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
  let Ωτ : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ
  let γ : (NPointDomain d n × unitInterval) →
      Fin n → Fin (d + 1) → ℂ :=
    fun p => BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2
  let K : Set (Fin n → Fin (d + 1) → ℂ) :=
    γ '' ((closure U) ×ˢ (Set.univ : Set unitInterval))
  have hdomain_compact :
      IsCompact ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hU_compact.prod isCompact_univ
  have hγ_cont : Continuous γ := by
    simpa [γ] using
      BHW.continuous_os45Figure24IdentityPath_joint (d := d) (n := n)
  have hK_compact : IsCompact K :=
    hdomain_compact.image hγ_cont
  have hclosure_connected : IsConnected (closure U) :=
    hU_connected.closure
  have hdomain_connected :
      IsConnected ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hclosure_connected.prod isConnected_univ
  have hK_connected : IsConnected K :=
    hdomain_connected.image γ hγ_cont.continuousOn
  have hΩ_open : IsOpen Ωτ :=
    BHW.isOpen_extendedTube.inter
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)
  have hKΩ : K ⊆ Ωτ := by
    rintro z ⟨p, hp, rfl⟩
    exact BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P)
      (subset_closure (hU_closure hp.1)) p.2
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ_open hKΩ with
    ⟨Ucx, hUcx_open, hUcx_connected, hK_Ucx, hUcx_Ω⟩
  refine ⟨Ucx, hUcx_open, hUcx_connected, ?_, ?_, hUcx_Ω⟩
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK : (fun k => wickRotatePoint (u k)) ∈ K := by
      refine ⟨(u, (0 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simpa [γ] using
          BHW.os45Figure24IdentityPath_zero (d := d) (n := n) u
    exact hK_Ucx hzK
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK :
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ K := by
      refine ⟨(u, (1 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simp [γ, BHW.os45Figure24IdentityPath_one (d := d) (n := n) u]
    exact hK_Ucx hzK

/-- A compact connected source window in a checked Figure-2-4 patch has an
open connected complex chart contained in the initial-sector overlap and
containing the permuted ordinary Wick section and the permuted horizontal
common-edge section.

This is the compact-chart version of the permuted ordinary corridor.  It is
still only geometry: it does not compare any branch values. -/
theorem os45Figure24_permActInitialSectorOverlap_chartNeighborhood
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧ IsConnected Ucx ∧
      (∀ u ∈ U,
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) ∈ Ucx) ∧
      Ucx ⊆ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
  let Ωτ : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ
  let γ : (NPointDomain d n × unitInterval) →
      Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.permAct (d := d) P.τ
        (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2)
  let K : Set (Fin n → Fin (d + 1) → ℂ) :=
    γ '' ((closure U) ×ˢ (Set.univ : Set unitInterval))
  have hdomain_compact :
      IsCompact ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hU_compact.prod isCompact_univ
  have hγ_cont : Continuous γ := by
    have hpath :
        Continuous (fun p : NPointDomain d n × unitInterval =>
          BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2) := by
      simpa using
        BHW.continuous_os45Figure24IdentityPath_joint (d := d) (n := n)
    exact
      (BHW.differentiable_permAct (d := d) (n := n) P.τ).continuous.comp hpath
  have hK_compact : IsCompact K :=
    hdomain_compact.image hγ_cont
  have hclosure_connected : IsConnected (closure U) :=
    hU_connected.closure
  have hdomain_connected :
      IsConnected ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hclosure_connected.prod isConnected_univ
  have hK_connected : IsConnected K :=
    hdomain_connected.image γ hγ_cont.continuousOn
  have hΩ_open : IsOpen Ωτ :=
    BHW.isOpen_extendedTube.inter
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)
  have hKΩ : K ⊆ Ωτ := by
    rintro z ⟨p, hp, rfl⟩
    exact BHW.os45Figure24_permActIdentityPath_mem_initialSectorOverlap
      (d := d) (n := n) (hd := hd) (P := P)
      (subset_closure (hU_closure hp.1)) p.2
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ_open hKΩ with
    ⟨Ucx, hUcx_open, hUcx_connected, hK_Ucx, hUcx_Ω⟩
  refine ⟨Ucx, hUcx_open, hUcx_connected, ?_, ?_, hUcx_Ω⟩
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK :
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) ∈ K := by
      refine ⟨(u, (0 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simpa [γ] using
          congrArg (BHW.permAct (d := d) P.τ)
            (BHW.os45Figure24IdentityPath_zero (d := d) (n := n) u)
    exact hK_Ucx hzK
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK :
        BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) ∈ K := by
      refine ⟨(u, (1 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simpa [γ] using
          congrArg (BHW.permAct (d := d) P.τ)
            (BHW.os45Figure24IdentityPath_one (d := d) (n := n) u)
    exact hK_Ucx hzK

/-- A compact connected source window in a checked Figure-2-4 patch has an
open connected complex chart containing the Wick and horizontal common-edge
sections, on which both the ordinary identity-path variable and its rotated
adjacent lift argument lie in the ordinary extended tube. -/
theorem os45Figure24_rotatedLift_chartNeighborhood
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧ IsConnected Ucx ∧
      (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
      Ucx ⊆
        BHW.ExtendedTube d n ∩
          {z : Fin n → Fin (d + 1) → ℂ |
            BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
              (BHW.permAct (d := d) P.τ z) ∈
                BHW.ExtendedTube d n} := by
  let Ω : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩
      {z : Fin n → Fin (d + 1) → ℂ |
        BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
          (BHW.permAct (d := d) P.τ z) ∈ BHW.ExtendedTube d n}
  let γ : (NPointDomain d n × unitInterval) →
      Fin n → Fin (d + 1) → ℂ :=
    fun p => BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2
  let K : Set (Fin n → Fin (d + 1) → ℂ) :=
    γ '' ((closure U) ×ˢ (Set.univ : Set unitInterval))
  have hdomain_compact :
      IsCompact ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hU_compact.prod isCompact_univ
  have hγ_cont : Continuous γ := by
    simpa [γ] using
      BHW.continuous_os45Figure24IdentityPath_joint (d := d) (n := n)
  have hK_compact : IsCompact K :=
    hdomain_compact.image hγ_cont
  have hclosure_connected : IsConnected (closure U) :=
    hU_connected.closure
  have hdomain_connected :
      IsConnected ((closure U) ×ˢ (Set.univ : Set unitInterval)) :=
    hclosure_connected.prod isConnected_univ
  have hK_connected : IsConnected K :=
    hdomain_connected.image γ hγ_cont.continuousOn
  have hperm_cont :
      Continuous (BHW.permAct (d := d) P.τ :
        (Fin n → Fin (d + 1) → ℂ) →
          Fin n → Fin (d + 1) → ℂ) :=
    (BHW.differentiable_permAct (d := d) (n := n) P.τ).continuous
  have hrot_cont :
      Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
            (BHW.permAct (d := d) P.τ z)) :=
    (BHW.continuous_figure24RotateAdjacentConfig
      (d := d) (n := n) hd).comp hperm_cont
  have hΩ_open : IsOpen Ω :=
    BHW.isOpen_extendedTube.inter
      (BHW.isOpen_extendedTube.preimage hrot_cont)
  have hKΩ : K ⊆ Ω := by
    rintro z ⟨p, hp, rfl⟩
    constructor
    · exact
        (BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_closure hp.1)) p.2).1
    · simpa [BHW.os45Figure24AdjacentLift] using
        P.adjLift_mem_extendedTube p.1 (hU_closure hp.1) p.2
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ_open hKΩ with
    ⟨Ucx, hUcx_open, hUcx_connected, hK_Ucx, hUcx_Ω⟩
  refine ⟨Ucx, hUcx_open, hUcx_connected, ?_, ?_, hUcx_Ω⟩
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK : (fun k => wickRotatePoint (u k)) ∈ K := by
      refine ⟨(u, (0 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simpa [γ] using
          BHW.os45Figure24IdentityPath_zero (d := d) (n := n) u
    exact hK_Ucx hzK
  · intro u hu
    have huc : u ∈ closure U := subset_closure hu
    have hzK :
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ K := by
      refine ⟨(u, (1 : unitInterval)), ?_, ?_⟩
      · exact ⟨huc, trivial⟩
      · simp [γ, BHW.os45Figure24IdentityPath_one (d := d) (n := n) u]
    exact hK_Ucx hzK

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

/-- The horizontal common-edge seed lies in the stored local BHW/Jost hull. -/
theorem OS45BHWJostHullData.commonEdgeSPrimeSeed_mem_ΩJ
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P) :
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P ∈ H.ΩJ :=
  H.extendedTube_subset_ΩJ
    (BHW.os45Figure24CommonEdgeSPrimeSeed_mem_extendedTube
      (d := d) hd)

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

/-- The flat common-chart EOW equality gives the actual local `S'_n` overlap
seed at the horizontal Figure-2-4 common edge.

The conclusion is precisely the open connected two-sector equality input
needed by `os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt`, transported
through the OS45 quarter-turn and the flattened coordinate equivalence. -/
theorem os45_BHWJost_localSPrimeEOWSeedAt_commonEdge_of_zeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧ IsPreconnected W ∧
      BHW.os45Figure24CommonEdgeSPrimeSeed d n P ∈ W ∧
      W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
        BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ ∧
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
  classical
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  obtain ⟨ys, hys_mem, hys_li⟩ :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  let x0 : BHW.OS45FlatCommonChartReal d n :=
    BHW.os45FlatCommonChartSeed d n P
      (1 : Equiv.Perm (Fin n))
  have hx0 :
      x0 ∈ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    simpa [x0] using
      BHW.os45FlatCommonChartSeed_mem_edgeSet d n P
        (1 : Equiv.Perm (Fin n))
  obtain ⟨R0, hR0, hball_sub, heq⟩ :=
    BHW.os45_BHWJost_flatCommonChart_eqOn_localEOWBall_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc
      (P := P) ys hys_mem hys_li x0 hx0 T hzero_plus hzero_minus
  let U : Set (BHW.OS45FlatCommonChartSpace d n) :=
    Metric.ball (0 : BHW.OS45FlatCommonChartSpace d n) R0
  let Q : (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ]
      (Fin n → Fin (d + 1) → ℂ) :=
    BHW.os45QuarterTurnCLE (d := d) (n := n)
  let Ψ : BHW.SPrimeConfig d n ≃L[ℂ]
      BHW.OS45FlatCommonChartSpace d n :=
    Q.trans (flattenCLEquiv n (d + 1))
  let A : BHW.OS45FlatCommonChartSpace d n ≃ₜ
      BHW.OS45FlatCommonChartSpace d n :=
    SCV.localEOWComplexAffineEquiv x0 ys hys_li
  let Φ : BHW.OS45FlatCommonChartSpace d n ≃ₜ BHW.SPrimeConfig d n :=
    A.trans Ψ.symm.toHomeomorph
  let W : Set (Fin n → Fin (d + 1) → ℂ) := Φ '' U
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hW_open : IsOpen W := by
    simpa [W] using Φ.isOpenMap U hU_open
  have hU_pre : IsPreconnected U :=
    (convex_ball (0 : BHW.OS45FlatCommonChartSpace d n) R0).isPreconnected
  have hW_pre : IsPreconnected W := by
    simpa [W] using hU_pre.image Φ Φ.continuous.continuousOn
  have hseed_eq :
      Φ (0 : BHW.OS45FlatCommonChartSpace d n) =
        BHW.os45Figure24CommonEdgeSPrimeSeed d n P := by
    have hseed :=
      BHW.os45Figure24CommonEdgeSPrimeSeed_eq_chart_zero
        (d := d) hd (P := P) (ys := ys)
    simpa [Φ, A, Ψ, Q, x0, BHW.unflattenCfg, flattenCLEquiv_symm_apply]
      using hseed
  have hseed_mem : BHW.os45Figure24CommonEdgeSPrimeSeed d n P ∈ W := by
    refine ⟨0, ?_, ?_⟩
    · simpa [U, Metric.mem_ball] using hR0
    · exact hseed_eq
  have hΦ_flat :
      ∀ w : BHW.OS45FlatCommonChartSpace d n,
        BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) =
          Q (Φ w) := by
    intro w
    have hΨΦ_A : Ψ (Φ w) = A w := by
      change Ψ (Ψ.symm (A w)) = A w
      exact Ψ.apply_symm_apply (A w)
    have hA_apply : A w = SCV.localEOWChart x0 ys w := by
      simp [A]
    rw [← hA_apply, ← hΨΦ_A]
    ext k μ
    simp [Ψ, Q, BHW.unflattenCfg]
  have hW_sub :
      W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
        BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    rintro z ⟨w, hw, rfl⟩
    have hdomains := hball_sub hw
    have hplus := hdomains.1
    have hminus := hdomains.2
    have hflat := hΦ_flat w
    change BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) at hplus
    rw [hflat] at hplus
    have hz_ET : Φ w ∈ BHW.ExtendedTube d n := by
      change
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hplus
      simpa [BHW.permAct] using hplus
    change BHW.unflattenCfg n d (SCV.localEOWChart x0 ys w) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n)
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) at hminus
    rw [hflat] at hminus
    have hz_perm :
        Φ w ∈ BHW.permutedExtendedTubeSector d n P.τ := by
      change
        BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          (Q.symm (Q (Φ w))) ∈ BHW.ExtendedTube d n at hminus
      simpa [BHW.permutedExtendedTubeSector, BHW.permAct, P.τ_eq]
        using hminus
    have hz_hull :
        Φ w ∈ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase := by
      have hzΩ : Φ w ∈ H.ΩJ :=
        H.extendedTube_subset_ΩJ hz_ET
      simpa [H.ΩJ_eq_localSPrimeTwoSectorHull] using hzΩ
    exact ⟨⟨hz_hull, hz_ET⟩, hz_perm⟩
  have hEqOn :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc n))
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        W := by
    rintro z ⟨w, hw, rfl⟩
    have hflat := hΦ_flat w
    have heq_flat := heq (x := w) hw
    have heq_pull :
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n)) (Q (Φ w)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) (Q (Φ w)) := by
      simpa [BHW.os45FlatCommonChartBranch, hflat] using heq_flat
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
            (Q.symm (Q (Φ w)))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
            (Q.symm (Q (Φ w)))) at heq_pull
    simpa [BHW.permAct, P.τ_eq] using heq_pull
  exact ⟨W, hW_open, hW_pre, hseed_mem, hW_sub, hEqOn⟩

/-- The endpoint of the ordinary Figure-2-4 path is exactly the ordinary pulled
real branch argument at the horizontal common edge. -/
theorem os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ closure P.V) :
    ∃ Γ : unitInterval → Fin n → Fin (d + 1) → ℂ,
      Continuous Γ ∧
      Γ (0 : unitInterval) = (fun k => wickRotatePoint (u k)) ∧
      Γ (1 : unitInterval) =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∧
      (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
      BHW.extendF (bvt_F OS lgc n) (Γ (1 : unitInterval)) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let y : NPointDomain d n :=
    BHW.os45CommonEdgeRealPoint (d := d) (n := n)
      (1 : Equiv.Perm (Fin n)) u
  rcases P.figPath_closure u hu with
    ⟨Γ, hΓ_cont, hΓ_zero, hΓ_one, hΓ_ET, _hΔ_ET, _hgram⟩
  refine ⟨Γ, hΓ_cont, hΓ_zero, ?_, hΓ_ET, ?_⟩
  · simpa [y] using hΓ_one
  · simp [BHW.os45PulledRealBranch, hΓ_one]

/-- Around the ordinary horizontal common-edge endpoint there is a connected
open chart inside any prescribed open hull window on which the ordinary
`(4.1)` branch is `extendF (bvt_F OS lgc n)`.

The endpoint trace is the checked Figure-2-4 ordinary pulled-real branch value.
This supplies the endpoint-centered ordinary chart for the local §4.5 gallery;
it does not compare with the adjacent endpoint branch. -/
theorem OS45BHWJostHullData.ordinaryCommonEdge_localChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch (BHW.extendF (bvt_F OS lgc n)) C0 ∧
      C0branch
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    BHW.extendF (bvt_F OS lgc n)
  have hp0_ext : p0 ∈ BHW.ExtendedTube d n := by
    have hmem :=
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) (subset_closure hu)
    simpa [p0] using hmem.1
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_ext, H.extendedTube_subset_ΩJ hp0_ext⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using BHW.isOpen_extendedTube.inter H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  let K : Set (Fin n → Fin (d + 1) → ℂ) := {p0}
  have hK_compact : IsCompact K := by
    simp [K]
  have hK_connected : IsConnected K := by
    simpa [K] using isConnected_singleton
  have hK_sub : K ⊆ Ω0 ∩ W := by
    intro z hz
    simpa [K] using hz ▸ hp0ΩW
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ0W_open hK_sub with
    ⟨C0, hC0_open, hC0_connected, hK_C0, hC0_sub⟩
  refine ⟨C0, B0, ?_, hC0_open, hC0_connected.isPreconnected, ?_, ?_, ?_, ?_⟩
  · change p0 ∈ C0
    exact hK_C0 (by simp [K])
  · simpa [Ω0] using hC0_sub
  · exact (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).mono (by
        intro z hz
        exact (hC0_sub hz).1.1)
  · intro z hz
    rfl
  · rcases
      BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P)
        (u := u) (subset_closure hu) with
      ⟨Γ, _hΓ_cont, _hΓ_zero, hΓ_one, _hΓ_ET, hΓ_trace⟩
    change
      BHW.extendF (bvt_F OS lgc n)
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))
    rw [← hΓ_one]
    exact hΓ_trace

/-- Metric-ball version of `ordinaryCommonEdge_localChartInWindow`.

This supplies the endpoint-centered ordinary horizontal chart in the exact
carrier shape needed by the local `Hdiff` overlap proof. -/
theorem OS45BHWJostHullData.ordinaryCommonEdge_metricBallChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) r ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch (BHW.extendF (bvt_F OS lgc n)) C0 ∧
      C0branch
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    BHW.extendF (bvt_F OS lgc n)
  have hp0_ext : p0 ∈ BHW.ExtendedTube d n := by
    have hmem :=
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) (subset_closure hu)
    simpa [p0] using hmem.1
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_ext, H.extendedTube_subset_ΩJ hp0_ext⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using BHW.isOpen_extendedTube.inter H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  rcases Metric.mem_nhds_iff.mp (hΩ0W_open.mem_nhds hp0ΩW) with
    ⟨r, hr_pos, hball_sub⟩
  refine
    ⟨Metric.ball p0 r, B0, r, hr_pos, ?_, ?_, Metric.isOpen_ball, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · exact Metric.mem_ball_self hr_pos
  · exact (convex_ball p0 r).isPreconnected
  · simpa [p0, Ω0] using hball_sub
  · exact (BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n).mono (by
        intro z hz
        exact (hball_sub hz).1.1)
  · intro z hz
    rfl
  · rcases
      BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P)
        (u := u) (subset_closure hu) with
      ⟨Γ, _hΓ_cont, _hΓ_zero, hΓ_one, _hΓ_ET, hΓ_trace⟩
    change
      BHW.extendF (bvt_F OS lgc n)
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))
    rw [← hΓ_one]
    exact hΓ_trace

/-- At the horizontal Figure-2-4 common edge, the ordinary endpoint is still a
forward-tube point after undoing the OS45 quarter-turn.  Hence the BHW
extension agrees there with the raw ACR/OS-II witness `bvt_F`.

This is only the ordinary plus-side normalization for the later local EOW
transfer.  It does not identify the adjacent pulled `extendF` branch with a raw
permuted Wick value. -/
theorem os45Figure24CommonEdge_ordinary_extendF_eq_bvt_F
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    BHW.extendF (bvt_F OS lgc n)
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) =
      bvt_F OS lgc n
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) := by
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
  have hforward :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈
        BHW.ForwardTube d n := by
    have hmem :=
      BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
        (P.V_ordered u hu)
    simpa [BHW.os45ACRBranchDomain] using hmem
  exact
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_lorentz
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)))
      hforward

/-- The ordinary horizontal Figure-2-4 common-edge endpoint is an ordinary
forward-tube point after undoing the OS45 quarter-turn. -/
theorem os45Figure24CommonEdge_mem_forwardTube
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈
      BHW.ForwardTube d n := by
  have hmem :=
    BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
      (P.V_ordered u hu)
  simpa [BHW.os45ACRBranchDomain] using hmem

/-- The selected permuted horizontal common-edge endpoint is not an ordinary
forward-tube point.

This is the formal obstruction to the false shortcut that would try to
normalize the adjacent horizontal branch by `extendF_eq_on_forwardTube`. -/
theorem os45Figure24_permActCommonEdge_not_mem_forwardTube
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    BHW.permAct (d := d) P.τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) ∉
      BHW.ForwardTube d n := by
  intro hperm_forward
  have hcommon_forward :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈
        BHW.ForwardTube d n :=
    BHW.os45Figure24CommonEdge_mem_forwardTube
      (d := d) (n := n) hd (P := P) hu
  have hcommon_permuted :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈
        BHW.PermutedForwardTube d n P.τ := by
    simpa [BHW.PermutedForwardTube, BHW.permAct] using hperm_forward
  have hτ_one :
      P.τ = (1 : Equiv.Perm (Fin n)) :=
    BHW.permutedForwardTube_forces_perm_one
      (d := d) (n := n) P.τ hcommon_forward hcommon_permuted
  exact (BHW.OS45Figure24CanonicalSourcePatchData.tau_ne_one
    (d := d) (n := n) P) hτ_one

/-- At the horizontal Figure-2-4 common edge, the adjacent branch obtained by
precomposing the ordinary BHW extension with the selected source permutation is
definitionally the adjacent pulled real branch.  This is only endpoint
bookkeeping; it contains no EOW, no OS symmetry, and no common-boundary
identification. -/
theorem os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (u : NPointDomain d n) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))) =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) := by
  simp [BHW.os45PulledRealBranch]

/-- Around the horizontal common-edge endpoint there is a connected open chart
on which the selected adjacent endpoint branch is
`z ↦ extendF (bvt_F OS lgc n) (permAct P.τ z)`.

This is endpoint bookkeeping for the real-Jost side of the local §4.5 gallery.
It is not the upstream `(4.12)` Wick seed and does not identify the adjacent
and ordinary endpoint branches. -/
theorem OS45BHWJostHullData.adjacentCommonEdge_localChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ z)
  have hp0_sector : p0 ∈ BHW.permutedExtendedTubeSector d n P.τ := by
    exact
      (BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure hu)).2
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_sector, H.permutedExtendedTubeSector_subset_ΩJ hp0_sector⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ).inter
        H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  let K : Set (Fin n → Fin (d + 1) → ℂ) := {p0}
  have hK_compact : IsCompact K := by
    simp [K]
  have hK_connected : IsConnected K := by
    simpa [K] using isConnected_singleton
  have hK_sub : K ⊆ Ω0 ∩ W := by
    intro z hz
    simpa [K] using hz ▸ hp0ΩW
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ0W_open hK_sub with
    ⟨C0, hC0_open, hC0_connected, hK_C0, hC0_sub⟩
  refine ⟨C0, B0, ?_, hC0_open, hC0_connected.isPreconnected, ?_, ?_, ?_, ?_⟩
  · change p0 ∈ C0
    exact hK_C0 (by simp [K])
  · simpa [Ω0] using hC0_sub
  · exact
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          exact (hC0_sub hz).1.1)
  · intro z hz
    rfl
  · change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))
    exact
      BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P) u

/-- Metric-ball version of `adjacentCommonEdge_localChartInWindow`.

This supplies the endpoint-centered adjacent horizontal chart in the exact
carrier shape needed by the local `Hdiff` overlap proof. -/
theorem OS45BHWJostHullData.adjacentCommonEdge_metricBallChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) r ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆ (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ
  let B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ z)
  have hp0_sector : p0 ∈ BHW.permutedExtendedTubeSector d n P.τ := by
    exact
      (BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure hu)).2
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_sector, H.permutedExtendedTubeSector_subset_ΩJ hp0_sector⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ).inter
        H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  rcases Metric.mem_nhds_iff.mp (hΩ0W_open.mem_nhds hp0ΩW) with
    ⟨r, hr_pos, hball_sub⟩
  refine
    ⟨Metric.ball p0 r, B0, r, hr_pos, ?_, ?_, Metric.isOpen_ball, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · exact Metric.mem_ball_self hr_pos
  · exact (convex_ball p0 r).isPreconnected
  · simpa [p0, Ω0] using hball_sub
  · exact
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          exact (hball_sub hz).1.1)
  · intro z hz
    rfl
  · change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))
    exact
      BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P) u

/-- Around the horizontal common-edge endpoint there is a connected open chart
on which the terminal adjacent-minus-ordinary difference is the literal
difference of the selected adjacent endpoint branch and the ordinary endpoint
branch.

This is endpoint trace data for the local `Hdiff` producer.  It does not prove
or assume the missing `h45_source_eqOn` comparison; it only supplies the
holomorphic local difference and its pulled-real endpoint formula. -/
theorem OS45BHWJostHullData.commonEdgeDifference_localChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (D0 : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        ((BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ D0 C0 ∧
      Set.EqOn D0
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z) C0 ∧
      D0
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
                (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    (BHW.ExtendedTube d n ∩
      BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ
  let D0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) -
        BHW.extendF (bvt_F OS lgc n) z
  have hp0_overlap :
      p0 ∈ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [p0] using
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure hu)
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_overlap, H.extendedTube_subset_ΩJ hp0_overlap.1⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using
      (BHW.isOpen_extendedTube.inter
        (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)).inter
        H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  let K : Set (Fin n → Fin (d + 1) → ℂ) := {p0}
  have hK_compact : IsCompact K := by
    simp [K]
  have hK_connected : IsConnected K := by
    simpa [K] using isConnected_singleton
  have hK_sub : K ⊆ Ω0 ∩ W := by
    intro z hz
    simpa [K] using hz ▸ hp0ΩW
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  rcases SCV.exists_open_connected_neighborhood_of_compact_connected_subset_open
      (E := Fin n → Fin (d + 1) → ℂ)
      hK_compact hK_connected hΩ0W_open hK_sub with
    ⟨C0, hC0_open, hC0_connected, hK_C0, hC0_sub⟩
  refine ⟨C0, D0, ?_, hC0_open, hC0_connected.isPreconnected,
    ?_, ?_, ?_, ?_⟩
  · change p0 ∈ C0
    exact hK_C0 (by simp [K])
  · simpa [Ω0] using hC0_sub
  · have hAdj :
        DifferentiableOn ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z)) C0 :=
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          exact (hC0_sub hz).1.1.2)
    have hOrd :
        DifferentiableOn ℂ
          (BHW.extendF (bvt_F OS lgc n)) C0 :=
      (BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n).mono (by
          intro z hz
          exact (hC0_sub hz).1.1.1)
    simpa [D0] using hAdj.sub hOrd
  · intro z hz
    rfl
  · have hAdj :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ p0) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simpa [p0] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have hOrd :
        BHW.extendF (bvt_F OS lgc n) p0 =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simp [BHW.os45PulledRealBranch, p0]
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ p0) -
        BHW.extendF (bvt_F OS lgc n) p0 =
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
    rw [hAdj, hOrd]

/-- Metric-ball version of `commonEdgeDifference_localChartInWindow`.

This supplies the endpoint-centered horizontal difference chart in the exact
carrier shape needed by the local `Hdiff` gluing proof. -/
theorem OS45BHWJostHullData.commonEdgeDifference_metricBallChartInWindow
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {u : NPointDomain d n} (hu : u ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ W) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (D0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) r ∧
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        ((BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ) ∩ W ∧
      DifferentiableOn ℂ D0 C0 ∧
      Set.EqOn D0
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z) C0 ∧
      D0
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
                (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  let Ω0 : Set (Fin n → Fin (d + 1) → ℂ) :=
    (BHW.ExtendedTube d n ∩
      BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ
  let D0 : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) -
        BHW.extendF (bvt_F OS lgc n) z
  have hp0_overlap :
      p0 ∈ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    simpa [p0] using
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure hu)
  have hp0Ω : p0 ∈ Ω0 := by
    exact ⟨hp0_overlap, H.extendedTube_subset_ΩJ hp0_overlap.1⟩
  have hΩ0_open : IsOpen Ω0 := by
    simpa [Ω0] using
      (BHW.isOpen_extendedTube.inter
        (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)).inter
        H.ΩJ_open
  have hΩ0W_open : IsOpen (Ω0 ∩ W) := hΩ0_open.inter hW_open
  have hp0ΩW : p0 ∈ Ω0 ∩ W := ⟨hp0Ω, by simpa [p0] using hcommonW⟩
  rcases Metric.mem_nhds_iff.mp (hΩ0W_open.mem_nhds hp0ΩW) with
    ⟨r, hr_pos, hball_sub⟩
  refine
    ⟨Metric.ball p0 r, D0, r, hr_pos, ?_, ?_, Metric.isOpen_ball, ?_,
      ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · exact Metric.mem_ball_self hr_pos
  · exact (convex_ball p0 r).isPreconnected
  · simpa [p0, Ω0] using hball_sub
  · have hAdj :
        DifferentiableOn ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z)) (Metric.ball p0 r) :=
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          exact (hball_sub hz).1.1.2)
    have hOrd :
        DifferentiableOn ℂ
          (BHW.extendF (bvt_F OS lgc n)) (Metric.ball p0 r) :=
      (BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n).mono (by
          intro z hz
          exact (hball_sub hz).1.1.1)
    simpa [D0] using hAdj.sub hOrd
  · intro z hz
    rfl
  · have hAdj :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ p0) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simpa [p0] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have hOrd :
        BHW.extendF (bvt_F OS lgc n) p0 =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simp [BHW.os45PulledRealBranch, p0]
    change
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ p0) -
        BHW.extendF (bvt_F OS lgc n) p0 =
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
    rw [hAdj, hOrd]

/-- The endpoint of the deterministic rotated adjacent Figure-2-4 lift has
the adjacent pulled-real `extendF` trace at the horizontal common edge. -/
theorem os45Figure24AdjacentLift_endpoint_extendF_eq_adjacentPulledRealBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {u : NPointDomain d n} (hu : u ∈ P.V) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ u (1 : unitInterval)) =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u)) := by
  have hLift :=
    BHW.os45Figure24AdjacentLift_extendF_eq_permActIdentityPath
      (d := d) (n := n) hd OS lgc P hu (1 : unitInterval)
  have hCommon :=
    BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
      (d := d) (n := n) hd OS lgc (P := P) u
  exact hLift.trans (by
    simpa [BHW.os45Figure24IdentityPath_one (d := d) (n := n) u] using
      hCommon)

/-- The endpoint of the oriented Figure-2-4 adjacent lift represents the same
`extendF` value as the adjacent pulled real branch at the horizontal common
edge.  This is the endpoint bookkeeping used inside the OS I §4.5
common-boundary source pairing: the path `Δ` comes from the checked oriented
Figure-2-4 packet, while the equality of endpoint branch values is the checked
Hall-Wightman source branch law on equal oriented source invariants. -/
theorem os45Figure24OrientedPath_endpoint_extendF_eq_adjacentPulledRealBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hP_oriented :
      ∀ x, x ∈ closure P.V →
        BHW.OS45Figure24OrientedPathField (d := d) n i hi x)
    {u : NPointDomain d n} (hu : u ∈ closure P.V) :
    ∃ Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ,
      Continuous Γ ∧
      Continuous Δ ∧
      Γ (0 : unitInterval) = (fun k => wickRotatePoint (u k)) ∧
      Γ (1 : unitInterval) =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∧
      (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
      (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
      BHW.extendF (bvt_F OS lgc n) (Δ (1 : unitInterval)) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  classical
  let τswap : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let y : NPointDomain d n :=
    BHW.os45CommonEdgeRealPoint (d := d) (n := n)
      (1 : Equiv.Perm (Fin n)) u
  have hpath := hP_oriented u hu
  dsimp [BHW.OS45Figure24OrientedPathField, τswap, y] at hpath
  rcases hpath with
    ⟨Γ, Δ, hΓ_cont, hΔ_cont, hΓ_zero, hΓ_one, hΓ_ET, hΔ_ET,
      hΔ_inv⟩
  refine ⟨Γ, Δ, hΓ_cont, hΔ_cont, hΓ_zero, ?_, hΓ_ET, hΔ_ET, ?_⟩
  · simpa [y] using hΓ_one
  · have hF_holo :
        DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using
        bvt_F_holomorphic (d := d) OS lgc n
    have hF_cinv :
        ∀ (Λ : ComplexLorentzGroup d)
          (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ForwardTube d n →
          BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
          bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
            bvt_F OS lgc n z := by
      intro Λ z hz hΛz
      exact bvt_F_complexLorentzInvariant_forwardTube
        (d := d) OS lgc n Λ z
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
    let w : Fin n → Fin (d + 1) → ℂ :=
      BHW.permAct (d := d) P.τ (Γ (1 : unitInterval))
    have hw_ET : w ∈ BHW.ExtendedTube d n := by
      have hpulled := P.closure_pulled_tau u hu
      have hσ :
          P.τ.symm = P.τ := by
        rw [P.τ_eq]
        ext k
        simp
      change
        BHW.permAct (d := d) P.τ.symm
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed y)) ∈ BHW.ExtendedTube d n at hpulled
      rw [hσ] at hpulled
      simpa [w, y, hΓ_one] using hpulled
    have hτswap_eq : τswap = P.τ := by
      simpa [τswap] using P.τ_eq.symm
    have hinv :
        BHW.sourceOrientedMinkowskiInvariant d n (Δ (1 : unitInterval)) =
          BHW.sourceOrientedMinkowskiInvariant d n w := by
      calc
        BHW.sourceOrientedMinkowskiInvariant d n (Δ (1 : unitInterval))
            =
          BHW.sourcePermuteOrientedGram d n τswap
            (BHW.sourceOrientedMinkowskiInvariant d n
              (Γ (1 : unitInterval))) := hΔ_inv (1 : unitInterval)
        _ =
          BHW.sourcePermuteOrientedGram d n P.τ
            (BHW.sourceOrientedMinkowskiInvariant d n
              (Γ (1 : unitInterval))) := by
            simp [hτswap_eq]
        _ =
          BHW.sourceOrientedMinkowskiInvariant d n w := by
            simpa [w] using
              (BHW.sourceOrientedMinkowskiInvariant_permAct
                (d := d) (n := n) P.τ
                (Γ (1 : unitInterval))).symm
    have hbranch :
        BHW.extendF (bvt_F OS lgc n) (Δ (1 : unitInterval)) =
          BHW.extendF (bvt_F OS lgc n) w :=
      BHW.extendedTube_same_sourceOrientedInvariant_extendF_eq
        (d := d) hd n (bvt_F OS lgc n) hF_holo hF_cinv
        (hΔ_ET (1 : unitInterval)) hw_ET hinv
    have hpull :
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed y) =
          BHW.extendF (bvt_F OS lgc n) w := by
      simp [BHW.os45PulledRealBranch, w, y, hΓ_one]
    exact hbranch.trans hpull.symm

/-- The Wick-anchor branch difference integrates to zero on the canonical
Figure-2-4 source patch.  This is just the checked Euclidean E3 edge theorem
rewritten into difference-integral form; the horizontal common-edge transfer is
the later OS I §4.5 germ step. -/
theorem os45CommonEdge_wickDifference_integral_zero_of_E3
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφP : tsupport (φ : NPointDomain d n → ℂ) ⊆ P.V) :
    ∫ u : NPointDomain d n,
      (bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) -
        bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * φ u = 0 := by
  classical
  have hint_adj :
      Integrable
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) * φ u) :=
    BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
      (d := d) OS lgc n P.V P.V_open P.V_ordered P.τ
      φ hφ_compact hφP
  have hint_ord :
      Integrable
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u) :=
    BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector
      (d := d) OS lgc n P.V P.V_open P.V_ordered φ hφ_compact hφP
  have hV_swap_ordered :
      ∀ x ∈ P.V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm *
              (1 : Equiv.Perm (Fin n))) := by
    intro x hx
    simpa [P.τ_eq] using P.V_swap_ordered x hx
  have hpair_swap :=
    BHW.os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
      (d := d) OS lgc n i hi P.V P.V_jost
      (1 : Equiv.Perm (Fin n)) P.V_ordered hV_swap_ordered φ hφP
  have hpair :
      ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) * φ u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u := by
    simpa [P.τ_eq] using hpair_swap
  calc
    ∫ u : NPointDomain d n,
        (bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * φ u
        =
      (∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) * φ u) -
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u := by
        simpa [sub_mul] using
          (MeasureTheory.integral_sub hint_adj hint_ord)
    _ = 0 := sub_eq_zero.mpr hpair

/-- The Wick-side ordinary and adjacent traces agree pointwise on any local
source window inside the canonical Figure-2-4 patch.

This is the Lean extraction of the Wick seed used before the finite
Figure-2-4 analytic-continuation gallery.  It is deliberately only a Wick
edge statement; it does not identify the horizontal common-edge branches. -/
theorem os45CommonEdge_wickTraces_eqOn_of_E3
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V) :
    Set.EqOn
      (fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))))
      (fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u k))) U := by
  classical
  let Gadj : NPointDomain d n → ℂ :=
    fun u => bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))
  let Gord : NPointDomain d n → ℂ :=
    fun u => bvt_F OS lgc n (fun k => wickRotatePoint (u k))
  have hF_cont :
      ContinuousOn (bvt_F OS lgc n) (_root_.ForwardTube d n) :=
    (bvt_F_holomorphic OS lgc n).continuousOn
  have hGord_cont : ContinuousOn Gord U := by
    refine hF_cont.comp
      (BHW.continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact
      wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n))
        (P.V_ordered x (hU_sub hx))
  have hGadj_eq_Gord : Set.EqOn Gadj Gord U := by
    intro u _hu
    simpa [Gadj, Gord, BHW.permAct] using
      bvt_F_perm (d := d) OS lgc n P.τ
        (fun k => wickRotatePoint (u k))
  have hGadj_cont : ContinuousOn Gadj U :=
    hGord_cont.congr fun u hu => hGadj_eq_Gord hu
  have hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n, Gadj u * φ u =
          ∫ u : NPointDomain d n, Gord u * φ u := by
    intro φ hφ_compact hφU
    have hφP : tsupport (φ : NPointDomain d n → ℂ) ⊆ P.V :=
      fun u hu => hU_sub (hφU hu)
    have hint_adj :
        Integrable (fun u : NPointDomain d n => Gadj u * φ u) := by
      simpa [Gadj] using
        BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
          (d := d) OS lgc n P.V P.V_open P.V_ordered P.τ
          φ hφ_compact hφP
    have hint_ord :
        Integrable (fun u : NPointDomain d n => Gord u * φ u) := by
      simpa [Gord] using
        BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector
          (d := d) OS lgc n P.V P.V_open P.V_ordered
          φ hφ_compact hφP
    have hzero :=
      BHW.os45CommonEdge_wickDifference_integral_zero_of_E3
        (d := d) hd OS lgc (P := P) φ hφ_compact hφP
    have hsub :
        ∫ u : NPointDomain d n, (Gadj u - Gord u) * φ u =
          (∫ u : NPointDomain d n, Gadj u * φ u) -
            ∫ u : NPointDomain d n, Gord u * φ u := by
      simpa [Gadj, Gord, sub_mul] using
        (MeasureTheory.integral_sub hint_adj hint_ord)
    exact sub_eq_zero.mp (hsub ▸ hzero)
  simpa [Gadj, Gord] using
    SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      (U := U) hU_open hGadj_cont hGord_cont hint

/-- A Wick-side E3 seed promotes to equality on any connected complex chart
once the two local analytic germs have the ordinary `(4.1)` and genuine
adjacent `(4.12)` Wick traces.

This is the first complex-open seed used in the Figure-2-4 gallery.  It does
not identify the horizontal common-edge endpoint branches; that still requires
the local OS I §4.5 continuation through the checked Figure-2-4 corridor. -/
theorem os45CommonEdge_complexWickSeed_eqOn_of_E3
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (Ford Fadj : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hFord_holo : DifferentiableOn ℂ Ford Ucx)
    (hFadj_holo : DifferentiableOn ℂ Fadj Ucx)
    (hFord_wick :
      ∀ u ∈ U,
        Ford (fun k => wickRotatePoint (u k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)))
    (hFadj_wick :
      ∀ u ∈ U,
        Fadj (fun k => wickRotatePoint (u k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))) :
    Set.EqOn Fadj Ford Ucx := by
  classical
  have hwick_eq :
      Set.EqOn
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))))
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u k))) U :=
    BHW.os45CommonEdge_wickTraces_eqOn_of_E3
      (d := d) hd OS lgc (P := P) hU_open hU_sub
  refine
    eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
      (d := d) (n := n)
      Ucx U hUcx_open hUcx_connected hU_open hU_nonempty
      hwick_mem Fadj Ford hFadj_holo hFord_holo ?_
  intro φ _hφ_compact hφU
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  by_cases hu : u ∈ U
  · calc
      Fadj (fun k => wickRotatePoint (u k)) * φ u
          =
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) * φ u := by
          rw [hFadj_wick u hu]
      _ =
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u := by
          exact congrArg (fun c : ℂ => c * φ u) (hwick_eq hu)
      _ =
        Ford (fun k => wickRotatePoint (u k)) * φ u := by
          exact congrArg (fun c : ℂ => c * φ u) (hFord_wick u hu).symm
  · have hφ_zero : φ u = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hφ_supp => hu (hφU hφ_supp))
    simp [hφ_zero]

/-- Branch-trace form of the local Figure-2-4 horizontal difference germ.

Given the ordinary `(4.1)` local branch and the genuine adjacent `(4.12)`
local branch on the same complex chart, E3 supplies the Wick-side
compact-test pairing of their difference.  The common-edge trace hypotheses
then identify the horizontal value of `Fadj - Ford` with the
adjacent-minus-ordinary pulled real branches.

This is a proof-body step for the active Path 2 `Hdiff` input shape: it
discharges the `wick_pairing_zero` and `common_trace` fields from concrete
branch traces, leaving only the actual OS-I branch construction/gluing as the
remaining analytic work. -/
theorem os45CommonEdge_HdiffGerm_data_of_E3_branchTraces
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V)
    {Ucx : Set (Fin n → Fin (d + 1) → ℂ)}
    (Ford Fadj : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hFord_holo : DifferentiableOn ℂ Ford Ucx)
    (hFadj_holo : DifferentiableOn ℂ Fadj Ucx)
    (hFord_wick :
      ∀ u ∈ U,
        Ford (fun k => wickRotatePoint (u k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)))
    (hFadj_wick :
      ∀ u ∈ U,
        Fadj (fun k => wickRotatePoint (u k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))))
    (hFord_common :
      ∀ u ∈ U,
        Ford
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))
    (hFadj_common :
      ∀ u ∈ U,
        Fadj
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) :
    ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
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
  refine ⟨fun z => Fadj z - Ford z, ?_, ?_, ?_⟩
  · exact hFadj_holo.sub hFord_holo
  · intro φ hφ_compact hφU
    have hφP : tsupport (φ : NPointDomain d n → ℂ) ⊆ P.V :=
      fun u hu => hU_sub (hφU hu)
    have hzero :=
      BHW.os45CommonEdge_wickDifference_integral_zero_of_E3
        (d := d) hd OS lgc (P := P) φ hφ_compact hφP
    calc
      ∫ u : NPointDomain d n,
          (Fadj (fun k => wickRotatePoint (u k)) -
              Ford (fun k => wickRotatePoint (u k))) * φ u
          =
        ∫ u : NPointDomain d n,
          (bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) -
              bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * φ u := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · change
              (Fadj (fun k => wickRotatePoint (u k)) -
                  Ford (fun k => wickRotatePoint (u k))) * φ u =
                (bvt_F OS lgc n
                    (fun k => wickRotatePoint (u (P.τ k))) -
                  bvt_F OS lgc n
                    (fun k => wickRotatePoint (u k))) * φ u
            rw [hFadj_wick u hu, hFord_wick u hu]
          · have hφ_zero : φ u = 0 :=
              image_eq_zero_of_notMem_tsupport
                (fun hφ_supp => hu (hφU hφ_supp))
            simp [hφ_zero]
      _ = 0 := hzero
  · intro u hu
    change
      Fadj
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))) -
        Ford
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
                (1 : Equiv.Perm (Fin n)) u))
    rw [hFadj_common u hu, hFord_common u hu]

/-- A local Figure-2-4 holomorphic difference germ whose Wick trace has zero
distributional pairing represents the zero distribution on the horizontal
common edge.  This is the checked identity-theorem reducer; the actual OS I
§4.5 work is the production of the germ hypotheses. -/
theorem os45CommonEdge_localHorizontalDifference_representsZero_of_germ
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (Ucx : Set (Fin n → Fin (d + 1) → ℂ))
    (Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
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
                  (1 : Equiv.Perm (Fin n)) u))) :
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
      (fun u =>
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
  classical
  let Ghoriz : NPointDomain d n → ℂ :=
    fun u =>
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
  have hHdiff_zero : Set.EqOn Hdiff (fun _ => 0) Ucx := by
    refine
      eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
        (d := d) (n := n)
        Ucx U hUcx_open hUcx_connected hU_open hU_nonempty
        hwick_mem Hdiff (fun _ => 0) hHdiff_holo
        (differentiableOn_const (c := (0 : ℂ))) ?_
    intro φ hφ_compact hφ_suppU
    calc
      ∫ u : NPointDomain d n,
          Hdiff (fun k => wickRotatePoint (u k)) * φ u
          = 0 := hwick_pairing_zero φ hφ_compact hφ_suppU
      _ = ∫ u : NPointDomain d n, (0 : ℂ) * φ u := by simp
  intro φ hφU
  have hpoint :
      ∀ u ∈ U, Ghoriz u = 0 := by
    intro u hu
    exact (hcommon_trace u hu).symm.trans
      (hHdiff_zero (hcommon_mem u hu))
  calc
    (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ) φ
        = ∫ u : NPointDomain d n, (0 : ℂ) * φ u := by simp
    _ = ∫ u : NPointDomain d n, Ghoriz u * φ u := by
        exact
          (BHW.integral_eq_of_tsupport_subset_of_pointwise_on
            (d := d) (n := n) U Ghoriz (fun _ => 0) φ hφU.2
            hpoint).symm

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

/-- Once a local EOW seed has been produced at an actual point of the
two-sector `S'_n` overlap, the authorized neutral local BHW theorem
mechanically produces the single reference branch on the checked OS45 local
hull. -/
noncomputable def os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (zseed : Fin n → Fin (d + 1) → ℂ)
    (hzseed :
      zseed ∈ H.ΩJ ∩ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ)
    (hEOW_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ IsPreconnected W ∧
        zseed ∈ W ∧
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
      zseed ∈
        BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [hΩ] using hzseed.1.1
    · exact hzseed.1.2
    · exact hzseed.2
  have hEOW_seed' :
      ∃ W : Set (BHW.SPrimeConfig d n),
        IsOpen W ∧ IsPreconnected W ∧
        zseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn Ford Fadj W := by
    simpa [Ford, Fadj] using hEOW_seed
  let hbranch :=
    BHW.localSPrime_twoSectorBranch_of_EOW_BHW
      (d := d) hd P.τ H.zbase zseed
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
