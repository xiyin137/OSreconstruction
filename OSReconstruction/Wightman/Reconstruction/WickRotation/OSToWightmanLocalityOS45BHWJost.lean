import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Compact

/-!
# OS45 BHW/Jost source-patch carriers

This file starts the direct OS I section 4.5 BHW/Jost carrier layer for the
theorem-2 locality route.  It contains only data surfaces and algebraic
bookkeeping after the analytic continuation data has been supplied.
-/

noncomputable section

open Complex Topology MeasureTheory

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- Pair of ordinary/adjacent BHW-Jost branches on one selected OS45 source
patch hull.

The carrier records exactly the data needed before subtracting the two
branches: both branches are holomorphic on the same connected domain, both
match their Wick traces on the selected Wick real section, and both match the
ordinary `extendF` real traces on the selected source real section. -/
structure OS45SourcePatchBHWJostPairData
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n)) where
  τ : Equiv.Perm (Fin n)
  τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
  U : Set (Fin n → Fin (d + 1) → ℂ)
  V_open : IsOpen V
  V_nonempty : V.Nonempty
  U_open : IsOpen U
  U_connected : IsConnected U
  wick_mem :
    ∀ x, x ∈ V → (fun k => wickRotatePoint (x k)) ∈ U
  real_mem :
    ∀ x, x ∈ V → BHW.realEmbed x ∈ U
  Bord : (Fin n → Fin (d + 1) → ℂ) → ℂ
  Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ
  Bord_holo : DifferentiableOn ℂ Bord U
  Btau_holo : DifferentiableOn ℂ Btau U
  Bord_wick_trace :
    ∀ x, x ∈ V →
      Bord (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  Btau_wick_trace :
    ∀ x, x ∈ V →
      Btau (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))
  Bord_real_trace :
    ∀ x, x ∈ V →
      Bord (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
  Btau_real_trace :
    ∀ x, x ∈ V →
      Btau (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (τ k)))

namespace OS45SourcePatchBHWJostPairData

variable {hd : 2 ≤ d}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {i : Fin n} {hi : i.val + 1 < n}
variable {V : Set (NPointDomain d n)}

/-- Restrict a BHW/Jost pair carrier to a smaller real source patch while
keeping the same complex hull and branches. -/
def restrict
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (W : Set (NPointDomain d n))
    (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty)
    (hW_subset : W ⊆ V) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi W where
  τ := P.τ
  τ_eq := P.τ_eq
  U := P.U
  V_open := hW_open
  V_nonempty := hW_nonempty
  U_open := P.U_open
  U_connected := P.U_connected
  wick_mem := fun x hx => P.wick_mem x (hW_subset hx)
  real_mem := fun x hx => P.real_mem x (hW_subset hx)
  Bord := P.Bord
  Btau := P.Btau
  Bord_holo := P.Bord_holo
  Btau_holo := P.Btau_holo
  Bord_wick_trace := fun x hx => P.Bord_wick_trace x (hW_subset hx)
  Btau_wick_trace := fun x hx => P.Btau_wick_trace x (hW_subset hx)
  Bord_real_trace := fun x hx => P.Bord_real_trace x (hW_subset hx)
  Btau_real_trace := fun x hx => P.Btau_real_trace x (hW_subset hx)

/-- Restrict a BHW/Jost pair carrier to the canonical Figure-2-4 source
patch. -/
def restrict_figure24SourcePatch
    (hd : 2 ≤ d)
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi
        (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) :=
  P.restrict
    (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
    (BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi)
    (BHW.nonempty_os45Figure24SourcePatch (d := d) hd n i hi)
    hsource_subset

/-- Difference branch attached to a BHW/Jost pair carrier. -/
def difference
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z => P.Btau z - P.Bord z

/-- The difference branch is holomorphic on the selected hull. -/
theorem difference_holo
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V) :
    DifferentiableOn ℂ P.difference P.U :=
  P.Btau_holo.sub P.Bord_holo

/-- Wick trace formula for the difference branch. -/
theorem difference_wick_trace
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    {x : NPointDomain d n} (hx : x ∈ V) :
    P.difference (fun k => wickRotatePoint (x k)) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  simp [difference, P.Btau_wick_trace x hx, P.Bord_wick_trace x hx]

/-- Real trace formula for the difference branch. -/
theorem difference_real_trace
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    {x : NPointDomain d n} (hx : x ∈ V) :
    P.difference (BHW.realEmbed x) =
      BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (P.τ k))) -
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  simp [difference, P.Btau_real_trace x hx, P.Bord_real_trace x hx]

end OS45SourcePatchBHWJostPairData

/-- If the BHW/Jost pair's abstract difference branch vanishes
distributionally on tests supported in its real source patch, then the explicit
`extendF` real source-branch difference vanishes on those same tests.

The only support argument is that a Schwartz test with `tsupport ⊆ V` is zero
outside `V`, so the pair's real-trace formula may be used under the integral. -/
theorem realSourceBranchDifference_zero_of_pairData_difference_zero
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            P.difference (BHW.realEmbed u) * ψ u = 0) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
      ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (P.τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0 := by
  intro ψ hψ_comp hψ_supp
  have hint :
      (∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (P.τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u)
        =
      ∫ u : NPointDomain d n,
          P.difference (BHW.realEmbed u) * ψ u := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ V
    · change
        (BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (P.τ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u =
          P.difference (BHW.realEmbed u) * ψ u
      rw [P.difference_real_trace hu]
    · have hψ_zero : ψ u = 0 := by
        have hnot :
            u ∉ tsupport (ψ : NPointDomain d n → ℂ) :=
          fun hu_supp => hu (hψ_supp hu_supp)
        exact image_eq_zero_of_notMem_tsupport hnot
      simp [hψ_zero]
  exact hint.trans (hzero ψ hψ_comp hψ_supp)

/-- Zero of the integrated real source-branch difference is exactly equality
of the two compact source-branch pairings.

This is pure measure algebra.  The analytic work is proving the displayed
zero integral from the BHW/Jost difference branch and the Wick-side compact
identity. -/
theorem integral_realSourceBranchDifference_eq_zero_to_pairing_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hid_int :
      Integrable
        (fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      Integrable
        (fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) * ψ u))
    (hzero :
      ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
      =
    ∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => u (τ k))) * ψ u := by
  have hfun :
      (fun u : NPointDomain d n =>
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u)
        =
      fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u := by
    funext u
    ring
  have hsub :
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u) -
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u) = 0 := by
    calc
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u) -
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
          =
        ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u := by
            rw [hfun]
            exact (MeasureTheory.integral_sub hτ_int hid_int).symm
      _ = 0 := hzero
  exact (sub_eq_zero.mp hsub).symm

/-- Source-patch compact pairing equality follows from vanishing of the real
source-branch difference distribution on the canonical Figure-2-4 source
patch.

The theorem is deliberately explicit about integrability.  The remaining
BHW/Jost analytic work is to construct the branch-difference zero statement
and these integrability facts from the OS I section 4.5 continuation data. -/
theorem os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            (BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
        =
      ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
            ψ u := by
  intro ψ hψ_comp hψ_supp
  exact
    BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq
      (d := d) OS lgc n (Equiv.swap i ⟨i.val + 1, hi⟩) ψ
      (hid_int ψ hψ_comp hψ_supp)
      (hτ_int ψ hψ_comp hψ_supp)
      (hzero ψ hψ_comp hψ_supp)

/-- A real source-branch-difference zero theorem packages directly into the
compact Figure-2-4 Wick-pairing packet.

This is the final algebraic step after the direct OS I section 4.5/BHW-Jost
analysis supplies the zero real-difference distribution on the canonical
source patch. -/
def os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            (BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_sourcePatchPairing
    (d := d) hd OS lgc n i hi
    (BHW.os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero
      (d := d) OS lgc n i hi hid_int hτ_int hzero)

/-- A BHW/Jost pair carrier plus distributional vanishing of its abstract
difference branch packages directly into the compact Figure-2-4 Wick-pairing
packet, provided the canonical source patch is contained in the carrier's real
patch.

This is the main algebraic consumer for the next analytic step:
construct the pair from OS I section 4.5 and prove the distributional zero of
`P.difference` on the canonical source patch. -/
def os45CompactFigure24WickPairingEq_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            P.difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero
    (d := d) hd OS lgc n i hi hid_int hτ_int
    (by
      intro ψ hψ_comp hψ_supp
      have hzero_τ :=
        BHW.realSourceBranchDifference_zero_of_pairData_difference_zero
          (d := d) (n := n) P hzero ψ hψ_comp
          (hψ_supp.trans hsource_subset)
      simpa [P.τ_eq] using hzero_τ)

/-- A full adjacent family of BHW/Jost pair carriers with distributionally
zero difference branches packages into the compact Figure-2-4 Wick-pairing
family. -/
def os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc :=
  fun i hi =>
    BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero
      (d := d) hd OS lgc n i hi (P i hi) (hsource_subset i hi)
      (hid_int i hi) (hτ_int i hi) (hzero i hi)

/-- A full adjacent family of zero-difference BHW/Jost pair carriers supplies
the direct source distributional adjacent-tube anchor. -/
def sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
      (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero)

/-- A full adjacent family of zero-difference BHW/Jost pair carriers supplies
the older selected-adjacent Jost anchor packet. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
      (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero)

/-- OS-selected naming wrapper for the direct source anchor produced from a
full adjacent family of zero-difference BHW/Jost pair carriers. -/
def bvt_F_distributionalJostAnchor_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero
    (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero

end BHW
