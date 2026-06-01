import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceBranchLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIRegularizedPairing
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity

/-!
# OS-II Axis-Pair Branch Descent

This companion records the quotient-descent part of the OS II V.2 handoff for
the concrete positive-side axis-pair branch CLM.  The point is deliberately
local: once the branch cutoff is supported in the positive time orthant, the
actual cutoff branch distribution descends to the Section 4.3 positive-time
quotient, so the same-distribution/A0 closure can be applied to the selected
Malgrange-Zerner branch.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators LineDeriv

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Direct local branch cutoff CLM retaining target quotient descent.

Unlike the product-source convergence packet, this construction only requires
the cutoff support to lie in the Lemma 5.1 branch window.  It is the usable
local OS-II V.2 surface for the selected Malgrange-Zerner branch: the cutoff
integral is a continuous linear functional and descends through the positive
time quotient whenever the cutoff support is positive. -/
theorem exists_axisPair_positiveSide_branchCutoffCLM_with_target_desc
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimePositiveRegion (d + 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            section43TimePositiveQuotientMap (d + 1) φ =
              section43TimePositiveQuotientMap (d + 1) ψ →
            T φ = T ψ) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                    (f.osConjTensorProduct
                      (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) * φ τ) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρbranch, _Cbranch, hρbranch, _hCbranch, hdiff, hreal, _hselector, _hbound⟩
  refine ⟨ρbranch, hρbranch, ?_⟩
  intro hχ_support hχ_pos
  let U0 : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρbranch
  let H0 : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have hU0_open : IsOpen U0 := by
    simpa [U0] using
      isOpen_osiiAxisPairTimeShellWindow (d := d) ξ (ρ := ρbranch)
  have hreal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp (continuous_apply ν)
  have hmaps0 :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        U0
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch) := by
    intro τ hτ
    simpa [U0, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hH0_cont : ContinuousOn H0 U0 := by
    simpa [H0, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hreal_cont.continuousOn hmaps0
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      H0 χ hU0_open hχ_compact (by simpa [U0] using hχ_support)
      hH0_cont with
    ⟨T, hT_cut, _hT_one⟩
  have hT_desc :
      ∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        section43TimePositiveQuotientMap (d + 1) φ =
          section43TimePositiveQuotientMap (d + 1) ψ →
        T φ = T ψ :=
    section43_integralMultiplierCLM_descends_of_tsupport_positive
      (n := d + 1) χ H0 T hT_cut hχ_pos
  have hT_schwinger :
      ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        T φ =
          ∫ τ : Fin (d + 1) → ℝ,
            (χ τ *
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) * φ τ := by
    intro φ
    rw [hT_cut φ]
    refine integral_congr_ae ?_
    filter_upwards with τ
    by_cases hτχ : τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ)
    · have hbranch :=
        hreal τ (by
          simpa [osiiAxisPairTimeShellWindow] using hχ_support hτχ)
      simp [H0, hbranch]
    · have hχ0 : χ τ = 0 := image_eq_zero_of_notMem_tsupport hτχ
      simp [hχ0]
  exact ⟨T, hT_cut, hT_desc, hT_schwinger⟩

/-- Product-source distributional form of the positive-side axis-pair real
trace.

On any carrier contained in the Lemma 5.1 time-shell window, the weighted MZ
branch has the same compact positive product-source pairings as the Schwinger
time shell.  This is the raw local `(5.2)` equality before any A0/P0 quotient
descent or endpoint selection. -/
theorem osiiAxisPair_weightedBranch_schwinger_productSource_pairings
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ U : Set (Fin (d + 1) → ℝ),
        U ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          (∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
              (section43TimeProductSource gs).f τ) =
            ∫ τ : Fin (d + 1) → ℝ,
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
                (section43TimeProductSource gs).f τ := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρ, _C, hρ, _hC, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨ρ, hρ, ?_⟩
  intro U hU_window gs hgsU
  let Branch : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  let Shell : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (τ 0) g)))
  exact
    integral_mul_eq_of_eqOn_tsupport
      Branch Shell
      ((section43TimeProductSource gs).f : (Fin (d + 1) → ℝ) → ℂ)
      (by
        intro τ hτ
        simpa [Branch, Shell, osiiAxisPairTimeShellWindow] using
          hreal τ (by
            simpa [osiiAxisPairTimeShellWindow] using hU_window (hgsU hτ)))

/-- BVT coordinate-shell selection from local branch pairings.

The previous theorem supplies the branch-versus-Schwinger product-source
pairings on a Lemma 5.1 window.  Therefore, if the BVT imaginary-axis product
kernel has the same product-source pairings as that branch on the same local
carrier, the Section 4.3 coordinate-height delta theorem identifies the BVT
value at `τ0` with the Schwinger shell at height `τ0 0`.

This is the assembly-facing form of the raw branch equality: the only remaining
input is the genuine BVT-to-branch product-source pairing comparison on the
carrier. -/
theorem osiiAxisPair_bvt_imagAxis_eq_coordinateShell_of_branch_pairings
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χsp : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (τ0 : Fin (d + 1) → ℝ) (hτ0 : ∀ i : Fin (d + 1), 0 < τ0 i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ U : Set (Fin (d + 1) → ℝ),
        U ∈ 𝓝 τ0 →
        U ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          (∫ τ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1) u χsp
                (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
                (section43TimeProductSource gs).f τ) =
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ) →
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            (d := d) OS lgc n (d + 1) u χsp
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
  classical
  haveI : Nonempty (Fin (d + 1)) := ⟨0⟩
  rcases
    osiiAxisPair_weightedBranch_schwinger_productSource_pairings
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρ, hρ, hbranch_pair⟩
  refine ⟨ρ, hρ, ?_⟩
  intro U hU_nhds hU_window hBVT_branch
  refine
    bvt_imagAxis_eq_coordinateShiftShell_of_local_productSource_pairings_eq
      (d := d) OS lgc u χsp (0 : Fin (d + 1)) f hf_ord g hg_ord
      hg_compact τ0 hτ0 U hU_nhds ?_
  intro gs hgsU
  calc
    (∫ τ : Fin (d + 1) → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n (d + 1) u χsp
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
          (section43TimeProductSource gs).f τ)
        =
      ∫ τ : Fin (d + 1) → ℝ,
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T0 ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
          (section43TimeProductSource gs).f τ := hBVT_branch gs hgsU
    _ =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ :=
        hbranch_pair U hU_window gs hgsU

/-- Source-current selection for the positive-side axis-pair branch.

If a compact time cutoff is supported in the Lemma 5.1 branch window and is
identically one on a local positive product-source carrier around `τ0`, then
compact product-source smearing forces the selected weighted branch scalar at
`τ0` to be the coordinate-height Schwinger shell.  This is the local OS-II V.2
selection step; it does not replace the boundary value by an endpoint. -/
theorem osiiAxisPair_weightedBranch_selects_schwinger_timeShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (τ0 : Fin (d + 1) → ℝ) (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ U : Set (Fin (d + 1) → ℝ),
        U ∈ 𝓝 τ0 →
        U ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        U ⊆ section43TimeStrictPositiveRegion (d + 1) →
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ U, χ τ = 1) →
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T0 ξ
          (fun ν : Fin (d + 1) => (τ0 ν : ℂ)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρ, _C, hρ, _hC, hdiff, hreal, _hselector, _hbound⟩
  refine ⟨ρ, hρ, ?_⟩
  intro U hU_nhds hU_window hU_pos hχ_window hχ_one_U
  let Branch : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  let Shell : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (τ 0) g)))
  let W : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρ
  let Wc : Set (Fin (d + 1) → ℂ) :=
    osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ
  have hofReal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp (continuous_apply ν)
  have hofReal_maps_W :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ))) W Wc := by
    intro τ hτ
    simpa [W, Wc, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hBranch_contOn_W : ContinuousOn Branch W := by
    simpa [Branch, W, Wc, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hofReal_cont.continuousOn hofReal_maps_W
  have hBranch_contOn_U : ContinuousOn Branch U :=
    hBranch_contOn_W.mono hU_window
  have hBranch_cont_at : ContinuousAt Branch τ0 :=
    hBranch_contOn_U.continuousAt hU_nhds
  have hShell_cont_t :
      ContinuousOn
        (fun t : ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))))
        (Set.Ioi 0) := by
    exact
      continuousOn_os_pairing_term_timeShift_of_isCompactSupport
        (d := d) OS f g hf_ord hg_ord hg_compact
  have hShell_contOn_U : ContinuousOn Shell U := by
    exact hShell_cont_t.comp
      (continuous_apply (0 : Fin (d + 1))).continuousOn
      (by
        intro τ hτ
        exact hU_pos hτ 0)
  have hShell_cont_at : ContinuousAt Shell τ0 :=
    hShell_contOn_U.continuousAt hU_nhds
  have hW_open : IsOpen W := by
    simpa [W] using isOpen_osiiAxisPairTimeShellWindow (d := d) ξ (ρ := ρ)
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      Branch χ hW_open hχ_compact (by simpa [W] using hχ_window)
      hBranch_contOn_W with
    ⟨Tcut, hTcut_branch, _hTcut_one⟩
  have hTcut_shell :
      ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        Tcut φ =
          ∫ τ : Fin (d + 1) → ℝ,
            (χ τ * Shell τ) * φ τ := by
    intro φ
    rw [hTcut_branch φ]
    refine integral_congr_ae ?_
    filter_upwards with τ
    by_cases hτχ : τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ)
    · have hB_eq : Branch τ = Shell τ := by
        simpa [Branch, Shell, W, osiiAxisPairTimeShellWindow] using
          hreal τ (by
            simpa [W, osiiAxisPairTimeShellWindow] using hχ_window hτχ)
      simp [hB_eq]
    · have hχ0 : χ τ = 0 := image_eq_zero_of_notMem_tsupport hτχ
      simp [hχ0]
  have hpair :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
        (∫ τ : Fin (d + 1) → ℝ,
          Branch τ * (section43TimeProductSource gs).f τ) =
          ∫ τ : Fin (d + 1) → ℝ,
            Shell τ * (section43TimeProductSource gs).f τ := by
    intro gs hgsU
    let source : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
      (section43TimeProductSource gs).f
    have hbranch_cut :
        (∫ τ : Fin (d + 1) → ℝ, Branch τ * source τ) =
          ∫ τ : Fin (d + 1) → ℝ, (χ τ * Branch τ) * source τ := by
      refine integral_congr_ae ?_
      filter_upwards with τ
      by_cases hτsource : τ ∈ tsupport (source : (Fin (d + 1) → ℝ) → ℂ)
      · have hχτ : χ τ = 1 := hχ_one_U τ (hgsU hτsource)
        simp [hχτ]
      · have hsource0 : source τ = 0 :=
          image_eq_zero_of_notMem_tsupport hτsource
        simp [hsource0]
    have hshell_cut :
        (∫ τ : Fin (d + 1) → ℝ, (χ τ * Shell τ) * source τ) =
          ∫ τ : Fin (d + 1) → ℝ, Shell τ * source τ := by
      refine integral_congr_ae ?_
      filter_upwards with τ
      by_cases hτsource : τ ∈ tsupport (source : (Fin (d + 1) → ℝ) → ℂ)
      · have hχτ : χ τ = 1 := hχ_one_U τ (hgsU hτsource)
        simp [hχτ]
      · have hsource0 : source τ = 0 :=
          image_eq_zero_of_notMem_tsupport hτsource
        simp [hsource0]
    calc
      (∫ τ : Fin (d + 1) → ℝ, Branch τ *
          (section43TimeProductSource gs).f τ)
          =
        ∫ τ : Fin (d + 1) → ℝ, Branch τ * source τ := rfl
      _ =
        ∫ τ : Fin (d + 1) → ℝ, (χ τ * Branch τ) * source τ := hbranch_cut
      _ =
        Tcut source := (hTcut_branch source).symm
      _ =
        ∫ τ : Fin (d + 1) → ℝ, (χ τ * Shell τ) * source τ :=
          hTcut_shell source
      _ =
        ∫ τ : Fin (d + 1) → ℝ, Shell τ * source τ := hshell_cut
      _ =
        ∫ τ : Fin (d + 1) → ℝ,
          Shell τ * (section43TimeProductSource gs).f τ := rfl
  have hpoint : Branch τ0 = Shell τ0 := by
    exact
      eq_of_local_positiveOrthant_productSource_pairings_eq_of_continuousOn
        Branch Shell τ0 hτ0pos U hU_nhds hBranch_cont_at hShell_cont_at
        hBranch_contOn_U hShell_contOn_U hpair
  simpa [Branch, Shell] using hpoint

/-- Product-source handoff from the local branch cutoff CLM to an A0 time-shell
cutoff CLM on a compact carrier.

This is the usable local form of OS-II `(5.2)`: the branch cutoff CLM is not
globalized.  It agrees with the A0 time-shell CLM on product sources whose
support lies in the compact carrier where the branch time cutoff is one and
the A0 scalar representative is the Schwinger shell. -/
theorem exists_axisPair_positiveSide_branchCutoffCLM_product_eq_A0_on_carrier
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (χtime : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχtime_compact :
      HasCompactSupport (χtime : (Fin (d + 1) → ℝ) → ℂ))
    (χA0 : SchwartzNPoint d (n + (d + 1)))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d (d + 1))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (U K : Set (Fin (d + 1) → ℝ))
    (hK_sub_U : K ⊆ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ)
        S_real U)
    (hS_eq :
      Set.EqOn S_real
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimePositiveRegion (d + 1) →
        (∀ τ ∈ K, χtime τ = 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χtime τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            section43TimePositiveQuotientMap (d + 1) φ =
              section43TimePositiveQuotientMap (d + 1) ψ →
            T φ = T ψ) ∧
          (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
            T (section43TimeProductSource gs).f =
              osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
                (section43TimeProductSource gs).f)) := by
  classical
  rcases
    exists_axisPair_positiveSide_branchCutoffCLM_with_target_desc
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      χtime hχtime_compact with
    ⟨ρ, hρ, hpacket⟩
  refine ⟨ρ, hρ, ?_⟩
  intro hχ_support hχ_pos hχ_one_K
  rcases hpacket hχ_support hχ_pos with
    ⟨T, hT_formula, hT_desc, hT_schwinger⟩
  refine ⟨T, hT_formula, hT_desc, ?_⟩
  intro gs hgsK
  let Fprod : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    (section43TimeProductSource gs).f
  let Shell : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (τ 0) g)))
  have hT_no_cut :
      T Fprod =
        ∫ τ : Fin (d + 1) → ℝ, Shell τ * Fprod τ := by
    rw [hT_schwinger Fprod]
    refine integral_congr_ae ?_
    filter_upwards with τ
    by_cases hτF : τ ∈ tsupport (Fprod : (Fin (d + 1) → ℝ) → ℂ)
    · have hχτ : χtime τ = 1 := hχ_one_K τ (hgsK hτF)
      simp [Shell, hχτ]
    · have hF0 : Fprod τ = 0 := image_eq_zero_of_notMem_tsupport hτF
      simp [hF0]
  have hShell_to_S :
      (∫ τ : Fin (d + 1) → ℝ, Shell τ * Fprod τ) =
        ∫ τ : Fin (d + 1) → ℝ, S_real τ * Fprod τ := by
    refine
      integral_mul_eq_of_eqOn_tsupport
        Shell S_real (Fprod : (Fin (d + 1) → ℝ) → ℂ) ?_
    intro τ hτ
    exact (hS_eq (hgsK hτ)).symm
  have hA0 :
      osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ Fprod =
        ∫ τ : Fin (d + 1) → ℝ, S_real τ * Fprod τ := by
    exact hrep Fprod
      ⟨(section43TimeProductSource gs).compact, fun τ hτ => hK_sub_U (hgsK hτ)⟩
  calc
    T (section43TimeProductSource gs).f = T Fprod := rfl
    _ = ∫ τ : Fin (d + 1) → ℝ, Shell τ * Fprod τ := hT_no_cut
    _ = ∫ τ : Fin (d + 1) → ℝ, S_real τ * Fprod τ := hShell_to_S
    _ = osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ Fprod :=
      hA0.symm
    _ =
      osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
        (section43TimeProductSource gs).f := rfl

/-- BVT-to-branch product-source transport through the same local A0 carrier.

This is the carrier packet needed for the OS-II V.2 handoff: the BVT
imaginary-axis product-source pairing and the positive-side axis-pair branch
pairing are both expressed through the same represented local A0 cutoff
distribution.  The branch cutoff disappears because it is identically one on the
compact carrier supporting the product source. -/
theorem bvt_axisPair_branch_productSource_pairings_from_localA0_carrier
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χsp : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (χtime : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχtime_compact :
      HasCompactSupport (χtime : (Fin (d + 1) → ℝ) → ℂ))
    (χA0 : SchwartzNPoint d (n + (d + 1)))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d (d + 1))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (U K : Set (Fin (d + 1) → ℝ))
    (hK_sub_U : K ⊆ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ)
        S_real U)
    (hS_eq :
      Set.EqOn S_real
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimePositiveRegion (d + 1) →
        (∀ τ ∈ K, χtime τ = 1) →
        (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ τ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                OS lgc n (d + 1) u χsp
                (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
                (section43TimeProductSource gs).f τ) =
            osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
              (section43TimeProductSource gs).f) →
        ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ τ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                OS lgc n (d + 1) u χsp
                (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
                (section43TimeProductSource gs).f τ) =
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ) := by
  classical
  rcases
    exists_axisPair_positiveSide_branchCutoffCLM_product_eq_A0_on_carrier
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      χtime hχtime_compact χA0 hχA0_disj fLeft κ S_real U K
      hK_sub_U hrep hS_eq with
    ⟨ρ, hρ, hpacket⟩
  refine ⟨ρ, hρ, ?_⟩
  intro hχ_window hχ_pos hχ_one_K hBVT_A0 gs hgsK
  rcases hpacket hχ_window hχ_pos hχ_one_K with
    ⟨T, hT_branch_cut, _hT_desc, hT_A0⟩
  let Fprod : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    (section43TimeProductSource gs).f
  let Branch : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have hT_branch_uncut :
      T Fprod =
        ∫ τ : Fin (d + 1) → ℝ, Branch τ * Fprod τ := by
    rw [hT_branch_cut Fprod]
    refine integral_congr_ae ?_
    filter_upwards with τ
    by_cases hτF : τ ∈ tsupport (Fprod : (Fin (d + 1) → ℝ) → ℂ)
    · have hχτ : χtime τ = 1 := hχ_one_K τ (hgsK hτF)
      simp [Branch, hχτ]
    · have hF0 : Fprod τ = 0 := image_eq_zero_of_notMem_tsupport hτF
      simp [hF0]
  calc
    (∫ τ : Fin (d + 1) → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          OS lgc n (d + 1) u χsp
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
          (section43TimeProductSource gs).f τ)
        =
      osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
        (section43TimeProductSource gs).f := hBVT_A0 gs hgsK
    _ = T (section43TimeProductSource gs).f := (hT_A0 gs hgsK).symm
    _ = T Fprod := rfl
    _ = ∫ τ : Fin (d + 1) → ℝ, Branch τ * Fprod τ := hT_branch_uncut
    _ =
      ∫ τ : Fin (d + 1) → ℝ,
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T0 ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
          (section43TimeProductSource gs).f τ := rfl

/-- BVT coordinate-shell selection from the represented local A0 carrier.

Combining the carrier transport packet with the branch-selection delta theorem
removes the abstract BVT-to-branch premise: it is enough to have the genuine
BVT/A0 product-source identity on the same compact carrier and a time cutoff
which is one there. -/
theorem bvt_imagAxis_eq_coordinateShell_from_localA0_carrier
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χsp : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (τ0 : Fin (d + 1) → ℝ) (hτ0 : ∀ i : Fin (d + 1), 0 < τ0 i)
    (χtime : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχtime_compact :
      HasCompactSupport (χtime : (Fin (d + 1) → ℝ) → ℂ))
    (χA0 : SchwartzNPoint d (n + (d + 1)))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d (d + 1))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (U K : Set (Fin (d + 1) → ℝ))
    (hK_sub_U : K ⊆ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ)
        S_real U)
    (hS_eq :
      Set.EqOn S_real
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (K ∈ 𝓝 τ0 →
        K ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimePositiveRegion (d + 1) →
        (∀ τ ∈ K, χtime τ = 1) →
        (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ τ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                OS lgc n (d + 1) u χsp
                (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
                (section43TimeProductSource gs).f τ) =
            osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
              (section43TimeProductSource gs).f) →
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            OS lgc n (d + 1) u χsp
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ0 0) g)))) := by
  classical
  rcases
    osiiAxisPair_bvt_imagAxis_eq_coordinateShell_of_branch_pairings
      (d := d) OS lgc u χsp f hf_ord g hg_ord hg_compact T0 hT0
      ξ hξ0 τ0 hτ0 with
    ⟨ρsel, hρsel, hselect⟩
  rcases
    bvt_axisPair_branch_productSource_pairings_from_localA0_carrier
      (d := d) OS lgc u χsp f hf_ord g hg_ord hg_compact T0 hT0
      ξ hξ0 χtime hχtime_compact χA0 hχA0_disj fLeft κ S_real
      U K hK_sub_U hrep hS_eq with
    ⟨ρtr, hρtr, htransport⟩
  let ρ : ℝ := min ρsel ρtr
  have hρ : 0 < ρ := lt_min hρsel hρtr
  refine ⟨ρ, hρ, ?_⟩
  intro hK_nhds hK_window hχ_window hχ_pos hχ_one_K hBVT_A0
  have hK_window_sel :
      K ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρsel := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hK_window hτ ν) (min_le_left ρsel ρtr)
  have hχ_window_tr :
      tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρtr := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hχ_window hτ ν) (min_le_right ρsel ρtr)
  have hbranch_pair :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
        (∫ τ : Fin (d + 1) → ℝ,
            bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              OS lgc n (d + 1) u χsp
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
              (section43TimeProductSource gs).f τ) =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
              (section43TimeProductSource gs).f τ :=
    htransport hχ_window_tr hχ_pos hχ_one_K hBVT_A0
  exact hselect K hK_nhds hK_window_sel hbranch_pair

/-- BVT/boundary point equality from the same represented local A0 carrier.

The BVT side is selected by the local A0 carrier theorem above; the neighboring
axis-pair boundary CLM is selected by the side-cone source-current theorem.  Thus
both boundary values agree at the target point through the same Schwinger
coordinate shell. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_from_localA0_carrier_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χsp : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (τ0 : Fin (d + 1) → ℝ) (hτ0 : ∀ i : Fin (d + 1), 0 < τ0 i)
    (χtime : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχtime_compact :
      HasCompactSupport (χtime : (Fin (d + 1) → ℝ) → ℂ))
    (χA0 : SchwartzNPoint d (n + (d + 1)))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d (d + 1))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (U K : Set (Fin (d + 1) → ℝ))
    (hK_sub_U : K ⊆ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ)
        S_real U)
    (hS_eq :
      Set.EqOn S_real
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ τ : Fin (d + 1) → ℝ,
      τ ∈ osiiAxisPairTimeShellWindow
          (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρZ →
      ∀ hτpos : τ ∈ section43TimeStrictPositiveRegion (d + 1),
        Z (section43TimeImagAxisProductKernel τ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ hτpos⟩) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (K ∈ 𝓝 τ0 →
        K ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        tsupport (χtime : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimePositiveRegion (d + 1) →
        (∀ τ ∈ K, χtime τ = 1) →
        (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ τ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                OS lgc n (d + 1) u χsp
                (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
                (section43TimeProductSource gs).f τ) =
            osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj fLeft κ
              (section43TimeProductSource gs).f) →
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            OS lgc n (d + 1) u χsp
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
          ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)).comp
            (osiiAxisPairHeadRestrictionCLM d))
            (section43TimeImagAxisProductKernel τ0)) := by
  classical
  haveI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  rcases
    bvt_imagAxis_eq_coordinateShell_from_localA0_carrier
      (d := d) OS lgc u χsp f hf_ord g hg_ord hg_compact T0 hT0
      ξ hξ0 τ0 hτ0 χtime hχtime_compact χA0 hχA0_disj fLeft
      κ S_real U K hK_sub_U hrep hS_eq with
    ⟨ρ, hρ, hBVT_point⟩
  refine ⟨ρ, hρ, ?_⟩
  intro hK_nhds hK_window hχ_window hχ_pos hχ_one_K hBVT_A0
  have hBVT :
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          OS lgc n (d + 1) u χsp
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) :=
    hBVT_point hK_nhds hK_window hχ_window hχ_pos hχ_one_K hBVT_A0
  have hBoundary :
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
    simpa using
      osiiAxisPair_boundaryCLM_sourceCurrent_selects_schwinger_sideCone
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0
        τ0 hτ0 hCside_pos ρZ hρZ Z hZ
  exact hBVT.trans hBoundary.symm

/-- OS-II Step 4 regularized `k_rho` integral transport.

Once the local A0/side-cone argument has selected the BVT imaginary-axis scalar
and the neighboring axis-pair boundary scalar pointwise on the real support of
the actual Step-4 regularizer, the whole regularized average transports across
that equality.  This is the integral handoff used before applying the Hilbert
space scalar-product bound. -/
theorem osiiStep4_regularizedK_integral_bvt_eq_axisPairBoundary_of_tsupport_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χsp : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    {rho : ℝ} (hrho : 0 < rho)
    (hpoint :
      ∀ τ ∈ tsupport
          (osiiStep4RegularizerKSchwartz (d + 1) rho hrho :
            (Fin (d + 1) → ℝ) → ℂ),
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            OS lgc n (d + 1) u χsp
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) =
          ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)).comp
            (osiiAxisPairHeadRestrictionCLM d))
            (section43TimeImagAxisProductKernel τ)) :
    (∫ τ : Fin (d + 1) → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            OS lgc n (d + 1) u χsp
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)) *
          osiiStep4RegularizerKSchwartz (d + 1) rho hrho τ) =
      ∫ τ : Fin (d + 1) → ℝ,
        ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)).comp
          (osiiAxisPairHeadRestrictionCLM d))
          (section43TimeImagAxisProductKernel τ) *
          osiiStep4RegularizerKSchwartz (d + 1) rho hrho τ := by
  exact
    integral_mul_eq_of_eqOn_tsupport
      (fun τ : Fin (d + 1) → ℝ =>
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          OS lgc n (d + 1) u χsp
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ i)))
      (fun τ : Fin (d + 1) → ℝ =>
        ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)).comp
          (osiiAxisPairHeadRestrictionCLM d))
          (section43TimeImagAxisProductKernel τ))
      (osiiStep4RegularizerKSchwartz (d + 1) rho hrho :
        (Fin (d + 1) → ℝ) → ℂ)
      hpoint

end OSReconstruction
