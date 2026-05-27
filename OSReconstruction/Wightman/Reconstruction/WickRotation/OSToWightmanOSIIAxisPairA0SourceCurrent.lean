import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairA0Bridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairRawCLMSelector
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent

/-!
# OS-II Axis-Pair A0 Source-Current Bridge

This companion records the OS II V.2 handoff from the glued axis-pair
Malgrange-Zerner real representative to the time-shell product CLM.  The
axis-pair chart selects a distinguished coordinate height `ξ 0`; the local
`(A0)->(P0)` bridge consumes compact positive product-source pairings of a
time-shell CLM.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The axis-pair MZ real representative pairs with the product-source time CLM
once the selected coordinate-height shell is represented by the CLM on the
support of the source.

This is the concrete source-current transport missing between the compact
axis-pair real-edge representative and the local `(A0)->(P0)` distributional
bridge. -/
theorem osiiAxisPair_timeShell_realRepresentative_productSource_pairing_timeCLM
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
    (T : ℝ) (hT : 0 < T)
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D)
    (hZ : ∀ (ξ : Fin (d + 1) → ℝ)
      (hξ : ξ ∈ tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
            ((section43TimeProductSource gs).positive hξ)⟩) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ),
          S_real τ =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∫ τ : Fin (d + 1) → ℝ,
            S_real τ * (section43TimeProductSource gs).f τ) =
          OS.S (n + r)
            (Z (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  classical
  rcases
    osiiAxisPair_timeShell_realRepresentative_productSource_pairing
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT gs with
    ⟨Ureal, S_real, hUreal_open, hsource_sub, hS_cont, hedge, hpair⟩
  refine ⟨Ureal, S_real, hUreal_open, hsource_sub, hS_cont, hedge, ?_⟩
  calc
    (∫ τ : Fin (d + 1) → ℝ,
        S_real τ * (section43TimeProductSource gs).f τ)
        =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ := hpair
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        exact
          schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS (q := (0 : Fin (d + 1))) f hf_ord g hg_ord Z gs hZ

/-- Fixed-compact version of the axis-pair real-representative/source-current
handoff.

The local `(A0)->(P0)` delta step needs one real representative on a fixed
neighborhood of the compact positive carrier, and then product-source pairings
for every source supported in that carrier.  This theorem is that fixed-carrier
form: the only source-current hypothesis is that the time CLM `Z` selects the
coordinate-height shifted Schwinger shell on `K`. -/
theorem osiiAxisPair_timeShell_realRepresentative_productSource_pairing_timeCLM_on_compact
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
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0})
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ (ξ : Fin (d + 1) → ℝ) (hξK : ξ ∈ K),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
            (hK_pos hξK)⟩) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        K ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ τ : Fin (d + 1) → ℝ,
              S_real τ * (section43TimeProductSource gs).f τ) =
            OS.S (n + r)
              (Z (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative_pairing
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge, hpair_edge⟩
  refine ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge, ?_⟩
  intro gs hgsK
  let source : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    (section43TimeProductSource gs).f
  let Tsch : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      Tsch gs (fun _ : Fin (d + 1) => 0)
  calc
    (∫ τ : Fin (d + 1) → ℝ,
        S_real τ * (section43TimeProductSource gs).f τ)
        =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ := by
        exact hpair_edge source (by simpa [source] using hgsK)
    _ =
      ∫ τ : Fin (d + 1) → ℝ,
        Tsch (section43TimeImagAxisProductKernel τ) *
          (section43TimeProductSource gs).f τ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun τ : Fin (d + 1) → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
            (fun τ : Fin (d + 1) → ℝ =>
              Tsch (section43TimeImagAxisProductKernel τ))
            ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ)
            ?_
        intro τ hτ
        have hτK : τ ∈ K := hgsK hτ
        have hτ0 : 0 < τ 0 := hK_pos hτK
        calc
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))
              =
            OS.S (n + r)
              (⟨f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g),
                VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
                  (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ hτ0⟩) := by
                rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes]
          _ =
            OS.S (n + r)
              (Z (section43TimeImagAxisProductKernel τ)) := by
                rw [hZ τ hτK]
          _ =
            Tsch (section43TimeImagAxisProductKernel τ) := by
                rfl
    _ =
      Tsch (section43TimeProductTensor
        (fun i : Fin (d + 1) =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
        hflat.symm
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        rfl

/-- Pointwise CLM selection from the fixed compact axis-pair source-current
packet.

This is the local OS-II V.2 positive-orthant delta step for the axis-pair
coordinate-height chart: compact product-source pairings on a neighborhood of
`τ0` force the glued real representative to equal the time-CLM kernel at
`τ0`. -/
theorem osiiAxisPair_timeShell_realRepresentative_selects_timeCLM_on_compact
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
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0})
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ (ξ : Fin (d + 1) → ℝ) (hξK : ξ ∈ K),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
            (hK_pos hξK)⟩)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0K : τ0 ∈ K)
    (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    (V : Set (Fin (d + 1) → ℝ))
    (hV_nhds : V ∈ 𝓝 τ0)
    (hV_sub_K : V ⊆ K)
    (hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1)) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        K ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        S_real τ0 =
          (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
            (section43TimeImagAxisProductKernel τ0) := by
  classical
  rcases
    osiiAxisPair_timeShell_realRepresentative_productSource_pairing_timeCLM_on_compact
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos Z hZ with
    ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, _hedge, hpair_all⟩
  let Tsch : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  let Kclm : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    Tsch (section43TimeImagAxisProductKernel τ)
  have hS_cont_at : ContinuousAt S_real τ0 :=
    hS_cont.continuousAt (hUreal_open.mem_nhds (hK_sub hτ0K))
  have hS_contOn_V : ContinuousOn S_real V :=
    hS_cont.mono (fun τ hτ => hK_sub (hV_sub_K hτ))
  have hkernel_cont_V :
      ContinuousOn section43TimeImagAxisProductKernel V :=
    continuousOn_section43TimeImagAxisProductKernel_strictPositive.mono hV_pos
  have hKclm_contOn_V : ContinuousOn Kclm V := by
    exact
      Tsch.continuous.continuousOn.comp hkernel_cont_V
        (fun _ _ => Set.mem_univ _)
  have hKclm_cont_at : ContinuousAt Kclm τ0 :=
    hKclm_contOn_V.continuousAt hV_nhds
  have hpair_delta :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        (∫ ξ : Fin (d + 1) → ℝ,
          S_real ξ * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin (d + 1) → ℝ,
            Kclm ξ * (section43TimeProductSource gs).f ξ := by
    intro gs hgsV
    have hgsK :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ K := fun ξ hξ => hV_sub_K (hgsV hξ)
    have hflat :=
      section43TimeProductTensor_allSlots_flattened
        Tsch gs (fun _ : Fin (d + 1) => 0)
    calc
      (∫ ξ : Fin (d + 1) → ℝ,
          S_real ξ * (section43TimeProductSource gs).f ξ)
          =
        Tsch (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          simpa [Tsch] using hpair_all gs hgsK
      _ =
        ∫ ξ : Fin (d + 1) → ℝ,
          Kclm ξ * (section43TimeProductSource gs).f ξ := by
          simpa [Kclm] using hflat
  have hpoint :
      S_real τ0 = Kclm τ0 := by
    exact
      eq_of_local_positiveOrthant_productSource_pairings_eq_of_continuousOn
        S_real Kclm τ0 hτ0pos V hV_nhds
        hS_cont_at hKclm_cont_at hS_contOn_V hKclm_contOn_V hpair_delta
  refine ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, ?_⟩
  simpa [Kclm, Tsch] using hpoint

/-- Head-restriction transport for the axis-pair source current.

The raw selector naturally acts on the one-dimensional positive-energy
time-test quotient.  The axis-pair product-source chart uses
`Fin (d+1)` auxiliary time variables; composing the one-dimensional current
with `osiiAxisPairHeadRestrictionCLM` gives the required vector current.  The
only analytic input is that the one-dimensional current factors through the
positive-energy quotient. -/
theorem osiiAxisPair_headRestriction_source_current_kernel
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (hZhead_respects :
      ∀ φ ψ : SchwartzMap ℝ ℂ,
        section43PositiveEnergyQuotientMap1D φ =
          section43PositiveEnergyQuotientMap1D ψ →
        Zhead φ = Zhead ψ)
    (hZhead_kernel :
      ∀ (t : ℝ) (ht : 0 < t),
        Zhead (section43PsiZTimeTest t ht) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
              (d := d) f hf_ord g hg_ord t ht⟩) :
    let Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
        ZeroDiagonalSchwartz d (n + r) :=
      Zhead.comp (osiiAxisPairHeadRestrictionCLM d)
    ∀ (ξ : Fin (d + 1) → ℝ)
      (hξ : ξ ∈ section43TimeStrictPositiveRegion (d + 1)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ (hξ 0)⟩ := by
  classical
  intro Z ξ hξ
  dsimp [Z]
  have hq :
      section43PositiveEnergyQuotientMap1D
          (osiiAxisPairHeadRestrictionCLM d
            (section43TimeImagAxisProductKernel ξ)) =
        section43PositiveEnergyQuotientMap1D
          (section43PsiZTimeTest (ξ 0) (hξ 0)) := by
    apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
    exact osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg ξ hξ
  exact (hZhead_respects _ _ hq).trans (by
    simpa using hZhead_kernel (ξ 0) (hξ 0))

/-- Local-chart form of the fixed compact axis-pair source-current selector.

The OS-II chart construction supplies the selected source-current identity on
an open strict-positive neighborhood of the target.  This theorem shrinks that
chart to a compact closed ball and applies the local product-source delta
argument, producing the real representative that selects the time CLM at the
target point. -/
theorem osiiAxisPair_timeShell_realRepresentative_selects_timeCLM_on_open_chart
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
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ (ξ : Fin (d + 1) → ℝ) (hξW : ξ ∈ W),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
            ((hW_pos hξW) 0)⟩) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        τ0 ∈ Ureal ∧
        ContinuousOn S_real Ureal ∧
        S_real τ0 =
          (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
            (section43TimeImagAxisProductKernel τ0) := by
  classical
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (hW_open.mem_nhds hτ0W) with
    ⟨ρ, hρ, hρ_sub_W⟩
  let K : Set (Fin (d + 1) → ℝ) := Metric.closedBall τ0 ρ
  let V : Set (Fin (d + 1) → ℝ) := Metric.ball τ0 ρ
  have hK : IsCompact K := by
    simpa [K] using isCompact_closedBall τ0 ρ
  have hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0} := by
    intro τ hτ
    exact (hW_pos (hρ_sub_W (by simpa [K] using hτ))) 0
  have hτ0K : τ0 ∈ K := by
    simpa [K] using
      (Metric.mem_closedBall_self (x := τ0) (ε := ρ) hρ.le)
  have hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i :=
    hW_pos hτ0W
  have hV_nhds : V ∈ 𝓝 τ0 := by
    simpa [V] using Metric.ball_mem_nhds τ0 hρ
  have hV_sub_K : V ⊆ K := by
    intro τ hτ
    exact Metric.ball_subset_closedBall (by simpa [V] using hτ)
  have hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1) := by
    intro τ hτ
    exact hW_pos (hρ_sub_W (hV_sub_K hτ))
  rcases
    osiiAxisPair_timeShell_realRepresentative_selects_timeCLM_on_compact
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos Z
      (fun ξ hξK => hZ ξ (hρ_sub_W (by simpa [K] using hξK)))
      τ0 hτ0K hτ0pos V hV_nhds hV_sub_K hV_pos with
    ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hselect⟩
  refine ⟨Ureal, S_real, hUreal_open, hK_sub hτ0K, hS_cont, hselect⟩

/-- Product-tensor source-current form of the positive side-cone boundary
selection.

The boundary CLM and the Schwinger coordinate-height shell are paired against
the same compact product source on the same time-shell window.  This is the
actual compact source-current transport exposed by the OS-II `(5.7)`--`(5.8)`
selector, not an endpoint replacement. -/
theorem osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_sideCone
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
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          TC (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
            ∫ τ : Fin (d + 1) → ℝ,
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
                (section43TimeProductSource gs).f τ := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_boundaryCLM_eq_schwinger_timeShell_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρ, C, hρ, hC, hkernel⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gs hgs_window
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      TC gs (fun _ : Fin (d + 1) => 0)
  calc
    TC (section43TimeProductTensor
        (fun i : Fin (d + 1) =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        =
      ∫ τ : Fin (d + 1) → ℝ,
        TC (section43TimeImagAxisProductKernel τ) *
          (section43TimeProductSource gs).f τ := by
        simpa [TC] using hflat
    _ =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun τ : Fin (d + 1) → ℝ =>
              TC (section43TimeImagAxisProductKernel τ))
            (fun τ : Fin (d + 1) → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
            ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ)
            ?_
        intro τ hτ
        exact hkernel τ (hgs_window hτ)
          ((section43TimeProductSource gs).positive hτ)

/-- Lower-side product-tensor source-current form of the boundary selection.

This is the same compact source-current transport as the positive side, but
the boundary CLM is selected through a lower cone `y 0 < 0`; the lower raw
selector has already been identified with the same MZ/Schwinger time-shell
branch. -/
theorem osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_lowerSideCone
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
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          TC (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
            ∫ τ : Fin (d + 1) → ℝ,
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
                (section43TimeProductSource gs).f τ := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_boundaryCLM_eq_schwinger_timeShell_lowerSideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_neg with
    ⟨ρ, C, hρ, hC, hkernel⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gs hgs_window
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      TC gs (fun _ : Fin (d + 1) => 0)
  calc
    TC (section43TimeProductTensor
        (fun i : Fin (d + 1) =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        =
      ∫ τ : Fin (d + 1) → ℝ,
        TC (section43TimeImagAxisProductKernel τ) *
          (section43TimeProductSource gs).f τ := by
        simpa [TC] using hflat
    _ =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun τ : Fin (d + 1) → ℝ =>
              TC (section43TimeImagAxisProductKernel τ))
            (fun τ : Fin (d + 1) → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
            ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ)
            ?_
        intro τ hτ
        exact hkernel τ (hgs_window hτ)
          ((section43TimeProductSource gs).positive hτ)

/-- Product-tensor equality between the positive side-cone boundary CLM and an
honest zero-diagonal time CLM on a common time-shell window.

The side-cone theorem provides the boundary CLM pairing with the Schwinger
coordinate-height shell; the coordinate source-current theorem then identifies
that same pairing with `OS.S` applied to the honest time CLM. -/
theorem osiiAxisPair_boundaryCLM_productTensor_eq_timeCLM_sideCone
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
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ τ : Fin (d + 1) → ℝ,
      τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρZ →
      ∀ hτpos : τ ∈ section43TimeStrictPositiveRegion (d + 1),
        Z (section43TimeImagAxisProductKernel τ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ
              hτpos⟩) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          TC (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
            OS.S (n + r)
              (Z (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρb, Cb, hρb, hCb, hboundary⟩
  refine ⟨min ρb ρZ, Cb, lt_min hρb hρZ, hCb, ?_⟩
  intro gs hgs_window
  have hgs_boundary :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρb := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρb ρZ)
  have hgs_Z :
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) →
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρZ := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_right ρb ρZ)
  calc
    TC (section43TimeProductTensor
        (fun i : Fin (d + 1) =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        =
      ∫ τ : Fin (d + 1) → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
          (section43TimeProductSource gs).f τ := by
        exact hboundary gs hgs_boundary
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        exact
          schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS (q := (0 : Fin (d + 1))) f hf_ord g hg_ord Z gs
            (fun τ hτ =>
              hZ τ (hgs_Z τ hτ) ((section43TimeProductSource gs).positive hτ))

/-- Pointwise side-cone boundary source-current selection.

The compact product-source equality from
`osiiAxisPair_boundaryCLM_productTensor_eq_timeCLM_sideCone` is converted back
to the point value at the center by the local positive-orthant delta theorem.
This is the OS-II V.2 smearing step for the boundary CLM itself; it does not
use an endpoint replacement. -/
theorem osiiAxisPair_boundaryCLM_sourceCurrent_selects_schwinger_sideCone
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
    (T : ℝ) (hT : 0 < T)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
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
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ
              hτpos⟩) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    TC (section43TimeImagAxisProductKernel τ0) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
  classical
  intro F G TC
  let center : Fin (d + 1) → ℝ :=
    osiiAxisPairTimeShellCenter (d := d) τ0
  have hcenter0 : 0 < center 0 := by
    simpa [center] using
      osiiAxisPairTimeShellCenter_time_pos (d := d) (hτ0pos 0)
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_timeCLM_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      center hcenter0 hCside_pos ρZ hρZ Z hZ with
    ⟨ρ, C, hρ, _hC, hprod⟩
  let U0 : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) center ρ
  let V : Set (Fin (d + 1) → ℝ) :=
    U0 ∩ section43TimeStrictPositiveRegion (d + 1)
  have hτ0U0 : τ0 ∈ U0 := by
    have hpert :
        osiiAxisPairTimeShellPerturbation (d := d) center τ0 = 0 := by
      simpa [center] using
        osiiAxisPairTimeShellPerturbation_center_self (d := d) τ0
    intro ν
    have hν := congrFun hpert ν
    simpa [U0, osiiAxisPairTimeShellWindow, hν] using hρ
  have hτ0Z :
      τ0 ∈ osiiAxisPairTimeShellWindow (d := d) center ρZ := by
    have hpert :
        osiiAxisPairTimeShellPerturbation (d := d) center τ0 = 0 := by
      simpa [center] using
        osiiAxisPairTimeShellPerturbation_center_self (d := d) τ0
    intro ν
    have hν := congrFun hpert ν
    simpa [osiiAxisPairTimeShellWindow, hν] using hρZ
  have hV_nhds : V ∈ 𝓝 τ0 := by
    have hpos_open : IsOpen (section43TimeStrictPositiveRegion (d + 1)) := by
      have hset :
          section43TimeStrictPositiveRegion (d + 1) =
            ⋂ i : Fin (d + 1),
              {τ : Fin (d + 1) → ℝ | 0 < τ i} := by
        ext τ
        simp [section43TimeStrictPositiveRegion]
      rw [hset]
      exact
        isOpen_iInter_of_finite fun i : Fin (d + 1) =>
          isOpen_lt
            (continuous_const :
              Continuous fun _τ : Fin (d + 1) → ℝ => (0 : ℝ))
            (continuous_apply i :
              Continuous fun τ : Fin (d + 1) → ℝ => τ i)
    exact
      Filter.inter_mem
        ((isOpen_osiiAxisPairTimeShellWindow (d := d) center).mem_nhds hτ0U0)
        (hpos_open.mem_nhds (by
          simpa [section43TimeStrictPositiveRegion] using hτ0pos))
  let Kboundary : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    TC (section43TimeImagAxisProductKernel τ)
  let TZ : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  let KZ : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    TZ (section43TimeImagAxisProductKernel τ)
  have hkernel_cont_V :
      ContinuousOn section43TimeImagAxisProductKernel V :=
    continuousOn_section43TimeImagAxisProductKernel_strictPositive.mono
      (fun τ hτ => hτ.2)
  have hKboundary_contOn : ContinuousOn Kboundary V := by
    exact TC.continuous.continuousOn.comp hkernel_cont_V
      (fun _ _ => Set.mem_univ _)
  have hKZ_contOn : ContinuousOn KZ V := by
    exact TZ.continuous.continuousOn.comp hkernel_cont_V
      (fun _ _ => Set.mem_univ _)
  have hKboundary_cont : ContinuousAt Kboundary τ0 :=
    hKboundary_contOn.continuousAt hV_nhds
  have hKZ_cont : ContinuousAt KZ τ0 :=
    hKZ_contOn.continuousAt hV_nhds
  have hpair :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ V →
        (∫ τ : Fin (d + 1) → ℝ,
          Kboundary τ * (section43TimeProductSource gs).f τ) =
          ∫ τ : Fin (d + 1) → ℝ,
            KZ τ * (section43TimeProductSource gs).f τ := by
    intro gs hgsV
    have hgsU0 :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U0 := fun τ hτ => (hgsV hτ).1
    have hflat_boundary :=
      section43TimeProductTensor_allSlots_flattened
        TC gs (fun _ : Fin (d + 1) => 0)
    have hflat_Z :=
      section43TimeProductTensor_allSlots_flattened
        TZ gs (fun _ : Fin (d + 1) => 0)
    calc
      (∫ τ : Fin (d + 1) → ℝ,
          Kboundary τ * (section43TimeProductSource gs).f τ)
          =
        TC (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          simpa [Kboundary] using hflat_boundary.symm
      _ =
        OS.S (n + r)
          (Z (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
          exact hprod gs hgsU0
      _ =
        TZ (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := rfl
      _ =
        ∫ τ : Fin (d + 1) → ℝ,
          KZ τ * (section43TimeProductSource gs).f τ := by
          simpa [KZ] using hflat_Z
  have hpoint : Kboundary τ0 = KZ τ0 := by
    exact
      eq_of_local_positiveOrthant_productSource_pairings_eq_of_continuousOn
        Kboundary KZ τ0 hτ0pos V hV_nhds
        hKboundary_cont hKZ_cont hKboundary_contOn hKZ_contOn hpair
  calc
    TC (section43TimeImagAxisProductKernel τ0)
        = Kboundary τ0 := rfl
    _ = KZ τ0 := hpoint
    _ =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
        dsimp [KZ, TZ]
        rw [hZ τ0 hτ0Z (by
          simpa [section43TimeStrictPositiveRegion] using hτ0pos)]
        rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_coord_of_strictPositive
          (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ0 (by
            simpa [section43TimeStrictPositiveRegion] using hτ0pos)]
        rfl

end OSReconstruction
