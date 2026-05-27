import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0TimeShellCoordinateChange
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairA0SourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional

/-!
# OS-II Axis-Pair BVT Bridge

This downstream companion compares the fixed-left Section 4.3 BVT probe with
the actual axis-pair spectral boundary CLM.  The comparison is not definitional:
both sides are identified with the same coordinate-height Schwinger shell by
the OS-II V.2 compact product-source smearing step.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The coordinate-height BVT delta step and the axis-pair boundary-CLM selector
have the same point value once the BVT compact product-source pairings are
transported to the same coordinate-height Schwinger shell.

This is the local OS-II V.2/Jost handoff needed before chart-overlap gluing:
the BVT probe is not identified with the boundary CLM by definition.  Both are
shown to select the same Schwinger value, and the remaining producer is the
concrete compact product-source equality `hpair`. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_coordinate_pairings_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
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
    (U : Set (Fin (d + 1) → ℝ)) (hU_nhds : U ∈ 𝓝 τ0)
    (hpair :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
        ((∫ ξ : Fin (d + 1) → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1) u χ
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (ξ i)) *
            (section43TimeProductSource gs).f ξ) =
          (∫ ξ : Fin (d + 1) → ℝ,
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ 0) g))) *
              (section43TimeProductSource gs).f ξ))
    )
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
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ
              hτpos⟩) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1) u χ
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      (let F : PositiveTimeBorchersSequence d :=
        PositiveTimeBorchersSequence.single n f hf_ord
      let G : PositiveTimeBorchersSequence d :=
        PositiveTimeBorchersSequence.single r g hg_ord
      let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
        (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
      TC (section43TimeImagAxisProductKernel τ0)) := by
  classical
  letI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  have hBVT :
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n (d + 1) u χ
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) :=
    bvt_imagAxis_eq_coordinateShiftShell_of_local_productSource_pairings_eq
      (d := d) OS lgc u χ (0 : Fin (d + 1)) f hf_ord g hg_ord hg_compact
      τ0 hτ0pos U hU_nhds hpair
  have hBoundary :
      (let F : PositiveTimeBorchersSequence d :=
        PositiveTimeBorchersSequence.single n f hf_ord
      let G : PositiveTimeBorchersSequence d :=
        PositiveTimeBorchersSequence.single r g hg_ord
      let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
        (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
      TC (section43TimeImagAxisProductKernel τ0)) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
    simpa using
      osiiAxisPair_boundaryCLM_sourceCurrent_selects_schwinger_sideCone
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
        τ0 hτ0pos hCside_pos ρZ hρZ Z hZ
  exact hBVT.trans hBoundary.symm

/-- Same-source product-tensor transport closes the BVT/boundary point
comparison.

The input is the genuine edge packet: on a common time-shell window, the
fixed-left BVT time-shell CLM and the side-cone boundary CLM agree on the same
one-sided Laplace product tensor.  The proof then uses the axis-pair boundary
source-current theorem to turn this into the compact coordinate-height pairing
equality required by the delta step. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_productTensor_transport_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
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
    (ρprod : ℝ) (hρprod : 0 < ρprod)
    (hprod :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow
              (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρprod →
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n (d + 1) u χ
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)).comp
            (osiiAxisPairHeadRestrictionCLM d))
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
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
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ
              hτpos⟩) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1) u χ
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := by
  classical
  letI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r g hg_ord
  let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
      (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
  let TBVT : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n (d + 1) u χ
  let center : Fin (d + 1) → ℝ :=
    osiiAxisPairTimeShellCenter (d := d) τ0
  have hcenter0 : 0 < center 0 := by
    simpa [center] using
      osiiAxisPairTimeShellCenter_time_pos (d := d) (hτ0pos 0)
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      center hcenter0 hCside_pos with
    ⟨ρbd, Cbd, hρbd, _hCbd, hboundary⟩
  let ρ : ℝ := min ρprod ρbd
  have hρ : 0 < ρ := lt_min hρprod hρbd
  let U : Set (Fin (d + 1) → ℝ) := osiiAxisPairTimeShellWindow (d := d) center ρ
  have hτ0U : τ0 ∈ U := by
    have hpert :
        osiiAxisPairTimeShellPerturbation (d := d) center τ0 = 0 := by
      simpa [center] using
        osiiAxisPairTimeShellPerturbation_center_self (d := d) τ0
    intro ν
    have hν := congrFun hpert ν
    simpa [U, osiiAxisPairTimeShellWindow, hν] using hρ
  have hU_nhds : U ∈ 𝓝 τ0 :=
    (isOpen_osiiAxisPairTimeShellWindow (d := d) center).mem_nhds hτ0U
  have hpair :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
        ((∫ ξ : Fin (d + 1) → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1) u χ
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (ξ i)) *
            (section43TimeProductSource gs).f ξ) =
          (∫ ξ : Fin (d + 1) → ℝ,
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ 0) g))) *
              (section43TimeProductSource gs).f ξ)) := by
    intro gs hgsU
    have hgs_prod :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) center ρprod := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgsU hτ ν) (min_le_left ρprod ρbd)
    have hgs_boundary :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) center ρbd := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgsU hτ ν) (min_le_right ρprod ρbd)
    have hflat_BVT :=
      section43TimeProductTensor_allSlots_flattened
        TBVT gs (fun _ : Fin (d + 1) => 0)
    calc
      (∫ ξ : Fin (d + 1) → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            (d := d) OS lgc n (d + 1) u χ
            (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (ξ i)) *
          (section43TimeProductSource gs).f ξ)
          =
        TBVT (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          simpa [TBVT, bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
            section43TimeImagAxisProductKernel] using hflat_BVT.symm
      _ =
        TC (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          simpa [TBVT, TC, F, G, center] using hprod gs hgs_prod
      _ =
        ∫ ξ : Fin (d + 1) → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g))) *
            (section43TimeProductSource gs).f ξ := by
          simpa [TC, F, G] using hboundary gs hgs_boundary
  simpa [F, G, TC] using
    bvt_imagAxis_eq_axisPair_boundaryCLM_of_coordinate_pairings_sideCone
      (d := d) OS lgc u χ f hf_ord g hg_ord hg_compact T hT τ0 hτ0pos
      U hU_nhds hpair hCside_ne hCside_pos ρZ hρZ Z hZ

/-- Source-current factorization form of the BVT/boundary product transport.

This is the faithful theorem shape for the remaining producer.  The BVT side is
not compared directly with the boundary CLM; instead both are compared on a
common time-shell window to the same zero-diagonal time-shell current `Z`.  The
boundary-to-`Z` half is supplied by the existing side-cone source-current
theorem, so the remaining leaf is the concrete BVT-to-`Z` product identity. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_timeCLM_product_transport_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d (d + 1)) ℂ)
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
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ
              hτpos⟩)
    (ρBVT : ℝ) (hρBVT : 0 < ρBVT)
    (hBVT_Z :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow
              (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρBVT →
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n (d + 1) u χ
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          OS.S (n + r)
            (Z (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1) u χ
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := by
  classical
  letI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r g hg_ord
  let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
      (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
  let center : Fin (d + 1) → ℝ :=
    osiiAxisPairTimeShellCenter (d := d) τ0
  have hcenter0 : 0 < center 0 := by
    simpa [center] using
      osiiAxisPairTimeShellCenter_time_pos (d := d) (hτ0pos 0)
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_timeCLM_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      center hcenter0 hCside_pos ρZ hρZ Z hZ with
    ⟨ρbd, Cbd, hρbd, _hCbd, hboundaryZ⟩
  let ρprod : ℝ := min ρBVT ρbd
  have hρprod : 0 < ρprod := lt_min hρBVT hρbd
  have hprod :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) center ρprod →
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n (d + 1) u χ
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)).comp
            (osiiAxisPairHeadRestrictionCLM d))
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
    intro gs hgs
    have hgs_BVT :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) center ρBVT := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgs hτ ν) (min_le_left ρBVT ρbd)
    have hgs_boundary :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) center ρbd := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgs hτ ν) (min_le_right ρBVT ρbd)
    calc
      bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n (d + 1) u χ
          (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
          =
        OS.S (n + r)
          (Z (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
          simpa [center] using hBVT_Z gs hgs_BVT
      _ =
        ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)).comp
          (osiiAxisPairHeadRestrictionCLM d))
          (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          simpa [TC, F, G] using (hboundaryZ gs hgs_boundary).symm
  simpa [F, G, TC] using
    bvt_imagAxis_eq_axisPair_boundaryCLM_of_productTensor_transport_sideCone
      (d := d) OS lgc u χ f hf_ord g hg_ord hg_compact T hT τ0 hτ0pos
      ρprod hρprod hprod hCside_ne hCside_pos ρZ hρZ Z hZ

/-- A represented local A0 cutoff shell gives the exact BVT-to-zero-current
product-tensor transport.

The compact source current is not definitionally the one-sided Laplace product
tensor.  The analytic bridge is supplied by
`osiiA0LocalCutoffTimeShell_productTensor_eq_bvt_of_rep_kernel_and_pairings`,
which uses the represented local A0 distribution and its imaginary-axis kernel
identity.  Unfolding the local cutoff CLM then exposes the same zero-diagonal
current under `OS.S`. -/
theorem bvt_timeSpatialRightCLM_productTensor_eq_localCutoffZeroCLM
    (n k : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d k)
    (χ : SchwartzNPoint d (n + k))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + k) → ℂ))
        (CoincidenceLocus d (n + k)))
    (S_real : (Fin k → ℝ) → ℂ)
    (U : Set (Fin k → ℝ))
    (hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real U)
    (hA0_kernel :
      ∀ ξ : Fin k → ℝ, ξ ∈ U →
        osiiA0LocalCutoffTimeShellCLM
            OS χ hχ_disj
            (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f)
            kappa2
            (section43TimeImagAxisProductKernel ξ) =
          S_real ξ)
    (hpairBVT :
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin k → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n k
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                  (section43TimeProductSource gs2).f))) :
    let fLeft : SchwartzNPoint d n :=
      section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
        (section43TimeProductSource gs1).f
    let Z : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + k) :=
      (osiiA0LocalCutoffZeroCLM χ hχ_disj).comp
        ((osConjTensorProductRightCLM (d := d) (n := n) (m := k) fLeft).comp
          (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1))
    ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
      tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n k
            (section43PositiveEnergyQuotientMap (d := d) n
              (section43NPointTimeSpatialTensor d n
                (section43TimeProductTensor
                  (fun i : Fin n =>
                    section43OneSidedLaplaceSchwartzRepresentative1D
                      (gs1 i)))
                (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
            (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
            (section43TimeProductTensor
              (fun i : Fin k =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i))) =
          OS.S (n + k)
            (Z (section43TimeProductTensor
              (fun i : Fin k =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) := by
  classical
  intro fLeft Z gs2 hgs2U
  have hA0_eq_BVT :=
    osiiA0LocalCutoffTimeShell_productTensor_eq_bvt_of_rep_kernel_and_pairings
      (d := d) n k OS lgc gs1 kappa1 kappa2 χ hχ_disj S_real U
      hRep hA0_kernel hpairBVT gs2 hgs2U
  calc
    bvt_W_pairing_descended_timeSpatialRightCLM
        (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (section43TimeProductTensor
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))
        =
      osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i))) :=
        hA0_eq_BVT.symm
    _ =
      OS.S (n + k)
        (Z (section43TimeProductTensor
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) := by
        simp [Z, fLeft, osiiA0LocalCutoffTimeShellCLM,
          osiiA0LocalCutoffSchwingerCLM,
          OsterwalderSchraderAxioms.schwingerCLM]

/-- Existential packet form of
`bvt_timeSpatialRightCLM_productTensor_eq_localCutoffZeroCLM`. -/
theorem exists_bvt_timeSpatialRightCLM_localCutoffZeroCLM_transport
    (n k : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d k)
    (χ : SchwartzNPoint d (n + k))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + k) → ℂ))
        (CoincidenceLocus d (n + k)))
    (S_real : (Fin k → ℝ) → ℂ)
    (U : Set (Fin k → ℝ))
    (hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real U)
    (hA0_kernel :
      ∀ ξ : Fin k → ℝ, ξ ∈ U →
        osiiA0LocalCutoffTimeShellCLM
            OS χ hχ_disj
            (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f)
            kappa2
            (section43TimeImagAxisProductKernel ξ) =
          S_real ξ)
    (hpairBVT :
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin k → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n k
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                  (section43TimeProductSource gs2).f))) :
    ∃ Z : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ]
        ZeroDiagonalSchwartz d (n + k),
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          bvt_W_pairing_descended_timeSpatialRightCLM
              (d := d) OS lgc n k
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (section43TimeProductTensor
                (fun i : Fin k =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i))) =
            OS.S (n + k)
              (Z (section43TimeProductTensor
                (fun i : Fin k =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) := by
  classical
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let Z : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + k) :=
    (osiiA0LocalCutoffZeroCLM χ hχ_disj).comp
      ((osConjTensorProductRightCLM (d := d) (n := n) (m := k) fLeft).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1))
  refine ⟨Z, ?_⟩
  exact
    bvt_timeSpatialRightCLM_productTensor_eq_localCutoffZeroCLM
      (d := d) n k OS lgc gs1 kappa1 kappa2 χ hχ_disj S_real U
      hRep hA0_kernel hpairBVT

/-- Represented local A0 cutoff handoff to the axis-pair boundary CLM.

Once the local A0 cutoff shell is represented on an axis-pair time-shell
window, the BVT compact product-source pairings transport the BVT time-shell
CLM to the corresponding localized zero-diagonal current.  If that same current
selects the coordinate-height Schwinger shell on the neighboring axis-pair
window, the side-cone boundary source-current theorem identifies the BVT
imaginary-axis point with the axis-pair boundary CLM point. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_represented_localCutoff_sideCone
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρBVT : ℝ) (hρBVT : 0 < ρBVT)
    (hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real
        (osiiAxisPairTimeShellWindow
          (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρBVT))
    (hA0_kernel :
      ∀ ξ : Fin (d + 1) → ℝ,
        ξ ∈ osiiAxisPairTimeShellWindow
          (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρBVT →
        osiiA0LocalCutoffTimeShellCLM
            OS χ hχ_disj
            (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f)
            kappa2
            (section43TimeImagAxisProductKernel ξ) =
          S_real ξ)
    (hpairBVT :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow
              (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρBVT →
          (∫ ξ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1)
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin (d + 1) =>
                  section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)))
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (hZ :
      let fLeft : SchwartzNPoint d n :=
        section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
          (section43TimeProductSource gs1).f
      let Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
          ZeroDiagonalSchwartz d (n + (d + 1)) :=
        (osiiA0LocalCutoffZeroCLM χ hχ_disj).comp
          ((osConjTensorProductRightCLM
              (d := d) (n := n) (m := d + 1) fLeft).comp
            (section43OrderedPullbackTimeSpatialTensorCLM
              d (d + 1) kappa2.1))
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow
            (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρZ →
        ∀ hτpos : τ ∈ section43TimeStrictPositiveRegion (d + 1),
          Z (section43TimeImagAxisProductKernel τ) =
            ⟨f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g),
              VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
                (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ hτpos⟩) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1)
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := by
  classical
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)) :=
    (osiiA0LocalCutoffZeroCLM χ hχ_disj).comp
      ((osConjTensorProductRightCLM (d := d) (n := n) (m := d + 1) fLeft).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1) kappa2.1))
  let U : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow
      (d := d) (osiiAxisPairTimeShellCenter (d := d) τ0) ρBVT
  have hBVT_Z :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          bvt_W_pairing_descended_timeSpatialRightCLM
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i))) =
            OS.S (n + (d + 1))
              (Z (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D
                    (gs2 i)))) := by
    simpa [U, Z, fLeft] using
      bvt_timeSpatialRightCLM_productTensor_eq_localCutoffZeroCLM
        (d := d) n (d + 1) OS lgc gs1 kappa1 kappa2 χ hχ_disj
        S_real U
        (by simpa [U] using hRep)
        (by simpa [U] using hA0_kernel)
        (by simpa [U] using hpairBVT)
  exact
    bvt_imagAxis_eq_axisPair_boundaryCLM_of_timeCLM_product_transport_sideCone
      (d := d) OS lgc
      (section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D
                (gs1 i)))
          (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
      (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
      f hf_ord g hg_ord hg_compact T hT τ0 hτ0pos
      hCside_ne hCside_pos ρZ hρZ Z (by simpa [Z, fLeft] using hZ)
      ρBVT hρBVT (by simpa [U] using hBVT_Z)

/-- Local-continuity version of the local A0/BVT point selector.

The MZ representative supplied by Lemma 5.1 is only known to be continuous on
its local real carrier.  This theorem is the corresponding OS-II V.2
delta-smearing handoff: product-source pairings on a neighborhood `U` identify
the BVT imaginary-axis value at `τ0`, while the continuity needed for the delta
limit is required only on a smaller neighborhood `V` inside the strict positive
orthant. -/
theorem osiiA0LocalCutoffTimeShell_rep_eq_bvt_imagAxis_of_pairings_local
    (n k : ℕ) [Nonempty (Fin k)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d k)
    (χ : SchwartzNPoint d (n + k))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + k) → ℂ))
        (CoincidenceLocus d (n + k)))
    (S_real : (Fin k → ℝ) → ℂ)
    (τ0 : Fin k → ℝ) (hτ0 : ∀ i : Fin k, 0 < τ0 i)
    (U V : Set (Fin k → ℝ))
    (hV_nhds : V ∈ 𝓝 τ0)
    (hV_sub_U : V ⊆ U)
    (hV_pos : V ⊆ section43TimeStrictPositiveRegion k)
    (hS_contOn : ContinuousOn S_real V)
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real U)
    (hpairBVT :
      ∀ gs2 : Fin k → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin k → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n k
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                  (section43TimeProductSource gs2).f))) :
    S_real τ0 =
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin k => section43ImagAxisPsiKernel (τ0 i)) := by
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let u : Section43PositiveEnergyComponent (d := d) n :=
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D
              (gs1 i)))
        (SchwartzMap.fourierTransformCLM ℂ kappa1.1))
  let χsp : SchwartzMap (Section43SpatialSpace d k) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ kappa2.1
  let KBVT : (Fin k → ℝ) → ℂ := fun ξ =>
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
      (d := d) OS lgc n k u χsp
      (fun i : Fin k => section43ImagAxisPsiKernel (ξ i))
  have hKBVT_contOn : ContinuousOn KBVT V := by
    exact
      (continuousOn_bvt_W_pairing_descended_timeSpatialRightProductMultilinear_imagAxis
        (d := d) OS lgc n k u χsp).mono
        (by
          intro ξ hξ
          simpa [section43TimeStrictPositiveRegion] using hV_pos hξ)
  have hS_cont : ContinuousAt S_real τ0 :=
    hS_contOn.continuousAt hV_nhds
  have hKBVT_cont : ContinuousAt KBVT τ0 :=
    hKBVT_contOn.continuousAt hV_nhds
  change S_real τ0 = KBVT τ0
  refine
    eq_of_local_positiveOrthant_productSource_pairings_eq_of_continuousOn
      S_real KBVT τ0 hτ0 V hV_nhds hS_cont hKBVT_cont
      hS_contOn hKBVT_contOn ?_
  intro gs2 hgs2V
  have hgs2U :
      tsupport ((section43TimeProductSource gs2).f : (Fin k → ℝ) → ℂ) ⊆ U :=
    fun ξ hξ => hV_sub_U (hgs2V hξ)
  have hS :=
    hrep (section43TimeProductSource gs2).f
      ⟨(section43TimeProductSource gs2).compact, hgs2U⟩
  have hBVT := hpairBVT gs2 hgs2U
  calc
    (∫ ξ : Fin k → ℝ, S_real ξ * (section43TimeProductSource gs2).f ξ)
        =
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
        (fLeft.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
            (section43TimeProductSource gs2).f)) := by
        simpa [fLeft] using hS.symm
    _ =
      ∫ ξ : Fin k → ℝ,
        KBVT ξ * (section43TimeProductSource gs2).f ξ := by
        simpa [KBVT, u, χsp, fLeft] using hBVT.symm

/-- Compact scalar-pairing producer from the axis-pair source current.

This is the concrete OS-II V.1/V.2 producer behind `(5.2)`: the fixed compact
MZ real-edge representative pairs through the selected time-shell current `Z`,
while the A0 cutoff packet supplies Schwinger recovery and the BVT/A0 product
pairings on the same compact carrier.  The remaining source-current input is
the scalar product-tensor equality for `Z`, which is the actual distributional
content of `(5.2)`; no local branch-representation wrapper is used here. -/
theorem osiiAxisPair_compact_scalar_pairings_from_source_current_product_eq
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord : tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
      OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK_comp : IsCompact K)
    (hK_pos : K ⊆ section43TimeStrictPositiveRegion (d + 1))
    (Z : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
    (hZ_kernel : ∀ (ξ : Fin (d + 1) → ℝ) (hξK : ξ ∈ K),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
            (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
            ((hK_pos hξK) 0)⟩)
    (hZ_product_ordered_scalar :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          OS.S (n + (d + 1))
            (Z (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)))) :
    ∃ (χ : SchwartzNPoint d (n + (d + 1)))
      (hχ_disj :
        Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
          (CoincidenceLocus d (n + (d + 1))))
      (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        K ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs2).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ ξ : Fin (d + 1) → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f))) ∧
        (∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
          tsupport ((section43TimeProductSource gs2).f :
            (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ ξ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1)
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin (d + 1) =>
                  section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f))) := by
  classical
  rcases
    exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_productSource_pairings_with_descent_and_schwinger
      (d := d) n (d + 1) OS lgc gs1 kappa1 kappa2 K hK_comp hK_pos with
    ⟨χ, hχ_disj, _hχ_time, _hCLM_respects, hχ_schwinger, hpairBVT⟩
  have hK_pos0 : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0} := by
    intro τ hτ
    exact (hK_pos hτ) 0
  rcases
    osiiAxisPair_timeShell_realRepresentative_productSource_pairing_timeCLM_on_compact
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      K hK_comp hK_pos0 Z hZ_kernel with
    ⟨Ureal, S_real, hUreal_open, hK_sub_Ureal, hS_cont, hedge, hpairZ⟩
  refine
    ⟨χ, hχ_disj, Ureal, S_real, hUreal_open, hK_sub_Ureal,
      hS_cont, hedge, ?_, ?_⟩
  · intro gs2 hgs2K
    let F : SchwartzNPoint d (n + (d + 1)) :=
      (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
          (section43TimeProductSource gs1).f).osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
          kappa2.1 (section43TimeProductSource gs2).f)
    calc
      (∫ ξ : Fin (d + 1) → ℝ,
          S_real ξ * (section43TimeProductSource gs2).f ξ)
          =
        OS.S (n + (d + 1))
          (Z (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) := by
          exact hpairZ gs2 hgs2K
      _ =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical F) := by
          exact hZ_product_ordered_scalar gs2 hgs2K
      _ =
        osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
              kappa2.1 (section43TimeProductSource gs2).f)) := by
          simpa [F] using
            (hχ_schwinger (section43TimeProductSource gs2).f hgs2K).symm
  · intro gs2 hgs2K
    exact hpairBVT gs2 hgs2K

/-- Axis-pair source-current `(5.2)` from a represented local real edge.

Once the local MZ/A0 branch-selection step has shown that the fixed A0 cutoff
distribution is represented by the selected real-edge scalar `S_real` on the
compact time shell, and that the cutoff has the Schwinger normalization there,
the finite-time source current automatically selects the same Schwinger scalar
on one-sided Laplace product tensors.  This is the actual OS II V.1/V.2
source-current transport; the compact representative is used as a distribution,
not as a pointwise endpoint shortcut. -/
theorem osiiAxisPair_sourceCurrent_product_scalar_eq_of_represented_realEdge
    (n m : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d m)
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (K : Set (Fin m → ℝ))
    (hK_pos : K ⊆ section43TimeStrictPositiveRegion m)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (S_real : (Fin m → ℝ) → ℂ)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + m))
    (hZ_kernel : ∀ (ξ : Fin m → ℝ) (hξK : ξ ∈ K),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) q f hf_ord g hg_ord ξ (hK_pos hξK)⟩)
    (hedge : ∀ τ ∈ K,
      S_real τ =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ q) g))))
    (hRep_real :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real K)
    (hχ_schwinger :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ K →
          osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d m kappa2.1 φ)) =
            OS.S (n + m)
              (ZeroDiagonalSchwartz.ofClassical
                ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                    (section43TimeProductSource gs1).f).osConjTensorProduct
                  (section43OrderedPullbackTimeSpatialTensorCLM d m kappa2.1 φ)))) :
    ∀ gs2 : Fin m → Section43CompactPositiveTimeSource1D,
      tsupport ((section43TimeProductSource gs2).f :
        (Fin m → ℝ) → ℂ) ⊆ K →
      OS.S (n + m)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m
              kappa2.1 (section43TimeProductSource gs2).f))) := by
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let Rhs : (Fin m → Section43CompactPositiveTimeSource1D) →
      ZeroDiagonalSchwartz d (n + m) := fun gs2 =>
    ZeroDiagonalSchwartz.ofClassical
      (fLeft.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m
          kappa2.1 (section43TimeProductSource gs2).f))
  have hselect :=
    schwinger_coordinateShiftShell_timeCLM_scalar_eq_of_compact_shell_pairings
      (d := d) OS q f hf_ord g hg_ord K hK_pos Z Rhs
      hZ_kernel
      (by
        intro gs2 hgs2K
        let φ : SchwartzMap (Fin m → ℝ) ℂ := (section43TimeProductSource gs2).f
        let right : SchwartzNPoint d m :=
          section43OrderedPullbackTimeSpatialTensorCLM d m kappa2.1 φ
        let F : SchwartzNPoint d (n + m) := fLeft.osConjTensorProduct right
        calc
          (∫ ξ : Fin m → ℝ,
            OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ q) g))) *
              (section43TimeProductSource gs2).f ξ)
              =
            ∫ ξ : Fin m → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ := by
              exact
                integral_mul_eq_of_eqOn_tsupport
                  (fun ξ : Fin m → ℝ =>
                    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
                      (f.osConjTensorProduct
                        (timeShiftSchwartzNPoint (d := d) (ξ q) g))))
                  S_real
                  ((section43TimeProductSource gs2).f :
                    (Fin m → ℝ) → ℂ)
                  (fun ξ hξ => (hedge ξ (hgs2K hξ)).symm)
          _ =
            osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2 φ := by
              exact (hRep_real φ
                ⟨(section43TimeProductSource gs2).compact, hgs2K⟩).symm
          _ =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj F := by
              rfl
          _ =
            OS.S (n + m) (Rhs gs2) := by
              simpa [Rhs, F, right, φ, fLeft] using hχ_schwinger φ hgs2K)
  intro gs2 hgs2K
  simpa [Rhs, fLeft] using hselect gs2 hgs2K

/-- Scalar product-source pairing handoff through the real-edge MZ value.

This is the OS-II V.2 `(5.2)` surface after the local A0/MZ representative
has been restricted to the real time shell: compact positive product-source
pairings of the selected scalar representative already identify the BVT
imaginary-axis point.  The proof intentionally avoids asking for the stronger
`RepresentsDistributionOn` package when only these scalar pairings are used. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_scalar_pairings_sideCone
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    (U V : Set (Fin (d + 1) → ℝ))
    (hV_nhds : V ∈ 𝓝 τ0)
    (hV_sub_U : V ⊆ U)
    (hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1))
    (hS_contOn : ContinuousOn S_real V)
    (hS_pair :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin (d + 1) → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)))
    (hpairBVT :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1)
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin (d + 1) =>
                  section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
              (d := d) f hf_ord g hg_ord t ht⟩)
    (hS_edge :
      S_real τ0 =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g)))) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1)
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := by
  classical
  haveI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  let Zraw : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)) :=
    Zhead.comp (osiiAxisPairHeadRestrictionCLM d)
  have hZraw :
      ∀ (ξ : Fin (d + 1) → ℝ)
        (hξ : ξ ∈ section43TimeStrictPositiveRegion (d + 1)),
        Zraw (section43TimeImagAxisProductKernel ξ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ (hξ 0)⟩ := by
    simpa [Zraw] using
      (osiiAxisPair_headRestriction_source_current_kernel
        (d := d) f hf_ord g hg_ord Zhead hZhead_respects hZhead_kernel)
  have hS_cont : ContinuousAt S_real τ0 :=
    hS_contOn.continuousAt hV_nhds
  have hS_pair_V :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ V →
          (∫ ξ : Fin (d + 1) → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)) := by
    intro gs2 hgs2V
    exact hS_pair gs2 (fun ξ hξ => hV_sub_U (hgs2V hξ))
  have hpairBVT_V :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ V →
          (∫ ξ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1)
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin (d + 1) =>
                  section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)) := by
    intro gs2 hgs2V
    exact hpairBVT gs2 (fun ξ hξ => hV_sub_U (hgs2V hξ))
  have hBVT :
      S_real τ0 =
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n (d + 1)
          (section43PositiveEnergyQuotientMap (d := d) n
            (section43NPointTimeSpatialTensor d n
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D
                    (gs1 i)))
              (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
          (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) :=
    osiiA0LocalCutoffTimeShell_pairings_eq_bvt_imagAxis
      (d := d) n (d + 1) OS lgc gs1 kappa1 kappa2 χ hχ_disj
      S_real τ0 hτ0pos V hV_nhds hV_pos hS_cont hS_contOn
      hS_pair_V hpairBVT_V
  have hBoundary :
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) :=
    osiiAxisPair_boundaryCLM_sourceCurrent_selects_schwinger_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT τ0 hτ0pos
      hCside_pos ρZ hρZ Zraw
      (fun τ _hτwin hτpos => by
        simpa using hZraw τ hτpos)
  calc
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1)
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i))
        = S_real τ0 := hBVT.symm
    _ =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := hS_edge
    _ =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := hBoundary.symm

/-- Represented local A0 cutoff handoff through the real-edge MZ value.

This is the route-correct BVT/axis-pair comparison when the local A0
representative is already known to have the OS-II real-edge value.  The BVT
point is selected by the local representative and compact product-source
pairings; the axis-pair boundary point is selected by the raw positive-energy
head current.  The proof deliberately does not identify the local cutoff
ordered-pullback current with a translated fixed right test. -/
theorem bvt_imagAxis_eq_axisPair_boundaryCLM_of_represented_localCutoff_realEdge_sideCone
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (S_real : (Fin (d + 1) → ℝ) → ℂ)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i)
    (U V : Set (Fin (d + 1) → ℝ))
    (hV_nhds : V ∈ 𝓝 τ0)
    (hV_sub_U : V ⊆ U)
    (hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1))
    (hS_contOn : ContinuousOn S_real V)
    (hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real U)
    (hpairBVT :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ U →
          (∫ ξ : Fin (d + 1) → ℝ,
              bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                (d := d) OS lgc n (d + 1)
                (section43PositiveEnergyQuotientMap (d := d) n
                  (section43NPointTimeSpatialTensor d n
                    (section43TimeProductTensor
                      (fun i : Fin n =>
                        section43OneSidedLaplaceSchwartzRepresentative1D
                          (gs1 i)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                (fun i : Fin (d + 1) =>
                  section43ImagAxisPsiKernel (ξ i)) *
              (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
              (d := d) f hf_ord g hg_ord t ht⟩)
    (hS_edge :
      S_real τ0 =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g)))) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1)
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := by
  classical
  haveI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  let Zraw : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)) :=
    Zhead.comp (osiiAxisPairHeadRestrictionCLM d)
  have hZraw :
      ∀ (ξ : Fin (d + 1) → ℝ)
        (hξ : ξ ∈ section43TimeStrictPositiveRegion (d + 1)),
        Zraw (section43TimeImagAxisProductKernel ξ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ (hξ 0)⟩ := by
    simpa [Zraw] using
      (osiiAxisPair_headRestriction_source_current_kernel
        (d := d) f hf_ord g hg_ord Zhead hZhead_respects hZhead_kernel)
  have hBVT :
      S_real τ0 =
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n (d + 1)
          (section43PositiveEnergyQuotientMap (d := d) n
            (section43NPointTimeSpatialTensor d n
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D
                    (gs1 i)))
              (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
          (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
          (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) :=
    osiiA0LocalCutoffTimeShell_rep_eq_bvt_imagAxis_of_pairings_local
      (d := d) n (d + 1) OS lgc gs1 kappa1 kappa2 χ hχ_disj
      S_real τ0 hτ0pos U V hV_nhds hV_sub_U hV_pos hS_contOn hRep hpairBVT
  have hBoundary :
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) :=
    osiiAxisPair_boundaryCLM_sourceCurrent_selects_schwinger_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT τ0 hτ0pos
      hCside_pos ρZ hρZ Zraw
      (fun τ _hτwin hτpos => by
        simpa using hZraw τ hτpos)
  calc
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n (d + 1)
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D
                  (gs1 i)))
            (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
        (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
        (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i))
        = S_real τ0 := hBVT.symm
    _ =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := hS_edge
    _ =
      ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
        (osiiAxisPairHeadRestrictionCLM d))
        (section43TimeImagAxisProductKernel τ0) := hBoundary.symm

/-- Extract the raw axis-pair real representative and expose the exact local
A0 representation leaf.

The raw head current supplies the valid axis-pair boundary source current.  The
returned `S_real` is the Lemma 5.1/MZ real-edge representative near `τ0`.
Once that same representative is proved to represent the local A0 cutoff
time-shell distribution, and the compact BVT/A0 pairings are available on its
carrier, the BVT imaginary-axis point equals the axis-pair boundary CLM point. -/
theorem exists_bvt_axisPair_realEdge_handoff_from_raw_current
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        τ0 ∈ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (SCV.RepresentsDistributionOn
            (osiiA0LocalCutoffTimeShellCLM
              OS χ hχ_disj
              (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f)
              kappa2)
            S_real Ureal →
          (∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs2).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal →
              (∫ ξ : Fin (d + 1) → ℝ,
                  bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                    (d := d) OS lgc n (d + 1)
                    (section43PositiveEnergyQuotientMap (d := d) n
                      (section43NPointTimeSpatialTensor d n
                        (section43TimeProductTensor
                          (fun i : Fin n =>
                            section43OneSidedLaplaceSchwartzRepresentative1D
                              (gs1 i)))
                        (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                    (fun i : Fin (d + 1) =>
                      section43ImagAxisPsiKernel (ξ i)) *
                  (section43TimeProductSource gs2).f ξ) =
                osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
                  ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                      (section43TimeProductSource gs1).f).osConjTensorProduct
                    (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                      kappa2.1 (section43TimeProductSource gs2).f))) →
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
            ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
              (osiiAxisPairHeadRestrictionCLM d))
              (section43TimeImagAxisProductKernel τ0)) := by
  classical
  haveI : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) := hCside_ne
  let Zraw : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)) :=
    Zhead.comp (osiiAxisPairHeadRestrictionCLM d)
  have hZraw :
      ∀ (ξ : Fin (d + 1) → ℝ)
        (hξ : ξ ∈ section43TimeStrictPositiveRegion (d + 1)),
        Zraw (section43TimeImagAxisProductKernel ξ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ (hξ 0)⟩ := by
    simpa [Zraw] using
      (osiiAxisPair_headRestriction_source_current_kernel
        (d := d) f hf_ord g hg_ord Zhead hZhead_respects hZhead_kernel)
  have hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i := by
    simpa [section43TimeStrictPositiveRegion] using hW_pos hτ0W
  rcases
    osiiAxisPair_timeShell_realRepresentative_selects_timeCLM_on_open_chart
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT W hW_open
      τ0 hτ0W hW_pos Zraw
      (fun ξ hξW => by
        simpa using hZraw ξ (hW_pos hξW)) with
    ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_contOn, hselect⟩
  refine ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_contOn, ?_⟩
  intro hRep hpairBVT
  let V : Set (Fin (d + 1) → ℝ) :=
    Ureal ∩ section43TimeStrictPositiveRegion (d + 1)
  have hV_nhds : V ∈ 𝓝 τ0 := by
    exact
      Filter.inter_mem
        (hUreal_open.mem_nhds hτ0Ureal)
        ((isOpen_section43TimeStrictPositiveRegion (d + 1)).mem_nhds
          (by simpa [section43TimeStrictPositiveRegion] using hτ0pos))
  have hV_sub_U : V ⊆ Ureal := by
    intro ξ hξ
    exact hξ.1
  have hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1) := by
    intro ξ hξ
    exact hξ.2
  have hS_contOn_V : ContinuousOn S_real V :=
    hS_contOn.mono hV_sub_U
  have hS_edge :
      S_real τ0 =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
    calc
      S_real τ0 =
          (OsterwalderSchraderAxioms.schwingerCLM
              (d := d) OS (n + (d + 1))).comp Zraw
            (section43TimeImagAxisProductKernel τ0) := hselect
      _ =
          OS.S (n + (d + 1))
            (Zraw (section43TimeImagAxisProductKernel τ0)) := rfl
      _ =
          OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
            rw [hZraw τ0 (by
              simpa [section43TimeStrictPositiveRegion] using hτ0pos)]
            rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord τ0 (by
                simpa [section43TimeStrictPositiveRegion] using hτ0pos)]
  exact
    bvt_imagAxis_eq_axisPair_boundaryCLM_of_represented_localCutoff_realEdge_sideCone
      (d := d) n OS lgc gs1 kappa1 kappa2 χ hχ_disj S_real τ0 hτ0pos
      Ureal V hV_nhds hV_sub_U hV_pos hS_contOn_V hRep hpairBVT
      f hf_ord g hg_ord hg_compact T hT hCside_ne hCside_pos
      ρZ hρZ Zhead hZhead_respects hZhead_kernel hS_edge

/-- Extract the raw axis-pair real representative and discharge its local A0
representation leaf from scalar time-shell local representatives.

This is the scalar MZ version of
`exists_bvt_axisPair_realEdge_handoff_from_raw_current`: after the frozen
left/spatial variables have been integrated out, local time-shell
representatives that glue and agree with the selected real-edge scalar already
give the `RepresentsDistributionOn` premise needed by the raw-current handoff.
The remaining branch work is therefore the actual OS-II local representative
construction, not an extra full-coordinate bookkeeping wrapper. -/
theorem exists_bvt_axisPair_realEdge_handoff_from_scalar_timeShell_local_reps
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        τ0 ∈ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ {ι : Type*}
          (N : ι → Set (Fin (d + 1) → ℝ))
          (D : ι → (Fin (d + 1) → ℝ) → ℂ),
          Ureal ⊆ ⋃ i, N i →
          (∀ i, IsOpen (N i)) →
          (∀ i, ContinuousOn (D i) (N i)) →
          (∀ i,
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffTimeShellCLM
                OS χ hχ_disj
                (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f)
                kappa2)
              (D i) (N i)) →
          (∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) →
          Set.EqOn (SCV.glued_iUnion N D) S_real Ureal →
          (∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs2).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal →
              (∫ ξ : Fin (d + 1) → ℝ,
                  bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                    (d := d) OS lgc n (d + 1)
                    (section43PositiveEnergyQuotientMap (d := d) n
                      (section43NPointTimeSpatialTensor d n
                        (section43TimeProductTensor
                          (fun i : Fin n =>
                            section43OneSidedLaplaceSchwartzRepresentative1D
                              (gs1 i)))
                        (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                    (fun i : Fin (d + 1) =>
                      section43ImagAxisPsiKernel (ξ i)) *
                  (section43TimeProductSource gs2).f ξ) =
                osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
                  ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                      (section43TimeProductSource gs1).f).osConjTensorProduct
                    (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                      kappa2.1 (section43TimeProductSource gs2).f))) →
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
            ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
              (osiiAxisPairHeadRestrictionCLM d))
              (section43TimeImagAxisProductKernel τ0)) := by
  classical
  rcases
    exists_bvt_axisPair_realEdge_handoff_from_raw_current
      (d := d) n OS lgc gs1 kappa1 kappa2 χ hχ_disj f hf_ord g hg_ord
      hg_compact T hT W hW_open τ0 hτ0W hW_pos hCside_ne hCside_pos
      ρZ hρZ Zhead hZhead_respects hZhead_kernel with
    ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_cont, hraw⟩
  refine ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_cont, ?_⟩
  intro ι N D hcover hN_open hD_cont hD_rep hEq hglue_eq hpairBVT
  have hRep_glue :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        (SCV.glued_iUnion N D) Ureal := by
    exact
      SCV.representsDistributionOn_glued_iUnion
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        N D Ureal hcover hN_open hD_cont hD_rep hEq
  have hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f)
          kappa2)
        S_real Ureal :=
    SCV.representsDistributionOn_congr_on_subset
      (osiiA0LocalCutoffTimeShellCLM
        OS χ hχ_disj
        (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
          (section43TimeProductSource gs1).f)
        kappa2)
      hRep_glue hglue_eq (fun _ hx => hx)
  exact hraw hRep hpairBVT

/-- Extract the raw axis-pair real representative and discharge the local A0
representation leaf from glued local cutoff representatives.

The last scalar premise is the honest remaining OS-II identification: the
time-shell scalar obtained from the glued local A0 representative must agree on
the returned real carrier with the Lemma 5.1/MZ real-edge selector `S_real`.
Given that equality, the A0 gluing theorem supplies the
`RepresentsDistributionOn` hypothesis consumed by the raw-current BVT handoff. -/
theorem exists_bvt_axisPair_realEdge_handoff_from_glued_local_cutoff_reps
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (χ : SchwartzNPoint d (n + (d + 1)))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
        (CoincidenceLocus d (n + (d + 1))))
    (hfLeft_comp :
      HasCompactSupport
        ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
            (section43TimeProductSource gs1).f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        τ0 ∈ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ {ι : Type*}
          (χloc : ι → SchwartzNPoint d (n + (d + 1)))
          (hχloc_disj : ∀ i : ι,
            Disjoint (tsupport (χloc i : NPointDomain d (n + (d + 1)) → ℂ))
              (CoincidenceLocus d (n + (d + 1))))
          (N : ι → Set (NPointDomain d (n + (d + 1))))
          (D : ι → NPointDomain d (n + (d + 1)) → ℂ),
          (∀ x : NPointDomain d (n + (d + 1)),
            x ∉ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              SCV.glued_iUnion N D x = 0) →
          (∀ x ∈
            { x : NPointDomain d (n + (d + 1)) |
              section43QTime (d := d) (n := d + 1)
                (section43DiffCoordRealCLE d (d + 1)
                  (splitLast n (d + 1) x)) ∈ Ureal },
            x ∈ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              x ∈ ⋃ i, N i) →
          (∀ i, IsOpen (N i)) →
          (∀ i, ContinuousOn (D i) (N i)) →
          (∀ i : ι,
            Set.EqOn (χloc i : NPointDomain d (n + (d + 1)) → ℂ)
              (χ : NPointDomain d (n + (d + 1)) → ℂ) (N i)) →
          (∀ i,
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS (χloc i) (hχloc_disj i))
              (D i) (N i)) →
          (∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) →
          Set.EqOn
            (osiiA0_timeShellScalarFromCoordinateRepresentative
              (fun xL τ η =>
                SCV.glued_iUnion N D
                  (Fin.append xL
                    (osiiA0_rightFromTimeSpatial d (d + 1) τ η)))
              (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f)
              kappa2)
            S_real Ureal →
          (∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs2).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal →
              (∫ ξ : Fin (d + 1) → ℝ,
                  bvt_W_pairing_descended_timeSpatialRightProductMultilinear
                    (d := d) OS lgc n (d + 1)
                    (section43PositiveEnergyQuotientMap (d := d) n
                      (section43NPointTimeSpatialTensor d n
                        (section43TimeProductTensor
                          (fun i : Fin n =>
                            section43OneSidedLaplaceSchwartzRepresentative1D
                              (gs1 i)))
                        (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
                    (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
                    (fun i : Fin (d + 1) =>
                      section43ImagAxisPsiKernel (ξ i)) *
                  (section43TimeProductSource gs2).f ξ) =
                osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
                  ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                      (section43TimeProductSource gs1).f).osConjTensorProduct
                    (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                      kappa2.1 (section43TimeProductSource gs2).f))) →
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
            ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
              (osiiAxisPairHeadRestrictionCLM d))
              (section43TimeImagAxisProductKernel τ0)) := by
  classical
  rcases
    exists_bvt_axisPair_realEdge_handoff_from_raw_current
      (d := d) n OS lgc gs1 kappa1 kappa2 χ hχ_disj f hf_ord g
      hg_ord hg_compact T hT W hW_open τ0 hτ0W hW_pos hCside_ne
      hCside_pos ρZ hρZ Zhead hZhead_respects hZhead_kernel with
    ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_cont, hhandoff⟩
  refine ⟨Ureal, S_real, hUreal_open, hτ0Ureal, hS_cont, ?_⟩
  intro ι χloc hχloc_disj N D hH_zero_off hcover hN_open hD_cont
    hχ_eq hD_rep_local hEq hShell_eq hpairBVT
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let Hshell : (Fin (d + 1) → ℝ) → ℂ :=
    osiiA0_timeShellScalarFromCoordinateRepresentative
      (fun xL τ η =>
        SCV.glued_iUnion N D
          (Fin.append xL
            (osiiA0_rightFromTimeSpatial d (d + 1) τ η)))
      fLeft kappa2
  have hRep_shell :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        Hshell Ureal := by
    simpa [fLeft, Hshell] using
      osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_local_cutoff_reps_rightTimeCylinder_open
        (d := d) (n := n) (m := d + 1) (ι := ι)
        OS χ hχ_disj χloc hχloc_disj fLeft hfLeft_comp kappa2 N D
        Ureal hUreal_open hH_zero_off hcover hN_open hD_cont hχ_eq
        hD_rep_local hEq
  have hRep_real :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        S_real Ureal := by
    exact
      SCV.representsDistributionOn_congr_on_subset
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        hRep_shell hShell_eq (fun _ hx => hx)
  exact hhandoff (by simpa [fLeft] using hRep_real) hpairBVT

/-- Compact-carrier version of the raw axis-pair BVT handoff.

This is the order used in OS-II V.2: first choose a compact strict-positive
right-time carrier around the target point, build the uniform local A0 cutoff
and compact product-source pairings on that carrier, then apply the raw
axis-pair real-edge selector.  The only remaining continuation hypotheses are
the genuine full-coordinate MZ/A0 branch-selection facts on the compact carrier. -/
theorem exists_bvt_axisPair_realEdge_handoff_from_compact_cutoff_glued_reps
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
    ∃ (Uchart : Set (Fin (d + 1) → ℝ))
      (K V : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ)
      (χ : SchwartzNPoint d (n + (d + 1))),
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
          (CoincidenceLocus d (n + (d + 1))) ∧
        IsOpen Uchart ∧
        IsCompact K ∧
        τ0 ∈ K ∧
        K ⊆ section43TimeStrictPositiveRegion (d + 1) ∧
        K ⊆ Uchart ∧
        V ∈ 𝓝 τ0 ∧
        V ⊆ K ∧
        ContinuousOn S_real V ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∀ {ι : Type*}
          (χloc : ι → SchwartzNPoint d (n + (d + 1)))
          (hχloc_disj : ∀ i : ι,
            Disjoint (tsupport (χloc i : NPointDomain d (n + (d + 1)) → ℂ))
              (CoincidenceLocus d (n + (d + 1))))
          (N : ι → Set (NPointDomain d (n + (d + 1))))
          (D : ι → NPointDomain d (n + (d + 1)) → ℂ),
          (∀ x : NPointDomain d (n + (d + 1)),
            x ∉ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              SCV.glued_iUnion N D x = 0) →
          (∀ x ∈
            { x : NPointDomain d (n + (d + 1)) |
              section43QTime (d := d) (n := d + 1)
                (section43DiffCoordRealCLE d (d + 1)
                  (splitLast n (d + 1) x)) ∈ Uchart },
            x ∈ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              x ∈ ⋃ i, N i) →
          (∀ i, IsOpen (N i)) →
          (∀ i, ContinuousOn (D i) (N i)) →
          (∀ i : ι,
            Set.EqOn (χloc i : NPointDomain d (n + (d + 1)) → ℂ)
              (χ : NPointDomain d (n + (d + 1)) → ℂ) (N i)) →
          (∀ i,
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS (χloc i) (hχloc_disj i))
              (D i) (N i)) →
          (∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) →
          Set.EqOn
            (osiiA0_timeShellScalarFromCoordinateRepresentative
              (fun xL τ η =>
                SCV.glued_iUnion N D
                  (Fin.append xL
                    (osiiA0_rightFromTimeSpatial d (d + 1) τ η)))
              (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f)
              kappa2)
            (fun τ : Fin (d + 1) → ℝ =>
              OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K →
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
            ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
              (osiiAxisPairHeadRestrictionCLM d))
              (section43TimeImagAxisProductKernel τ0)) := by
  classical
  rcases Metric.nhds_basis_closedBall.mem_iff.mp
      (hW_open.mem_nhds hτ0W) with
    ⟨ρ, hρ, hρ_sub_W⟩
  let R : ℝ := ρ / 2
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hR_lt_ρ : R < ρ := by
    dsimp [R]
    linarith
  let Uchart : Set (Fin (d + 1) → ℝ) := Metric.ball τ0 ρ
  let K : Set (Fin (d + 1) → ℝ) := Metric.closedBall τ0 R
  let V : Set (Fin (d + 1) → ℝ) := Metric.ball τ0 R
  have hUchart_open : IsOpen Uchart := by
    change IsOpen (Metric.ball τ0 ρ)
    exact Metric.isOpen_ball
  have hK_comp : IsCompact K := by
    simpa [K] using isCompact_closedBall τ0 R
  have hτ0K : τ0 ∈ K := by
    simpa [K] using Metric.mem_closedBall_self (x := τ0) (ε := R) hR.le
  have hK_sub_closedρ : K ⊆ Metric.closedBall τ0 ρ := by
    intro τ hτ
    have hdist : dist τ τ0 ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_comm] using hτ
    have hR_le_ρ : R ≤ ρ := le_of_lt hR_lt_ρ
    simpa [Metric.mem_closedBall, dist_comm] using le_trans hdist hR_le_ρ
  have hK_sub_W : K ⊆ W := fun τ hτ => hρ_sub_W (hK_sub_closedρ hτ)
  have hK_pos : K ⊆ section43TimeStrictPositiveRegion (d + 1) :=
    fun τ hτ => hW_pos (hK_sub_W hτ)
  have hK_pos0 : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0} :=
    fun τ hτ => (hK_pos hτ) 0
  have hK_sub_Uchart : K ⊆ Uchart := by
    intro τ hτ
    have hdist : dist τ τ0 ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_comm] using hτ
    have hdist_lt : dist τ τ0 < ρ := lt_of_le_of_lt hdist hR_lt_ρ
    simpa [Uchart, Metric.mem_ball, dist_comm] using hdist_lt
  have hV_nhds : V ∈ 𝓝 τ0 := by
    simpa [V] using Metric.ball_mem_nhds τ0 hR
  have hV_sub_K : V ⊆ K := by
    intro τ hτ
    exact Metric.ball_subset_closedBall hτ
  have hV_pos : V ⊆ section43TimeStrictPositiveRegion (d + 1) :=
    fun τ hτ => hK_pos (hV_sub_K hτ)
  have hτ0pos : ∀ i : Fin (d + 1), 0 < τ0 i :=
    hW_pos hτ0W
  let Zraw : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)) :=
    Zhead.comp (osiiAxisPairHeadRestrictionCLM d)
  have hZraw :
      ∀ (ξ : Fin (d + 1) → ℝ) (hξK : ξ ∈ K),
        Zraw (section43TimeImagAxisProductKernel ξ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
              ((hK_pos hξK) 0)⟩ := by
    intro ξ hξK
    simpa [Zraw] using
      osiiAxisPair_headRestriction_source_current_kernel
        (d := d) f hf_ord g hg_ord Zhead hZhead_respects hZhead_kernel
        ξ (hK_pos hξK)
  rcases
    osiiAxisPair_timeShell_realRepresentative_productSource_pairing_timeCLM_on_compact
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK_comp
      hK_pos0 Zraw hZraw with
    ⟨Ureal, S_real, _hUreal_open, hK_sub_Ureal, hS_cont, hedge, hpair_raw⟩
  rcases
    exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_productSource_pairings_with_descent_and_schwinger
      (d := d) n (d + 1) OS lgc gs1 kappa1 kappa2 K hK_comp hK_pos with
    ⟨χ, hχ_disj, _hχ_time, _hdesc, hχ_schwinger, hpairBVT⟩
  have hS_cont_V : ContinuousOn S_real V :=
    hS_cont.mono (fun τ hτ => hK_sub_Ureal (hV_sub_K hτ))
  refine
    ⟨Uchart, K, V, S_real, χ, hχ_disj, hUchart_open, hK_comp,
      hτ0K, hK_pos, hK_sub_Uchart, hV_nhds, hV_sub_K, hS_cont_V,
      hedge, ?_⟩
  intro ι χloc hχloc_disj N D hH_zero_off hcover hN_open hD_cont
    hχ_eq hD_rep_local hEq hShell_schwinger
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  let Hshell : (Fin (d + 1) → ℝ) → ℂ :=
    osiiA0_timeShellScalarFromCoordinateRepresentative
      (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d (d + 1) τ η)))
      fLeft kappa2
  have hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ) := by
    simpa [fLeft] using
      osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_product
        (d := d) (n := n) gs1 kappa1
  have hRep_shell :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        Hshell Uchart := by
    simpa [fLeft, Hshell] using
      osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_local_cutoff_reps_rightTimeCylinder_open
        (d := d) (n := n) (m := d + 1) (ι := ι)
        OS χ hχ_disj χloc hχloc_disj fLeft hfLeft_comp kappa2 N D
        Uchart hUchart_open hH_zero_off hcover hN_open hD_cont hχ_eq
        hD_rep_local hEq
  have hRep_real :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        S_real K := by
    have hShell_eq : Set.EqOn Hshell S_real K := by
      intro τ hτ
      calc
        Hshell τ =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g))) :=
          hShell_schwinger hτ
        _ = S_real τ := (hedge τ hτ).symm
    exact
      SCV.representsDistributionOn_congr_on_subset
        (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft kappa2)
        hRep_shell hShell_eq hK_sub_Uchart
  have hS_edge :
      S_real τ0 =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ0 0) g))) := by
    exact hedge τ0 hτ0K
  have hZraw_strict :
      ∀ (ξ : Fin (d + 1) → ℝ) (hξK : ξ ∈ K),
        Zraw (section43TimeImagAxisProductKernel ξ) =
          ⟨f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0) g),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) (0 : Fin (d + 1)) f hf_ord g hg_ord ξ
              (hK_pos hξK)⟩ := by
    intro ξ hξK
    simpa using hZraw ξ hξK
  have hZ_product_ordered_scalar :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          OS.S (n + (d + 1))
            (Zraw (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f))) := by
    exact
      osiiAxisPair_sourceCurrent_product_scalar_eq_of_represented_realEdge
        (d := d) n (d + 1) OS gs1 kappa1 kappa2 (0 : Fin (d + 1))
        f hf_ord g hg_ord K hK_pos χ hχ_disj S_real Zraw hZraw_strict
        hedge (by simpa [fLeft] using hRep_real) hχ_schwinger
  have hS_pair :
      ∀ gs2 : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs2).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
          (∫ ξ : Fin (d + 1) → ℝ,
              S_real ξ * (section43TimeProductSource gs2).f ξ) =
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                  (section43TimeProductSource gs1).f).osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
                  kappa2.1 (section43TimeProductSource gs2).f)) := by
    intro gs2 hgs2K
    let F : SchwartzNPoint d (n + (d + 1)) :=
      (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
          (section43TimeProductSource gs1).f).osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
          kappa2.1 (section43TimeProductSource gs2).f)
    calc
      (∫ ξ : Fin (d + 1) → ℝ,
          S_real ξ * (section43TimeProductSource gs2).f ξ)
          =
        OS.S (n + (d + 1))
          (Zraw (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)))) := by
          exact hpair_raw gs2 hgs2K
      _ =
        OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical F) := by
          simpa [F] using hZ_product_ordered_scalar gs2 hgs2K
      _ =
        osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          ((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
              (section43TimeProductSource gs1).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d (d + 1)
              kappa2.1 (section43TimeProductSource gs2).f)) := by
          simpa [F] using
            (hχ_schwinger (section43TimeProductSource gs2).f hgs2K).symm
  exact
    bvt_imagAxis_eq_axisPair_boundaryCLM_of_scalar_pairings_sideCone
      (d := d) n OS lgc gs1 kappa1 kappa2 χ hχ_disj S_real τ0 hτ0pos
      K V hV_nhds hV_sub_K hV_pos hS_cont_V
      hS_pair hpairBVT
      f hf_ord g hg_ord hg_compact T hT hCside_ne hCside_pos
      ρZ hρZ Zhead hZhead_respects hZhead_kernel hS_edge

/-- Compact-carrier axis-pair BVT handoff from support-local branch selection.

This discharges the scalar compact-shell equality required by
`exists_bvt_axisPair_realEdge_handoff_from_compact_cutoff_glued_reps` using the
local MZ/A0 branch-selection theorem
`osiiA0_glued_timeShellScalar_schwinger_of_local_weight_support`.  The remaining
input is no longer an opaque equality of time-shell scalars: each weighted
slice point must be covered by a local branch that agrees there with the
Schwinger-normalized coordinate representative. -/
theorem exists_bvt_axisPair_realEdge_handoff_from_compact_cutoff_local_branch_selection
    (n : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (kappa2 : Section43SpatialCompactSource d (d + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d (d + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (d + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (d + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (d + 1) → ℂ))
    (T : ℝ) (hT : 0 < T)
    (W : Set (Fin (d + 1) → ℝ))
    (hW_open : IsOpen W)
    (τ0 : Fin (d + 1) → ℝ)
    (hτ0W : τ0 ∈ W)
    (hW_pos : W ⊆ section43TimeStrictPositiveRegion (d + 1))
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_ne : NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ)))
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (ρZ : ℝ) (hρZ : 0 < ρZ)
    (Zhead : SchwartzMap ℝ ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + (d + 1)))
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
    ∃ (Uchart : Set (Fin (d + 1) → ℝ))
      (K V : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ)
      (χ : SchwartzNPoint d (n + (d + 1))),
      Disjoint (tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ))
          (CoincidenceLocus d (n + (d + 1))) ∧
        IsOpen Uchart ∧
        IsCompact K ∧
        τ0 ∈ K ∧
        K ⊆ section43TimeStrictPositiveRegion (d + 1) ∧
        K ⊆ Uchart ∧
        V ∈ 𝓝 τ0 ∧
        V ⊆ K ∧
        ContinuousOn S_real V ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∀ {ι : Type*}
          (χloc : ι → SchwartzNPoint d (n + (d + 1)))
          (hχloc_disj : ∀ i : ι,
            Disjoint (tsupport (χloc i : NPointDomain d (n + (d + 1)) → ℂ))
              (CoincidenceLocus d (n + (d + 1))))
          (N : ι → Set (NPointDomain d (n + (d + 1))))
          (D : ι → NPointDomain d (n + (d + 1)) → ℂ)
          (Hsch :
            NPointDomain d n → (Fin (d + 1) → ℝ) →
              Section43SpatialSpace d (d + 1) → ℂ),
          (∀ x : NPointDomain d (n + (d + 1)),
            x ∉ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              SCV.glued_iUnion N D x = 0) →
          (∀ x ∈
            { x : NPointDomain d (n + (d + 1)) |
              section43QTime (d := d) (n := d + 1)
                (section43DiffCoordRealCLE d (d + 1)
                  (splitLast n (d + 1) x)) ∈ Uchart },
            x ∈ tsupport (χ : NPointDomain d (n + (d + 1)) → ℂ) →
              x ∈ ⋃ i, N i) →
          (∀ i, IsOpen (N i)) →
          (∀ i, ContinuousOn (D i) (N i)) →
          (∀ i : ι,
            Set.EqOn (χloc i : NPointDomain d (n + (d + 1)) → ℂ)
              (χ : NPointDomain d (n + (d + 1)) → ℂ) (N i)) →
          (∀ i,
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS (χloc i) (hχloc_disj i))
              (D i) (N i)) →
          (∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) →
          (∀ τ ∈ K,
            ∀ e : NPointDomain d n × Section43SpatialSpace d (d + 1),
              e.1 ∈ tsupport
                (((section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                    (section43TimeProductSource gs1).f).osConj :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) →
              e.2 ∈ tsupport
                (kappa2.1 : Section43SpatialSpace d (d + 1) → ℂ) →
                ∃ i : ι,
                  Fin.append e.1
                      (osiiA0_rightFromTimeSpatial d (d + 1) τ e.2) ∈ N i ∧
                    D i (Fin.append e.1
                      (osiiA0_rightFromTimeSpatial d (d + 1) τ e.2)) =
                      Hsch e.1 τ e.2) →
          Set.EqOn
            (osiiA0_timeShellScalarFromCoordinateRepresentative Hsch
              (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f)
              kappa2)
            (fun τ : Fin (d + 1) → ℝ =>
              OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K →
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n (d + 1)
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin (d + 1) => section43ImagAxisPsiKernel (τ0 i)) =
            ((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single (d + 1) g hg_ord)).comp
              (osiiAxisPairHeadRestrictionCLM d))
              (section43TimeImagAxisProductKernel τ0)) := by
  classical
  rcases
    exists_bvt_axisPair_realEdge_handoff_from_compact_cutoff_glued_reps
      (d := d) n OS lgc gs1 kappa1 kappa2 f hf_ord g hg_ord hg_compact
      T hT W hW_open τ0 hτ0W hW_pos hCside_ne hCside_pos ρZ hρZ
      Zhead hZhead_respects hZhead_kernel with
    ⟨Uchart, K, V, S_real, χ, hχ_disj, hUchart_open, hK_comp, hτ0K,
      hK_pos, hK_sub_Uchart, hV_nhds, hV_sub_K, hS_cont_V, hedge,
      hcontinue⟩
  refine
    ⟨Uchart, K, V, S_real, χ, hχ_disj, hUchart_open, hK_comp, hτ0K,
      hK_pos, hK_sub_Uchart, hV_nhds, hV_sub_K, hS_cont_V, hedge, ?_⟩
  intro ι χloc hχloc_disj N D Hsch hH_zero_off hcover hN_open hD_cont
    hχ_eq hD_rep_local hEq hBranch hSch
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  have hShell_schwinger :
      Set.EqOn
        (osiiA0_timeShellScalarFromCoordinateRepresentative
          (fun xL τ η =>
            SCV.glued_iUnion N D
              (Fin.append xL
                (osiiA0_rightFromTimeSpatial d (d + 1) τ η)))
          fLeft kappa2)
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) K := by
    simpa [fLeft] using
      osiiA0_glued_timeShellScalar_schwinger_of_local_weight_support
        (d := d) (n := n) (m := d + 1)
        N D Hsch fLeft kappa2 K
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + (d + 1)) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
        hEq hBranch hSch
  exact
    hcontinue χloc hχloc_disj N D hH_zero_off hcover hN_open hD_cont
      hχ_eq hD_rep_local hEq (by simpa [fLeft] using hShell_schwinger)

end OSReconstruction
