import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorRealEdge

/-!
# OS-II Schwinger Source-Current Shells

This upstream companion records the Schwinger-side source-current identities
that do not depend on downstream boundary-value carriers.  They are the OS-II
V.2 finite product-source transport step: strict positive time sources select
honest zero-diagonal Schwinger shells, and compact product-source pairings can
be evaluated through the corresponding finite-time CLM.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- A strictly positive Euclidean time shift preserves zero-diagonal
admissibility of an OS tensor product whose two factors have ordered
positive-time support. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (t : ℝ) (ht : 0 < t) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f)
      (g := timeShiftSchwartzNPoint (d := d) t g)
      hf_ord
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) t ht g hg_ord)

/-- Coordinate-height zero-diagonal shell from positivity of just the selected
coordinate.  This is the form used by the axis-pair chart: the chart selects
one physical time height, while the remaining auxiliary source coordinates are
only part of the compact product-source smearing device. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
    {m n r : ℕ}
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξq : 0 < ξ q) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q) g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
      (d := d) f hf_ord g hg_ord (ξ q) hξq

/-- On the strict positive orthant, the total OS-II finite-time shift is
strictly positive. -/
theorem section43TimeStrictPositiveRegion_sum_pos
    {m : ℕ} [Nonempty (Fin m)] {ξ : Fin m → ℝ}
    (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    0 < ∑ p : Fin m, ξ p := by
  classical
  exact
    Finset.sum_pos
      (fun p _ => hξ p)
      Finset.univ_nonempty

/-- The OS-II strict positive orthant gives honest zero-diagonal shifted shells
for the Schwinger functional. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
      (d := d) f hf_ord g hg_ord
      (∑ p : Fin m, ξ p)
      (section43TimeStrictPositiveRegion_sum_pos (m := m) hξ)

/-- The totalized `ofClassical` branch is the honest shifted-shell subtype on
the OS-II strict positive orthant. -/
theorem ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) =
      ⟨f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g),
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
          (d := d) f hf_ord g hg_ord ξ hξ⟩ := by
  exact
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
        (d := d) f hf_ord g hg_ord ξ hξ)

/-- A strict-positive finite-time vector gives an honest zero-diagonal shell
when only one selected coordinate is used as the Euclidean time shift. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
    {m n r : ℕ}
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q) g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
      (d := d) f hf_ord g hg_ord (ξ q) (hξ q)

/-- Coordinate-height `ofClassical` identification on the strict positive
orthant. -/
theorem ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_coord_of_strictPositive
    {m n r : ℕ}
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q) g)) =
      ⟨f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q) g),
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
          (d := d) q f hf_ord g hg_ord ξ hξ⟩ := by
  exact
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q) g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
        (d := d) q f hf_ord g hg_ord ξ hξ)

/-- Localized product-source evaluation for a coordinate-height Schwinger
shell.

This is the coordinate analogue of the total-height source-current transport:
the time-shell CLM only has to agree with the honest shifted-shell kernel on
the support of the compact product source.  It is the exact handoff used by
the axis-pair chart, where the selected real-edge shell depends on one
distinguished coordinate height rather than on the total height. -/
theorem schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (gs : Fin m → Section43CompactPositiveTimeSource1D)
    (hZ : ∀ (ξ : Fin m → ℝ)
      (hξ : ξ ∈ tsupport ((section43TimeProductSource gs).f :
        (Fin m → ℝ) → ℂ)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) q f hf_ord g hg_ord ξ
            ((section43TimeProductSource gs).positive hξ)⟩) :
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q) g))) *
        (section43TimeProductSource gs).f ξ) =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs (fun _ : Fin m => 0)
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q) g))) *
        (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        T (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun ξ : Fin m → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (ξ q) g))))
            (fun ξ : Fin m → ℝ =>
              T (section43TimeImagAxisProductKernel ξ))
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            ?_
        intro ξ hξ
        have hξpos : ξ ∈ section43TimeStrictPositiveRegion m :=
          (section43TimeProductSource gs).positive hξ
        calc
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ q) g)))
              =
            OS.S (n + r)
              (⟨f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) (ξ q) g),
                VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
                  (d := d) q f hf_ord g hg_ord ξ hξpos⟩) := by
                rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_coord_of_strictPositive
                  (d := d) q f hf_ord g hg_ord ξ hξpos]
          _ =
            OS.S (n + r)
              (Z (section43TimeImagAxisProductKernel ξ)) := by
                rw [hZ ξ hξ]
          _ =
            T (section43TimeImagAxisProductKernel ξ) := by
                rfl
    _ =
      T (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
        hflat.symm
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        rfl

/-- Scalar one-sided product selection from compact coordinate-shell pairings.

This is the finite-time source-current form of OS II V.1/V.2 `(5.2)`: if a
time-shell current has the honest coordinate-height Schwinger kernel on the
compact positive carrier used by the product source, and that kernel has the
compact product-source pairings of a target Schwinger vector, then the current
selects the same target scalar on the one-sided Laplace product tensor. -/
theorem schwinger_coordinateShiftShell_timeCLM_scalar_eq_of_compact_shell_pairings
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (q : Fin m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (K : Set (Fin m → ℝ))
    (hK_pos : K ⊆ section43TimeStrictPositiveRegion m)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (Rhs : (Fin m → Section43CompactPositiveTimeSource1D) →
      ZeroDiagonalSchwartz d (n + r))
    (hZ_kernel : ∀ (ξ : Fin m → ℝ) (hξK : ξ ∈ K),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) q f hf_ord g hg_ord ξ (hK_pos hξK)⟩)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ K →
        (∫ ξ : Fin m → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ q) g))) *
            (section43TimeProductSource gs).f ξ) =
          OS.S (n + r) (Rhs gs)) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      tsupport ((section43TimeProductSource gs).f :
        (Fin m → ℝ) → ℂ) ⊆ K →
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
        OS.S (n + r) (Rhs gs) := by
  intro gs hgsK
  have hshell_to_current :
      (∫ ξ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q) g))) *
          (section43TimeProductSource gs).f ξ) =
        OS.S (n + r)
          (Z (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
    exact
      schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
        (d := d) OS q f hf_ord g hg_ord Z gs
        (fun ξ hξ => hZ_kernel ξ (hgsK hξ))
  exact hshell_to_current.symm.trans (hpair gs hgsK)

/-- Product-source delta recovery for coordinate-height Schwinger shells.

This is the axis-pair analogue of the total-time real-edge delta step: the
selected shell depends on one finite-time coordinate `ξ q`, not on the total
sum of all finite-time coordinates. -/
theorem schwinger_coordinateShiftShell_eq_of_productSource_pairings
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (q₁ q₂ : Fin m)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁))) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂))) *
              (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₁) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₂) g₂))) := by
  let K₁ : (Fin m → ℝ) → ℂ := fun ξ =>
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
      (f₁.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁)))
  let K₂ : (Fin m → ℝ) → ℂ := fun ξ =>
    OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
      (f₂.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂)))
  have hK₁_cont_t :
      ContinuousOn
        (fun t : ℝ =>
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₁))))
        (Set.Ioi 0) := by
    exact
      continuousOn_os_pairing_term_timeShift_of_isCompactSupport
        (d := d) OS f₁ g₁ hf₁_ord hg₁_ord hg₁_compact
  have hK₂_cont_t :
      ContinuousOn
        (fun t : ℝ =>
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₂))))
        (Set.Ioi 0) := by
    exact
      continuousOn_os_pairing_term_timeShift_of_isCompactSupport
        (d := d) OS f₂ g₂ hf₂_ord hg₂_ord hg₂_compact
  have hK₁_cont : ContinuousAt K₁ x0 := by
    have ht :
        ContinuousAt
          (fun t : ℝ =>
            OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
              (f₁.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g₁))))
          (x0 q₁) :=
      hK₁_cont_t.continuousAt (isOpen_Ioi.mem_nhds (hx0 q₁))
    simpa [K₁, Function.comp_def] using
      ContinuousAt.comp (x := x0) (f := fun ξ : Fin m → ℝ => ξ q₁)
        (g := fun t : ℝ =>
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₁))))
        ht (continuous_apply q₁).continuousAt
  have hK₂_cont : ContinuousAt K₂ x0 := by
    have ht :
        ContinuousAt
          (fun t : ℝ =>
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g₂))))
          (x0 q₂) :=
      hK₂_cont_t.continuousAt (isOpen_Ioi.mem_nhds (hx0 q₂))
    simpa [K₂, Function.comp_def] using
      ContinuousAt.comp (x := x0) (f := fun ξ : Fin m → ℝ => ξ q₂)
        (g := fun t : ℝ =>
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₂))))
        ht (continuous_apply q₂).continuousAt
  have hK₁_contOn :
      ContinuousOn K₁ {ξ : Fin m → ℝ | ∀ i : Fin m, 0 < ξ i} := by
    exact hK₁_cont_t.comp
      (continuous_apply q₁).continuousOn
      (by intro ξ hξ; exact hξ q₁)
  have hK₂_contOn :
      ContinuousOn K₂ {ξ : Fin m → ℝ | ∀ i : Fin m, 0 < ξ i} := by
    exact hK₂_cont_t.comp
      (continuous_apply q₂).continuousOn
      (by intro ξ hξ; exact hξ q₂)
  change K₁ x0 = K₂ x0
  exact
    eq_of_positiveOrthant_productSource_pairings_eq
      K₁ K₂ x0 hx0 hK₁_cont hK₂_cont hK₁_contOn hK₂_contOn
      (by intro gs; exact hpair gs)

/-- Coordinate-height pointwise equality from concrete Schwinger time-CLMs.

This is the source-current consumer for the axis-pair chart: once the two
time-shell CLMs have honest coordinate-height kernels on the strict positive
orthant, equality of their one-sided Laplace product values recovers the
pointwise shifted Schwinger equality. -/
theorem schwinger_coordinateShiftShell_eq_of_timeCLM_honest_kernel_eq
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (q₁ q₂ : Fin m)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) q₁ f₁ hf₁_ord g₁ hg₁_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
            (d := d) q₂ f₂ hf₂_ord g₂ hg₂_ord ξ hξ⟩)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S (n₁ + r₁) (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S (n₂ + r₂) (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₁) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₂) g₂))) := by
  refine
    schwinger_coordinateShiftShell_eq_of_productSource_pairings
      (d := d) OS q₁ q₂
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact x0 hx0 ?_
  intro gs
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁))) *
        (section43TimeProductSource gs).f ξ)
        =
      OS.S (n₁ + r₁)
        (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        exact
          schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS q₁ f₁ hf₁_ord g₁ hg₁_ord Z₁ gs
            (fun ξ hξ =>
              hZ₁ ξ ((section43TimeProductSource gs).positive hξ))
    _ =
      OS.S (n₂ + r₂)
        (Z₂ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :=
        hprod gs
    _ =
      (∫ ξ : Fin m → ℝ,
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂))) *
          (section43TimeProductSource gs).f ξ) := by
        exact
          (schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS q₂ f₂ hf₂_ord g₂ hg₂_ord Z₂ gs
            (fun ξ hξ =>
              hZ₂ ξ ((section43TimeProductSource gs).positive hξ))).symm

/-- Local product-source delta recovery for coordinate-height Schwinger shells.

The axis-pair source-current comparison is naturally local in a time-shell
window.  Equality of compact positive product-source pairings for sources
supported in a neighborhood of the target still recovers the pointwise
coordinate-height Schwinger value. -/
theorem schwinger_coordinateShiftShell_eq_of_local_productSource_pairings
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (q₁ q₂ : Fin m)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (U : Set (Fin m → ℝ)) (hU_nhds : U ∈ 𝓝 x0)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ U →
        (∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁))) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂))) *
              (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₁) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₂) g₂))) := by
  let K₁ : (Fin m → ℝ) → ℂ := fun ξ =>
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
      (f₁.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁)))
  let K₂ : (Fin m → ℝ) → ℂ := fun ξ =>
    OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
      (f₂.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂)))
  have hK₁_cont_t :
      ContinuousOn
        (fun t : ℝ =>
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₁))))
        (Set.Ioi 0) :=
    continuousOn_os_pairing_term_timeShift_of_isCompactSupport
      (d := d) OS f₁ g₁ hf₁_ord hg₁_ord hg₁_compact
  have hK₂_cont_t :
      ContinuousOn
        (fun t : ℝ =>
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₂))))
        (Set.Ioi 0) :=
    continuousOn_os_pairing_term_timeShift_of_isCompactSupport
      (d := d) OS f₂ g₂ hf₂_ord hg₂_ord hg₂_compact
  have hK₁_cont : ContinuousAt K₁ x0 := by
    have ht :
        ContinuousAt
          (fun t : ℝ =>
            OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
              (f₁.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g₁))))
          (x0 q₁) :=
      hK₁_cont_t.continuousAt (isOpen_Ioi.mem_nhds (hx0 q₁))
    simpa [K₁, Function.comp_def] using
      ContinuousAt.comp (x := x0) (f := fun ξ : Fin m → ℝ => ξ q₁)
        (g := fun t : ℝ =>
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₁))))
        ht (continuous_apply q₁).continuousAt
  have hK₂_cont : ContinuousAt K₂ x0 := by
    have ht :
        ContinuousAt
          (fun t : ℝ =>
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g₂))))
          (x0 q₂) :=
      hK₂_cont_t.continuousAt (isOpen_Ioi.mem_nhds (hx0 q₂))
    simpa [K₂, Function.comp_def] using
      ContinuousAt.comp (x := x0) (f := fun ξ : Fin m → ℝ => ξ q₂)
        (g := fun t : ℝ =>
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g₂))))
        ht (continuous_apply q₂).continuousAt
  have hK₁_contOn :
      ContinuousOn K₁ {ξ : Fin m → ℝ | ∀ i : Fin m, 0 < ξ i} := by
    exact hK₁_cont_t.comp
      (continuous_apply q₁).continuousOn
      (by intro ξ hξ; exact hξ q₁)
  have hK₂_contOn :
      ContinuousOn K₂ {ξ : Fin m → ℝ | ∀ i : Fin m, 0 < ξ i} := by
    exact hK₂_cont_t.comp
      (continuous_apply q₂).continuousOn
      (by intro ξ hξ; exact hξ q₂)
  change K₁ x0 = K₂ x0
  exact
    eq_of_local_positiveOrthant_productSource_pairings_eq
      K₁ K₂ x0 hx0 U hU_nhds hK₁_cont hK₂_cont
      hK₁_contOn hK₂_contOn
      (by intro gs hgsU; exact hpair gs hgsU)

/-- Local coordinate-height pointwise equality from concrete time CLMs.

This is the local-window version of
`schwinger_coordinateShiftShell_eq_of_timeCLM_honest_kernel_eq`: the honest
kernel identities and product-tensor equality are required only on product
sources supported in the target neighborhood. -/
theorem schwinger_coordinateShiftShell_eq_of_local_timeCLM_honest_kernel_eq
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (q₁ q₂ : Fin m)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (U : Set (Fin m → ℝ)) (hU_nhds : U ∈ 𝓝 x0)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ξ ∈ U →
      ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
        Z₁ (section43TimeImagAxisProductKernel ξ) =
          ⟨f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) q₁ f₁ hf₁_ord g₁ hg₁_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ξ ∈ U →
      ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
        Z₂ (section43TimeImagAxisProductKernel ξ) =
          ⟨f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_strictPositive
              (d := d) q₂ f₂ hf₂_ord g₂ hg₂_ord ξ hξ⟩)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ U →
        OS.S (n₁ + r₁) (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S (n₂ + r₂) (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₁) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (x0 q₂) g₂))) := by
  refine
    schwinger_coordinateShiftShell_eq_of_local_productSource_pairings
      (d := d) OS q₁ q₂
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact x0 hx0 U hU_nhds ?_
  intro gs hgsU
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ q₁) g₁))) *
        (section43TimeProductSource gs).f ξ)
        =
      OS.S (n₁ + r₁)
        (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        exact
          schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS q₁ f₁ hf₁_ord g₁ hg₁_ord Z₁ gs
            (fun ξ hξ =>
              hZ₁ ξ (hgsU hξ) ((section43TimeProductSource gs).positive hξ))
    _ =
      OS.S (n₂ + r₂)
        (Z₂ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :=
        hprod gs hgsU
    _ =
      (∫ ξ : Fin m → ℝ,
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ q₂) g₂))) *
          (section43TimeProductSource gs).f ξ) := by
        exact
          (schwinger_coordinateShiftShell_productSource_integral_eq_timeCLM_on_tsupport
            (d := d) OS q₂ f₂ hf₂_ord g₂ hg₂_ord Z₂ gs
            (fun ξ hξ =>
              hZ₂ ξ (hgsU hξ) ((section43TimeProductSource gs).positive hξ))).symm

end OSReconstruction
