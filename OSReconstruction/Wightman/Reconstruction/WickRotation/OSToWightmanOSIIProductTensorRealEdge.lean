import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDirectionalSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeScalarProbe

/-!
# OS II Product-Tensor Real-Edge Delta Bridge

This file instantiates the positive-orthant delta-smearing bridge for the
common OS-II total positive-time real-edge scalar candidates.  The remaining
input is the genuine OS pairing identity against compact positive-orthant
tests.
-/

noncomputable section

open Complex Topology MeasureTheory Filter
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- If two scalar kernels agree on the topological support of a test function,
then their pairings against that test agree. -/
theorem integral_mul_eq_of_eqOn_tsupport
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [MeasureSpace E]
    (A B : E → ℂ) (h : E → ℂ)
    (hEq : ∀ x ∈ tsupport h, A x = B x) :
    (∫ x, A x * h x) = ∫ x, B x * h x := by
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ tsupport h
  · rw [hEq x hx]
  · have hzero : h x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hzero]

/-- Integrated compact-test version of the OS-II real-edge split identity.
The conditional branch is harmless because the test has support in the
nonnegative orthant. -/
theorem integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_nonneg
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (q : Fin m)
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (hh_nonneg : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 ≤ τ p}) :
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ G q :
              BorchersSequence d))
      else 0) * h τ) =
      ∫ τ : Fin m → ℝ,
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (G : BorchersSequence d)) * h τ := by
  refine
    integral_mul_eq_of_eqOn_tsupport
      (fun τ : Fin m → ℝ =>
        if hτ : ∀ p : Fin m, 0 ≤ τ p then
          OSInnerProduct d OS.S
            (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
            (timeShiftBorchers (d := d) (τ q)
              (osiiRightSplitPositiveBranch (d := d) τ hτ G q :
                BorchersSequence d))
        else 0)
      (fun τ : Fin m → ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (G : BorchersSequence d)))
      (h : (Fin m → ℝ) → ℂ) ?_
  intro τ hτsupp
  have hτ : ∀ p : Fin m, 0 ≤ τ p := hh_nonneg hτsupp
  have hsum :
      osiiLeftTimeSum τ q + (τ q + osiiRightTimeSum τ q) =
        ∑ p : Fin m, τ p := by
    have hsplit := osii_left_add_self_add_right_eq_sum τ q
    linarith
  simp only [hτ]
  simpa [hsum] using
    osii_real_edge_positiveBranch_agrees_combined_of_nonneg
      (d := d) OS F G τ hτ q (τ q) (hτ q)

/-- Positive-orthant specialization of the integrated split identity. -/
theorem integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (q : Fin m)
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (hh_pos : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p}) :
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ G q :
              BorchersSequence d))
      else 0) * h τ) =
      ∫ τ : Fin m → ℝ,
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (G : BorchersSequence d)) * h τ := by
  exact
    integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_nonneg
      (d := d) OS F G q h
      (fun τ hτsupp p => le_of_lt ((hh_pos hτsupp) p))

/-- Compact positive-orthant pairings of two q-directional split branches
agree, since both are equal to the total positive-time edge pairing. -/
theorem integral_osii_real_edge_positiveBranch_pairings_agree_of_tsupport_positive
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ}
    (F G : PositiveTimeBorchersSequence d)
    (q q' : Fin m)
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (hh_pos : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p}) :
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ G q :
              BorchersSequence d))
      else 0) * h τ) =
      ∫ τ : Fin m → ℝ,
        (if hτ : ∀ p : Fin m, 0 ≤ τ p then
          OSInnerProduct d OS.S
            (osiiLeftSplitPositiveBranch (d := d) τ hτ F q' : BorchersSequence d)
            (timeShiftBorchers (d := d) (τ q')
              (osiiRightSplitPositiveBranch (d := d) τ hτ G q' :
                BorchersSequence d))
        else 0) * h τ := by
  exact
    (integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
      (d := d) OS F G q h hh_pos).trans
      (integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
        (d := d) OS F G q' h hh_pos).symm

/-- Equality against all compact positive product sources recovers pointwise
equality on the finite positive orthant.  This is the product-source
replacement for the older "all compact positive tests" delta input. -/
theorem eq_of_positiveOrthant_productSource_pairings_eq
    {m : ℕ}
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_contOn : ContinuousOn F {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hG_contOn : ContinuousOn G {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          F ξ * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            G ξ * (section43TimeProductSource gs).f ξ) :
    F x0 = G x0 := by
  obtain ⟨gs, r, hnonneg, hreal, hint, hsupport, hr⟩ :=
    exists_section43TimeProductSource_shrinking_approx_identity m
  let φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ := fun n =>
    (section43TimeProductSource (gs n)).f
  refine
    eq_of_equal_positiveOrthant_translated_delta_smearings
      φ r F G x0 ?_ ?_ ?_ ?_ hr hF_cont hG_cont ?_ ?_ ?_
  · intro n x
    exact hnonneg n x
  · intro n x
    exact hreal n x
  · intro n
    exact hint n
  · intro n
    exact hsupport n
  · intro n
    exact
      integrable_positiveOrthant_schwartz_mul_continuousOn_shift
        (h := φ n) F x0 hx0
        (section43TimeProductSource (gs n)).compact
        (section43TimeProductSource (gs n)).positive
        hF_contOn
  · intro n
    exact
      integrable_positiveOrthant_schwartz_mul_continuousOn_shift
        (h := φ n) G x0 hx0
        (section43TimeProductSource (gs n)).compact
        (section43TimeProductSource (gs n)).positive
        hG_contOn
  · intro n
    let gsShift : Fin m → Section43CompactPositiveTimeSource1D := fun i =>
      section43CompactPositiveTimeSource1D_translateRight
        (gs n i) (x0 i) (le_of_lt (hx0 i))
    calc
      (∫ ξ : Fin m → ℝ,
        F ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ)
          =
        ∫ ξ : Fin m → ℝ,
          F ξ * (section43TimeProductSource gsShift).f ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [section43TimeProductSource_translateRight_apply
            (gs := gs n) (a := x0) (ha := fun i => le_of_lt (hx0 i))]
      _ =
        ∫ ξ : Fin m → ℝ,
          G ξ * (section43TimeProductSource gsShift).f ξ := hpair gsShift
      _ =
        ∫ ξ : Fin m → ℝ,
          G ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [section43TimeProductSource_translateRight_apply
            (gs := gs n) (a := x0) (ha := fun i => le_of_lt (hx0 i))]

/-- Section 4.3 product-source Fubini reassembly for the OS-II real-edge
pairing input.  Equality of the single compact product tensor under two scalar
probes, together with pointwise identification of their imaginary-axis product
kernel values, gives equality of all compact positive product-source pairings. -/
theorem section43_productSource_pairing_eq_of_productTensor_scalar_eq
    {m : ℕ}
    (T₁ T₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ,
      T₁ (section43TimeImagAxisProductKernel ξ) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ,
      T₂ (section43TimeImagAxisProductKernel ξ) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        T₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          T₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  intro gs
  have hleft :=
    section43TimeProductTensor_allSlots_flattened
      T₁ gs (fun _ : Fin m => 0)
  have hright :=
    section43TimeProductTensor_allSlots_flattened
      T₂ gs (fun _ : Fin m => 0)
  calc
    (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        T₁ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [hK₁ ξ]
    _ =
      T₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := hleft.symm
    _ =
      T₂ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := hprod gs
    _ =
      ∫ ξ : Fin m → ℝ,
        T₂ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := hright
    _ =
      ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [hK₂ ξ]

/-- Section 4.3 product-source Fubini reassembly when the imaginary-axis kernel
identifications are only known on the strict positive time orthant.  This is the
honest support-local form used by compact positive product sources. -/
theorem section43_productSource_pairing_eq_of_productTensor_scalar_eq_on_positive
    {m : ℕ}
    (T₁ T₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      T₁ (section43TimeImagAxisProductKernel ξ) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      T₂ (section43TimeImagAxisProductKernel ξ) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        T₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          T₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  intro gs
  have hleft :=
    section43TimeProductTensor_allSlots_flattened
      T₁ gs (fun _ : Fin m => 0)
  have hright :=
    section43TimeProductTensor_allSlots_flattened
      T₂ gs (fun _ : Fin m => 0)
  calc
    (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        T₁ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            K₁
            (fun ξ : Fin m → ℝ => T₁ (section43TimeImagAxisProductKernel ξ))
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            ?_
        intro ξ hξ
        exact (hK₁ ξ ((section43TimeProductSource gs).positive hξ)).symm
    _ =
      T₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := hleft.symm
    _ =
      T₂ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := hprod gs
    _ =
      ∫ ξ : Fin m → ℝ,
        T₂ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := hright
    _ =
      ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
        exact
          integral_mul_eq_of_eqOn_tsupport
            (fun ξ : Fin m → ℝ => T₂ (section43TimeImagAxisProductKernel ξ))
            K₂
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            (fun ξ hξ => hK₂ ξ ((section43TimeProductSource gs).positive hξ))

/-- Section 4.3 product-source Fubini reassembly with the scalar probes
constructed from multilinear time-factor data.  This removes the arbitrary
continuous-linear-map inputs from the OS-II product-source consumer: the only
remaining input is equality of the two multilinear Schwinger functionals on
the one-sided Laplace representatives. -/
theorem section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq
    {m : ℕ}
    (Phi₁ Phi₂ : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => SchwartzMap ℝ ℂ) ℂ)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ,
      Phi₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ,
      Phi₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        Phi₁
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) =
          Phi₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  obtain ⟨T₁, hT₁⟩ :=
    exists_section43TimeProductTensor_scalarProbe m Phi₁
  obtain ⟨T₂, hT₂⟩ :=
    exists_section43TimeProductTensor_scalarProbe m Phi₂
  refine
    section43_productSource_pairing_eq_of_productTensor_scalar_eq
      T₁ T₂ K₁ K₂ ?_ ?_ ?_
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using
      (hT₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i))).trans
        (hK₁ ξ)
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using
      (hT₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i))).trans
        (hK₂ ξ)
  · intro gs
    exact
      (hT₁
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))).trans
        ((hprod gs).trans
          (hT₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))).symm)

/-- Positive-support version of
`section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq`.  The
kernel identities are required only on the support of compact positive product
sources. -/
theorem section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq_on_positive
    {m : ℕ}
    (Phi₁ Phi₂ : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => SchwartzMap ℝ ℂ) ℂ)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      Phi₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      Phi₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        Phi₁
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) =
          Phi₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  obtain ⟨T₁, hT₁⟩ :=
    exists_section43TimeProductTensor_scalarProbe m Phi₁
  obtain ⟨T₂, hT₂⟩ :=
    exists_section43TimeProductTensor_scalarProbe m Phi₂
  refine
    section43_productSource_pairing_eq_of_productTensor_scalar_eq_on_positive
      T₁ T₂ K₁ K₂ ?_ ?_ ?_
  · intro ξ hξ
    simpa [section43TimeImagAxisProductKernel] using
      (hT₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i))).trans
        (hK₁ ξ hξ)
  · intro ξ hξ
    simpa [section43TimeImagAxisProductKernel] using
      (hT₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i))).trans
        (hK₂ ξ hξ)
  · intro gs
    exact
      (hT₁
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))).trans
        ((hprod gs).trans
          (hT₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))).symm)

/-- Product-source version of the OS-II total positive-time real-edge delta
recovery.  This is the interface fed by Section 4.3 Fubini product sources. -/
theorem eq_osii_total_positive_time_real_edges_of_productSource_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F₁ G₁ F₂ G₂ : PositiveTimeBorchersSequence d)
    (hG₁_compact : ∀ n,
      HasCompactSupport (((G₁ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (hG₂_compact : ∀ n,
      HasCompactSupport (((G₂ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          OSInnerProduct d OS.S (F₁ : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, ξ p)
              (G₁ : BorchersSequence d)) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OSInnerProduct d OS.S (F₂ : BorchersSequence d)
              (timeShiftBorchers (d := d)
                (∑ p : Fin m, ξ p)
                (G₂ : BorchersSequence d)) *
              (section43TimeProductSource gs).f ξ) :
    OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₁ : BorchersSequence d)) =
      OSInnerProduct d OS.S (F₂ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₂ : BorchersSequence d)) := by
  let E₁ : (Fin m → ℝ) → ℂ := fun τ =>
    OSInnerProduct d OS.S (F₁ : BorchersSequence d)
      (timeShiftBorchers (d := d)
        (∑ p : Fin m, τ p)
        (G₁ : BorchersSequence d))
  let E₂ : (Fin m → ℝ) → ℂ := fun τ =>
    OSInnerProduct d OS.S (F₂ : BorchersSequence d)
      (timeShiftBorchers (d := d)
        (∑ p : Fin m, τ p)
        (G₂ : BorchersSequence d))
  change E₁ x0 = E₂ x0
  refine
    eq_of_positiveOrthant_productSource_pairings_eq E₁ E₂ x0 hx0
      ?_ ?_ ?_ ?_ ?_
  · exact continuousAt_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₁ G₁ hG₁_compact x0 hx0
  · exact continuousAt_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₂ G₂ hG₂_compact x0 hx0
  · exact continuousOn_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₁ G₁ hG₁_compact
  · exact continuousOn_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₂ G₂ hG₂_compact
  · intro gs
    exact hpair gs

/-- Delta-smearing instantiated for two OS-II common total real edges.  The only
remaining hypothesis is the compact positive-orthant test-pairing equality. -/
theorem eq_osii_total_positive_time_real_edges_of_positiveOrthant_distribution_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F₁ G₁ F₂ G₂ : PositiveTimeBorchersSequence d)
    (hG₁_compact : ∀ n,
      HasCompactSupport (((G₁ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (hG₂_compact : ∀ n,
      HasCompactSupport (((G₂ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        (∫ ξ : Fin m → ℝ,
          OSInnerProduct d OS.S (F₁ : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, ξ p)
              (G₁ : BorchersSequence d)) * h ξ) =
          ∫ ξ : Fin m → ℝ,
            OSInnerProduct d OS.S (F₂ : BorchersSequence d)
              (timeShiftBorchers (d := d)
                (∑ p : Fin m, ξ p)
                (G₂ : BorchersSequence d)) * h ξ) :
    OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₁ : BorchersSequence d)) =
      OSInnerProduct d OS.S (F₂ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₂ : BorchersSequence d)) := by
  let E₁ : (Fin m → ℝ) → ℂ := fun τ =>
    OSInnerProduct d OS.S (F₁ : BorchersSequence d)
      (timeShiftBorchers (d := d)
        (∑ p : Fin m, τ p)
        (G₁ : BorchersSequence d))
  let E₂ : (Fin m → ℝ) → ℂ := fun τ =>
    OSInnerProduct d OS.S (F₂ : BorchersSequence d)
      (timeShiftBorchers (d := d)
        (∑ p : Fin m, τ p)
        (G₂ : BorchersSequence d))
  change E₁ x0 = E₂ x0
  refine
    eq_of_positiveOrthant_distribution_eq E₁ E₂ x0 hx0
      ?_ ?_ ?_ ?_ ?_
  · exact continuousAt_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₁ G₁ hG₁_compact x0 hx0
  · exact continuousAt_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F₂ G₂ hG₂_compact x0 hx0
  · intro h hh_compact hh_pos
    exact
      integrable_positiveOrthant_schwartz_mul_continuousOn_shift
        h E₁ x0 hx0 hh_compact hh_pos
        (continuousOn_osii_total_positive_time_real_edge_positiveOrthant
          (d := d) OS lgc F₁ G₁ hG₁_compact)
  · intro h hh_compact hh_pos
    exact
      integrable_positiveOrthant_schwartz_mul_continuousOn_shift
        h E₂ x0 hx0 hh_compact hh_pos
        (continuousOn_osii_total_positive_time_real_edge_positiveOrthant
          (d := d) OS lgc F₂ G₂ hG₂_compact)
  · intro h hh_compact hh_pos
    exact hpair h hh_compact hh_pos

/-- If the compact positive-orthant distributional pairings of two
directional split branches agree, then the corresponding total real-edge
Schwinger scalars agree pointwise.  This is the interface that the remaining
product-tensor/Fubini calculation has to feed. -/
theorem eq_osii_total_positive_time_real_edges_of_positiveBranch_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F₁ G₁ F₂ G₂ : PositiveTimeBorchersSequence d)
    (hG₁_compact : ∀ n,
      HasCompactSupport (((G₁ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (hG₂_compact : ∀ n,
      HasCompactSupport (((G₂ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (q₁ q₂ : Fin m)
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        (∫ ξ : Fin m → ℝ,
          (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
            OSInnerProduct d OS.S
              (osiiLeftSplitPositiveBranch (d := d) ξ hξ F₁ q₁ :
                BorchersSequence d)
              (timeShiftBorchers (d := d) (ξ q₁)
                (osiiRightSplitPositiveBranch (d := d) ξ hξ G₁ q₁ :
                  BorchersSequence d))
          else 0) * h ξ) =
          ∫ ξ : Fin m → ℝ,
            (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
              OSInnerProduct d OS.S
                (osiiLeftSplitPositiveBranch (d := d) ξ hξ F₂ q₂ :
                  BorchersSequence d)
                (timeShiftBorchers (d := d) (ξ q₂)
                  (osiiRightSplitPositiveBranch (d := d) ξ hξ G₂ q₂ :
                    BorchersSequence d))
            else 0) * h ξ) :
    OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₁ : BorchersSequence d)) =
      OSInnerProduct d OS.S (F₂ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₂ : BorchersSequence d)) := by
  refine
    eq_osii_total_positive_time_real_edges_of_positiveOrthant_distribution_eq
      (d := d) OS lgc F₁ G₁ F₂ G₂ hG₁_compact hG₂_compact x0 hx0 ?_
  intro h hh_compact hh_pos
  calc
    (∫ ξ : Fin m → ℝ,
      OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, ξ p)
          (G₁ : BorchersSequence d)) * h ξ)
        =
      ∫ ξ : Fin m → ℝ,
        (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
          OSInnerProduct d OS.S
            (osiiLeftSplitPositiveBranch (d := d) ξ hξ F₁ q₁ :
              BorchersSequence d)
            (timeShiftBorchers (d := d) (ξ q₁)
              (osiiRightSplitPositiveBranch (d := d) ξ hξ G₁ q₁ :
                BorchersSequence d))
        else 0) * h ξ := by
          exact
            (integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
              (d := d) OS F₁ G₁ q₁ h hh_pos).symm
    _ =
      ∫ ξ : Fin m → ℝ,
        (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
          OSInnerProduct d OS.S
            (osiiLeftSplitPositiveBranch (d := d) ξ hξ F₂ q₂ :
              BorchersSequence d)
            (timeShiftBorchers (d := d) (ξ q₂)
              (osiiRightSplitPositiveBranch (d := d) ξ hξ G₂ q₂ :
                BorchersSequence d))
        else 0) * h ξ := hpair h hh_compact hh_pos
    _ =
      ∫ ξ : Fin m → ℝ,
        OSInnerProduct d OS.S (F₂ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, ξ p)
            (G₂ : BorchersSequence d)) * h ξ := by
          exact
            integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
              (d := d) OS F₂ G₂ q₂ h hh_pos

/-- Concentrated-product form of the total positive-time real edge. -/
theorem osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (τ : Fin m → ℝ) :
    OSInnerProduct d OS.S
        (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, τ p) g))) := by
  simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
    OSInnerProduct_single_right_timeShift
      (d := d) OS f g (∑ p : Fin m, τ p)

/-- Concentrated-product form of the common-time shifted total positive-time
real edge.  The common nonnegative Euclidean shift is absorbed into the left
Schwinger source, while the right source is shifted by the total
time-difference variable. -/
theorem osii_total_positive_time_real_edge_single_leftTimeShift_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (τ : Fin m → ℝ) :
    OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
          (PositiveTimeBorchersSequence.single n f hf_ord) : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, τ p) g))) := by
  have hleft_shift :
      ∀ s,
        (timeShiftBorchers (d := d) a (BorchersSequence.single n f)).funcs s =
          (BorchersSequence.single n
            (timeShiftSchwartzNPoint (d := d) a f)).funcs s := by
    intro s
    by_cases hs : s = n
    · subst hs
      simp [BorchersSequence.single]
    · simp [BorchersSequence.single, hs]
  have hcongr :
      OSInnerProduct d OS.S
          (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
          (timeShiftBorchers (d := d) (∑ p : Fin m, τ p)
            (BorchersSequence.single r g)) =
        OSInnerProduct d OS.S
          (BorchersSequence.single n (timeShiftSchwartzNPoint (d := d) a f))
          (timeShiftBorchers (d := d) (∑ p : Fin m, τ p)
            (BorchersSequence.single r g)) := by
    exact OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
      (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
      (BorchersSequence.single n (timeShiftSchwartzNPoint (d := d) a f))
      (timeShiftBorchers (d := d) (∑ p : Fin m, τ p)
        (BorchersSequence.single r g)) hleft_shift
  calc
    OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
          (PositiveTimeBorchersSequence.single n f hf_ord) : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) =
      OSInnerProduct d OS.S
        (timeShiftBorchers (d := d) a (BorchersSequence.single n f))
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (BorchersSequence.single r g)) := by
        rfl
    _ =
      OSInnerProduct d OS.S
        (BorchersSequence.single n (timeShiftSchwartzNPoint (d := d) a f))
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (BorchersSequence.single r g)) := hcongr
    _ =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, τ p) g))) := by
        exact OSInnerProduct_single_right_timeShift
          (d := d) OS (timeShiftSchwartzNPoint (d := d) a f) g
          (∑ p : Fin m, τ p)

/-- Product-source weighted form of the common-time shifted total real edge. -/
theorem integral_osii_total_positive_time_real_edge_single_leftTimeShift_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (h : SchwartzMap (Fin m → ℝ) ℂ) :
    (∫ τ : Fin m → ℝ,
      OSInnerProduct d OS.S
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
          (PositiveTimeBorchersSequence.single n f hf_ord) : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, τ p)
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) *
        h τ) =
      ∫ τ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, τ p) g))) *
          h τ := by
  refine integral_congr_ae ?_
  filter_upwards with τ
  rw [osii_total_positive_time_real_edge_single_leftTimeShift_eq_schwinger_timeShift
    (d := d) OS a ha f hf_ord g hg_ord τ]

/-- Positive-branch split integral with a common left time shift, rewritten as
the corresponding left-shifted Schwinger product-shell integral. -/
theorem integral_osii_real_edge_positiveBranch_single_leftTimeShift_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (q : Fin m)
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (hh_pos : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p}) :
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ
            (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
              (PositiveTimeBorchersSequence.single n f hf_ord)) q :
              BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ
              (PositiveTimeBorchersSequence.single r g hg_ord) q :
                BorchersSequence d))
      else 0) * h τ) =
      ∫ τ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, τ p) g))) * h τ := by
  calc
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ
            (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
              (PositiveTimeBorchersSequence.single n f hf_ord)) q :
              BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ
              (PositiveTimeBorchersSequence.single r g hg_ord) q :
                BorchersSequence d))
      else 0) * h τ)
        =
      ∫ τ : Fin m → ℝ,
        OSInnerProduct d OS.S
          (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
            (PositiveTimeBorchersSequence.single n f hf_ord) :
              BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (PositiveTimeBorchersSequence.single r g hg_ord :
              BorchersSequence d)) * h τ := by
        exact
          integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
            (d := d) OS
            (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
              (PositiveTimeBorchersSequence.single n f hf_ord))
            (PositiveTimeBorchersSequence.single r g hg_ord) q h hh_pos
    _ =
      ∫ τ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, τ p) g))) * h τ := by
        exact
          integral_osii_total_positive_time_real_edge_single_leftTimeShift_eq_schwinger_timeShift
            (d := d) OS a ha f hf_ord g hg_ord h

/-- Compact positive-orthant pairing of a q-directional split of concentrated
Borchers factors, rewritten as the corresponding Schwinger product-shell
integral.  The remaining E-to-R gap is to identify this integral with the
single compact product tensor by Fubini/continuity of `OS.S`. -/
theorem integral_osii_real_edge_positiveBranch_single_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    {m n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (q : Fin m)
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (hh_pos : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p}) :
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ
            (PositiveTimeBorchersSequence.single n f hf_ord) q :
              BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ
              (PositiveTimeBorchersSequence.single r g hg_ord) q :
                BorchersSequence d))
      else 0) * h τ) =
      ∫ τ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, τ p) g))) * h τ := by
  calc
    (∫ τ : Fin m → ℝ,
      (if hτ : ∀ p : Fin m, 0 ≤ τ p then
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ
            (PositiveTimeBorchersSequence.single n f hf_ord) q :
              BorchersSequence d)
          (timeShiftBorchers (d := d) (τ q)
            (osiiRightSplitPositiveBranch (d := d) τ hτ
              (PositiveTimeBorchersSequence.single r g hg_ord) q :
                BorchersSequence d))
      else 0) * h τ)
        =
      ∫ τ : Fin m → ℝ,
        OSInnerProduct d OS.S
          (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (PositiveTimeBorchersSequence.single r g hg_ord :
              BorchersSequence d)) * h τ := by
          exact
            integral_osii_real_edge_positiveBranch_agrees_total_of_tsupport_positive
              (d := d) OS
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) q h hh_pos
    _ =
      ∫ τ : Fin m → ℝ,
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, τ p) g))) * h τ := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          rw [osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
            (d := d) OS f hf_ord g hg_ord τ]

/-- Product-source shifted-shell pairing equality follows from the
corresponding equality of the positive-branch OS semigroup pairings.

This is the compact-source bridge from the OS-II directional semigroup side to
the Schwinger shifted-shell pairing side.  The remaining producer still has to
prove the positive-branch pairing equality; this theorem performs the
book-faithful rewrite of each branch through the total positive-time real edge. -/
theorem schwinger_shifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    {m n₁ r₁ n₂ r₂ : ℕ}
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (q₁ q₂ : Fin m)
    (hbranch :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
            OSInnerProduct d OS.S
              (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                (PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord) q₁ :
                  BorchersSequence d)
              (timeShiftBorchers (d := d) (ξ q₁)
                (osiiRightSplitPositiveBranch (d := d) ξ hξ
                  (PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord) q₁ :
                    BorchersSequence d))
          else 0) * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
              OSInnerProduct d OS.S
                (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                  (PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord) q₂ :
                    BorchersSequence d)
                (timeShiftBorchers (d := d) (ξ q₂)
                  (osiiRightSplitPositiveBranch (d := d) ξ hξ
                    (PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord) q₂ :
                      BorchersSequence d))
            else 0) * (section43TimeProductSource gs).f ξ) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ,
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))) *
          (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₂))) *
            (section43TimeProductSource gs).f ξ := by
  intro gs
  have h₁ :=
    integral_osii_real_edge_positiveBranch_single_eq_schwinger_timeShift
      (d := d) OS f₁ hf₁_ord g₁ hg₁_ord q₁
      (section43TimeProductSource gs).f
      (section43TimeProductSource gs).positive
  have h₂ :=
    integral_osii_real_edge_positiveBranch_single_eq_schwinger_timeShift
      (d := d) OS f₂ hf₂_ord g₂ hg₂_ord q₂
      (section43TimeProductSource gs).f
      (section43TimeProductSource gs).positive
  exact h₁.symm.trans ((hbranch gs).trans h₂)

/-- Product-source left-shifted shell pairing equality follows from equality
of the corresponding common-left-shift positive-branch OS semigroup pairings. -/
theorem schwinger_leftShifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    {m n₁ r₁ n₂ r₂ : ℕ}
    (a₁ : ℝ) (ha₁ : 0 ≤ a₁)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (a₂ : ℝ) (ha₂ : 0 ≤ a₂)
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (q₁ q₂ : Fin m)
    (hbranch :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
            OSInnerProduct d OS.S
              (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                (timeShiftNonnegPositiveTimeBorchers (d := d) a₁ ha₁
                  (PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord)) q₁ :
                  BorchersSequence d)
              (timeShiftBorchers (d := d) (ξ q₁)
                (osiiRightSplitPositiveBranch (d := d) ξ hξ
                  (PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord) q₁ :
                    BorchersSequence d))
          else 0) * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
              OSInnerProduct d OS.S
                (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                  (timeShiftNonnegPositiveTimeBorchers (d := d) a₂ ha₂
                    (PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord)) q₂ :
                    BorchersSequence d)
                (timeShiftBorchers (d := d) (ξ q₂)
                  (osiiRightSplitPositiveBranch (d := d) ξ hξ
                    (PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord) q₂ :
                      BorchersSequence d))
            else 0) * (section43TimeProductSource gs).f ξ) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ,
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a₁ f₁).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))) *
          (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            ((timeShiftSchwartzNPoint (d := d) a₂ f₂).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₂))) *
            (section43TimeProductSource gs).f ξ := by
  intro gs
  have h₁ :=
    integral_osii_real_edge_positiveBranch_single_leftTimeShift_eq_schwinger_timeShift
      (d := d) OS a₁ ha₁ f₁ hf₁_ord g₁ hg₁_ord q₁
      (section43TimeProductSource gs).f
      (section43TimeProductSource gs).positive
  have h₂ :=
    integral_osii_real_edge_positiveBranch_single_leftTimeShift_eq_schwinger_timeShift
      (d := d) OS a₂ ha₂ f₂ hf₂_ord g₂ hg₂_ord q₂
      (section43TimeProductSource gs).f
      (section43TimeProductSource gs).positive
  exact h₁.symm.trans ((hbranch gs).trans h₂)

/-- Product-source version of the concentrated Schwinger shifted-shell
positive-orthant recovery. -/
theorem eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₁))) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d)
                  (∑ p : Fin m, ξ p) g₂))) *
              (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  let F₁ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord
  let G₁ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord
  let F₂ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord
  let G₂ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord
  have hG₁_compact :
      ∀ s,
        HasCompactSupport ((((G₁ : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r₁
    · subst hs
      simpa [G₁, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg₁_compact
    · have hzero :
        (((G₁ : BorchersSequence d).funcs s : SchwartzNPoint d s) :
          NPointDomain d s → ℂ) = 0 := by
          simp [G₁, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  have hG₂_compact :
      ∀ s,
        HasCompactSupport ((((G₂ : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r₂
    · subst hs
      simpa [G₂, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg₂_compact
    · have hzero :
        (((G₂ : BorchersSequence d).funcs s : SchwartzNPoint d s) :
          NPointDomain d s → ℂ) = 0 := by
          simp [G₂, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  have htotal :
      OSInnerProduct d OS.S (F₁ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, x0 p)
            (G₁ : BorchersSequence d)) =
        OSInnerProduct d OS.S (F₂ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, x0 p)
            (G₂ : BorchersSequence d)) := by
    refine
      eq_osii_total_positive_time_real_edges_of_productSource_pairings_eq
        (d := d) OS lgc F₁ G₁ F₂ G₂ hG₁_compact hG₂_compact x0 hx0 ?_
    intro gs
    calc
      (∫ ξ : Fin m → ℝ,
        OSInnerProduct d OS.S (F₁ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, ξ p)
            (G₁ : BorchersSequence d)) *
          (section43TimeProductSource gs).f ξ)
          =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₁))) *
            (section43TimeProductSource gs).f ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            rw [osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₁ hf₁_ord g₁ hg₁_ord ξ]
      _ =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₂))) *
            (section43TimeProductSource gs).f ξ := hpair gs
      _ =
        ∫ ξ : Fin m → ℝ,
          OSInnerProduct d OS.S (F₂ : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, ξ p)
              (G₂ : BorchersSequence d)) *
            (section43TimeProductSource gs).f ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            rw [osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₂ hf₂_ord g₂ hg₂_ord ξ]
  calc
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁)))
        =
      OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₁ : BorchersSequence d)) := by
          exact
            (osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₁ hf₁_ord g₁ hg₁_ord x0).symm
    _ =
      OSInnerProduct d OS.S (F₂ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₂ : BorchersSequence d)) := htotal
    _ =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
          exact
            osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₂ hf₂_ord g₂ hg₂_ord x0

/-- Concentrated shifted-shell equality from the Section 4.3 compact
product-source Fubini identity.  The remaining OS-specific producer is now
localized to constructing the two scalar probes, identifying their
imaginary-axis product-kernel values with the shifted Schwinger shells, and
proving equality on the single tensor of one-sided Laplace representatives. -/
theorem eq_schwinger_timeShift_single_of_section43_productTensor_scalar_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
    (T₁ T₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ,
      T₁ (section43TimeImagAxisProductKernel ξ) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ,
      T₂ (section43TimeImagAxisProductKernel ξ) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        T₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          T₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 ?_
  exact
    section43_productSource_pairing_eq_of_productTensor_scalar_eq
      T₁ T₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      hK₁ hK₂ hprod

/-- Concentrated shifted-shell equality from multilinear time-factor data.
The scalar probes on finite-time Schwartz space are constructed by the
Section 4.3 nuclear-extension step, so the OS-specific producer only has to
identify imaginary-axis kernel values and prove equality on one-sided
Laplace representatives. -/
theorem eq_schwinger_timeShift_single_of_timeProductTensor_multilinear_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
    (Phi₁ Phi₂ : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => SchwartzMap ℝ ℂ) ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ,
      Phi₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ,
      Phi₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        Phi₁
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) =
          Phi₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 ?_
  exact
    section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq
      Phi₁ Phi₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      hK₁ hK₂ hprod

/-- Concentrated shifted-shell equality from scalar product-tensor probes when
the imaginary-axis kernel identifications are only known on the strict
positive orthant. -/
theorem eq_schwinger_timeShift_single_of_section43_productTensor_scalar_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
    (T₁ T₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      T₁ (section43TimeImagAxisProductKernel ξ) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      T₂ (section43TimeImagAxisProductKernel ξ) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        T₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          T₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 ?_
  exact
    section43_productSource_pairing_eq_of_productTensor_scalar_eq_on_positive
      T₁ T₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      hK₁ hK₂ hprod

/-- Concentrated shifted-shell equality from multilinear time-factor probes
whose imaginary-axis kernel identifications are localized to the strict
positive orthant. -/
theorem eq_schwinger_timeShift_single_of_timeProductTensor_multilinear_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
    (Phi₁ Phi₂ : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => SchwartzMap ℝ ℂ) ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      Phi₁ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      Phi₂ (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        Phi₁
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) =
          Phi₂
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 ?_
  exact
    section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq_on_positive
      Phi₁ Phi₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      hK₁ hK₂ hprod

/-- Positive-orthant delta recovery after rewriting concentrated OS real edges
as Schwinger shifted product shells.  The remaining input is the genuine
compact-test Schwinger/Fubini identity for the two product-shell families. -/
theorem eq_schwinger_timeShift_single_of_positiveOrthant_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
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
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        (∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₁))) * h ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d)
                  (∑ p : Fin m, ξ p) g₂))) * h ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  let F₁ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord
  let G₁ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord
  let F₂ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord
  let G₂ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord
  have hG₁_compact :
      ∀ s,
        HasCompactSupport ((((G₁ : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r₁
    · subst hs
      simpa [G₁, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg₁_compact
    · have hzero :
        (((G₁ : BorchersSequence d).funcs s : SchwartzNPoint d s) :
          NPointDomain d s → ℂ) = 0 := by
          simp [G₁, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  have hG₂_compact :
      ∀ s,
        HasCompactSupport ((((G₂ : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r₂
    · subst hs
      simpa [G₂, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg₂_compact
    · have hzero :
        (((G₂ : BorchersSequence d).funcs s : SchwartzNPoint d s) :
          NPointDomain d s → ℂ) = 0 := by
          simp [G₂, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  have htotal :
      OSInnerProduct d OS.S (F₁ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, x0 p)
            (G₁ : BorchersSequence d)) =
        OSInnerProduct d OS.S (F₂ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, x0 p)
            (G₂ : BorchersSequence d)) := by
    refine
      eq_osii_total_positive_time_real_edges_of_positiveOrthant_distribution_eq
        (d := d) OS lgc F₁ G₁ F₂ G₂ hG₁_compact hG₂_compact x0 hx0 ?_
    intro h hh_compact hh_pos
    calc
      (∫ ξ : Fin m → ℝ,
        OSInnerProduct d OS.S (F₁ : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, ξ p)
            (G₁ : BorchersSequence d)) * h ξ)
          =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₁))) * h ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            rw [osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₁ hf₁_ord g₁ hg₁_ord ξ]
      _ =
        ∫ ξ : Fin m → ℝ,
          OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
            (f₂.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₂))) * h ξ :=
            hpair h hh_compact hh_pos
      _ =
        ∫ ξ : Fin m → ℝ,
          OSInnerProduct d OS.S (F₂ : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, ξ p)
              (G₂ : BorchersSequence d)) * h ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            rw [osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₂ hf₂_ord g₂ hg₂_ord ξ]
  calc
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁)))
        =
      OSInnerProduct d OS.S (F₁ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₁ : BorchersSequence d)) := by
          exact
            (osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₁ hf₁_ord g₁ hg₁_ord x0).symm
    _ =
      OSInnerProduct d OS.S (F₂ : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, x0 p)
          (G₂ : BorchersSequence d)) := htotal
    _ =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
          exact
            osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
              (d := d) OS f₂ hf₂_ord g₂ hg₂_ord x0

end OSReconstruction
