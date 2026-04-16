import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- Continuous-linear time projection used by the derivative formula for the
Section 4.3 Fourier-Laplace integral. -/
noncomputable def section43QTimeCLM (d n : ℕ) [NeZero d] :
    NPointDomain d n →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d))).comp
    (nPointTimeSpatialCLE (d := d) n).toContinuousLinearMap

@[simp] theorem section43QTimeCLM_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) :
    section43QTimeCLM d n q = section43QTime (d := d) (n := n) q := by
  rfl

/-- Continuous-linear spatial projection used by the derivative formula for the
Section 4.3 Fourier-Laplace integral. -/
noncomputable def section43QSpatialCLM (d n : ℕ) [NeZero d] :
    NPointDomain d n →L[ℝ] EuclideanSpace ℝ (Fin n × Fin d) :=
  (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d))).comp
    (nPointTimeSpatialCLE (d := d) n).toContinuousLinearMap

@[simp] theorem section43QSpatialCLM_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) :
    section43QSpatialCLM d n q = section43QSpatial (d := d) (n := n) q := by
  rfl

/-- Continuous-linear argument of the Laplace exponential in the Section 4.3
Fourier-Laplace integrand, with the time variable `τ` fixed. -/
noncomputable def section43FourierLaplace_expArgCLM
    (d n : ℕ) [NeZero d] (τ : Fin n → ℝ) :
    NPointDomain d n →L[ℝ] ℂ :=
  ∑ k : Fin n,
    (((ContinuousLinearMap.proj
        (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n)).smulRight
        (-(τ k : ℂ)))

@[simp] theorem section43FourierLaplace_expArgCLM_apply
    (d n : ℕ) [NeZero d] (τ : Fin n → ℝ) (q : NPointDomain d n) :
    section43FourierLaplace_expArgCLM d n τ q =
      -(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) := by
  simp [section43FourierLaplace_expArgCLM, mul_comm]

/-- CLM-valued first derivative candidate for the Section 4.3 Fourier-Laplace
time integrand.  Applied to a direction `m`, it is the derivative of the
Laplace exponential in the time variables plus the spatial derivative of the
partial spatial Fourier transform. -/
noncomputable def section43FourierLaplace_timeIntegrandFDerivCLM
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (τ : Fin n → ℝ) :
    NPointDomain d n →L[ℝ] ℂ :=
  let E : ℂ :=
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let P : ℂ :=
    partialFourierSpatial_fun (d := d) (n := n) F
      (τ, section43QSpatial (d := d) (n := n) q)
  (∑ k : Fin n,
    (((ContinuousLinearMap.proj
        (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n)).smulRight
        (-(τ k : ℂ) * E * P))) +
  E •
    ((fderiv ℝ
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
      (section43QSpatial (d := d) (n := n) q)).comp
        (section43QSpatialCLM d n))

@[simp] theorem section43FourierLaplace_timeIntegrandFDerivCLM_apply
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q m : NPointDomain d n)
    (τ : Fin n → ℝ) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
      let E : ℂ :=
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
      let P : ℂ :=
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q)
      (∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * E * P)) +
      E •
        (fderiv ℝ
          (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
            partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
          (section43QSpatial (d := d) (n := n) q))
          (section43QSpatial (d := d) (n := n) m) := by
  simp [section43FourierLaplace_timeIntegrandFDerivCLM]

set_option backward.isDefEq.respectTransparency false in
/-- First derivative candidate for the Section 4.3 Fourier-Laplace integral,
as the Bochner integral of the CLM-valued pointwise derivative. -/
noncomputable def section43FourierLaplaceIntegral_fderivCandidate
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (q : NPointDomain d n) :
    NPointDomain d n →L[ℝ] ℂ :=
  ∫ τ : Fin n → ℝ,
    section43FourierLaplace_timeIntegrandFDerivCLM d n
      (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ

/-- Pointwise first derivative of the Section 4.3 Fourier-Laplace time
integrand.  This is the product rule for the Laplace exponential and the
spatial partial Fourier transform, expressed in the explicit CLM form that will
later be integrated in `τ`. -/
theorem hasFDerivAt_section43FourierLaplace_timeIntegrand
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (τ : Fin n → ℝ) :
    HasFDerivAt
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q' k : ℂ))) *
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q'))
      (section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ)
      q := by
  let L : NPointDomain d n →L[ℝ] ℂ :=
    section43FourierLaplace_expArgCLM d n τ
  have hL_apply : ∀ q' : NPointDomain d n,
      L q' =
        -(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q' k : ℂ)) := by
    intro q'
    simp [L]
  have hE : HasFDerivAt
      (fun q' : NPointDomain d n => Complex.exp (L q'))
      (Complex.exp (L q) • L) q := by
    exact L.hasFDerivAt.cexp
  have hP0 : HasFDerivAt
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
      (fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q))
      (section43QSpatial (d := d) (n := n) q) := by
    exact (differentiableAt_partialFourierSpatial_fun_spatial
      (d := d) (n := n) F τ
      (section43QSpatial (d := d) (n := n) q)).hasFDerivAt
  have hP : HasFDerivAt
      (fun q' : NPointDomain d n =>
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q'))
      ((fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q)).comp
          (section43QSpatialCLM d n)) q := by
    simpa using hP0.comp q (section43QSpatialCLM d n).hasFDerivAt
  have hprod := hE.mul hP
  convert hprod using 1
  · ext q'
    simp [hL_apply]
  · ext m
    simp [section43FourierLaplace_timeIntegrandFDerivCLM, L,
      section43FourierLaplace_expArgCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      mul_assoc, mul_left_comm, mul_comm, add_comm]
    ring_nf
    rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    ring_nf

private theorem exists_pos_le_on_compact_of_forall_pos
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {g : E → ℝ} (hg : Continuous g)
    (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ g x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hx₀_min⟩ := hK.exists_isMinOn hne hg.continuousOn
    have hx₀_pos : 0 < g x₀ := hpos x₀ hx₀
    refine ⟨g x₀ / 2, by linarith, ?_⟩
    intro x hx
    have hle : g x₀ ≤ g x := isMinOn_iff.mp hx₀_min x hx
    linarith
  · refine ⟨1, by positivity, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

/-- Compact support inside the OS ordered positive-time region is uniformly
separated from every time-wall and every ordered-pair collision wall. -/
theorem exists_orderedPositiveTimeRegion_margin_of_compact_tsupport_subset
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ δ > 0,
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)} := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hf_compact
  let I : Type := ULift Unit ⊕ (Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2})
  have hI_nonempty : (Finset.univ : Finset I).Nonempty := by
    exact ⟨Sum.inl (ULift.up ()), Finset.mem_univ _⟩
  let lowerFun : I → (NPointDomain d n → ℝ) := fun a =>
    match a with
    | Sum.inl _ => fun _ => 1
    | Sum.inr (Sum.inl i) => fun x => x i 0
    | Sum.inr (Sum.inr p) => fun x => x p.1.2 0 - x p.1.1 0
  have hbounds : ∀ a : I, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ lowerFun a x := by
    intro a
    cases a with
    | inl _ =>
        refine ⟨1, by positivity, ?_⟩
        intro x hx
        simp [lowerFun]
    | inr b =>
        cases b with
        | inl i =>
            refine exists_pos_le_on_compact_of_forall_pos hK_compact ?_ ?_
            · exact (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply i)
            · intro x hx
              exact (hf_ord hx i).1
        | inr p =>
            refine exists_pos_le_on_compact_of_forall_pos hK_compact ?_ ?_
            · exact (((continuous_apply (0 : Fin (d + 1))).comp
                (continuous_apply p.1.2)).sub
                ((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply p.1.1)))
            · intro x hx
              exact sub_pos.mpr ((hf_ord hx p.1.1).2 p.1.2 p.2)
  let ε : I → ℝ := fun a => Classical.choose (hbounds a)
  have hε_pos : ∀ a : I, 0 < ε a := fun a => (Classical.choose_spec (hbounds a)).1
  have hε_le : ∀ a : I, ∀ x ∈ K, ε a ≤ lowerFun a x :=
    fun a => (Classical.choose_spec (hbounds a)).2
  let δ : ℝ := (Finset.univ : Finset I).inf' hI_nonempty ε
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact (Finset.lt_inf'_iff hI_nonempty).2 (fun a _ha => hε_pos a)
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx
  constructor
  · intro i
    have hδ_le_ε : δ ≤ ε (Sum.inr (Sum.inl i) : I) := by
      dsimp [δ]
      exact Finset.inf'_le (s := (Finset.univ : Finset I)) (f := ε)
        (b := (Sum.inr (Sum.inl i) : I)) (Finset.mem_univ _)
    have hε_le_x : ε (Sum.inr (Sum.inl i) : I) ≤ x i 0 := by
      simpa [lowerFun] using hε_le (Sum.inr (Sum.inl i) : I) x hx
    exact le_trans hδ_le_ε hε_le_x
  · intro i j hij
    let a : I := Sum.inr (Sum.inr ⟨(i, j), hij⟩)
    have hδ_le_ε : δ ≤ ε a := by
      dsimp [δ]
      exact Finset.inf'_le (s := (Finset.univ : Finset I)) (f := ε)
        (b := a) (Finset.mem_univ _)
    have hε_le_x : ε a ≤ x j 0 - x i 0 := by
      simpa [a, lowerFun] using hε_le a x hx
    exact le_trans hδ_le_ε hε_le_x

/-- The ordered-region margin becomes a coordinatewise positive margin after
the OS-I difference-coordinate pullback. -/
theorem tsupport_section43DiffPullback_subset_margin_positiveOrthant
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    tsupport
      (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆
        {ξ | ∀ k : Fin n, δ ≤ ξ k 0} := by
  intro ξ hξ k
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm ξ
  have hpre : y ∈ tsupport (f : NPointDomain d n → ℂ) := by
    exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
      (section43DiffCoordRealCLE d n).symm.continuous hξ
  have hy := hδ_supp hpre
  have hcoord :
      ξ k 0 =
        (if hk : k.val = 0 then y k 0 else y k 0 - y ⟨k.val - 1, by omega⟩ 0) := by
    have happly :=
      congr_fun (congr_fun ((section43DiffCoordRealCLE d n).apply_symm_apply ξ) k) 0
    rw [section43DiffCoordRealCLE_apply] at happly
    exact happly.symm
  rw [hcoord]
  by_cases hk : k.val = 0
  · simp [hk, hy.1 k]
  · simp [hk]
    have hprev_lt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
      exact Fin.mk_lt_mk.mpr (by omega)
    exact hy.2 ⟨k.val - 1, by omega⟩ k hprev_lt

/-- Spatial Fourier transform does not enlarge the time support: with a strict
ordered-support margin, every time slice below that margin vanishes. -/
theorem partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hτ : ∃ i : Fin n, τ i < δ) :
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) (τ, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards with η
  rcases hτ with ⟨i, hi⟩
  let x : NPointDomain d n := (nPointTimeSpatialCLE (d := d) n).symm (τ, η)
  have hx_not_tsupport :
      x ∉ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro hx
    have hx_margin :=
      tsupport_section43DiffPullback_subset_margin_positiveOrthant
        d n f hf_ord hδ_supp hx i
    have hτ_le : δ ≤ τ i := by
      simpa [x, nPointTimeSpatialCLE] using hx_margin
    exact not_le_of_gt hi hτ_le
  have hx_zero :
      ((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_not_tsupport
  simp [x, nPointTimeSpatialSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hx_zero]

/-- Compact support of the original ordered-time test gives an upper bound on
the time block of the OS-I difference-coordinate pullback.  This is the upper
time-slab input needed for ambient differentiability of the Fourier-Laplace
integral near the positive-energy boundary. -/
theorem exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hf_compact
  let g : NPointDomain d n → (Fin n → ℝ) := fun y =>
    section43QTime (d := d) (n := n) ((section43DiffCoordRealCLE d n) y)
  have hg_cont : Continuous g := by
    dsimp [g, section43QTime, nPointTimeSpatialCLE]
    fun_prop
  rcases hK_compact.exists_bound_of_continuousOn (f := g) hg_cont.continuousOn with
    ⟨R₀, hR₀⟩
  let R : ℝ := max R₀ 0
  refine ⟨R, le_max_right R₀ 0, ?_⟩
  intro ξ hξ
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm ξ
  have hy : y ∈ K := by
    exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
      (section43DiffCoordRealCLE d n).symm.continuous hξ
  have hbound : ‖g y‖ ≤ R₀ := hR₀ y hy
  have hgy : g y = section43QTime (d := d) (n := n) ξ := by
    simp [g, y]
  have hboundξ : ‖section43QTime (d := d) (n := n) ξ‖ ≤ R₀ := by
    simpa [hgy] using hbound
  exact hboundξ.trans (le_max_left R₀ 0)

/-- Spatial Fourier transform does not enlarge the compact time slab: if a time
slice lies above the compact-support time-norm bound, the partial spatial
Fourier transform vanishes. -/
theorem partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {R : ℝ}
    (hR_supp :
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R)
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hτ : R < ‖τ‖) :
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) (τ, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards with η
  let x : NPointDomain d n := (nPointTimeSpatialCLE (d := d) n).symm (τ, η)
  have hx_not_tsupport :
      x ∉ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro hx
    have hx_bound := hR_supp x hx
    have htime : section43QTime (d := d) (n := n) x = τ := by
      ext i
      simp [x, section43QTime, nPointTimeSpatialCLE]
    have hle : ‖τ‖ ≤ R := by
      simpa [htime] using hx_bound
    exact not_le_of_gt hτ hle
  have hx_zero :
      ((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_not_tsupport
  simp [x, nPointTimeSpatialSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hx_zero]

/-- The pointwise first-derivative CLM of the Section 4.3 Fourier-Laplace
integrand vanishes on time slices outside the compact-support time slab. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_timeNorm_gt_bound
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {R : ℝ}
    (hR_supp :
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R)
    (q : NPointDomain d n) (τ : Fin n → ℝ)
    (hτ : R < ‖τ‖) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n
      (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ = 0 := by
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  have hP_zero :
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q) = 0 := by
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
        d n f hf_ord hR_supp τ
        (section43QSpatial (d := d) (n := n) q) hτ
  have hfun_zero :
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)) = fun _ => 0 := by
    funext ξ
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
        d n f hf_ord hR_supp τ ξ hτ
  have hfderiv_zero :
      fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q) = 0 := by
    rw [hfun_zero]
    simp
  ext m
  simp [section43FourierLaplace_timeIntegrandFDerivCLM, F, hP_zero, hfderiv_zero]

/-- For compact ordered support, the pointwise first-derivative CLM is compactly
supported as a function of the time variable `τ`. -/
theorem hasCompactSupport_section43FourierLaplace_timeIntegrandFDerivCLM_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    HasCompactSupport fun τ : Fin n → ℝ =>
      section43FourierLaplace_timeIntegrandFDerivCLM d n
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ := by
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    d n f hf_ord hf_compact with ⟨R, _hR_nonneg, hR_supp⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro τ hτ_support
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra hnot
  have hlt : R < ‖τ‖ := lt_of_not_ge hnot
  have hzero :=
    section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_timeNorm_gt_bound
      d n f hf_ord hR_supp q τ hlt
  exact hτ_support hzero

/-- On time slices above a strict support margin, the Laplace exponential gains
uniform damping by the total positive-energy time. -/
theorem norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (τ : Fin n → ℝ) {δ : ℝ}
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (hτ : ∀ i : Fin n, δ ≤ τ i) :
    ‖Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))‖ ≤
      Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hsum_ge :
      δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k ≤
        ∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hτ k) (by
        simpa [section43QTime, nPointTimeSpatialCLE] using hq k)
  have hre :
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))).re =
        -(∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k) := by
    simp
  rw [hre]
  exact neg_le_neg hsum_ge

/-- The strict ordered-support margin gives the Section 4.3 time integrand an
exponential positive-energy damping factor. -/
theorem norm_section43FourierLaplace_timeIntegrand_le_exp_neg_margin_sum
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) :
    ‖Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q)‖ ≤
      Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k)) *
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
  by_cases hlt : ∃ i : Fin n, τ i < δ
  · have hF_zero :
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q) = 0 := by
      exact partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
        d n f hf_ord hδ_supp τ (section43QSpatial (d := d) (n := n) q) hlt
    simp [hF_zero]
  · have hτ : ∀ i : Fin n, δ ≤ τ i := by
      intro i
      exact le_of_not_gt fun hi => hlt ⟨i, hi⟩
    have hE_le :=
      norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
        d n q τ hq hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hE_le (norm_nonneg _)

/-- Base norm estimate for the Section 4.3 Fourier-Laplace integral: the strict
ordered-support margin factors out as exponential positive-energy damping. -/
theorem section43FourierLaplaceIntegral_norm_le_exp_margin_integral
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
      ∫ τ : Fin n → ℝ,
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
  let E : (Fin n → ℝ) → ℂ := fun τ =>
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
      (τ, section43QSpatial (d := d) (n := n) q)
  let A : ℝ := Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k))
  have hF_int : Integrable F (volume : Measure (Fin n → ℝ)) := by
    simpa [F] using
      integrable_partialFourierSpatial_timeSlice
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (section43QSpatial (d := d) (n := n) q)
  have hAF_int : Integrable (fun τ : Fin n → ℝ => A * ‖F τ‖)
      (volume : Measure (Fin n → ℝ)) := by
    exact hF_int.norm.const_mul A
  have hpoint : ∀ τ : Fin n → ℝ, ‖E τ * F τ‖ ≤ A * ‖F τ‖ := by
    intro τ
    simpa [E, F, A] using
      norm_section43FourierLaplace_timeIntegrand_le_exp_neg_margin_sum
        d n f hf_ord hδ_supp q hq τ
  calc
    ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ = ‖∫ τ : Fin n → ℝ, E τ * F τ‖ := by
      simp [section43FourierLaplaceIntegral, E, F]
    _ ≤ ∫ τ : Fin n → ℝ, ‖E τ * F τ‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ τ : Fin n → ℝ, A * ‖F τ‖ := by
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun τ => norm_nonneg (E τ * F τ))
        hAF_int
        (Filter.Eventually.of_forall hpoint)
    _ = A * ∫ τ : Fin n → ℝ, ‖F τ‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
      ∫ τ : Fin n → ℝ,
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
      rfl

/-- The Euclidean norm is bounded by the sum of absolute coordinate values. -/
theorem euclidean_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (ξ : EuclideanSpace ℝ ι) :
    ‖ξ‖ ≤ ∑ i : ι, ‖ξ i‖ := by
  have hsum_nonneg : 0 ≤ ∑ i : ι, ‖ξ i‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg ξ) hsum_nonneg).mp
  calc
    ‖ξ‖ ^ 2 = ∑ i : ι, ‖ξ i‖ ^ 2 := EuclideanSpace.norm_sq_eq ξ
    _ ≤ (∑ i : ι, ‖ξ i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i : ι => ‖ξ i‖)
        (fun i _hi => norm_nonneg _)

/-- The finite sup norm on real-valued functions is bounded by the sum of
absolute coordinate values. -/
theorem pi_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    ‖x‖ ≤ ∑ i : ι, ‖x i‖ := by
  classical
  by_cases hne : (Finset.univ : Finset ι).Nonempty
  · obtain ⟨i, hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset ι)) hne
        (fun j : ι => ‖x j‖₊)
    have hnorm_eq : ‖x‖ = ‖x i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun y : NNReal => (y : ℝ)) hi_sup
    rw [hnorm_eq]
    exact Finset.single_le_sum (fun j _hj => norm_nonneg (x j)) hi
  · have hempty : (Finset.univ : Finset ι) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [Pi.norm_def]
    simp [hempty]

/-- On the nonnegative orthant, the finite sup norm is bounded by the sum of
coordinates. -/
theorem pi_norm_le_sum_of_nonneg {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∀ i : ι, 0 ≤ x i) :
    ‖x‖ ≤ ∑ i : ι, x i := by
  calc
    ‖x‖ ≤ ∑ i : ι, ‖x i‖ := pi_norm_le_sum_norm x
    _ = ∑ i : ι, x i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Real.norm_of_nonneg (hx i)

/-- Version of `euclidean_norm_le_sum_norm` with a dummy constant coordinate,
suited to later finite-power comparisons for `(1 + ‖ξ‖)^r`. -/
theorem one_add_euclidean_norm_le_sum_option_norm {ι : Type*} [Fintype ι]
    (ξ : EuclideanSpace ℝ ι) :
    1 + ‖ξ‖ ≤
      ∑ a : Option ι, match a with | none => (1 : ℝ) | some i => ‖ξ i‖ := by
  calc
    1 + ‖ξ‖ ≤ 1 + ∑ i : ι, ‖ξ i‖ := by
      nlinarith [euclidean_norm_le_sum_norm ξ]
    _ = ∑ a : Option ι, match a with | none => (1 : ℝ) | some i => ‖ξ i‖ := by
      simp

/-- Finite-coordinate power comparison for the Euclidean rapid-decay weight.

This turns the single weight `(1 + ‖ξ‖)^r` into a finite sum of coordinate
powers, with a dimension-only constant. -/
theorem one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
    {ι : Type*} [Fintype ι] (r : ℕ)
    (ξ : EuclideanSpace ℝ ι) :
    (1 + ‖ξ‖) ^ r ≤
      (Fintype.card (Option ι) : ℝ) ^ r *
        ∑ a : Option ι,
          (match a with | none => (1 : ℝ) | some i => ‖ξ i‖) ^ r := by
  classical
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  have hw_nonneg : ∀ a : Option ι, 0 ≤ w a := by
    intro a
    cases a <;> simp [w]
  have hbase : 1 + ‖ξ‖ ≤ ∑ a : Option ι, w a := by
    simpa [w] using one_add_euclidean_norm_le_sum_option_norm (ι := ι) ξ
  have hcard_ge_one : 1 ≤ (Fintype.card (Option ι) : ℝ) := by
    exact_mod_cast
      (Nat.succ_le_of_lt
        (Fintype.card_pos_iff.mpr ⟨(none : Option ι)⟩))
  cases r with
  | zero =>
      simp
  | succ m =>
      have hpow_base :
          (1 + ‖ξ‖) ^ (m + 1) ≤ (∑ a : Option ι, w a) ^ (m + 1) := by
        exact pow_le_pow_left₀ (by positivity) hbase (m + 1)
      have hjensen :
          (∑ a : Option ι, w a) ^ (m + 1) ≤
            (Fintype.card (Option ι) : ℝ) ^ m *
              ∑ a : Option ι, w a ^ (m + 1) := by
        simpa using
          (pow_sum_le_card_mul_sum_pow
            (s := (Finset.univ : Finset (Option ι))) (f := w)
            (fun a _ha => hw_nonneg a) m)
      have hcard_pow_le :
          (Fintype.card (Option ι) : ℝ) ^ m ≤
            (Fintype.card (Option ι) : ℝ) ^ (m + 1) := by
        calc
          (Fintype.card (Option ι) : ℝ) ^ m =
              (Fintype.card (Option ι) : ℝ) ^ m * 1 := by
                rw [mul_one]
          _ ≤ (Fintype.card (Option ι) : ℝ) ^ m *
              (Fintype.card (Option ι) : ℝ) := by
                exact mul_le_mul_of_nonneg_left hcard_ge_one (by positivity)
          _ = (Fintype.card (Option ι) : ℝ) ^ (m + 1) := by
                rw [pow_succ]
      have hsum_nonneg : 0 ≤ ∑ a : Option ι, w a ^ (m + 1) := by
        exact Finset.sum_nonneg fun a _ha => pow_nonneg (hw_nonneg a) (m + 1)
      calc
        (1 + ‖ξ‖) ^ (m + 1) ≤ (∑ a : Option ι, w a) ^ (m + 1) := hpow_base
        _ ≤ (Fintype.card (Option ι) : ℝ) ^ m *
            ∑ a : Option ι, w a ^ (m + 1) := hjensen
        _ ≤ (Fintype.card (Option ι) : ℝ) ^ (m + 1) *
            ∑ a : Option ι, w a ^ (m + 1) := by
              exact mul_le_mul_of_nonneg_right hcard_pow_le hsum_nonneg

/-- Uniform polynomial time decay of the partial spatial Fourier transform.

The older `exists_normPow_bound_partialFourierSpatial_timeSlice` exposes the
same estimate after fixing the spatial frequency.  This version keeps the
constant independent of that frequency, which is the form needed for
dominated-convergence estimates in the Fourier-Laplace witness construction. -/
theorem exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d)),
        ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  by_cases hK : K = 0
  · subst K
    refine ⟨C0, hC0_nonneg, ?_⟩
    intro τ ξ
    simpa using hC0 (τ, ξ)
  classical
  choose Ccoord hCcoord_nonneg hCcoord using
    fun i : Fin n =>
      exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
        (d := d) (n := n) f i K
  let Csum : ℝ := C0 + ∑ i : Fin n, Ccoord i
  refine ⟨Csum, add_nonneg hC0_nonneg (Finset.sum_nonneg fun i _ => hCcoord_nonneg i), ?_⟩
  intro τ ξ
  by_cases hτnorm : ‖τ‖ = 0
  · have hpow : ‖τ‖ ^ K = 0 := by
      rw [hτnorm]
      exact zero_pow hK
    exact le_trans (by simp [hpow]) (add_nonneg hC0_nonneg
      (Finset.sum_nonneg fun i _ => hCcoord_nonneg i))
  · have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      by_contra hne
      have hempty : (Finset.univ : Finset (Fin n)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hnorm_zero : ‖τ‖ = 0 := by
        rw [Pi.norm_def]
        simp [hempty]
      exact hτnorm hnorm_zero
    obtain ⟨i, _hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n))) huniv_nonempty
        (fun j : Fin n => ‖τ j‖₊)
    have hnorm_eq : ‖τ‖ = ‖τ i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun x : NNReal => (x : ℝ)) hi_sup
    have hcoord := hCcoord i (τ, ξ)
    have hrewrite :
        ‖τ‖ ^ K *
            ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, hnorm_eq]
    calc
      ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := hrewrite
      _ ≤ Ccoord i := hcoord
      _ ≤ Csum := by
        have hi_le_sum : Ccoord i ≤ ∑ j : Fin n, Ccoord j :=
          Finset.single_le_sum (fun j _ => hCcoord_nonneg j) (Finset.mem_univ i)
        exact hi_le_sum.trans (by simp [Csum, hC0_nonneg])

/-- Uniform integrable domination for time slices of the partial spatial
Fourier transform. -/
theorem exists_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  let μ : Measure (Fin n → ℝ) := volume
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) f μ.integrablePower with
    ⟨C1, hC1_nonneg, hC1⟩
  let I : ℝ := ∫ τ : Fin n → ℝ, (1 + ‖τ‖) ^ (-(μ.integrablePower : ℝ))
  let C : ℝ := 2 ^ μ.integrablePower * I * (C0 + C1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => by positivity
  refine ⟨C, by positivity, ?_⟩
  intro ξ
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hbound0 : ∀ τ : Fin n → ℝ, ‖F τ‖ ≤ C0 := by
    intro τ
    simpa [F] using hC0 (τ, ξ)
  have hboundPow : ∀ τ : Fin n → ℝ,
      ‖τ‖ ^ (0 + μ.integrablePower) * ‖F τ‖ ≤ C1 := by
    intro τ
    simpa [F, Nat.zero_add] using hC1 τ ξ
  have hmain := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := μ) (f := F) (C₁ := C0) (C₂ := C1) (k := 0) hbound0 hboundPow
  simpa [F, μ, C, I, Nat.zero_add] using hmain

/-- Uniform time-moment integral control for time slices of the partial
spatial Fourier transform.  This is the derivative-ready version of
`exists_integral_norm_partialFourierSpatial_timeSlice_uniform`: time
derivatives of the Laplace exponential introduce powers of `τ`. -/
theorem exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  let μ : Measure (Fin n → ℝ) := volume
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) f (K + μ.integrablePower) with
    ⟨C1, hC1_nonneg, hC1⟩
  let I : ℝ := ∫ τ : Fin n → ℝ, (1 + ‖τ‖) ^ (-(μ.integrablePower : ℝ))
  let C : ℝ := 2 ^ μ.integrablePower * I * (C0 + C1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => by positivity
  refine ⟨C, by positivity, ?_⟩
  intro ξ
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hbound0 : ∀ τ : Fin n → ℝ, ‖F τ‖ ≤ C0 := by
    intro τ
    simpa [F] using hC0 (τ, ξ)
  have hboundPow : ∀ τ : Fin n → ℝ,
      ‖τ‖ ^ (K + μ.integrablePower) * ‖F τ‖ ≤ C1 := by
    intro τ
    simpa [F] using hC1 τ ξ
  have hmain := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := μ) (f := F) (C₁ := C0) (C₂ := C1) (k := K) hbound0 hboundPow
  simpa [F, μ, C, I] using hmain

/-- Uniform time-integral control after multiplying by a spatial coordinate
power.  This is the coordinatewise integration-by-parts estimate used for the
spatial rapid-decay half of the Fourier-Laplace witness construction. -/
theorem exists_spatialCoordPow_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (i : Fin n × Fin d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖((((ξ i : ℝ) : ℂ)) ^ k) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  induction k generalizing f with
  | zero =>
      rcases exists_integral_norm_partialFourierSpatial_timeSlice_uniform
          (d := d) (n := n) f with
        ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro ξ
      simpa using hbound ξ
  | succ k ih =>
      let c : ℂ := 2 * Real.pi * Complex.I
      let g : SchwartzNPoint d n :=
        ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
          (LineDeriv.lineDerivOp ((EuclideanSpace.single i (1 : ℝ), (0 : Fin n → ℝ)))
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      rcases ih g with ⟨C, hC_nonneg, hbound⟩
      have hc0 : c ≠ 0 := by
        have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
          exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
        exact mul_ne_zero htwoPi Complex.I_ne_zero
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      refine ⟨C / ‖c‖, by positivity, ?_⟩
      intro ξ
      let z : ℂ := ((ξ i : ℝ) : ℂ)
      have hpoint : ∀ τ : Fin n → ℝ,
          ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ‖c‖⁻¹ *
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
        intro τ
        have htransport :
            (c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ) =
              partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
          simpa [c, g, z] using
            partialFourierSpatial_fun_spatialCoord_eq_transport
              (d := d) (n := n) f i (τ, ξ)
        have hscaled_eq :
            ‖c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                (τ, ξ))‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          congr 1
          calc
            c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ))
                = (z ^ k) *
                    ((c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)) := by
                    simp [pow_succ', mul_assoc, mul_left_comm]
            _ = (z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
                    rw [htransport]
        have hscaled :
            ‖c‖ *
                ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                  (τ, ξ)‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          rw [← hscaled_eq]
          simp
        calc
          ‖(z ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
              ‖c‖⁻¹ * (‖c‖ *
                ‖(z ^ (k + 1)) *
                  partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖) := by
                field_simp [hcnorm.ne']
          _ = ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
                rw [hscaled]
      calc
        ∫ τ : Fin n → ℝ,
          ‖((((ξ i : ℝ) : ℂ)) ^ (k + 1)) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ∫ τ : Fin n → ℝ,
              ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              simpa [z] using hpoint τ
        _ = ‖c‖⁻¹ * ∫ τ : Fin n → ℝ,
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              rw [MeasureTheory.integral_const_mul]
        _ ≤ ‖c‖⁻¹ * C := by
              exact mul_le_mul_of_nonneg_left (hbound ξ) (inv_nonneg.mpr hcnorm.le)
        _ = C / ‖c‖ := by
              rw [div_eq_mul_inv, mul_comm]

/-- Uniform time-moment integral control after multiplying by a spatial
coordinate power.  This combines the derivative-ready time moments with the
coordinatewise spatial integration-by-parts estimate. -/
theorem exists_spatialCoordPow_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (i : Fin n × Fin d) (k K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖((((ξ i : ℝ) : ℂ)) ^ k) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  induction k generalizing f with
  | zero =>
      rcases exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
          (d := d) (n := n) f K with
        ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro ξ
      simpa using hbound ξ
  | succ k ih =>
      let c : ℂ := 2 * Real.pi * Complex.I
      let g : SchwartzNPoint d n :=
        ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
          (LineDeriv.lineDerivOp ((EuclideanSpace.single i (1 : ℝ), (0 : Fin n → ℝ)))
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      rcases ih g with ⟨C, hC_nonneg, hbound⟩
      have hc0 : c ≠ 0 := by
        have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
          exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
        exact mul_ne_zero htwoPi Complex.I_ne_zero
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      refine ⟨C / ‖c‖, by positivity, ?_⟩
      intro ξ
      let z : ℂ := ((ξ i : ℝ) : ℂ)
      have hpoint : ∀ τ : Fin n → ℝ,
          ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ‖c‖⁻¹ *
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
        intro τ
        have htransport :
            (c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ) =
              partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
          simpa [c, g, z] using
            partialFourierSpatial_fun_spatialCoord_eq_transport
              (d := d) (n := n) f i (τ, ξ)
        have hscaled_eq :
            ‖c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                (τ, ξ))‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          congr 1
          calc
            c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ))
                = (z ^ k) *
                    ((c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)) := by
                    simp [pow_succ', mul_assoc, mul_left_comm]
            _ = (z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
                    rw [htransport]
        have hscaled :
            ‖c‖ *
                ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                  (τ, ξ)‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          rw [← hscaled_eq]
          simp
        calc
          ‖(z ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
              ‖c‖⁻¹ * (‖c‖ *
                ‖(z ^ (k + 1)) *
                  partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖) := by
                field_simp [hcnorm.ne']
          _ = ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
                rw [hscaled]
      calc
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖((((ξ i : ℝ) : ℂ)) ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                (‖c‖⁻¹ *
                  ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              simpa [z] using congrArg (fun y : ℝ => ‖τ‖ ^ K * y) (hpoint τ)
        _ = ∫ τ : Fin n → ℝ,
              ‖c‖⁻¹ *
                (‖τ‖ ^ K *
                  ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              ring
        _ = ‖c‖⁻¹ * ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              rw [MeasureTheory.integral_const_mul]
        _ ≤ ‖c‖⁻¹ * C := by
              exact mul_le_mul_of_nonneg_left (hbound ξ) (inv_nonneg.mpr hcnorm.le)
        _ = C / ‖c‖ := by
              rw [div_eq_mul_inv, mul_comm]

/-- Spatial rapid decay of every finite time-moment integral of the partial
spatial Fourier transform.  This is the main domination estimate needed when
time derivatives of the Fourier-Laplace integrand introduce powers of `τ`. -/
theorem section43PartialFourier_timeMomentIntegral_spatialRapid
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (K r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        (1 + ‖ξ‖) ^ r *
          ∫ τ : Fin n → ℝ,
            ‖τ‖ ^ K *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ ≤ C := by
  classical
  let ι : Type := Fin n × Fin d
  rcases exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) F K with
    ⟨C0, hC0_nonneg, hC0_bound⟩
  choose Ccoord hCcoord_nonneg hCcoord_bound using
    fun i : ι =>
      exists_spatialCoordPow_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
        (d := d) (n := n) F i r K
  let C : ℝ :=
    (Fintype.card (Option ι) : ℝ) ^ r *
      ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i
  have hsumC_nonneg :
      0 ≤ ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i := by
    exact Finset.sum_nonneg fun a _ha => by
      cases a <;> simp [hC0_nonneg, hCcoord_nonneg]
  refine ⟨C, mul_nonneg (by positivity) hsumC_nonneg, ?_⟩
  intro ξ
  let A : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖τ‖ ^ K *
        ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  let B : Option ι → ℝ := fun a =>
    match a with | none => A | some i => ‖ξ i‖ ^ r * A
  let D : Option ι → ℝ := fun a =>
    match a with | none => C0 | some i => Ccoord i
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun τ =>
      mul_nonneg (pow_nonneg (norm_nonneg τ) K) (norm_nonneg _)
  have hpow :
      (1 + ‖ξ‖) ^ r ≤
        (Fintype.card (Option ι) : ℝ) ^ r *
          ∑ a : Option ι, w a ^ r := by
    simpa [ι, w] using
      one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
        (ι := ι) r ξ
  have hsum_mul :
      (∑ a : Option ι, w a ^ r) * A = ∑ a : Option ι, B a := by
    rw [Finset.sum_mul]
    simp [B, w]
  have hB_le_D : ∀ a : Option ι, B a ≤ D a := by
    intro a
    cases a with
    | none =>
        simpa [B, D, A] using hC0_bound ξ
    | some i =>
        have hprod_eq :
            ‖ξ i‖ ^ r * A =
              ∫ τ : Fin n → ℝ,
                ‖τ‖ ^ K *
                  ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
          calc
            ‖ξ i‖ ^ r * A =
                ∫ τ : Fin n → ℝ,
                  ‖ξ i‖ ^ r *
                    (‖τ‖ ^ K *
                      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) := by
                  dsimp [A]
                  rw [MeasureTheory.integral_const_mul]
            _ = ∫ τ : Fin n → ℝ,
                ‖τ‖ ^ K *
                  ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with τ
                  rw [norm_mul, norm_pow, Complex.norm_real]
                  ring
        calc
          B (some i) = ‖ξ i‖ ^ r * A := by
            simp [B]
          _ = ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := hprod_eq
          _ ≤ Ccoord i := hCcoord_bound i ξ
          _ = D (some i) := by
            simp [D]
  have hsum_le : ∑ a : Option ι, B a ≤ ∑ a : Option ι, D a :=
    Finset.sum_le_sum fun a _ha => hB_le_D a
  calc
    (1 + ‖ξ‖) ^ r * A
        ≤ ((Fintype.card (Option ι) : ℝ) ^ r *
            ∑ a : Option ι, w a ^ r) * A := by
              exact mul_le_mul_of_nonneg_right hpow hA_nonneg
    _ = (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, B a := by
              rw [mul_assoc, hsum_mul]
    _ ≤ (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, D a := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = C := by
              simp [C, D]

/-- Spatial rapid decay of the time-integrated partial spatial Fourier
transform. -/
theorem section43PartialFourier_timeIntegral_spatialRapid
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        (1 + ‖ξ‖) ^ r *
          ∫ τ : Fin n → ℝ,
            ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ ≤ C := by
  classical
  let ι : Type := Fin n × Fin d
  rcases exists_integral_norm_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) F with
    ⟨C0, hC0_nonneg, hC0_bound⟩
  choose Ccoord hCcoord_nonneg hCcoord_bound using
    fun i : ι =>
      exists_spatialCoordPow_integral_norm_partialFourierSpatial_timeSlice_uniform
        (d := d) (n := n) F i r
  let C : ℝ :=
    (Fintype.card (Option ι) : ℝ) ^ r *
      ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i
  have hsumC_nonneg :
      0 ≤ ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i := by
    exact Finset.sum_nonneg fun a _ha => by
      cases a <;> simp [hC0_nonneg, hCcoord_nonneg]
  refine ⟨C, mul_nonneg (by positivity) hsumC_nonneg, ?_⟩
  intro ξ
  let A : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  let B : Option ι → ℝ := fun a =>
    match a with | none => A | some i => ‖ξ i‖ ^ r * A
  let D : Option ι → ℝ := fun a =>
    match a with | none => C0 | some i => Ccoord i
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun τ => norm_nonneg _
  have hpow :
      (1 + ‖ξ‖) ^ r ≤
        (Fintype.card (Option ι) : ℝ) ^ r *
          ∑ a : Option ι, w a ^ r := by
    simpa [ι, w] using
      one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
        (ι := ι) r ξ
  have hsum_mul :
      (∑ a : Option ι, w a ^ r) * A = ∑ a : Option ι, B a := by
    rw [Finset.sum_mul]
    simp [B, w]
  have hB_le_D : ∀ a : Option ι, B a ≤ D a := by
    intro a
    cases a with
    | none =>
        simpa [B, D, A] using hC0_bound ξ
    | some i =>
        have hprod_eq :
            ‖ξ i‖ ^ r * A =
              ∫ τ : Fin n → ℝ,
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
          calc
            ‖ξ i‖ ^ r * A =
                ∫ τ : Fin n → ℝ,
                  ‖ξ i‖ ^ r *
                    ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  dsimp [A]
                  rw [MeasureTheory.integral_const_mul]
            _ = ∫ τ : Fin n → ℝ,
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with τ
                  simp [norm_pow, Complex.norm_real]
        calc
          B (some i) = ‖ξ i‖ ^ r * A := by
            simp [B]
          _ = ∫ τ : Fin n → ℝ,
              ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := hprod_eq
          _ ≤ Ccoord i := hCcoord_bound i ξ
          _ = D (some i) := by
            simp [D]
  have hsum_le : ∑ a : Option ι, B a ≤ ∑ a : Option ι, D a :=
    Finset.sum_le_sum fun a _ha => hB_le_D a
  calc
    (1 + ‖ξ‖) ^ r * A
        ≤ ((Fintype.card (Option ι) : ℝ) ^ r *
            ∑ a : Option ι, w a ^ r) * A := by
              exact mul_le_mul_of_nonneg_right hpow hA_nonneg
    _ = (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, B a := by
              rw [mul_assoc, hsum_mul]
    _ ≤ (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, D a := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = C := by
              simp [C, D]

/-- Exponential damping in the positive-energy time variables dominates every
polynomial weight in the time norm. -/
theorem exp_margin_sum_controls_positiveEnergy_time_polynomial
    (d n : ℕ) [NeZero d]
    {δ : ℝ} (hδ_pos : 0 < δ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖section43QTime (d := d) (n := n) q‖) ^ r *
          Real.exp (-(δ * ∑ k : Fin n,
            section43QTime (d := d) (n := n) q k)) ≤ C := by
  rcases SCV.pow_mul_exp_neg_le_const hδ_pos r with
    ⟨C0, hC0_pos, hC0_bound⟩
  let C : ℝ := Real.exp δ * C0
  refine ⟨C, mul_nonneg (Real.exp_pos δ).le hC0_pos.le, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let s : ℝ := ∑ k : Fin n, t k
  have ht_nonneg : ∀ k : Fin n, 0 ≤ t k := by
    intro k
    simpa [t, section43QTime, nPointTimeSpatialCLE] using hq k
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun k _hk => ht_nonneg k
  have hnorm_le_sum : ‖t‖ ≤ s := by
    simpa [s] using pi_norm_le_sum_of_nonneg (x := t) ht_nonneg
  have hone_norm_le : 1 + ‖t‖ ≤ 1 + s := by
    linarith
  have hpow_le : (1 + ‖t‖) ^ r ≤ (1 + s) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hone_norm_le r
  have hx_nonneg : 0 ≤ 1 + s := by
    linarith
  have htail := hC0_bound (1 + s) hx_nonneg
  have hexp_eq :
      Real.exp (-(δ * s)) =
        Real.exp δ * Real.exp (-(δ * (1 + s))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (1 + ‖section43QTime (d := d) (n := n) q‖) ^ r *
        Real.exp (-(δ * ∑ k : Fin n,
          section43QTime (d := d) (n := n) q k))
        = (1 + ‖t‖) ^ r * Real.exp (-(δ * s)) := by
          simp [t, s]
    _ ≤ (1 + s) ^ r * Real.exp (-(δ * s)) := by
          exact mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le
    _ = Real.exp δ * ((1 + s) ^ r * Real.exp (-(δ * (1 + s)))) := by
          rw [hexp_eq]
          ring
    _ ≤ C := by
          exact mul_le_mul_of_nonneg_left htail (Real.exp_pos δ).le

/-- The full spacetime norm is controlled by the separated time and spatial
weights coming from `nPointTimeSpatialCLE`. -/
theorem one_add_norm_le_section43_time_spatial_product
    (d n : ℕ) [NeZero d] (q : NPointDomain d n) :
    1 + ‖q‖ ≤
      (1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖) *
        (1 + ‖section43QTime (d := d) (n := n) q‖) *
          (1 + ‖section43QSpatial (d := d) (n := n) q‖) := by
  let e := nPointTimeSpatialCLE (d := d) n
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let M : ℝ := ‖e.symm.toContinuousLinearMap‖
  let a : ℝ := ‖t‖
  let b : ℝ := ‖ξ‖
  let P : ℝ := (1 + a) * (1 + b)
  have hM_nonneg : 0 ≤ M := by
    exact norm_nonneg _
  have ha_nonneg : 0 ≤ a := by
    exact norm_nonneg _
  have hb_nonneg : 0 ≤ b := by
    exact norm_nonneg _
  have hpair_eq : (t, ξ) = e q := by
    ext i <;> simp [t, ξ, e, section43QTime, section43QSpatial]
  have hq_eq : q = e.symm (t, ξ) := by
    rw [hpair_eq]
    simp [e]
  have hpair_norm : ‖(t, ξ)‖ ≤ a + b := by
    dsimp [a, b]
    exact max_le_add_of_nonneg (norm_nonneg t) (norm_nonneg ξ)
  have hq_norm : ‖q‖ ≤ M * (a + b) := by
    calc
      ‖q‖ = ‖e.symm (t, ξ)‖ := by
        rw [hq_eq]
      _ ≤ M * ‖(t, ξ)‖ := by
        simpa [M] using
          (ContinuousLinearMap.le_opNorm e.symm.toContinuousLinearMap (t, ξ))
      _ ≤ M * (a + b) := by
        exact mul_le_mul_of_nonneg_left hpair_norm hM_nonneg
  have hP_ge_one : 1 ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  have hP_ge_a : a ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  have hP_ge_b : b ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  calc
    1 + ‖q‖ ≤ 1 + M * (a + b) := by
      linarith
    _ ≤ (1 + 2 * M) * P := by
      nlinarith [hM_nonneg, hP_ge_one, hP_ge_a, hP_ge_b]
    _ = (1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖) *
        (1 + ‖section43QTime (d := d) (n := n) q‖) *
          (1 + ‖section43QSpatial (d := d) (n := n) q‖) := by
      simp [M, P, a, b, t, ξ, e, mul_assoc]

/-- Zero-derivative rapid decay of the Section 4.3 Fourier-Laplace integral on
the positive-energy half-space. -/
theorem section43FourierLaplaceIntegral_rapid_on_positiveEnergy_zeroDeriv
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖q‖) ^ r *
          ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤ C := by
  intro r
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases section43PartialFourier_timeIntegral_spatialRapid
      (d := d) (n := n) F r with
    ⟨Csp, hCsp_nonneg, hCsp_bound⟩
  rcases exp_margin_sum_controls_positiveEnergy_time_polynomial
      (d := d) (n := n) hδ_pos r with
    ⟨Ct, hCt_nonneg, hCt_bound⟩
  let A : ℝ :=
    1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖
  let C : ℝ := A ^ r * Ct * Csp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨C, mul_nonneg (mul_nonneg (pow_nonneg hA_nonneg r) hCt_nonneg) hCsp_nonneg, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let I : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let E : ℝ := Real.exp (-(δ * ∑ k : Fin n, t k))
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => norm_nonneg _
  have hspatial :
      (1 + ‖ξ‖) ^ r * I ≤ Csp := by
    simpa [I, F, ξ] using hCsp_bound ξ
  have htime :
      (1 + ‖t‖) ^ r * E ≤ Ct := by
    simpa [t, E] using hCt_bound q hq
  have hscalar :
      ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤ E * I := by
    simpa [E, I, F, t, ξ] using
      section43FourierLaplaceIntegral_norm_le_exp_margin_integral
        d n f hf_ord hδ_supp q hq
  have hnorm :
      1 + ‖q‖ ≤ A * (1 + ‖t‖) * (1 + ‖ξ‖) := by
    simpa [A, t, ξ] using
      one_add_norm_le_section43_time_spatial_product d n q
  have hpow_norm :
      (1 + ‖q‖) ^ r ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hnorm r
  have htime_nonneg : 0 ≤ (1 + ‖t‖) ^ r * E := by
    exact mul_nonneg (pow_nonneg (by positivity) r) (Real.exp_pos _).le
  have hspatial_nonneg : 0 ≤ (1 + ‖ξ‖) ^ r * I := by
    exact mul_nonneg (pow_nonneg (by positivity) r) hI_nonneg
  have hterm_prod :
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I) ≤ Ct * Csp := by
    calc
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I)
          ≤ Ct * ((1 + ‖ξ‖) ^ r * I) := by
            exact mul_le_mul_of_nonneg_right htime hspatial_nonneg
      _ ≤ Ct * Csp := by
            exact mul_le_mul_of_nonneg_left hspatial hCt_nonneg
  calc
    (1 + ‖q‖) ^ r *
        ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖
        ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r *
            ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ := by
          exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
    _ ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r * (E * I) := by
          exact mul_le_mul_of_nonneg_left hscalar (pow_nonneg (by positivity) r)
    _ = A ^ r * (((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I)) := by
          rw [mul_pow, mul_pow]
          ring
    _ ≤ A ^ r * (Ct * Csp) := by
          exact mul_le_mul_of_nonneg_left hterm_prod (pow_nonneg hA_nonneg r)
    _ = C := by
          simp [C, mul_assoc]

end OSReconstruction
