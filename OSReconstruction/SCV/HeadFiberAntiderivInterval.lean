/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.HeadFiberAntideriv

/-!
# Head-fiber interval pieces and raw antiderivative

This file contains the variable interval piece and head-direction FTC package
used by the finite-dimensional head-fiber antiderivative in the theorem-2
descent route.  The restricted half-line slice `iicZeroSlice` is already in
`SCV.HeadFiberAntideriv`.
-/

noncomputable section

open scoped SchwartzMap Topology
open MeasureTheory SchwartzMap LineDeriv

namespace SCV

/-- The improper integral over `(-∞, x]` has derivative equal to the integrand,
for continuous integrable functions. This is the scalar FTC input needed for the
head-direction derivative of the fiberwise antiderivative. -/
theorem hasDerivAt_integral_Iic {f : ℝ → ℂ}
    (hf_cont : Continuous f)
    (hf_int : Integrable f (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (a : ℝ) :
    HasDerivAt (fun x => ∫ t in Set.Iic x, f t) (f a) a := by
  have hsplit :
      ∀ x : ℝ,
        ∫ t in Set.Iic x, f t
          = (∫ t in (0 : ℝ)..x, f t) + ∫ t in Set.Iic (0 : ℝ), f t := by
    intro x
    have hIic_x :
        Filter.Tendsto (fun r => ∫ t in r..x, f t) Filter.atBot
          (nhds (∫ t in Set.Iic x, f t)) :=
      intervalIntegral_tendsto_integral_Iic x hf_int.integrableOn Filter.tendsto_id
    have hIic_zero :
        Filter.Tendsto (fun r => ∫ t in r..(0 : ℝ), f t) Filter.atBot
          (nhds (∫ t in Set.Iic (0 : ℝ), f t)) :=
      intervalIntegral_tendsto_integral_Iic 0 hf_int.integrableOn Filter.tendsto_id
    have hadd :
        ∀ r : ℝ,
          ∫ t in r..x, f t =
            (∫ t in r..(0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t := by
      intro r
      exact (intervalIntegral.integral_add_adjacent_intervals
        hf_int.intervalIntegrable hf_int.intervalIntegrable).symm
    have hlim :=
      hIic_zero.add_const (∫ t in (0 : ℝ)..x, f t)
    have heq_lim :
        Filter.Tendsto (fun r => ∫ t in r..x, f t) Filter.atBot
          (nhds ((∫ t in Set.Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t)) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall fun r => (hadd r).symm) hlim
    rw [tendsto_nhds_unique hIic_x heq_lim, add_comm]
  have heq :
      (fun x => ∫ t in Set.Iic x, f t)
        = fun x => (∫ t in (0 : ℝ)..x, f t) + ∫ t in Set.Iic (0 : ℝ), f t := by
    funext x
    exact hsplit x
  rw [heq]
  have hinterval :
      HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f a) a :=
    intervalIntegral.integral_hasDerivAt_right
      hf_int.intervalIntegrable
      (hf_cont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hf_cont.continuousAt
  let c : ℂ := ∫ t in Set.Iic (0 : ℝ), f t
  have hsum :
      HasDerivAt
        (fun x => (∫ t in (0 : ℝ)..x, f t) + c)
        (f a) a := by
    simpa [c] using hinterval.add_const c
  simpa [c] using hsum

/-- The variable-limit interval piece of the head antiderivative construction. -/
def intervalPiece {n : ℕ} (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t (Fin.tail v))

/-- In the head direction, the interval piece differentiates to the original
Schwartz function by the one-variable FTC. -/
theorem hasDerivAt_intervalPiece_head {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, F (Fin.cons t (Fin.tail v)))
      (F v) (v 0) := by
  set y : Fin n → ℝ := Fin.tail v
  have hcont : Continuous (fun t : ℝ => F (Fin.cons t y)) := by
    exact F.continuous.comp (continuous_pi fun j =>
      Fin.cases continuous_id (fun _ => continuous_const) j)
  have hFTC : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, F (Fin.cons t y))
      (F (Fin.cons (v 0) y)) (v 0) :=
    intervalIntegral.integral_hasDerivAt_right
      (integrable_sliceSection F y).intervalIntegrable
      (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hcont.continuousAt
  rwa [show F (Fin.cons (v 0) y) = F v from congr_arg F (Fin.cons_self_tail v)] at hFTC

/-- For fixed upper limit `a`, the interval piece is Fréchet differentiable in
the tail variables, with derivative obtained by integrating the ambient
derivative composed with `tailInsertCLM`. -/
theorem hasFDerivAt_intervalPiece_tailFixed {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (a : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt
      (fun y' : Fin n → ℝ => ∫ t in (0 : ℝ)..a, F (Fin.cons t y'))
      (∫ t in (0 : ℝ)..a,
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
          (tailInsertCLM n)))
      y := by
  let bound1 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * (1 + x ^ 2)⁻¹
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds y := Filter.univ_mem
  have hF_meas :
      ∀ᶠ y' in nhds y,
        AEStronglyMeasurable (fun t : ℝ => F (Fin.cons t y'))
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    refine Filter.Eventually.of_forall ?_
    intro y'
    have hcont : Continuous (fun t : ℝ => F (Fin.cons t y')) := by
      have hpath : Continuous fun t : ℝ => (Fin.cons t y' : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun t : ℝ => t)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y' i)
      exact F.continuous.comp hpath
    exact hcont.aestronglyMeasurable.restrict
  have hF_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t y)) MeasureTheory.volume (0 : ℝ) a := by
    exact (integrable_sliceSection F y).intervalIntegrable
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
            (tailInsertCLM n)))
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    have hpath : Continuous fun t : ℝ => (Fin.cons t y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    have hcont :
        Continuous
          (fun t : ℝ =>
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
              (tailInsertCLM n))) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    exact hcont.aestronglyMeasurable.restrict
  have h_bound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 t := by
    exact Filter.Eventually.of_forall (fun t y' _ => by
      simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' t)
  have h_bound_int :
      IntervalIntegrable bound1 MeasureTheory.volume (0 : ℝ) a := by
    exact (integrable_inv_one_add_sq.const_mul
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F)).intervalIntegrable
  have h_diff :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt
            (fun y'' : Fin n → ℝ => F (Fin.cons t y''))
            ((((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
              (tailInsertCLM n)))
            y' := by
    exact Filter.Eventually.of_forall
      (fun t y' _ => hasFDerivAt_sliceSection F t y')
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (μ := MeasureTheory.volume)
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := y)
      (F := fun y' t => F (Fin.cons t y'))
      (F' := fun y' t =>
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
          (tailInsertCLM n)))
      (a := (0 : ℝ)) (b := a)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)

/-- Splitting the interval piece at a base point `a`. This is the clean
algebraic decomposition behind the product-space derivative proof. -/
theorem intervalPiece_split_at {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (a x : ℝ) (y : Fin n → ℝ) :
    (∫ t in (0 : ℝ)..x, F (Fin.cons t y)) =
      (∫ t in (0 : ℝ)..a, F (Fin.cons t y)) +
      ∫ t in a..x, F (Fin.cons t y) := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (integrable_sliceSection F y).intervalIntegrable
    (integrable_sliceSection F y).intervalIntegrable).symm

/-- The fixed-interval tail piece is Fréchet differentiable on the product
space; its derivative only sees the tail variable. -/
theorem hasFDerivAt_intervalPiece_tailFixed_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (a : ℝ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..a, F (Fin.cons t q.2))
      ((∫ t in (0 : ℝ)..a,
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
            (tailInsertCLM n))).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))
      p := by
  simpa using
    (hasFDerivAt_intervalPiece_tailFixed F a p.2).comp p hasFDerivAt_snd

/-- The fixed-tail moving-endpoint piece is Fréchet differentiable on the
product space; its derivative only sees the head variable. -/
theorem hasFDerivAt_intervalPiece_headFixed_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2))
      ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
        (F (Fin.cons p.1 p.2)))
      p := by
  have hcont : Continuous (fun t : ℝ => F (Fin.cons t p.2)) := by
    have hpath : Continuous fun t : ℝ => (Fin.cons t p.2 : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => p.2 i)
    exact F.continuous.comp hpath
  have hhead :
      HasDerivAt (fun x : ℝ => ∫ t in p.1..x, F (Fin.cons t p.2))
        (F (Fin.cons p.1 p.2)) p.1 := by
    exact intervalIntegral.integral_hasDerivAt_right
      (integrable_sliceSection F p.2).intervalIntegrable
      (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hcont.continuousAt
  have hfst :
      HasFDerivAt
        (fun q : ℝ × (Fin n → ℝ) => q.1)
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
        p := hasFDerivAt_fst
  simpa using hhead.hasFDerivAt.comp p hfst

/-- The remaining error term after splitting the interval piece into the
fixed-interval tail piece and the fixed-tail moving-endpoint piece. This is the
only nonlinear interaction still missing in the joint product-space derivative. -/
def intervalPieceShortTailError {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (p q : ℝ × (Fin n → ℝ)) : ℂ :=
  ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))

/-- Exact product-space decomposition of the interval piece around a base point
`p = (a, y)`. The first term has only tail variation, the second only head
variation, and the third is the genuine mixed error term. -/
theorem intervalPiece_prod_split {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (p q : ℝ × (Fin n → ℝ)) :
    ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2) =
      (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
      (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
      intervalPieceShortTailError F p q := by
  rw [intervalPieceShortTailError]
  have hp_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t p.2)) MeasureTheory.volume p.1 q.1 := by
    exact (integrable_sliceSection F p.2).intervalIntegrable
  have hq_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t q.2)) MeasureTheory.volume p.1 q.1 := by
    exact (integrable_sliceSection F q.2).intervalIntegrable
  have hsub_int :
      IntervalIntegrable
        (fun t : ℝ => F (Fin.cons t q.2) - F (Fin.cons t p.2)) MeasureTheory.volume p.1 q.1 := by
    exact hq_int.sub hp_int
  calc
    ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)
        = (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
            ∫ t in p.1..q.1, F (Fin.cons t q.2) := by
              exact intervalPiece_split_at F p.1 q.1 q.2
    _ =
        (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          ((∫ t in p.1..q.1, F (Fin.cons t p.2)) +
            ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))) := by
              congr 1
              calc
                ∫ t in p.1..q.1, F (Fin.cons t q.2)
                    = ∫ t in p.1..q.1,
                        (F (Fin.cons t p.2) +
                          (F (Fin.cons t q.2) - F (Fin.cons t p.2))) := by
                            refine intervalIntegral.integral_congr_ae ?_
                            exact Filter.Eventually.of_forall (fun t _ => by ring)
                _ =
                    (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
                    ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2)) := by
                      exact intervalIntegral.integral_add hp_int hsub_int
    _ =
        (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
          ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2)) := by
            ring_nf

/-- The mixed short-tail error is quadratic in the head/tail increments: its
norm is bounded by a global Schwartz seminorm constant times
`|q₀ - p₀| * ‖q_tail - p_tail‖`. -/
theorem norm_intervalPieceShortTailError_le {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p q : ℝ × (Fin n → ℝ)) :
    ‖intervalPieceShortTailError F p q‖ ≤
      (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖) *
        |q.1 - p.1| := by
  rw [intervalPieceShortTailError]
  let C : ℝ :=
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖
  have hmain :
      ‖∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))‖ ≤
        C * |q.1 - p.1| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    have hdiff :
        ∀ z : Fin n → ℝ, DifferentiableAt ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z := by
      intro z
      exact (hasFDerivAt_sliceSection F t z).differentiableAt
    have hbound :
        ∀ z : Fin n → ℝ,
          ‖fderiv ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z‖ ≤
            (4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
      intro z
      calc
        ‖fderiv ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z‖
            = ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t z))).comp
                (tailInsertCLM n))‖ := by
                  simpa using congrArg norm (hasFDerivAt_sliceSection F t z).fderiv
        _ ≤ ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * (1 + t ^ 2)⁻¹ := by
              simpa using norm_fderiv_sliceSection_le_inv_one_add_sq F z t
        _ ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
              have hone : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
              have hinv : (1 + t ^ 2)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hone
              have hCnonneg :
                  0 ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
                    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
                positivity
              have hm := mul_le_mul_of_nonneg_left hinv hCnonneg
              simpa using hm
    have hmv :
        ‖F (Fin.cons t q.2) - F (Fin.cons t p.2)‖ ≤
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖ := by
      simpa using
        (Convex.norm_image_sub_le_of_norm_fderiv_le
          (s := (Set.univ : Set (Fin n → ℝ)))
          (f := fun y' : Fin n → ℝ => F (Fin.cons t y'))
          (x := p.2) (y := q.2)
          (fun z _ => hdiff z)
          (fun z _ => hbound z)
          convex_univ (by simp) (by simp))
    simpa [C] using hmv
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- The mixed short-tail error has zero Fréchet derivative at the base point.
This is the key nonlinear remainder estimate behind the full derivative of the
interval piece. -/
theorem hasFDerivAt_intervalPieceShortTailError {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt (intervalPieceShortTailError F p)
      (0 : (ℝ × (Fin n → ℝ)) →L[ℝ] ℂ) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hp0 : intervalPieceShortTailError F p p = 0 := by
    simp [intervalPieceShortTailError]
  have hbig :
      (fun h : ℝ × (Fin n → ℝ) => intervalPieceShortTailError F p (p + h)) =O[𝓝 0]
        fun h : ℝ × (Fin n → ℝ) => ‖h‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) ?_
    refine Filter.Eventually.of_forall ?_
    intro h
    have hbase := norm_intervalPieceShortTailError_le F p (p + h)
    have hfst : |h.1| ≤ ‖h‖ := by
      calc
        |h.1| = ‖h.1‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖h‖ := by
          calc
            ‖h.1‖ = ‖ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) h‖ := by rfl
            _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)‖ * ‖h‖ := by
                  exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖h‖ := by
                  gcongr
                  exact ContinuousLinearMap.norm_fst_le ℝ ℝ (Fin n → ℝ)
            _ = ‖h‖ := by ring
    have hsnd : ‖h.2‖ ≤ ‖h‖ := by
      calc
        ‖h.2‖ = ‖ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ) h‖ := by rfl
        _ ≤ ‖ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)‖ * ‖h‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖h‖ := by
              gcongr
              exact ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin n → ℝ)
        _ = ‖h‖ := by ring
    have hCnonneg :
        0 ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
      positivity
    have hprod :
        (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h.2‖) * |h.1| ≤
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h‖ ^ 2 := by
      have hmul :
          ‖h.2‖ * |h.1| ≤ ‖h‖ * ‖h‖ := by
        exact mul_le_mul hsnd hfst (abs_nonneg _) (norm_nonneg _)
      have hleft := mul_le_mul_of_nonneg_left hmul hCnonneg
      simpa [pow_two, mul_assoc] using hleft
    have hsimp :
        ‖intervalPieceShortTailError F p (p + h)‖ ≤
          (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h.2‖) * |h.1| := by
      simpa [Prod.fst_add, Prod.snd_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    refine hsimp.trans ?_
    refine hprod.trans ?_
    have hsq_nonneg : 0 ≤ ‖h‖ ^ 2 := by positivity
    simp [Real.norm_of_nonneg hsq_nonneg]
  have hsmall :
      (fun h : ℝ × (Fin n → ℝ) =>
        intervalPieceShortTailError F p (p + h) - intervalPieceShortTailError F p p) =o[𝓝 0]
          fun h : ℝ × (Fin n → ℝ) => h := by
    simpa [hp0] using
      hbig.trans_isLittleO
        (Asymptotics.isLittleO_norm_pow_id (E' := ℝ × (Fin n → ℝ)) one_lt_two)
  simpa using hsmall

/-- The head/tail coordinate map on `Fin (n+1) → ℝ`. -/
noncomputable def headTailCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).prod
    (tailCLM n)

@[simp] theorem headTailCLM_apply {n : ℕ} (v : Fin (n + 1) → ℝ) :
    headTailCLM n v = (v 0, Fin.tail v) := rfl

/-- Product-space Fréchet derivative of the interval piece. This is the clean
assembly of the head FTC term, the tail DCT term, and the zero-derivative mixed
error. -/
theorem hasFDerivAt_intervalPiece_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2))
      (((∫ t in (0 : ℝ)..p.1,
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
            (tailInsertCLM n))).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))) +
        ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
          (F (Fin.cons p.1 p.2))))
      p := by
  have hsplit :
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)) =
        (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
        (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2)) +
        intervalPieceShortTailError F p := by
    funext q
    simpa [Pi.add_apply, add_assoc] using intervalPiece_prod_split F p q
  have htail := hasFDerivAt_intervalPiece_tailFixed_prod F p.1 p
  have hhead := hasFDerivAt_intervalPiece_headFixed_prod F p
  have herr := hasFDerivAt_intervalPieceShortTailError F p
  have hsum :
      HasFDerivAt
        ((fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2)) +
          intervalPieceShortTailError F p)
        ((((∫ t in (0 : ℝ)..p.1,
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
              (tailInsertCLM n))).comp
            (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))) +
          ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
            (F (Fin.cons p.1 p.2)))) +
          (0 : (ℝ × (Fin n → ℝ)) →L[ℝ] ℂ))
        p := by
    exact (htail.add hhead).add herr
  simpa [hsplit, add_assoc] using hsum

/-- The interval piece is C^1 (combining FTC for head + DCT for tail).
This is the key HasFDerivAt step. -/
theorem hasFDerivAt_intervalPiece {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    HasFDerivAt (intervalPiece F)
      (ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F v) +
       (∫ t in (0 : ℝ)..(v 0),
          ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail v))).comp
            (tailInsertCLM n))).comp (tailCLM n))
       v := by
  have hprod := hasFDerivAt_intervalPiece_prod F (headTailCLM n v)
  have hcomp :
      HasFDerivAt (fun w : Fin (n + 1) → ℝ => headTailCLM n w) (headTailCLM n) v := by
    simpa using (headTailCLM n).hasFDerivAt
  have h := hprod.comp v hcomp
  let Ltail : (Fin n → ℝ) →L[ℝ] ℂ :=
    ∫ t in (0 : ℝ)..(v 0),
      ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail v))).comp
        (tailInsertCLM n))
  let LprodComp : (Fin (n + 1) → ℝ) →L[ℝ] ℂ :=
    ((Ltail.comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))).comp (headTailCLM n)) +
      (((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
        (F (Fin.cons (v 0) (Fin.tail v)))).comp (headTailCLM n))
  let Ltarget : (Fin (n + 1) → ℝ) →L[ℝ] ℂ :=
    ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F v) +
      Ltail.comp (tailCLM n)
  have h' :
      HasFDerivAt
        ((fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)) ∘ headTailCLM n)
        LprodComp
        v := by
    simpa [LprodComp, Ltail, headTailCLM_apply, Fin.cons_self_tail] using h
  have hL : LprodComp = Ltarget := by
    ext w
    simp [LprodComp, Ltarget, Ltail, headTailCLM, tailCLM_apply,
      ContinuousLinearMap.comp_apply, Fin.cons_self_tail, add_comm]
  simpa [intervalPiece, Ltarget, hL] using h'

/-- The interval piece is C^∞. Proof by induction on derivative order:
- Head derivative of intervalPiece F = F (Schwartz, hence C^∞)
- Tail derivative of intervalPiece F = intervalPiece (fderivCLM F) ∘ tailInsertCLM
  (same structure, apply IH)
- Combined: C^{m+1} from C^m of both derivatives. -/
theorem contDiff_intervalPiece {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (intervalPiece F) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing F with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_iff_continuousAt.2 fun x => (hasFDerivAt_intervalPiece F x).continuousAt
  | succ m ih =>
      simpa using
        (contDiff_succ_iff_fderiv_apply
          (𝕜 := ℝ) (D := Fin (n + 1) → ℝ)
          (n := (m : ℕ∞)) (f := intervalPiece F)).2 <|
          ⟨fun x => (hasFDerivAt_intervalPiece F x).differentiableAt, by simp,
            fun y => by
              let ytail : Fin (n + 1) → ℝ := tailInsertCLM n (tailCLM n y)
              let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := lineDerivOp ytail F
              have hEq :
                  (fun x : Fin (n + 1) → ℝ => (fderiv ℝ (intervalPiece F) x) y) =
                    fun x : Fin (n + 1) → ℝ =>
                      (y 0 : ℝ) • F x + intervalPiece dF x := by
                funext x
                let φ : ℝ → (Fin n → ℝ) →L[ℝ] ℂ := fun t =>
                  ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
                    (tailInsertCLM n))
                have hφ_cont :
                    Continuous φ := by
                  have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
                    classical
                    refine continuous_pi ?_
                    intro j
                    refine Fin.cases ?_ ?_ j
                    · simpa using (continuous_id : Continuous fun t : ℝ => t)
                    · intro i
                      simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
                  simpa [φ] using
                    (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
                have hφ_int :
                    IntervalIntegrable φ MeasureTheory.volume (0 : ℝ) (x 0) := by
                  exact hφ_cont.intervalIntegrable _ _
                rw [(hasFDerivAt_intervalPiece F x).fderiv]
                calc
                  ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).smulRight (F x) +
                      ((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n))) y
                      = (y 0 : ℝ) • F x + (∫ t in (0 : ℝ)..(x 0), φ t) (Fin.tail y) := by
                          simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
                            ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply,
                            tailCLM_apply]
                          congr 1
                  _ = (y 0 : ℝ) • F x + ∫ t in (0 : ℝ)..(x 0), (φ t) (Fin.tail y) := by
                          rw [ContinuousLinearMap.intervalIntegral_apply hφ_int (Fin.tail y)]
                  _ = (y 0 : ℝ) • F x + intervalPiece dF x := by
                          simp [intervalPiece, ytail, dF, φ, SchwartzMap.lineDerivOp_apply_eq_fderiv,
                            tailInsertCLM_apply]
                          have htailfun : (fun i => y i.succ) = Fin.tail y := by
                            ext i
                            rfl
                          rw [htailfun]
              simpa [hEq] using ((F.smooth m).const_smul (y 0)).add (ih dF)⟩

/-- Fiberwise antiderivative along the head coordinate. For fixed tail variables,
integrate the head slice over `(-∞, x₀]`. This is the raw construction behind
the multi-dimensional Schwartz Poincare lemma. -/
def headFiberAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (Fin (n + 1) → ℝ) → ℂ :=
  fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

/-- The raw head antiderivative splits into the variable-limit interval piece
plus the fixed `(-∞, 0]` slice. -/
theorem headFiberAntiderivRaw_eq_interval_add_iic {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    headFiberAntiderivRaw F v =
      intervalPiece F v + iicZeroSlice F (Fin.tail v) := by
  set y : Fin n → ℝ := Fin.tail v
  rw [headFiberAntiderivRaw, intervalPiece, iicZeroSlice]
  change ∫ t in Set.Iic (v 0), F (Fin.cons t y) =
    (∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y)) +
      ∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)
  have hf_int := integrable_sliceSection F y
  have hIic_v0 :
      Filter.Tendsto (fun r => ∫ t in r..(v 0), F (Fin.cons t y)) Filter.atBot
        (nhds (∫ t in Set.Iic (v 0), F (Fin.cons t y))) :=
    intervalIntegral_tendsto_integral_Iic (v 0) hf_int.integrableOn Filter.tendsto_id
  have hIic_0 :
      Filter.Tendsto (fun r => ∫ t in r..(0 : ℝ), F (Fin.cons t y)) Filter.atBot
        (nhds (∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y))) :=
    intervalIntegral_tendsto_integral_Iic 0 hf_int.integrableOn Filter.tendsto_id
  have hadd : ∀ r : ℝ,
      ∫ t in r..(v 0), F (Fin.cons t y) =
        (∫ t in r..(0 : ℝ), F (Fin.cons t y)) + ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y) :=
    fun r => (intervalIntegral.integral_add_adjacent_intervals
      hf_int.intervalIntegrable hf_int.intervalIntegrable).symm
  have hlim := hIic_0.add_const (∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y))
  have heq_lim :
      Filter.Tendsto (fun r => ∫ t in r..(v 0), F (Fin.cons t y)) Filter.atBot
        (nhds ((∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)) +
               ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y))) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun r => (hadd r).symm) hlim
  rw [tendsto_nhds_unique hIic_v0 heq_lim, add_comm]

/-- Differentiating the raw fiberwise antiderivative in the head direction
recovers the original Schwartz function. -/
theorem lineDeriv_headFiberAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    lineDeriv ℝ (headFiberAntiderivRaw F) v (Pi.single 0 1) = F v := by
  set e0 : Fin (n + 1) → ℝ := Pi.single 0 1 with he0
  set y : Fin n → ℝ := Fin.tail v with hy
  set G : ℝ → ℂ := fun s => F (Fin.cons s y) with hG
  have hG_cont : Continuous G := by
    rw [hG]
    have hcons_cont : Continuous (fun s : ℝ => (Fin.cons s y : Fin (n + 1) → ℝ)) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun s : ℝ => s)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    exact F.continuous.comp hcons_cont
  have hG_int : Integrable G (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [hG]
    simpa [hy] using integrable_sliceSection (F := F) (y := Fin.tail v)
  have hFTC : HasDerivAt (fun x => ∫ s in Set.Iic x, G s) (G (v 0)) (v 0) :=
    hasDerivAt_integral_Iic hG_cont hG_int (v 0)
  have hcomp : HasDerivAt (fun t => ∫ s in Set.Iic (v 0 + t), G s) (G (v 0)) 0 := by
    have hFTC' : HasDerivAt (fun x => ∫ s in Set.Iic x, G s) (G (v 0)) (v 0 + 0) := by
      simpa using hFTC
    simpa using hFTC'.comp_const_add (v 0) 0
  have heq :
      ∀ t : ℝ,
        headFiberAntiderivRaw F (v + t • e0)
          = ∫ s in Set.Iic (v 0 + t), G s := by
    intro t
    rw [headFiberAntiderivRaw, hG]
    have hhead : (v + t • e0) 0 = v 0 + t := by
      simp [e0, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, mul_one]
    have htail :
        Fin.tail (v + t • e0) = y := by
      ext i
      simp [Fin.tail, e0, hy, Pi.add_apply, Pi.smul_apply]
    rw [hhead, htail]
  have hline : HasLineDerivAt ℝ (headFiberAntiderivRaw F) (G (v 0)) v e0 := by
    show HasDerivAt (fun t => headFiberAntiderivRaw F (v + t • e0)) (G (v 0)) 0
    have hfun :
        (fun t => headFiberAntiderivRaw F (v + t • e0))
          = fun t => ∫ s in Set.Iic (v 0 + t), G s := by
      funext t
      exact heq t
    rw [hfun]
    exact hcomp
  rw [hline.lineDeriv]
  simp [hG, hy, Fin.cons_self_tail]

end SCV
