/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase

/-!
# ACR(1) Euclidean Kernel Package

This file supplies the finite-dimensional real-section step used by the
OS-to-Wightman base continuation: an ACR(1) witness with permutation and
translation invariance has an a.e. measurable, polynomially bounded Euclidean
section.  The proof follows the standard OS/Jost sorting argument:

* almost every Euclidean configuration has distinct time coordinates;
* on each strict time-order chamber, a common positive time translation and the
  chamber permutation put the Wick-rotated configuration in `C_k^(1)`;
* permutation/translation invariance identifies the original section with that
  ACR(1) value;
* the finite chamber union has full measure, giving measurability and the
  polynomial pullback bound.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

variable {d k : ℕ} [NeZero d]

private theorem measure_timeEq_zero_kernel {d n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.volume {x : NPointDomain d n | x i 0 = x j 0} = 0 := by
  let L : NPointDomain d n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i 0 - x j 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp
        ring }
  have hset :
      {x : NPointDomain d n | x i 0 = x j 0} =
        (LinearMap.ker L : Set (NPointDomain d n)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have hji : j ≠ i := by
      intro h
      exact hij h.symm
    have : (1 : ℝ) = 0 := by
      simp [L, hji] at hval
    norm_num at this
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L)
    hker_ne_top

private theorem ae_pairwise_distinct_timeCoords_kernel {d n : ℕ} :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0 := by
  have hall : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, x p.1.1 0 ≠ x p.1.2 0 := by
    simpa using
      ((Set.toFinite (Set.univ : Set {p : Fin n × Fin n // p.1 ≠ p.2})).eventually_all
        (l := MeasureTheory.ae
          (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
        (p := fun p => fun x : NPointDomain d n => x p.1.1 0 ≠ x p.1.2 0)).2
        (fun p _ => by
          let s : Set (NPointDomain d n) := {x | x p.1.1 0 = x p.1.2 0}
          have hs0 : MeasureTheory.volume s = 0 := by
            simpa [s] using measure_timeEq_zero_kernel (d := d) p.1.1 p.1.2 p.2
          have hsae :
              sᶜ ∈ MeasureTheory.ae
                (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
            MeasureTheory.compl_mem_ae_iff.mpr hs0
          simpa [s, Set.compl_setOf] using hsae)
  filter_upwards [hall] with x hx i j hij
  exact hx ⟨⟨i, j⟩, hij⟩

private def timeOrderChamber (k d : ℕ) (σ : Equiv.Perm (Fin k)) :
    Set (NPointDomain d k) :=
  {x | ∀ i j : Fin k, i < j → x (σ i) 0 < x (σ j) 0}

private theorem isOpen_timeOrderChamber (σ : Equiv.Perm (Fin k)) :
    IsOpen (timeOrderChamber k d σ) := by
  simp only [timeOrderChamber, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i < j
  · have hconti : Continuous fun x : NPointDomain d k => x (σ i) 0 :=
      (continuous_apply 0).comp (continuous_apply (σ i))
    have hcontj : Continuous fun x : NPointDomain d k => x (σ j) 0 :=
      (continuous_apply 0).comp (continuous_apply (σ j))
    simpa [hij] using isOpen_lt hconti hcontj
  · simp [hij]

private theorem exists_timeOrderChamber_of_pairwise_distinct
    (x : NPointDomain d k)
    (hdistinct : ∀ i j : Fin k, i ≠ j → x i 0 ≠ x j 0) :
    ∃ σ : Equiv.Perm (Fin k), x ∈ timeOrderChamber k d σ := by
  let σ := Tuple.sort (fun i : Fin k => x i 0)
  have hmono := Tuple.monotone_sort (fun i : Fin k => x i 0)
  have hinj : Function.Injective (fun i : Fin k => x i 0) := by
    intro i j h
    by_contra hij
    exact hdistinct i j hij h
  have hstrict : StrictMono ((fun i : Fin k => x i 0) ∘ σ) :=
    hmono.strictMono_of_injective (hinj.comp σ.injective)
  refine ⟨σ, ?_⟩
  intro i j hij
  exact hstrict hij

private theorem ae_mem_iUnion_timeOrderChamber :
    ∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume,
      x ∈ ⋃ σ : Equiv.Perm (Fin k), timeOrderChamber k d σ := by
  filter_upwards [ae_pairwise_distinct_timeCoords_kernel (d := d) (n := k)] with x hdistinct
  rcases exists_timeOrderChamber_of_pairwise_distinct (d := d) (k := k) x hdistinct with
    ⟨σ, hσ⟩
  exact Set.mem_iUnion.mpr ⟨σ, hσ⟩

private def timeShiftAmount (k d : ℕ) (x : NPointDomain d k) : ℝ :=
  1 + ∑ i : Fin k, |x i 0|

private def timeShiftConfig (k d : ℕ) (x : NPointDomain d k) : NPointDomain d k :=
  fun i μ => x i μ + if μ = 0 then timeShiftAmount k d x else 0

private def shiftedSortedWick (σ : Equiv.Perm (Fin k))
    (x : NPointDomain d k) : Fin k → Fin (d + 1) → ℂ :=
  fun i => wickRotatePoint (timeShiftConfig k d x (σ i))

private theorem continuous_timeShiftAmount :
    Continuous (timeShiftAmount k d : NPointDomain d k → ℝ) := by
  refine continuous_const.add ?_
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  exact continuous_abs.comp ((continuous_apply 0).comp (continuous_apply i))

private theorem continuous_timeShiftConfig :
    Continuous (timeShiftConfig k d : NPointDomain d k → NPointDomain d k) := by
  refine continuous_pi fun i => continuous_pi fun μ => ?_
  refine Continuous.add ((continuous_apply μ).comp (continuous_apply i)) ?_
  by_cases hμ : μ = 0
  · simpa [timeShiftConfig, hμ] using continuous_timeShiftAmount (k := k) (d := d)
  · simpa [timeShiftConfig, hμ] using
      (continuous_const : Continuous fun _ : NPointDomain d k => (0 : ℝ))

private theorem continuous_shiftedSortedWick (σ : Equiv.Perm (Fin k)) :
    Continuous (shiftedSortedWick (d := d) σ) := by
  refine continuous_pi fun i => continuous_pi fun μ => ?_
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord : Continuous fun x : NPointDomain d k =>
        timeShiftConfig k d x (σ i) 0 :=
      (continuous_apply 0).comp
        ((continuous_apply (σ i)).comp (continuous_timeShiftConfig (k := k) (d := d)))
    simpa [shiftedSortedWick, wickRotatePoint] using
      continuous_const.mul (Complex.continuous_ofReal.comp hcoord)
  · have hcoord : Continuous fun x : NPointDomain d k =>
        timeShiftConfig k d x (σ i) μ :=
      (continuous_apply μ).comp
        ((continuous_apply (σ i)).comp (continuous_timeShiftConfig (k := k) (d := d)))
    simpa [shiftedSortedWick, wickRotatePoint, hμ] using
      Complex.continuous_ofReal.comp hcoord

private theorem timeShiftConfig_time_pos (x : NPointDomain d k) (i : Fin k) :
    0 < timeShiftConfig k d x i 0 := by
  have hi_le : |x i 0| ≤ ∑ j : Fin k, |x j 0| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j 0)) (Finset.mem_univ i)
  have hneg : -|x i 0| ≤ x i 0 := neg_abs_le (x i 0)
  dsimp [timeShiftConfig, timeShiftAmount]
  linarith

private theorem shiftedSortedWick_mem_acr_one
    (σ : Equiv.Perm (Fin k)) {x : NPointDomain d k}
    (hx : x ∈ timeOrderChamber k d σ) :
    shiftedSortedWick (d := d) σ x ∈ AnalyticContinuationRegion d k 1 := by
  rw [AnalyticContinuationRegion]
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  subst hμ0
  by_cases hi : i.val = 0
  · have hpos := timeShiftConfig_time_pos (d := d) (k := k) x (σ i)
    simpa [shiftedSortedWick, wickRotatePoint, hi, timeShiftConfig] using hpos
  · let ipred : Fin k := ⟨i.val - 1, by omega⟩
    have hlt : ipred < i := by
      change i.val - 1 < i.val
      omega
    have hord := hx ipred i hlt
    have hdiff :
        0 < timeShiftConfig k d x (σ i) 0 - timeShiftConfig k d x (σ ipred) 0 := by
      simp [timeShiftConfig]
      exact hord
    simpa [shiftedSortedWick, wickRotatePoint, hi, ipred, Complex.sub_im] using hdiff

private theorem rawWick_eq_shiftedSortedWick_value
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z)
    (σ : Equiv.Perm (Fin k)) (x : NPointDomain d k) :
    S_prod (fun i => wickRotatePoint (x i)) =
      S_prod (shiftedSortedWick (d := d) σ x) := by
  let z : Fin k → Fin (d + 1) → ℂ := fun i => wickRotatePoint (x i)
  let a : Fin (d + 1) → ℂ :=
    wickRotatePoint (fun μ => if μ = 0 then timeShiftAmount k d x else 0)
  have hperm : S_prod (fun i => z (σ i)) = S_prod z := hS_prod_perm σ z
  have hshift_fun :
      shiftedSortedWick (d := d) σ x = fun i μ => z (σ i) μ + a μ := by
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [shiftedSortedWick, z, a, timeShiftConfig, wickRotatePoint]
      ring
    · simp [shiftedSortedWick, z, a, timeShiftConfig, wickRotatePoint, hμ]
  have htrans :
      S_prod (shiftedSortedWick (d := d) σ x) = S_prod (fun i => z (σ i)) := by
    rw [hshift_fun]
    exact hS_prod_trans (fun i => z (σ i)) a
  rw [htrans, hperm]

private theorem rawWickKernel_continuousOn_timeOrderUnion
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_holo : DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1))
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) :
    ContinuousOn
      (fun x : NPointDomain d k => S_prod (fun i => wickRotatePoint (x i)))
      (⋃ σ : Equiv.Perm (Fin k), timeOrderChamber k d σ) := by
  refine ContinuousOn.iUnion_of_isOpen ?_ ?_
  · intro σ
    have hshift_cont : ContinuousOn
        (fun x : NPointDomain d k => S_prod (shiftedSortedWick (d := d) σ x))
        (timeOrderChamber k d σ) := by
      refine hS_prod_holo.continuousOn.comp
        (continuous_shiftedSortedWick (d := d) (k := k) σ).continuousOn ?_
      intro x hx
      exact shiftedSortedWick_mem_acr_one (d := d) (k := k) σ hx
    refine hshift_cont.congr ?_
    intro x hx
    exact rawWick_eq_shiftedSortedWick_value (d := d) (k := k)
      S_prod hS_prod_perm hS_prod_trans σ x
  · intro σ
    exact isOpen_timeOrderChamber (d := d) (k := k) σ

private theorem rawWickKernel_aestronglyMeasurable
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_holo : DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1))
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d k => S_prod (fun i => wickRotatePoint (x i)))
      MeasureTheory.volume := by
  let S : Set (NPointDomain d k) := ⋃ σ : Equiv.Perm (Fin k), timeOrderChamber k d σ
  have hS_open : IsOpen S := isOpen_iUnion fun σ =>
    isOpen_timeOrderChamber (d := d) (k := k) σ
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  have hcont : ContinuousOn
      (fun x : NPointDomain d k => S_prod (fun i => wickRotatePoint (x i))) S :=
    rawWickKernel_continuousOn_timeOrderUnion (d := d) (k := k)
      S_prod hS_prod_holo hS_prod_perm hS_prod_trans
  have hrestr : MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d k => S_prod (fun i => wickRotatePoint (x i)))
      (MeasureTheory.volume.restrict S) :=
    hcont.aestronglyMeasurable hS_meas
  have hS_ae : ∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume, x ∈ S :=
    ae_mem_iUnion_timeOrderChamber (d := d) (k := k)
  have hrestr_eq : MeasureTheory.volume.restrict S =
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d k)) :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem hS_ae
  rwa [hrestr_eq] at hrestr

private theorem timeShiftAmount_pos (x : NPointDomain d k) :
    0 < timeShiftAmount k d x := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, |x i 0| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  dsimp [timeShiftAmount]
  linarith

private theorem timeShiftAmount_le_norm (x : NPointDomain d k) :
    timeShiftAmount k d x ≤ 1 + (k : ℝ) * ‖x‖ := by
  have hsum_le : (∑ i : Fin k, |x i 0|) ≤ ∑ i : Fin k, ‖x‖ := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hcoord : ‖x i 0‖ ≤ ‖x‖ :=
      (norm_le_pi_norm (x i) 0).trans (norm_le_pi_norm x i)
    simpa [Real.norm_eq_abs] using hcoord
  have hsum_const : (∑ _i : Fin k, ‖x‖) = (k : ℝ) * ‖x‖ := by
    simp
  dsimp [timeShiftAmount]
  rw [hsum_const] at hsum_le
  linarith

private theorem norm_timeShiftConfig_component_le
    (x : NPointDomain d k) (i : Fin k) (μ : Fin (d + 1)) :
    ‖timeShiftConfig k d x i μ‖ ≤ 1 + ((k : ℝ) + 1) * ‖x‖ := by
  have hcoord : ‖x i μ‖ ≤ ‖x‖ :=
    (norm_le_pi_norm (x i) μ).trans (norm_le_pi_norm x i)
  have hApos : 0 < timeShiftAmount k d x := timeShiftAmount_pos (d := d) (k := k) x
  have hAle : timeShiftAmount k d x ≤ 1 + (k : ℝ) * ‖x‖ :=
    timeShiftAmount_le_norm (d := d) (k := k) x
  by_cases hμ : μ = 0
  · subst hμ
    have hadd := norm_add_le (x i 0) (timeShiftAmount k d x)
    have hAnorm : ‖timeShiftAmount k d x‖ = timeShiftAmount k d x :=
      Real.norm_of_nonneg (le_of_lt hApos)
    dsimp [timeShiftConfig]
    calc
      ‖x i 0 + timeShiftAmount k d x‖
          ≤ ‖x i 0‖ + ‖timeShiftAmount k d x‖ := hadd
      _ = ‖x i 0‖ + timeShiftAmount k d x := by rw [hAnorm]
      _ ≤ ‖x‖ + (1 + (k : ℝ) * ‖x‖) := add_le_add hcoord hAle
      _ = 1 + ((k : ℝ) + 1) * ‖x‖ := by ring
  · dsimp [timeShiftConfig]
    rw [if_neg hμ, add_zero]
    have hnonneg : 0 ≤ (k : ℝ) * ‖x‖ :=
      mul_nonneg (Nat.cast_nonneg k) (norm_nonneg x)
    calc
      |x i μ| = ‖x i μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ := hcoord
      _ ≤ 1 + ((k : ℝ) + 1) * ‖x‖ := by nlinarith [norm_nonneg x, hnonneg]

private theorem norm_timeShiftConfig_perm_le
    (σ : Equiv.Perm (Fin k)) (x : NPointDomain d k) :
    ‖(fun i : Fin k => timeShiftConfig k d x (σ i))‖ ≤
      ((k : ℝ) + 2) * (1 + ‖x‖) := by
  let B : ℝ := 1 + ((k : ℝ) + 1) * ‖x‖
  have hB_nonneg : 0 ≤ B := by
    have : 0 ≤ ((k : ℝ) + 1) * ‖x‖ :=
      mul_nonneg (by positivity) (norm_nonneg x)
    dsimp [B]
    linarith
  have h_inner : ∀ i : Fin k, ‖timeShiftConfig k d x (σ i)‖ ≤ B := by
    intro i
    rw [Pi.norm_def]
    change ↑(Finset.univ.sup fun μ => ‖timeShiftConfig k d x (σ i) μ‖₊) ≤ B
    exact_mod_cast (Finset.sup_le (s := Finset.univ)
      (f := fun μ => ‖timeShiftConfig k d x (σ i) μ‖₊)
      (a := (⟨B, hB_nonneg⟩ : NNReal)) (by
        intro μ hμ
        have hcomp := norm_timeShiftConfig_component_le (d := d) (k := k) x (σ i) μ
        dsimp [B]
        exact_mod_cast hcomp))
  have houter : ‖(fun i : Fin k => timeShiftConfig k d x (σ i))‖ ≤ B := by
    rw [Pi.norm_def]
    change ↑(Finset.univ.sup fun i =>
      ‖(fun μ : Fin (d + 1) => timeShiftConfig k d x (σ i) μ)‖₊) ≤ B
    exact_mod_cast (Finset.sup_le (s := Finset.univ)
      (f := fun i => ‖(fun μ : Fin (d + 1) => timeShiftConfig k d x (σ i) μ)‖₊)
      (a := (⟨B, hB_nonneg⟩ : NNReal)) (by
        intro i hi
        have hi' := h_inner i
        exact_mod_cast hi'))
  calc
    ‖(fun i : Fin k => timeShiftConfig k d x (σ i))‖
        ≤ B := houter
    _ ≤ ((k : ℝ) + 2) * (1 + ‖x‖) := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hx : 0 ≤ ‖x‖ := norm_nonneg x
      dsimp [B]
      nlinarith

private theorem norm_shiftedSortedWick_le
    (σ : Equiv.Perm (Fin k)) (x : NPointDomain d k) :
    ‖shiftedSortedWick (d := d) σ x‖ ≤ ((k : ℝ) + 2) * (1 + ‖x‖) := by
  calc
    ‖shiftedSortedWick (d := d) σ x‖
        = ‖fun i : Fin k => wickRotatePoint (timeShiftConfig k d x (σ i))‖ := rfl
    _ ≤ ‖(fun i : Fin k => timeShiftConfig k d x (σ i))‖ :=
      wickRotate_norm_le (d := d) (n := k) (fun i => timeShiftConfig k d x (σ i))
    _ ≤ ((k : ℝ) + 2) * (1 + ‖x‖) :=
      norm_timeShiftConfig_perm_le (d := d) (k := k) σ x

private theorem rawWickKernel_polynomial_bound
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z)
    (C0 : ℝ) (N0 : ℕ) (hC0 : 0 < C0)
    (hS_prod_growth :
      ∀ z ∈ AnalyticContinuationRegion d k 1,
        ‖S_prod z‖ ≤ C0 * (1 + ‖z‖) ^ N0) :
    ∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume,
      ‖S_prod (fun i => wickRotatePoint (x i))‖ ≤
        (C0 * (((k : ℝ) + 3) ^ N0)) * (1 + ‖x‖) ^ N0 := by
  filter_upwards [ae_mem_iUnion_timeOrderChamber (d := d) (k := k)] with x hx
  rcases Set.mem_iUnion.mp hx with ⟨σ, hσ⟩
  have heq := rawWick_eq_shiftedSortedWick_value (d := d) (k := k)
    S_prod hS_prod_perm hS_prod_trans σ x
  rw [heq]
  have hmem : shiftedSortedWick (d := d) σ x ∈ AnalyticContinuationRegion d k 1 :=
    shiftedSortedWick_mem_acr_one (d := d) (k := k) σ hσ
  have hgrowth := hS_prod_growth (shiftedSortedWick (d := d) σ x) hmem
  have hnorm := norm_shiftedSortedWick_le (d := d) (k := k) σ x
  have hbase : 1 + ‖shiftedSortedWick (d := d) σ x‖ ≤
      ((k : ℝ) + 3) * (1 + ‖x‖) := by
    calc
      1 + ‖shiftedSortedWick (d := d) σ x‖
          ≤ 1 + ((k : ℝ) + 2) * (1 + ‖x‖) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hnorm 1
      _ ≤ ((k : ℝ) + 3) * (1 + ‖x‖) := by
        have hxnorm : 0 ≤ ‖x‖ := norm_nonneg x
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
  have hpow : (1 + ‖shiftedSortedWick (d := d) σ x‖) ^ N0 ≤
      (((k : ℝ) + 3) * (1 + ‖x‖)) ^ N0 := by
    exact pow_le_pow_left₀ (by positivity) hbase N0
  calc
    ‖S_prod (shiftedSortedWick (d := d) σ x)‖
        ≤ C0 * (1 + ‖shiftedSortedWick (d := d) σ x‖) ^ N0 := hgrowth
    _ ≤ C0 * ((((k : ℝ) + 3) * (1 + ‖x‖)) ^ N0) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt hC0)
    _ = (C0 * (((k : ℝ) + 3) ^ N0)) * (1 + ‖x‖) ^ N0 := by
      rw [mul_pow]
      ring

/-- The Euclidean real section of an ACR(1) witness is a.e. measurable and
polynomially bounded, after using the standard finite time-order chamber
sorting and common positive time-translation argument. -/
theorem acrOne_productTensor_witness_euclidKernelPackage_from_acrGrowth
    {d : ℕ} [NeZero d]
    (k : ℕ)
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_holo : DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1))
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z)
    (hS_prod_growth :
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      MeasureTheory.AEStronglyMeasurable
        (fun x : NPointDomain d k => S_prod (fun j => wickRotatePoint (x j)))
        MeasureTheory.volume ∧
      (∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume,
        ‖S_prod (fun j => wickRotatePoint (x j))‖ ≤ C_bd * (1 + ‖x‖) ^ N) := by
  rcases hS_prod_growth with ⟨C0, N0, hC0, hgrowth⟩
  refine ⟨C0 * (((k : ℝ) + 3) ^ N0), N0, ?_, ?_, ?_⟩
  · exact mul_pos hC0 (pow_pos (by positivity) N0)
  · exact rawWickKernel_aestronglyMeasurable (d := d) (k := k)
      S_prod hS_prod_holo hS_prod_perm hS_prod_trans
  · exact rawWickKernel_polynomial_bound (d := d) (k := k)
      S_prod hS_prod_perm hS_prod_trans C0 N0 hC0 hgrowth

