/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv










open scoped Topology

noncomputable section

namespace OSReconstruction.SchwartzFlatness

/-- A smooth map that is flat on a nonempty closed set is bounded by a power of
the distance to that set, provided its next derivative is uniformly bounded. -/
theorem norm_le_infDist_pow_of_flat_on_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS_closed : IsClosed S) (hS_nonempty : S.Nonempty)
    {f : E → F}
    (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hflat : ∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k f y = 0)
    (m : ℕ) {A : ℝ} (hA_nonneg : 0 ≤ A)
    (hA : ∀ x : E, ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ A) :
    ∀ x : E, ‖f x‖ ≤
      (A / (Nat.factorial m : ℝ)) * Metric.infDist x S ^ (m + 1) := by
  intro x
  obtain ⟨y, hyS, hyDist⟩ := hS_closed.exists_infDist_eq_dist hS_nonempty x
  let v : E := x - y
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → F := (fun z : E => f (z + y)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : E => f (z + y)) :=
    fun r => by
      simpa using (hf_smooth.of_le (by exact_mod_cast le_top)).comp
        (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using
      (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : E => f (z + y))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : E => f (z + y))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k f (L 0 + y) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hflat k y hyS
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          A * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hL : ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simp [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul,
        mul_comm]
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : E => f (z + y))
            (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : E => f (z + y))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) f (L t + y)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) f (L t + y)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ A * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
          exact hA (L t + y)
      _ = A * ‖L‖ ^ (m + 1) := by simp
      _ ≤ A * ‖v‖ ^ (m + 1) := by gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := A * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hg_one : g 1 = f x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg,
      add_comm, add_left_comm]
  have hv_dist : ‖v‖ = Metric.infDist x S := by
    rw [hyDist, dist_eq_norm]
  calc
    ‖f x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ (A * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (Nat.factorial m : ℝ) := by
      simpa [hTaylor_zero] using hrem
    _ = (A / (Nat.factorial m : ℝ)) * ‖v‖ ^ (m + 1) := by
      field_simp [Nat.cast_ne_zero]
      ring
    _ = (A / (Nat.factorial m : ℝ)) *
          Metric.infDist x S ^ (m + 1) := by
      rw [hv_dist]

end OSReconstruction.SchwartzFlatness
