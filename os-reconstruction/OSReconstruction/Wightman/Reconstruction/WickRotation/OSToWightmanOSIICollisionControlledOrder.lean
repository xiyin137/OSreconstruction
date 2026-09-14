import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductNeighborhood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius

/-!
# Chronological reduction controlled by collision distance

The existing universal projection theorem gives one proper rotation and
ordering whose reduced time gaps stay uniformly above collision distance.
The reduced configuration has a dimension-only norm bound. No OS or
analytic-continuation premise is used here.
-/

noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

theorem exists_osiiCollisionControlledOrder (d k : Nat) [NeZero d] [NeZero k] :
    ∃ c : Real, 0 < c ∧ ∀ x : NPointDomain d (k + 1),
      x ∉ CoincidenceLocus d (k + 1) ->
      ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
        (sigma : Equiv.Perm (Fin (k + 1))),
        R.transpose * R = 1 ∧ R.det = 1 ∧
        let q := BHW.reducedDiffMapReal (k + 1) d (fun j => R.mulVec (x (sigma j)))
        section43QTime (d := d) (n := k) q ∈ section43TimeStrictPositiveRegion k ∧
        ‖q‖ ≤ (2 * (d + 1) : Real) * ‖x‖ ∧
        c * Metric.infDist x (CoincidenceLocus d (k + 1)) ≤
          osiiTimeBoundaryDistance k
            (osiiPositiveRealTimeEmbed (section43QTime (d := d) (n := k) q)) := by
  obtain ⟨c, hc, hprojection⟩ := exists_universal_time_projection' d (k + 1)
  refine ⟨c, hc, ?_⟩
  intro x hx
  obtain ⟨R, hR, hdet, hproj⟩ := hprojection x
  let t : Fin (k + 1) -> Real := fun j => (R.mulVec (x j)) 0
  have ht : Function.Injective t := by
    intro i j hij
    by_contra hne
    have hnorm : 0 < ‖x i - x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
      (fun h => hx ⟨i, j, hne, h⟩))
    have hb := hproj i j hne
    rw [Matrix.mulVec_sub] at hb
    change c * ‖x i - x j‖ ≤ |t i - t j| at hb
    rw [hij, sub_self, abs_zero] at hb
    exact (not_le_of_gt (mul_pos hc hnorm)) hb
  let sigma := Tuple.sort t
  have hs : StrictMono (fun j => t (sigma j)) := by
    intro i j hij
    exact lt_of_le_of_ne (Tuple.monotone_sort t hij.le)
      (ht.ne (sigma.injective.ne (ne_of_lt hij)))
  let y : NPointDomain d (k + 1) := fun j => R.mulVec (x (sigma j))
  let q : NPointDomain d k := BHW.reducedDiffMapReal (k + 1) d y
  have hq (j : Fin k) : q j = y j.succ - y j.castSucc := rfl
  have htime (j : Fin k) : q j 0 = t (sigma j.succ) - t (sigma j.castSucc) := rfl
  have hpositive (j : Fin k) : 0 < q j 0 := by
    rw [htime]
    exact sub_pos.mpr (hs Fin.castSucc_lt_succ)
  have hgap (j : Fin k) :
      c * Metric.infDist x (CoincidenceLocus d (k + 1)) ≤ q j 0 := by
    have hne : sigma j.succ ≠ sigma j.castSucc :=
      sigma.injective.ne (ne_of_gt Fin.castSucc_lt_succ)
    have hb := hproj (sigma j.succ) (sigma j.castSucc) hne
    rw [Matrix.mulVec_sub] at hb
    change c * ‖x (sigma j.succ) - x (sigma j.castSucc)‖ ≤ |q j 0| at hb
    rw [abs_of_pos (hpositive j)] at hb
    exact (mul_le_mul_of_nonneg_left
      (infDist_CoincidenceLocus_le_pairDifference x _ _ hne) hc.le).trans hb
  have hy : ‖y‖ ≤ (d + 1 : Real) * ‖x‖ := by
    have hrot := norm_matrix_mulVec_npoint_le_of_orthogonal R hR x
    apply le_trans ?_ hrot
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => R.mulVec (x j)))).2
    intro j
    exact norm_le_pi_norm (fun i => R.mulVec (x i)) (sigma j)
  refine ⟨R, sigma, hR, hdet, ?_, ?_, ?_⟩
  · exact hpositive
  · change ‖q‖ ≤ _
    have hnorm : ‖q‖ ≤ 2 * ‖y‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro j
      rw [hq]
      exact (norm_sub_le _ _).trans (by
        nlinarith [norm_le_pi_norm y j.succ, norm_le_pi_norm y j.castSucc])
    nlinarith
  · change c * Metric.infDist x (CoincidenceLocus d (k + 1)) ≤
      Metric.infDist (fun j => q j 0) (osiiTimePositiveCone k)ᶜ
    apply (Metric.le_infDist
      (osiiTimePositiveCone_compl_nonempty (Nat.pos_of_ne_zero (NeZero.ne k)))).2
    intro z hz
    have hz' : ∃ j, z j ≤ 0 := by
      simpa only [osiiTimePositiveCone, section43TimeStrictPositiveRegion,
        Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] using hz
    obtain ⟨j, hj⟩ := hz'
    calc
      c * Metric.infDist x (CoincidenceLocus d (k + 1)) ≤ q j 0 := hgap j
      _ ≤ q j 0 - z j := by linarith
      _ ≤ |q j 0 - z j| := le_abs_self _
      _ = dist (q j 0) (z j) := Real.dist_eq _ _ |>.symm
      _ ≤ dist (fun j => q j 0) z := dist_le_pi_dist (fun j : Fin k => q j 0) z j

end OSReconstruction
