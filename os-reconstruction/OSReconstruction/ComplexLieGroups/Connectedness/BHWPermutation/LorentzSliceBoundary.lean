/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.DimensionZero
import Mathlib.Analysis.LocallyConvex.Separation



















noncomputable section

open Matrix LorentzLieGroup Set

namespace BHW.SliceGeometry

variable {d : ℕ}

private theorem separator_of_range_avoids_forward
    (M : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ))
    (h : ∀ v, ¬ InOpenForwardCone d (M v)) :
    ∃ f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ,
      (∀ v, f (M v) = 0) ∧ (∀ y, InOpenForwardCone d y → 0 < f y) := by
  have hdis : Disjoint {y | InOpenForwardCone d y} (LinearMap.range M : Set _) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨v, rfl⟩
    exact h v hy
  have hopen : IsOpen {y | InOpenForwardCone d y} := by
    have hq : Continuous (fun y : Fin (d + 1) → ℝ =>
        ∑ i, minkowskiSignature d i * y i ^ 2) := by fun_prop
    exact (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt hq continuous_const)
  obtain ⟨f, u, hcone, hrange⟩ := geometric_hahn_banach_open
    inOpenForwardCone_convex hopen (LinearMap.range M).convex hdis
  have hzero : ∀ v, f (M v) = 0 := by
    intro v
    by_contra hv
    have hbad := hrange (M (((u - 1) / f (M v)) • v)) ⟨_, rfl⟩
    simp only [map_smul, smul_eq_mul] at hbad
    rw [div_mul_cancel₀ _ hv] at hbad
    linarith
  refine ⟨-f, ?_, ?_⟩
  · intro v
    simp [hzero]
  · intro y hy
    have hu := hrange 0 (LinearMap.range M).zero_mem
    simp only [map_zero] at hu
    have hc := hcone y hy
    change 0 < -f y
    linarith

private def dot (p y : Fin (d + 1) → ℝ) : ℝ := ∑ i, p i * y i

private theorem dual_forward_coordinates (p : Fin (d + 1) → ℝ)
    (h : ∀ y, InOpenForwardCone d y → 0 < dot p y) :
    0 < p 0 ∧ (∑ i : Fin d, p i.succ ^ 2) ≤ p 0 ^ 2 := by
  have hp : 0 < p 0 := by
    have he : InOpenForwardCone d (Fin.cons 1 (fun _ : Fin d => 0)) := by
      constructor
      · norm_num
      · rw [minkowski_sum_decomp]
        norm_num
    simpa [dot, Fin.sum_univ_succ] using h _ he
  refine ⟨hp, ?_⟩
  by_contra hnot
  have hs : p 0 ^ 2 < ∑ i : Fin d, p i.succ ^ 2 := lt_of_not_ge hnot
  let S : ℝ := ∑ i : Fin d, p i.succ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let y : Fin (d + 1) → ℝ := Fin.cons (S + p 0 ^ 2) (fun i => -2 * p 0 * p i.succ)
  have hsum : (∑ i : Fin d, y i.succ ^ 2) = 4 * p 0 ^ 2 * S := by
    dsimp [y, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.cons_succ]
    ring
  have hy : InOpenForwardCone d y := by
    constructor
    · change 0 < S + p 0 ^ 2
      positivity
    · rw [minkowski_sum_decomp, hsum]
      change -(S + p 0 ^ 2) ^ 2 + 4 * p 0 ^ 2 * S < 0
      have hs' : p 0 ^ 2 < S := hs
      nlinarith [sq_pos_of_pos (sub_pos.mpr hs')]
  have hdot : dot p y = p 0 * (p 0 ^ 2 - S) := by
    rw [dot, Fin.sum_univ_succ]
    change p 0 * (S + p 0 ^ 2) +
      (∑ i : Fin d, p i.succ * (-2 * p 0 * p i.succ)) = _
    have hsum' : (∑ i : Fin d, p i.succ * (-2 * p 0 * p i.succ)) = -2 * p 0 * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum']
    ring
  have hpos := h y hy
  rw [hdot] at hpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr hs.le))) hpos

private theorem dot_pos_of_coordinates (p y : Fin (d + 1) → ℝ)
    (hp0 : 0 < p 0) (hp : (∑ i : Fin d, p i.succ ^ 2) ≤ p 0 ^ 2)
    (hy : InOpenForwardCone d y) : 0 < dot p y := by
  have hyq : (∑ i : Fin d, y i.succ ^ 2) < y 0 ^ 2 := by
    have h := hy.2
    rw [minkowski_sum_decomp] at h
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin d => p i.succ) (fun i : Fin d => y i.succ)
  have hlt : (∑ i : Fin d, p i.succ * y i.succ) ^ 2 < (p 0 * y 0) ^ 2 := by
    calc
      _ ≤ (∑ i : Fin d, p i.succ ^ 2) * (∑ i : Fin d, y i.succ ^ 2) := hcs
      _ ≤ p 0 ^ 2 * (∑ i : Fin d, y i.succ ^ 2) :=
        mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ < p 0 ^ 2 * y 0 ^ 2 := mul_lt_mul_of_pos_left hyq (sq_pos_of_pos hp0)
      _ = _ := by ring
  have habs := abs_lt_of_sq_lt_sq hlt (mul_pos hp0 hy.1).le
  rw [dot, Fin.sum_univ_succ]
  linarith [neg_abs_le (∑ i : Fin d, p i.succ * y i.succ)]

private theorem dot_nonpos_of_nonpos_time (p y : Fin (d + 1) → ℝ)
    (hp0 : p 0 ≤ 0) (hp : (∑ i : Fin d, p i.succ ^ 2) ≤ p 0 ^ 2)
    (hy : InOpenForwardCone d y) : dot p y ≤ 0 := by
  have hyq : (∑ i : Fin d, y i.succ ^ 2) ≤ y 0 ^ 2 := by
    have h := hy.2
    rw [minkowski_sum_decomp] at h
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin d => p i.succ) (fun i : Fin d => y i.succ)
  have hle : (∑ i : Fin d, p i.succ * y i.succ) ^ 2 ≤ (-p 0 * y 0) ^ 2 := by
    calc
      _ ≤ (∑ i : Fin d, p i.succ ^ 2) * (∑ i : Fin d, y i.succ ^ 2) := hcs
      _ ≤ p 0 ^ 2 * y 0 ^ 2 := mul_le_mul hp hyq
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hupper := (abs_le_of_sq_le_sq' hle (mul_nonneg (neg_nonneg.mpr hp0) hy.1.le)).2
  rw [dot, Fin.sum_univ_succ]
  linarith

private theorem linear_eq_dot (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (y : Fin (d + 1) → ℝ) :
    f y = dot (fun i => f (Pi.single i 1)) y := by
  have hvec : (∑ i : Fin (d + 1), y i •
      (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)) = y := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [← hvec, map_sum]
  simp [dot, map_smul, smul_eq_mul, mul_comm]

private def transposeLorentz (L : ComplexLorentzGroup d) : ComplexLorentzGroup d where
  val := L.val.transpose
  metric_preserving := by
    apply ComplexLorentzGroup.of_metric_preserving_matrix
    simp only [Matrix.transpose_transpose]
    have hleft : (ComplexLorentzGroup.ηℂ * L.val.transpose * ComplexLorentzGroup.ηℂ) *
        L.val = 1 := by
      calc
        _ = ComplexLorentzGroup.ηℂ *
            (L.val.transpose * ComplexLorentzGroup.ηℂ * L.val) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [ComplexLorentzGroup.metric_preserving_matrix, ComplexLorentzGroup.ηℂ_sq]
    have hright := mul_eq_one_comm.mpr hleft
    have hmul := congrArg (fun M => M * ComplexLorentzGroup.ηℂ) hright
    simpa only [Matrix.mul_assoc, ComplexLorentzGroup.ηℂ_sq, Matrix.mul_one,
      Matrix.one_mul] using hmul
  proper := by rw [Matrix.det_transpose, L.proper]

private def dotCLM (p : Fin (d + 1) → ℝ) : (Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

@[simp] private theorem dotCLM_apply (p y : Fin (d + 1) → ℝ) : dotCLM p y = dot p y := by
  simp [dotCLM, dot, ContinuousLinearMap.sum_apply]

private theorem forward_functional_strictMono {n : ℕ}
    (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ y, InOpenForwardCone d y → 0 < f y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    StrictMono (fun k => f (fun μ => (z k μ).im)) := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have h := hf _ (hz i.succ)
    have heq : imDiff z i.succ = (fun μ => (z i.succ μ).im) -
        (fun μ => (z i.castSucc μ).im) := by
      ext μ
      simp [imDiff, Complex.sub_im]
      rfl
    change 0 < f (imDiff z i.succ) at h
    rw [heq, map_sub] at h
    exact sub_pos.mp h

private theorem forward_functional_pos {n : ℕ}
    (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ y, InOpenForwardCone d y → 0 < f y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) (k : Fin n) :
    0 < f (fun μ => (z k μ).im) := by
  cases n with
  | zero => exact k.elim0
  | succ m =>
    have h0 : 0 < f (fun μ => (z 0 μ).im) := by
      simpa [ForwardTube] using hf _ (hz 0)
    exact h0.trans_le ((forward_functional_strictMono f hf z hz).monotone (Fin.zero_le k))

private theorem complex_quadratic_preserved [NeZero d] (L : ComplexLorentzGroup d)
    (z : Fin (d + 1) → ℂ) :
    (∑ μ, (minkowskiSignature d μ : ℂ) * (complexLorentzVectorAction L z μ) ^ 2) =
      ∑ μ, (minkowskiSignature d μ : ℂ) * z μ ^ 2 := by
  have hL : ∀ μ ν, ∑ a : Fin (d + 1),
      (MinkowskiSpace.metricSignature d a : ℂ) * L.val a μ * L.val a ν =
      if μ = ν then (MinkowskiSpace.metricSignature d μ : ℂ) else 0 := by
    intro μ ν
    simpa [MinkowskiSpace.metricSignature, minkowskiSignature] using L.metric_preserving μ ν
  simpa [MinkowskiSpace.complexMinkowskiQuadratic, MinkowskiSpace.metricSignature,
    minkowskiSignature, complexLorentzVectorAction] using
    MinkowskiSpace.complexQuadratic_lorentz_invariant d L.val hL z

def imaginaryPart (L : ComplexLorentzGroup d) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  Matrix.toLin' (fun i j => (L.val i j).im)

private def realPart (L : ComplexLorentzGroup d) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  Matrix.toLin' (fun i j => (L.val i j).re)

private def pullback (L : ComplexLorentzGroup d) (p : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun j => ∑ i, p i * (L.val i j).re

private theorem transpose_action_real_of_annihilates_imaginary
    (L : ComplexLorentzGroup d) (p : Fin (d + 1) → ℝ)
    (h : ∀ v, dot p (imaginaryPart L v) = 0) :
    complexLorentzVectorAction (transposeLorentz L) (fun i => (p i : ℂ)) =
      fun i => (pullback L p i : ℂ) := by
  have hcol : ∀ j, (∑ i, p i * (L.val i j).im) = 0 := by
    intro j
    have hv := h (Pi.single j (1 : ℝ))
    change (∑ i, p i * ∑ k, (L.val i k).im *
      ((Pi.single j (1 : ℝ)) : Fin (d + 1) → ℝ) k) = 0 at hv
    simpa [Pi.single_apply] using hv
  ext j
  apply Complex.ext
  · simp [complexLorentzVectorAction, transposeLorentz, pullback, Complex.mul_re,
      mul_comm]
  · simpa [complexLorentzVectorAction, transposeLorentz, Complex.mul_im,
      mul_comm] using hcol j

private theorem pullback_causal [NeZero d] (L : ComplexLorentzGroup d)
    (p : Fin (d + 1) → ℝ)
    (hp : (∑ i : Fin d, p i.succ ^ 2) ≤ p 0 ^ 2)
    (h : ∀ v, dot p (imaginaryPart L v) = 0) :
    (∑ i : Fin d, pullback L p i.succ ^ 2) ≤ pullback L p 0 ^ 2 := by
  have hquad := complex_quadratic_preserved (transposeLorentz L) (fun i => (p i : ℂ))
  rw [transpose_action_real_of_annihilates_imaginary L p h] at hquad
  dsimp only at hquad
  have hreal : (∑ i, minkowskiSignature d i * pullback L p i ^ 2) =
      ∑ i, minkowskiSignature d i * p i ^ 2 := by exact_mod_cast hquad
  rw [minkowski_sum_decomp, minkowski_sum_decomp] at hreal
  linarith

private theorem dot_realPart (L : ComplexLorentzGroup d) (p y : Fin (d + 1) → ℝ) :
    dot p (realPart L y) = dot (pullback L p) y := by
  change (∑ i, p i * ∑ j, (L.val i j).re * y j) =
    ∑ j, (∑ i, p i * (L.val i j).re) * y j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dot_action_imaginary (L : ComplexLorentzGroup d) (p : Fin (d + 1) → ℝ)
    (h : ∀ v, dot p (imaginaryPart L v) = 0) (z : Fin (d + 1) → ℂ) :
    dot p (fun i => (complexLorentzVectorAction L z i).im) =
      dot (pullback L p) (fun i => (z i).im) := by
  have heq : (fun i => (complexLorentzVectorAction L z i).im) =
      realPart L (fun i => (z i).im) + imaginaryPart L (fun i => (z i).re) := by
    ext i
    change (∑ x, L.val i x * z x).im =
      (∑ x, (L.val i x).re * (z x).im) + ∑ x, (L.val i x).im * (z x).re
    simp [Complex.mul_im, Finset.sum_add_distrib]
  rw [heq, ← dotCLM_apply, map_add, dotCLM_apply, dotCLM_apply, h, add_zero]
  exact dot_realPart L p _

private theorem forward_functional_nonpos {n : ℕ}
    (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ y, InOpenForwardCone d y → f y ≤ 0)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) (k : Fin n) :
    f (fun μ => (z k μ).im) ≤ 0 := by
  cases n with
  | zero => exact k.elim0
  | succ m =>
    induction k using Fin.induction with
    | zero => simpa [ForwardTube] using hf _ (hz 0)
    | succ i ih =>
      have h := hf _ (hz i.succ)
      have heq : imDiff z i.succ = (fun μ => (z i.succ μ).im) -
          (fun μ => (z i.castSucc μ).im) := by
        ext μ
        simp [imDiff, Complex.sub_im]
        rfl
      change f (imDiff z i.succ) ≤ 0 at h
      rw [heq, map_sub] at h
      linarith

theorem exists_imaginary_forward_of_perm_overlap [NeZero d] {n : ℕ}
    (L : ComplexLorentzGroup d) (s : Equiv.Perm (Fin n)) (hs : s ≠ 1)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    (hLz : complexLorentzAction L (permAct s z) ∈ ForwardTube d n) :
    ∃ v : Fin (d + 1) → ℝ, InOpenForwardCone d (imaginaryPart L v) := by
  cases n with
  | zero => exact (hs (Subsingleton.elim _ _)).elim
  | succ m =>
    by_contra hnone
    push Not at hnone
    obtain ⟨f, hvan, hpos⟩ := separator_of_range_avoids_forward (imaginaryPart L) hnone
    let p : Fin (d + 1) → ℝ := fun i => f (Pi.single i 1)
    have hp : ∀ y, InOpenForwardCone d y → 0 < dot p y := by
      intro y hy
      rw [← linear_eq_dot f y]
      exact hpos y hy
    have hzero : ∀ v, dot p (imaginaryPart L v) = 0 := by
      intro v
      rw [← linear_eq_dot f (imaginaryPart L v)]
      exact hvan v
    have hpcoord := dual_forward_coordinates p hp
    have hqc := pullback_causal L p hpcoord.2 hzero
    have hpf : ∀ y, InOpenForwardCone d y → 0 < dotCLM p y := by
      simpa only [dotCLM_apply] using hp
    have hqp : 0 < dot (pullback L p) (fun μ => (z (s 0) μ).im) := by
      have ht := forward_functional_pos (dotCLM p) hpf _ hLz 0
      simp only [dotCLM_apply] at ht
      change 0 < dot p (fun μ => (complexLorentzVectorAction L (z (s 0)) μ).im) at ht
      rwa [dot_action_imaginary L p hzero] at ht
    have hq0 : 0 < pullback L p 0 := by
      by_contra hnot
      have hqf : ∀ y, InOpenForwardCone d y → dotCLM (pullback L p) y ≤ 0 := by
        intro y hy
        simpa only [dotCLM_apply] using dot_nonpos_of_nonpos_time
          (pullback L p) y (le_of_not_gt hnot) hqc hy
      have hbad := forward_functional_nonpos (dotCLM (pullback L p)) hqf z hz (s 0)
      simp only [dotCLM_apply] at hbad
      exact (not_lt_of_ge hbad) hqp
    have hqf : ∀ y, InOpenForwardCone d y → 0 < dotCLM (pullback L p) y := by
      intro y hy
      simpa only [dotCLM_apply] using dot_pos_of_coordinates (pullback L p) y hq0 hqc hy
    apply hs
    apply strictMono_perm_eq_one
    intro i j hij
    have ht := forward_functional_strictMono (dotCLM p) hpf _ hLz hij
    simp only [dotCLM_apply] at ht
    change dot p (fun μ => (complexLorentzVectorAction L (z (s i)) μ).im) <
      dot p (fun μ => (complexLorentzVectorAction L (z (s j)) μ).im) at ht
    rw [dot_action_imaginary L p hzero, dot_action_imaginary L p hzero] at ht
    have hmono : StrictMono (fun k => dot (pullback L p) (fun μ => (z k μ).im)) := by
      simpa only [dotCLM_apply] using
        forward_functional_strictMono (dotCLM (pullback L p)) hqf z hz
    exact hmono.lt_iff_lt.mp ht

private theorem relative_functional_strictMono {m : ℕ}
    (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ y, InOpenForwardCone d y → 0 < f y)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : ∀ i : Fin m,
      InOpenForwardCone d (fun μ => (z i.succ μ - z i.castSucc μ).im)) :
    StrictMono (fun k => f (fun μ => (z k μ).im)) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h := hf _ (hz i)
  change 0 < f ((fun μ => (z i.succ μ).im) - (fun μ => (z i.castSucc μ).im)) at h
  rwa [map_sub, sub_pos] at h

private theorem relative_functional_antitone {m : ℕ}
    (f : (Fin (d + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ y, InOpenForwardCone d y → f y ≤ 0)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : ∀ i : Fin m,
      InOpenForwardCone d (fun μ => (z i.succ μ - z i.castSucc μ).im)) :
    Antitone (fun k => f (fun μ => (z k μ).im)) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  have h := hf _ (hz i)
  change f ((fun μ => (z i.succ μ).im) - (fun μ => (z i.castSucc μ).im)) ≤ 0 at h
  rwa [map_sub, sub_nonpos] at h

/-- With no basepoint condition, a causal separator can be past-directed.
That case forces full reversal, which must be handled separately. -/
theorem exists_imaginary_forward_of_relative_perm_overlap [NeZero d] {m : ℕ}
    (L : ComplexLorentzGroup d) (s : Equiv.Perm (Fin (m + 1)))
    (hs : s ≠ 1) (hrev : s ≠ Fin.revPerm)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : ∀ i : Fin m,
      InOpenForwardCone d (fun μ => (z i.succ μ - z i.castSucc μ).im))
    (hLz : ∀ i : Fin m, InOpenForwardCone d (fun μ =>
      (complexLorentzAction L (permAct s z) i.succ μ -
        complexLorentzAction L (permAct s z) i.castSucc μ).im)) :
    ∃ v : Fin (d + 1) → ℝ, InOpenForwardCone d (imaginaryPart L v) := by
  by_contra hnone
  push Not at hnone
  obtain ⟨f, hvan, hpos⟩ := separator_of_range_avoids_forward (imaginaryPart L) hnone
  let p : Fin (d + 1) → ℝ := fun i => f (Pi.single i 1)
  have hp : ∀ y, InOpenForwardCone d y → 0 < dot p y := by
    intro y hy
    rw [← linear_eq_dot f y]
    exact hpos y hy
  have hzero : ∀ v, dot p (imaginaryPart L v) = 0 := by
    intro v
    rw [← linear_eq_dot f (imaginaryPart L v)]
    exact hvan v
  have hqc := pullback_causal L p (dual_forward_coordinates p hp).2 hzero
  have ht := relative_functional_strictMono (dotCLM p)
    (by simpa only [dotCLM_apply] using hp) _ hLz
  simp only [dotCLM_apply] at ht
  change StrictMono (fun k => dot p
    (fun μ => (complexLorentzVectorAction L (z (s k)) μ).im)) at ht
  simp_rw [dot_action_imaginary L p hzero] at ht
  by_cases hq0 : 0 < pullback L p 0
  · have hmono := relative_functional_strictMono (dotCLM (pullback L p))
      (fun y hy => by simpa only [dotCLM_apply] using
        dot_pos_of_coordinates _ y hq0 hqc hy) z hz
    simp only [dotCLM_apply] at hmono
    exact hs (strictMono_perm_eq_one s (fun i j hij => hmono.lt_iff_lt.mp (ht hij)))
  · have hanti := relative_functional_antitone (dotCLM (pullback L p))
      (fun y hy => by simpa only [dotCLM_apply] using
        dot_nonpos_of_nonpos_time _ y (le_of_not_gt hq0) hqc hy) z hz
    simp only [dotCLM_apply] at hanti
    have hsanti : StrictAnti s := by
      intro i j hij
      by_contra hnot
      exact (not_lt_of_ge (hanti (le_of_not_gt hnot))) (ht hij)
    have hid := strictMono_perm_eq_one (Fin.revPerm * s)
      (Fin.rev_strictAnti.comp hsanti)
    apply hrev
    apply Equiv.ext
    intro i
    have hi := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => Fin.rev (σ i)) hid
    simpa using hi

private theorem minkowskiNormSq_eq_sum [NeZero d] (v : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiNormSq d v = ∑ i, minkowskiSignature d i * v i ^ 2 := by
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  apply Finset.sum_congr rfl
  intro i _
  simp [MinkowskiSpace.metricSignature, minkowskiSignature, pow_two]

private theorem real_action_decomp (L : ComplexLorentzGroup d) (v : Fin (d + 1) → ℝ) :
    complexLorentzVectorAction L (fun i => (v i : ℂ)) =
      fun i => (realPart L v i : ℂ) + (imaginaryPart L v i : ℂ) * Complex.I := by
  ext i
  apply Complex.ext
  · change (∑ x, L.val i x * (v x : ℂ)).re =
      ((∑ x, (L.val i x).re * v x : ℝ) : ℂ).re +
        (((∑ x, (L.val i x).im * v x : ℝ) : ℂ) * Complex.I).re
    simp [Complex.mul_re]
  · change (∑ x, L.val i x * (v x : ℂ)).im =
      ((∑ x, (L.val i x).re * v x : ℝ) : ℂ).im +
        (((∑ x, (L.val i x).im * v x : ℝ) : ℂ) * Complex.I).im
    simp [Complex.mul_im]

theorem spacelike_of_imaginary_forward [NeZero d] (L : ComplexLorentzGroup d)
    (v : Fin (d + 1) → ℝ) (hv : InOpenForwardCone d (imaginaryPart L v)) :
    IsSpacelike d v := by
  have hquad : MinkowskiSpace.complexMinkowskiQuadratic d
      (complexLorentzVectorAction L (fun i => (v i : ℂ))) =
      MinkowskiSpace.complexMinkowskiQuadratic d (fun i => (v i : ℂ)) := by
    simpa [MinkowskiSpace.complexMinkowskiQuadratic, MinkowskiSpace.metricSignature,
      minkowskiSignature] using complex_quadratic_preserved L (fun i => (v i : ℂ))
  rw [real_action_decomp] at hquad
  have hre := congrArg Complex.re hquad
  have him := congrArg Complex.im hquad
  have hreal : (MinkowskiSpace.complexMinkowskiQuadratic d (fun i => (v i : ℂ))).re =
      MinkowskiSpace.minkowskiNormSq d v := by
    simpa [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner] using
      MinkowskiSpace.complexQuadratic_re d v (0 : Fin (d + 1) → ℝ)
  have himag : (MinkowskiSpace.complexMinkowskiQuadratic d (fun i => (v i : ℂ))).im = 0 := by
    simp [MinkowskiSpace.complexMinkowskiQuadratic, pow_two, Complex.mul_im]
  rw [MinkowskiSpace.complexQuadratic_re, hreal] at hre
  rw [MinkowskiSpace.complexQuadratic_im, himag] at him
  have horth : MinkowskiSpace.minkowskiInner d (realPart L v) (imaginaryPart L v) = 0 := by
    linarith
  have htime : MinkowskiSpace.IsTimelike d (imaginaryPart L v) := by
    change MinkowskiSpace.minkowskiNormSq d (imaginaryPart L v) < 0
    rw [minkowskiNormSq_eq_sum]
    exact hv.2
  have hnonneg := MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg d
    (realPart L v) (imaginaryPart L v) htime hv.1 horth
  change 0 < ∑ i, minkowskiSignature d i * v i ^ 2
  rw [← minkowskiNormSq_eq_sum]
  change MinkowskiSpace.minkowskiNormSq d (imaginaryPart L v) < 0 at htime
  linarith

theorem exists_real_jost_anchor_of_perm_overlap [NeZero d] {n : ℕ}
    (L : ComplexLorentzGroup d) (s : Equiv.Perm (Fin n)) (hs : s ≠ 1)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    (hLz : complexLorentzAction L (permAct s z) ∈ ForwardTube d n) :
    ∃ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n ∧
      complexLorentzAction L (permAct s (realEmbed x)) ∈ ForwardTube d n := by
  obtain ⟨v, hv⟩ := exists_imaginary_forward_of_perm_overlap L s hs z hz hLz
  have hvsp := spacelike_of_imaginary_forward L v hv
  let x : Fin n → Fin (d + 1) → ℝ := fun k => (((s⁻¹ k).val : ℝ) + 1) • v
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro k
      exact isSpacelike_smul hvsp (by positivity)
    · intro i j hij
      have hne : ((s⁻¹ i).val : ℝ) - (s⁻¹ j).val ≠ 0 := by
        intro heq
        apply hij
        apply s.symm.injective
        apply Fin.ext
        exact_mod_cast sub_eq_zero.mp heq
      have heq : (fun μ => x i μ - x j μ) =
          (((s⁻¹ i).val : ℝ) - (s⁻¹ j).val) • v := by
        ext μ
        dsimp [x]
        ring
      rw [heq]
      exact isSpacelike_smul hvsp hne
  · have hact (k : Fin n) : complexLorentzAction L (permAct s (realEmbed x)) k =
        fun μ => ((k.val : ℂ) + 1) * complexLorentzVectorAction L (fun i => (v i : ℂ)) μ := by
      change complexLorentzVectorAction L
        (fun μ => (((((s⁻¹ (s k)).val : ℝ) + 1) * v μ : ℝ) : ℂ)) = _
      simpa using
        complexLorentzVectorAction_smul L ((k.val : ℂ) + 1) (fun i => (v i : ℂ))
    intro k
    have hdiff : imDiff (complexLorentzAction L (permAct s (realEmbed x))) k =
        imaginaryPart L v := by
      ext μ
      by_cases hk : k.val = 0
      · simp only [imDiff, hk, dite_true, Pi.zero_apply, sub_zero]
        rw [hact, real_action_decomp]
        simp [hk]
      · simp only [imDiff, hk, dite_false, hact, real_action_decomp, Complex.sub_im,
          Complex.mul_im, Complex.add_im, Complex.natCast_im, Complex.one_im,
          Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.ofReal_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          zero_mul, add_zero, zero_add]
        have hpred : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
          norm_num
        rw [hpred]
        ring
    change InOpenForwardCone d (imDiff _ k)
    rwa [hdiff]

theorem forwardTube_real_interpolation {n : ℕ}
    (x : Fin n → Fin (d + 1) → ℝ) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n) (a b : ℝ) (hb : 0 < b) :
    a • realEmbed x + b • z ∈ ForwardTube d n := by
  intro k
  change InOpenForwardCone d (imDiff (a • realEmbed x + b • z) k)
  rw [imDiff_linear]
  have hzero : imDiff (realEmbed x) k = 0 := by
    ext μ
    by_cases hk : k.val = 0 <;> simp [imDiff, realEmbed, hk]
  rw [hzero, smul_zero, zero_add]
  exact inOpenForwardCone_smul_pos (hz k) hb

theorem exists_real_jost_anchor_segment_of_perm_overlap [NeZero d] {n : ℕ}
    (L : ComplexLorentzGroup d) (s : Equiv.Perm (Fin n)) (hs : s ≠ 1)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    (hLz : complexLorentzAction L (permAct s z) ∈ ForwardTube d n) :
    ∃ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n ∧
      complexLorentzAction L (permAct s (realEmbed x)) ∈ ForwardTube d n ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        (1 - t) • realEmbed x + t • z ∈ ForwardTube d n ∧
        complexLorentzAction L (permAct s ((1 - t) • realEmbed x + t • z)) ∈
          ForwardTube d n := by
  obtain ⟨x, hx, hLx⟩ := exists_real_jost_anchor_of_perm_overlap L s hs z hz hLz
  refine ⟨x, hx, hLx, ?_⟩
  intro t ht ht1
  refine ⟨forwardTube_real_interpolation x z hz (1 - t) t ht, ?_⟩
  have hperm : permAct s ((1 - t) • realEmbed x + t • z) =
      (1 - t) • permAct s (realEmbed x) + t • permAct s z := rfl
  rw [hperm, complexLorentzAction_real_linear]
  exact forwardTube_convex hLx hLz (sub_nonneg.mpr ht1) ht.le (by ring)

end BHW.SliceGeometry
