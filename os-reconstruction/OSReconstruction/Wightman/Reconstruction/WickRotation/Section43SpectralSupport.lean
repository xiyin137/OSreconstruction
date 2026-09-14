/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory
open SchwartzMap

namespace OSReconstruction











noncomputable def zeroHeadBlockShiftCLM (m n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (m + n) → ℝ) where
  toFun := zeroHeadBlockShift (m := m) (n := n)
  map_add' := by
    intro a b
    induction m with
    | zero =>
        ext i
        simp [zeroHeadBlockShift, Pi.add_apply, castFinCLE]
    | succ m ih =>
        ext i
        simp only [zeroHeadBlockShift, Pi.add_apply, castFinCLE_symm_apply]
        let j : Fin ((m + n) + 1) := (finCongr (Nat.succ_add m n)) i
        let fab : Fin ((m + n) + 1) → ℝ :=
          Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) (a + b))
        let fa : Fin ((m + n) + 1) → ℝ :=
          Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a)
        let fb : Fin ((m + n) + 1) → ℝ :=
          Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) b)
        change fab j = fa j + fb j
        cases j using Fin.cases with
        | zero => simp [fab, fa, fb]
        | succ j => simp [fab, fa, fb, ih, Pi.add_apply]
  map_smul' := by
    intro c a
    induction m with
    | zero =>
        ext i
        simp [zeroHeadBlockShift, Pi.smul_apply, castFinCLE]
    | succ m ih =>
        ext i
        simp only [zeroHeadBlockShift, Pi.smul_apply, castFinCLE_symm_apply]
        let j : Fin ((m + n) + 1) := (finCongr (Nat.succ_add m n)) i
        let fca : Fin ((m + n) + 1) → ℝ :=
          Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) (c • a))
        let fa : Fin ((m + n) + 1) → ℝ :=
          Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a)
        change fca j = c * fa j
        cases j using Fin.cases with
        | zero => simp [fca, fa]
        | succ j => simp [fca, fa, ih, Pi.smul_apply]
  cont := by
    induction m with
    | zero =>
        simpa [zeroHeadBlockShift] using (castFinCLE (Nat.zero_add n)).symm.continuous
    | succ m ih =>
        rw [show (zeroHeadBlockShift (m := m + 1) (n := n)) =
            (castFinCLE (Nat.succ_add m n)).symm ∘
              (fun a : Fin n → ℝ =>
                Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a)) by
          funext a
          simp [zeroHeadBlockShift]]
        apply Continuous.comp (castFinCLE (Nat.succ_add m n)).symm.continuous
        exact continuous_pi fun i => by
          refine Fin.cases ?_ ?_ i
          · exact continuous_const
          · intro j
            exact (continuous_apply j).comp ih

@[simp] theorem zeroHeadBlockShiftCLM_apply (m n : ℕ)
    (y : Fin n → ℝ) :
    zeroHeadBlockShiftCLM m n y =
      zeroHeadBlockShift (m := m) (n := n) y := rfl

noncomputable def zeroHeadSectionCLM :
    ∀ p q : ℕ,
      SchwartzMap (Fin (p + q) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin q → ℝ) ℂ
  | 0, q =>
      reindexSchwartzFin (Nat.zero_add q)
  | p + 1, q =>
      (zeroHeadSectionCLM p q).comp
        ((headSectionCLM (p + q)).comp
          (reindexSchwartzFin (Nat.succ_add p q)))

noncomputable def headBlockBumpExtension :
    ∀ p q : ℕ,
      SchwartzMap (Fin q → ℝ) ℂ →
        SchwartzMap (Fin (p + q) → ℝ) ℂ
  | 0, q, G =>
      reindexSchwartzFin (Nat.zero_add q).symm G
  | p + 1, q, G =>
      reindexSchwartzFin (Nat.succ_add p q).symm
        (unitBumpSchwartz.prependField
          (headBlockBumpExtension p q G))

@[simp] theorem headBlockBumpExtension_zeroHeadBlockShift
    (p q : ℕ) (G : SchwartzMap (Fin q → ℝ) ℂ)
    (y : Fin q → ℝ) :
    headBlockBumpExtension p q G
      (zeroHeadBlockShift (m := p) (n := q) y) =
      G y := by
  induction p with
  | zero =>
      simp only [headBlockBumpExtension, zeroHeadBlockShift, reindexSchwartzFin_apply]
      have harg :
          (castFinCLE (Nat.zero_add q).symm).symm
            ((castFinCLE (Nat.zero_add q)).symm y) = y := by
        ext i
        simp [castFinCLE]
      rw [harg]
  | succ p ih =>
      simp [headBlockBumpExtension, zeroHeadBlockShift, SchwartzMap.prependField_apply,
        unitBumpSchwartz_zero, ih]

theorem eq_of_splitFirst_eq_splitLast_eq {p q : ℕ}
    {x y : Fin (p + q) → ℝ}
    (hfirst : splitFirst p q x = splitFirst p q y)
    (hlast : splitLast p q x = splitLast p q y) :
    x = y := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    exact congrFun hfirst a
  · intro b
    exact congrFun hlast b

theorem eq_zeroHeadBlockShift_of_splitFirst_eq_zero
    {p q : ℕ} {x : Fin (p + q) → ℝ}
    (hx : splitFirst p q x = 0) :
    x = zeroHeadBlockShift (m := p) (n := q) (splitLast p q x) := by
  apply eq_of_splitFirst_eq_splitLast_eq
  · rw [splitFirst_zeroHeadBlockShift_eq_zero]
    exact hx
  · rw [splitLast_zeroHeadBlockShift_eq]

theorem section43_fin_prefix_sum_eq_lower_sum_public
    {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) (k : Fin n) :
    (∑ l : Fin (k.val + 1), f ⟨l.val, by omega⟩) =
      ∑ j : Fin n, if j.val ≤ k.val then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun l (_hl : l ∈ (Finset.univ : Finset (Fin (k.val + 1)))) =>
      (⟨l.val, by omega⟩ : Fin n)) ?hmem ?hinj ?hsurj ?hval
  · intro l _hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_succ_iff.mp l.isLt
  · intro a _ha b _hb h
    have hval := congrArg Fin.val h
    apply Fin.ext
    exact hval
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    let a : Fin (k.val + 1) := ⟨b.val, Nat.lt_succ_iff.mpr hb⟩
    refine ⟨a, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro _l _hl
    rfl

theorem section43_fin_prefix_mul_eq_sum_tail_public
    {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, (∑ l : Fin (k.val + 1), a ⟨l.val, by omega⟩) * b k) =
      ∑ j : Fin n, a j * ∑ k : Fin n, if j.val ≤ k.val then b k else 0 := by
  classical
  calc
    (∑ k : Fin n, (∑ l : Fin (k.val + 1), a ⟨l.val, by omega⟩) * b k)
        = ∑ k : Fin n, (∑ j : Fin n, if j.val ≤ k.val then a j else 0) * b k := by
          simp only [section43_fin_prefix_sum_eq_lower_sum_public]
    _ = ∑ k : Fin n, ∑ j : Fin n, (if j.val ≤ k.val then a j else 0) * b k := by
          simp [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ k : Fin n, (if j.val ≤ k.val then a j else 0) * b k := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, a j * ∑ k : Fin n, if j.val ≤ k.val then b k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _hk
          by_cases h : j.val ≤ k.val
          · simp [h]
          · simp [h]

theorem section43DiffCoord_pairing_eq_rawCumulativeTail
    (d n : ℕ) [NeZero d]
    (δ : NPointDomain d n)
    (ξ : Fin (n * (d + 1)) → ℝ) :
    (∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)
      =
    ∑ j : Fin n, ∑ μ : Fin (d + 1),
      δ j μ * section43RawCumulativeTailMomentumCLE d n ξ j μ := by
  classical
  calc
    (∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)
        = ∑ k : Fin n, ∑ μ : Fin (d + 1),
            (section43DiffCoordRealCLE d n).symm δ k μ *
              ξ (finProdFinEquiv (k, μ)) := by
          calc
            (∑ i : Fin (n * (d + 1)),
                flattenCLEquivReal n (d + 1)
                  ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)
                = ∑ p : Fin n × Fin (d + 1),
                    flattenCLEquivReal n (d + 1)
                      ((section43DiffCoordRealCLE d n).symm δ)
                        (finProdFinEquiv p) *
                      ξ (finProdFinEquiv p) := by
                  simpa using
                    (finProdFinEquiv.sum_comp
                      (fun i : Fin (n * (d + 1)) =>
                        flattenCLEquivReal n (d + 1)
                          ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)).symm
            _ = ∑ k : Fin n, ∑ μ : Fin (d + 1),
                    (section43DiffCoordRealCLE d n).symm δ k μ *
                      ξ (finProdFinEquiv (k, μ)) := by
                  simpa [flattenCLEquivReal_apply] using
                    (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                      (t := (Finset.univ : Finset (Fin (d + 1))))
                      (f := fun p : Fin n × Fin (d + 1) =>
                        (section43DiffCoordRealCLE d n).symm δ p.1 p.2 *
                          ξ (finProdFinEquiv p)))
    _ = ∑ k : Fin n, ∑ μ : Fin (d + 1),
          (∑ l : Fin (k.val + 1), δ ⟨l.val, by omega⟩ μ) *
            ξ (finProdFinEquiv (k, μ)) := by
          simp only [section43DiffCoordRealCLE_symm_apply]
    _ = ∑ μ : Fin (d + 1), ∑ k : Fin n,
          (∑ l : Fin (k.val + 1), δ ⟨l.val, by omega⟩ μ) *
            ξ (finProdFinEquiv (k, μ)) := by
          rw [Finset.sum_comm]
    _ = ∑ μ : Fin (d + 1), ∑ j : Fin n,
          δ j μ * ∑ k : Fin n, if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro μ _hμ
          exact section43_fin_prefix_mul_eq_sum_tail_public
            (fun j : Fin n => δ j μ) (fun k : Fin n => ξ (finProdFinEquiv (k, μ)))
    _ = ∑ j : Fin n, ∑ μ : Fin (d + 1),
          δ j μ * ∑ k : Fin n, if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ μ : Fin (d + 1),
          δ j μ * section43RawCumulativeTailMomentumCLE d n ξ j μ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_congr rfl ?_
          intro μ _hμ
          simp [section43RawCumulativeTailMomentumCLE_apply]

theorem exists_pos_mul_abs_lt_of_neg {c s : ℝ} (hs : s < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε * |c| < -s := by
  refine ⟨(-s) / (2 * (|c| + 1)), ?_, ?_⟩
  · have hs_pos : 0 < -s := by linarith
    have hden_pos : 0 < 2 * (|c| + 1) := by positivity
    exact div_pos hs_pos hden_pos
  · have hs_pos : 0 < -s := by linarith
    have hden_pos : 0 < 2 * (|c| + 1) := by positivity
    have hlt : |c| < 2 * (|c| + 1) := by
      nlinarith [abs_nonneg c]
    have hfrac_lt_one : |c| / (2 * (|c| + 1)) < 1 := by
      rw [div_lt_one hden_pos]
      exact hlt
    calc
      (-s) / (2 * (|c| + 1)) * |c| = (-s) * (|c| / (2 * (|c| + 1))) := by ring
      _ < (-s) * 1 := by
        exact mul_lt_mul_of_pos_left hfrac_lt_one hs_pos
      _ = -s := by ring

end OSReconstruction
