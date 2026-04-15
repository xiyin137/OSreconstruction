import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43TotalMomentumSupport

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory
open SchwartzMap

namespace OSReconstruction

/-!
# Section 4.3 Spectral Support Combination

This file contains the small support-combination infrastructure for the
OS-route Section 4.3 spectral condition.  It intentionally stays separate from
the already stable total-momentum support file: the goal here is to combine
dual-cone support with total-momentum-zero support without using the false
generic closed-set intersection theorem.
-/

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

@[simp] theorem zeroHeadSectionCLM_apply
    (p q : ℕ) (F : SchwartzMap (Fin (p + q) → ℝ) ℂ)
    (y : Fin q → ℝ) :
    zeroHeadSectionCLM p q F y =
      F (zeroHeadBlockShift (m := p) (n := q) y) := by
  induction p with
  | zero =>
      simp [zeroHeadSectionCLM, zeroHeadBlockShift]
  | succ p ih =>
      simp [zeroHeadSectionCLM, zeroHeadBlockShift, ih, headSectionCLM_apply,
        reindexSchwartzFin_apply]

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

theorem splitLast_castFinCLE_succ_add_tail
    {p q : ℕ} (x : Fin ((p + 1) + q) → ℝ) :
    splitLast p q
        (fun i : Fin (p + q) =>
          (castFinCLE (Nat.succ_add p q) x) i.succ)
      =
    splitLast (p + 1) q x := by
  ext j
  simp [splitLast]
  change x ((finCongr (Nat.succ_add p q)).symm ((Fin.natAdd p j).succ)) =
    x (Fin.natAdd (p + 1) j)
  congr 1
  apply Fin.ext
  simp
  omega

theorem headBlockBumpExtension_eq_zero_of_tail_zero
    (p q : ℕ) (G : SchwartzMap (Fin q → ℝ) ℂ)
    (x : Fin (p + q) → ℝ)
    (hG : G (splitLast p q x) = 0) :
    headBlockBumpExtension p q G x = 0 := by
  induction p with
  | zero =>
      simp only [headBlockBumpExtension, reindexSchwartzFin_apply]
      have harg :
          (castFinCLE (Nat.zero_add q).symm).symm x = splitLast 0 q x := by
        ext i
        simp [splitLast, castFinCLE]
      rw [harg, hG]
  | succ p ih =>
      simp only [headBlockBumpExtension, reindexSchwartzFin_apply]
      let x' : Fin ((p + q) + 1) → ℝ := castFinCLE (Nat.succ_add p q) x
      have htail : splitLast p q (fun i : Fin (p + q) => x' i.succ) =
          splitLast (p + 1) q x := by
        simpa [x'] using splitLast_castFinCLE_succ_add_tail (p := p) (q := q) x
      have hzero :
          headBlockBumpExtension p q G (fun i : Fin (p + q) => x' i.succ) = 0 := by
        apply ih
        simpa [htail] using hG
      change unitBumpSchwartz (x' 0) *
          headBlockBumpExtension p q G (fun i : Fin (p + q) => x' i.succ) = 0
      rw [hzero, mul_zero]

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

theorem section43_inOpenForwardCone_timeAxis_public (d : ℕ) [NeZero d]
    {a : ℝ} (ha : 0 < a) :
    InOpenForwardCone d
      (fun μ : Fin (d + 1) => if μ = (0 : Fin (d + 1)) then a else 0) := by
  refine ⟨by simp [ha], ?_⟩
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  simp only [MinkowskiSpace.spatialNormSq, ↓reduceIte, Fin.succ_ne_zero]
  simp
  nlinarith [sq_pos_of_pos ha]

theorem section43DiffCoordRealCLE_mem_openForwardCone_of_mem_forwardConeAbs
    (d n : ℕ) [NeZero d]
    {y : NPointDomain d n} (hy : y ∈ ForwardConeAbs d n) :
    ∀ k : Fin n, InOpenForwardCone d (section43DiffCoordRealCLE d n y k) := by
  intro k
  have hk := hy k
  change InOpenForwardCone d (fun μ : Fin (d + 1) =>
    section43DiffCoordRealCLE d n y k μ)
  simp only [section43DiffCoordRealCLE_apply]
  by_cases h : k.val = 0
  · simpa [ForwardConeAbs, h] using hk
  · simpa [ForwardConeAbs, h] using hk

theorem section43DiffCoordRealCLE_symm_mem_forwardConeAbs_public
    (d n : ℕ) [NeZero d]
    {δ : NPointDomain d n}
    (hδ : ∀ k : Fin n, InOpenForwardCone d (δ k)) :
    (section43DiffCoordRealCLE d n).symm δ ∈ ForwardConeAbs d n := by
  intro k
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm δ
  have hcoord :
      (fun μ : Fin (d + 1) =>
          y k μ -
            (let prev : Fin (d + 1) → ℝ :=
              if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
            prev μ)) =
        δ k := by
    ext μ
    have happly :=
      congr_fun (congr_fun ((section43DiffCoordRealCLE d n).apply_symm_apply δ) k) μ
    rw [section43DiffCoordRealCLE_apply] at happly
    by_cases hk : k.val = 0
    · simp [hk] at happly ⊢
      exact happly
    · simp [hk] at happly ⊢
      exact happly
  change InOpenForwardCone d
    (fun μ : Fin (d + 1) =>
      y k μ -
        (let prev : Fin (d + 1) → ℝ :=
          if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
        prev μ))
  rw [hcoord]
  exact hδ k

def section43FirstDiffTimeAxisPerturbation
    (d N' : ℕ) [NeZero d]
    (δ : NPointDomain d (N' + 1)) (ε : ℝ) :
    NPointDomain d (N' + 1) :=
  fun k μ =>
    if k = 0 then
      if μ = 0 then ε else 0
    else
      δ k μ

theorem section43FirstDiffTimeAxisPerturbation_mem_forwardConeAbs
    (d N' : ℕ) [NeZero d]
    {δ : NPointDomain d (N' + 1)} {ε : ℝ}
    (hε : 0 < ε)
    (hδ_tail : ∀ j : Fin N', InOpenForwardCone d (δ j.succ)) :
    (section43DiffCoordRealCLE d (N' + 1)).symm
      (section43FirstDiffTimeAxisPerturbation d N' δ ε)
      ∈ ForwardConeAbs d (N' + 1) := by
  apply section43DiffCoordRealCLE_symm_mem_forwardConeAbs_public
  intro k
  cases k using Fin.cases with
  | zero =>
      simpa [section43FirstDiffTimeAxisPerturbation] using
        section43_inOpenForwardCone_timeAxis_public d hε
  | succ j =>
      simpa [section43FirstDiffTimeAxisPerturbation] using hδ_tail j

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

noncomputable def section43TotalMomentumZeroProjection
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) →L[ℝ]
      (Fin ((N' + 1) * (d + 1)) → ℝ) :=
  let e := section43TotalMomentumHeadTailCLE d N'
  e.symm.toContinuousLinearMap.comp
    ((zeroHeadBlockShiftCLM (d + 1) (N' * (d + 1))).comp
      ((splitLastCLM (E := ℝ) (d + 1) (N' * (d + 1))).comp
        e.toContinuousLinearMap))

@[simp] theorem section43TotalMomentumZeroProjection_headTail
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    section43TotalMomentumHeadTailCLE d N'
        (section43TotalMomentumZeroProjection d N' ξ)
      =
    zeroHeadBlockShift
      (m := d + 1) (n := N' * (d + 1))
      (splitLast (d + 1) (N' * (d + 1))
        (section43TotalMomentumHeadTailCLE d N' ξ)) := by
  simp [section43TotalMomentumZeroProjection]

theorem section43TotalMomentumZeroProjection_mem_totalMomentumZero
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    section43TotalMomentumZeroProjection d N' ξ ∈
      section43TotalMomentumZeroFlat d (N' + 1) := by
  change section43TotalMomentumFlat d (N' + 1)
      (section43TotalMomentumZeroProjection d N' ξ) = 0
  rw [← splitFirst_section43TotalMomentumHeadTailCLE d N'
    (section43TotalMomentumZeroProjection d N' ξ)]
  rw [section43TotalMomentumZeroProjection_headTail]
  simp

theorem section43TotalMomentumZeroProjection_eq_of_mem_totalMomentumZero
    (d N' : ℕ) [NeZero d]
    {ξ : Fin ((N' + 1) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43TotalMomentumZeroFlat d (N' + 1)) :
    section43TotalMomentumZeroProjection d N' ξ = ξ := by
  let e := section43TotalMomentumHeadTailCLE d N'
  apply e.injective
  rw [section43TotalMomentumZeroProjection_headTail]
  have hhead : splitFirst (d + 1) (N' * (d + 1)) (e ξ) = 0 := by
    simpa [e, section43TotalMomentumZeroFlat] using hξ
  exact (eq_zeroHeadBlockShift_of_splitFirst_eq_zero hhead).symm

@[simp] theorem section43TotalMomentumZeroProjection_zero
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (μ : Fin (d + 1)) :
    section43TotalMomentumZeroProjection d N' ξ
        (finProdFinEquiv ((0 : Fin (N' + 1)), μ)) =
      - ∑ j : Fin N', ξ (finProdFinEquiv (j.succ, μ)) := by
  change (section43TotalMomentumHeadTailCLE d N').symm
      (zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
        (splitLast (d + 1) (N' * (d + 1))
          (section43TotalMomentumHeadTailCLE d N' ξ)))
      (finProdFinEquiv ((0 : Fin (N' + 1)), μ)) = _
  rw [section43TotalMomentumHeadTailCLE_symm_zero]
  let y : Fin (N' * (d + 1)) → ℝ :=
    splitLast (d + 1) (N' * (d + 1))
      (section43TotalMomentumHeadTailCLE d N' ξ)
  change zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1)) y
        (Fin.castAdd (N' * (d + 1)) μ) -
      ∑ x : Fin N', zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1)) y
        (Fin.natAdd (d + 1) (finProdFinEquiv (x, μ))) = _
  have hy_head : zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1)) y
      (Fin.castAdd (N' * (d + 1)) μ) = 0 := by
    have h := congrFun (splitFirst_zeroHeadBlockShift_eq_zero
      (m := d + 1) (n := N' * (d + 1)) y) μ
    simpa [splitFirst] using h
  have hy_tail : ∀ x : Fin N',
      zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1)) y
        (Fin.natAdd (d + 1) (finProdFinEquiv (x, μ))) =
      ξ (finProdFinEquiv (x.succ, μ)) := by
    intro x
    have h := congrFun (splitLast_zeroHeadBlockShift_eq
      (m := d + 1) (n := N' * (d + 1)) y) (finProdFinEquiv (x, μ))
    have hidx :
        finProdFinEquiv (((finProdFinEquiv (x, μ)).divNat).succ,
            (finProdFinEquiv (x, μ)).modNat) =
          finProdFinEquiv (x.succ, μ) := by
      have hp : (finProdFinEquiv (x, μ)).divNat = x ∧
          (finProdFinEquiv (x, μ)).modNat = μ :=
        Prod.ext_iff.mp (Equiv.symm_apply_apply finProdFinEquiv (x, μ))
      exact congrArg finProdFinEquiv (Prod.ext (congrArg Fin.succ hp.1) hp.2)
    simpa [splitLast, y, splitLast_section43TotalMomentumHeadTailCLE, hidx] using h
  rw [hy_head]
  simp [hy_tail]

@[simp] theorem section43TotalMomentumZeroProjection_succ
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    section43TotalMomentumZeroProjection d N' ξ
        (finProdFinEquiv (j.succ, μ)) =
      ξ (finProdFinEquiv (j.succ, μ)) := by
  change (section43TotalMomentumHeadTailCLE d N').symm
      (zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
        (splitLast (d + 1) (N' * (d + 1))
          (section43TotalMomentumHeadTailCLE d N' ξ)))
      (finProdFinEquiv (j.succ, μ)) = _
  rw [section43TotalMomentumHeadTailCLE_symm_succ]
  let y : Fin (N' * (d + 1)) → ℝ :=
    splitLast (d + 1) (N' * (d + 1))
      (section43TotalMomentumHeadTailCLE d N' ξ)
  change zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1)) y
        (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) = _
  have h := congrFun (splitLast_zeroHeadBlockShift_eq
      (m := d + 1) (n := N' * (d + 1)) y) (finProdFinEquiv (j, μ))
  have hidx :
      finProdFinEquiv (((finProdFinEquiv (j, μ)).divNat).succ,
          (finProdFinEquiv (j, μ)).modNat) =
        finProdFinEquiv (j.succ, μ) := by
    have hp : (finProdFinEquiv (j, μ)).divNat = j ∧
        (finProdFinEquiv (j, μ)).modNat = μ :=
      Prod.ext_iff.mp (Equiv.symm_apply_apply finProdFinEquiv (j, μ))
    exact congrArg finProdFinEquiv (Prod.ext (congrArg Fin.succ hp.1) hp.2)
  simpa [splitLast, y, splitLast_section43TotalMomentumHeadTailCLE, hidx] using h

theorem section43TotalMomentumZeroProjection_rawCumulative_zero
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d (N' + 1)
      (section43TotalMomentumZeroProjection d N' ξ)
      (0 : Fin (N' + 1)) μ = 0 := by
  rw [section43RawCumulativeTailMomentumCLE_apply]
  simp only [Fin.val_zero, zero_le, ↓reduceIte]
  rw [Fin.sum_univ_succ]
  simp

theorem section43TotalMomentumZeroProjection_rawCumulative_succ
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d (N' + 1)
      (section43TotalMomentumZeroProjection d N' ξ)
      (j.succ) μ =
    section43RawCumulativeTailMomentumCLE d (N' + 1) ξ (j.succ) μ := by
  rw [section43RawCumulativeTailMomentumCLE_apply]
  rw [section43RawCumulativeTailMomentumCLE_apply]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp

theorem section43FirstDiffTimeAxisPerturbation_pairing_eq
    (d N' : ℕ) [NeZero d]
    (δ : NPointDomain d (N' + 1))
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (ε : ℝ) :
    (∑ j : Fin (N' + 1), ∑ μ : Fin (d + 1),
      section43FirstDiffTimeAxisPerturbation d N' δ ε j μ *
        section43RawCumulativeTailMomentumCLE d (N' + 1) ξ j μ)
    = ε * section43RawCumulativeTailMomentumCLE d (N' + 1) ξ (0 : Fin (N' + 1)) 0 +
      ∑ j : Fin N', ∑ μ : Fin (d + 1),
        δ j.succ μ * section43RawCumulativeTailMomentumCLE d (N' + 1) ξ j.succ μ := by
  rw [Fin.sum_univ_succ]
  simp [section43FirstDiffTimeAxisPerturbation]

theorem section43TotalMomentumZeroProjection_rawCumulative_pairing_eq_tail
    (d N' : ℕ) [NeZero d]
    (δ : NPointDomain d (N' + 1))
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    (∑ j : Fin (N' + 1), ∑ μ : Fin (d + 1),
      δ j μ * section43RawCumulativeTailMomentumCLE d (N' + 1)
        (section43TotalMomentumZeroProjection d N' ξ) j μ)
    = ∑ j : Fin N', ∑ μ : Fin (d + 1),
      δ j.succ μ * section43RawCumulativeTailMomentumCLE d (N' + 1) ξ j.succ μ := by
  rw [Fin.sum_univ_succ]
  have hzero : (∑ μ : Fin (d + 1),
      δ 0 μ * section43RawCumulativeTailMomentumCLE d (N' + 1)
        (section43TotalMomentumZeroProjection d N' ξ) 0 μ) = 0 := by
    apply Finset.sum_eq_zero
    intro μ _hμ
    rw [section43TotalMomentumZeroProjection_rawCumulative_zero]
    ring
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  refine Finset.sum_congr rfl ?_
  intro μ _hμ
  rw [section43TotalMomentumZeroProjection_rawCumulative_succ]

theorem section43TotalMomentumZeroProjection_mem_dualCone
    (d N' : ℕ) [NeZero d]
    {ξ : Fin ((N' + 1) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (N' + 1) (d + 1)) ''
          ForwardConeAbs d (N' + 1))) :
    section43TotalMomentumZeroProjection d N' ξ ∈
      DualConeFlat
        ((flattenCLEquivReal (N' + 1) (d + 1)) ''
          ForwardConeAbs d (N' + 1)) := by
  rw [mem_dualConeFlat] at hξ ⊢
  intro yflat hyflat
  rcases hyflat with ⟨y, hy, rfl⟩
  let δ : NPointDomain d (N' + 1) := section43DiffCoordRealCLE d (N' + 1) y
  let target : ℝ :=
    ∑ j : Fin N', ∑ μ : Fin (d + 1),
      δ j.succ μ * section43RawCumulativeTailMomentumCLE d (N' + 1) ξ j.succ μ
  have hdot_eq :
      (∑ i : Fin ((N' + 1) * (d + 1)),
          flattenCLEquivReal (N' + 1) (d + 1) y i *
            section43TotalMomentumZeroProjection d N' ξ i) = target := by
    calc
      (∑ i : Fin ((N' + 1) * (d + 1)),
          flattenCLEquivReal (N' + 1) (d + 1) y i *
            section43TotalMomentumZeroProjection d N' ξ i)
          = ∑ j : Fin (N' + 1), ∑ μ : Fin (d + 1),
              δ j μ * section43RawCumulativeTailMomentumCLE d (N' + 1)
                (section43TotalMomentumZeroProjection d N' ξ) j μ := by
            simpa [δ] using
              section43DiffCoord_pairing_eq_rawCumulativeTail d (N' + 1) δ
                (section43TotalMomentumZeroProjection d N' ξ)
      _ = target := by
            simpa [target] using
              section43TotalMomentumZeroProjection_rawCumulative_pairing_eq_tail d N' δ ξ
  rw [hdot_eq]
  by_contra hnot
  have htarget_neg : target < 0 := lt_of_not_ge hnot
  let c : ℝ := section43RawCumulativeTailMomentumCLE d (N' + 1) ξ (0 : Fin (N' + 1)) 0
  obtain ⟨ε, hε_pos, hε_small⟩ :=
    exists_pos_mul_abs_lt_of_neg (c := c) (s := target) htarget_neg
  let δeps : NPointDomain d (N' + 1) := section43FirstDiffTimeAxisPerturbation d N' δ ε
  have hδ_tail : ∀ j : Fin N', InOpenForwardCone d (δ j.succ) := by
    intro j
    exact section43DiffCoordRealCLE_mem_openForwardCone_of_mem_forwardConeAbs d
      (N' + 1) hy j.succ
  have hy_eps : (section43DiffCoordRealCLE d (N' + 1)).symm δeps ∈
      ForwardConeAbs d (N' + 1) := by
    simpa [δeps] using
      section43FirstDiffTimeAxisPerturbation_mem_forwardConeAbs d N'
        (δ := δ) (ε := ε) hε_pos hδ_tail
  have hy_eps_flat :
      flattenCLEquivReal (N' + 1) (d + 1)
          ((section43DiffCoordRealCLE d (N' + 1)).symm δeps) ∈
        (flattenCLEquivReal (N' + 1) (d + 1)) '' ForwardConeAbs d (N' + 1) := by
    exact ⟨(section43DiffCoordRealCLE d (N' + 1)).symm δeps, hy_eps, rfl⟩
  have hnonneg_dot := hξ
    (flattenCLEquivReal (N' + 1) (d + 1)
      ((section43DiffCoordRealCLE d (N' + 1)).symm δeps)) hy_eps_flat
  have hnonneg_sum :
      0 ≤ ∑ j : Fin (N' + 1), ∑ μ : Fin (d + 1),
        δeps j μ * section43RawCumulativeTailMomentumCLE d (N' + 1) ξ j μ := by
    rw [← section43DiffCoord_pairing_eq_rawCumulativeTail d (N' + 1) δeps ξ]
    exact hnonneg_dot
  have hnonneg_eps : 0 ≤ ε * c + target := by
    rw [← section43FirstDiffTimeAxisPerturbation_pairing_eq d N' δ ξ ε]
    simpa [δeps, c, target] using hnonneg_sum
  have hεc_le : ε * c ≤ ε * |c| := by
    exact mul_le_mul_of_nonneg_left (le_abs_self c) hε_pos.le
  have hlt : ε * c + target < 0 := by
    linarith
  linarith

theorem exists_section43TotalMomentumZeroExtension_vanishes_dualCone
    (d N : ℕ) [NeZero d]
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (hK :
      ∀ ξ, ξ ∈ section43WightmanSpectralRegion d N → K ξ = 0) :
    ∃ KE : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
      (∀ ξ, ξ ∈ section43TotalMomentumZeroFlat d N → KE ξ = K ξ) ∧
      (∀ ξ, ξ ∈
        DualConeFlat ((flattenCLEquivReal N (d + 1)) ''
          ForwardConeAbs d N) → KE ξ = 0) := by
  cases N with
  | zero =>
      refine ⟨K, ?_, ?_⟩
      · intro ξ _hξ
        rfl
      · intro ξ hdual
        apply hK ξ
        refine ⟨hdual, ?_⟩
        change section43TotalMomentumFlat d 0 ξ = 0
        ext μ
        simp [section43TotalMomentumFlat]
  | succ N' =>
      let e := section43TotalMomentumHeadTailCLE d N'
      let F : SchwartzMap (Fin ((d + 1) + (N' * (d + 1))) → ℝ) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm K
      let G : SchwartzMap (Fin (N' * (d + 1)) → ℝ) ℂ :=
        zeroHeadSectionCLM (d + 1) (N' * (d + 1)) F
      let B : SchwartzMap (Fin ((d + 1) + (N' * (d + 1))) → ℝ) ℂ :=
        headBlockBumpExtension (d + 1) (N' * (d + 1)) G
      let KE : SchwartzMap (Fin ((N' + 1) * (d + 1)) → ℝ) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e B
      refine ⟨KE, ?_, ?_⟩
      · intro ξ hξ
        have hhead : splitFirst (d + 1) (N' * (d + 1)) (e ξ) = 0 := by
          simpa [e, section43TotalMomentumZeroFlat] using hξ
        have heq : e ξ = zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
            (splitLast (d + 1) (N' * (d + 1)) (e ξ)) :=
          eq_zeroHeadBlockShift_of_splitFirst_eq_zero hhead
        calc
          KE ξ = B (e ξ) := by
            simp [KE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
          _ = B (zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
              (splitLast (d + 1) (N' * (d + 1)) (e ξ))) := by
            exact congrArg B heq
          _ = G (splitLast (d + 1) (N' * (d + 1)) (e ξ)) := by
            simpa only [B] using
              headBlockBumpExtension_zeroHeadBlockShift
                (d + 1) (N' * (d + 1)) G
                (splitLast (d + 1) (N' * (d + 1)) (e ξ))
          _ = F (zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
              (splitLast (d + 1) (N' * (d + 1)) (e ξ))) := by
            simp [G]
          _ = F (e ξ) := by rw [← heq]
          _ = K ξ := by
            simp [F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      · intro ξ hdual
        let η : Fin ((N' + 1) * (d + 1)) → ℝ :=
          section43TotalMomentumZeroProjection d N' ξ
        have hη_total : η ∈ section43TotalMomentumZeroFlat d (N' + 1) := by
          exact section43TotalMomentumZeroProjection_mem_totalMomentumZero d N' ξ
        have hη_dual : η ∈
            DualConeFlat ((flattenCLEquivReal (N' + 1) (d + 1)) ''
              ForwardConeAbs d (N' + 1)) := by
          simpa [η] using section43TotalMomentumZeroProjection_mem_dualCone d N' hdual
        have hη_spec : η ∈ section43WightmanSpectralRegion d (N' + 1) := by
          exact ⟨hη_dual, hη_total⟩
        have hKη : K η = 0 := hK η hη_spec
        have hGtail : G (splitLast (d + 1) (N' * (d + 1)) (e ξ)) = 0 := by
          calc
            G (splitLast (d + 1) (N' * (d + 1)) (e ξ)) =
                F (zeroHeadBlockShift (m := d + 1) (n := N' * (d + 1))
                  (splitLast (d + 1) (N' * (d + 1)) (e ξ))) := by
              simp [G]
            _ = F (e η) := by
              rw [← section43TotalMomentumZeroProjection_headTail d N' ξ]
            _ = K η := by
              simp [F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
            _ = 0 := hKη
        calc
          KE ξ = B (e ξ) := by
            simp [KE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
          _ = 0 := by
            exact headBlockBumpExtension_eq_zero_of_tail_zero
              (d + 1) (N' * (d + 1)) G (e ξ) hGtail

theorem tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant
    (d : ℕ) [NeZero d] {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K)
    (μ : Fin (d + 1))
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    Tflat (section43TotalMomentumCoordMultiplierCLM d N μ K) = 0 := by
  obtain ⟨φflat, hφflat⟩ := physicsFourierFlatCLM_surjective (N * (d + 1)) K
  let v : Fin (N * (d + 1)) → ℝ :=
    section43DiagonalTranslationFlat d N (section43TotalMomentumBasis d μ)
  let L : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    Tflat.comp physicsFourierFlatCLM
  have hline : L (∂_{v} φflat) = 0 := by
    have hquot :
        Filter.Tendsto
          (fun t : ℝ =>
            L (t⁻¹ • (SCV.translateSchwartz (t • v) φflat - φflat)))
          (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (L (∂_{v} φflat))) :=
      (L.continuous.tendsto (∂_{v} φflat)).comp
        (tendsto_diffQuotient_translateSchwartz_zero φflat v)
    have hzero :
        Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
          (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 0) :=
      tendsto_const_nhds
    have heq :
        (fun t : ℝ =>
          L (t⁻¹ • (SCV.translateSchwartz (t • v) φflat - φflat))) =
          fun _ => (0 : ℂ) := by
      funext t
      have htrans : L (SCV.translateSchwartz (t • v) φflat) = L φflat := by
        change
          Tflat (physicsFourierFlatCLM (SCV.translateSchwartz (t • v) φflat)) =
            Tflat (physicsFourierFlatCLM φflat)
        rw [show t • v =
            t • section43DiagonalTranslationFlat d N
              (section43TotalMomentumBasis d μ) by rfl]
        rw [physicsFourierFlatCLM_diagonalBasisTranslate_eq_basisPhaseCLM]
        simpa [section43TotalMomentumBasisPhaseCLM] using
          hphase (t • section43TotalMomentumBasis d μ)
            (physicsFourierFlatCLM φflat)
      let X : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ :=
        SCV.translateSchwartz (t • v) φflat - φflat
      have hreal_smul :
          t⁻¹ • X = ((t⁻¹ : ℂ) • X) := by
        ext ξ
        change t⁻¹ • X ξ = ((t⁻¹ : ℂ) • X ξ)
        rw [Complex.real_smul]
        rw [smul_eq_mul]
        rw [Complex.ofReal_inv]
      change L (t⁻¹ • X) = 0
      rw [hreal_smul]
      rw [L.map_smul, map_sub, sub_eq_zero.mpr htrans, smul_zero]
    have hzero' :
        Filter.Tendsto
          (fun t : ℝ =>
            L (t⁻¹ • (SCV.translateSchwartz (t • v) φflat - φflat)))
          (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 0) := by
      simpa only [heq] using hzero
    exact tendsto_nhds_unique hquot hzero'
  have hderiv :=
    physicsFourierFlatCLM_lineDeriv_diagonalTranslation_eq_coordMultiplier
      (d := d) (N := N) (μ := μ) (φflat := φflat)
  have hcoord_neg :
      Tflat ((-Complex.I) • section43TotalMomentumCoordMultiplierCLM d N μ K) = 0 := by
    rw [← hφflat]
    rw [← hderiv]
    simpa [L] using hline
  rw [Tflat.map_smul] at hcoord_neg
  exact (smul_eq_zero.mp hcoord_neg).resolve_left (by simp)

theorem hasFourierSupportIn_totalMomentumZero_of_phase_invariant
    (d : ℕ) [NeZero d] {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K) :
    HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat := by
  intro φ hφ
  have hvanish_compact : ∀ n : ℕ, Tflat (bumpTruncationRadius φ n) = 0 := by
    intro n
    have hcompact : HasCompactSupport ((bumpTruncationRadius φ n :
        SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) : (Fin (N * (d + 1)) → ℝ) → ℂ) := by
      exact hasCompactSupport_cutoff_mul_radius
        (bumpTruncationRadiusValue n) (bumpTruncationRadiusValue_pos n) φ
    have hzero : ∀ ξ, section43TotalMomentumFlat d N ξ = 0 →
        bumpTruncationRadius φ n ξ = 0 := by
      intro ξ hξ
      have hφzero : φ ξ = 0 := by
        by_contra hne
        exact hφ ξ (Function.mem_support.mpr hne) hξ
      let ψ : (Fin (N * (d + 1)) → ℝ) → ℂ :=
        unitBallBumpSchwartzPiRadius (N * (d + 1))
          (bumpTruncationRadiusValue n)
          (bumpTruncationRadiusValue_pos n)
      have hψtemp : ψ.HasTemperateGrowth := by
        simpa [ψ] using (unitBallBumpSchwartzPiRadius (N * (d + 1))
          (bumpTruncationRadiusValue n)
          (bumpTruncationRadiusValue_pos n)).hasTemperateGrowth
      rw [bumpTruncationRadius]
      rw [SchwartzMap.smulLeftCLM_apply_apply hψtemp]
      simp [hφzero, ψ]
    obtain ⟨H, hH⟩ :=
      exists_eq_sum_totalMomentum_smul_of_vanishes_totalMomentumZero_of_hasCompactSupport
        d N (bumpTruncationRadius φ n) hcompact hzero
    rw [hH]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro μ _hμ
    exact tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant d Tflat hphase μ (H μ)
  have htend : Filter.Tendsto (fun n : ℕ => Tflat (bumpTruncationRadius φ n))
      Filter.atTop (𝓝 (Tflat φ)) :=
    (Tflat.continuous.tendsto φ).comp (SchwartzMap.tendsto_bump_truncation_nhds φ)
  have hzero_tend : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  have heq : (fun n : ℕ => Tflat (bumpTruncationRadius φ n)) = fun _ : ℕ => (0 : ℂ) := by
    funext n
    exact hvanish_compact n
  have hzero_tend' : Filter.Tendsto (fun n : ℕ => Tflat (bumpTruncationRadius φ n))
      Filter.atTop (𝓝 0) := by
    simp [heq, hzero_tend]
  exact tendsto_nhds_unique htend hzero_tend'

theorem hasFourierSupportIn_wightmanSpectralRegion_of_dualCone_and_totalMomentumZero
    (d N : ℕ) [NeZero d]
    {Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ}
    (hdual :
      HasFourierSupportIn
        (DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
        Tflat)
    (htotal :
      HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat := by
  intro K hKsupp
  have hKzero : ∀ ξ, ξ ∈ section43WightmanSpectralRegion d N → K ξ = 0 := by
    intro ξ hξ
    by_contra hne
    exact hKsupp ξ hne hξ
  obtain ⟨KE, hKE_total, hKE_dual⟩ :=
    exists_section43TotalMomentumZeroExtension_vanishes_dualCone d N K hKzero
  have hdiff : Tflat (K - KE) = 0 := by
    apply htotal
    intro ξ hξ hξ_total
    have hzero : (K - KE) ξ = 0 := by
      simp [hKE_total ξ hξ_total]
    exact hξ hzero
  have hKEzero : Tflat KE = 0 := by
    apply hdual
    intro ξ hξ hξ_dual
    exact hξ (hKE_dual ξ hξ_dual)
  have hsub : Tflat K - Tflat KE = 0 := by
    simpa using hdiff
  have hEq : Tflat K = Tflat KE := sub_eq_zero.mp hsub
  rw [hEq, hKEzero]

theorem hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero
    (d N : ℕ) [NeZero d]
    {Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ}
    (hdual :
      HasFourierSupportIn
        (DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
        Tflat)
    (htotal :
      HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat :=
  hasFourierSupportIn_wightmanSpectralRegion_of_dualCone_and_totalMomentumZero d N hdual htotal

end OSReconstruction
