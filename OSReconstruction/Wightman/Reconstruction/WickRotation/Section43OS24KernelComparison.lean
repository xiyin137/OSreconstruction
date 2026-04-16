import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- The raw OS `xiShift` shell for a successor-right split.  This is the shell
used by the already compiled Schwinger-side bridge; it is not asserted to lie
in the forward tube. -/
private def section43RawXiShiftConfig_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)

/-- Chronological reversal of the OS-reflected left block, fixing the right
tail. -/
private def section43LeftBlockReversePerm_succRight
    (n m : ℕ) :
    Equiv.Perm (Fin (n + (m + 1))) :=
  (finSumFinEquiv (m := n) (n := m + 1)).symm.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin (m + 1)))).trans
      (finSumFinEquiv (m := n) (n := m + 1)))

@[simp] private theorem section43LeftBlockReversePerm_succRight_castAdd
    (n m : ℕ) (i : Fin n) :
    section43LeftBlockReversePerm_succRight n m
        (Fin.castAdd (m + 1) i) =
      Fin.castAdd (m + 1) (Fin.rev i) := by
  simp [section43LeftBlockReversePerm_succRight]

@[simp] private theorem section43LeftBlockReversePerm_succRight_natAdd
    (n m : ℕ) (j : Fin (m + 1)) :
    section43LeftBlockReversePerm_succRight n m
        (Fin.natAdd n j) =
      Fin.natAdd n j := by
  simp [section43LeftBlockReversePerm_succRight]

private theorem section43_eq_castAdd_of_val_lt
    {n m : ℕ} {i : Fin (n + (m + 1))} (hi : i.val < n) :
    i = Fin.castAdd (m + 1) (⟨i.val, hi⟩ : Fin n) := by
  ext
  rfl

private theorem section43_eq_natAdd_of_not_val_lt
    {n m : ℕ} {i : Fin (n + (m + 1))} (hi : ¬ i.val < n) :
    i = Fin.natAdd n (⟨i.val - n, by omega⟩ : Fin (m + 1)) := by
  ext
  simp [Fin.natAdd]
  omega

/-- The raw shell after the left block has been put into Borchers
chronological order. -/
private def section43OSBorchersTimeShiftConfig_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43RawXiShiftConfig_succRight d t y
      (section43LeftBlockReversePerm_succRight n m i)

private def section43FirstIndex_succRight
    {n m : ℕ} : Fin (n + (m + 1)) :=
  ⟨0, by omega⟩

/-- A y-dependent diagonal translation making the first imaginary time equal
to `1`; later support lemmas prove the translated configuration is in the
forward tube on OS support. -/
private def section43OSForwardTubeLiftTranslation_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    if μ = 0 then
      Complex.I *
        (((1 : ℝ) -
          (section43OSBorchersTimeShiftConfig_succRight d t y
            section43FirstIndex_succRight 0).im : ℝ) : ℂ)
    else 0

/-- The forward-tube lift used for the Fourier-Laplace side of S5. -/
private def section43OSForwardTubeLift_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43OSBorchersTimeShiftConfig_succRight d t y i +
      section43OSForwardTubeLiftTranslation_succRight d t y

@[simp] private theorem section43OSBorchersTimeShiftConfig_castAdd_time_im_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1)))
    (i : Fin n) :
    (section43OSBorchersTimeShiftConfig_succRight d t y
        (Fin.castAdd (m + 1) i) 0).im =
      y (Fin.castAdd (m + 1) (Fin.rev i)) 0 := by
  have hleft : ¬ n ≤ n - (i.val + 1) := by
    omega
  simp [section43OSBorchersTimeShiftConfig_succRight,
    section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hleft]

@[simp] private theorem section43OSBorchersTimeShiftConfig_natAdd_time_im_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1)))
    (j : Fin (m + 1)) :
    (section43OSBorchersTimeShiftConfig_succRight d t y
        (Fin.natAdd n j) 0).im =
      y (Fin.natAdd n j) 0 + t := by
  simp [section43OSBorchersTimeShiftConfig_succRight,
    section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint]

@[simp] private theorem section43OSForwardTubeLift_first_time_im_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    (section43OSForwardTubeLift_succRight d t y
        (section43FirstIndex_succRight : Fin (n + (m + 1))) 0).im = 1 := by
  simp [section43OSForwardTubeLift_succRight,
    section43OSForwardTubeLiftTranslation_succRight]

private def section43ComplexDiagonalTranslationFlat
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℂ) : Fin (N * (d + 1)) → ℂ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    a p.2

private theorem section43ComplexDiagonalTranslationFlat_pair_eq_totalMomentum
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℂ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    (∑ i : Fin (N * (d + 1)),
        section43ComplexDiagonalTranslationFlat d N a i * (ξ i : ℂ))
      =
    ∑ μ : Fin (d + 1),
      a μ * (section43TotalMomentumFlat d N ξ μ : ℂ) := by
  classical
  calc
    (∑ i : Fin (N * (d + 1)),
        section43ComplexDiagonalTranslationFlat d N a i * (ξ i : ℂ))
        = ∑ p : Fin N × Fin (d + 1),
            a p.2 * (ξ (finProdFinEquiv p) : ℂ) := by
          simpa [section43ComplexDiagonalTranslationFlat] using
            (finProdFinEquiv.sum_comp
              (fun i : Fin (N * (d + 1)) =>
                section43ComplexDiagonalTranslationFlat d N a i *
                  (ξ i : ℂ))).symm
    _ = ∑ k : Fin N, ∑ μ : Fin (d + 1),
            a μ * (ξ (finProdFinEquiv (k, μ)) : ℂ) := by
          simpa using
            (Finset.sum_product (s := (Finset.univ : Finset (Fin N)))
              (t := (Finset.univ : Finset (Fin (d + 1))))
              (f := fun p : Fin N × Fin (d + 1) =>
                a p.2 * (ξ (finProdFinEquiv p) : ℂ)))
    _ = ∑ μ : Fin (d + 1), ∑ k : Fin N,
            a μ * (ξ (finProdFinEquiv (k, μ)) : ℂ) := by
          rw [Finset.sum_comm]
    _ = ∑ μ : Fin (d + 1),
          a μ * (section43TotalMomentumFlat d N ξ μ : ℂ) := by
          simp [section43TotalMomentumFlat, Finset.mul_sum]

private theorem section43OSForwardTubeLift_phase_cancel_of_totalMomentumZero_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (t : ℝ)
    (y : NPointDomain d (n + (m + 1)))
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ_zero :
      ξ ∈ section43TotalMomentumZeroFlat d (n + (m + 1))) :
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight d t y) i *
            (ξ i : ℂ)) =
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight d t y) i *
            (ξ i : ℂ)) := by
  classical
  let N := n + (m + 1)
  let a : Fin (d + 1) → ℂ :=
    section43OSForwardTubeLiftTranslation_succRight d t y
  have hsum :
      (∑ i : Fin (N * (d + 1)),
          flattenCLEquiv N (d + 1)
            (section43OSForwardTubeLift_succRight d t y) i *
            (ξ i : ℂ)) =
        (∑ i : Fin (N * (d + 1)),
          flattenCLEquiv N (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight d t y) i *
            (ξ i : ℂ)) +
        ∑ i : Fin (N * (d + 1)),
          section43ComplexDiagonalTranslationFlat d N a i * (ξ i : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [N, a, section43OSForwardTubeLift_succRight,
      section43ComplexDiagonalTranslationFlat, add_mul]
  have htrans :
      (∑ i : Fin (N * (d + 1)),
          section43ComplexDiagonalTranslationFlat d N a i * (ξ i : ℂ)) = 0 := by
    rw [section43ComplexDiagonalTranslationFlat_pair_eq_totalMomentum]
    have hzero : section43TotalMomentumFlat d N ξ = 0 := by
      simpa [N] using hξ_zero
    simp [hzero]
  rw [hsum, htrans, add_zero]

private theorem section43OSConjTensorProduct_support_left_reflected_ordered_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    timeReflectionN d (splitFirst n (m + 1) y) ∈
      OrderedPositiveTimeRegion d n := by
  have hprod_ne :
      (f.1.osConjTensorProduct g.1 : SchwartzNPoint d (n + (m + 1))) y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have hmul_ne :
      f.1.osConj (splitFirst n (m + 1) y) *
          g.1 (splitLast n (m + 1) y) ≠ 0 := by
    simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply]
      using hprod_ne
  have hleft_ne : f.1.osConj (splitFirst n (m + 1) y) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul_ne).1
  have hf_ne :
      f.1 (timeReflectionN d (splitFirst n (m + 1) y)) ≠ 0 := by
    intro hf_zero
    exact hleft_ne (by simp [SchwartzNPoint.osConj_apply, hf_zero])
  exact f.2 (subset_tsupport _ (Function.mem_support.mpr hf_ne))

private theorem section43OSConjTensorProduct_support_right_ordered_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    splitLast n (m + 1) y ∈
      OrderedPositiveTimeRegion d (m + 1) := by
  have hprod_ne :
      (f.1.osConjTensorProduct g.1 : SchwartzNPoint d (n + (m + 1))) y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have hmul_ne :
      f.1.osConj (splitFirst n (m + 1) y) *
          g.1 (splitLast n (m + 1) y) ≠ 0 := by
    simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply]
      using hprod_ne
  have hright_ne : g.1 (splitLast n (m + 1) y) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul_ne).2
  exact g.2 (subset_tsupport _ (Function.mem_support.mpr hright_ne))

private theorem section43OSBorchersTimeShiftConfig_strictOrdered_of_osSupport_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    StrictMono
      (fun i : Fin (n + (m + 1)) =>
        (section43OSBorchersTimeShiftConfig_succRight d t y i 0).im) := by
  intro i j hij
  have hij_val : i.val < j.val := hij
  have hleftOrd :=
    section43OSConjTensorProduct_support_left_reflected_ordered_succRight
      d f g hy
  have hrightOrd :=
    section43OSConjTensorProduct_support_right_ordered_succRight
      d f g hy
  by_cases hj_left : j.val < n
  · have hi_left : i.val < n := lt_trans hij_val hj_left
    let ii : Fin n := ⟨i.val, hi_left⟩
    let jj : Fin n := ⟨j.val, hj_left⟩
    have hi_eq : i = Fin.castAdd (m + 1) ii :=
      section43_eq_castAdd_of_val_lt (m := m) hi_left
    have hj_eq : j = Fin.castAdd (m + 1) jj :=
      section43_eq_castAdd_of_val_lt (m := m) hj_left
    have hij_tail : ii < jj := by
      change i.val < j.val
      exact hij_val
    have hrev : Fin.rev jj < Fin.rev ii := by
      rw [Fin.rev_lt_iff]
      simpa [ii, jj] using hij_tail
    have hneg :=
      (hleftOrd (Fin.rev jj)).2 (Fin.rev ii) hrev
    have hneg' :
        -(y (Fin.castAdd (m + 1) (Fin.rev jj)) 0) <
          -(y (Fin.castAdd (m + 1) (Fin.rev ii)) 0) := by
      simpa [timeReflectionN, timeReflection, splitFirst] using hneg
    rw [hi_eq, hj_eq]
    simp
    nlinarith
  · by_cases hi_left : i.val < n
    · let ii : Fin n := ⟨i.val, hi_left⟩
      let jj : Fin (m + 1) := ⟨j.val - n, by omega⟩
      have hi_eq : i = Fin.castAdd (m + 1) ii :=
        section43_eq_castAdd_of_val_lt (m := m) hi_left
      have hj_eq : j = Fin.natAdd n jj :=
        section43_eq_natAdd_of_not_val_lt (m := m) hj_left
      have hleft_pos : 0 <
          timeReflectionN d (splitFirst n (m + 1) y) (Fin.rev ii) 0 :=
        (hleftOrd (Fin.rev ii)).1
      have hleft_neg :
          y (Fin.castAdd (m + 1) (Fin.rev ii)) 0 < 0 := by
        have hneg : 0 < -(y (Fin.castAdd (m + 1) (Fin.rev ii)) 0) := by
          simpa [timeReflectionN, timeReflection, splitFirst] using hleft_pos
        nlinarith
      have hright_pos : 0 < y (Fin.natAdd n jj) 0 :=
        (hrightOrd jj).1
      rw [hi_eq, hj_eq]
      simp
      nlinarith
    · let ii : Fin (m + 1) := ⟨i.val - n, by omega⟩
      let jj : Fin (m + 1) := ⟨j.val - n, by omega⟩
      have hi_eq : i = Fin.natAdd n ii :=
        section43_eq_natAdd_of_not_val_lt (m := m) hi_left
      have hj_eq : j = Fin.natAdd n jj :=
        section43_eq_natAdd_of_not_val_lt (m := m) hj_left
      have hij_tail : ii < jj := by
        change i.val - n < j.val - n
        omega
      have hright_lt :=
        (hrightOrd ii).2 jj hij_tail
      have hright_lt' :
          y (Fin.natAdd n ii) 0 < y (Fin.natAdd n jj) 0 := by
        simpa [splitLast] using hright_lt
      rw [hi_eq, hj_eq]
      simp
      nlinarith

private def section43OSForwardTubeLiftRealConfig_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    NPointDomain d (n + (m + 1)) :=
  fun i μ =>
    if μ = 0 then
      (section43OSForwardTubeLift_succRight d t y i 0).im
    else
      (section43OSForwardTubeLift_succRight d t y i μ).re

private theorem section43OSForwardTubeLift_eq_wickRotatePoint_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    section43OSForwardTubeLift_succRight d t y =
      fun i => wickRotatePoint
        (section43OSForwardTubeLiftRealConfig_succRight d t y i) := by
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hi : n ≤ ((section43LeftBlockReversePerm_succRight n m) i).val
    · by_cases h0 :
        n ≤ ((section43LeftBlockReversePerm_succRight n m)
          (section43FirstIndex_succRight : Fin (n + (m + 1)))).val
      · simp [section43OSForwardTubeLiftRealConfig_succRight,
          section43OSForwardTubeLift_succRight,
          section43OSForwardTubeLiftTranslation_succRight,
          section43OSBorchersTimeShiftConfig_succRight,
          section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hi, h0]
        ring_nf
      · simp [section43OSForwardTubeLiftRealConfig_succRight,
          section43OSForwardTubeLift_succRight,
          section43OSForwardTubeLiftTranslation_succRight,
          section43OSBorchersTimeShiftConfig_succRight,
          section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hi, h0]
        ring_nf
    · by_cases h0 :
        n ≤ ((section43LeftBlockReversePerm_succRight n m)
          (section43FirstIndex_succRight : Fin (n + (m + 1)))).val
      · simp [section43OSForwardTubeLiftRealConfig_succRight,
          section43OSForwardTubeLift_succRight,
          section43OSForwardTubeLiftTranslation_succRight,
          section43OSBorchersTimeShiftConfig_succRight,
          section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hi, h0]
        ring_nf
      · simp [section43OSForwardTubeLiftRealConfig_succRight,
          section43OSForwardTubeLift_succRight,
          section43OSForwardTubeLiftTranslation_succRight,
          section43OSBorchersTimeShiftConfig_succRight,
          section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hi, h0]
        ring_nf
  · simp [section43OSForwardTubeLiftRealConfig_succRight,
      section43OSForwardTubeLift_succRight,
      section43OSForwardTubeLiftTranslation_succRight,
      section43OSBorchersTimeShiftConfig_succRight,
      section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint, hμ]

private theorem section43OSForwardTubeLift_mem_forwardTube_of_osSupport_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    section43OSForwardTubeLift_succRight d t y ∈
      TubeDomainSetPi (ForwardConeAbs d (n + (m + 1))) := by
  let N := n + (m + 1)
  let xs : NPointDomain d N :=
    section43OSForwardTubeLiftRealConfig_succRight d t y
  have hborch_strict :=
    section43OSBorchersTimeShiftConfig_strictOrdered_of_osSupport_succRight
      d f g ht hy
  have hlift_eq :=
    section43OSForwardTubeLift_eq_wickRotatePoint_succRight d t y
  have hord : ∀ k j : Fin N, k < j → xs k 0 < xs j 0 := by
    intro k j hkj
    have hstrict := hborch_strict hkj
    dsimp [xs, section43OSForwardTubeLiftRealConfig_succRight]
    simp [section43OSForwardTubeLift_succRight]
    nlinarith
  have hpos : ∀ k : Fin N, xs k 0 > 0 := by
    intro k
    let first : Fin N := section43FirstIndex_succRight
    by_cases hk : k = first
    · subst hk
      have hfirst :=
        section43OSForwardTubeLift_first_time_im_succRight
          (d := d) (n := n) (m := m) t y
      change (section43OSForwardTubeLift_succRight d t y first 0).im > 0
      rw [hfirst]
      norm_num
    · have hkval : k.val ≠ 0 := by
        intro hk0
        apply hk
        ext
        simpa [first, section43FirstIndex_succRight] using hk0
      have hfirst_lt : first < k := by
        change first.val < k.val
        simpa [first, section43FirstIndex_succRight] using
          Nat.pos_of_ne_zero hkval
      have hfirst_time : xs first 0 = 1 := by
        have hfirst :=
          section43OSForwardTubeLift_first_time_im_succRight
            (d := d) (n := n) (m := m) t y
        change (section43OSForwardTubeLift_succRight d t y first 0).im = 1
        exact hfirst
      have hk_gt := hord first k hfirst_lt
      nlinarith
  have hft : (fun k => wickRotatePoint (xs k)) ∈ ForwardTube d N :=
    euclidean_ordered_in_forwardTube (d := d) (n := N) xs hord hpos
  rw [hlift_eq]
  simpa [N, TubeDomainSetPi, forwardTube_eq_imPreimage] using hft

private theorem section43OSForwardTubeLift_multiDimPsiZExt_apply_of_spectralRegion_succRight
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness OS lgc (n + (m + 1)) Tflat)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1)))
    (y : NPointDomain d (n + (m + 1)))
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    multiDimPsiZExt
      ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
        ForwardConeAbs d (n + (m + 1)))
      hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
      hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
      (flattenCLEquiv (n + (m + 1)) (d + 1)
        (section43OSForwardTubeLift_succRight d t y)) ξ =
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight d t y) i *
            (ξ i : ℂ)) := by
  let N := n + (m + 1)
  have hξ_spec :
      ξ ∈
        DualConeFlat ((flattenCLEquivReal N (d + 1)) ''
            ForwardConeAbs d N) ∩
          section43TotalMomentumZeroFlat d N := by
    simpa [N, section43WightmanSpectralRegion] using hξ
  have hz_tube :
      section43OSForwardTubeLift_succRight d t y ∈
        TubeDomainSetPi (ForwardConeAbs d N) := by
    simpa [N] using
      section43OSForwardTubeLift_mem_forwardTube_of_osSupport_succRight
        (d := d) f g ht hy
  have hz_flat :
      flattenCLEquiv N (d + 1)
          (section43OSForwardTubeLift_succRight d t y) ∈
        SCV.TubeDomain
          ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) := by
    exact flattenCLEquiv_mem_tubeDomain_image (n := N) (r := d) hz_tube
  suffices h :
      multiDimPsiZExt
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
        hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
        hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
        (flattenCLEquiv N (d + 1)
          (section43OSForwardTubeLift_succRight d t y)) ξ =
      Complex.exp
        (Complex.I *
          ∑ i : Fin (N * (d + 1)),
            flattenCLEquiv N (d + 1)
              (section43OSBorchersTimeShiftConfig_succRight d t y) i *
              (ξ i : ℂ)) by
    simpa [N] using h
  calc
    multiDimPsiZExt
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
        hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
        hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
        (flattenCLEquiv N (d + 1)
          (section43OSForwardTubeLift_succRight d t y)) ξ
        =
      Complex.exp
        (Complex.I *
          ∑ i : Fin (N * (d + 1)),
            flattenCLEquiv N (d + 1)
              (section43OSForwardTubeLift_succRight d t y) i *
              (ξ i : ℂ)) := by
          exact
            multiDimPsiZExt_apply_of_mem_dualCone
              ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
              hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
              hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
              (flattenCLEquiv N (d + 1)
                (section43OSForwardTubeLift_succRight d t y))
              hz_flat hξ_spec.1
    _ =
      Complex.exp
        (Complex.I *
          ∑ i : Fin (N * (d + 1)),
            flattenCLEquiv N (d + 1)
              (section43OSBorchersTimeShiftConfig_succRight d t y) i *
              (ξ i : ℂ)) := by
          simpa [N] using
            section43OSForwardTubeLift_phase_cancel_of_totalMomentumZero_succRight
              (d := d) (n := n) (m := m) t y ξ
              (by simpa [N] using hξ_spec.2)

/-- The local Section 4.3 flat time-shift direction agrees with the semigroup
time-shift convention used by `timeShiftFlatOrbit`. -/
theorem section43FlatTimeShiftDirection_eq_flatTimeShiftDirection
    (d m : ℕ) :
    section43FlatTimeShiftDirection d m = flatTimeShiftDirection d m := by
  ext i
  rfl

/-- The embedded successor-right time-shift direction agrees with the
`timeShiftFlatOrbit` direction from the boundary-value layer. -/
theorem section43SuccRightTimeShiftFlatDirection_eq_flatTimeShiftDirection
    (d n m : ℕ) [NeZero d] :
    section43SuccRightTimeShiftFlatDirection d n m =
      castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1))) := by
  ext i
  simp [section43SuccRightTimeShiftFlatDirection,
    section43FlatTimeShiftDirection_eq_flatTimeShiftDirection]

/-- The `eta` CLM is exactly `-lambda/(2π)` for the
`timeShiftFlatOrbit` pairing convention. -/
theorem section43SuccRightEtaCLM_eq_timeShiftFlatOrbit_eta
    (d n m : ℕ) [NeZero d]
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    section43SuccRightEtaCLM d n m ξ =
      -(∑ i : Fin ((n + (m + 1)) * (d + 1)),
          (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
            (zeroHeadBlockShift
              (m := n * (d + 1)) (n := (m + 1) * (d + 1))
              (flatTimeShiftDirection d (m + 1)))) i) * ξ i) /
        (2 * Real.pi) := by
  rw [section43SuccRightEtaCLM_apply]
  rw [section43SuccRightTimeShiftFlatDirection_eq_flatTimeShiftDirection]

private theorem section43SuccRightEtaCLM_nonneg_of_mem_dualCone
    (d n m : ℕ) [NeZero d]
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1)))) :
    0 ≤ section43SuccRightEtaCLM d n m ξ := by
  have hlam :=
    zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m + 1) (ξ := ξ) hξ
  have hlam' :
      ∑ i : Fin ((n + (m + 1)) * (d + 1)),
        section43SuccRightTimeShiftFlatDirection d n m i * ξ i ≤ 0 := by
    simpa [section43SuccRightTimeShiftFlatDirection_eq_flatTimeShiftDirection]
      using hlam
  rw [section43SuccRightEtaCLM_apply]
  exact div_nonneg (neg_nonneg.mpr hlam') Real.two_pi_pos.le

private theorem section43SuccRightEtaCLM_nonneg_of_mem_spectralRegion
    (d n m : ℕ) [NeZero d]
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    0 ≤ section43SuccRightEtaCLM d n m ξ :=
  section43SuccRightEtaCLM_nonneg_of_mem_dualCone d n m hξ.1

private theorem section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let lamξ : ℝ :=
      ∑ i : Fin ((n + (m + 1)) * (d + 1)),
        (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
          (zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) =
      section43PsiZTimeTest t ht ηξ := by
  let lamξ : ℝ :=
    ∑ i : Fin ((n + (m + 1)) * (d + 1)),
      (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  let ηξ : ℝ := -lamξ / (2 * Real.pi)
  have heta :
      section43SuccRightEtaCLM d n m ξ = ηξ := by
    dsimp [ηξ, lamξ]
    exact section43SuccRightEtaCLM_eq_timeShiftFlatOrbit_eta d n m ξ
  have hη_nonneg : 0 ≤ ηξ := by
    rw [← heta]
    exact section43SuccRightEtaCLM_nonneg_of_mem_spectralRegion d n m hξ
  change Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) =
    section43PsiZTimeTest t ht ηξ
  rw [section43PsiZTimeTest_apply]
  rw [SCV.psiZ_eq_exp_of_nonneg hη_nonneg]
  congr 1
  have harg :
      Complex.I * (2 * (Real.pi : ℂ) * ((t : ℂ) * Complex.I)) =
        -(2 * (Real.pi : ℂ) * (t : ℂ)) := by
    rw [show
      2 * (Real.pi : ℂ) * ((t : ℂ) * Complex.I) =
        (2 * (Real.pi : ℂ) * (t : ℂ)) * Complex.I by ring]
    rw [show
      Complex.I * (2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I) =
        (2 * (Real.pi : ℂ) * (t : ℂ)) * (Complex.I * Complex.I) by ring]
    rw [Complex.I_mul_I]
    ring
  rw [harg]

/-- The explicit time-shift/`ψ_Z` Fourier kernel agrees with the OS I `(4.24)`
kernel on the Section 4.3 Wightman spectral region. -/
theorem section43_timeShiftKernel_psiZ_eq_OS24Kernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (KψZ_t : SchwartzMap
      (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ) :
    Set.EqOn
      (fun ξ => KψZ_t ξ)
      (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
      (section43WightmanSpectralRegion d (n + (m + 1))) := by
  intro ξ hξ
  let ψZt : SchwartzMap ℝ ℂ := section43PsiZTimeTest t ht
  let base : ℂ :=
    physicsFourierFlatCLM
      (reindexSchwartzFin
        (Nat.add_mul n (m + 1) (d + 1)).symm
        (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (flattenSchwartzNPoint (d := d) ψ)))) ξ
  let lam : ℝ :=
    ∑ i : Fin ((n + (m + 1)) * (d + 1)),
      (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  have hbase :
      base =
        star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
              (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) *
          (section43FrequencyRepresentative (d := d) (m + 1) ψ)
            (section43RightTailBlock d n (m + 1)
              (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)) := by
    dsimp [base]
    simpa using
      physicsFourierFlatCLM_borchersTensor_eq_frequencyRepresentatives_on_spectralRegion
        (d := d) (n := n) (m := m) φ ψ hξ
  have heta :
      section43SuccRightEtaCLM d n m ξ = -lam / (2 * Real.pi) := by
    dsimp [lam]
    exact section43SuccRightEtaCLM_eq_timeShiftFlatOrbit_eta d n m ξ
  have hphase :
      (∫ τ : ℝ,
          timeShiftFlatOrbit (d := d) φ ψ τ ξ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) τ) =
        section43HorizontalPhasePairingCLM base lam
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) := by
    calc
      (∫ τ : ℝ,
          timeShiftFlatOrbit (d := d) φ ψ τ ξ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) τ)
          =
        ∫ τ : ℝ,
          base *
            (Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) τ) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with τ
            rw [timeShiftFlatOrbit_apply_phase]
            dsimp only [base, lam]
            ac_rfl
      _ =
        base *
          ∫ τ : ℝ,
            Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) τ := by
            exact
              MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun τ : ℝ =>
                  Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                    (SchwartzMap.fourierTransformCLM ℂ ψZt) τ)
      _ =
        section43HorizontalPhasePairingCLM base lam
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) := by
            exact
              (section43HorizontalPhasePairingCLM_apply base lam
                ((SchwartzMap.fourierTransformCLM ℂ) ψZt)).symm
  calc
    KψZ_t ξ
        =
      ∫ τ : ℝ,
        timeShiftFlatOrbit (d := d) φ ψ τ ξ *
          (SchwartzMap.fourierTransformCLM ℂ (section43PsiZTimeTest t ht)) τ :=
          hKψZ_eval ξ
    _ = section43HorizontalPhasePairingCLM base lam
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) := by
          simpa [ψZt] using hphase
    _ = base * ψZt (-lam / (2 * Real.pi)) := by
          rw [section43HorizontalPhasePairingCLM_fourierTransform]
    _ =
      (star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
              (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1)
            (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) *
        ψZt (-lam / (2 * Real.pi)) := by
          rw [hbase]
    _ =
      ψZt (-lam / (2 * Real.pi)) *
        (star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
              (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1)
            (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) := by
          rw [mul_comm]
    _ = section43OS24Kernel_succRight d n m φ ψ t ht ξ := by
          rw [section43OS24Kernel_succRight_apply_of_mem_spectralRegion
            (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) ht ξ hξ]
          dsimp [section43OS24VisibleKernel_succRight, ψZt]
          rw [heta]

end OSReconstruction
