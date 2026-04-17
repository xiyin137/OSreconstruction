import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge
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

/-- Split an absolute `NPointDomain` block into its first and last point
blocks.  This is the concrete product equivalence used by the Section 4.3
Fubini step. -/
def section43NPointProductSplitMeasurableEquiv
    (d n r : ℕ) :
    NPointDomain d (n + r) ≃ᵐ (NPointDomain d n × NPointDomain d r) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin n ⊕ Fin r => SpacetimeDim d))

theorem section43NPointProductSplitMeasurableEquiv_measurePreserving
    (d n r : ℕ) :
    MeasureTheory.MeasurePreserving
      (section43NPointProductSplitMeasurableEquiv d n r)
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d (n + r)))
      ((MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d r))) := by
  let e1 := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
  have he1 : MeasureTheory.MeasurePreserving e1 MeasureTheory.volume MeasureTheory.volume := by
    simpa [e1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin (n + r) => SpacetimeDim d)
        (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)))
  have he2 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin n ⊕ Fin r => SpacetimeDim d))
      MeasureTheory.volume
      ((MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d r))) := by
    simpa using
      (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Fin n ⊕ Fin r => SpacetimeDim d))
  simpa [section43NPointProductSplitMeasurableEquiv, e1] using he2.comp (he1.symm e1)

private theorem section43NPointProductSplitMeasurableEquiv_fst_apply
    (d n r : ℕ) (x : NPointDomain d (n + r)) (i : Fin n) :
    (section43NPointProductSplitMeasurableEquiv d n r x).1 i =
      x (Fin.castAdd r i) := by
  rw [section43NPointProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))).symm x) (Sum.inl i) =
    x (Fin.castAdd r i)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (n + r) => SpacetimeDim d)
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
    ((Equiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))).symm x)
    (Sum.inl i)
  rw [← h]
  simp [finSumFinEquiv_apply_left]

private theorem section43NPointProductSplitMeasurableEquiv_snd_apply
    (d n r : ℕ) (x : NPointDomain d (n + r)) (j : Fin r) :
    (section43NPointProductSplitMeasurableEquiv d n r x).2 j =
      x (Fin.natAdd n j) := by
  rw [section43NPointProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))).symm x) (Sum.inr j) =
    x (Fin.natAdd n j)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (n + r) => SpacetimeDim d)
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
    ((Equiv.piCongrLeft (fun _ : Fin (n + r) => SpacetimeDim d)
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))).symm x)
    (Sum.inr j)
  rw [← h]
  simp [finSumFinEquiv_apply_right]

private theorem section43NPointProductSplitMeasurableEquiv_fst_eq_splitFirst
    (d n r : ℕ) (x : NPointDomain d (n + r)) :
    (section43NPointProductSplitMeasurableEquiv d n r x).1 =
      splitFirst n r x := by
  ext i μ
  exact congrFun (section43NPointProductSplitMeasurableEquiv_fst_apply d n r x i) μ

private theorem section43NPointProductSplitMeasurableEquiv_snd_eq_splitLast
    (d n r : ℕ) (x : NPointDomain d (n + r)) :
    (section43NPointProductSplitMeasurableEquiv d n r x).2 =
      splitLast n r x := by
  ext j μ
  exact congrFun (section43NPointProductSplitMeasurableEquiv_snd_apply d n r x j) μ

private theorem section43NPointProductSplitMeasurableEquiv_symm_castAdd
    (d n r : ℕ) (xL : NPointDomain d n) (xR : NPointDomain d r)
    (i : Fin n) :
    (section43NPointProductSplitMeasurableEquiv d n r).symm (xL, xR)
        (Fin.castAdd r i) =
      xL i := by
  let e := section43NPointProductSplitMeasurableEquiv d n r
  have hcoord :
      (e (e.symm (xL, xR))).1 i = xL i :=
    congrFun (congrArg Prod.fst (e.apply_symm_apply (xL, xR))) i
  have hsplit :
      (e (e.symm (xL, xR))).1 i =
        e.symm (xL, xR) (Fin.castAdd r i) :=
    section43NPointProductSplitMeasurableEquiv_fst_apply d n r
      (e.symm (xL, xR)) i
  exact hsplit.symm.trans hcoord

private theorem section43NPointProductSplitMeasurableEquiv_symm_natAdd
    (d n r : ℕ) (xL : NPointDomain d n) (xR : NPointDomain d r)
    (j : Fin r) :
    (section43NPointProductSplitMeasurableEquiv d n r).symm (xL, xR)
        (Fin.natAdd n j) =
      xR j := by
  let e := section43NPointProductSplitMeasurableEquiv d n r
  have hcoord :
      (e (e.symm (xL, xR))).2 j = xR j :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply (xL, xR))) j
  have hsplit :
      (e (e.symm (xL, xR))).2 j =
        e.symm (xL, xR) (Fin.natAdd n j) :=
    section43NPointProductSplitMeasurableEquiv_snd_apply d n r
      (e.symm (xL, xR)) j
  exact hsplit.symm.trans hcoord

private theorem section43NPointProductSplitMeasurableEquiv_symm_continuous
    (d n r : ℕ) :
    Continuous
      ((section43NPointProductSplitMeasurableEquiv d n r).symm :
        NPointDomain d n × NPointDomain d r → NPointDomain d (n + r)) := by
  apply continuous_pi
  intro i
  by_cases hi : i.val < n
  · let ii : Fin n := ⟨i.val, hi⟩
    have hi_eq : i = Fin.castAdd r ii := by
      ext
      rfl
    have hcoord :
        (fun p : NPointDomain d n × NPointDomain d r =>
            (section43NPointProductSplitMeasurableEquiv d n r).symm p i) =
          fun p => p.1 ii := by
      funext p
      rw [hi_eq]
      exact section43NPointProductSplitMeasurableEquiv_symm_castAdd
        d n r p.1 p.2 ii
    rw [hcoord]
    exact (continuous_apply ii).comp continuous_fst
  · let jj : Fin r := ⟨i.val - n, by omega⟩
    have hi_eq : i = Fin.natAdd n jj := by
      ext
      simp [jj, Fin.natAdd]
      omega
    have hcoord :
        (fun p : NPointDomain d n × NPointDomain d r =>
            (section43NPointProductSplitMeasurableEquiv d n r).symm p i) =
          fun p => p.2 jj := by
      funext p
      rw [hi_eq]
      exact section43NPointProductSplitMeasurableEquiv_symm_natAdd
        d n r p.1 p.2 jj
    rw [hcoord]
    exact (continuous_apply jj).comp continuous_snd

/-- The raw shell after the left block has been put into Borchers
chronological order. -/
def section43OSBorchersTimeShiftConfig_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43RawXiShiftConfig_succRight d t y
      (section43LeftBlockReversePerm_succRight n m i)

private def section43FirstIndex_succRight
    {n m : ℕ} : Fin (n + (m + 1)) :=
  ⟨0, by omega⟩

private theorem section43OSBorchersTimeShiftConfig_splitLeft_timeReflection_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1))
    (i : Fin n) (μ : Fin (d + 1)) :
    let r : ℕ := m + 1
    let y : NPointDomain d (n + r) :=
      (section43NPointProductSplitMeasurableEquiv d n r).symm
        (timeReflectionN d xL, xR)
    section43OSBorchersTimeShiftConfig_succRight (d := d) t y
        (Fin.castAdd r i) μ =
      wickRotatePoint (timeReflection d (xL (Fin.rev i))) μ := by
  have hleft : ¬ n ≤ n - (i.val + 1) := by omega
  simp [section43OSBorchersTimeShiftConfig_succRight,
    section43RawXiShiftConfig_succRight, xiShift, hleft,
    section43NPointProductSplitMeasurableEquiv_symm_castAdd, timeReflectionN]

private theorem section43OSBorchersTimeShiftConfig_splitRight_shift_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1))
    (j : Fin (m + 1)) (μ : Fin (d + 1)) :
    let r : ℕ := m + 1
    let y : NPointDomain d (n + r) :=
      (section43NPointProductSplitMeasurableEquiv d n r).symm
        (timeReflectionN d xL, xR)
    section43OSBorchersTimeShiftConfig_succRight (d := d) t y
        (Fin.natAdd n j) μ =
      if μ = 0 then
        wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
      else
        wickRotatePoint (xR j) μ := by
  by_cases hμ : μ = 0
  · subst μ
    simp [section43OSBorchersTimeShiftConfig_succRight,
      section43RawXiShiftConfig_succRight, xiShift,
      section43NPointProductSplitMeasurableEquiv_symm_natAdd]
  · simp [section43OSBorchersTimeShiftConfig_succRight,
      section43RawXiShiftConfig_succRight, xiShift, hμ,
      section43NPointProductSplitMeasurableEquiv_symm_natAdd]

theorem section43TimeReflectionN_involutive
    (d : ℕ) [NeZero d] {n : ℕ} (x : NPointDomain d n) :
    timeReflectionN d (timeReflectionN d x) = x := by
  ext i μ
  exact congrFun (timeReflection_timeReflection d (x i)) μ

private theorem section43OSConjTensorProduct_split_timeReflection_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d (m + 1))
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1)) :
    let y : NPointDomain d (n + (m + 1)) :=
      (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
        (timeReflectionN d xL, xR)
    (f.osConjTensorProduct g) y =
      star (f xL) * g xR := by
  let y : NPointDomain d (n + (m + 1)) :=
    (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
      (timeReflectionN d xL, xR)
  have hfirst : splitFirst n (m + 1) y = timeReflectionN d xL := by
    ext i μ
    exact congrFun
      (section43NPointProductSplitMeasurableEquiv_symm_castAdd
        d n (m + 1) (timeReflectionN d xL) xR i) μ
  have hlast : splitLast n (m + 1) y = xR := by
    ext j μ
    exact congrFun
      (section43NPointProductSplitMeasurableEquiv_symm_natAdd
        d n (m + 1) (timeReflectionN d xL) xR j) μ
  change (f.osConjTensorProduct g) y = star (f xL) * g xR
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, hfirst, hlast, section43TimeReflectionN_involutive]

private theorem section43OSBorchersPhase_left_sum_eq_neg_star_sum
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (xL : NPointDomain d n) :
    (∑ a : Fin (n * (d + 1)),
        flattenCLEquiv n (d + 1)
          (fun k => wickRotatePoint (timeReflection d (xL (Fin.rev k)))) a *
        (section43SplitLeftFlat d n r ξ a : ℂ)) =
      -star
        (∑ a : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (xL k)) a *
          (section43NegRevFlat d n
            (section43SplitLeftFlat d n r ξ) a : ℂ)) := by
  classical
  calc
    (∑ a : Fin (n * (d + 1)),
        flattenCLEquiv n (d + 1)
          (fun k => wickRotatePoint (timeReflection d (xL (Fin.rev k)))) a *
        (section43SplitLeftFlat d n r ξ a : ℂ))
        =
      ∑ p : Fin n × Fin (d + 1),
        star (wickRotatePoint (xL (Fin.rev p.1)) p.2) *
        (section43SplitLeftFlat d n r ξ (finProdFinEquiv p) : ℂ) := by
          rw [← finProdFinEquiv.sum_comp]
          refine Finset.sum_congr rfl ?_
          intro p _hp
          simp only [flattenCLEquiv_apply, finProdFinEquiv.symm_apply_apply]
          rw [wickRotatePoint_timeReflection]
          rfl
    _ =
      ∑ p : Fin n × Fin (d + 1),
        star (wickRotatePoint (xL p.1) p.2) *
        (section43SplitLeftFlat d n r ξ
          (finProdFinEquiv (Fin.rev p.1, p.2)) : ℂ) := by
          refine Finset.sum_bij
            (fun p (_hp : p ∈ (Finset.univ :
                Finset (Fin n × Fin (d + 1)))) =>
              (Fin.rev p.1, p.2)) ?hmem ?hinj ?hsurj ?hval
          · intro p _hp
            simp
          · intro a _ha b _hb h
            have h' : (Fin.rev a.1, a.2) = (Fin.rev b.1, b.2) := by
              simpa using h
            injection h' with hfst hsnd
            apply Prod.ext
            · exact Fin.rev_injective hfst
            · exact hsnd
          · intro b _hb
            exact ⟨(Fin.rev b.1, b.2), by simp⟩
          · intro p _hp
            simp
    _ =
      -star
        (∑ a : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (xL k)) a *
          (section43NegRevFlat d n
            (section43SplitLeftFlat d n r ξ) a : ℂ)) := by
          rw [← finProdFinEquiv.sum_comp]
          simp [flattenCLEquiv_apply, section43NegRevFlat, section43SplitLeftFlat]

private theorem section43OSBorchersPhase_right_sum_eq_sum_add_tail
    (d n r : ℕ) [NeZero d]
    (t : ℝ)
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (xR : NPointDomain d r) :
    (∑ a : Fin (r * (d + 1)),
        flattenCLEquiv r (d + 1)
          (fun j μ =>
            if μ = 0 then
              wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
            else
              wickRotatePoint (xR j) μ) a *
        (section43SplitRightFlat d n r ξ a : ℂ)) =
      (∑ a : Fin (r * (d + 1)),
          flattenCLEquiv r (d + 1)
            (fun j => wickRotatePoint (xR j)) a *
          (section43SplitRightFlat d n r ξ a : ℂ)) +
        ((t : ℂ) * Complex.I) *
          (∑ j : Fin r,
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) := by
  classical
  let c : ℂ := (t : ℂ) * Complex.I
  let B : Fin r × Fin (d + 1) → ℂ := fun p =>
    (section43SplitRightFlat d n r ξ (finProdFinEquiv p) : ℂ)
  have htail :
      (∑ p : Fin r × Fin (d + 1),
          if p.2 = 0 then c * B p else 0) =
        c *
          (∑ j : Fin r,
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) := by
    calc
      (∑ p : Fin r × Fin (d + 1),
          if p.2 = 0 then c * B p else 0)
          =
        ∑ j : Fin r,
          ∑ μ : Fin (d + 1), if μ = 0 then c * B (j, μ) else 0 := by
            simpa using
              (Finset.sum_product
                (s := (Finset.univ : Finset (Fin r)))
                (t := (Finset.univ : Finset (Fin (d + 1))))
                (f := fun p : Fin r × Fin (d + 1) =>
                  if p.2 = 0 then c * B p else 0))
      _ = ∑ j : Fin r, c * B (j, 0) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [Finset.sum_eq_single (0 : Fin (d + 1))]
            · rfl
            · intro μ _hμ hμ0
              simp [hμ0]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ _))
      _ =
        c *
          (∑ j : Fin r,
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) := by
            simp [B, section43SplitRightFlat_apply, Finset.mul_sum]
  calc
    (∑ a : Fin (r * (d + 1)),
        flattenCLEquiv r (d + 1)
          (fun j μ =>
            if μ = 0 then
              wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
            else
              wickRotatePoint (xR j) μ) a *
        (section43SplitRightFlat d n r ξ a : ℂ))
        =
      ∑ p : Fin r × Fin (d + 1),
        ((if p.2 = 0 then
            wickRotatePoint (xR p.1) p.2 + c
          else
            wickRotatePoint (xR p.1) p.2) *
          B p) := by
          rw [← finProdFinEquiv.sum_comp]
          simp [flattenCLEquiv_apply, B, c]
    _ =
      ∑ p : Fin r × Fin (d + 1),
        (wickRotatePoint (xR p.1) p.2 * B p +
          if p.2 = 0 then c * B p else 0) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          by_cases hμ : p.2 = 0
          · simp [hμ, add_mul]
          · simp [hμ]
    _ =
      (∑ p : Fin r × Fin (d + 1),
        wickRotatePoint (xR p.1) p.2 * B p) +
      (∑ p : Fin r × Fin (d + 1),
        if p.2 = 0 then c * B p else 0) := by
          rw [Finset.sum_add_distrib]
    _ =
      (∑ p : Fin r × Fin (d + 1),
        wickRotatePoint (xR p.1) p.2 * B p) +
        c *
          (∑ j : Fin r,
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) := by
          rw [htail]
    _ =
      (∑ a : Fin (r * (d + 1)),
          flattenCLEquiv r (d + 1)
            (fun j => wickRotatePoint (xR j)) a *
          (section43SplitRightFlat d n r ξ a : ℂ)) +
        ((t : ℂ) * Complex.I) *
          (∑ j : Fin r,
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) := by
          rw [← finProdFinEquiv.sum_comp]
          simp [flattenCLEquiv_apply, B, c]

private theorem section43OSBorchersPhase_full_sum_eq_factorized_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} (t : ℝ)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1)) :
    let y : NPointDomain d (n + (m + 1)) :=
      (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
        (timeReflectionN d xL, xR)
    (∑ a : Fin ((n + (m + 1)) * (d + 1)),
        flattenCLEquiv (n + (m + 1)) (d + 1)
          (section43OSBorchersTimeShiftConfig_succRight
            (d := d) t y) a *
        (ξ a : ℂ)) =
      -star
        (∑ a : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (xL k)) a *
          (section43NegRevFlat d n
            (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)) +
        ((∑ a : Fin ((m + 1) * (d + 1)),
            flattenCLEquiv (m + 1) (d + 1)
              (fun k => wickRotatePoint (xR k)) a *
            (section43SplitRightFlat d n (m + 1) ξ a : ℂ)) +
          ((t : ℂ) * Complex.I) *
            (∑ j : Fin (m + 1),
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ))) := by
  classical
  let y : NPointDomain d (n + (m + 1)) :=
    (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
      (timeReflectionN d xL, xR)
  let leftShifted : ℂ :=
    ∑ a : Fin (n * (d + 1)),
      flattenCLEquiv n (d + 1)
        (fun k => wickRotatePoint (timeReflection d (xL (Fin.rev k)))) a *
      (section43SplitLeftFlat d n (m + 1) ξ a : ℂ)
  let rightShifted : ℂ :=
    ∑ a : Fin ((m + 1) * (d + 1)),
      flattenCLEquiv (m + 1) (d + 1)
        (fun j μ =>
          if μ = 0 then
            wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
          else
            wickRotatePoint (xR j) μ) a *
      (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
  have hleft :
      (∑ i : Fin n,
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.castAdd (m + 1) i) μ *
              (ξ (finProdFinEquiv
                (Fin.castAdd (m + 1) i, μ)) : ℂ)) =
        leftShifted := by
    have hflat :
        leftShifted =
          ∑ i : Fin n,
            ∑ μ : Fin (d + 1),
              wickRotatePoint (timeReflection d (xL (Fin.rev i))) μ *
                (ξ (finProdFinEquiv
                  (Fin.castAdd (m + 1) i, μ)) : ℂ) := by
      dsimp [leftShifted]
      calc
        (∑ a : Fin (n * (d + 1)),
            flattenCLEquiv n (d + 1)
              (fun k => wickRotatePoint (timeReflection d (xL (Fin.rev k)))) a *
            (section43SplitLeftFlat d n (m + 1) ξ a : ℂ))
            =
          ∑ p : Fin n × Fin (d + 1),
            wickRotatePoint (timeReflection d (xL (Fin.rev p.1))) p.2 *
            (ξ (finProdFinEquiv
                (Fin.castAdd (m + 1) p.1, p.2)) : ℂ) := by
              rw [← finProdFinEquiv.sum_comp]
              refine Finset.sum_congr rfl ?_
              intro p _hp
              simp only [flattenCLEquiv_apply, finProdFinEquiv.symm_apply_apply]
              rw [section43SplitLeftFlat_apply]
        _ =
          ∑ i : Fin n,
            ∑ μ : Fin (d + 1),
              wickRotatePoint (timeReflection d (xL (Fin.rev i))) μ *
                (ξ (finProdFinEquiv
                  (Fin.castAdd (m + 1) i, μ)) : ℂ) := by
              simpa using
                (Finset.sum_product
                  (s := (Finset.univ : Finset (Fin n)))
                  (t := (Finset.univ : Finset (Fin (d + 1))))
                  (f := fun p : Fin n × Fin (d + 1) =>
                    wickRotatePoint (timeReflection d (xL (Fin.rev p.1))) p.2 *
                      (ξ (finProdFinEquiv
                        (Fin.castAdd (m + 1) p.1, p.2)) : ℂ)))
    calc
      (∑ i : Fin n,
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.castAdd (m + 1) i) μ *
              (ξ (finProdFinEquiv
                (Fin.castAdd (m + 1) i, μ)) : ℂ))
          =
        ∑ i : Fin n,
          ∑ μ : Fin (d + 1),
            wickRotatePoint (timeReflection d (xL (Fin.rev i))) μ *
              (ξ (finProdFinEquiv
                (Fin.castAdd (m + 1) i, μ)) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro μ _hμ
            rw [section43OSBorchersTimeShiftConfig_splitLeft_timeReflection_succRight]
      _ = leftShifted := hflat.symm
  have hright :
      (∑ j : Fin (m + 1),
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.natAdd n j) μ *
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, μ)) : ℂ)) =
        rightShifted := by
    have hflat :
        rightShifted =
          ∑ j : Fin (m + 1),
            ∑ μ : Fin (d + 1),
              (if μ = 0 then
                wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
              else
                wickRotatePoint (xR j) μ) *
                (ξ (finProdFinEquiv
                  (Fin.natAdd n j, μ)) : ℂ) := by
      dsimp [rightShifted]
      calc
        (∑ a : Fin ((m + 1) * (d + 1)),
            flattenCLEquiv (m + 1) (d + 1)
              (fun j μ =>
                if μ = 0 then
                  wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
                else
                  wickRotatePoint (xR j) μ) a *
            (section43SplitRightFlat d n (m + 1) ξ a : ℂ))
            =
          ∑ p : Fin (m + 1) × Fin (d + 1),
            (if p.2 = 0 then
              wickRotatePoint (xR p.1) p.2 + (t : ℂ) * Complex.I
            else
              wickRotatePoint (xR p.1) p.2) *
            (ξ (finProdFinEquiv
                (Fin.natAdd n p.1, p.2)) : ℂ) := by
              rw [← finProdFinEquiv.sum_comp]
              refine Finset.sum_congr rfl ?_
              intro p _hp
              simp only [flattenCLEquiv_apply, finProdFinEquiv.symm_apply_apply]
              rw [section43SplitRightFlat_apply]
        _ =
          ∑ j : Fin (m + 1),
            ∑ μ : Fin (d + 1),
              (if μ = 0 then
                wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
              else
                wickRotatePoint (xR j) μ) *
                (ξ (finProdFinEquiv
                  (Fin.natAdd n j, μ)) : ℂ) := by
              simpa using
                (Finset.sum_product
                  (s := (Finset.univ : Finset (Fin (m + 1))))
                  (t := (Finset.univ : Finset (Fin (d + 1))))
                  (f := fun p : Fin (m + 1) × Fin (d + 1) =>
                    (if p.2 = 0 then
                      wickRotatePoint (xR p.1) p.2 + (t : ℂ) * Complex.I
                    else
                      wickRotatePoint (xR p.1) p.2) *
                      (ξ (finProdFinEquiv
                        (Fin.natAdd n p.1, p.2)) : ℂ)))
    calc
      (∑ j : Fin (m + 1),
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.natAdd n j) μ *
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, μ)) : ℂ))
          =
        ∑ j : Fin (m + 1),
          ∑ μ : Fin (d + 1),
            (if μ = 0 then
              wickRotatePoint (xR j) μ + (t : ℂ) * Complex.I
            else
              wickRotatePoint (xR j) μ) *
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, μ)) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            refine Finset.sum_congr rfl ?_
            intro μ _hμ
            rw [section43OSBorchersTimeShiftConfig_splitRight_shift_succRight]
      _ = rightShifted := hflat.symm
  calc
    (∑ a : Fin ((n + (m + 1)) * (d + 1)),
        flattenCLEquiv (n + (m + 1)) (d + 1)
          (section43OSBorchersTimeShiftConfig_succRight
            (d := d) t y) a *
        (ξ a : ℂ))
        =
      ∑ p : Fin (n + (m + 1)) × Fin (d + 1),
        section43OSBorchersTimeShiftConfig_succRight
          (d := d) t y p.1 p.2 *
          (ξ (finProdFinEquiv p) : ℂ) := by
          rw [← finProdFinEquiv.sum_comp]
          simp [flattenCLEquiv_apply]
    _ =
      ∑ k : Fin (n + (m + 1)),
        ∑ μ : Fin (d + 1),
          section43OSBorchersTimeShiftConfig_succRight
            (d := d) t y k μ *
            (ξ (finProdFinEquiv (k, μ)) : ℂ) := by
          simpa using
            (Finset.sum_product
              (s := (Finset.univ : Finset (Fin (n + (m + 1)))))
              (t := (Finset.univ : Finset (Fin (d + 1))))
              (f := fun p : Fin (n + (m + 1)) × Fin (d + 1) =>
                section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y p.1 p.2 *
                  (ξ (finProdFinEquiv p) : ℂ)))
    _ =
      (∑ i : Fin n,
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.castAdd (m + 1) i) μ *
              (ξ (finProdFinEquiv
                (Fin.castAdd (m + 1) i, μ)) : ℂ)) +
      (∑ j : Fin (m + 1),
          ∑ μ : Fin (d + 1),
            section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y (Fin.natAdd n j) μ *
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, μ)) : ℂ)) := by
          rw [Fin.sum_univ_add]
    _ = leftShifted + rightShifted := by
          rw [hleft, hright]
    _ =
      -star
        (∑ a : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (xL k)) a *
          (section43NegRevFlat d n
            (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)) +
        ((∑ a : Fin ((m + 1) * (d + 1)),
            flattenCLEquiv (m + 1) (d + 1)
              (fun k => wickRotatePoint (xR k)) a *
            (section43SplitRightFlat d n (m + 1) ξ a : ℂ)) +
          ((t : ℂ) * Complex.I) *
            (∑ j : Fin (m + 1),
              (ξ (finProdFinEquiv
                (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ))) := by
          simp [leftShifted, rightShifted,
            section43OSBorchersPhase_left_sum_eq_neg_star_sum,
            section43OSBorchersPhase_right_sum_eq_sum_add_tail]

private theorem section43OSBorchersPhase_pointwise_factorized_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    {t : ℝ}
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1)) :
    let y : NPointDomain d (n + (m + 1)) :=
      (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
        (timeReflectionN d xL, xR)
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) =
      Complex.exp
        (-(∑ j : Fin (m + 1),
          (t : ℂ) *
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ))) *
        star
          (Complex.exp
            (Complex.I *
              ∑ a : Fin (n * (d + 1)),
                flattenCLEquiv n (d + 1)
                  (fun k => wickRotatePoint (xL k)) a *
                (section43NegRevFlat d n
                  (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ))) *
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((m + 1) * (d + 1)),
              flattenCLEquiv (m + 1) (d + 1)
                (fun k => wickRotatePoint (xR k)) a *
              (section43SplitRightFlat d n (m + 1) ξ a : ℂ)) := by
  classical
  let y : NPointDomain d (n + (m + 1)) :=
    (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
      (timeReflectionN d xL, xR)
  let L : ℂ :=
    ∑ a : Fin (n * (d + 1)),
      flattenCLEquiv n (d + 1)
        (fun k => wickRotatePoint (xL k)) a *
      (section43NegRevFlat d n
        (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)
  let R : ℂ :=
    ∑ a : Fin ((m + 1) * (d + 1)),
      flattenCLEquiv (m + 1) (d + 1)
        (fun k => wickRotatePoint (xR k)) a *
      (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
  let tailRaw : ℂ :=
    ∑ j : Fin (m + 1),
      (ξ (finProdFinEquiv
        (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
  let tailSum : ℂ := ∑ j : Fin (m + 1),
    (t : ℂ) *
      (ξ (finProdFinEquiv
        (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
  have htail : tailSum = (t : ℂ) * tailRaw := by
    simp [tailSum, tailRaw, Finset.mul_sum]
  have hsum :
      (∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) =
        -star L + (R + ((t : ℂ) * Complex.I) * tailRaw) := by
    dsimp [L, R, tailRaw, y]
    exact section43OSBorchersPhase_full_sum_eq_factorized_succRight
      (d := d) (n := n) (m := m) (t := t) ξ xL xR
  have harg :
      Complex.I * (-star L + (R + ((t : ℂ) * Complex.I) * tailRaw)) =
        -tailSum + star (Complex.I * L) + Complex.I * R := by
    rw [htail]
    simp
    ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by
      rw [pow_two, Complex.I_mul_I]]
    ring
  calc
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ))
        =
      Complex.exp (-tailSum + star (Complex.I * L) + Complex.I * R) := by
        rw [hsum, harg]
    _ =
      Complex.exp (-tailSum) *
        star (Complex.exp (Complex.I * L)) *
        Complex.exp (Complex.I * R) := by
        rw [show -tailSum + star (Complex.I * L) + Complex.I * R =
            (-tailSum + star (Complex.I * L)) + Complex.I * R by ring]
        rw [Complex.exp_add]
        rw [Complex.exp_add]
        have hconj :
            Complex.exp (star (Complex.I * L)) =
              star (Complex.exp (Complex.I * L)) := by
          simpa using (Complex.exp_conj (Complex.I * L))
        rw [hconj]
    _ =
      Complex.exp
        (-(∑ j : Fin (m + 1),
          (t : ℂ) *
            (ξ (finProdFinEquiv
              (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ))) *
        star
          (Complex.exp
            (Complex.I *
              ∑ a : Fin (n * (d + 1)),
                flattenCLEquiv n (d + 1)
                  (fun k => wickRotatePoint (xL k)) a *
                (section43NegRevFlat d n
                  (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ))) *
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((m + 1) * (d + 1)),
              flattenCLEquiv (m + 1) (d + 1)
                (fun k => wickRotatePoint (xR k)) a *
              (section43SplitRightFlat d n (m + 1) ξ a : ℂ)) := by
        rfl

theorem section43OSBorchersPhase_splitIntegrand_factorized_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d (m + 1))
    {t : ℝ}
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (xL : NPointDomain d n) (xR : NPointDomain d (m + 1)) :
    let y : NPointDomain d (n + (m + 1)) :=
      (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
        (timeReflectionN d xL, xR)
    let Lphase : ℂ :=
      ∑ a : Fin (n * (d + 1)),
        flattenCLEquiv n (d + 1)
          (fun k => wickRotatePoint (xL k)) a *
        (section43NegRevFlat d n
          (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)
    let Rphase : ℂ :=
      ∑ a : Fin ((m + 1) * (d + 1)),
        flattenCLEquiv (m + 1) (d + 1)
          (fun k => wickRotatePoint (xR k)) a *
        (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
    let tail : ℂ :=
      ∑ j : Fin (m + 1),
        (t : ℂ) *
          (ξ (finProdFinEquiv
            (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) *
        (f.osConjTensorProduct g) y =
      Complex.exp (-tail) *
        (star (Complex.exp (Complex.I * Lphase) * f xL) *
          (Complex.exp (Complex.I * Rphase) * g xR)) := by
  classical
  let y : NPointDomain d (n + (m + 1)) :=
    (section43NPointProductSplitMeasurableEquiv d n (m + 1)).symm
      (timeReflectionN d xL, xR)
  let Lphase : ℂ :=
    ∑ a : Fin (n * (d + 1)),
      flattenCLEquiv n (d + 1)
        (fun k => wickRotatePoint (xL k)) a *
      (section43NegRevFlat d n
        (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)
  let Rphase : ℂ :=
    ∑ a : Fin ((m + 1) * (d + 1)),
      flattenCLEquiv (m + 1) (d + 1)
        (fun k => wickRotatePoint (xR k)) a *
      (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
  let tail : ℂ :=
    ∑ j : Fin (m + 1),
      (t : ℂ) *
        (ξ (finProdFinEquiv
          (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
  have hphase :
      Complex.exp
        (Complex.I *
          ∑ a : Fin ((n + (m + 1)) * (d + 1)),
            flattenCLEquiv (n + (m + 1)) (d + 1)
              (section43OSBorchersTimeShiftConfig_succRight
                (d := d) t y) a *
            (ξ a : ℂ)) =
        Complex.exp (-tail) *
          star (Complex.exp (Complex.I * Lphase)) *
          Complex.exp (Complex.I * Rphase) := by
    simpa [y, Lphase, Rphase, tail] using
      section43OSBorchersPhase_pointwise_factorized_succRight
        (d := d) (n := n) (m := m) (t := t) ξ xL xR
  have hos :
      (f.osConjTensorProduct g) y = star (f xL) * g xR := by
    simpa [y] using
      section43OSConjTensorProduct_split_timeReflection_succRight
        (d := d) (n := n) (m := m) f g xL xR
  change
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) *
        (f.osConjTensorProduct g) y =
      Complex.exp (-tail) *
        (star (Complex.exp (Complex.I * Lphase) * f xL) *
          (Complex.exp (Complex.I * Rphase) * g xR))
  rw [hphase, hos]
  rw [star_mul]
  ring

theorem integrable_section43OSBorchersPhaseIntegral_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (_ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    Integrable
      (fun y : NPointDomain d (n + (m + 1)) =>
        Complex.exp
          (Complex.I *
            ∑ a : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) a *
              (ξ a : ℂ)) *
        (f.1.osConjTensorProduct g.1) y) := by
  classical
  let e := section43NPointProductSplitMeasurableEquiv d n (m + 1)
  let tail : ℂ :=
    ∑ j : Fin (m + 1),
      (t : ℂ) *
        (ξ (finProdFinEquiv
          (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)
  let Lphase : NPointDomain d n → ℂ := fun xL =>
    ∑ a : Fin (n * (d + 1)),
      flattenCLEquiv n (d + 1)
        (fun k => wickRotatePoint (xL k)) a *
      (section43NegRevFlat d n
        (section43SplitLeftFlat d n (m + 1) ξ) a : ℂ)
  let Rphase : NPointDomain d (m + 1) → ℂ := fun xR =>
    ∑ a : Fin ((m + 1) * (d + 1)),
      flattenCLEquiv (m + 1) (d + 1)
        (fun k => wickRotatePoint (xR k)) a *
      (section43SplitRightFlat d n (m + 1) ξ a : ℂ)
  let leftFactor : NPointDomain d n → ℂ := fun xL =>
    Complex.exp (Complex.I * Lphase xL) * f.1 xL
  let rightFactor : NPointDomain d (m + 1) → ℂ := fun xR =>
    Complex.exp (Complex.I * Rphase xR) * g.1 xR
  let H : NPointDomain d n × NPointDomain d (m + 1) → ℂ := fun p =>
    Complex.exp (-tail) * (star (leftFactor p.1) * rightFactor p.2)
  let F : NPointDomain d (n + (m + 1)) → ℂ := fun y =>
    Complex.exp
      (Complex.I *
        ∑ a : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight
              (d := d) t y) a *
          (ξ a : ℂ)) *
      (f.1.osConjTensorProduct g.1) y
  let qL : NPointDomain d n :=
    section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
      (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)
  let qR : NPointDomain d (m + 1) :=
    section43RightTailBlock d n (m + 1)
      (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)
  have hqL : qL ∈ section43PositiveEnergyRegion d n := by
    simpa [qL] using
      section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ)
        (Nat.succ_pos m) hξ
  have hqR : qR ∈ section43PositiveEnergyRegion d (m + 1) := by
    simpa [qR] using
      section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ) hξ
  have hξL :
      (section43CumulativeTailMomentumCLE d n).symm qL =
        section43NegRevFlat d n (section43SplitLeftFlat d n (m + 1) ξ) := by
    simpa [qL] using
      section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
        (d := d) (n := n) (r := m + 1) (Nat.succ_pos m)
        (ξ := ξ) hξ.2
  have hξR :
      (section43CumulativeTailMomentumCLE d (m + 1)).symm qR =
        section43SplitRightFlat d n (m + 1) ξ := by
    simpa [qR] using
      (section43SplitRightFlat_eq_cumulativeTail_rightTail
        (d := d) (n := n) (r := m + 1) ξ).symm
  have hleft : Integrable leftFactor := by
    simpa [leftFactor, Lphase, hξL] using
      integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy
        (d := d) (n := n) f qL hqL
  have hright : Integrable rightFactor := by
    simpa [rightFactor, Rphase, hξR] using
      integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy
        (d := d) (n := m + 1) g qR hqR
  have hH : Integrable H
      ((volume : Measure (NPointDomain d n)).prod
        (volume : Measure (NPointDomain d (m + 1)))) := by
    have hleftStar :
        Integrable (fun xL : NPointDomain d n => star (leftFactor xL))
          (volume : Measure (NPointDomain d n)) := by
      have hconj :
          Integrable (fun xL : NPointDomain d n =>
              Complex.conjLIE (leftFactor xL))
            (volume : Measure (NPointDomain d n)) :=
        (LinearIsometryEquiv.integrable_comp_iff
          (L := Complex.conjLIE)
          (φ := leftFactor)
          (μ := (volume : Measure (NPointDomain d n)))).2 hleft
      simpa using hconj
    have hprod :
        Integrable
          (fun p : NPointDomain d n × NPointDomain d (m + 1) =>
            star (leftFactor p.1) * rightFactor p.2)
          ((volume : Measure (NPointDomain d n)).prod
            (volume : Measure (NPointDomain d (m + 1)))) :=
      hleftStar.mul_prod hright
    simpa [H] using hprod.const_mul (Complex.exp (-tail))
  have hprod_reflect :
      MeasurePreserving
        (Prod.map (timeReflectionN d) id)
        ((volume : Measure (NPointDomain d n)).prod
          (volume : Measure (NPointDomain d (m + 1))))
        ((volume : Measure (NPointDomain d n)).prod
          (volume : Measure (NPointDomain d (m + 1)))) :=
    (timeReflectionN_measurePreserving (d := d) (n := n)).prod
      (MeasurePreserving.id (volume : Measure (NPointDomain d (m + 1))))
  let G : NPointDomain d n × NPointDomain d (m + 1) → ℂ := fun p =>
    F (e.symm p)
  have hG : Integrable G
      ((volume : Measure (NPointDomain d n)).prod
        (volume : Measure (NPointDomain d (m + 1)))) := by
    have hcomp :
        Integrable
          (fun p : NPointDomain d n × NPointDomain d (m + 1) =>
            H (Prod.map (timeReflectionN d) id p))
          ((volume : Measure (NPointDomain d n)).prod
            (volume : Measure (NPointDomain d (m + 1)))) :=
      hprod_reflect.integrable_comp_of_integrable hH
    refine hcomp.congr ?_
    filter_upwards with p
    rcases p with ⟨yL, xR⟩
    have hpoint :=
      section43OSBorchersPhase_splitIntegrand_factorized_succRight
        (d := d) (n := n) (m := m) (f := f.1) (g := g.1)
        (t := t) ξ (timeReflectionN d yL) xR
    simpa [G, F, H, leftFactor, rightFactor, Lphase, Rphase, tail, e,
      section43TimeReflectionN_involutive] using hpoint.symm
  have he :
      MeasurePreserving e
        (volume : Measure (NPointDomain d (n + (m + 1))))
        ((volume : Measure (NPointDomain d n)).prod
          (volume : Measure (NPointDomain d (m + 1)))) :=
    section43NPointProductSplitMeasurableEquiv_measurePreserving d n (m + 1)
  have hF : Integrable F :=
    (he.integrable_comp_of_integrable hG).congr (by
      filter_upwards with y
      simp [G, F, e])
  simpa [F] using hF

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
def section43OSForwardTubeLift_succRight
    (d : ℕ) {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43OSBorchersTimeShiftConfig_succRight d t y i +
      section43OSForwardTubeLiftTranslation_succRight d t y

/-- The successor-right forward-tube lift is continuous in the Euclidean
configuration parameter. -/
theorem continuous_section43OSForwardTubeLift_succRight
    (d : ℕ) [NeZero d] {n m : ℕ} (t : ℝ) :
    Continuous
      (section43OSForwardTubeLift_succRight (d := d) (n := n) (m := m) t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  simp [section43OSForwardTubeLift_succRight,
    section43OSForwardTubeLiftTranslation_succRight,
    section43OSBorchersTimeShiftConfig_succRight,
    section43RawXiShiftConfig_succRight, xiShift, wickRotatePoint]
  continuity

/-- The forward-tube lift differs from the raw `xiShift` shell only by a
Borchers-ordering permutation and a diagonal translation.  The chosen
continuation `bvt_F` is invariant under both, so the two shell values agree. -/
theorem section43_bvt_F_forwardTubeLift_eq_xiShiftShell_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (y : NPointDomain d (n + (m + 1))) :
    bvt_F OS lgc (n + (m + 1))
        (section43OSForwardTubeLift_succRight (d := d) t y) =
      bvt_F OS lgc (n + (m + 1))
        (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
  calc
    bvt_F OS lgc (n + (m + 1))
        (section43OSForwardTubeLift_succRight (d := d) t y)
        =
      bvt_F OS lgc (n + (m + 1))
        (section43OSBorchersTimeShiftConfig_succRight d t y) := by
          simpa [section43OSForwardTubeLift_succRight] using
            bvt_F_translationInvariant OS lgc (n + (m + 1))
              (section43OSBorchersTimeShiftConfig_succRight d t y)
              (section43OSForwardTubeLiftTranslation_succRight d t y)
    _ =
      bvt_F OS lgc (n + (m + 1))
        (section43RawXiShiftConfig_succRight d t y) := by
          simpa [section43OSBorchersTimeShiftConfig_succRight] using
            bvt_F_perm OS lgc (n + (m + 1))
              (section43LeftBlockReversePerm_succRight n m)
              (section43RawXiShiftConfig_succRight d t y)
    _ =
      bvt_F OS lgc (n + (m + 1))
        (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
          rfl

/-- Integral form of
`section43_bvt_F_forwardTubeLift_eq_xiShiftShell_succRight`. -/
theorem section43_forwardTubeLiftIntegral_eq_xiShiftShell_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (t : ℝ) (χ : NPointDomain d (n + (m + 1)) → ℂ) :
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        χ y) =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        χ y := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [section43_bvt_F_forwardTubeLift_eq_xiShiftShell_succRight
    (d := d) (n := n) (m := m) OS lgc t y]

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

private theorem section43_tsupport_precomp_subset {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

private theorem section43_continuous_timeReflectionN
    (d : ℕ) {n : ℕ} :
    Continuous (timeReflectionN d (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [timeReflectionN, timeReflection] using
      ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
        Continuous fun x : NPointDomain d n => -x i 0)
  · simpa [timeReflectionN, timeReflection, hμ] using
      ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
        (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
        Continuous fun x : NPointDomain d n => x i μ)

private theorem section43_continuous_splitFirst
    (d : ℕ) {n m : ℕ} :
    Continuous (splitFirst n m : NPointDomain d (n + m) → NPointDomain d n) := by
  apply continuous_pi
  intro i
  simpa [splitFirst] using
    (continuous_apply (Fin.castAdd m i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.castAdd m i))

private theorem section43_continuous_splitLast
    (d : ℕ) {n m : ℕ} :
    Continuous (splitLast n m : NPointDomain d (n + m) → NPointDomain d m) := by
  apply continuous_pi
  intro i
  simpa [splitLast] using
    (continuous_apply (Fin.natAdd n i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.natAdd n i))

/-- Compact support is preserved by the OS-conjugated tensor product when both
factors are compactly supported. -/
theorem hasCompactSupport_osConjTensorProduct_of_hasCompactSupport
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    HasCompactSupport
      ((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ) := by
  let Kleft : Set (NPointDomain d n) :=
    timeReflectionN d '' tsupport (f : NPointDomain d n → ℂ)
  let Kprod : Set (NPointDomain d n × NPointDomain d m) :=
    Kleft ×ˢ tsupport (g : NPointDomain d m → ℂ)
  let e := section43NPointProductSplitMeasurableEquiv d n m
  have hKleft_compact : IsCompact Kleft := by
    exact hf_compact.isCompact.image (section43_continuous_timeReflectionN d)
  have hKprod_compact : IsCompact Kprod := hKleft_compact.prod hg_compact.isCompact
  refine HasCompactSupport.of_support_subset_isCompact
    (hKprod_compact.image (section43NPointProductSplitMeasurableEquiv_symm_continuous d n m))
    ?_
  intro y hy
  have hprod_ne :
      (f.osConjTensorProduct g : SchwartzNPoint d (n + m)) y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have hmul_ne :
      f.osConj (splitFirst n m y) * g (splitLast n m y) ≠ 0 := by
    simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply]
      using hprod_ne
  have hleft_ne : f.osConj (splitFirst n m y) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul_ne).1
  have hright_ne : g (splitLast n m y) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul_ne).2
  have hf_pre :
      timeReflectionN d (splitFirst n m y) ∈
        tsupport (f : NPointDomain d n → ℂ) := by
    have hf_ne :
        f (timeReflectionN d (splitFirst n m y)) ≠ 0 := by
      intro hf_zero
      exact hleft_ne (by simp [SchwartzNPoint.osConj_apply, hf_zero])
    exact subset_tsupport _ (Function.mem_support.mpr hf_ne)
  have hleft_mem : splitFirst n m y ∈ Kleft := by
    refine ⟨timeReflectionN d (splitFirst n m y), hf_pre, ?_⟩
    exact section43TimeReflectionN_involutive d (splitFirst n m y)
  have hright_mem :
      splitLast n m y ∈ tsupport (g : NPointDomain d m → ℂ) :=
    subset_tsupport _ (Function.mem_support.mpr hright_ne)
  refine ⟨(splitFirst n m y, splitLast n m y), ⟨hleft_mem, hright_mem⟩, ?_⟩
  ext i μ
  by_cases hi : i.val < n
  · let ii : Fin n := ⟨i.val, hi⟩
    have hi_eq : i = Fin.castAdd m ii := by
      ext
      rfl
    rw [hi_eq]
    exact congrFun
      (section43NPointProductSplitMeasurableEquiv_symm_castAdd
        d n m (splitFirst n m y) (splitLast n m y) ii) μ
  · let jj : Fin m := ⟨i.val - n, by omega⟩
    have hi_eq : i = Fin.natAdd n jj := by
      ext
      simp [jj, Fin.natAdd]
      omega
    rw [hi_eq]
    exact congrFun
      (section43NPointProductSplitMeasurableEquiv_symm_natAdd
        d n m (splitFirst n m y) (splitLast n m y) jj) μ

/-- Closed-support chronological localization for OS-conjugated tensor
products.  On the topological support, the reflected left block and the right
block both lie in their ordered positive-time regions. -/
theorem tsupport_osConjTensorProduct_subset_split_neg_pos
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    tsupport
        ((f.1.osConjTensorProduct g.1 : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ) ⊆
      {y | timeReflectionN d (splitFirst n m y) ∈
          OrderedPositiveTimeRegion d n} ∩
      {y | splitLast n m y ∈ OrderedPositiveTimeRegion d m} := by
  let A : Set (NPointDomain d (n + m)) :=
    {y | timeReflectionN d (splitFirst n m y) ∈
      OrderedPositiveTimeRegion d n}
  let B : Set (NPointDomain d (n + m)) :=
    {y | splitLast n m y ∈ OrderedPositiveTimeRegion d m}
  have hosConj :
      tsupport ((f.1.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) ⊆
        {x | timeReflectionN d x ∈ OrderedPositiveTimeRegion d n} := by
    intro x hx
    have hxpre :
        timeReflectionN d x ∈ tsupport (f.1 : NPointDomain d n → ℂ) := by
      exact section43_tsupport_precomp_subset (f := (f.1 : NPointDomain d n → ℂ))
        (h := timeReflectionN d) (section43_continuous_timeReflectionN d)
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _)
          (fun y : NPointDomain d n => f.1 (timeReflectionN d y))) hx)
    exact f.2 hxpre
  have hA :
      tsupport (fun y : NPointDomain d (n + m) =>
          f.1.osConj (splitFirst n m y)) ⊆ A := by
    intro y hy
    exact hosConj <|
      section43_tsupport_precomp_subset
        (f := ((f.1.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        (h := splitFirst n m) (section43_continuous_splitFirst d) hy
  have hB :
      tsupport (fun y : NPointDomain d (n + m) =>
          g.1 (splitLast n m y)) ⊆ B := by
    intro y hy
    exact g.2 <|
      section43_tsupport_precomp_subset
        (f := (g.1 : NPointDomain d m → ℂ))
        (h := splitLast n m) (section43_continuous_splitLast d) hy
  intro y hy
  have hyprod :
      y ∈ tsupport (fun x : NPointDomain d (n + m) =>
        f.1.osConj (splitFirst n m x) * g.1 (splitLast n m x)) := by
    simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply] using hy
  refine ⟨?_, ?_⟩
  · exact hA ((tsupport_mul_subset_left
      (f := fun x : NPointDomain d (n + m) =>
        f.1.osConj (splitFirst n m x))
      (g := fun x : NPointDomain d (n + m) =>
        g.1 (splitLast n m x))) hyprod)
  · exact hB ((tsupport_mul_subset_right
      (f := fun x : NPointDomain d (n + m) =>
        f.1.osConj (splitFirst n m x))
      (g := fun x : NPointDomain d (n + m) =>
        g.1 (splitLast n m x))) hyprod)

private theorem section43OSConjTensorProduct_tsupport_left_reflected_ordered_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ tsupport
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    timeReflectionN d (splitFirst n (m + 1) y) ∈
      OrderedPositiveTimeRegion d n :=
  (tsupport_osConjTensorProduct_subset_split_neg_pos d f g hy).1

private theorem section43OSConjTensorProduct_tsupport_right_ordered_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ tsupport
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    splitLast n (m + 1) y ∈
      OrderedPositiveTimeRegion d (m + 1) :=
  (tsupport_osConjTensorProduct_subset_split_neg_pos d f g hy).2

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

private theorem section43OSBorchersTimeShiftConfig_strictOrdered_of_osTsupport_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ tsupport
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    StrictMono
      (fun i : Fin (n + (m + 1)) =>
        (section43OSBorchersTimeShiftConfig_succRight d t y i 0).im) := by
  intro i j hij
  have hij_val : i.val < j.val := hij
  have hleftOrd :=
    section43OSConjTensorProduct_tsupport_left_reflected_ordered_succRight
      d f g hy
  have hrightOrd :=
    section43OSConjTensorProduct_tsupport_right_ordered_succRight
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

/-- Closed-support version of
`section43OSForwardTubeLift_mem_forwardTube_of_osSupport_succRight`.  This is
the support-localization input needed for the safe forward-tube Fubini packet. -/
theorem section43OSForwardTubeLift_mem_forwardTube_of_osTsupport_succRight
    (d : ℕ) [NeZero d] {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ tsupport
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    section43OSForwardTubeLift_succRight d t y ∈
      TubeDomainSetPi (ForwardConeAbs d (n + (m + 1))) := by
  let N := n + (m + 1)
  let xs : NPointDomain d N :=
    section43OSForwardTubeLiftRealConfig_succRight d t y
  have hborch_strict :=
    section43OSBorchersTimeShiftConfig_strictOrdered_of_osTsupport_succRight
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

theorem section43OSForwardTubeLift_multiDimPsiZExt_apply_of_spectralRegion_succRight
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

theorem section43SuccRightEtaCLM_nonneg_of_mem_spectralRegion
    (d n m : ℕ) [NeZero d]
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    0 ≤ section43SuccRightEtaCLM d n m ξ :=
  section43SuccRightEtaCLM_nonneg_of_mem_dualCone d n m hξ.1

theorem section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight
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

/-- The successor-right Borchers phase's ordinary right tail is exactly the
one-factor Section 4.3 Fourier-Laplace integral at the right cumulative-tail
block. -/
theorem section43OSBorchersPhase_rightFactor_eq_fourierLaplaceIntegral_succRight
    (d n m : ℕ) [NeZero d]
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ xR : NPointDomain d (m + 1),
        Complex.exp
          (Complex.I *
            ∑ i : Fin ((m + 1) * (d + 1)),
              flattenCLEquiv (m + 1) (d + 1)
                (fun k => wickRotatePoint (xR k)) i *
              (section43SplitRightFlat d n (m + 1) ξ i : ℂ)) *
        g.1 xR) =
      section43FourierLaplaceIntegral d (m + 1) g
        (section43RightTailBlock d n (m + 1)
          (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)) := by
  classical
  let qR : NPointDomain d (m + 1) :=
    section43RightTailBlock d n (m + 1)
      (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)
  have hqR : qR ∈ section43PositiveEnergyRegion d (m + 1) := by
    simpa [qR] using
      section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ) hξ
  have hξR :
      (section43CumulativeTailMomentumCLE d (m + 1)).symm qR =
        section43SplitRightFlat d n (m + 1) ξ := by
    simpa [qR] using
      (section43SplitRightFlat_eq_cumulativeTail_rightTail
        (d := d) (n := n) (r := m + 1) ξ).symm
  rw [section43FourierLaplaceIntegral_eq_wickRotatePhaseIntegral_of_mem_positiveEnergy
    (d := d) (n := m + 1) (f := g) (q := qR) hqR]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with xR
  simp [qR, hξR]

/-- After the left split variable has been time-reflected, the
successor-right Borchers left factor is the complex conjugate of the one-factor
Section 4.3 Fourier-Laplace integral at the shifted Borchers-left block. -/
theorem section43OSBorchersPhase_leftFactor_eq_star_fourierLaplaceIntegral_succRight
    (d n m : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ xL : NPointDomain d n,
        star
          (Complex.exp
            (Complex.I *
              ∑ i : Fin (n * (d + 1)),
                flattenCLEquiv n (d + 1)
                  (fun k => wickRotatePoint (xL k)) i *
                (section43NegRevFlat d n
                  (section43SplitLeftFlat d n (m + 1) ξ) i : ℂ)) *
            f.1 xL)) =
      star
        (section43FourierLaplaceIntegral d n f
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
            (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) := by
  classical
  let qL : NPointDomain d n :=
    section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
      (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)
  have hqL : qL ∈ section43PositiveEnergyRegion d n := by
    simpa [qL] using
      section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
        (d := d) (n := n) (r := m + 1) (ξ := ξ)
        (Nat.succ_pos m) hξ
  have hξL :
      (section43CumulativeTailMomentumCLE d n).symm qL =
        section43NegRevFlat d n (section43SplitLeftFlat d n (m + 1) ξ) := by
    simpa [qL] using
      section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
        (d := d) (n := n) (r := m + 1) (Nat.succ_pos m)
        (ξ := ξ) hξ.2
  rw [section43FourierLaplaceIntegral_eq_wickRotatePhaseIntegral_of_mem_positiveEnergy
    (d := d) (n := n) (f := f) (q := qL) hqL]
  rw [hξL]
  exact _root_.integral_conj

/-- The scalar factor created by shifting the right OS block by Euclidean time
`t` is exactly the `2π`-normalized semigroup damping factor used by the
`ψ_Z` kernel. -/
theorem section43OSBorchersPhase_tailFactor_eq_eta_succRight
    (d n m : ℕ) [NeZero d]
    (t : ℝ)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    let lamξ : ℝ :=
      ∑ i : Fin ((n + (m + 1)) * (d + 1)),
        (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
          (zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    Complex.exp
        (-(t : ℂ) *
          (∑ j : Fin (m + 1),
            (ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ))) =
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) := by
  classical
  let tailSum : ℝ :=
    ∑ j : Fin (m + 1),
      ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1))))
  let lamξ : ℝ :=
    ∑ i : Fin ((n + (m + 1)) * (d + 1)),
      (((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
        (zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  let ηξ : ℝ := -lamξ / (2 * Real.pi)
  have hlam : lamξ = -tailSum := by
    simpa [lamξ, tailSum] using
      zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum
        (d := d) (n := n) (m := m + 1) (ξ := ξ)
  dsimp only
  rw [show
      (∑ j : Fin (m + 1),
          (ξ (finProdFinEquiv (Fin.natAdd n j, (0 : Fin (d + 1)))) : ℂ)) =
        (tailSum : ℂ) by simp [tailSum]]
  have hlam_norm :
      ((-(∑ i : Fin ((n + (m + 1)) * (d + 1)),
          ((castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm)
            (zeroHeadBlockShift
              (m := n * (d + 1)) (n := (m + 1) * (d + 1))
              (flatTimeShiftDirection d (m + 1)))) i * ξ i)) /
        (2 * Real.pi)) =
      (-lamξ) / (2 * Real.pi) := by
    simp [lamξ]
  rw [hlam_norm]
  rw [hlam]
  congr 1
  norm_num
  field_simp [Real.pi_ne_zero]

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
