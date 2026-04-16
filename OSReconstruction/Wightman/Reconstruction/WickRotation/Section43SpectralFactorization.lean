import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

@[simp] theorem castFinCLE_apply {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) := rfl

/-- Reindex an `NPointDomain` along an equality of its point count. -/
abbrev section43CastNPointCLE (d : ℕ) {a b : ℕ} (h : a = b) :
    NPointDomain d a ≃L[ℝ] NPointDomain d b :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b => SpacetimeDim d) (finCongr h)

@[simp] theorem section43CastNPointCLE_apply
    (d : ℕ) {a b : ℕ} (h : a = b)
    (q : NPointDomain d a) (i : Fin b) :
    section43CastNPointCLE d h q i = q ((finCongr h).symm i) := rfl

/-!
# Section 4.3 Spectral Factorization Coordinates

This small companion contains the coordinate blocks needed to factor the
full-flat Wightman Fourier kernel on the Section 4.3 spectral region.  The key
point is that the Borchers-reversed left factor uses the total-momentum-shifted
block `section43LeftBorchersBlock`, not the naive reversed left block.
-/

/-- Left flat frequency block of a full `(n + r)`-point flat frequency. -/
def section43SplitLeftFlat (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    ξ (finProdFinEquiv (Fin.castAdd r p.1, p.2))

/-- Right flat frequency block of a full `(n + r)`-point flat frequency. -/
def section43SplitRightFlat (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (r * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    ξ (finProdFinEquiv (Fin.natAdd n p.1, p.2))

/-- Negative chronological reversal of an `n`-point flat frequency block. -/
def section43NegRevFlat (d n : ℕ) [NeZero d]
    (ξL : Fin (n * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    -(ξL (finProdFinEquiv (Fin.rev p.1, p.2)))

/-- The shifted Borchers-left cumulative-tail block.

For `q` in the full `(n + r)` cumulative-tail coordinates, this is
`q_n, q_{n-1}, ..., q_1`.  The `r > 0` hypothesis ensures the first index
`n` exists in the full block.
-/
def section43LeftBorchersBlock (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r)) : NPointDomain d n :=
  fun i μ => q ⟨n - i.val, by omega⟩ μ

@[simp] theorem section43SplitLeftFlat_apply
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (i : Fin n) (μ : Fin (d + 1)) :
    section43SplitLeftFlat d n r ξ (finProdFinEquiv (i, μ)) =
      ξ (finProdFinEquiv (Fin.castAdd r i, μ)) := by
  simp [section43SplitLeftFlat]

@[simp] theorem section43SplitRightFlat_apply
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (j : Fin r) (μ : Fin (d + 1)) :
    section43SplitRightFlat d n r ξ (finProdFinEquiv (j, μ)) =
      ξ (finProdFinEquiv (Fin.natAdd n j, μ)) := by
  simp [section43SplitRightFlat]

@[simp] theorem section43NegRevFlat_apply
    (d n : ℕ) [NeZero d]
    (ξL : Fin (n * (d + 1)) → ℝ)
    (i : Fin n) (μ : Fin (d + 1)) :
    section43NegRevFlat d n ξL (finProdFinEquiv (i, μ)) =
      -(ξL (finProdFinEquiv (Fin.rev i, μ))) := by
  simp [section43NegRevFlat]

/-- Flat chronological reversal as an equivalence of flattened coordinates. -/
def section43FlatReverseEquiv (d n : ℕ) [NeZero d] :
    Fin (n * (d + 1)) ≃ Fin (n * (d + 1)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr Fin.revPerm (Equiv.refl (Fin (d + 1)))).trans
      finProdFinEquiv)

/-- Flat chronological reversal as a continuous linear equivalence. -/
noncomputable def section43FlatReverseCLE (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ
    (section43FlatReverseEquiv d n)).toContinuousLinearEquiv

@[simp] theorem section43FlatReverseCLE_apply
    (d n : ℕ) [NeZero d]
    (x : Fin (n * (d + 1)) → ℝ) (i : Fin n) (μ : Fin (d + 1)) :
    section43FlatReverseCLE d n x (finProdFinEquiv (i, μ)) =
      x (finProdFinEquiv (Fin.rev i, μ)) := by
  simp [section43FlatReverseCLE, section43FlatReverseEquiv]

/-- The flat reversal preserves Lebesgue measure on finite-dimensional
coordinate space. -/
theorem section43FlatReverseCLE_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasureTheory.MeasurePreserving
      (section43FlatReverseCLE d n)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (n * (d + 1)) → ℝ))
      MeasureTheory.volume := by
  convert
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin (n * (d + 1)) => ℝ)
      (section43FlatReverseEquiv d n).symm) using 1
  ext x a
  change x (section43FlatReverseEquiv d n a) =
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n * (d + 1)) => ℝ)
      (section43FlatReverseEquiv d n).symm) x a
  rw [MeasurableEquiv.coe_piCongrLeft]
  simpa using
    (Equiv.piCongrLeft_apply_apply
      (fun _ : Fin (n * (d + 1)) => ℝ)
      (section43FlatReverseEquiv d n).symm x
      ((section43FlatReverseEquiv d n) a)).symm

/-- Pairing with a flat-reversed variable is the negative pairing against the
negative reversed frequency. -/
theorem section43FlatReverse_pair_eq_neg_negRevFlat_pair
    (d n : ℕ) [NeZero d]
    (x ξL : Fin (n * (d + 1)) → ℝ) :
    (∑ a : Fin (n * (d + 1)),
        (section43FlatReverseCLE d n x a : ℂ) * (ξL a : ℂ)) =
      -∑ a : Fin (n * (d + 1)),
        (x a : ℂ) * (section43NegRevFlat d n ξL a : ℂ) := by
  classical
  calc
    (∑ a : Fin (n * (d + 1)),
        (section43FlatReverseCLE d n x a : ℂ) * (ξL a : ℂ))
        = ∑ p : Fin n × Fin (d + 1),
            (x (finProdFinEquiv (Fin.rev p.1, p.2)) : ℂ) *
              (ξL (finProdFinEquiv p) : ℂ) := by
          rw [← finProdFinEquiv.sum_comp]
          refine Finset.sum_congr rfl ?_
          intro p _hp
          rw [section43FlatReverseCLE_apply]
    _ = ∑ p : Fin n × Fin (d + 1),
            (x (finProdFinEquiv p) : ℂ) *
              (ξL (finProdFinEquiv (Fin.rev p.1, p.2)) : ℂ) := by
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
    _ = -∑ a : Fin (n * (d + 1)),
          (x a : ℂ) * (section43NegRevFlat d n ξL a : ℂ) := by
          rw [← Finset.sum_neg_distrib]
          rw [← finProdFinEquiv.sum_comp]
          refine Finset.sum_congr rfl ?_
          intro p _hp
          simp [section43NegRevFlat]

/-- Flattened Borchers conjugation is conjugation after flat chronological
reversal. -/
theorem flatten_borchersConj_eq_star_flatten_comp_flatReverse
    (d n : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (x : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d) φ.borchersConj x =
      starRingEnd ℂ
        (flattenSchwartzNPoint (d := d) φ
          (section43FlatReverseCLE d n x)) := by
  simp only [flattenSchwartzNPoint_apply, SchwartzMap.borchersConj_apply]
  apply congrArg (starRingEnd ℂ)
  congr 1
  ext i μ
  simp [section43FlatReverseCLE_apply]

/-- Flat chronological reversal is involutive. -/
theorem section43FlatReverseCLE_involutive
    (d n : ℕ) [NeZero d]
    (x : Fin (n * (d + 1)) → ℝ) :
    section43FlatReverseCLE d n (section43FlatReverseCLE d n x) = x := by
  ext a
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
  rw [section43FlatReverseCLE_apply, section43FlatReverseCLE_apply,
    Fin.rev_rev]

/-- Physics Fourier transform of a Borchers-conjugated flattened component. -/
theorem physicsFourierFlatCLM_borchersConj_apply
    (d n : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (ξL : Fin (n * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (flattenSchwartzNPoint (d := d) φ.borchersConj) ξL =
      star
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) φ)
          (section43NegRevFlat d n ξL)) := by
  rw [← physicsFourierFlatCLM_integral, ← physicsFourierFlatCLM_integral]
  let R := section43FlatReverseCLE d n
  let η := section43NegRevFlat d n ξL
  have hcomp := (section43FlatReverseCLE_measurePreserving d n).integral_comp
    (R.toHomeomorph.measurableEmbedding)
    (fun x : Fin (n * (d + 1)) → ℝ =>
      Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξL i : ℂ)) *
        flattenSchwartzNPoint (d := d) φ.borchersConj x)
  calc
    (∫ x : Fin (n * (d + 1)) → ℝ,
      Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξL i : ℂ)) *
        flattenSchwartzNPoint (d := d) φ.borchersConj x)
        = ∫ x : Fin (n * (d + 1)) → ℝ,
            Complex.exp (Complex.I * ∑ i, ((R x) i : ℂ) * (ξL i : ℂ)) *
              flattenSchwartzNPoint (d := d) φ.borchersConj (R x) := by
            exact hcomp.symm
    _ = ∫ x : Fin (n * (d + 1)) → ℝ,
          starRingEnd ℂ
            (Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (η i : ℂ)) *
              flattenSchwartzNPoint (d := d) φ x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [flatten_borchersConj_eq_star_flatten_comp_flatReverse]
          dsimp only [R, η]
          rw [section43FlatReverseCLE_involutive]
          rw [section43FlatReverse_pair_eq_neg_negRevFlat_pair]
          simp only [map_mul]
          congr 1
          have harg : Complex.I * -∑ a,
              (x a : ℂ) * (section43NegRevFlat d n ξL a : ℂ) =
              starRingEnd ℂ (Complex.I * ∑ a,
                (x a : ℂ) * (section43NegRevFlat d n ξL a : ℂ)) := by
            simp
          rw [harg, Complex.exp_conj]
    _ = starRingEnd ℂ (∫ x : Fin (n * (d + 1)) → ℝ,
          Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (η i : ℂ)) *
            flattenSchwartzNPoint (d := d) φ x) := by
          exact _root_.integral_conj

/-- Split a flat finite-dimensional coordinate block into its first and last
flat coordinate blocks. -/
private def section43FlatProductSplitMeasurableEquiv (a b : ℕ) :
    (Fin (a + b) → ℝ) ≃ᵐ ((Fin a → ℝ) × (Fin b → ℝ)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ))

private theorem section43FlatProductSplitMeasurableEquiv_measurePreserving
    (a b : ℕ) :
    MeasureTheory.MeasurePreserving
      (section43FlatProductSplitMeasurableEquiv a b)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (a + b) → ℝ))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin a → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin b → ℝ))) := by
  let e1 := MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
  have he1 : MeasureTheory.MeasurePreserving e1 MeasureTheory.volume MeasureTheory.volume := by
    simpa [e1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin (a + b) => ℝ)
        (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  have he2 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ))
      MeasureTheory.volume
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin a → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin b → ℝ))) := by
    simpa using
      (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Fin a ⊕ Fin b => ℝ))
  simpa [section43FlatProductSplitMeasurableEquiv, e1] using he2.comp (he1.symm e1)

private theorem section43FlatProductSplitMeasurableEquiv_fst_apply
    (a b : ℕ) (x : Fin (a + b) → ℝ) (i : Fin a) :
    (section43FlatProductSplitMeasurableEquiv a b x).1 i = x (Fin.castAdd b i) := by
  rw [section43FlatProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x) (Sum.inl i) =
    x (Fin.castAdd b i)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (a + b) => ℝ)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
    ((Equiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
    (Sum.inl i)
  rw [← h]
  simp [finSumFinEquiv_apply_left]

private theorem section43FlatProductSplitMeasurableEquiv_snd_apply
    (a b : ℕ) (x : Fin (a + b) → ℝ) (j : Fin b) :
    (section43FlatProductSplitMeasurableEquiv a b x).2 j = x (Fin.natAdd a j) := by
  rw [section43FlatProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x) (Sum.inr j) =
    x (Fin.natAdd a j)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (a + b) => ℝ)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
    ((Equiv.piCongrLeft (fun _ : Fin (a + b) => ℝ)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
    (Sum.inr j)
  rw [← h]
  simp [finSumFinEquiv_apply_right]

private theorem section43FlatProductSplitMeasurableEquiv_fst_eq_splitFirst
    (a b : ℕ) (x : Fin (a + b) → ℝ) :
    (section43FlatProductSplitMeasurableEquiv a b x).1 = splitFirst a b x := by
  ext i
  exact section43FlatProductSplitMeasurableEquiv_fst_apply a b x i

private theorem section43FlatProductSplitMeasurableEquiv_snd_eq_splitLast
    (a b : ℕ) (x : Fin (a + b) → ℝ) :
    (section43FlatProductSplitMeasurableEquiv a b x).2 = splitLast a b x := by
  ext i
  exact section43FlatProductSplitMeasurableEquiv_snd_apply a b x i

private theorem splitFirst_castFinCLE_symm_eq_section43SplitLeftFlat
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    splitFirst (n * (d + 1)) (r * (d + 1))
        ((castFinCLE (by ring : n * (d + 1) + r * (d + 1) =
          (n + r) * (d + 1))).symm ξ) =
      section43SplitLeftFlat d n r ξ := by
  ext a
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
  rw [section43SplitLeftFlat_apply]
  simp only [splitFirst, castFinCLE_symm_apply]
  refine congrArg ξ ?_
  apply Fin.ext
  simp [finProdFinEquiv]

private theorem splitLast_castFinCLE_symm_eq_section43SplitRightFlat
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    splitLast (n * (d + 1)) (r * (d + 1))
        ((castFinCLE (by ring : n * (d + 1) + r * (d + 1) =
          (n + r) * (d + 1))).symm ξ) =
      section43SplitRightFlat d n r ξ := by
  ext a
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
  rw [section43SplitRightFlat_apply]
  simp only [splitLast, castFinCLE_symm_apply]
  refine congrArg ξ ?_
  apply Fin.ext
  simp [finProdFinEquiv]
  ring

private theorem reindex_tensorProduct_apply_section43Split
    (d n r : ℕ) [NeZero d]
    (F : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
    (G : SchwartzMap (Fin (r * (d + 1)) → ℝ) ℂ)
    (x : Fin ((n + r) * (d + 1)) → ℝ) :
    reindexSchwartzFin
        (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))
        (F.tensorProduct G) x =
      F (section43SplitLeftFlat d n r x) *
        G (section43SplitRightFlat d n r x) := by
  rw [reindexSchwartzFin_apply, SchwartzMap.tensorProduct_apply]
  rw [splitFirst_castFinCLE_symm_eq_section43SplitLeftFlat]
  rw [splitLast_castFinCLE_symm_eq_section43SplitRightFlat]

private theorem section43_fullFlat_pair_eq_splitFlat_pair
    (d n r : ℕ) [NeZero d]
    (x ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    (∑ a : Fin ((n + r) * (d + 1)), (x a : ℂ) * (ξ a : ℂ)) =
      (∑ a : Fin (n * (d + 1)),
        (section43SplitLeftFlat d n r x a : ℂ) *
          (section43SplitLeftFlat d n r ξ a : ℂ)) +
      (∑ a : Fin (r * (d + 1)),
        (section43SplitRightFlat d n r x a : ℂ) *
          (section43SplitRightFlat d n r ξ a : ℂ)) := by
  classical
  let h : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1) := by ring
  calc
    (∑ a : Fin ((n + r) * (d + 1)), (x a : ℂ) * (ξ a : ℂ))
        = ∑ a : Fin (n * (d + 1) + r * (d + 1)),
            (x ((finCongr h) a) : ℂ) * (ξ ((finCongr h) a) : ℂ) := by
          rw [← (finCongr h).sum_comp]
    _ = (∑ a : Fin (n * (d + 1)),
          (x ((finCongr h) (Fin.castAdd (r * (d + 1)) a)) : ℂ) *
            (ξ ((finCongr h) (Fin.castAdd (r * (d + 1)) a)) : ℂ)) +
        (∑ a : Fin (r * (d + 1)),
          (x ((finCongr h) (Fin.natAdd (n * (d + 1)) a)) : ℂ) *
            (ξ ((finCongr h) (Fin.natAdd (n * (d + 1)) a)) : ℂ)) := by
          rw [Fin.sum_univ_add]
    _ = (∑ a : Fin (n * (d + 1)),
        (section43SplitLeftFlat d n r x a : ℂ) *
          (section43SplitLeftFlat d n r ξ a : ℂ)) +
      (∑ a : Fin (r * (d + 1)),
        (section43SplitRightFlat d n r x a : ℂ) *
          (section43SplitRightFlat d n r ξ a : ℂ)) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro a _ha
            obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
            rw [section43SplitLeftFlat_apply, section43SplitLeftFlat_apply]
            have hidx : (finCongr h) (Fin.castAdd (r * (d + 1)) (finProdFinEquiv p)) =
                finProdFinEquiv (Fin.castAdd r p.1, p.2) := by
              apply Fin.ext
              simp [finProdFinEquiv]
            rw [hidx]
          · refine Finset.sum_congr rfl ?_
            intro a _ha
            obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
            rw [section43SplitRightFlat_apply, section43SplitRightFlat_apply]
            have hidx : (finCongr h) (Fin.natAdd (n * (d + 1)) (finProdFinEquiv p)) =
                finProdFinEquiv (Fin.natAdd n p.1, p.2) := by
              apply Fin.ext
              simp [finProdFinEquiv]
              ring
            rw [hidx]

private def section43FullFlatProductSplitMeasurableEquiv
    (d n r : ℕ) [NeZero d] :
    (Fin ((n + r) * (d + 1)) → ℝ) ≃ᵐ
      ((Fin (n * (d + 1)) → ℝ) × (Fin (r * (d + 1)) → ℝ)) :=
  ((MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((n + r) * (d + 1)) => ℝ)
    (finCongr (by ring : n * (d + 1) + r * (d + 1) =
      (n + r) * (d + 1)))).symm).trans
    (section43FlatProductSplitMeasurableEquiv
      (n * (d + 1)) (r * (d + 1)))

private theorem section43FullFlatProductSplitMeasurableEquiv_measurePreserving
    (d n r : ℕ) [NeZero d] :
    MeasureTheory.MeasurePreserving
      (section43FullFlatProductSplitMeasurableEquiv d n r)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin ((n + r) * (d + 1)) → ℝ))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (n * (d + 1)) → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (r * (d + 1)) → ℝ))) := by
  let h : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1) := by ring
  let e1 := MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((n + r) * (d + 1)) => ℝ) (finCongr h)
  have he1 : MeasureTheory.MeasurePreserving e1 MeasureTheory.volume MeasureTheory.volume := by
    simpa [e1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin ((n + r) * (d + 1)) => ℝ) (finCongr h))
  have he2 := section43FlatProductSplitMeasurableEquiv_measurePreserving
    (n * (d + 1)) (r * (d + 1))
  simpa [section43FullFlatProductSplitMeasurableEquiv, h, e1] using
    he2.comp (he1.symm e1)

private theorem section43FullFlatProductSplitMeasurableEquiv_fst_apply
    (d n r : ℕ) [NeZero d]
    (x : Fin ((n + r) * (d + 1)) → ℝ) :
    (section43FullFlatProductSplitMeasurableEquiv d n r x).1 =
      section43SplitLeftFlat d n r x := by
  change (section43FlatProductSplitMeasurableEquiv (n * (d + 1)) (r * (d + 1))
      ((castFinCLE (by ring : n * (d + 1) + r * (d + 1) =
          (n + r) * (d + 1))).symm x)).1 =
      section43SplitLeftFlat d n r x
  rw [section43FlatProductSplitMeasurableEquiv_fst_eq_splitFirst]
  exact splitFirst_castFinCLE_symm_eq_section43SplitLeftFlat d n r x

private theorem section43FullFlatProductSplitMeasurableEquiv_snd_apply
    (d n r : ℕ) [NeZero d]
    (x : Fin ((n + r) * (d + 1)) → ℝ) :
    (section43FullFlatProductSplitMeasurableEquiv d n r x).2 =
      section43SplitRightFlat d n r x := by
  change (section43FlatProductSplitMeasurableEquiv (n * (d + 1)) (r * (d + 1))
      ((castFinCLE (by ring : n * (d + 1) + r * (d + 1) =
          (n + r) * (d + 1))).symm x)).2 =
      section43SplitRightFlat d n r x
  rw [section43FlatProductSplitMeasurableEquiv_snd_eq_splitLast]
  exact splitLast_castFinCLE_symm_eq_section43SplitRightFlat d n r x

/-- The physics Fourier transform factors over a reindexed tensor product. -/
theorem physicsFourierFlatCLM_reindex_tensorProduct_apply
    (d n r : ℕ) [NeZero d]
    (F : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
    (G : SchwartzMap (Fin (r * (d + 1)) → ℝ) ℂ)
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
      (reindexSchwartzFin
        (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))
        (F.tensorProduct G)) ξ =
    physicsFourierFlatCLM F (section43SplitLeftFlat d n r ξ) *
      physicsFourierFlatCLM G (section43SplitRightFlat d n r ξ) := by
  rw [← physicsFourierFlatCLM_integral, ← physicsFourierFlatCLM_integral,
    ← physicsFourierFlatCLM_integral]
  let e := section43FullFlatProductSplitMeasurableEquiv d n r
  let ξL := section43SplitLeftFlat d n r ξ
  let ξR := section43SplitRightFlat d n r ξ
  let g : ((Fin (n * (d + 1)) → ℝ) × (Fin (r * (d + 1)) → ℝ)) → ℂ := fun p =>
    Complex.exp (Complex.I *
      ((∑ a, (p.1 a : ℂ) * (ξL a : ℂ)) +
       (∑ b, (p.2 b : ℂ) * (ξR b : ℂ)))) * (F p.1 * G p.2)
  have he := section43FullFlatProductSplitMeasurableEquiv_measurePreserving d n r
  calc
    (∫ x : Fin ((n + r) * (d + 1)) → ℝ,
      Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) *
        reindexSchwartzFin
          (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))
          (F.tensorProduct G) x)
        = ∫ x : Fin ((n + r) * (d + 1)) → ℝ, g (e x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [g]
          rw [section43FullFlatProductSplitMeasurableEquiv_fst_apply]
          rw [section43FullFlatProductSplitMeasurableEquiv_snd_apply]
          rw [splitFirst_castFinCLE_symm_eq_section43SplitLeftFlat]
          rw [splitLast_castFinCLE_symm_eq_section43SplitRightFlat]
          rw [section43_fullFlat_pair_eq_splitFlat_pair]
    _ = ∫ p : (Fin (n * (d + 1)) → ℝ) × (Fin (r * (d + 1)) → ℝ), g p := by
          exact he.integral_comp' (g := g)
    _ = ∫ p : (Fin (n * (d + 1)) → ℝ) × (Fin (r * (d + 1)) → ℝ),
          (Complex.exp (Complex.I * ∑ a, (p.1 a : ℂ) * (ξL a : ℂ)) * F p.1) *
            (Complex.exp (Complex.I * ∑ b, (p.2 b : ℂ) * (ξR b : ℂ)) * G p.2) := by
          apply integral_congr_ae
          filter_upwards with p
          dsimp [g]
          rw [mul_add, Complex.exp_add]
          ring
    _ = (∫ x : Fin (n * (d + 1)) → ℝ,
          Complex.exp (Complex.I * ∑ a, (x a : ℂ) * (ξL a : ℂ)) * F x) *
        (∫ y : Fin (r * (d + 1)) → ℝ,
          Complex.exp (Complex.I * ∑ b, (y b : ℂ) * (ξR b : ℂ)) * G y) := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_prod_mul
              (μ := (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (n * (d + 1)) → ℝ)))
              (ν := (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (r * (d + 1)) → ℝ)))
              (f := fun x : Fin (n * (d + 1)) → ℝ =>
                Complex.exp (Complex.I * ∑ a, (x a : ℂ) * (ξL a : ℂ)) * F x)
              (g := fun y : Fin (r * (d + 1)) → ℝ =>
                Complex.exp (Complex.I * ∑ b, (y b : ℂ) * (ξR b : ℂ)) * G y))

@[simp] theorem section43LeftBorchersBlock_apply
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r))
    (i : Fin n) (μ : Fin (d + 1)) :
    section43LeftBorchersBlock d n r hr q i μ =
      q ⟨n - i.val, by omega⟩ μ := rfl

/-- The Borchers-left block is empty when the left component has length zero. -/
theorem section43LeftBorchersBlock_zero_left
    (d r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (0 + r)) :
    section43LeftBorchersBlock d 0 r hr q = 0 := by
  ext i
  exact Fin.elim0 i

/-- With no left block, the right tail block is the full cumulative-tail block. -/
theorem section43RightTailBlock_zero_left
    (d m : ℕ) [NeZero d]
    (q : NPointDomain d (m + 1)) :
    section43RightTailBlock d 0 (m + 1)
        (fun i : Fin (0 + (m + 1)) =>
          q (Fin.cast (Nat.zero_add (m + 1)) i)) = q := by
  ext j μ
  simp [section43RightTailBlock]

/-- The shifted Borchers-left block as a continuous linear map. -/
noncomputable def section43LeftBorchersBlockCLM
    (d n r : ℕ) [NeZero d] (hr : 0 < r) :
    NPointDomain d (n + r) →L[ℝ] NPointDomain d n where
  toFun := section43LeftBorchersBlock d n r hr
  map_add' := by
    intro q q'
    ext i μ
    simp [section43LeftBorchersBlock, Pi.add_apply]
  map_smul' := by
    intro c q
    ext i μ
    simp [section43LeftBorchersBlock, Pi.smul_apply]
  cont := by
    unfold section43LeftBorchersBlock
    fun_prop

@[simp] theorem section43LeftBorchersBlockCLM_apply
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r)) :
    section43LeftBorchersBlockCLM d n r hr q =
      section43LeftBorchersBlock d n r hr q := rfl

/-- The ordinary right-tail block as a continuous linear map. -/
noncomputable def section43RightTailBlockCLM
    (d n r : ℕ) [NeZero d] :
    NPointDomain d (n + r) →L[ℝ] NPointDomain d r where
  toFun := section43RightTailBlock d n r
  map_add' := by
    intro q q'
    ext i μ
    simp [section43RightTailBlock, Pi.add_apply]
  map_smul' := by
    intro c q
    ext i μ
    simp [section43RightTailBlock, Pi.smul_apply]
  cont := by
    unfold section43RightTailBlock
    fun_prop

@[simp] theorem section43RightTailBlockCLM_apply
    (d n r : ℕ) [NeZero d]
    (q : NPointDomain d (n + r)) :
    section43RightTailBlockCLM d n r q =
      section43RightTailBlock d n r q := rfl

/-- The shifted Borchers-left block pulled back to full flat frequency
coordinates through cumulative-tail momentum. -/
noncomputable def section43LeftBorchersFlatCLM
    (d n r : ℕ) [NeZero d] (hr : 0 < r) :
    (Fin ((n + r) * (d + 1)) → ℝ) →L[ℝ] NPointDomain d n :=
  (section43LeftBorchersBlockCLM d n r hr).comp
    (section43CumulativeTailMomentumCLE d (n + r)).toContinuousLinearMap

@[simp] theorem section43LeftBorchersFlatCLM_apply
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    section43LeftBorchersFlatCLM d n r hr ξ =
      section43LeftBorchersBlock d n r hr
        (section43CumulativeTailMomentumCLE d (n + r) ξ) := rfl

/-- The ordinary right-tail block pulled back to full flat frequency
coordinates through cumulative-tail momentum. -/
noncomputable def section43RightTailFlatCLM
    (d n r : ℕ) [NeZero d] :
    (Fin ((n + r) * (d + 1)) → ℝ) →L[ℝ] NPointDomain d r :=
  (section43RightTailBlockCLM d n r).comp
    (section43CumulativeTailMomentumCLE d (n + r)).toContinuousLinearMap

@[simp] theorem section43RightTailFlatCLM_apply
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    section43RightTailFlatCLM d n r ξ =
      section43RightTailBlock d n r
        (section43CumulativeTailMomentumCLE d (n + r) ξ) := rfl

/-- Pointwise product of scalar-valued Schwartz maps. -/
def section43SchwartzMul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) F G

@[simp] theorem section43SchwartzMul_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : SchwartzMap E ℂ) (x : E) :
    section43SchwartzMul F G x = F x * G x := rfl

/-- Total-momentum zero makes the zeroth corrected cumulative-tail momentum
zero.  Spatial components of `section43CumulativeTailMomentumCLE` are scaled,
so the zero-form is the useful invariant statement. -/
theorem section43CumulativeTailMomentumCLE_head_zero_of_totalMomentumFlat
    (d N : ℕ) [NeZero d] (hN : 0 < N)
    {ξ : Fin (N * (d + 1)) → ℝ}
    (hξ : section43TotalMomentumFlat d N ξ = 0) :
    section43CumulativeTailMomentumCLE d N ξ ⟨0, hN⟩ = 0 := by
  ext μ
  have hsum : (∑ k : Fin N, ξ (finProdFinEquiv (k, μ))) = 0 := by
    simpa [section43TotalMomentumFlat] using congrFun hξ μ
  by_cases hμ : μ = 0
  · subst μ
    simp [section43CumulativeTailMomentumCLE_apply, hsum]
  · simp [section43CumulativeTailMomentumCLE_apply, hμ, hsum]

/-- Spectral-region membership makes the zeroth corrected cumulative-tail
momentum vanish. -/
theorem section43WightmanSpectralRegion_cumulativeTail_head_zero
    (d N : ℕ) [NeZero d] (hN : 0 < N)
    {ξ : Fin (N * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d N) :
    section43CumulativeTailMomentumCLE d N ξ ⟨0, hN⟩ = 0 :=
  section43CumulativeTailMomentumCLE_head_zero_of_totalMomentumFlat
    (d := d) (N := N) hN hξ.2

/-- Split cumulative-tail coordinates into the zeroth momentum coordinate and
the remaining tail coordinates. -/
noncomputable def section43CumulativeTailHeadTailLinearEquiv
    (d N' : ℕ) [NeZero d] :
    NPointDomain d (N' + 1) ≃ₗ[ℝ]
      (SpacetimeDim d × NPointDomain d N') where
  toFun q := (q 0, fun j => q j.succ)
  invFun p := fun i => Fin.cases p.1 p.2 i
  map_add' := by
    intro q r
    ext i μ <;> rfl
  map_smul' := by
    intro a q
    ext i μ <;> rfl
  left_inv := by
    intro q
    ext i μ
    cases i using Fin.cases <;> rfl
  right_inv := by
    intro p
    ext i μ <;> rfl

/-- Continuous-linear cumulative-tail head-tail split. -/
noncomputable def section43CumulativeTailHeadTailCLE
    (d N' : ℕ) [NeZero d] :
    NPointDomain d (N' + 1) ≃L[ℝ]
      (SpacetimeDim d × NPointDomain d N') :=
  (section43CumulativeTailHeadTailLinearEquiv d N').toContinuousLinearEquiv

@[simp] theorem section43CumulativeTailHeadTailCLE_head
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) :
    (section43CumulativeTailHeadTailCLE d N' q).1 = q 0 := rfl

@[simp] theorem section43CumulativeTailHeadTailCLE_tail
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) (j : Fin N') :
    (section43CumulativeTailHeadTailCLE d N' q).2 j = q j.succ := rfl

@[simp] theorem section43CumulativeTailHeadTailCLE_symm_zero
    (d N' : ℕ) [NeZero d]
    (p : SpacetimeDim d × NPointDomain d N') :
    (section43CumulativeTailHeadTailCLE d N').symm p 0 = p.1 := rfl

@[simp] theorem section43CumulativeTailHeadTailCLE_symm_succ
    (d N' : ℕ) [NeZero d]
    (p : SpacetimeDim d × NPointDomain d N') (j : Fin N') :
    (section43CumulativeTailHeadTailCLE d N').symm p j.succ = p.2 j := rfl

/-- Forward flattened head-tail coordinates for cumulative-tail momenta. -/
def section43CumulativeTailHeadTailFlatForward
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) :
    Fin ((d + 1) + (N' * (d + 1))) → ℝ :=
  Fin.addCases
    (fun μ : Fin (d + 1) => q 0 μ)
    (fun j : Fin (N' * (d + 1)) =>
      let p := finProdFinEquiv.symm j
      q p.1.succ p.2)

/-- Inverse to `section43CumulativeTailHeadTailFlatForward`. -/
def section43CumulativeTailHeadTailFlatInverse
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) :
    NPointDomain d (N' + 1) :=
  fun i μ =>
    Fin.cases
      (η (Fin.castAdd (N' * (d + 1)) μ))
      (fun j : Fin N' => η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))))
      i

@[simp] theorem section43CumulativeTailHeadTailFlatForward_head
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) (μ : Fin (d + 1)) :
    section43CumulativeTailHeadTailFlatForward d N' q
        (Fin.castAdd (N' * (d + 1)) μ) =
      q 0 μ := by
  simp [section43CumulativeTailHeadTailFlatForward]

@[simp] theorem section43CumulativeTailHeadTailFlatForward_tail
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) (j : Fin N') (μ : Fin (d + 1)) :
    section43CumulativeTailHeadTailFlatForward d N' q
        (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) =
      q j.succ μ := by
  unfold section43CumulativeTailHeadTailFlatForward
  rw [Fin.addCases_right]
  change
    q (finProdFinEquiv.symm (finProdFinEquiv (j, μ))).1.succ
        (finProdFinEquiv.symm (finProdFinEquiv (j, μ))).2 =
      q j.succ μ
  simp

@[simp] theorem section43CumulativeTailHeadTailFlatInverse_zero
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ) (μ : Fin (d + 1)) :
    section43CumulativeTailHeadTailFlatInverse d N' η 0 μ =
      η (Fin.castAdd (N' * (d + 1)) μ) := by
  simp [section43CumulativeTailHeadTailFlatInverse]

@[simp] theorem section43CumulativeTailHeadTailFlatInverse_succ
    (d N' : ℕ) [NeZero d]
    (η : Fin ((d + 1) + (N' * (d + 1))) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    section43CumulativeTailHeadTailFlatInverse d N' η j.succ μ =
      η (Fin.natAdd (d + 1) (finProdFinEquiv (j, μ))) := by
  simp [section43CumulativeTailHeadTailFlatInverse]

noncomputable def section43CumulativeTailHeadTailFlatLinearEquiv
    (d N' : ℕ) [NeZero d] :
    NPointDomain d (N' + 1) ≃ₗ[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ) where
  toFun := section43CumulativeTailHeadTailFlatForward d N'
  invFun := section43CumulativeTailHeadTailFlatInverse d N'
  map_add' := by
    intro q r
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro μ
      simp [section43CumulativeTailHeadTailFlatForward, Pi.add_apply]
    · intro j
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective j
      rcases p with ⟨j, μ⟩
      simp [section43CumulativeTailHeadTailFlatForward, Pi.add_apply]
  map_smul' := by
    intro a q
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro μ
      simp [section43CumulativeTailHeadTailFlatForward, Pi.smul_apply]
    · intro j
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective j
      rcases p with ⟨j, μ⟩
      simp [section43CumulativeTailHeadTailFlatForward, Pi.smul_apply]
  left_inv := by
    intro q
    ext i μ
    cases i using Fin.cases <;> simp
  right_inv := by
    intro η
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro μ
      simp
    · intro j
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective j
      rcases p with ⟨j, μ⟩
      simp

/-- Flattened head-tail coordinates for cumulative-tail momenta: the head is
`q 0`, followed by the flattened tail `(q 1, ..., q N')`. -/
noncomputable def section43CumulativeTailHeadTailFlatCLE
    (d N' : ℕ) [NeZero d] :
    NPointDomain d (N' + 1) ≃L[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ) :=
  (section43CumulativeTailHeadTailFlatLinearEquiv d N').toContinuousLinearEquiv

@[simp] theorem section43CumulativeTailHeadTailFlatCLE_splitFirst
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) :
    splitFirst (d + 1) (N' * (d + 1))
        (section43CumulativeTailHeadTailFlatCLE d N' q) =
      q 0 := by
  ext μ
  simp [splitFirst, section43CumulativeTailHeadTailFlatCLE,
    section43CumulativeTailHeadTailFlatLinearEquiv]

@[simp] theorem section43CumulativeTailHeadTailFlatCLE_splitLast
    (d N' : ℕ) [NeZero d]
    (q : NPointDomain d (N' + 1)) :
    splitLast (d + 1) (N' * (d + 1))
        (section43CumulativeTailHeadTailFlatCLE d N' q) =
      flattenCLEquivReal N' (d + 1) (fun j : Fin N' => q j.succ) := by
  ext j
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective j
  rcases p with ⟨j, μ⟩
  simp [splitLast, section43CumulativeTailHeadTailFlatCLE,
    section43CumulativeTailHeadTailFlatLinearEquiv,
    flattenCLEquivReal_apply]

/-- For `0 < n`, tail coordinates determine the Borchers-left block together
with the right tail block.  The source represents `(q 1, ..., q (n + m))`;
the output duplicates the shared coordinate `q n` but forgets no tail
coordinate. -/
noncomputable def section43TailToBorchersProductCLM
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    NPointDomain d (n + m) →L[ℝ]
      (NPointDomain d n × NPointDomain d (m + 1)) where
  toFun qt :=
    (fun i μ => qt ⟨n - 1 - i.val, by omega⟩ μ,
     fun j μ => qt ⟨n - 1 + j.val, by omega⟩ μ)
  map_add' := by
    intro q r
    ext i μ <;> rfl
  map_smul' := by
    intro a q
    ext i μ <;> rfl
  cont := by
    fun_prop

@[simp] theorem section43TailToBorchersProductCLM_left_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) (i : Fin n) (μ : Fin (d + 1)) :
    (section43TailToBorchersProductCLM d n m hn qt).1 i μ =
      qt ⟨n - 1 - i.val, by omega⟩ μ := rfl

@[simp] theorem section43TailToBorchersProductCLM_right_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) (j : Fin (m + 1)) (μ : Fin (d + 1)) :
    (section43TailToBorchersProductCLM d n m hn qt).2 j μ =
      qt ⟨n - 1 + j.val, by omega⟩ μ := rfl

/-- The tail-to-Borchers product map is injective: the left output recovers
tail coordinates before `q n`, and the right output recovers coordinates from
`q n` onward. -/
theorem section43TailToBorchersProductCLM_injective
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    Function.Injective (section43TailToBorchersProductCLM d n m hn) := by
  intro q r hqr
  ext k μ
  by_cases hk : k.val < n
  · let i : Fin n := ⟨n - 1 - k.val, by omega⟩
    have hleft :=
      congrArg
        (fun p : NPointDomain d n × NPointDomain d (m + 1) => p.1 i μ) hqr
    have hidx : (⟨n - 1 - i.val, by omega⟩ : Fin (n + m)) = k := by
      apply Fin.ext
      dsimp [i]
      omega
    simpa [i, hidx] using hleft
  · let j : Fin (m + 1) := ⟨k.val - (n - 1), by omega⟩
    have hright :=
      congrArg
        (fun p : NPointDomain d n × NPointDomain d (m + 1) => p.2 j μ) hqr
    have hidx : (⟨n - 1 + j.val, by omega⟩ : Fin (n + m)) = k := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa [j, hidx] using hright

/-- Finite-dimensional injectivity gives the antilipschitz condition needed by
`SchwartzMap.compCLMOfAntilipschitz`. -/
theorem section43TailToBorchersProductCLM_antilipschitz
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    ∃ K, AntilipschitzWith K (section43TailToBorchersProductCLM d n m hn) := by
  rcases (((section43TailToBorchersProductCLM d n m hn :
      NPointDomain d (n + m) →L[ℝ]
        (NPointDomain d n × NPointDomain d (m + 1))) :
      NPointDomain d (n + m) →ₗ[ℝ]
        (NPointDomain d n × NPointDomain d (m + 1))).injective_iff_antilipschitz.mp
        (section43TailToBorchersProductCLM_injective d n m hn)) with
    ⟨K, _hKpos, hK⟩
  exact ⟨K, hK⟩

/-- Raw coordinate function underlying the direct concat tail map. -/
def section43TailToBorchersConcatFun
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) : NPointDomain d (n + (m + 1)) :=
    Fin.addCases
      (fun i : Fin n => qt ⟨n - 1 - i.val, by omega⟩)
      (fun j : Fin (m + 1) => qt ⟨n - 1 + j.val, by omega⟩)

/-- Direct concat version of the injective tail map.  This is the shape needed
to pull back `SchwartzMap.tensorProduct`: the first `n` coordinates are the
Borchers-left block, and the final `m + 1` coordinates are the right tail. -/
noncomputable def section43TailToBorchersConcatCLM
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    NPointDomain d (n + m) →L[ℝ] NPointDomain d (n + (m + 1)) where
  toFun := section43TailToBorchersConcatFun d n m hn
  map_add' := by
    intro q r
    ext k μ
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [section43TailToBorchersConcatFun, Pi.add_apply]
    · intro j
      simp [section43TailToBorchersConcatFun, Pi.add_apply]
  map_smul' := by
    intro a q
    ext k μ
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [section43TailToBorchersConcatFun, Pi.smul_apply]
    · intro j
      simp [section43TailToBorchersConcatFun, Pi.smul_apply]
  cont := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    refine Fin.addCases ?_ ?_ k
    · intro i
      let idx : Fin (n + m) := ⟨n - 1 - i.val, by omega⟩
      simpa [section43TailToBorchersConcatFun, idx] using
        ((continuous_apply μ).comp (continuous_apply idx) :
          Continuous fun qt : NPointDomain d (n + m) => qt idx μ)
    · intro j
      let idx : Fin (n + m) := ⟨n - 1 + j.val, by omega⟩
      simpa [section43TailToBorchersConcatFun, idx] using
        ((continuous_apply μ).comp (continuous_apply idx) :
          Continuous fun qt : NPointDomain d (n + m) => qt idx μ)

@[simp] theorem section43TailToBorchersConcatCLM_left_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) (i : Fin n) (μ : Fin (d + 1)) :
    section43TailToBorchersConcatCLM d n m hn qt (Fin.castAdd (m + 1) i) μ =
      qt ⟨n - 1 - i.val, by omega⟩ μ := by
  change section43TailToBorchersConcatFun d n m hn qt
      (Fin.castAdd (m + 1) i) μ = qt ⟨n - 1 - i.val, by omega⟩ μ
  simp [section43TailToBorchersConcatFun]

@[simp] theorem section43TailToBorchersConcatCLM_right_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) (j : Fin (m + 1)) (μ : Fin (d + 1)) :
    section43TailToBorchersConcatCLM d n m hn qt (Fin.natAdd n j) μ =
      qt ⟨n - 1 + j.val, by omega⟩ μ := by
  change section43TailToBorchersConcatFun d n m hn qt
      (Fin.natAdd n j) μ = qt ⟨n - 1 + j.val, by omega⟩ μ
  simp [section43TailToBorchersConcatFun]

@[simp] theorem section43TailToBorchersConcatCLM_splitFirst
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) :
    splitFirst n (m + 1) (section43TailToBorchersConcatCLM d n m hn qt) =
      (section43TailToBorchersProductCLM d n m hn qt).1 := by
  ext i μ
  simp [splitFirst]

@[simp] theorem section43TailToBorchersConcatCLM_splitLast
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (qt : NPointDomain d (n + m)) :
    splitLast n (m + 1) (section43TailToBorchersConcatCLM d n m hn qt) =
      (section43TailToBorchersProductCLM d n m hn qt).2 := by
  ext j μ
  simp [splitLast]

/-- The direct concat tail map is injective, because its split outputs recover
the already-injective product tail map. -/
theorem section43TailToBorchersConcatCLM_injective
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    Function.Injective (section43TailToBorchersConcatCLM d n m hn) := by
  intro q r hqr
  apply section43TailToBorchersProductCLM_injective d n m hn
  apply Prod.ext
  · rw [← section43TailToBorchersConcatCLM_splitFirst d n m hn q,
      ← section43TailToBorchersConcatCLM_splitFirst d n m hn r, hqr]
  · rw [← section43TailToBorchersConcatCLM_splitLast d n m hn q,
      ← section43TailToBorchersConcatCLM_splitLast d n m hn r, hqr]

/-- Finite-dimensional injectivity gives the antilipschitz condition for the
direct concat pullback. -/
theorem section43TailToBorchersConcatCLM_antilipschitz
    (d n m : ℕ) [NeZero d] (hn : 0 < n) :
    ∃ K, AntilipschitzWith K (section43TailToBorchersConcatCLM d n m hn) := by
  rcases (((section43TailToBorchersConcatCLM d n m hn :
      NPointDomain d (n + m) →L[ℝ] NPointDomain d (n + (m + 1))) :
      NPointDomain d (n + m) →ₗ[ℝ] NPointDomain d (n + (m + 1))).injective_iff_antilipschitz.mp
        (section43TailToBorchersConcatCLM_injective d n m hn)) with
    ⟨K, _hKpos, hK⟩
  exact ⟨K, hK⟩

/-- The visible tail product in cumulative-tail coordinates, after removing
the total-momentum head coordinate.  This is a genuine Schwartz map because
the tail-to-concat map is injective/antilipschitz. -/
noncomputable def section43VisibleTailProductSchwartz
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (NPointDomain d (n + m)) ℂ :=
  let hanti := Classical.choose_spec
    (section43TailToBorchersConcatCLM_antilipschitz d n m hn)
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (section43TailToBorchersConcatCLM d n m hn).hasTemperateGrowth hanti
    (((section43FrequencyRepresentative (d := d) n φ).conj).tensorProduct
      (section43FrequencyRepresentative (d := d) (m + 1) ψ))

@[simp] theorem section43VisibleTailProductSchwartz_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (qt : NPointDomain d (n + m)) :
    section43VisibleTailProductSchwartz d n m hn φ ψ qt =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43TailToBorchersProductCLM d n m hn qt).1) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43TailToBorchersProductCLM d n m hn qt).2 := by
  simp [section43VisibleTailProductSchwartz, SchwartzMap.tensorProduct_apply]

/-- Flatten the visible tail product so it can be extended by the head-block
bump construction. -/
noncomputable def section43VisibleTailProductFlatSchwartz
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenCLEquivReal (n + m) (d + 1)).symm
    (section43VisibleTailProductSchwartz d n m hn φ ψ)

@[simp] theorem section43VisibleTailProductFlatSchwartz_apply
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (u : Fin ((n + m) * (d + 1)) → ℝ) :
    section43VisibleTailProductFlatSchwartz d n m hn φ ψ u =
      section43VisibleTailProductSchwartz d n m hn φ ψ
        ((flattenCLEquivReal (n + m) (d + 1)).symm u) := by
  simp [section43VisibleTailProductFlatSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Head-bump extension of the visible tail product in flattened head-tail
coordinates.  This is the legal Schwartz replacement for the false pullback
of a tail function by a projection. -/
noncomputable def section43CutoffTailProductHeadTailSchwartz
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (Fin ((d + 1) + ((n + m) * (d + 1))) → ℝ) ℂ :=
  headBlockBumpExtension (d + 1) ((n + m) * (d + 1))
    (section43VisibleTailProductFlatSchwartz d n m hn φ ψ)

/-- Cutoff-tail product as a Schwartz function of the full cumulative-tail
coordinate `q`.  The cutoff is hidden in `headBlockBumpExtension`; on
`q 0 = 0` it evaluates to the visible tail product. -/
noncomputable def section43TotalMomentumCutoffSchwartz
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (NPointDomain d (n + (m + 1))) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43CumulativeTailHeadTailFlatCLE d (n + m))
    (section43CutoffTailProductHeadTailSchwartz d n m hn φ ψ)

theorem section43TotalMomentumCutoffSchwartz_one_on_totalMomentum_zero
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {q : NPointDomain d (n + (m + 1))}
    (hq0 : q 0 = 0) :
    section43TotalMomentumCutoffSchwartz d n m hn φ ψ q =
      section43VisibleTailProductSchwartz d n m hn φ ψ
        (fun j : Fin (n + m) => q j.succ) := by
  let e := section43CumulativeTailHeadTailFlatCLE d (n + m)
  let G := section43VisibleTailProductFlatSchwartz d n m hn φ ψ
  let B := section43CutoffTailProductHeadTailSchwartz d n m hn φ ψ
  have hhead : splitFirst (d + 1) ((n + m) * (d + 1)) (e q) = 0 := by
    ext μ
    simpa [e] using congrFun hq0 μ
  have heq : e q =
      zeroHeadBlockShift (m := d + 1) (n := (n + m) * (d + 1))
        (splitLast (d + 1) ((n + m) * (d + 1)) (e q)) :=
    eq_zeroHeadBlockShift_of_splitFirst_eq_zero hhead
  calc
    section43TotalMomentumCutoffSchwartz d n m hn φ ψ q
        = B (e q) := by
            simp [section43TotalMomentumCutoffSchwartz, e, B,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    _ = B (zeroHeadBlockShift (m := d + 1) (n := (n + m) * (d + 1))
          (splitLast (d + 1) ((n + m) * (d + 1)) (e q))) := by
            exact congrArg B heq
    _ = G (splitLast (d + 1) ((n + m) * (d + 1)) (e q)) := by
            simp [B, section43CutoffTailProductHeadTailSchwartz, G,
              headBlockBumpExtension_zeroHeadBlockShift
                (d + 1) ((n + m) * (d + 1)) G
                (splitLast (d + 1) ((n + m) * (d + 1)) (e q))]
    _ = G (flattenCLEquivReal (n + m) (d + 1)
          (fun j : Fin (n + m) => q j.succ)) := by
            simp [e]
    _ = section43VisibleTailProductSchwartz d n m hn φ ψ
          (fun j : Fin (n + m) => q j.succ) := by
            simp [G]

/-- The `n = 0` visible product branch.  No tail-only injective map is used:
the left factor is the vacuum/empty-block scalar and the right factor is the
full right frequency representative. -/
noncomputable def section43VisibleProductZeroLeftSchwartz
    (d m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d 0) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (NPointDomain d (m + 1)) ℂ :=
  (star
    ((section43FrequencyRepresentative (d := d) 0 φ)
      (0 : NPointDomain d 0))) •
    (section43FrequencyRepresentative (d := d) (m + 1) ψ)

@[simp] theorem section43VisibleProductZeroLeftSchwartz_apply
    (d m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d 0) (ψ : SchwartzNPoint d (m + 1))
    (q : NPointDomain d (m + 1)) :
    section43VisibleProductZeroLeftSchwartz d m φ ψ q =
      star
        ((section43FrequencyRepresentative (d := d) 0 φ)
          (0 : NPointDomain d 0)) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ) q := by
  simp [section43VisibleProductZeroLeftSchwartz, smul_eq_mul]

/-- The one-variable Paley test at positive imaginary height `t`, with the
`2π` scaling used by the Section 4.3 Fourier normalization. -/
noncomputable def section43PsiZTimeTest (t : ℝ) (ht : 0 < t) :
    SchwartzMap ℝ ℂ :=
  SCV.schwartzPsiZ
    (((2 * Real.pi : ℂ) * (t * Complex.I)))
    (by
      simpa [Complex.mul_im, ht.ne'] using
        mul_pos Real.two_pi_pos ht)

@[simp] theorem section43PsiZTimeTest_apply
    (t : ℝ) (ht : 0 < t) (η : ℝ) :
    section43PsiZTimeTest t ht η =
      SCV.psiZ (((2 * Real.pi : ℂ) * (t * Complex.I))) η := by
  simp [section43PsiZTimeTest, SCV.schwartzPsiZ_apply]

/-- The flat positive-time shift direction used locally in the Section 4.3
right block.  It matches the semigroup convention: shifting forward in
Euclidean time translates flat functions by `-e_time`. -/
abbrev section43FlatTimeShiftDirection (d n : ℕ) :
    Fin (n * (d + 1)) → ℝ :=
  fun k => if (finProdFinEquiv.symm k).2 = 0 then (-1 : ℝ) else 0

/-- The flat right-time-shift direction embedded in the full
`(n + (m + 1))` frequency coordinate. -/
noncomputable def section43SuccRightTimeShiftFlatDirection
    (d n m : ℕ) [NeZero d] :
    Fin ((n + (m + 1)) * (d + 1)) → ℝ :=
  castFinCLE (Nat.add_mul n (m + 1) (d + 1)).symm
    (zeroHeadBlockShift
      (m := n * (d + 1)) (n := (m + 1) * (d + 1))
      (section43FlatTimeShiftDirection d (m + 1)))

/-- Pairing with the embedded right-time-shift direction. -/
noncomputable def section43SuccRightTimeShiftPairingCLM
    (d n m : ℕ) [NeZero d] :
    (Fin ((n + (m + 1)) * (d + 1)) → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin ((n + (m + 1)) * (d + 1)),
    (section43SuccRightTimeShiftFlatDirection d n m i) •
      ContinuousLinearMap.proj (R := ℝ)
        (ι := Fin ((n + (m + 1)) * (d + 1))) (φ := fun _ => ℝ) i

@[simp] theorem section43SuccRightTimeShiftPairingCLM_apply
    (d n m : ℕ) [NeZero d]
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    section43SuccRightTimeShiftPairingCLM d n m ξ =
      ∑ i : Fin ((n + (m + 1)) * (d + 1)),
        section43SuccRightTimeShiftFlatDirection d n m i * ξ i := by
  simp [section43SuccRightTimeShiftPairingCLM]

/-- The nonnegative Paley frequency on the spectral cone is
`η = -λ / (2π)`, where `λ` is the right-time-shift pairing. -/
noncomputable def section43SuccRightEtaCLM
    (d n m : ℕ) [NeZero d] :
    (Fin ((n + (m + 1)) * (d + 1)) → ℝ) →L[ℝ] ℝ :=
  (-(1 / (2 * Real.pi))) •
    section43SuccRightTimeShiftPairingCLM d n m

@[simp] theorem section43SuccRightEtaCLM_apply
    (d n m : ℕ) [NeZero d]
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    section43SuccRightEtaCLM d n m ξ =
      -(∑ i : Fin ((n + (m + 1)) * (d + 1)),
          section43SuccRightTimeShiftFlatDirection d n m i * ξ i) /
        (2 * Real.pi) := by
  simp [section43SuccRightEtaCLM, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm]

theorem section43PsiZTimeTest_comp_eta_hasTemperateGrowth
    (d n m : ℕ) [NeZero d] {t : ℝ} (ht : 0 < t) :
    (fun ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ =>
      section43PsiZTimeTest t ht (section43SuccRightEtaCLM d n m ξ)
    ).HasTemperateGrowth :=
  (section43PsiZTimeTest t ht).hasTemperateGrowth.comp
    (section43SuccRightEtaCLM d n m).hasTemperateGrowth

private theorem section43_fourierInv_eq_cexp_integral
    (χ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourierInv χ ξ =
      ∫ x : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * χ x := by
  have hcoe :
      FourierTransform.fourierInv χ ξ =
        FourierTransform.fourierInv (χ : ℝ → ℂ) ξ := by
    simpa using congrArg (fun g => g ξ) (SchwartzMap.fourierInv_coe (f := χ))
  rw [hcoe, Real.fourierInv_eq' (f := (χ : ℝ → ℂ)) (w := ξ)]
  congr 1
  ext v
  have hinner : ∀ a b : ℝ, @inner ℝ ℝ _ a b = b * a := by
    intro a b
    simp [inner, mul_comm]
  simp only [smul_eq_mul, hinner, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring_nf

/-- One-variable phase evaluation for the Section 4.3 horizontal kernel:
pairing a pure oscillatory phase against the Fourier transform of a Schwartz
test recovers the test at the matching frequency. -/
theorem section43_integral_phase_mul_fourierTransform_eq_eval
    (χ : SchwartzMap ℝ ℂ)
    (lam : ℝ) :
    ∫ τ : ℝ,
      Complex.exp (-(Complex.I * (lam : ℂ) * τ)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) τ =
      χ (-lam / (2 * Real.pi)) := by
  have hfourierInv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) χ) (-lam / (2 * Real.pi)) =
        χ (-lam / (2 * Real.pi)) := by
    set f := (SchwartzMap.fourierTransformCLM ℂ) χ
    have hf : FourierTransform.fourierInv f = χ := by
      simp [f, FourierTransform.fourierInv_fourier_eq χ]
    exact congrArg (fun g : SchwartzMap ℝ ℂ => g (-lam / (2 * Real.pi))) hf
  rw [section43_fourierInv_eq_cexp_integral
      (χ := (SchwartzMap.fourierTransformCLM ℂ) χ)
      (ξ := -lam / (2 * Real.pi))] at hfourierInv
  calc
    ∫ τ : ℝ,
        Complex.exp (-(Complex.I * (lam : ℂ) * τ)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) τ
      =
        ∫ τ : ℝ,
          Complex.exp
              (2 * Real.pi * Complex.I *
                ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (τ : ℂ)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) τ := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with τ
              congr 2
              have harg :
                  2 * Real.pi * Complex.I *
                      ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (τ : ℂ) =
                    -(Complex.I * (lam : ℂ) * τ) := by
                have hscalar_real :
                    (2 * Real.pi) * (-lam / (2 * Real.pi)) * τ =
                      -(lam * τ) := by
                  field_simp [Real.pi_ne_zero]
                have hscalar :
                    ((2 * Real.pi : ℂ) *
                        (((-lam / (2 * Real.pi) : ℝ) : ℂ))) * (τ : ℂ) =
                      -((lam : ℂ) * τ) := by
                  exact_mod_cast hscalar_real
                calc
                  2 * Real.pi * Complex.I *
                      ((-lam / (2 * Real.pi) : ℝ) : ℂ) * (τ : ℂ)
                      = Complex.I *
                          ((((2 * Real.pi : ℂ) *
                              (((-lam / (2 * Real.pi) : ℝ) : ℂ))) *
                            (τ : ℂ))) := by
                            ring_nf
                  _ = Complex.I * (-((lam : ℂ) * τ)) := by rw [hscalar]
                  _ = -(Complex.I * (lam : ℂ) * τ) := by ring_nf
              rw [harg]
    _ = χ (-lam / (2 * Real.pi)) := hfourierInv

/-- Fixed-frequency one-variable functional for the horizontal Paley kernel. -/
noncomputable def section43HorizontalPhasePairingCLM
    (base : ℂ) (lam : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  base •
    ((SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
      (SchwartzMap.smulLeftCLM ℂ
        (fun τ : ℝ =>
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))))))

theorem section43HorizontalPhasePairingCLM_apply
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    section43HorizontalPhasePairingCLM base lam χ =
      base *
        ∫ τ : ℝ,
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) * χ τ := by
  simp [section43HorizontalPhasePairingCLM, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (section43_realOscillatoryPhase_hasTemperateGrowth lam),
    smul_eq_mul]

theorem section43HorizontalPhasePairingCLM_fourierTransform
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    section43HorizontalPhasePairingCLM base lam
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      base * χ (-lam / (2 * Real.pi)) := by
  rw [section43HorizontalPhasePairingCLM_apply]
  rw [section43_integral_phase_mul_fourierTransform_eq_eval]

/-- The branchwise cumulative-tail OS I `(4.24)` product, made Schwartz by the
total-momentum cutoff when `0 < n` and by the zero-left visible product when
`n = 0`. -/
noncomputable def section43OS24CumulativeTailProduct
    (d : ℕ) [NeZero d] :
    (n m : ℕ) →
      SchwartzNPoint d n → SchwartzNPoint d (m + 1) →
        SchwartzMap (NPointDomain d (n + (m + 1))) ℂ
  | 0, m, φ, ψ =>
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43CastNPointCLE d (Nat.zero_add (m + 1)))
        (section43VisibleProductZeroLeftSchwartz d m φ ψ)
  | n + 1, m, φ, ψ =>
      section43TotalMomentumCutoffSchwartz d (n + 1) m (Nat.succ_pos n) φ ψ

theorem section43TailToBorchersProductCLM_left_tail_eq_leftBorchersBlock
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (q : NPointDomain d (n + (m + 1))) :
    (section43TailToBorchersProductCLM d n m hn
      (fun j : Fin (n + m) => q j.succ)).1 =
      section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q := by
  ext i μ
  have hidx :
      (⟨n - 1 - i.val, by omega⟩ : Fin (n + m)).succ =
        (⟨n - i.val, by omega⟩ : Fin (n + (m + 1))) := by
    ext
    simp
    omega
  simpa [section43LeftBorchersBlock] using congrFun (congrArg q hidx) μ

theorem section43TailToBorchersProductCLM_right_tail_eq_rightTailBlock
    (d n m : ℕ) [NeZero d] (hn : 0 < n)
    (q : NPointDomain d (n + (m + 1))) :
    (section43TailToBorchersProductCLM d n m hn
      (fun j : Fin (n + m) => q j.succ)).2 =
      section43RightTailBlock d n (m + 1) q := by
  ext j μ
  have hidx :
      (⟨n - 1 + j.val, by omega⟩ : Fin (n + m)).succ =
        Fin.natAdd n j := by
    ext
    simp
    omega
  simpa [section43RightTailBlock] using congrFun (congrArg q hidx) μ

theorem section43OS24CumulativeTailProduct_eq_visible_of_head_zero
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {q : NPointDomain d (n + (m + 1))}
    (hq0 : q 0 = 0) :
    section43OS24CumulativeTailProduct d n m φ ψ q =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q)) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1) q) := by
  cases n with
  | zero =>
      let e := section43CastNPointCLE d (Nat.zero_add (m + 1))
      have hright : section43RightTailBlock d 0 (m + 1) q = e q := by
        ext j μ
        simp [e, section43RightTailBlock]
      rw [section43OS24CumulativeTailProduct]
      rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      rw [hright]
      simp [e, section43LeftBorchersBlock_zero_left]
  | succ n =>
      have hcut :=
        section43TotalMomentumCutoffSchwartz_one_on_totalMomentum_zero
          (d := d) (n := n + 1) (m := m) (Nat.succ_pos n)
          (φ := φ) (ψ := ψ) (q := q) hq0
      have hleft :=
        section43TailToBorchersProductCLM_left_tail_eq_leftBorchersBlock
          (d := d) (n := n + 1) (m := m) (Nat.succ_pos n) q
      have hright :=
        section43TailToBorchersProductCLM_right_tail_eq_rightTailBlock
          (d := d) (n := n + 1) (m := m) (Nat.succ_pos n) q
      rw [section43OS24CumulativeTailProduct]
      rw [hcut]
      rw [section43VisibleTailProductSchwartz_apply]
      rw [hleft, hright]

/-- The cumulative-tail product pulled back to flat frequency coordinates. -/
noncomputable def section43OS24FlatBaseKernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43CumulativeTailMomentumCLE d (n + (m + 1)))
    (section43OS24CumulativeTailProduct d n m φ ψ)

@[simp] theorem section43OS24FlatBaseKernel_succRight_apply
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    section43OS24FlatBaseKernel_succRight d n m φ ψ ξ =
      section43OS24CumulativeTailProduct d n m φ ψ
        (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ) := by
  simp [section43OS24FlatBaseKernel_succRight,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The visible OS I `(4.24)` scalar on the spectral region. -/
def section43OS24VisibleKernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) : ℂ :=
  let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
  section43PsiZTimeTest t ht (section43SuccRightEtaCLM d n m ξ) *
    (star
      ((section43FrequencyRepresentative (d := d) n φ)
        (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
      (section43FrequencyRepresentative (d := d) (m + 1) ψ)
        (section43RightTailBlock d n (m + 1) qξ))

/-- Direct Schwartz witness for the OS I `(4.24)` kernel.  Its global values
include the cutoff extension; only the spectral-region `EqOn` theorem exposes
the visible formula. -/
noncomputable def section43OS24KernelWitness_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ =>
      section43PsiZTimeTest t ht (section43SuccRightEtaCLM d n m ξ))
    (section43OS24FlatBaseKernel_succRight d n m φ ψ)

theorem section43OS24KernelWitness_succRight_eqOn_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t) :
    Set.EqOn
      (fun ξ => section43OS24KernelWitness_succRight d n m φ ψ t ht ξ)
      (section43OS24VisibleKernel_succRight d n m φ ψ t ht)
      (section43WightmanSpectralRegion d (n + (m + 1))) := by
  intro ξ hξ
  have hN : 0 < n + (m + 1) := by omega
  have hq0 :
      section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ 0 = 0 :=
    section43WightmanSpectralRegion_cumulativeTail_head_zero
      (d := d) (N := n + (m + 1)) hN hξ
  change
    ((SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ =>
        section43PsiZTimeTest t ht (section43SuccRightEtaCLM d n m ξ))
      (section43OS24FlatBaseKernel_succRight d n m φ ψ)) ξ) =
      section43OS24VisibleKernel_succRight d n m φ ψ t ht ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (section43PsiZTimeTest_comp_eta_hasTemperateGrowth d n m ht)]
  rw [section43OS24FlatBaseKernel_succRight_apply]
  rw [section43OS24CumulativeTailProduct_eq_visible_of_head_zero
    (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) hq0]
  rfl

private theorem exists_section43OS24Kernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t) :
    ∃ KOS : SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
      Set.EqOn
        (fun ξ => KOS ξ)
        (section43OS24VisibleKernel_succRight d n m φ ψ t ht)
        (section43WightmanSpectralRegion d (n + (m + 1))) :=
  ⟨section43OS24KernelWitness_succRight d n m φ ψ t ht,
    section43OS24KernelWitness_succRight_eqOn_spectralRegion d n m φ ψ ht⟩

noncomputable def section43OS24Kernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  Classical.choose
    (exists_section43OS24Kernel_succRight d n m φ ψ t ht)

theorem section43OS24Kernel_succRight_eqOn_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t) :
    Set.EqOn
      (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
      (section43OS24VisibleKernel_succRight d n m φ ψ t ht)
      (section43WightmanSpectralRegion d (n + (m + 1))) :=
  Classical.choose_spec
    (exists_section43OS24Kernel_succRight d n m φ ψ t ht)

theorem section43OS24Kernel_succRight_apply_of_mem_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    section43OS24Kernel_succRight d n m φ ψ t ht ξ =
      section43OS24VisibleKernel_succRight d n m φ ψ t ht ξ :=
  section43OS24Kernel_succRight_eqOn_spectralRegion d n m φ ψ ht hξ

/-- Reindex the right split tail sum into the corresponding full tail sum. -/
private theorem section43_splitRight_tail_sum_eq_full_tail
    {d n r : ℕ} [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (j : Fin r) (μ : Fin (d + 1)) :
    (∑ x : Fin r,
      if j.val ≤ x.val then
        ξ (finProdFinEquiv (Fin.natAdd n x, μ))
      else 0) =
    ∑ y : Fin (n + r),
      if (Fin.natAdd n j).val ≤ y.val then
        ξ (finProdFinEquiv (y, μ))
      else 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun x (_hx : x ∈ (Finset.univ.filter fun x : Fin r => j.val ≤ x.val)) =>
      Fin.natAdd n x) ?hmem ?hinj ?hsurj ?hval
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simpa [Fin.natAdd] using Nat.add_le_add_left hx n
  · intro a _ha b _hb h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa [Fin.natAdd] using hval
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hy_val : n + j.val ≤ y.val := by
      simpa [Fin.natAdd] using hy
    have hn_le : n ≤ y.val := by omega
    let x : Fin r := ⟨y.val - n, by omega⟩
    have hxval : j.val ≤ x.val := by
      dsimp [x]
      omega
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_iff_val_le_val.mpr hxval
    · apply Fin.ext
      change n + x.val = y.val
      dsimp [x]
      omega
  · intro _x _hx
    rfl

/-- The right split flat frequency is the inverse cumulative-tail coordinate
of the full right tail block. -/
theorem section43CumulativeTailMomentumCLE_splitRightFlat
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    section43CumulativeTailMomentumCLE d r (section43SplitRightFlat d n r ξ) =
      section43RightTailBlock d n r
        (section43CumulativeTailMomentumCLE d (n + r) ξ) := by
  ext j μ
  have hsum := section43_splitRight_tail_sum_eq_full_tail
    (d := d) (n := n) (r := r) ξ j μ
  by_cases hμ : μ = 0
  · subst μ
    simp [section43CumulativeTailMomentumCLE_apply, section43SplitRightFlat,
      section43RightTailBlock]
    exact hsum
  · simp [section43CumulativeTailMomentumCLE_apply, section43SplitRightFlat,
      section43RightTailBlock, hμ]
    exact hsum

/-- Equivalent inverse-coordinate form of
`section43CumulativeTailMomentumCLE_splitRightFlat`. -/
theorem section43SplitRightFlat_eq_cumulativeTail_rightTail
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    section43SplitRightFlat d n r ξ =
      (section43CumulativeTailMomentumCLE d r).symm
        (section43RightTailBlock d n r
          (section43CumulativeTailMomentumCLE d (n + r) ξ)) := by
  rw [← section43CumulativeTailMomentumCLE_splitRightFlat
    (d := d) (n := n) (r := r) ξ]
  simp

/-- Reindex the negative reversed left split tail as the negative missing
prefix of the full frequency. -/
private theorem section43_negRev_left_tail_sum_eq_neg_prefix
    {d n r : ℕ} [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (j : Fin n) (μ : Fin (d + 1)) :
    (∑ x : Fin n,
      if j ≤ x then
        -ξ (finProdFinEquiv (Fin.castAdd r (Fin.rev x), μ))
      else 0) =
    -(∑ y : Fin (n + r),
      if y.val + j.val < n then
        ξ (finProdFinEquiv (y, μ))
      else 0) := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  rw [Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_bij
    (fun x (_hx : x ∈ (Finset.univ.filter fun x : Fin n => j ≤ x)) =>
      Fin.castAdd r (Fin.rev x)) ?hmem ?hinj ?hsurj ?hval
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hxval : j.val ≤ x.val := Fin.le_iff_val_le_val.mp hx
    rw [Fin.val_castAdd, Fin.val_rev]
    omega
  · intro a _ha b _hb h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd] at hval
    have hrev : Fin.rev a = Fin.rev b := by
      apply Fin.ext
      exact hval
    have h' := congrArg Fin.rev hrev
    simp only [Fin.rev_rev] at h'
    exact h'
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    let a : Fin n := ⟨y.val, by omega⟩
    let x : Fin n := Fin.rev a
    have hxval : j.val ≤ x.val := by
      dsimp [x, a]
      omega
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_iff_val_le_val.mpr hxval
    · apply Fin.ext
      change (Fin.rev x).val = y.val
      have hxrev : Fin.rev x = a := by
        dsimp [x]
        exact Fin.rev_rev a
      rw [hxrev]
  · intro _x _hx
    rfl

/-- Under total momentum zero, the full tail equals the negative missing
prefix. -/
private theorem section43_full_tail_sum_eq_neg_prefix_of_totalMomentum
    {d n r : ℕ} [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (hξ_total : section43TotalMomentumFlat d (n + r) ξ = 0)
    (j : Fin n) (μ : Fin (d + 1)) :
    (∑ y : Fin (n + r),
      if n ≤ y.val + j.val then
        ξ (finProdFinEquiv (y, μ))
      else 0) =
    -(∑ y : Fin (n + r),
      if y.val + j.val < n then
        ξ (finProdFinEquiv (y, μ))
      else 0) := by
  classical
  set pre : ℝ := (∑ y : Fin (n + r),
      if y.val + j.val < n then ξ (finProdFinEquiv (y, μ)) else 0)
  set tail : ℝ := (∑ y : Fin (n + r),
      if n ≤ y.val + j.val then ξ (finProdFinEquiv (y, μ)) else 0)
  have htotalμ : (∑ y : Fin (n + r), ξ (finProdFinEquiv (y, μ))) = 0 := by
    have h := congrArg (fun f : Fin (d + 1) → ℝ => f μ) hξ_total
    simpa [section43TotalMomentumFlat] using h
  have hpartition :
      (∑ y : Fin (n + r), ξ (finProdFinEquiv (y, μ))) = pre + tail := by
    simp only [pre, tail]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _hy
    by_cases hylt : y.val + j.val < n
    · have hnle : ¬ n ≤ y.val + j.val := by omega
      simp [hylt, hnle]
    · have hle : n ≤ y.val + j.val := by omega
      simp [hylt, hle]
  have hzero : pre + tail = 0 := by
    rw [htotalμ] at hpartition
    exact hpartition.symm
  change tail = -pre
  linarith

/-- Combine left reversal reindexing with total momentum zero. -/
private theorem section43_negRev_left_tail_sum_eq_full_tail_of_totalMomentum
    {d n r : ℕ} [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (hξ_total : section43TotalMomentumFlat d (n + r) ξ = 0)
    (j : Fin n) (μ : Fin (d + 1)) :
    (∑ x : Fin n,
      if j ≤ x then
        -ξ (finProdFinEquiv (Fin.castAdd r (Fin.rev x), μ))
      else 0) =
    ∑ y : Fin (n + r),
      if n ≤ y.val + j.val then
        ξ (finProdFinEquiv (y, μ))
      else 0 := by
  exact
    (section43_negRev_left_tail_sum_eq_neg_prefix (d := d) (n := n) (r := r)
      ξ j μ).trans
      (section43_full_tail_sum_eq_neg_prefix_of_totalMomentum
        (d := d) (n := n) (r := r) ξ hξ_total j μ).symm

/-- Under total momentum zero, the negative reversed left split has cumulative
tail coordinates equal to the shifted Borchers-left block. -/
theorem section43CumulativeTailMomentumCLE_negRevFlat_splitLeft_of_totalMomentum
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hξ_total : section43TotalMomentumFlat d (n + r) ξ = 0) :
    section43CumulativeTailMomentumCLE d n
        (section43NegRevFlat d n (section43SplitLeftFlat d n r ξ)) =
      section43LeftBorchersBlock d n r hr
        (section43CumulativeTailMomentumCLE d (n + r) ξ) := by
  ext j μ
  have hsum := section43_negRev_left_tail_sum_eq_full_tail_of_totalMomentum
    (d := d) (n := n) (r := r) ξ hξ_total j μ
  by_cases hμ : μ = 0
  · subst μ
    simp [section43CumulativeTailMomentumCLE_apply, section43NegRevFlat,
      section43SplitLeftFlat, section43LeftBorchersBlock]
    exact hsum
  · simp [section43CumulativeTailMomentumCLE_apply, section43NegRevFlat,
      section43SplitLeftFlat, section43LeftBorchersBlock, hμ]
    exact hsum

/-- Equivalent inverse-coordinate form of the shifted Borchers-left block
identity. -/
theorem section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hξ_total : section43TotalMomentumFlat d (n + r) ξ = 0) :
    (section43CumulativeTailMomentumCLE d n).symm
        (section43LeftBorchersBlock d n r hr
          (section43CumulativeTailMomentumCLE d (n + r) ξ)) =
      section43NegRevFlat d n (section43SplitLeftFlat d n r ξ) := by
  rw [← section43CumulativeTailMomentumCLE_negRevFlat_splitLeft_of_totalMomentum
    (d := d) (n := n) (r := r) hr (ξ := ξ) hξ_total]
  simp

/-- On the Section 4.3 Wightman spectral region, the frozen full-flat
Borchers tensor base factors into the left Borchers frequency representative
and the ordinary right-tail frequency representative. -/
theorem physicsFourierFlatCLM_borchersTensor_eq_frequencyRepresentatives_on_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
    physicsFourierFlatCLM
      (reindexSchwartzFin
        (by ring :
          n * (d + 1) + (m + 1) * (d + 1) =
            (n + (m + 1)) * (d + 1))
        (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (flattenSchwartzNPoint (d := d) ψ)))) ξ =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1) qξ) := by
  classical
  dsimp only
  have hprod := physicsFourierFlatCLM_reindex_tensorProduct_apply
    (d := d) (n := n) (r := m + 1)
    (F := flattenSchwartzNPoint (d := d) φ.borchersConj)
    (G := flattenSchwartzNPoint (d := d) ψ)
    (ξ := ξ)
  have hleftArg := section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
    (d := d) (n := n) (r := m + 1) (Nat.succ_pos m)
    (ξ := ξ) hξ.2
  have hleft :
      physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ.borchersConj)
          (section43SplitLeftFlat d n (m + 1) ξ) =
        star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m)
              (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ))) := by
    rw [physicsFourierFlatCLM_borchersConj_apply]
    rw [← hleftArg]
    rfl
  have hrightArg := section43SplitRightFlat_eq_cumulativeTail_rightTail
    (d := d) (n := n) (r := m + 1) ξ
  have hright :
      physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ)
          (section43SplitRightFlat d n (m + 1) ξ) =
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1)
            (section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ)) := by
    rw [hrightArg]
    rfl
  rw [hprod, hleft, hright]

/-- Spectral-region membership makes the shifted left Borchers block
positive-energy. -/
theorem section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
    (d n r : ℕ) [NeZero d] {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hr : 0 < r)
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r)) :
    section43LeftBorchersBlock d n r hr
        (section43CumulativeTailMomentumCLE d (n + r) ξ) ∈
      section43PositiveEnergyRegion d n := by
  have hq :
      section43CumulativeTailMomentumCLE d (n + r) ξ ∈
        section43PositiveEnergyRegion d (n + r) :=
    section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
      d (n + r) hξ.1
  intro i
  simpa [section43PositiveEnergyRegion, section43LeftBorchersBlock] using
    hq ⟨n - i.val, by omega⟩

/-- Spectral-region membership makes the ordinary right tail block
positive-energy. -/
theorem section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
    (d n r : ℕ) [NeZero d] {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r)) :
    section43RightTailBlock d n r
        (section43CumulativeTailMomentumCLE d (n + r) ξ) ∈
      section43PositiveEnergyRegion d r := by
  have hq :
      section43CumulativeTailMomentumCLE d (n + r) ξ ∈
        section43PositiveEnergyRegion d (n + r) :=
    section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
      d (n + r) hξ.1
  exact section43RightTailBlock_mem_positiveEnergy d n r hq

/-- If the left frequency representative is known to be a Section 4.3
Fourier-Laplace representative, then its value at the shifted Borchers-left
block is the corresponding Fourier-Laplace integral. -/
theorem section43_leftBorchers_frequencyRepresentative_eq_fourierLaplaceIntegral
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    {q : NPointDomain d (n + (m + 1))}
    (_hq : q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hq_left :
      section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q ∈
        section43PositiveEnergyRegion d n) :
    (section43FrequencyRepresentative (d := d) n φ)
      (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q) =
    section43FourierLaplaceIntegral d n f
      (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q) := by
  exact section43FourierLaplaceRepresentative_apply
    (d := d) (n := n) (f := f)
    (Φ := section43FrequencyRepresentative (d := d) n φ)
    hφ_rep hq_left

/-- If the right frequency representative is known to be a Section 4.3
Fourier-Laplace representative, then its value at the ordinary right tail is
the corresponding Fourier-Laplace integral. -/
theorem section43_rightTail_frequencyRepresentative_eq_fourierLaplaceIntegral
    (d n m : ℕ) [NeZero d]
    (ψ : SchwartzNPoint d (m + 1))
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {q : NPointDomain d (n + (m + 1))}
    (_hq : q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hq_right :
      section43RightTailBlock d n (m + 1) q ∈
        section43PositiveEnergyRegion d (m + 1)) :
    (section43FrequencyRepresentative (d := d) (m + 1) ψ)
      (section43RightTailBlock d n (m + 1) q) =
    section43FourierLaplaceIntegral d (m + 1) g
      (section43RightTailBlock d n (m + 1) q) := by
  exact section43FourierLaplaceRepresentative_apply
    (d := d) (n := m + 1) (f := g)
    (Φ := section43FrequencyRepresentative (d := d) (m + 1) ψ)
    hψ_rep hq_right

end OSReconstruction
