import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceWitness

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- A single derivative slot in the Section 4.3 Fourier-Laplace integrand.

`time k` means the derivative hits the Laplace exponential and contributes the
time-coordinate scalar from the direction.  `spatial i` means the derivative
hits the spatial Fourier argument and contributes the `i`th spatial-coordinate
scalar from the direction. -/
inductive Section43DerivativeAtom (d n : ℕ) where
  | time (k : Fin n)
  | spatial (i : Fin n × Fin d)
  deriving DecidableEq, Fintype

/-- A length-`r` derivative word records which factor each derivative slot hits.
The slot order follows `iteratedFDeriv_succ_apply_left`: index `0` is the
newest derivative direction when passing from `r` to `r + 1`. -/
abbrev Section43DerivativeWord (d n r : ℕ) :=
  Fin r → Section43DerivativeAtom d n

/-- The derivative atom type is the finite disjoint union of time-coordinate
atoms and spatial-coordinate atoms. -/
def section43DerivativeAtomEquivSum (d n : ℕ) :
    Section43DerivativeAtom d n ≃ (Fin n) ⊕ (Fin n × Fin d) where
  toFun
    | Section43DerivativeAtom.time k => Sum.inl k
    | Section43DerivativeAtom.spatial i => Sum.inr i
  invFun
    | Sum.inl k => Section43DerivativeAtom.time k
    | Sum.inr i => Section43DerivativeAtom.spatial i
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro a
    cases a <;> rfl

/-- Split a finite sum over derivative atoms into its time and spatial pieces. -/
theorem section43DerivativeAtom_sum
    (d n : ℕ) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) (g : Fin n × Fin d → M) :
    (∑ a : Section43DerivativeAtom d n,
      match a with
      | Section43DerivativeAtom.time k => f k
      | Section43DerivativeAtom.spatial i => g i) =
    (∑ k : Fin n, f k) + ∑ i : Fin n × Fin d, g i := by
  classical
  let e := section43DerivativeAtomEquivSum d n
  calc
    (∑ a : Section43DerivativeAtom d n,
      match a with
      | Section43DerivativeAtom.time k => f k
      | Section43DerivativeAtom.spatial i => g i) =
        ∑ s : (Fin n) ⊕ (Fin n × Fin d),
          match s with
          | Sum.inl k => f k
          | Sum.inr i => g i := by
          refine Fintype.sum_equiv e _ _ ?_
          intro a
          cases a <;> rfl
    _ = (∑ k : Fin n, f k) + ∑ i : Fin n × Fin d, g i := by
          rw [Fintype.sum_sum_type]

/-- Prepend one derivative atom to a word. -/
def section43DerivativeWordCons
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    Section43DerivativeWord d n (r + 1) :=
  Fin.cons head tail

@[simp] theorem section43DerivativeWordCons_zero
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCons d n r head tail 0 = head := by
  rfl

@[simp] theorem section43DerivativeWordCons_succ
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r)
    (j : Fin r) :
    section43DerivativeWordCons d n r head tail j.succ = tail j := by
  rfl

/-- A nonempty derivative word is equivalently its newest atom together with
the remaining tail word. -/
def section43DerivativeWordEquivCons (d n r : ℕ) :
    Section43DerivativeWord d n (r + 1) ≃
      Section43DerivativeAtom d n × Section43DerivativeWord d n r where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := section43DerivativeWordCons d n r p.1 p.2
  left_inv := by
    intro a
    funext j
    refine Fin.cases ?zero ?succ j
    · rfl
    · intro i
      rfl
  right_inv := by
    intro p
    cases p with
    | mk head tail =>
        rfl

/-- Reindex a finite sum over nonempty derivative words by newest atom and
tail word. -/
theorem section43DerivativeWord_sum_cons
    (d n r : ℕ) {M : Type*} [AddCommMonoid M]
    (f : Section43DerivativeWord d n (r + 1) → M) :
    (∑ a : Section43DerivativeWord d n (r + 1), f a) =
      ∑ head : Section43DerivativeAtom d n,
        ∑ tail : Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r head tail) := by
  classical
  let e := section43DerivativeWordEquivCons d n r
  calc
    (∑ a : Section43DerivativeWord d n (r + 1), f a) =
        ∑ p : Section43DerivativeAtom d n × Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r p.1 p.2) := by
          refine Fintype.sum_equiv e _ _ ?_
          intro a
          exact congrArg f (e.left_inv a).symm
    _ = ∑ head : Section43DerivativeAtom d n,
        ∑ tail : Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r head tail) := by
          rw [Fintype.sum_prod_type]

/-- Drop the newest derivative slot from a nonempty derivative word. -/
def section43DerivativeWordTail
    (d n r : ℕ)
    (a : Section43DerivativeWord d n (r + 1)) :
    Section43DerivativeWord d n r :=
  fun j => a j.succ

@[simp] theorem section43DerivativeWordTail_cons
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTail d n r
      (section43DerivativeWordCons d n r head tail) = tail := by
  rfl

/-- Drop the newest direction from a nonempty direction tuple. -/
def section43DirectionTail
    (d n r : ℕ) [NeZero d]
    (m : Fin (r + 1) → NPointDomain d n) :
    Fin r → NPointDomain d n :=
  fun j => m j.succ

@[simp] theorem section43DirectionTail_cons
    (d n r : ℕ) [NeZero d]
    (head : NPointDomain d n)
    (tail : Fin r → NPointDomain d n) :
    section43DirectionTail d n r (Fin.cons head tail) = tail := by
  rfl

/-- Number of time atoms in a derivative word.  This is the exponent of the
time-moment weight `‖τ‖ ^ K` consumed by the partial-Fourier rapid theorem. -/
def section43DerivativeWordTimeCount
    (d n : ℕ) : (r : ℕ) → Section43DerivativeWord d n r → ℕ
  | 0, _ => 0
  | r + 1, a =>
      let old := section43DerivativeWordTimeCount d n r
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time _ => old + 1
      | Section43DerivativeAtom.spatial _ => old

@[simp] theorem section43DerivativeWordTimeCount_cons_time
    (d n r : ℕ) (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTimeCount d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43DerivativeWordTimeCount d n r tail + 1 := by
  rfl

@[simp] theorem section43DerivativeWordTimeCount_cons_spatial
    (d n r : ℕ) (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTimeCount d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43DerivativeWordTimeCount d n r tail := by
  rfl

/-- The transported Schwartz input attached to a derivative word.  Spatial atoms
apply the already compiled coordinate multiplier transport; time atoms leave the
input unchanged. -/
noncomputable def section43DerivativeWordInput
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → SchwartzNPoint d n → Section43DerivativeWord d n r → SchwartzNPoint d n
  | 0, F, _ => F
  | r + 1, F, a =>
      let old := section43DerivativeWordInput d n r F
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time _ => old
      | Section43DerivativeAtom.spatial i =>
          section43SpatialMultiplierTransport d n old i

@[simp] theorem section43DerivativeWordInput_cons_time
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n) (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordInput d n (r + 1) F
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43DerivativeWordInput d n r F tail := by
  rfl

@[simp] theorem section43DerivativeWordInput_cons_spatial
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n) (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordInput d n (r + 1) F
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43SpatialMultiplierTransport d n
        (section43DerivativeWordInput d n r F tail) i := by
  rfl

/-- Nonnegative scalar coefficient controlling the coordinate factors in a
derivative word. -/
noncomputable def section43DerivativeWordCoeff
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → Section43DerivativeWord d n r → ℝ
  | 0, _ => 1
  | r + 1, a =>
      let old := section43DerivativeWordCoeff d n r
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time k =>
          section43QTimeCoordOpNorm d n k * old
      | Section43DerivativeAtom.spatial i =>
          section43QSpatialCoordOpNorm d n i * old

@[simp] theorem section43DerivativeWordCoeff_cons_time
    (d n r : ℕ) [NeZero d] (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCoeff d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43QTimeCoordOpNorm d n k *
        section43DerivativeWordCoeff d n r tail := by
  rfl

@[simp] theorem section43DerivativeWordCoeff_cons_spatial
    (d n r : ℕ) [NeZero d] (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCoeff d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43QSpatialCoordOpNorm d n i *
        section43DerivativeWordCoeff d n r tail := by
  rfl

/-- Scalar factor carried by a derivative word after evaluating it on the
direction tuple `m`. -/
noncomputable def section43DerivativeWordScalar
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → Section43DerivativeWord d n r →
      (Fin n → ℝ) → (Fin r → NPointDomain d n) → ℂ
  | 0, _a, _τ, _m => 1
  | r + 1, a, τ, m =>
      let old := section43DerivativeWordScalar d n r
        (section43DerivativeWordTail d n r a) τ
        (section43DirectionTail d n r m)
      match a 0 with
      | Section43DerivativeAtom.time k =>
          (-((τ k : ℂ) *
            (section43QTime (d := d) (n := n) (m 0) k : ℂ))) * old
      | Section43DerivativeAtom.spatial i =>
          ((section43QSpatial (d := d) (n := n) (m 0) i : ℝ) : ℂ) * old

@[simp] theorem section43DerivativeWordScalar_cons_time
    (d n r : ℕ) [NeZero d]
    (k : Fin n) (tail : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (head : NPointDomain d n)
    (directions : Fin r → NPointDomain d n) :
    section43DerivativeWordScalar d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail)
      τ (Fin.cons head directions) =
      (-((τ k : ℂ) *
        (section43QTime (d := d) (n := n) head k : ℂ))) *
        section43DerivativeWordScalar d n r tail τ directions := by
  rfl

@[simp] theorem section43DerivativeWordScalar_cons_spatial
    (d n r : ℕ) [NeZero d]
    (i : Fin n × Fin d) (tail : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (head : NPointDomain d n)
    (directions : Fin r → NPointDomain d n) :
    section43DerivativeWordScalar d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail)
      τ (Fin.cons head directions) =
      ((section43QSpatial (d := d) (n := n) head i : ℝ) : ℂ) *
        section43DerivativeWordScalar d n r tail τ directions := by
  rfl

theorem section43DerivativeWordCoeff_nonneg
    (d n r : ℕ) [NeZero d]
    (a : Section43DerivativeWord d n r) :
    0 ≤ section43DerivativeWordCoeff d n r a := by
  induction r with
  | zero =>
      simp [section43DerivativeWordCoeff]
  | succ r ih =>
      cases h : a 0 with
      | time k =>
          have hold :
              0 ≤ section43DerivativeWordCoeff d n r
                (section43DerivativeWordTail d n r a) :=
            ih (section43DerivativeWordTail d n r a)
          simp [section43DerivativeWordCoeff, h,
            section43QTimeCoordOpNorm,
            mul_nonneg (norm_nonneg _) hold]
      | spatial i =>
          have hold :
              0 ≤ section43DerivativeWordCoeff d n r
                (section43DerivativeWordTail d n r a) :=
            ih (section43DerivativeWordTail d n r a)
          simp [section43DerivativeWordCoeff, h,
            section43QSpatialCoordOpNorm,
            mul_nonneg (norm_nonneg _) hold]

/-- Norm bound for the scalar carried by a derivative word.  Time atoms
contribute one power of `‖τ‖`; every atom contributes the corresponding
coordinate-projection operator norm and one direction norm. -/
theorem section43DerivativeWordScalar_norm_le
    (d n r : ℕ) [NeZero d]
    (a : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (m : Fin r → NPointDomain d n) :
    ‖section43DerivativeWordScalar d n r a τ m‖ ≤
      section43DerivativeWordCoeff d n r a *
        ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
          ∏ j : Fin r, ‖m j‖ := by
  induction r with
  | zero =>
      simp [section43DerivativeWordScalar, section43DerivativeWordCoeff,
        section43DerivativeWordTimeCount]
  | succ r ih =>
      cases h : a 0 with
      | time k =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          let head : ℂ :=
            -((τ k : ℂ) *
              (section43QTime (d := d) (n := n) (m 0) k : ℂ))
          let oldScalar : ℂ :=
            section43DerivativeWordScalar d n r oldWord τ oldDirections
          have hhead :
              ‖head‖ ≤ section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
            have hm := abs_section43QTime_coord_le_opNorm d n (m 0) k
            have hτk : |τ k| ≤ ‖τ‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm τ k
            calc
              ‖head‖ =
                  |τ k| * |section43QTime (d := d) (n := n) (m 0) k| := by
                    simp [head, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ ‖τ‖ *
                    (section43QTimeCoordOpNorm d n k * ‖m 0‖) := by
                    exact mul_le_mul hτk hm (abs_nonneg _)
                      (norm_nonneg _)
              _ = section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
                    ring
          have hold :
              ‖oldScalar‖ ≤
                section43DerivativeWordCoeff d n r oldWord *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                    ∏ j : Fin r, ‖oldDirections j‖ := by
            simpa [oldScalar, oldWord, oldDirections] using
              ih oldWord oldDirections
          have hhead_nonneg :
              0 ≤ section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
            exact mul_nonneg
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_nonneg _)
          have hmul :
              ‖head‖ * ‖oldScalar‖ ≤
                (section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := by
            exact mul_le_mul hhead hold (norm_nonneg _) hhead_nonneg
          calc
            ‖section43DerivativeWordScalar d n (r + 1) a τ m‖ =
                ‖head‖ * ‖oldScalar‖ := by
                  simp [section43DerivativeWordScalar, h, head, oldScalar,
                    oldWord, oldDirections]
            _ ≤
                (section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := hmul
            _ =
                section43DerivativeWordCoeff d n (r + 1) a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
                    ∏ j : Fin (r + 1), ‖m j‖ := by
                  simp [section43DerivativeWordCoeff,
                    section43DerivativeWordTimeCount, h, oldWord,
                    oldDirections, section43DirectionTail,
                    Fin.prod_univ_succ, pow_succ]
                  ring
      | spatial i =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          let head : ℂ :=
            ((section43QSpatial (d := d) (n := n) (m 0) i : ℝ) : ℂ)
          let oldScalar : ℂ :=
            section43DerivativeWordScalar d n r oldWord τ oldDirections
          have hhead :
              ‖head‖ ≤ section43QSpatialCoordOpNorm d n i * ‖m 0‖ := by
            have hm := abs_section43QSpatial_coord_le_opNorm d n (m 0) i
            simpa [head, Complex.norm_real, Real.norm_eq_abs] using hm
          have hold :
              ‖oldScalar‖ ≤
                section43DerivativeWordCoeff d n r oldWord *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                    ∏ j : Fin r, ‖oldDirections j‖ := by
            simpa [oldScalar, oldWord, oldDirections] using
              ih oldWord oldDirections
          have hhead_nonneg :
              0 ≤ section43QSpatialCoordOpNorm d n i * ‖m 0‖ := by
            exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          have hmul :
              ‖head‖ * ‖oldScalar‖ ≤
                (section43QSpatialCoordOpNorm d n i * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := by
            exact mul_le_mul hhead hold (norm_nonneg _) hhead_nonneg
          calc
            ‖section43DerivativeWordScalar d n (r + 1) a τ m‖ =
                ‖head‖ * ‖oldScalar‖ := by
                  simp [section43DerivativeWordScalar, h, head, oldScalar,
                    oldWord, oldDirections]
            _ ≤
                (section43QSpatialCoordOpNorm d n i * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := hmul
            _ =
                section43DerivativeWordCoeff d n (r + 1) a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
                    ∏ j : Fin (r + 1), ‖m j‖ := by
                  simp [section43DerivativeWordCoeff,
                    section43DerivativeWordTimeCount, h, oldWord,
                    oldDirections, section43DirectionTail,
                    Fin.prod_univ_succ]
                  ring

/-- The first derivative is the one-letter instance of the finite word
expansion: time atoms come from differentiating the exponential, and spatial
atoms come from differentiating the spatial Fourier argument. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_apply_eq_sum_atoms
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q m : NPointDomain d n)
    (τ : Fin n → ℝ) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
      ∑ a : Section43DerivativeAtom d n,
        match a with
        | Section43DerivativeAtom.time k =>
            (-((τ k : ℂ) *
              (section43QTime (d := d) (n := n) m k : ℂ))) *
              Complex.exp
                (-(∑ j : Fin n,
                  (τ j : ℂ) *
                    (section43QTime (d := d) (n := n) q j : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n) F
                  (τ, section43QSpatial (d := d) (n := n) q)
        | Section43DerivativeAtom.spatial i =>
            ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
              Complex.exp
                (-(∑ j : Fin n,
                  (τ j : ℂ) *
                    (section43QTime (d := d) (n := n) q j : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43SpatialMultiplierTransport d n F i)
                  (τ, section43QSpatial (d := d) (n := n) q) := by
  classical
  let E : ℂ :=
    Complex.exp
      (-(∑ j : Fin n,
        (τ j : ℂ) * (section43QTime (d := d) (n := n) q j : ℂ)))
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let P : ℂ :=
    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)
  let timeTerm : Fin n → ℂ := fun k =>
    (-((τ k : ℂ) *
      (section43QTime (d := d) (n := n) m k : ℂ))) * E * P
  let spatialTerm : Fin n × Fin d → ℂ := fun i =>
    ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) * E *
      partialFourierSpatial_fun (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) (τ, ξ)
  have hspatial :
      (fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ)
        (section43QSpatial (d := d) (n := n) m) =
        ∑ i : Fin n × Fin d,
          ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ) := by
    simpa [ξ] using
      fderiv_partialFourierSpatial_fun_spatial_apply_eq_sum_multiplierTransport
        d n F τ ξ (section43QSpatial (d := d) (n := n) m)
  have hsplit :
      (∑ a : Section43DerivativeAtom d n,
        match a with
        | Section43DerivativeAtom.time k => timeTerm k
        | Section43DerivativeAtom.spatial i => spatialTerm i) =
      (∑ k : Fin n, timeTerm k) + ∑ i : Fin n × Fin d, spatialTerm i := by
    exact section43DerivativeAtom_sum d n timeTerm spatialTerm
  calc
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
        (∑ k : Fin n,
          (section43QTime (d := d) (n := n) m k : ℝ) •
            (-(τ k : ℂ) * E * P)) +
          E •
            (fderiv ℝ
              (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
                partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
              ξ)
              (section43QSpatial (d := d) (n := n) m) := by
          simp [section43FourierLaplace_timeIntegrandFDerivCLM_apply, E, P, ξ]
    _ = (∑ k : Fin n, timeTerm k) + ∑ i : Fin n × Fin d, spatialTerm i := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro k _hk
            simp [timeTerm, Complex.real_smul, mul_assoc, mul_left_comm]
          · rw [hspatial]
            simp [spatialTerm, smul_eq_mul, Finset.mul_sum,
              mul_assoc, mul_left_comm]
    _ =
        ∑ a : Section43DerivativeAtom d n,
          match a with
          | Section43DerivativeAtom.time k =>
              (-((τ k : ℂ) *
                (section43QTime (d := d) (n := n) m k : ℂ))) *
                Complex.exp
                  (-(∑ j : Fin n,
                    (τ j : ℂ) *
                      (section43QTime (d := d) (n := n) q j : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n) F
                    (τ, section43QSpatial (d := d) (n := n) q)
          | Section43DerivativeAtom.spatial i =>
              ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
                Complex.exp
                  (-(∑ j : Fin n,
                    (τ j : ℂ) *
                      (section43QTime (d := d) (n := n) q j : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n F i)
                    (τ, section43QSpatial (d := d) (n := n) q) := by
          rw [← hsplit]

end OSReconstruction
