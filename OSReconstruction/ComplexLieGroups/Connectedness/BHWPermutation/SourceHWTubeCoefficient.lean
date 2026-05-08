import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWSelectedProjection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtendedTubeRank

/-!
# Hall-Wightman tube coefficient support

This file starts the rank-deficient tube-stability layer used by the
Hall-Wightman Lemma-3 route.  The first theorems are deliberately only API
bridges: they expose additivity, scalar coefficients, cancellation, Lorentz
invariance of the complex bilinear form, and the elementary exponential limit
in the shapes needed by the coefficient-freedom proof.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Normal form used in Hall-Wightman's second and third remarks after
Lemma 2.  Either `q = 0`, or `q = α (u + i v)` with real spacelike
orthonormal `u,v`, and every source vector `η i` is orthogonal to both
real directions. -/
def HWNullResidualNormalForm
    (d n : ℕ) [NeZero d]
    (q : Fin (d + 1) → ℂ)
    (η : Fin n → Fin (d + 1) → ℂ) : Prop :=
  q = 0 ∨
    ∃ (α : ℂ) (u v : Fin (d + 1) → ℝ),
      α ≠ 0 ∧
      q = (fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ))) ∧
      MinkowskiSpace.minkowskiInner d u u = 1 ∧
      MinkowskiSpace.minkowskiInner d v v = 1 ∧
      MinkowskiSpace.minkowskiInner d u v = 0 ∧
      (∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (u μ : ℂ)) (η i) = 0) ∧
      (∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (v μ : ℂ)) (η i) = 0)

/-- The real and imaginary parts of a complex null vector are collinear along
a common real null direction. -/
def realNullCollinear
    (d : ℕ) [NeZero d]
    (x y : Fin (d + 1) → ℝ) : Prop :=
  ∃ (ℓ : Fin (d + 1) → ℝ) (a b : ℝ),
    ℓ ≠ 0 ∧
    MinkowskiSpace.minkowskiInner d ℓ ℓ = 0 ∧
    x = (fun μ => a * ℓ μ) ∧
    y = (fun μ => b * ℓ μ)

/-- The configuration Lorentz action distributes over pointwise addition. -/
theorem complexLorentzAction_add
    (Λ : ComplexLorentzGroup d)
    (z w : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ (fun i μ => z i μ + w i μ) =
      fun i μ => complexLorentzAction Λ z i μ +
        complexLorentzAction Λ w i μ := by
  ext i μ
  exact congrFun (complexLorentzVectorAction_add Λ (z i) (w i)) μ

/-- The configuration Lorentz action pulls scalar source coefficients through
the vector action. -/
theorem complexLorentzAction_smul_vector
    (Λ : ComplexLorentzGroup d)
    (c : Fin n → ℂ)
    (v : Fin (d + 1) → ℂ) :
    complexLorentzAction Λ (fun i μ => c i * v μ) =
      fun i μ => c i * complexLorentzVectorAction Λ v μ := by
  ext i μ
  exact congrFun (complexLorentzVectorAction_smul Λ (c i) v) μ

/-- Cancel a common left Lorentz action from configurations. -/
theorem complexLorentzAction_cancel_left
    (Λ : ComplexLorentzGroup d)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (h : complexLorentzAction Λ z = complexLorentzAction Λ w) :
    z = w := by
  have h' := congrArg (complexLorentzAction Λ⁻¹) h
  simpa [complexLorentzAction_inv] using h'

/-- Acting by `Λ⁻¹` and then by `Λ` cancels on configurations. -/
theorem complexLorentzAction_inv_left
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ (complexLorentzAction Λ⁻¹ z) = z := by
  simpa using (complexLorentzAction_inv (Λ := Λ⁻¹) (z := z))

/-- Acting by `Λ⁻¹` and then by `Λ` cancels on a single spacetime vector. -/
theorem complexLorentzVectorAction_inv_left
    (Λ : ComplexLorentzGroup d)
    (v : Fin (d + 1) → ℂ) :
    complexLorentzVectorAction Λ (complexLorentzVectorAction Λ⁻¹ v) = v := by
  let z : Fin 1 → Fin (d + 1) → ℂ := fun _ => v
  have h :=
    congrFun (complexLorentzAction_inv_left (d := d) (n := 1) Λ z)
      (0 : Fin 1)
  simpa [z, complexLorentzAction] using h

/-- Complex Lorentz transformations preserve the complex bilinear Minkowski
pairing on individual source vectors. -/
theorem sourceComplexMinkowskiInner_complexLorentzVectorAction
    (Λ : ComplexLorentzGroup d)
    (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d
        (complexLorentzVectorAction Λ u)
        (complexLorentzVectorAction Λ v) =
      sourceComplexMinkowskiInner d u v := by
  let z : Fin 2 → Fin (d + 1) → ℂ :=
    fun i => if i = (0 : Fin 2) then u else v
  have h :=
    congrFun
      (congrFun
        (sourceMinkowskiGram_complexLorentzAction
          (d := d) (n := 2) Λ z) (0 : Fin 2))
      (1 : Fin 2)
  simpa [sourceMinkowskiGram_apply_eq_complexInner, z,
    complexLorentzAction] using h

/-- Right linearity of the complex source Minkowski pairing over an arbitrary
finite sum. -/
theorem sourceComplexMinkowskiInner_finset_sum_smul_right
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι)
    (u : Fin (d + 1) → ℂ)
    (coeff : ι → ℂ)
    (v : ι → Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u
      (∑ a ∈ S, coeff a • v a) =
      ∑ a ∈ S, coeff a *
        sourceComplexMinkowskiInner d u (v a) := by
  let L : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun w => sourceComplexMinkowskiInner d u w
    map_add' := by
      intro p q
      exact sourceComplexMinkowskiInner_add_right d u p q
    map_smul' := by
      intro c p
      exact sourceComplexMinkowskiInner_smul_right d c u p }
  change L (∑ a ∈ S, coeff a • v a) =
    ∑ a ∈ S, coeff a * L (v a)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [L.map_smul]
  simp [smul_eq_mul]

/-- The scalar `exp(-t)` tends to zero as `t → +∞`, in complex form. -/
theorem tendsto_complex_exp_neg_atTop_nhds_zero :
    Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ))
      atTop (nhds (0 : ℂ)) := by
  have hreal : Tendsto (fun t : ℝ => Real.exp (-t))
      atTop (nhds (0 : ℝ)) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot : Tendsto (fun t : ℝ => -t) atTop atBot)
  convert (Complex.continuous_ofReal.tendsto 0).comp hreal using 1

/-- A single residual with coefficient `exp(-t)` tends to zero in the finite
configuration space. -/
theorem tendsto_singleResidual_exp_neg_zero
    (b : Fin n → ℂ)
    (q : Fin (d + 1) → ℂ) :
    Tendsto
      (fun t : ℝ =>
        fun i μ => (Real.exp (-t) : ℂ) * b i * q μ)
      atTop
      (nhds (0 : Fin n → Fin (d + 1) → ℂ)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro μ
  have h :=
    (tendsto_complex_exp_neg_atTop_nhds_zero.mul
      (tendsto_const_nhds (x := b i))).mul
      (tendsto_const_nhds (x := q μ))
  simpa [Pi.zero_apply, mul_assoc] using h

/-- Real and imaginary parts of a complex null vector have equal real
Minkowski square and are mutually orthogonal. -/
theorem complexNull_iff_real_imag_equal_orthogonal
    [NeZero d]
    (q : Fin (d + 1) → ℂ)
    (hq : sourceComplexMinkowskiInner d q q = 0) :
    MinkowskiSpace.minkowskiInner d
        (fun μ => (q μ).re) (fun μ => (q μ).re) =
      MinkowskiSpace.minkowskiInner d
        (fun μ => (q μ).im) (fun μ => (q μ).im) ∧
    MinkowskiSpace.minkowskiInner d
        (fun μ => (q μ).re) (fun μ => (q μ).im) = 0 := by
  have hparts := sourceComplexMinkowskiInner_self_re_im d q
  have hre0 : (sourceComplexMinkowskiInner d q q).re = 0 := by
    simp [hq]
  have him0 : (sourceComplexMinkowskiInner d q q).im = 0 := by
    simp [hq]
  constructor
  · linarith [hparts.1]
  · have htwice :
        2 * MinkowskiSpace.minkowskiInner d
          (fun μ => (q μ).re) (fun μ => (q μ).im) = 0 := by
      rw [← hparts.2]
      exact him0
    nlinarith

/-- If a complex vector is nonzero, at least one of its real and imaginary
parts is nonzero. -/
theorem real_imag_nonzero_of_complex_ne_zero
    {q : Fin (d + 1) → ℂ}
    (hq : q ≠ 0) :
    (fun μ => (q μ).re) ≠ 0 ∨ (fun μ => (q μ).im) ≠ 0 := by
  by_contra h
  have hre_zero : (fun μ => (q μ).re) = 0 := by
    by_contra hne
    exact h (Or.inl hne)
  have him_zero : (fun μ => (q μ).im) = 0 := by
    by_contra hne
    exact h (Or.inr hne)
  apply hq
  ext μ
  apply Complex.ext
  · simpa using congrFun hre_zero μ
  · simpa using congrFun him_zero μ

/-- Unpack a collinear real-null pair to a common null vector. -/
theorem realNullCollinear_commonVector
    [NeZero d]
    {x y : Fin (d + 1) → ℝ}
    (hcoll : realNullCollinear d x y)
    (_hxy_ne : x ≠ 0 ∨ y ≠ 0) :
    ∃ ℓ : Fin (d + 1) → ℝ,
      ℓ ≠ 0 ∧
      MinkowskiSpace.minkowskiInner d ℓ ℓ = 0 ∧
      (∃ a : ℝ, x = fun μ => a * ℓ μ) ∧
      (∃ b : ℝ, y = fun μ => b * ℓ μ) := by
  rcases hcoll with ⟨ℓ, a, b, hℓ_ne, hℓ_null, hx, hy⟩
  exact ⟨ℓ, hℓ_ne, hℓ_null, ⟨a, hx⟩, ⟨b, hy⟩⟩

/-- If the real and imaginary parts use a nonzero common direction, the
corresponding complex scalar is nonzero. -/
theorem realNullCollinear_scalar_ne_zero_of_nonzero_direction
    {qre qim ℓ : Fin (d + 1) → ℝ}
    {a b : ℝ}
    (hqre : qre = fun μ => a * ℓ μ)
    (hqim : qim = fun μ => b * ℓ μ)
    (hq_ne : qre ≠ 0 ∨ qim ≠ 0) :
    (a : ℂ) + Complex.I * (b : ℂ) ≠ 0 := by
  intro h
  have ha : a = 0 := by
    simpa using congrArg Complex.re h
  have hb : b = 0 := by
    have := congrArg Complex.im h
    simpa [ha] using this
  rcases hq_ne with hqre_ne | hqim_ne
  · exact hqre_ne (by ext μ; simp [hqre, ha])
  · exact hqim_ne (by ext μ; simp [hqim, hb])

/-- If real and imaginary parts are collinear along `ℓ`, orthogonality of the
corresponding complex vector to every source vector gives orthogonality of
`ℓ` to every forward-tube successive imaginary difference. -/
theorem realNullCollinear_orthogonal_forwardTube_differences
    [NeZero d]
    {ζ : Fin n → Fin (d + 1) → ℂ}
    {qre qim ℓ : Fin (d + 1) → ℝ}
    (hq_orth :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (qre μ : ℂ) + Complex.I * (qim μ : ℂ))
          (ζ i) = 0)
    (hq_ne : qre ≠ 0 ∨ qim ≠ 0)
    (hqre : ∃ a : ℝ, qre = fun μ => a * ℓ μ)
    (hqim : ∃ b : ℝ, qim = fun μ => b * ℓ μ) :
    ∀ k : Fin n,
      MinkowskiSpace.minkowskiInner d ℓ
        (fun μ =>
          ((ζ k μ) -
            (if h : k.val = 0 then 0
             else ζ ⟨k.val - 1, by omega⟩ μ)).im) = 0 := by
  rcases hqre with ⟨a, hqre⟩
  rcases hqim with ⟨b, hqim⟩
  have hscalar_ne : (a : ℂ) + Complex.I * (b : ℂ) ≠ 0 :=
    realNullCollinear_scalar_ne_zero_of_nonzero_direction
      (qre := qre) (qim := qim) (ℓ := ℓ) hqre hqim hq_ne
  have hℓ_orth_point :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (ℓ μ : ℂ)) (ζ i) = 0 := by
    intro i
    have hqi := hq_orth i
    have hfactor :
        (fun μ => (qre μ : ℂ) + Complex.I * (qim μ : ℂ)) =
        fun μ => ((a : ℂ) + Complex.I * (b : ℂ)) * (ℓ μ : ℂ) := by
      ext μ
      simp [hqre, hqim, mul_add, mul_comm, mul_left_comm]
    rw [hfactor] at hqi
    have hqi' :
        ((a : ℂ) + Complex.I * (b : ℂ)) *
          sourceComplexMinkowskiInner d
            (fun μ => (ℓ μ : ℂ)) (ζ i) = 0 := by
      simpa [Pi.smul_apply] using
        (sourceComplexMinkowskiInner_smul_left
          d ((a : ℂ) + Complex.I * (b : ℂ))
          (fun μ => (ℓ μ : ℂ)) (ζ i)).symm.trans hqi
    exact (mul_eq_zero.mp hqi').resolve_left hscalar_ne
  intro k
  by_cases hk : k.val = 0
  · simpa [sourceComplexMinkowskiInner,
      MinkowskiSpace.minkowskiInner, hk] using
      congrArg Complex.im (hℓ_orth_point k)
  · have hprev :=
      hℓ_orth_point ⟨k.val - 1, by omega⟩
    have hcurr := hℓ_orth_point k
    have hdiff :
        sourceComplexMinkowskiInner d
          (fun μ => (ℓ μ : ℂ))
          (fun μ => ζ k μ - ζ ⟨k.val - 1, by omega⟩ μ) = 0 := by
      change sourceComplexMinkowskiInner d
          (fun μ => (ℓ μ : ℂ))
          (ζ k - ζ ⟨k.val - 1, by omega⟩) = 0
      rw [sourceComplexMinkowskiInner_sub_right, hcurr, hprev]
      simp
    simpa [sourceComplexMinkowskiInner,
      MinkowskiSpace.minkowskiInner, hk] using
      congrArg Complex.im hdiff

/-- A finite sum of squares vanishes only if every square vanishes. -/
theorem sum_sq_eq_zero
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ)
    (h : ∑ i, f i ^ 2 = 0) :
    ∀ i, f i = 0 := by
  have hall :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (f j))).mp h
  intro i
  exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))

/-- Absolute Cauchy-Schwarz for finite real coordinate sums. -/
theorem abs_sum_mul_le_sqrt_mul_sqrt
    {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) :
    |∑ i, f i * g i| ≤
      Real.sqrt (∑ i, f i ^ 2) *
        Real.sqrt (∑ i, g i ^ 2) := by
  have hpos :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  have hneg :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => -f i) g
  have hneg' :
      -(∑ i, f i * g i) ≤
        Real.sqrt (∑ i, f i ^ 2) *
          Real.sqrt (∑ i, g i ^ 2) := by
    simpa [Finset.sum_neg_distrib, neg_mul, neg_sq] using hneg
  have hleft :
      -(Real.sqrt (∑ i, f i ^ 2) *
          Real.sqrt (∑ i, g i ^ 2)) ≤
        ∑ i, f i * g i := by
    linarith
  exact abs_le.mpr ⟨hleft, hpos⟩

/-- Expand the finite Euclidean square of a real linear combination. -/
theorem sum_sq_linear_combination_expand
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (A B : ℝ) :
    ∑ i, (A * x i - B * y i) ^ 2 =
      A ^ 2 * (∑ i, x i ^ 2) -
        2 * A * B * (∑ i, x i * y i) +
        B ^ 2 * (∑ i, y i ^ 2) := by
  calc
    ∑ i, (A * x i - B * y i) ^ 2
        = ∑ i,
            (A ^ 2 * x i ^ 2 + (-(2 * A * B * (x i * y i))) +
              B ^ 2 * y i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = A ^ 2 * (∑ i, x i ^ 2) -
        2 * A * B * (∑ i, x i * y i) +
        B ^ 2 * (∑ i, y i ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
          ring

/-- Equality in the finite real Cauchy-Schwarz inequality forces the two
coordinate families to be collinear in homogeneous coordinates. -/
theorem real_cauchy_eq_collinear_of_abs_dot_eq_norms
    {ι : Type*} [Fintype ι]
    {x y : ι → ℝ}
    (heq :
      |∑ i, x i * y i| =
        Real.sqrt (∑ i, x i ^ 2) *
          Real.sqrt (∑ i, y i ^ 2)) :
    ∃ a b : ℝ,
      (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ i, b * x i = a * y i := by
  let xy : ℝ := ∑ i, x i * y i
  let xx : ℝ := ∑ i, x i ^ 2
  let yy : ℝ := ∑ i, y i ^ 2
  have hxx_nonneg : 0 ≤ xx :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hyy_nonneg : 0 ≤ yy :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have hsq : xy ^ 2 = xx * yy := by
    have h := congrArg (fun r : ℝ => r ^ 2) heq
    simpa [xy, xx, yy, sq_abs, mul_pow, Real.sq_sqrt hxx_nonneg,
      Real.sq_sqrt hyy_nonneg] using h
  by_cases hxx_zero : xx = 0
  · have hx_each : ∀ i, x i = 0 := by
      apply sum_sq_eq_zero x
      simpa [xx] using hxx_zero
    refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
    intro i
    simp [hx_each i]
  · refine ⟨xx, xy, Or.inl hxx_zero, ?_⟩
    have hsum0 : ∑ i, (xy * x i - xx * y i) ^ 2 = 0 := by
      have hexpand := sum_sq_linear_combination_expand x y xy xx
      rw [hexpand]
      simp [xy, xx, yy] at hsq ⊢
      ring_nf
      rw [hsq]
      ring
    have h_each : ∀ i, xy * x i - xx * y i = 0 :=
      sum_sq_eq_zero (fun i => xy * x i - xx * y i) hsum0
    intro i
    exact sub_eq_zero.mp (h_each i)

/-- A real null vector has time component whose absolute value is the Euclidean
length of its spatial part. -/
theorem realNull_abs_time_eq_spatial_norm
    [NeZero d]
    {ℓ : Fin (d + 1) → ℝ}
    (hℓ_null : MinkowskiSpace.minkowskiInner d ℓ ℓ = 0) :
    |ℓ 0| = Real.sqrt (∑ i : Fin d, ℓ i.succ ^ 2) := by
  have hsq :
      ℓ 0 ^ 2 = ∑ i : Fin d, ℓ i.succ ^ 2 := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d ℓ ℓ
    rw [hℓ_null] at hdecomp
    have hsum :
        (∑ i : Fin d, ℓ i.succ * ℓ i.succ) = ℓ 0 * ℓ 0 := by
      linarith
    simpa [pow_two] using hsum.symm
  rw [← Real.sqrt_sq_eq_abs, hsq]

/-- Two nonzero real null vectors which are Minkowski-orthogonal are
collinear along a common real null direction. -/
theorem realNull_orthogonal_collinear
    [NeZero d]
    {x y : Fin (d + 1) → ℝ}
    (hx_null : MinkowskiSpace.minkowskiInner d x x = 0)
    (hy_null : MinkowskiSpace.minkowskiInner d y y = 0)
    (hxy : MinkowskiSpace.minkowskiInner d x y = 0)
    (hne : x ≠ 0 ∨ y ≠ 0) :
    realNullCollinear d x y := by
  have hx_sp : (∑ i : Fin d, x i.succ ^ 2) = x 0 ^ 2 := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d x x
    rw [hx_null] at hdecomp
    have hsum :
        (∑ i : Fin d, x i.succ * x i.succ) = x 0 * x 0 := by
      linarith
    simpa [pow_two] using hsum
  have hy_sp : (∑ i : Fin d, y i.succ ^ 2) = y 0 ^ 2 := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d y y
    rw [hy_null] at hdecomp
    have hsum :
        (∑ i : Fin d, y i.succ * y i.succ) = y 0 * y 0 := by
      linarith
    simpa [pow_two] using hsum
  have hxy_sp :
      (∑ i : Fin d, x i.succ * y i.succ) = x 0 * y 0 := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d x y
    rw [hxy] at hdecomp
    nlinarith
  have hx_abs :
      |x 0| = Real.sqrt (∑ i : Fin d, x i.succ ^ 2) :=
    realNull_abs_time_eq_spatial_norm (d := d) hx_null
  have hy_abs :
      |y 0| = Real.sqrt (∑ i : Fin d, y i.succ ^ 2) :=
    realNull_abs_time_eq_spatial_norm (d := d) hy_null
  have hcs_eq :
      |∑ i : Fin d, x i.succ * y i.succ| =
        Real.sqrt (∑ i : Fin d, x i.succ ^ 2) *
          Real.sqrt (∑ i : Fin d, y i.succ ^ 2) := by
    calc
      |∑ i : Fin d, x i.succ * y i.succ| = |x 0 * y 0| := by
        rw [hxy_sp]
      _ = |x 0| * |y 0| := by
        rw [abs_mul]
      _ = Real.sqrt (∑ i : Fin d, x i.succ ^ 2) *
          Real.sqrt (∑ i : Fin d, y i.succ ^ 2) := by
        rw [hx_abs, hy_abs]
  rcases real_cauchy_eq_collinear_of_abs_dot_eq_norms
      (x := fun i : Fin d => x i.succ)
      (y := fun i : Fin d => y i.succ) hcs_eq with
    ⟨a, b, hab_ne, hsp⟩
  have hxrel_sum :
      b * (∑ i : Fin d, x i.succ ^ 2) =
        a * (∑ i : Fin d, x i.succ * y i.succ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := hsp i
    calc
      b * x i.succ ^ 2 = (b * x i.succ) * x i.succ := by
        ring
      _ = (a * y i.succ) * x i.succ := by
        rw [h]
      _ = a * (x i.succ * y i.succ) := by
        ring
  have hyrel_sum :
      b * (∑ i : Fin d, x i.succ * y i.succ) =
        a * (∑ i : Fin d, y i.succ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := hsp i
    calc
      b * (x i.succ * y i.succ) =
          (b * x i.succ) * y i.succ := by
        ring
      _ = (a * y i.succ) * y i.succ := by
        rw [h]
      _ = a * y i.succ ^ 2 := by
        ring
  have hx_time_eq : b * x 0 ^ 2 = a * (x 0 * y 0) := by
    rw [← hx_sp, ← hxy_sp]
    exact hxrel_sum
  have hy_time_eq : b * (x 0 * y 0) = a * y 0 ^ 2 := by
    rw [← hxy_sp, ← hy_sp]
    exact hyrel_sum
  have hx_time_factor : x 0 * (b * x 0 - a * y 0) = 0 := by
    calc
      x 0 * (b * x 0 - a * y 0) =
          b * x 0 ^ 2 - a * (x 0 * y 0) := by
        ring
      _ = 0 := by
        rw [hx_time_eq]
        ring
  have hy_time_factor : y 0 * (b * x 0 - a * y 0) = 0 := by
    calc
      y 0 * (b * x 0 - a * y 0) =
          b * (x 0 * y 0) - a * y 0 ^ 2 := by
        ring
      _ = 0 := by
        rw [hy_time_eq]
        ring
  have htime : b * x 0 = a * y 0 := by
    by_cases hx0 : x 0 = 0
    · by_cases hy0 : y 0 = 0
      · exfalso
        have hx_sp0 : ∑ i : Fin d, x i.succ ^ 2 = 0 := by
          simpa [hx0] using hx_sp
        have hy_sp0 : ∑ i : Fin d, y i.succ ^ 2 = 0 := by
          simpa [hy0] using hy_sp
        have hx_each : ∀ i : Fin d, x i.succ = 0 :=
          sum_sq_eq_zero (fun i : Fin d => x i.succ) hx_sp0
        have hy_each : ∀ i : Fin d, y i.succ = 0 :=
          sum_sq_eq_zero (fun i : Fin d => y i.succ) hy_sp0
        have hx_zero : x = 0 := by
          ext μ
          cases μ using Fin.cases with
          | zero => exact hx0
          | succ i => exact hx_each i
        have hy_zero : y = 0 := by
          ext μ
          cases μ using Fin.cases with
          | zero => exact hy0
          | succ i => exact hy_each i
        exact
          hne.elim (fun hx_ne => hx_ne hx_zero)
            (fun hy_ne => hy_ne hy_zero)
      · have hzero : b * x 0 - a * y 0 = 0 :=
          (mul_eq_zero.mp hy_time_factor).resolve_left hy0
        exact sub_eq_zero.mp hzero
    · have hzero : b * x 0 - a * y 0 = 0 :=
        (mul_eq_zero.mp hx_time_factor).resolve_left hx0
      exact sub_eq_zero.mp hzero
  by_cases ha : a = 0
  · have hb_ne : b ≠ 0 := by
      rcases hab_ne with ha_ne | hb_ne
      · exact (ha_ne ha).elim
      · exact hb_ne
    have hx_zero : x = 0 := by
      ext μ
      cases μ using Fin.cases with
      | zero =>
          have h : b * x 0 = 0 := by
            simpa [ha] using htime
          exact (mul_eq_zero.mp h).resolve_left hb_ne
      | succ i =>
          have h := hsp i
          have hzero : b * x i.succ = 0 := by
            simpa [ha] using h
          exact (mul_eq_zero.mp hzero).resolve_left hb_ne
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      exact
        hne.elim (fun hx_ne => hx_ne hx_zero)
          (fun hy_ne => hy_ne hy_zero)
    refine ⟨y, 0, 1, hy_ne, hy_null, ?_, ?_⟩
    · ext μ
      simp [hx_zero]
    · ext μ
      simp
  · have hx_ne : x ≠ 0 := by
      intro hx_zero
      have hy_zero : y = 0 := by
        ext μ
        cases μ using Fin.cases with
        | zero =>
            have h : a * y 0 = 0 := by
              simpa [hx_zero] using htime.symm
            exact (mul_eq_zero.mp h).resolve_left ha
        | succ i =>
            have h := hsp i
            have hzero : a * y i.succ = 0 := by
              simpa [hx_zero] using h.symm
            exact (mul_eq_zero.mp hzero).resolve_left ha
      exact
        hne.elim (fun hx_ne => hx_ne hx_zero)
          (fun hy_ne => hy_ne hy_zero)
    refine ⟨x, 1, b / a, hx_ne, hx_null, ?_, ?_⟩
    · ext μ
      simp
    · ext μ
      cases μ using Fin.cases with
      | zero =>
          have h : y 0 = (b / a) * x 0 := by
            field_simp [ha]
            linarith [htime]
          simpa [mul_comm] using h
      | succ i =>
          have hsp_i := hsp i
          have h : y i.succ = (b / a) * x i.succ := by
            field_simp [ha]
            linarith [hsp_i]
          simpa [mul_comm] using h

/-- If two orthogonal real vectors have equal Minkowski square and are not
collinear in the real-null alternative, then that common square is positive. -/
theorem real_orthogonal_equalNorm_not_collinear_positive
    [NeZero d]
    {x y : Fin (d + 1) → ℝ}
    (hne : x ≠ 0 ∨ y ≠ 0)
    (heq :
      MinkowskiSpace.minkowskiInner d x x =
        MinkowskiSpace.minkowskiInner d y y)
    (hxy : MinkowskiSpace.minkowskiInner d x y = 0)
    (hnot : ¬ realNullCollinear d x y) :
    0 < MinkowskiSpace.minkowskiInner d x x := by
  let A : ℝ := MinkowskiSpace.minkowskiInner d x x
  have hAdef : A = MinkowskiSpace.minkowskiInner d x x := rfl
  rcases lt_trichotomy A 0 with hA_neg | hA_zero | hA_pos
  · have hx_time_ne : x 0 ≠ 0 := by
      intro hx0
      have hdecomp := MinkowskiSpace.minkowskiInner_decomp d x x
      have hsum_nonneg : 0 ≤ ∑ i : Fin d, x i.succ * x i.succ :=
        Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i.succ))
      rw [← hAdef] at hdecomp
      rw [hdecomp, hx0] at hA_neg
      linarith
    have htimelike_x : MinkowskiSpace.IsTimelike d x := by
      simpa [MinkowskiSpace.IsTimelike, MinkowskiSpace.minkowskiNormSq, A]
        using hA_neg
    have horth_yx : MinkowskiSpace.minkowskiInner d y x = 0 := by
      simpa [MinkowskiSpace.minkowskiInner_comm] using hxy
    by_cases hx0_pos : 0 < x 0
    · have hnonneg_y : 0 ≤ MinkowskiSpace.minkowskiInner d y y := by
        have h :=
          MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
            (d := d) y x htimelike_x hx0_pos horth_yx
        simpa [MinkowskiSpace.minkowskiNormSq] using h
      have hy_eq_A : MinkowskiSpace.minkowskiInner d y y = A := by
        rw [← heq, ← hAdef]
      linarith
    · have hx0_neg : x 0 < 0 := by
        have hx0_le : x 0 ≤ 0 := le_of_not_gt hx0_pos
        exact lt_of_le_of_ne hx0_le hx_time_ne
      let nx : Fin (d + 1) → ℝ := fun μ => -x μ
      have htimelike_nx : MinkowskiSpace.IsTimelike d nx := by
        have hnorm : MinkowskiSpace.minkowskiNormSq d nx = A := by
          simp [nx, MinkowskiSpace.minkowskiNormSq,
            MinkowskiSpace.minkowskiInner, A]
        rw [MinkowskiSpace.IsTimelike, hnorm]
        exact hA_neg
      have hfuture_nx : MinkowskiSpace.IsFutureDirected d nx := by
        simpa [MinkowskiSpace.IsFutureDirected, MinkowskiSpace.timeComponent,
          nx] using neg_pos.mpr hx0_neg
      have horth_ynx : MinkowskiSpace.minkowskiInner d y nx = 0 := by
        simpa [nx, MinkowskiSpace.minkowskiInner] using
          congrArg Neg.neg horth_yx
      have hnonneg_y : 0 ≤ MinkowskiSpace.minkowskiInner d y y := by
        have h :=
          MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
            (d := d) y nx htimelike_nx hfuture_nx horth_ynx
        simpa [MinkowskiSpace.minkowskiNormSq] using h
      have hy_eq_A : MinkowskiSpace.minkowskiInner d y y = A := by
        rw [← heq, ← hAdef]
      linarith
  · have hx_null : MinkowskiSpace.minkowskiInner d x x = 0 := by
      rw [← hAdef]
      exact hA_zero
    have hy_null : MinkowskiSpace.minkowskiInner d y y = 0 := by
      rw [← heq]
      exact hx_null
    exact
      (hnot
        (realNull_orthogonal_collinear (d := d)
          hx_null hy_null hxy hne)).elim
  · simpa [A] using hA_pos

/-- A non-collinear complex null vector has the Hall-Wightman real spacelike
normal form `α (u + I v)` with `u.u = v.v = 1` and `u.v = 0`. -/
theorem realImag_null_not_collinear_to_spacelike_orthonormal
    [NeZero d]
    (_hd : 2 ≤ d)
    {qre qim : Fin (d + 1) → ℝ}
    (h_ne : qre ≠ 0 ∨ qim ≠ 0)
    (hnull_real :
      MinkowskiSpace.minkowskiInner d qre qre =
        MinkowskiSpace.minkowskiInner d qim qim ∧
      MinkowskiSpace.minkowskiInner d qre qim = 0)
    (hnot_collinear : ¬ realNullCollinear d qre qim) :
    ∃ (α : ℂ) (u v : Fin (d + 1) → ℝ),
      α ≠ 0 ∧
      (fun μ => (qre μ : ℂ) + Complex.I * (qim μ : ℂ)) =
        (fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ))) ∧
      MinkowskiSpace.minkowskiInner d u u = 1 ∧
      MinkowskiSpace.minkowskiInner d v v = 1 ∧
      MinkowskiSpace.minkowskiInner d u v = 0 := by
  let A : ℝ := MinkowskiSpace.minkowskiInner d qre qre
  have hA_pos : 0 < A :=
    real_orthogonal_equalNorm_not_collinear_positive
      (d := d) (x := qre) (y := qim) h_ne
      hnull_real.1 hnull_real.2 hnot_collinear
  let s : ℝ := Real.sqrt A
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hA_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_neC : (s : ℂ) ≠ 0 := by exact_mod_cast hs_ne
  have hs_sq : s ^ 2 = A := Real.sq_sqrt (le_of_lt hA_pos)
  let u : Fin (d + 1) → ℝ := fun μ => qre μ / s
  let v : Fin (d + 1) → ℝ := fun μ => qim μ / s
  refine ⟨(s : ℂ), u, v, hs_neC, ?_, ?_, ?_, ?_⟩
  · ext μ
    simp [u, v]
    field_simp [hs_ne]
  · have hinner_qre :
        (∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qre μ ^ 2) = A := by
      change
        (∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qre μ ^ 2) =
        ∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qre μ * qre μ
      apply Finset.sum_congr rfl
      intro μ _
      ring
    calc
      MinkowskiSpace.minkowskiInner d u u =
          (∑ μ : Fin (d + 1),
            MinkowskiSpace.metricSignature d μ * qre μ ^ 2) / s ^ 2 := by
            simp [u, MinkowskiSpace.minkowskiInner]
            calc
              ∑ μ : Fin (d + 1),
                  MinkowskiSpace.metricSignature d μ *
                    (qre μ / s) * (qre μ / s)
                  = ∑ μ : Fin (d + 1),
                      (MinkowskiSpace.metricSignature d μ * qre μ ^ 2) /
                        s ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro μ _
                    field_simp [hs_ne]
              _ =
                  (∑ μ : Fin (d + 1),
                    MinkowskiSpace.metricSignature d μ * qre μ ^ 2) /
                      s ^ 2 := by
                    exact
                      (Finset.sum_div Finset.univ
                        (fun μ : Fin (d + 1) =>
                          MinkowskiSpace.metricSignature d μ * qre μ ^ 2)
                        (s ^ 2)).symm
      _ = 1 := by
        rw [hinner_qre, ← hs_sq]
        field_simp [hs_ne]
  · have hinner_qim :
        (∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qim μ ^ 2) = A := by
      calc
        (∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qim μ ^ 2) =
            MinkowskiSpace.minkowskiInner d qim qim := by
              change
                (∑ μ : Fin (d + 1),
                  MinkowskiSpace.metricSignature d μ * qim μ ^ 2) =
                ∑ μ : Fin (d + 1),
                  MinkowskiSpace.metricSignature d μ * qim μ * qim μ
              apply Finset.sum_congr rfl
              intro μ _
              ring
        _ = A := by
          rw [← hnull_real.1]
    calc
      MinkowskiSpace.minkowskiInner d v v =
          (∑ μ : Fin (d + 1),
            MinkowskiSpace.metricSignature d μ * qim μ ^ 2) / s ^ 2 := by
            simp [v, MinkowskiSpace.minkowskiInner]
            calc
              ∑ μ : Fin (d + 1),
                  MinkowskiSpace.metricSignature d μ *
                    (qim μ / s) * (qim μ / s)
                  = ∑ μ : Fin (d + 1),
                      (MinkowskiSpace.metricSignature d μ * qim μ ^ 2) /
                        s ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro μ _
                    field_simp [hs_ne]
              _ =
                  (∑ μ : Fin (d + 1),
                    MinkowskiSpace.metricSignature d μ * qim μ ^ 2) /
                      s ^ 2 := by
                    exact
                      (Finset.sum_div Finset.univ
                        (fun μ : Fin (d + 1) =>
                          MinkowskiSpace.metricSignature d μ * qim μ ^ 2)
                        (s ^ 2)).symm
      _ = 1 := by
        rw [hinner_qim, ← hs_sq]
        field_simp [hs_ne]
  · have hinner_cross :
        (∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * qre μ * qim μ) = 0 := by
      simpa [MinkowskiSpace.minkowskiInner, mul_assoc] using hnull_real.2
    calc
      MinkowskiSpace.minkowskiInner d u v =
          (∑ μ : Fin (d + 1),
            MinkowskiSpace.metricSignature d μ * qre μ * qim μ) /
              s ^ 2 := by
            simp [u, v, MinkowskiSpace.minkowskiInner]
            calc
              ∑ μ : Fin (d + 1),
                  MinkowskiSpace.metricSignature d μ *
                    (qre μ / s) * (qim μ / s)
                  = ∑ μ : Fin (d + 1),
                      (MinkowskiSpace.metricSignature d μ * qre μ * qim μ) /
                        s ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro μ _
                    field_simp [hs_ne]
              _ =
                  (∑ μ : Fin (d + 1),
                    MinkowskiSpace.metricSignature d μ * qre μ * qim μ) /
                      s ^ 2 := by
                    exact
                      (Finset.sum_div Finset.univ
                        (fun μ : Fin (d + 1) =>
                          MinkowskiSpace.metricSignature d μ * qre μ * qim μ)
                        (s ^ 2)).symm
      _ = 0 := by
        rw [hinner_cross]
        simp

/-- A nonzero real null vector cannot be orthogonal to a strict forward-cone
vector. -/
theorem realNull_not_orthogonal_to_forwardCone
    [NeZero d]
    {ℓ η : Fin (d + 1) → ℝ}
    (hη : InOpenForwardCone d η)
    (hℓ_ne : ℓ ≠ 0)
    (hℓ_null : MinkowskiSpace.minkowskiInner d ℓ ℓ = 0) :
    MinkowskiSpace.minkowskiInner d ℓ η ≠ 0 := by
  have hη_spatial_lt :
      Real.sqrt (∑ i : Fin d, η i.succ ^ 2) < η 0 :=
    spatial_norm_lt_time hη
  have hℓ_time_abs :
      |ℓ 0| = Real.sqrt (∑ i : Fin d, ℓ i.succ ^ 2) :=
    realNull_abs_time_eq_spatial_norm (d := d) hℓ_null
  have hℓ_time_ne : ℓ 0 ≠ 0 := by
    intro h0
    have hsp0 : ∑ i : Fin d, ℓ i.succ ^ 2 = 0 := by
      have hdecomp := MinkowskiSpace.minkowskiInner_decomp d ℓ ℓ
      rw [hℓ_null, h0] at hdecomp
      have hsum : (∑ i : Fin d, ℓ i.succ * ℓ i.succ) = 0 := by
        linarith
      simpa [pow_two] using hsum
    have hsp_each : ∀ i : Fin d, ℓ i.succ = 0 :=
      sum_sq_eq_zero (fun i : Fin d => ℓ i.succ) hsp0
    apply hℓ_ne
    ext μ
    cases μ using Fin.cases with
    | zero => exact h0
    | succ i => exact hsp_each i
  intro horth
  have hdot_eq :
      (∑ i : Fin d, ℓ i.succ * η i.succ) = ℓ 0 * η 0 := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d ℓ η
    rw [horth] at hdecomp
    nlinarith
  have hcs :
      |∑ i : Fin d, ℓ i.succ * η i.succ| ≤
        Real.sqrt (∑ i : Fin d, ℓ i.succ ^ 2) *
          Real.sqrt (∑ i : Fin d, η i.succ ^ 2) :=
    abs_sum_mul_le_sqrt_mul_sqrt
      (fun i : Fin d => ℓ i.succ) (fun i => η i.succ)
  have habs_eq :
      |∑ i : Fin d, ℓ i.succ * η i.succ| = |ℓ 0| * η 0 := by
    rw [hdot_eq, abs_mul, abs_of_pos hη.1]
  have hle :
      |ℓ 0| * η 0 ≤
        |ℓ 0| * Real.sqrt (∑ i : Fin d, η i.succ ^ 2) := by
    simpa [habs_eq, hℓ_time_abs] using hcs
  exact
    not_le_of_gt hη_spatial_lt
      (le_of_mul_le_mul_left hle (abs_pos.mpr hℓ_time_ne))

/-- A nonzero real null vector cannot be orthogonal to every forward-tube
successive imaginary difference. -/
theorem nonzero_realNull_not_orthogonal_to_forwardCone_differences
    [NeZero d] [NeZero n]
    {ζ : Fin n → Fin (d + 1) → ℂ}
    {ℓ : Fin (d + 1) → ℝ}
    (hζ : ζ ∈ ForwardTube d n)
    (hℓ_ne : ℓ ≠ 0)
    (hℓ_null : MinkowskiSpace.minkowskiInner d ℓ ℓ = 0)
    (hℓ_orth :
      ∀ k : Fin n,
        MinkowskiSpace.minkowskiInner d ℓ
          (fun μ =>
            ((ζ k μ) -
              (if h : k.val = 0 then 0
               else ζ ⟨k.val - 1, by omega⟩ μ)).im) = 0) :
    False := by
  let k : Fin n := 0
  have hkFT : InOpenForwardCone d
      (fun μ =>
        ((ζ k μ) -
          (if h : k.val = 0 then 0
           else ζ ⟨k.val - 1, by omega⟩ μ)).im) :=
    hζ k
  exact
    realNull_not_orthogonal_to_forwardCone
      (d := d) hkFT hℓ_ne hℓ_null (hℓ_orth k)

/-- A complex null vector orthogonal to a forward-tube configuration has the
Hall-Wightman spacelike two-plane normal form.  The excluded real-lightlike
collinear alternative would make a nonzero real null vector orthogonal to a
strict forward-cone imaginary difference. -/
theorem complexNullOrthogonal_forwardTube_spacelikeNormalForm
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {ζ : Fin n → Fin (d + 1) → ℂ}
    {q : Fin (d + 1) → ℂ}
    (hζ : ζ ∈ ForwardTube d n)
    (hq_ne : q ≠ 0)
    (hq_null : sourceComplexMinkowskiInner d q q = 0)
    (hq_orth :
      ∀ i, sourceComplexMinkowskiInner d q (ζ i) = 0) :
    ∃ (α : ℂ) (u v : Fin (d + 1) → ℝ),
      α ≠ 0 ∧
      q = (fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ))) ∧
      MinkowskiSpace.minkowskiInner d u u = 1 ∧
      MinkowskiSpace.minkowskiInner d v v = 1 ∧
      MinkowskiSpace.minkowskiInner d u v = 0 := by
  let qre : Fin (d + 1) → ℝ := fun μ => (q μ).re
  let qim : Fin (d + 1) → ℝ := fun μ => (q μ).im
  have hnull_real :
      MinkowskiSpace.minkowskiInner d qre qre =
        MinkowskiSpace.minkowskiInner d qim qim ∧
      MinkowskiSpace.minkowskiInner d qre qim = 0 :=
    complexNull_iff_real_imag_equal_orthogonal
      (d := d) (q := q) hq_null
  have hqreim_ne : qre ≠ 0 ∨ qim ≠ 0 :=
    real_imag_nonzero_of_complex_ne_zero (q := q) hq_ne
  have hq_reim_fun :
      (fun μ => (qre μ : ℂ) + Complex.I * (qim μ : ℂ)) = q := by
    ext μ
    calc
      (qre μ : ℂ) + Complex.I * (qim μ : ℂ) =
          (qre μ : ℂ) + (qim μ : ℂ) * Complex.I := by
        ring
      _ = q μ := by
        simp [qre, qim]
  have hq_orth_reim :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (qre μ : ℂ) + Complex.I * (qim μ : ℂ))
          (ζ i) = 0 := by
    intro i
    simpa [hq_reim_fun] using hq_orth i
  have hnot_lightlike_collinear : ¬ realNullCollinear d qre qim := by
    intro hcoll
    rcases realNullCollinear_commonVector hcoll hqreim_ne with
      ⟨ℓ, hℓ_ne, hℓ_null, hqre, hqim⟩
    have hℓ_orth_diffs :
        ∀ k : Fin n,
          MinkowskiSpace.minkowskiInner d ℓ
            (fun μ =>
              ((ζ k μ) -
                (if h : k.val = 0 then 0
                 else ζ ⟨k.val - 1, by omega⟩ μ)).im) = 0 :=
      realNullCollinear_orthogonal_forwardTube_differences
        (d := d)
        hq_orth_reim
        hqreim_ne
        hqre hqim
    exact
      nonzero_realNull_not_orthogonal_to_forwardCone_differences
        (d := d) hζ hℓ_ne hℓ_null hℓ_orth_diffs
  rcases
    realImag_null_not_collinear_to_spacelike_orthonormal
      (d := d) hd hqreim_ne hnull_real hnot_lightlike_collinear with
    ⟨α, u, v, hα, hq_reim, huu, hvv, huv⟩
  refine ⟨α, u, v, hα, ?_, huu, hvv, huv⟩
  ext μ
  calc
    q μ = (qre μ : ℂ) + Complex.I * (qim μ : ℂ) := by
      exact (congrFun hq_reim_fun μ).symm
    _ = α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)) :=
      congrFun hq_reim μ

/-- Along a continuous timelike segment, the time orientation cannot switch
sign. -/
theorem forwardCone_timeOrientation_constant_on_timelike_segment
    [NeZero d]
    {γ : ℝ → Fin (d + 1) → ℝ}
    (hγ_cont : Continuous γ)
    (hγ_timelike :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        MinkowskiSpace.minkowskiInner d (γ s) (γ s) < 0)
    (hγ_one_time : (γ 1) 0 > 0) :
    (γ 0) 0 > 0 := by
  by_contra hnot
  have h0_nonpos : (γ 0) 0 ≤ 0 := le_of_not_gt hnot
  have htime_path :
      ContinuousOn (fun s : ℝ => (γ s) 0) (Set.Icc 0 1) :=
    (continuous_apply 0).comp_continuousOn hγ_cont.continuousOn
  have hzero :
      ∃ s ∈ Set.Icc (0 : ℝ) 1, (γ s) 0 = 0 := by
    simpa using
      (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
        htime_path ⟨h0_nonpos, le_of_lt hγ_one_time⟩)
  rcases hzero with ⟨s, hs, htime0⟩
  have hquad_nonneg :
      0 ≤ MinkowskiSpace.minkowskiInner d (γ s) (γ s) := by
    have hdecomp := MinkowskiSpace.minkowskiInner_decomp d (γ s) (γ s)
    have hsum_nonneg :
        0 ≤ ∑ i : Fin d, (γ s) i.succ * (γ s) i.succ :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg ((γ s) i.succ))
    rw [hdecomp, htime0]
    linarith
  exact not_lt_of_ge hquad_nonneg (hγ_timelike s hs)

/-- Hall-Wightman's equation (41): removing a spacelike orthogonal two-plane
component from an open-forward-cone vector preserves open-forward-cone
membership. -/
theorem forwardCone_remove_spacelikeOrthogonal_twoPlane
    [NeZero d]
    {Y u v : Fin (d + 1) → ℝ}
    {p r : ℝ}
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0)
    (hYu : MinkowskiSpace.minkowskiInner d Y u = 0)
    (hYv : MinkowskiSpace.minkowskiInner d Y v = 0)
    (hYpr : InOpenForwardCone d (fun μ => Y μ + p * u μ + r * v μ)) :
    InOpenForwardCone d Y := by
  have hinner_self_eq_quad :
      ∀ Z : Fin (d + 1) → ℝ,
        MinkowskiSpace.minkowskiInner d Z Z =
          ∑ μ : Fin (d + 1), minkowskiSignature d μ * Z μ ^ 2 := by
    intro Z
    unfold MinkowskiSpace.minkowskiInner
    apply Finset.sum_congr rfl
    intro μ _
    by_cases hμ : μ = 0
    · subst μ
      simp [MinkowskiSpace.metricSignature, minkowskiSignature, pow_two]
    · simp [MinkowskiSpace.metricSignature, minkowskiSignature, hμ, pow_two]
  have hsquare_decomp :
      ∀ s : ℝ,
        MinkowskiSpace.minkowskiInner d
          (fun μ => Y μ + s * p * u μ + s * r * v μ)
          (fun μ => Y μ + s * p * u μ + s * r * v μ)
        =
        MinkowskiSpace.minkowskiInner d Y Y +
          s ^ 2 * (p ^ 2 + r ^ 2) := by
    intro s
    have hpath :
        (fun μ => Y μ + s * p * u μ + s * r * v μ) =
          Y + (s * p) • u + (s * r) • v := by
      ext μ
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpath]
    simp [MinkowskiSpace.minkowskiInner_add_right,
      MinkowskiSpace.minkowskiInner_smul_right,
      huu, hvv, huv, hYu, hYv,
      MinkowskiSpace.minkowskiInner_comm]
    ring
  have hneg_at_one :
      MinkowskiSpace.minkowskiInner d Y Y + (p ^ 2 + r ^ 2) < 0 := by
    have hinner_path1 :
        MinkowskiSpace.minkowskiInner d
          (fun μ => Y μ + 1 * p * u μ + 1 * r * v μ)
          (fun μ => Y μ + 1 * p * u μ + 1 * r * v μ) < 0 := by
      rw [hinner_self_eq_quad]
      simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using hYpr.2
    simpa using (show
      MinkowskiSpace.minkowskiInner d
          (fun μ => Y μ + 1 * p * u μ + 1 * r * v μ)
          (fun μ => Y μ + 1 * p * u μ + 1 * r * v μ)
        = MinkowskiSpace.minkowskiInner d Y Y + (p ^ 2 + r ^ 2) by
          simpa using hsquare_decomp 1) ▸ hinner_path1
  have hYY_neg : MinkowskiSpace.minkowskiInner d Y Y < 0 := by
    nlinarith [sq_nonneg p, sq_nonneg r, hneg_at_one]
  have hpath_timelike :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        MinkowskiSpace.minkowskiInner d
          (fun μ => Y μ + s * p * u μ + s * r * v μ)
          (fun μ => Y μ + s * p * u μ + s * r * v μ) < 0 := by
    intro s hs
    rw [hsquare_decomp s]
    have hs_sq : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    nlinarith [sq_nonneg p, sq_nonneg r, hs_sq, hneg_at_one]
  have htime_path0 :
      (fun μ => Y μ + (0 : ℝ) * p * u μ + (0 : ℝ) * r * v μ) 0 > 0 :=
    forwardCone_timeOrientation_constant_on_timelike_segment
      (d := d)
      (γ := fun s μ => Y μ + s * p * u μ + s * r * v μ)
      (hγ_cont := by
        continuity)
      (hγ_timelike := hpath_timelike)
      (hγ_one_time := by simpa using hYpr.1)
  have htime_pos : Y 0 > 0 := by
    simpa using htime_path0
  have hYY_quad_neg :
      ∑ μ : Fin (d + 1), minkowskiSignature d μ * Y μ ^ 2 < 0 := by
    rw [← hinner_self_eq_quad]
    exact hYY_neg
  exact ⟨htime_pos, hYY_quad_neg⟩

/-- In the normal null plane `q = α (u + I v)`, orthogonality to `q`
relates the two real plane coordinates. -/
theorem hw_nullPlane_orthogonality_relation
    [NeZero d]
    {q ξ : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    (hα : α ≠ 0)
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (horth : sourceComplexMinkowskiInner d q ξ = 0) :
    sourceComplexMinkowskiInner d (fun μ => (v μ : ℂ)) ξ =
      Complex.I *
        sourceComplexMinkowskiInner d (fun μ => (u μ : ℂ)) ξ := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  have hq_smul : q = α • (U + Complex.I • V) := by
    ext μ
    simp [hq, U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  rw [hq_smul, sourceComplexMinkowskiInner_smul_left,
    sourceComplexMinkowskiInner_add_left,
    sourceComplexMinkowskiInner_smul_left] at horth
  have hsum :
      sourceComplexMinkowskiInner d U ξ +
        Complex.I * sourceComplexMinkowskiInner d V ξ = 0 :=
    (mul_eq_zero.mp horth).resolve_left hα
  have hmul := congrArg (fun z => Complex.I * z) hsum
  change
    Complex.I *
      (sourceComplexMinkowskiInner d U ξ +
        Complex.I * sourceComplexMinkowskiInner d V ξ) =
      Complex.I * 0 at hmul
  ring_nf at hmul
  have hzero :
        Complex.I * sourceComplexMinkowskiInner d U ξ -
          sourceComplexMinkowskiInner d V ξ = 0 := by
    simpa [sub_eq_add_neg] using hmul
  exact (sub_eq_zero.mp hzero).symm

/-- Hall-Wightman's coefficient split in the normal null plane.  Subtracting
`(B(u,ξᵢ)/α) q` kills both real spacelike plane coordinates. -/
theorem hw_secondRemark_coefficients_orthogonalTo_nullPlane
    [NeZero d]
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {q : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    (hα : α ≠ 0)
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0)
    (hq_orth :
      ∀ i, sourceComplexMinkowskiInner d q (ξ i) = 0) :
    ∃ (η : Fin n → Fin (d + 1) → ℂ)
      (β : Fin n → ℂ),
      (∀ i μ, ξ i μ = η i μ + β i * q μ) ∧
      (∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (u μ : ℂ)) (η i) = 0) ∧
      (∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (v μ : ℂ)) (η i) = 0) := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  let cu : (Fin (d + 1) → ℂ) → ℂ :=
    fun x => sourceComplexMinkowskiInner d U x
  let cv : (Fin (d + 1) → ℂ) → ℂ :=
    fun x => sourceComplexMinkowskiInner d V x
  let β : Fin n → ℂ := fun i => cu (ξ i) / α
  let η : Fin n → Fin (d + 1) → ℂ := fun i μ => ξ i μ - β i * q μ
  have hq_smul : q = α • (U + Complex.I • V) := by
    ext μ
    simp [hq, U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  have hUU : sourceComplexMinkowskiInner d U U = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huu
    simpa [U, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hUV : sourceComplexMinkowskiInner d U V = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huv
    simpa [U, V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVV : sourceComplexMinkowskiInner d V V = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hvv
    simpa [V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVU : sourceComplexMinkowskiInner d V U = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hUV
  have hcu_q : cu q = α := by
    change sourceComplexMinkowskiInner d U q = α
    rw [hq_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hUU, hUV]
    ring
  have hcv_q : cv q = Complex.I * α := by
    change sourceComplexMinkowskiInner d V q = Complex.I * α
    rw [hq_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hVU, hVV]
    ring
  refine ⟨η, β, ?_, ?_, ?_⟩
  · intro i μ
    simp [η]
  · intro i
    have heta : η i = ξ i - β i • q := by
      ext μ
      simp [η, Pi.smul_apply, smul_eq_mul]
    rw [heta, sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right]
    change cu (ξ i) - β i * cu q = 0
    rw [hcu_q]
    simp [β, cu, hα]
  · intro i
    have heta : η i = ξ i - β i • q := by
      ext μ
      simp [η, Pi.smul_apply, smul_eq_mul]
    have hcv_relation : cv (ξ i) = Complex.I * cu (ξ i) :=
      hw_nullPlane_orthogonality_relation
        (d := d) hα hq (hq_orth i)
    rw [heta, sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right]
    change cv (ξ i) - β i * cv q = 0
    rw [hcv_q]
    simp [β, cv, hcv_relation]
    field_simp [hα]
    ring

/-- Pointwise complex orthogonality to a real vector descends to
orthogonality of every successive imaginary difference. -/
theorem imag_difference_orthogonal_realVector
    [NeZero d]
    {η : Fin n → Fin (d + 1) → ℂ}
    {u : Fin (d + 1) → ℝ}
    (huη :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (u μ : ℂ)) (η i) = 0)
    (k : Fin n) :
    MinkowskiSpace.minkowskiInner d
      (fun μ =>
        (η k μ -
          (if h : k.val = 0 then 0
           else η ⟨k.val - 1, by omega⟩ μ)).im) u = 0 := by
  by_cases hk : k.val = 0
  · have h := congrArg Complex.im (huη k)
    simpa [sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.minkowskiInner_comm, hk, mul_comm, mul_left_comm,
      mul_assoc] using h
  · have hprev := huη ⟨k.val - 1, by omega⟩
    have hcurr := huη k
    have hdiff :
        sourceComplexMinkowskiInner d
          (fun μ => (u μ : ℂ))
          (η k - η ⟨k.val - 1, by omega⟩) = 0 := by
      rw [sourceComplexMinkowskiInner_sub_right, hcurr, hprev]
      simp
    have h := congrArg Complex.im hdiff
    simpa [sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.minkowskiInner_comm, hk, mul_comm, mul_left_comm,
      mul_assoc] using h

/-- Imaginary parts of scalar multiples of a normal-form null vector lie in
the real two-plane spanned by the normal directions. -/
theorem imag_nullNormalForm_coefficients
    [NeZero d]
    {q : Fin (d + 1) → ℂ}
    {α γ : ℂ}
    {u v : Fin (d + 1) → ℝ}
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ))) :
    ∃ p r : ℝ,
      (fun μ => (γ * q μ).im) =
        fun μ => p * u μ + r * v μ := by
  let δ : ℂ := γ * α
  refine ⟨δ.im, δ.re, ?_⟩
  ext μ
  simp [hq, δ, mul_add, Complex.mul_re, Complex.mul_im]
  ring

/-- Tube part of Hall-Wightman's second remark: after the coefficient split,
the residual configuration `η` itself is in the forward tube. -/
theorem hw_secondRemark_eta_mem_forwardTube
    [NeZero d]
    {ξ η : Fin n → Fin (d + 1) → ℂ}
    {a β : Fin n → ℂ}
    {q : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    (hξ_split : ∀ i μ, ξ i μ = η i μ + β i * q μ)
    (hq : q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0)
    (huη :
      ∀ i, sourceComplexMinkowskiInner d
        (fun μ => (u μ : ℂ)) (η i) = 0)
    (hvη :
      ∀ i, sourceComplexMinkowskiInner d
        (fun μ => (v μ : ℂ)) (η i) = 0)
    (hξaq : (fun i μ => ξ i μ + a i * q μ) ∈ ForwardTube d n) :
    η ∈ ForwardTube d n := by
  intro k
  let prevη : Fin (d + 1) → ℂ :=
    if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩
  let δη : Fin (d + 1) → ℂ := fun μ => η k μ - prevη μ
  let γ : ℂ :=
    (β k + a k) -
      (if h : k.val = 0 then 0
       else β ⟨k.val - 1, by omega⟩ + a ⟨k.val - 1, by omega⟩)
  have hdiff_tube :
      (fun μ =>
        (let prev : Fin (d + 1) → ℂ :=
          if h : k.val = 0 then 0
          else (fun i μ => ξ i μ + a i * q μ) ⟨k.val - 1, by omega⟩
        ((fun i μ => ξ i μ + a i * q μ) k μ - prev μ).im))
      = fun μ => (δη μ + γ * q μ).im := by
    ext μ
    by_cases hk : k.val = 0
    · simp [δη, prevη, hξ_split, γ, hk, add_comm, add_left_comm,
        add_assoc, sub_eq_add_neg]
      ring
    · simp [δη, prevη, hξ_split, γ, hk, add_comm, add_left_comm,
        add_assoc, sub_eq_add_neg]
      ring
  have horth_u :
      MinkowskiSpace.minkowskiInner d (fun μ => (δη μ).im) u = 0 :=
    by
      by_cases hk : k.val = 0
      · simpa [δη, prevη, hk] using
          imag_difference_orthogonal_realVector (d := d) huη k
      · simpa [δη, prevη, hk] using
          imag_difference_orthogonal_realVector (d := d) huη k
  have horth_v :
      MinkowskiSpace.minkowskiInner d (fun μ => (δη μ).im) v = 0 :=
    by
      by_cases hk : k.val = 0
      · simpa [δη, prevη, hk] using
          imag_difference_orthogonal_realVector (d := d) hvη k
      · simpa [δη, prevη, hk] using
          imag_difference_orthogonal_realVector (d := d) hvη k
  have hcone_with_plane :
      InOpenForwardCone d (fun μ => (δη μ + γ * q μ).im) := by
    have hcone_raw := hξaq k
    dsimp [ForwardTube] at hcone_raw
    convert hcone_raw using 1
    ext μ
    by_cases hk : k.val = 0
    · simp [δη, prevη, γ, hk, hξ_split, add_comm, add_left_comm,
        add_assoc, sub_eq_add_neg]
      ring
    · simp [δη, prevη, γ, hk, hξ_split, add_comm, add_left_comm,
        add_assoc, sub_eq_add_neg]
      ring
  rcases imag_nullNormalForm_coefficients (d := d) (γ := γ) hq with
    ⟨p, r, himag_eq⟩
  have hcone_plane_real :
      InOpenForwardCone d (fun μ => (δη μ).im + p * u μ + r * v μ) := by
    have hfun :
        (fun μ => (δη μ + γ * q μ).im) =
          fun μ => (δη μ).im + p * u μ + r * v μ := by
      ext μ
      calc
        (δη μ + γ * q μ).im = (δη μ).im + (γ * q μ).im := by
          rw [Complex.add_im]
        _ = (δη μ).im + (p * u μ + r * v μ) := by
          rw [congrFun himag_eq μ]
        _ = (δη μ).im + p * u μ + r * v μ := by
          ring
    exact hfun ▸ hcone_with_plane
  have hremove :=
    forwardCone_remove_spacelikeOrthogonal_twoPlane
      (d := d) (Y := fun μ => (δη μ).im)
      (u := u) (v := v) (p := p) (r := r)
      huu hvv huv horth_u horth_v
      hcone_plane_real
  simpa [ForwardTube, δη, prevη] using hremove

/-- Hall-Wightman's second remark after Lemma 2: a forward-tube point with one
orthogonal complex-null residual can be rewritten as a forward-tube point plus
the same null residual in standard spacelike normal form. -/
theorem hw_secondRemark_forwardTube_singleNullResidual_normalForm
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → ℂ}
    {q : Fin (d + 1) → ℂ}
    (hξq : (fun i μ => ξ i μ + a i * q μ) ∈ ForwardTube d n)
    (hq_null : sourceComplexMinkowskiInner d q q = 0)
    (hq_orth :
      ∀ i, sourceComplexMinkowskiInner d q (ξ i) = 0) :
    ∃ (η : Fin n → Fin (d + 1) → ℂ)
      (β : Fin n → ℂ),
      η ∈ ForwardTube d n ∧
      HWNullResidualNormalForm d n q η ∧
      (∀ i μ, ξ i μ = η i μ + β i * q μ) := by
  by_cases hq0 : q = 0
  · refine ⟨ξ, 0, ?_, ?_, ?_⟩
    · simpa [hq0] using hξq
    · exact Or.inl hq0
    · intro i μ
      simp [hq0]
  · have horth_forward :
        ∀ i,
          sourceComplexMinkowskiInner d q
            ((fun i μ => ξ i μ + a i * q μ) i) = 0 := by
      intro i
      change sourceComplexMinkowskiInner d q
          (ξ i + a i • q) = 0
      rw [sourceComplexMinkowskiInner_add_right,
        sourceComplexMinkowskiInner_smul_right,
        hq_orth i, hq_null]
      ring
    rcases
      complexNullOrthogonal_forwardTube_spacelikeNormalForm
        (d := d) hd hξq hq0 hq_null horth_forward with
      ⟨α, u, v, hα, hq, huu, hvv, huv⟩
    rcases
      hw_secondRemark_coefficients_orthogonalTo_nullPlane
        (d := d) (ξ := ξ) (q := q)
        hα hq huu hvv huv hq_orth with
      ⟨η, β, hξ_split, huη, hvη⟩
    have hηFT : η ∈ ForwardTube d n :=
      hw_secondRemark_eta_mem_forwardTube
        (d := d) hξ_split hq huu hvv huv huη hvη hξq
    refine ⟨η, β, hηFT, ?_, hξ_split⟩
    exact Or.inr ⟨α, u, v, hα, hq, huu, hvv, huv, huη, hvη⟩

/-- Explicit complex two-plane rotation from Hall-Wightman's third remark.
It fixes the orthogonal complement of the real spacelike plane spanned by
`u,v` and applies the hyperbolic complex rotation on that plane. -/
def complexMinkowskiTwoPlaneRotation
    [NeZero d]
    (u v : Fin (d + 1) → ℝ)
    (t : ℝ)
    (x : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  let cu : ℂ :=
    sourceComplexMinkowskiInner d (fun μ => (u μ : ℂ)) x
  let cv : ℂ :=
    sourceComplexMinkowskiInner d (fun μ => (v μ : ℂ)) x
  fun μ =>
    x μ +
      cu * (((Real.cosh t : ℂ) - 1) * (u μ : ℂ) +
        Complex.I * (Real.sinh t : ℂ) * (v μ : ℂ)) +
      cv * (-Complex.I * (Real.sinh t : ℂ) * (u μ : ℂ) +
        (((Real.cosh t : ℂ) - 1) * (v μ : ℂ)))

set_option maxHeartbeats 800000 in
/-- The two-plane rotation as a complex linear map. -/
def complexMinkowskiTwoPlaneRotationLinearMap
    [NeZero d]
    (u v : Fin (d + 1) → ℝ)
    (t : ℝ) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) where
  toFun := complexMinkowskiTwoPlaneRotation (d := d) u v t
  map_add' := by
    intro x y
    ext μ
    simp [complexMinkowskiTwoPlaneRotation,
      sourceComplexMinkowskiInner_add_right,
      add_comm, add_left_comm, add_assoc, mul_add]
    ring
  map_smul' := by
    intro c x
    ext μ
    simp [complexMinkowskiTwoPlaneRotation,
      sourceComplexMinkowskiInner_smul_right,
      mul_comm, mul_left_comm]
    ring

@[simp]
theorem complexMinkowskiTwoPlaneRotationLinearMap_apply
    [NeZero d]
    (u v : Fin (d + 1) → ℝ)
    (t : ℝ)
    (x : Fin (d + 1) → ℂ) :
    complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t x =
      complexMinkowskiTwoPlaneRotation (d := d) u v t x :=
  rfl

/-- The two-plane rotation fixes vectors orthogonal to both plane directions. -/
theorem complexMinkowskiTwoPlaneRotation_apply_orthogonal
    [NeZero d]
    {u v x : Fin (d + 1) → ℂ}
    {ur vr : Fin (d + 1) → ℝ}
    {t : ℝ}
    (hu : u = fun μ => (ur μ : ℂ))
    (hv : v = fun μ => (vr μ : ℂ))
    (hux : sourceComplexMinkowskiInner d u x = 0)
    (hvx : sourceComplexMinkowskiInner d v x = 0) :
    complexMinkowskiTwoPlaneRotation (d := d) ur vr t x = x := by
  have hux' :
      sourceComplexMinkowskiInner d (fun μ => (ur μ : ℂ)) x = 0 := by
    simpa [hu] using hux
  have hvx' :
      sourceComplexMinkowskiInner d (fun μ => (vr μ : ℂ)) x = 0 := by
    simpa [hv] using hvx
  ext μ
  simp [complexMinkowskiTwoPlaneRotation, hux', hvx']

/-- Action of the two-plane rotation on the first spacelike direction. -/
theorem complexMinkowskiTwoPlaneRotation_apply_u
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    {t : ℝ}
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    complexMinkowskiTwoPlaneRotation (d := d) u v t
        (fun μ => (u μ : ℂ)) =
      fun μ =>
        (Real.cosh t : ℂ) * (u μ : ℂ) +
        Complex.I * (Real.sinh t : ℂ) * (v μ : ℂ) := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  have hUU : sourceComplexMinkowskiInner d U U = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huu
    simpa [U, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hUV : sourceComplexMinkowskiInner d U V = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huv
    simpa [U, V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVU : sourceComplexMinkowskiInner d V U = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hUV
  ext μ
  simp [complexMinkowskiTwoPlaneRotation, U, V, hUU, hVU]
  ring

/-- Action of the two-plane rotation on the second spacelike direction. -/
theorem complexMinkowskiTwoPlaneRotation_apply_v
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    {t : ℝ}
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    complexMinkowskiTwoPlaneRotation (d := d) u v t
        (fun μ => (v μ : ℂ)) =
      fun μ =>
        -Complex.I * (Real.sinh t : ℂ) * (u μ : ℂ) +
        (Real.cosh t : ℂ) * (v μ : ℂ) := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  have hUV : sourceComplexMinkowskiInner d U V = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huv
    simpa [U, V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVV : sourceComplexMinkowskiInner d V V = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hvv
    simpa [V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  ext μ
  simp [complexMinkowskiTwoPlaneRotation, U, V, hUV, hVV]
  ring

/-- The two-plane rotation scales the normal-form null vector `u + I v` by
`exp t`. -/
theorem complexMinkowskiTwoPlaneRotation_scale_null
    [NeZero d]
    {q : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    {t : ℝ}
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    complexMinkowskiTwoPlaneRotation (d := d) u v t q =
      fun μ => (Real.exp t : ℂ) * q μ := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  have hq_smul : q = α • (U + Complex.I • V) := by
    ext μ
    simp [hq, U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  have hUU : sourceComplexMinkowskiInner d U U = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huu
    simpa [U, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hUV : sourceComplexMinkowskiInner d U V = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huv
    simpa [U, V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVV : sourceComplexMinkowskiInner d V V = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hvv
    simpa [V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVU : sourceComplexMinkowskiInner d V U = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hUV
  have hUq : sourceComplexMinkowskiInner d U q = α := by
    rw [hq_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hUU, hUV]
    ring
  have hVq : sourceComplexMinkowskiInner d V q = Complex.I * α := by
    rw [hq_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hVU, hVV]
    ring
  ext μ
  have hqμ : q μ = α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)) :=
    congrFun hq μ
  simp [complexMinkowskiTwoPlaneRotation, U, V, hUq, hVq]
  rw [hqμ, ← Complex.cosh_add_sinh (t : ℂ)]
  ring_nf
  rw [Complex.I_sq]
  ring

set_option maxHeartbeats 1000000 in
/-- The explicit two-plane rotation preserves the complex Minkowski bilinear
form. -/
theorem complexMinkowskiTwoPlaneRotation_preserves_inner
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    {t : ℝ}
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0)
    (x y : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d
      (complexMinkowskiTwoPlaneRotation (d := d) u v t x)
      (complexMinkowskiTwoPlaneRotation (d := d) u v t y) =
    sourceComplexMinkowskiInner d x y := by
  let U : Fin (d + 1) → ℂ := fun μ => (u μ : ℂ)
  let V : Fin (d + 1) → ℂ := fun μ => (v μ : ℂ)
  let cu : (Fin (d + 1) → ℂ) → ℂ :=
    fun z => sourceComplexMinkowskiInner d U z
  let cv : (Fin (d + 1) → ℂ) → ℂ :=
    fun z => sourceComplexMinkowskiInner d V z
  have hUU : sourceComplexMinkowskiInner d U U = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huu
    simpa [U, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hUV : sourceComplexMinkowskiInner d U V = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) huv
    simpa [U, V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  have hVU : sourceComplexMinkowskiInner d V U = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hUV
  have hVV : sourceComplexMinkowskiInner d V V = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hvv
    simpa [V, sourceComplexMinkowskiInner, MinkowskiSpace.minkowskiInner]
      using h
  let xperp : Fin (d + 1) → ℂ :=
    fun μ => x μ - cu x * U μ - cv x * V μ
  let yperp : Fin (d + 1) → ℂ :=
    fun μ => y μ - cu y * U μ - cv y * V μ
  have hxperp_u : sourceComplexMinkowskiInner d U xperp = 0 := by
    change sourceComplexMinkowskiInner d U
      (x - cu x • U - cv x • V) = 0
    rw [sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    change cu x - cu x * sourceComplexMinkowskiInner d U U -
      cv x * sourceComplexMinkowskiInner d U V = 0
    rw [hUU, hUV]
    ring
  have hxperp_v : sourceComplexMinkowskiInner d V xperp = 0 := by
    change sourceComplexMinkowskiInner d V
      (x - cu x • U - cv x • V) = 0
    rw [sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    change cv x - cu x * sourceComplexMinkowskiInner d V U -
      cv x * sourceComplexMinkowskiInner d V V = 0
    rw [hVU, hVV]
    ring
  have hyperp_u : sourceComplexMinkowskiInner d U yperp = 0 := by
    change sourceComplexMinkowskiInner d U
      (y - cu y • U - cv y • V) = 0
    rw [sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    change cu y - cu y * sourceComplexMinkowskiInner d U U -
      cv y * sourceComplexMinkowskiInner d U V = 0
    rw [hUU, hUV]
    ring
  have hyperp_v : sourceComplexMinkowskiInner d V yperp = 0 := by
    change sourceComplexMinkowskiInner d V
      (y - cu y • U - cv y • V) = 0
    rw [sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    change cv y - cu y * sourceComplexMinkowskiInner d V U -
      cv y * sourceComplexMinkowskiInner d V V = 0
    rw [hVU, hVV]
    ring
  have hxperp_u_right : sourceComplexMinkowskiInner d xperp U = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hxperp_u
  have hxperp_v_right : sourceComplexMinkowskiInner d xperp V = 0 := by
    simpa [sourceComplexMinkowskiInner_comm] using hxperp_v
  have hdecomp_x : x = xperp + cu x • U + cv x • V := by
    ext μ
    simp [xperp, U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdecomp_y : y = yperp + cu y • U + cv y • V := by
    ext μ
    simp [yperp, U, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let L := complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t
  let C : ℂ := (Real.cosh t : ℂ)
  let S : ℂ := (Real.sinh t : ℂ)
  let D : ℂ := Complex.I * S
  let E : ℂ := -Complex.I * S
  have hfix_xperp : L xperp = xperp := by
    simpa [L, U, V] using
      complexMinkowskiTwoPlaneRotation_apply_orthogonal
        (d := d) (ur := u) (vr := v) (t := t)
        (u := U) (v := V) (x := xperp)
        rfl rfl hxperp_u hxperp_v
  have hfix_yperp : L yperp = yperp := by
    simpa [L, U, V] using
      complexMinkowskiTwoPlaneRotation_apply_orthogonal
        (d := d) (ur := u) (vr := v) (t := t)
        (u := U) (v := V) (x := yperp)
        rfl rfl hyperp_u hyperp_v
  have hLU :
      L U =
        C • U + D • V := by
    ext μ
    change complexMinkowskiTwoPlaneRotation (d := d) u v t
        (fun μ => (u μ : ℂ)) μ =
      (C • U + D • V) μ
    rw [congrFun
      (complexMinkowskiTwoPlaneRotation_apply_u
        (d := d) (u := u) (v := v) (t := t) huu huv) μ]
    simp [U, V, C, D, S, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hLV :
      L V =
        E • U + C • V := by
    ext μ
    change complexMinkowskiTwoPlaneRotation (d := d) u v t
        (fun μ => (v μ : ℂ)) μ =
      (E • U + C • V) μ
    rw [congrFun
      (complexMinkowskiTwoPlaneRotation_apply_v
        (d := d) (u := u) (v := v) (t := t) hvv huv) μ]
    simp [U, V, C, E, S, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hLx :
      complexMinkowskiTwoPlaneRotation (d := d) u v t x =
        xperp +
          cu x • (C • U + D • V) +
          cv x • (E • U + C • V) := by
    change L x = _
    calc
      L x = L (xperp + cu x • U + cv x • V) := by
        exact congrArg L hdecomp_x
      _ = L xperp + cu x • L U + cv x • L V := by
        simp [map_add, map_smul, add_assoc]
      _ = xperp + cu x • (C • U + D • V) +
          cv x • (E • U + C • V) := by
        rw [hfix_xperp, hLU, hLV]
  have hLy :
      complexMinkowskiTwoPlaneRotation (d := d) u v t y =
        yperp +
          cu y • (C • U + D • V) +
          cv y • (E • U + C • V) := by
    change L y = _
    calc
      L y = L (yperp + cu y • U + cv y • V) := by
        exact congrArg L hdecomp_y
      _ = L yperp + cu y • L U + cv y • L V := by
        simp [map_add, map_smul, add_assoc]
      _ = yperp + cu y • (C • U + D • V) +
          cv y • (E • U + C • V) := by
        rw [hfix_yperp, hLU, hLV]
  calc
    sourceComplexMinkowskiInner d
        (complexMinkowskiTwoPlaneRotation (d := d) u v t x)
        (complexMinkowskiTwoPlaneRotation (d := d) u v t y)
        =
      sourceComplexMinkowskiInner d
        (xperp +
          cu x • (C • U + D • V) +
          cv x • (E • U + C • V))
        (yperp +
          cu y • (C • U + D • V) +
          cv y • (E • U + C • V)) := by
        rw [hLx, hLy]
    _ =
      sourceComplexMinkowskiInner d
        (xperp + cu x • U + cv x • V)
        (yperp + cu y • U + cv y • V) := by
        simp [sourceComplexMinkowskiInner_add_left,
          sourceComplexMinkowskiInner_add_right,
          sourceComplexMinkowskiInner_smul_left,
          sourceComplexMinkowskiInner_smul_right,
          hxperp_u_right, hxperp_v_right, hyperp_u, hyperp_v,
          hUU, hUV, hVU, hVV]
        simp [C, D, E, S]
        ring_nf
        rw [Complex.I_sq]
        ring_nf
        have hcosh := Complex.cosh_sq_sub_sinh_sq (t : ℂ)
        have hcosh_eq :
            Complex.cosh (t : ℂ) ^ 2 =
              1 + Complex.sinh (t : ℂ) ^ 2 :=
          by
            rw [← hcosh]
            ring
        rw [hcosh_eq]
        ring
    _ = sourceComplexMinkowskiInner d x y := by
      rw [← hdecomp_x, ← hdecomp_y]

/-- A complex-linear map preserving the source complex Minkowski inner product
has a coordinate matrix satisfying the componentwise Lorentz metric equation. -/
theorem sourceComplexMinkowskiInner_preserving_toMatrix'_metric
    [NeZero d]
    (L :
      (Fin (d + 1) → ℂ) →ₗ[ℂ]
        (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (L x) (L y) =
          sourceComplexMinkowskiInner d x y) :
    ∀ μ ν : Fin (d + 1),
      ∑ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
          (LinearMap.toMatrix' L) α μ *
          (LinearMap.toMatrix' L) α ν =
      if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  have h := hpres (Pi.single μ (1 : ℂ)) (Pi.single ν (1 : ℂ))
  by_cases hμν : μ = ν
  · subst ν
    simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
      Pi.single_apply, mul_assoc, mul_comm, mul_left_comm] using h
  · have hνμ : ν ≠ μ := by
      intro h
      exact hμν h.symm
    simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
      Pi.single_apply, hμν, hνμ, mul_assoc, mul_comm, mul_left_comm] using h

/-- The coordinate determinant of the two-plane rotation has square one, as
for any linear map preserving the complex Minkowski metric. -/
theorem complexMinkowskiTwoPlaneRotation_det_sq
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    {t : ℝ}
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    (LinearMap.toMatrix'
      (complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t)).det ^ 2 =
      1 := by
  let L := complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := LinearMap.toMatrix' L
  have hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (L x) (L y) =
          sourceComplexMinkowskiInner d x y :=
    complexMinkowskiTwoPlaneRotation_preserves_inner
      (d := d) huu hvv huv
  have hmetric :
      ∀ μ ν : Fin (d + 1),
        ∑ α : Fin (d + 1),
          (minkowskiSignature d α : ℂ) * M α μ * M α ν =
        if μ = ν then (minkowskiSignature d μ : ℂ) else 0 :=
    sourceComplexMinkowskiInner_preserving_toMatrix'_metric
      (d := d) L hpres
  have hmatrix :
      M.transpose * ComplexLorentzGroup.ηℂ (d := d) * M =
        ComplexLorentzGroup.ηℂ (d := d) := by
    ext μ ν
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      ComplexLorentzGroup.ηℂ, Matrix.diagonal_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    convert hmetric μ ν using 1
    apply Finset.sum_congr rfl
    intro α _
    ring
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hη_ne :
      (ComplexLorentzGroup.ηℂ (d := d) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det ≠ 0 := by
    have h := congrArg Matrix.det (ComplexLorentzGroup.ηℂ_sq (d := d))
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have h2 :
      M.det ^ 2 *
          (ComplexLorentzGroup.ηℂ (d := d) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det =
        1 *
          (ComplexLorentzGroup.ηℂ (d := d) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det := by
    rw [one_mul, sq]
    linear_combination hdet
  have hsq : M.det ^ 2 = 1 :=
    mul_right_cancel₀ hη_ne h2
  simpa [M, L] using hsq

/-- The explicit two-plane rotation lies on the determinant-one branch. -/
theorem complexMinkowskiTwoPlaneRotation_det_one
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    (t : ℝ)
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    (LinearMap.toMatrix'
      (complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t)).det =
      1 := by
  let detPath : ℝ → ℂ := fun s =>
    (LinearMap.toMatrix'
      (complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v s)).det
  have hdet_sq : ∀ s : ℝ, detPath s ^ 2 = 1 := by
    intro s
    exact
      complexMinkowskiTwoPlaneRotation_det_sq
        (d := d) (u := u) (v := v) (t := s) huu hvv huv
  have hdet_0 : detPath 0 = 1 := by
    have hL0 :
        complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v 0 =
          LinearMap.id := by
      ext x μ
      simp [complexMinkowskiTwoPlaneRotationLinearMap,
        complexMinkowskiTwoPlaneRotation]
    simp [detPath, hL0]
  have hdet_cont : Continuous detPath := by
    have hmat_cont :
        Continuous fun s : ℝ =>
          LinearMap.toMatrix'
            (complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v s) := by
      apply continuous_matrix
      intro μ ν
      have hentry :
          Continuous fun s : ℝ =>
            complexMinkowskiTwoPlaneRotation (d := d) u v s
              (Pi.single ν (1 : ℂ)) μ := by
        unfold complexMinkowskiTwoPlaneRotation
        continuity
      simpa [LinearMap.toMatrix'_apply,
        complexMinkowskiTwoPlaneRotationLinearMap] using hentry
    exact hmat_cont.matrix_det
  have hcover : ∀ s : ℝ, detPath s = 1 ∨ detPath s = -1 := by
    intro s
    have h0 : (detPath s - 1) * (detPath s + 1) = 0 := by
      calc
        (detPath s - 1) * (detPath s + 1) =
            detPath s ^ 2 - 1 := by
          ring
        _ = 0 := by
          rw [hdet_sq s]
          ring
    rcases mul_eq_zero.mp h0 with h1 | h2
    · left
      exact sub_eq_zero.mp h1
    · right
      exact eq_neg_of_add_eq_zero_left h2
  have h1_closed : IsClosed {s : ℝ | detPath s = 1} :=
    (isClosed_singleton (x := (1 : ℂ))).preimage hdet_cont
  have hm1_closed : IsClosed {s : ℝ | detPath s = -1} :=
    (isClosed_singleton (x := (-1 : ℂ))).preimage hdet_cont
  have h1_open : IsOpen {s : ℝ | detPath s = 1} := by
    rw [show {s : ℝ | detPath s = 1} =
        {s : ℝ | detPath s = -1}ᶜ from by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by
        rw [h1] at hm1
        norm_num at hm1,
        fun hne => (hcover s).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ :=
    IsClopen.eq_univ ⟨h1_closed, h1_open⟩ ⟨0, hdet_0⟩
  have ht_mem : t ∈ {s : ℝ | detPath s = 1} :=
    h1_univ ▸ Set.mem_univ t
  simpa [detPath] using ht_mem

/-- The explicit two-plane rotation is represented by a complex Lorentz-group
element. -/
theorem complexMinkowskiTwoPlaneRotation_to_complexLorentzGroup
    [NeZero d]
    {u v : Fin (d + 1) → ℝ}
    (t : ℝ)
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    ∃ A : ComplexLorentzGroup d,
      ∀ x μ,
        complexLorentzVectorAction A x μ =
          complexMinkowskiTwoPlaneRotation (d := d) u v t x μ := by
  let L := complexMinkowskiTwoPlaneRotationLinearMap (d := d) u v t
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := LinearMap.toMatrix' L
  have hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (L x) (L y) =
          sourceComplexMinkowskiInner d x y :=
    complexMinkowskiTwoPlaneRotation_preserves_inner
      (d := d) huu hvv huv
  have hmetric :
      ∀ μ ν : Fin (d + 1),
        ∑ α : Fin (d + 1),
          (minkowskiSignature d α : ℂ) * M α μ * M α ν =
        if μ = ν then (minkowskiSignature d μ : ℂ) else 0 :=
    sourceComplexMinkowskiInner_preserving_toMatrix'_metric
      (d := d) L hpres
  have hdet : M.det = 1 := by
    simpa [M, L] using
      complexMinkowskiTwoPlaneRotation_det_one
        (d := d) (u := u) (v := v) t huu hvv huv
  refine ⟨⟨M, hmetric, hdet⟩, ?_⟩
  intro x μ
  have happ := congrFun (LinearMap.toMatrix'_mulVec L x) μ
  change (M *ᵥ x) μ = L x μ
  exact happ

/-- Lorentz family implementing Hall-Wightman's complex two-plane rotation:
it fixes the orthogonal complement of `span {u,v}` and scales
`q = α (u + I v)` by `exp t`. -/
theorem complexMinkowski_twoPlaneComplexRotation_lorentz
    [NeZero d]
    {q : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0) :
    ∃ A : ℝ → ComplexLorentzGroup d,
      (∀ t (x : Fin (d + 1) → ℂ),
        sourceComplexMinkowskiInner d (fun μ => (u μ : ℂ)) x = 0 →
        sourceComplexMinkowskiInner d (fun μ => (v μ : ℂ)) x = 0 →
        ∀ μ, complexLorentzVectorAction (A t) x μ = x μ) ∧
      (∀ t μ,
        complexLorentzVectorAction (A t) q μ =
          (Real.exp t : ℂ) * q μ) := by
  choose A hA_apply using
    fun t =>
      complexMinkowskiTwoPlaneRotation_to_complexLorentzGroup
        (d := d) (u := u) (v := v) t huu hvv huv
  refine ⟨A, ?_, ?_⟩
  · intro t x hux hvx μ
    calc
      complexLorentzVectorAction (A t) x μ =
          complexMinkowskiTwoPlaneRotation (d := d) u v t x μ :=
        hA_apply t x μ
      _ = x μ :=
        congrFun
          (complexMinkowskiTwoPlaneRotation_apply_orthogonal
            (d := d) (ur := u) (vr := v) (t := t)
            (u := fun μ => (u μ : ℂ))
            (v := fun μ => (v μ : ℂ))
            rfl rfl hux hvx) μ
  · intro t μ
    calc
      complexLorentzVectorAction (A t) q μ =
          complexMinkowskiTwoPlaneRotation (d := d) u v t q μ :=
        hA_apply t q μ
      _ = (Real.exp t : ℂ) * q μ :=
        congrFun
          (complexMinkowskiTwoPlaneRotation_scale_null
            (d := d) (t := t) hq huu hvv huv) μ

/-- Configuration-level form of the two-plane scaling family. -/
theorem complexMinkowski_nullPlaneScalingFamily
    [NeZero d]
    {η : Fin n → Fin (d + 1) → ℂ}
    {q : Fin (d + 1) → ℂ}
    {α : ℂ} {u v : Fin (d + 1) → ℝ}
    (hq :
      q = fun μ => α * ((u μ : ℂ) + Complex.I * (v μ : ℂ)))
    (huu : MinkowskiSpace.minkowskiInner d u u = 1)
    (hvv : MinkowskiSpace.minkowskiInner d v v = 1)
    (huv : MinkowskiSpace.minkowskiInner d u v = 0)
    (huη :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (u μ : ℂ)) (η i) = 0)
    (hvη :
      ∀ i,
        sourceComplexMinkowskiInner d
          (fun μ => (v μ : ℂ)) (η i) = 0) :
    ∃ A : ℝ → ComplexLorentzGroup d,
      (∀ t i μ, complexLorentzAction (A t) η i μ = η i μ) ∧
      (∀ t μ,
        complexLorentzVectorAction (A t) q μ =
          (Real.exp t : ℂ) * q μ) := by
  rcases
    complexMinkowski_twoPlaneComplexRotation_lorentz
      (d := d) hq huu hvv huv with
    ⟨A, hfix, hscale⟩
  refine ⟨A, ?_, hscale⟩
  intro t i μ
  exact hfix t (η i) (huη i) (hvη i) μ

/-- Openness of the forward tube at a null-normal-form base point: for fixed
coefficients, the perturbation `η + exp(-t) b q` is eventually forward-tube
as `t → +∞`. -/
theorem forwardTube_eventually_singleNullSmallCoefficients
    [NeZero d]
    {η : Fin n → Fin (d + 1) → ℂ}
    (hη : η ∈ ForwardTube d n)
    (b : Fin n → ℂ)
    (q : Fin (d + 1) → ℂ) :
    ∀ᶠ t : ℝ in atTop,
      (fun i μ => η i μ + Real.exp (-t) * b i * q μ) ∈
        ForwardTube d n := by
  have hopen : IsOpen (ForwardTube d n) := isOpen_forwardTube
  have htend :
      Tendsto
        (fun t : ℝ =>
          fun i μ => (Real.exp (-t) : ℂ) * b i * q μ)
        atTop
        (nhds (0 : Fin n → Fin (d + 1) → ℂ)) :=
    tendsto_singleResidual_exp_neg_zero (d := d) (n := n) b q
  have hto :
      Tendsto
        (fun t : ℝ =>
          fun i μ => η i μ + (Real.exp (-t) : ℂ) * b i * q μ)
        atTop (nhds η) := by
    simpa using htend.const_add η
  exact hto.eventually (hopen.mem_nhds hη)

/-- Hall-Wightman's third remark in normal form: in the standard null plane,
all coefficient choices along the null vector lie in the extended tube. -/
theorem hw_thirdRemark_nullNormalForm_allCoefficients_mem_extendedTube
    [NeZero d]
    {η : Fin n → Fin (d + 1) → ℂ}
    {q : Fin (d + 1) → ℂ}
    (hη : η ∈ ForwardTube d n)
    (hnorm : HWNullResidualNormalForm d n q η) :
    ∀ b : Fin n → ℂ,
      (fun i μ => η i μ + b i * q μ) ∈ ExtendedTube d n := by
  intro b
  rcases hnorm with hq0 | ⟨α, u, v, hα, hq, huu, hvv, huv, huη, hvη⟩
  · simpa [hq0] using forwardTube_subset_extendedTube hη
  · rcases
      complexMinkowski_nullPlaneScalingFamily
        (d := d) (η := η) (q := q) hq huu hvv huv huη hvη with
      ⟨A, hA_fix_η, hA_scale_q⟩
    have hsmall :
        ∀ᶠ t : ℝ in atTop,
          (fun i μ => η i μ + (Real.exp (-t) : ℂ) * b i * q μ) ∈
            ForwardTube d n :=
      forwardTube_eventually_singleNullSmallCoefficients
        (d := d) hη b q
    rcases hsmall.exists with ⟨t, htFT⟩
    have hexp : (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    have hA_eq :
        complexLorentzAction (A t)
          (fun i μ => η i μ + (Real.exp (-t) : ℂ) * b i * q μ) =
        (fun i μ => η i μ + b i * q μ) := by
      ext i μ
      have hsplit :=
        congrFun
          (congrFun
            (complexLorentzAction_add (A t) η
              (fun i μ => ((Real.exp (-t) : ℂ) * b i) * q μ)) i) μ
      have hcoef :=
        congrFun
          (congrFun
            (complexLorentzAction_smul_vector (A t)
              (fun i => (Real.exp (-t) : ℂ) * b i) q) i) μ
      rw [hsplit, hcoef, hA_fix_η t i μ, hA_scale_q t μ]
      calc
        η i μ + ((Real.exp (-t) : ℂ) * b i) *
            ((Real.exp t : ℂ) * q μ)
            = η i μ +
                ((Real.exp (-t) : ℂ) * (Real.exp t : ℂ)) *
                  (b i * q μ) := by
              ring
        _ = η i μ + b i * q μ := by
              rw [hexp]
              ring
    exact
      hA_eq ▸
        complexLorentzAction_mem_extendedTube n (A t)
          (forwardTube_subset_extendedTube htFT)

/-- One-null-vector coefficient freedom, forward representative version. -/
theorem hw_singleIsotropicResidual_allCoefficients_mem_extendedTube_of_forwardEndpoint
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → ℂ}
    {q : Fin (d + 1) → ℂ}
    (hξa : (fun i μ => ξ i μ + a i * q μ) ∈ ForwardTube d n)
    (hq_null : sourceComplexMinkowskiInner d q q = 0)
    (hq_orth :
      ∀ i, sourceComplexMinkowskiInner d q (ξ i) = 0) :
    ∀ b : Fin n → ℂ,
      (fun i μ => ξ i μ + b i * q μ) ∈ ExtendedTube d n := by
  rcases
    hw_secondRemark_forwardTube_singleNullResidual_normalForm
      (d := d) hd hξa hq_null hq_orth with
    ⟨η, β, hηFT, hnorm, hξ_eq⟩
  intro b
  have hη_coeff :
      (fun i μ => η i μ + (β i + b i) * q μ) ∈ ExtendedTube d n :=
    hw_thirdRemark_nullNormalForm_allCoefficients_mem_extendedTube
      (d := d) hηFT hnorm (fun i => β i + b i)
  simpa [hξ_eq, add_mul, add_comm, add_left_comm, add_assoc] using
    hη_coeff

/-- One-null-vector coefficient freedom for an arbitrary extended-tube
endpoint, obtained by transporting to a forward representative. -/
theorem hw_singleIsotropicResidual_allCoefficients_mem_extendedTube
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → ℂ}
    {q : Fin (d + 1) → ℂ}
    (hξa : (fun i μ => ξ i μ + a i * q μ) ∈ ExtendedTube d n)
    (hq_null : sourceComplexMinkowskiInner d q q = 0)
    (hq_orth :
      ∀ i, sourceComplexMinkowskiInner d q (ξ i) = 0) :
    ∀ b : Fin n → ℂ,
      (fun i μ => ξ i μ + b i * q μ) ∈ ExtendedTube d n := by
  intro b
  rcases Set.mem_iUnion.mp hξa with ⟨Λ, y, hyFT, hy_eq⟩
  let ξ0 : Fin n → Fin (d + 1) → ℂ :=
    complexLorentzAction Λ⁻¹ ξ
  let q0 : Fin (d + 1) → ℂ :=
    complexLorentzVectorAction Λ⁻¹ q
  have hξ_back : complexLorentzAction Λ ξ0 = ξ := by
    simpa [ξ0] using
      (complexLorentzAction_inv_left (d := d) (n := n) Λ ξ)
  have hq_back : complexLorentzVectorAction Λ q0 = q := by
    simpa [q0] using
      (complexLorentzVectorAction_inv_left (d := d) Λ q)
  have htransport_coeff :
      ∀ c : Fin n → ℂ,
        complexLorentzAction Λ
          (fun i μ => ξ0 i μ + c i * q0 μ) =
        (fun i μ => ξ i μ + c i * q μ) := by
    intro c
    calc
      complexLorentzAction Λ
          (fun i μ => ξ0 i μ + c i * q0 μ) =
        (fun i μ =>
          complexLorentzAction Λ ξ0 i μ +
            c i * complexLorentzVectorAction Λ q0 μ) := by
          rw [complexLorentzAction_add, complexLorentzAction_smul_vector]
      _ = (fun i μ => ξ i μ + c i * q μ) := by
        ext i μ
        have hξ_iμ := congrFun (congrFun hξ_back i) μ
        have hq_μ := congrFun hq_back μ
        rw [hξ_iμ, hq_μ]
  have hback_a :
      complexLorentzAction Λ
        (fun i μ => ξ0 i μ + a i * q0 μ) =
      (fun i μ => ξ i μ + a i * q μ) :=
    htransport_coeff a
  have hy_as_coeff :
      y = fun i μ => ξ0 i μ + a i * q0 μ := by
    apply complexLorentzAction_cancel_left (Λ := Λ)
    calc
      complexLorentzAction Λ y =
          (fun i μ => ξ i μ + a i * q μ) := hy_eq.symm
      _ = complexLorentzAction Λ
          (fun i μ => ξ0 i μ + a i * q0 μ) := hback_a.symm
  have hq0_null : sourceComplexMinkowskiInner d q0 q0 = 0 :=
    (sourceComplexMinkowskiInner_complexLorentzVectorAction
      (d := d) Λ⁻¹ q q).trans hq_null
  have hq0_orth :
      ∀ i, sourceComplexMinkowskiInner d q0 (ξ0 i) = 0 := by
    intro i
    simpa [ξ0, q0] using
      (sourceComplexMinkowskiInner_complexLorentzVectorAction
        (d := d) Λ⁻¹ q (ξ i)).trans (hq_orth i)
  have hforward_all :
      (fun i μ => ξ0 i μ + b i * q0 μ) ∈ ExtendedTube d n :=
    hw_singleIsotropicResidual_allCoefficients_mem_extendedTube_of_forwardEndpoint
      (d := d) hd
      (ξ := ξ0) (a := a) (q := q0)
      (by simpa [hy_as_coeff] using hyFT)
      hq0_null hq0_orth b
  have htransport :
      complexLorentzAction Λ
        (fun i μ => ξ0 i μ + b i * q0 μ) =
      (fun i μ => ξ i μ + b i * q μ) :=
    htransport_coeff b
  simpa [htransport] using
    complexLorentzAction_mem_extendedTube n Λ hforward_all

/-- Finite-frame coefficient freedom over an arbitrary finite subset of the
frame labels.  The frame vectors are pairwise isotropic and orthogonal to the
base tuple. -/
theorem hw_isotropicFrame_allCoefficients_mem_extendedTube_finset
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {m : ℕ}
    (S : Finset (Fin m))
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → Fin m → ℂ}
    {q : Fin m → Fin (d + 1) → ℂ}
    (hξa :
      (fun i => ξ i + ∑ c ∈ S, a i c • q c) ∈ ExtendedTube d n)
    (hq_pair :
      ∀ c ∈ S, ∀ c' ∈ S,
        sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth :
      ∀ c ∈ S, ∀ i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) :
    ∀ b : Fin n → Fin m → ℂ,
      (fun i => ξ i + ∑ c ∈ S, b i c • q c) ∈ ExtendedTube d n := by
  classical
  let P : Finset (Fin m) → Prop := fun T =>
    ∀ (ξ : Fin n → Fin (d + 1) → ℂ)
      (a : Fin n → Fin m → ℂ),
      (fun i => ξ i + ∑ c ∈ T, a i c • q c) ∈ ExtendedTube d n →
      (∀ c ∈ T, ∀ c' ∈ T,
        sourceComplexMinkowskiInner d (q c) (q c') = 0) →
      (∀ c ∈ T, ∀ i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) →
      ∀ b : Fin n → Fin m → ℂ,
        (fun i => ξ i + ∑ c ∈ T, b i c • q c) ∈ ExtendedTube d n
  have hP : P S := by
    refine Finset.induction_on S ?empty ?insert
    · intro ξ a hξa hq_pair hq_orth b
      simpa using hξa
    · intro c S hc ih ξ a hξa hq_pair hq_orth b
      let ξS : Fin n → Fin (d + 1) → ℂ :=
        fun i => ξ i + ∑ r ∈ S, a i r • q r
      have hc_mem : c ∈ insert c S := by simp
      have hstart :
          (fun i μ => ξS i μ + a i c * q c μ) ∈ ExtendedTube d n := by
        have hstart_eq :
            (fun i μ => ξS i μ + a i c * q c μ) =
            (fun i => ξ i + ∑ r ∈ insert c S, a i r • q r) := by
          ext i μ
          simp [ξS, Finset.sum_insert hc, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, add_comm, add_left_comm]
        rw [hstart_eq]
        exact hξa
      have hc_null : sourceComplexMinkowskiInner d (q c) (q c) = 0 :=
        hq_pair c hc_mem c hc_mem
      have hc_orth_ξS :
          ∀ i, sourceComplexMinkowskiInner d (q c) (ξS i) = 0 := by
        intro i
        have hsum_zero :
            (∑ r ∈ S,
              a i r * sourceComplexMinkowskiInner d (q c) (q r)) = 0 := by
          apply Finset.sum_eq_zero
          intro r hr
          have hr_mem : r ∈ insert c S := by simp [hr]
          simp [hq_pair c hc_mem r hr_mem]
        calc
          sourceComplexMinkowskiInner d (q c) (ξS i)
              =
            sourceComplexMinkowskiInner d (q c) (ξ i) +
              sourceComplexMinkowskiInner d (q c)
                (∑ r ∈ S, a i r • q r) := by
                simp [ξS, sourceComplexMinkowskiInner_add_right]
          _ =
            sourceComplexMinkowskiInner d (q c) (ξ i) +
              ∑ r ∈ S,
                a i r * sourceComplexMinkowskiInner d (q c) (q r) := by
                rw [sourceComplexMinkowskiInner_finset_sum_smul_right]
          _ = 0 := by
                rw [hq_orth c hc_mem i, hsum_zero]
                simp
      have hone :
          (fun i μ => ξS i μ + b i c * q c μ) ∈ ExtendedTube d n :=
        hw_singleIsotropicResidual_allCoefficients_mem_extendedTube
          (d := d) hd
          (ξ := ξS) (a := fun i => a i c) (q := q c)
          hstart hc_null hc_orth_ξS (fun i => b i c)
      let ξc : Fin n → Fin (d + 1) → ℂ :=
        fun i => ξ i + b i c • q c
      have hone_for_ih :
          (fun i => ξc i + ∑ r ∈ S, a i r • q r) ∈
            ExtendedTube d n := by
        have hone_eq :
            (fun i μ => ξS i μ + b i c * q c μ) =
            (fun i => ξc i + ∑ r ∈ S, a i r • q r) := by
          ext i μ
          simp [ξS, ξc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            add_assoc, add_comm, add_left_comm]
        rw [← hone_eq]
        exact hone
      have hpair_S :
          ∀ r ∈ S, ∀ r' ∈ S,
            sourceComplexMinkowskiInner d (q r) (q r') = 0 := by
        intro r hr r' hr'
        exact hq_pair r (by simp [hr]) r' (by simp [hr'])
      have horth_S :
          ∀ r ∈ S, ∀ i,
            sourceComplexMinkowskiInner d (q r) (ξc i) = 0 := by
        intro r hr i
        have hr_mem : r ∈ insert c S := by simp [hr]
        calc
          sourceComplexMinkowskiInner d (q r) (ξc i)
              =
            sourceComplexMinkowskiInner d (q r) (ξ i) +
              sourceComplexMinkowskiInner d (q r) (b i c • q c) := by
                simp [ξc, sourceComplexMinkowskiInner_add_right]
          _ =
            sourceComplexMinkowskiInner d (q r) (ξ i) +
              b i c * sourceComplexMinkowskiInner d (q r) (q c) := by
                rw [sourceComplexMinkowskiInner_smul_right]
          _ = 0 := by
                rw [hq_orth r hr_mem i, hq_pair r hr_mem c hc_mem]
                simp
      have hall_S :
          (fun i => ξc i + ∑ r ∈ S, b i r • q r) ∈
            ExtendedTube d n :=
        ih ξc a hone_for_ih hpair_S horth_S b
      simpa [ξc, Finset.sum_insert hc, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, add_assoc, add_comm, add_left_comm] using hall_S
  exact hP ξ a hξa hq_pair hq_orth

/-- Finite-frame coefficient freedom for a full indexed isotropic frame, in
the nonempty source-tuple case. -/
theorem hw_isotropicFrame_allCoefficients_mem_extendedTube_nonempty_coefficients
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {m : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → Fin m → ℂ}
    {q : Fin m → Fin (d + 1) → ℂ}
    (hξa :
      (fun i => ξ i + ∑ c, a i c • q c) ∈ ExtendedTube d n)
    (hq_pair :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth :
      ∀ c i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) :
    ∀ b : Fin n → Fin m → ℂ,
      (fun i => ξ i + ∑ c, b i c • q c) ∈ ExtendedTube d n := by
  classical
  intro b
  exact
    hw_isotropicFrame_allCoefficients_mem_extendedTube_finset
      (d := d) hd (S := (Finset.univ : Finset (Fin m)))
      (ξ := ξ) (a := a) (q := q)
      (by simpa using hξa)
      (by intro c _ c' _; exact hq_pair c c')
      (by intro c _ i; exact hq_orth c i)
      b

/-- Finite-frame coefficient freedom for a full indexed isotropic frame, in
the nonempty source-tuple case.  This form also records the zero-coefficient
base point. -/
theorem hw_isotropicFrame_allCoefficients_mem_extendedTube_nonempty
    [NeZero d] [NeZero n]
    (hd : 2 ≤ d)
    {m : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → Fin m → ℂ}
    {q : Fin m → Fin (d + 1) → ℂ}
    (hξa :
      (fun i => ξ i + ∑ c, a i c • q c) ∈ ExtendedTube d n)
    (hq_pair :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth :
      ∀ c i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) :
    ξ ∈ ExtendedTube d n ∧
    ∀ b : Fin n → Fin m → ℂ,
      (fun i => ξ i + ∑ c, b i c • q c) ∈ ExtendedTube d n := by
  have hall :=
    hw_isotropicFrame_allCoefficients_mem_extendedTube_nonempty_coefficients
      (d := d) hd (ξ := ξ) (a := a) (q := q)
      hξa hq_pair hq_orth
  constructor
  · simpa using hall (fun _ _ => 0)
  · exact hall

/-- Finite-frame coefficient freedom for a full indexed isotropic frame,
including the trivial empty source-tuple case. -/
theorem hw_isotropicFrame_allCoefficients_mem_extendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    {m : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → Fin m → ℂ}
    {q : Fin m → Fin (d + 1) → ℂ}
    (hξa :
      (fun i => ξ i + ∑ c, a i c • q c) ∈ ExtendedTube d n)
    (hq_pair :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth :
      ∀ c i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) :
    ξ ∈ ExtendedTube d n ∧
    ∀ b : Fin n → Fin m → ℂ,
      (fun i => ξ i + ∑ c, b i c • q c) ∈ ExtendedTube d n := by
  by_cases hn : n = 0
  · subst hn
    have hξ : ξ ∈ ExtendedTube d 0 := by
      simpa [Subsingleton.elim
        (fun i => ξ i + ∑ c, a i c • q c) ξ] using hξa
    constructor
    · exact hξ
    · intro b
      simpa [Subsingleton.elim
        (fun i => ξ i + ∑ c, b i c • q c) ξ] using hξ
  · haveI : NeZero n := ⟨hn⟩
    exact
      hw_isotropicFrame_allCoefficients_mem_extendedTube_nonempty
        (d := d) hd hξa hq_pair hq_orth

/-- The zero-coefficient base point is in the extended tube whenever one
coefficient choice along a finite isotropic frame is. -/
theorem hw_isotropicFrame_base_mem_extendedTube_of_endpoint
    [NeZero d]
    (hd : 2 ≤ d)
    {m : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {a : Fin n → Fin m → ℂ}
    {q : Fin m → Fin (d + 1) → ℂ}
    (hξa :
      (fun i => ξ i + ∑ c, a i c • q c) ∈ ExtendedTube d n)
    (hq_pair :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth :
      ∀ c i,
        sourceComplexMinkowskiInner d (q c) (ξ i) = 0) :
    ξ ∈ ExtendedTube d n :=
  (hw_isotropicFrame_allCoefficients_mem_extendedTube
    (d := d) hd hξa hq_pair hq_orth).1

end BHW
