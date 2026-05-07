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

end BHW
