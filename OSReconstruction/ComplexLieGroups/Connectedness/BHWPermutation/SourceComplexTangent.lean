import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRegularRank

/-!
# Complex tangent support for the source Gram variety

This companion file continues the Hall-Wightman source-geometry packet after
the real regular-rank and local-chart support in `SourceRegularRank.lean`.
It starts with the tangent inclusions that are immediate from real
complexification; the remaining same-Gram complex tangent-range theorem is the
next hard finite-dimensional selected-coordinate step.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Complex bilinear Minkowski pairing on the source spacetime. -/
def sourceComplexMinkowskiInner
    (d : ℕ) (u v : Fin (d + 1) → ℂ) : ℂ :=
  ∑ μ : Fin (d + 1),
    (MinkowskiSpace.metricSignature d μ : ℂ) * u μ * v μ

/-- Each complex source Gram entry is the complex Minkowski pairing of the
corresponding rows. -/
theorem sourceMinkowskiGram_apply_eq_complexInner
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (i j : Fin n) :
    sourceMinkowskiGram d n z i j =
      sourceComplexMinkowskiInner d (z i) (z j) :=
  rfl

/-- Symmetry of the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_comm
    (d : ℕ) (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u v =
      sourceComplexMinkowskiInner d v u := by
  unfold sourceComplexMinkowskiInner
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Left scalar linearity of the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_smul_left
    (d : ℕ) (c : ℂ)
    (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d (c • u) v =
      c * sourceComplexMinkowskiInner d u v := by
  unfold sourceComplexMinkowskiInner
  calc
    (∑ μ : Fin (d + 1),
        (MinkowskiSpace.metricSignature d μ : ℂ) * (c • u) μ * v μ)
        = ∑ μ : Fin (d + 1),
            c * ((MinkowskiSpace.metricSignature d μ : ℂ) * u μ * v μ) := by
          apply Finset.sum_congr rfl
          intro μ _
          simp [Pi.smul_apply, smul_eq_mul]
          ring
    _ = c * ∑ μ : Fin (d + 1),
          (MinkowskiSpace.metricSignature d μ : ℂ) * u μ * v μ := by
          rw [Finset.mul_sum]

/-- Right additivity of the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_add_right
    (d : ℕ)
    (u v w : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u (v + w) =
      sourceComplexMinkowskiInner d u v +
        sourceComplexMinkowskiInner d u w := by
  unfold sourceComplexMinkowskiInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  simp [Pi.add_apply]
  ring

/-- Left additivity of the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_add_left
    (d : ℕ)
    (u v w : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d (u + v) w =
      sourceComplexMinkowskiInner d u w +
        sourceComplexMinkowskiInner d v w := by
  rw [sourceComplexMinkowskiInner_comm d (u + v) w]
  rw [sourceComplexMinkowskiInner_add_right d w u v]
  rw [sourceComplexMinkowskiInner_comm d w u]
  rw [sourceComplexMinkowskiInner_comm d w v]

/-- Right scalar linearity of the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_smul_right
    (d : ℕ) (c : ℂ)
    (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u (c • v) =
      c * sourceComplexMinkowskiInner d u v := by
  rw [sourceComplexMinkowskiInner_comm d u (c • v)]
  rw [sourceComplexMinkowskiInner_smul_left d c v u]
  rw [sourceComplexMinkowskiInner_comm d v u]

/-- Linearity of the complex source Minkowski pairing in finite sums on the
left. -/
theorem sourceComplexMinkowskiInner_sum_smul_left
    (d m : ℕ)
    (coeff : Fin m → ℂ)
    (u : Fin m → Fin (d + 1) → ℂ)
    (v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d
      (∑ a : Fin m, coeff a • u a) v =
      ∑ a : Fin m, coeff a *
        sourceComplexMinkowskiInner d (u a) v := by
  let L : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun w => sourceComplexMinkowskiInner d w v
    map_add' := by
      intro p q
      exact sourceComplexMinkowskiInner_add_left d p q v
    map_smul' := by
      intro c p
      exact sourceComplexMinkowskiInner_smul_left d c p v }
  calc
    sourceComplexMinkowskiInner d
        (∑ a : Fin m, coeff a • u a) v
        = ∑ a : Fin m,
            sourceComplexMinkowskiInner d (coeff a • u a) v := by
          change L (∑ a : Fin m, coeff a • u a) =
            ∑ a : Fin m, L (coeff a • u a)
          rw [map_sum]
    _ = ∑ a : Fin m, coeff a *
          sourceComplexMinkowskiInner d (u a) v := by
          apply Finset.sum_congr rfl
          intro a _
          change L (coeff a • u a) =
            coeff a * sourceComplexMinkowskiInner d (u a) v
          rw [L.map_smul]
          change coeff a • sourceComplexMinkowskiInner d (u a) v =
            coeff a * sourceComplexMinkowskiInner d (u a) v
          simp [smul_eq_mul]

/-- Linearity of the complex source Minkowski pairing in finite sums on the
right. -/
theorem sourceComplexMinkowskiInner_sum_smul_right
    (d m : ℕ)
    (u : Fin (d + 1) → ℂ)
    (coeff : Fin m → ℂ)
    (v : Fin m → Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u
      (∑ a : Fin m, coeff a • v a) =
      ∑ a : Fin m, coeff a *
        sourceComplexMinkowskiInner d u (v a) := by
  rw [sourceComplexMinkowskiInner_comm d u (∑ a : Fin m, coeff a • v a)]
  rw [sourceComplexMinkowskiInner_sum_smul_left d m coeff v u]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceComplexMinkowskiInner_comm d (v a) u]

/-- Left subtraction for the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_sub_left
    (d : ℕ)
    (u v w : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d (u - v) w =
      sourceComplexMinkowskiInner d u w -
        sourceComplexMinkowskiInner d v w := by
  unfold sourceComplexMinkowskiInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  simp [Pi.sub_apply]
  ring

/-- Right subtraction for the complex source Minkowski pairing. -/
theorem sourceComplexMinkowskiInner_sub_right
    (d : ℕ)
    (u v w : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u (v - w) =
      sourceComplexMinkowskiInner d u v -
        sourceComplexMinkowskiInner d u w := by
  rw [sourceComplexMinkowskiInner_comm d u (v - w)]
  rw [sourceComplexMinkowskiInner_sub_left d v w u]
  rw [sourceComplexMinkowskiInner_comm d v u]
  rw [sourceComplexMinkowskiInner_comm d w u]

/-- The complex Gram differential is the sum of the two complex Minkowski
pairings obtained by differentiating each argument. -/
theorem sourceComplexGramDifferential_apply_eq_complexInner
    (d n : ℕ)
    (z h : Fin n → Fin (d + 1) → ℂ)
    (i j : Fin n) :
    sourceComplexGramDifferential d n z h i j =
      sourceComplexMinkowskiInner d (h i) (z j) +
        sourceComplexMinkowskiInner d (z i) (h j) := by
  change (∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        (h i μ * z j μ + z i μ * h j μ)) =
    sourceComplexMinkowskiInner d (h i) (z j) +
      sourceComplexMinkowskiInner d (z i) (h j)
  unfold sourceComplexMinkowskiInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The complex source Gram differential is symmetric in its matrix indices. -/
theorem sourceComplexGramDifferential_symm
    (d n : ℕ)
    (z h : Fin n → Fin (d + 1) → ℂ)
    (i j : Fin n) :
    sourceComplexGramDifferential d n z h i j =
      sourceComplexGramDifferential d n z h j i := by
  rw [sourceComplexGramDifferential_apply_eq_complexInner]
  rw [sourceComplexGramDifferential_apply_eq_complexInner]
  rw [sourceComplexMinkowskiInner_comm d (h i) (z j)]
  rw [sourceComplexMinkowskiInner_comm d (z i) (h j)]
  ring

/-- Projection from a full complex Gram variation to pairings with a selected
family of source rows. -/
def sourceSelectedComplexGramCoord
    (n m : ℕ) (I : Fin m → Fin n) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin m → ℂ) where
  toFun := fun δ i a => δ i (I a)
  map_add' := by
    intro δ ε
    ext i a
    rfl
  map_smul' := by
    intro c δ
    ext i a
    rfl

@[simp]
theorem sourceSelectedComplexGramCoord_apply
    (n m : ℕ) (I : Fin m → Fin n)
    (δ : Fin n → Fin n → ℂ)
    (i : Fin n) (a : Fin m) :
    sourceSelectedComplexGramCoord n m I δ i a = δ i (I a) :=
  rfl

/-- A nonzero real selected minor makes the corresponding real-embedded
selected source rows complex-linearly independent. -/
theorem linearIndependent_complex_realEmbed_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) =>
        realEmbed (d := d) (n := n) x (I a)) := by
  let m := min n (d + 1)
  let restrictJ : (Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin m → ℂ) := {
    toFun := fun v b => v (J b)
    map_add' := by
      intro v w
      ext b
      simp
    map_smul' := by
      intro c v
      ext b
      simp }
  have hdet_real :
      (Matrix.of fun a b : Fin m => x (I a) (J b)).det ≠ 0 := by
    simpa [sourceRegularMinor, m] using hminor
  have hdetC :
      (Matrix.of fun a b : Fin m => (x (I a) (J b) : ℂ)).det ≠ 0 := by
    let M : Matrix (Fin m) (Fin m) ℝ :=
      Matrix.of fun a b => x (I a) (J b)
    have hmatrix : Complex.ofRealHom.mapMatrix M =
        (Matrix.of fun a b : Fin m => (x (I a) (J b) : ℂ)) := by
      ext a b
      rfl
    rw [← hmatrix]
    have hmap := RingHom.map_det Complex.ofRealHom M
    rw [← hmap]
    have hM : M.det ≠ 0 := by
      simpa [M] using hdet_real
    exact (Complex.ofReal_ne_zero).2 hM
  have hrowsC : LinearIndependent ℂ
      (fun a : Fin m => fun b : Fin m => (x (I a) (J b) : ℂ)) := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetC
  apply LinearIndependent.of_comp restrictJ
  simpa [Function.comp_def, restrictJ, realEmbed, m] using hrowsC

/-- In the full-spacetime case, a nonzero real selected minor makes the
real-embedded selected rows span the whole complex source spacetime. -/
theorem sourceComplexRealEmbedSelectedRows_span_top_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0)
    (hD : d + 1 ≤ n) :
    Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) =>
          realEmbed (d := d) (n := n) x (I a))) = ⊤ := by
  have hli :=
    linearIndependent_complex_realEmbed_sourceRows_of_sourceRegularMinor_ne_zero
      d n hminor
  have hcard :
      Fintype.card (Fin (min n (d + 1))) =
        Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    simp [Nat.min_eq_right hD]
  exact hli.span_eq_top_of_card_eq_finrank' hcard

/-- The standard complex coordinate basis vector in source spacetime. -/
def sourceComplexStdBasisVector
    (d : ℕ) (μ : Fin (d + 1)) : Fin (d + 1) → ℂ :=
  Pi.single (M := fun _ : Fin (d + 1) => ℂ) μ (1 : ℂ)

/-- The complex source Minkowski pairing is nondegenerate in the left
argument. -/
theorem sourceComplexMinkowskiInner_left_nonDegenerate
    (d : ℕ) {w : Fin (d + 1) → ℂ}
    (horth :
      ∀ v : Fin (d + 1) → ℂ,
        sourceComplexMinkowskiInner d w v = 0) :
    w = 0 := by
  ext μ
  have hμ := horth (sourceComplexStdBasisVector d μ)
  have hsig_ne : (MinkowskiSpace.metricSignature d μ : ℂ) ≠ 0 := by
    by_cases h0 : μ = 0
    · simp [MinkowskiSpace.metricSignature, h0]
    · simp [MinkowskiSpace.metricSignature, h0]
  have hmul : (MinkowskiSpace.metricSignature d μ : ℂ) * w μ = 0 := by
    simpa [sourceComplexMinkowskiInner, sourceComplexStdBasisVector,
      Pi.single_apply, mul_comm, mul_left_comm, mul_assoc] using hμ
  exact (mul_eq_zero.mp hmul).resolve_left hsig_ne

/-- A complex vector orthogonal to a spanning selected family is zero. -/
theorem sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
    (d m : ℕ)
    {e : Fin m → Fin (d + 1) → ℂ}
    (hspan : Submodule.span ℂ (Set.range e) = ⊤)
    {w : Fin (d + 1) → ℂ}
    (horth :
      ∀ a : Fin m,
        sourceComplexMinkowskiInner d w (e a) = 0) :
    w = 0 := by
  apply sourceComplexMinkowskiInner_left_nonDegenerate d
  intro v
  let L : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun u => sourceComplexMinkowskiInner d w u
    map_add' := by
      intro u v
      exact sourceComplexMinkowskiInner_add_right d w u v
    map_smul' := by
      intro c u
      exact sourceComplexMinkowskiInner_smul_right d c w u }
  change L v = 0
  have hv : v ∈ Submodule.span ℂ (Set.range e) := by
    rw [hspan]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro u ⟨a, rfl⟩
    exact horth a
  · unfold L sourceComplexMinkowskiInner
    simp
  · intro u v _ _ hu hv
    simp [map_add, hu, hv]
  · intro c u _ hu
    simp [map_smul, hu]

/-- In the full-spacetime case, equality of complex Gram matrices with a
regular real source point transfers full span to the selected rows of the
arbitrary complex realization. -/
theorem sourceComplexRows_span_top_of_sameGram_real_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hzG :
      sourceMinkowskiGram d n z =
        sourceRealGramComplexify n (sourceRealMinkowskiGram d n x))
    (hD : d + 1 ≤ n) :
    Submodule.span ℂ
      (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) = ⊤ := by
  let m := min n (d + 1)
  have hspan_x : Submodule.span ℂ
      (Set.range (fun a : Fin m =>
        realEmbed (d := d) (n := n) x (I a))) = ⊤ := by
    simpa [m] using
      sourceComplexRealEmbedSelectedRows_span_top_of_sourceRegularMinor_ne_zero
        d n hminor_x hD
  have hli_x : LinearIndependent ℂ
      (fun a : Fin m => realEmbed (d := d) (n := n) x (I a)) := by
    simpa [m] using
      linearIndependent_complex_realEmbed_sourceRows_of_sourceRegularMinor_ne_zero
        d n hminor_x
  have hli_z : LinearIndependent ℂ (fun a : Fin m => z (I a)) := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hsum a
    have hxcombo_zero :
        (∑ c : Fin m,
          coeff c • realEmbed (d := d) (n := n) x (I c)) = 0 := by
      apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m hspan_x
      intro b
      have hzorth :
          sourceComplexMinkowskiInner d
            (∑ c : Fin m, coeff c • z (I c)) (z (I b)) = 0 := by
        rw [hsum]
        unfold sourceComplexMinkowskiInner
        simp
      calc
        sourceComplexMinkowskiInner d
            (∑ c : Fin m,
              coeff c • realEmbed (d := d) (n := n) x (I c))
            (realEmbed (d := d) (n := n) x (I b))
            = ∑ c : Fin m,
                coeff c *
                  sourceComplexMinkowskiInner d
                    (realEmbed (d := d) (n := n) x (I c))
                    (realEmbed (d := d) (n := n) x (I b)) := by
              rw [sourceComplexMinkowskiInner_sum_smul_left]
        _ = ∑ c : Fin m,
                coeff c *
                  sourceComplexMinkowskiInner d (z (I c)) (z (I b)) := by
              apply Finset.sum_congr rfl
              intro c _
              have h := congrFun (congrFun hzG (I c)) (I b)
              change sourceMinkowskiGram d n z (I c) (I b) =
                sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
                  (I c) (I b) at h
              have hx :
                  sourceComplexMinkowskiInner d
                    (realEmbed (d := d) (n := n) x (I c))
                    (realEmbed (d := d) (n := n) x (I b)) =
                  sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
                    (I c) (I b) := by
                simpa [sourceMinkowskiGram_apply_eq_complexInner] using
                  congrFun (congrFun
                    (sourceMinkowskiGram_realEmbed d n x) (I c)) (I b)
              rw [hx, ← h]
              rfl
        _ = sourceComplexMinkowskiInner d
            (∑ c : Fin m, coeff c • z (I c)) (z (I b)) := by
              rw [sourceComplexMinkowskiInner_sum_smul_left]
        _ = 0 := hzorth
    exact (Fintype.linearIndependent_iff.mp hli_x coeff hxcombo_zero) a
  have hcard :
      Fintype.card (Fin m) =
        Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    simp [m, Nat.min_eq_right hD]
  exact hli_z.span_eq_top_of_card_eq_finrank' hcard

/-- If a complex realization has the same Gram matrix as a regular real source
point, then the real selected-row coefficients also expand the complex rows. -/
theorem sourceComplexRows_eq_real_coefficients_of_sameGram_real_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hzspan :
      Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) = ⊤)
    (hzG :
      sourceMinkowskiGram d n z =
        sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)) :
    ∃ c : Fin n → Fin (min n (d + 1)) → ℂ,
      (∀ r,
        realEmbed (d := d) (n := n) x r =
          ∑ a : Fin (min n (d + 1)),
            c r a • realEmbed (d := d) (n := n) x (I a)) ∧
      (∀ r,
        z r = ∑ a : Fin (min n (d + 1)), c r a • z (I a)) := by
  let m := min n (d + 1)
  rcases sourceRows_coefficients_of_sourceRegularMinor_ne_zero d n
      hminor_x with
    ⟨cR, hcR⟩
  let c : Fin n → Fin m → ℂ := fun r a => (cR r a : ℂ)
  have hx_expand : ∀ r : Fin n,
      realEmbed (d := d) (n := n) x r =
        ∑ a : Fin m, c r a • realEmbed (d := d) (n := n) x (I a) := by
    intro r
    ext μ
    have h :=
      congrArg (fun v : Fin (d + 1) → ℝ => ((v μ : ℝ) : ℂ)) (hcR r)
    simpa [realEmbed, c, Pi.smul_apply, smul_eq_mul] using h
  have hz_expand : ∀ r : Fin n,
      z r = ∑ a : Fin m, c r a • z (I a) := by
    intro r
    let zApprox : Fin (d + 1) → ℂ := ∑ a : Fin m, c r a • z (I a)
    have hzero : z r - zApprox = 0 := by
      apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m
      · simpa [m] using hzspan
      intro b
      have hz_pair :
          sourceComplexMinkowskiInner d (z r) (z (I b)) =
            sourceComplexMinkowskiInner d
              (realEmbed (d := d) (n := n) x r)
              (realEmbed (d := d) (n := n) x (I b)) := by
        have h := congrFun (congrFun hzG r) (I b)
        change sourceMinkowskiGram d n z r (I b) =
          sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
            r (I b) at h
        have hx :
            sourceComplexMinkowskiInner d
              (realEmbed (d := d) (n := n) x r)
              (realEmbed (d := d) (n := n) x (I b)) =
            sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
              r (I b) := by
          simpa [sourceMinkowskiGram_apply_eq_complexInner] using
            congrFun (congrFun (sourceMinkowskiGram_realEmbed d n x) r) (I b)
        rw [hx, ← h]
        rfl
      have hzApprox_pair :
          sourceComplexMinkowskiInner d zApprox (z (I b)) =
            sourceComplexMinkowskiInner d
              (realEmbed (d := d) (n := n) x r)
              (realEmbed (d := d) (n := n) x (I b)) := by
        have hzApprox_expand :
            sourceComplexMinkowskiInner d zApprox (z (I b)) =
              ∑ a : Fin m,
                c r a *
                  sourceComplexMinkowskiInner d (z (I a)) (z (I b)) := by
          unfold zApprox
          rw [sourceComplexMinkowskiInner_sum_smul_left]
        have hx_pair_expand :
            sourceComplexMinkowskiInner d
                (realEmbed (d := d) (n := n) x r)
                (realEmbed (d := d) (n := n) x (I b)) =
              ∑ a : Fin m,
                c r a *
                  sourceComplexMinkowskiInner d
                    (realEmbed (d := d) (n := n) x (I a))
                    (realEmbed (d := d) (n := n) x (I b)) := by
          rw [hx_expand r]
          rw [sourceComplexMinkowskiInner_sum_smul_left]
        have hblock : ∀ a : Fin m,
            sourceComplexMinkowskiInner d (z (I a)) (z (I b)) =
              sourceComplexMinkowskiInner d
                (realEmbed (d := d) (n := n) x (I a))
                (realEmbed (d := d) (n := n) x (I b)) := by
          intro a
          have h := congrFun (congrFun hzG (I a)) (I b)
          change sourceMinkowskiGram d n z (I a) (I b) =
            sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
              (I a) (I b) at h
          have hx :
              sourceComplexMinkowskiInner d
                (realEmbed (d := d) (n := n) x (I a))
                (realEmbed (d := d) (n := n) x (I b)) =
              sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)
                (I a) (I b) := by
            simpa [sourceMinkowskiGram_apply_eq_complexInner] using
              congrFun (congrFun
                (sourceMinkowskiGram_realEmbed d n x) (I a)) (I b)
          rw [hx, ← h]
          rfl
        rw [hzApprox_expand, hx_pair_expand]
        apply Finset.sum_congr rfl
        intro a _
        rw [hblock a]
      rw [sourceComplexMinkowskiInner_sub_left, hz_pair, hzApprox_pair]
      ring
    exact sub_eq_zero.mp hzero
  exact ⟨c, by simpa [m] using hx_expand, by simpa [m] using hz_expand⟩

/-- The complex Gram differential is determined by its selected columns once the
source rows are expanded in the selected row family. -/
theorem sourceComplexGramDifferential_selected_formula
    (d n m : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {h : Fin n → Fin (d + 1) → ℂ}
    {I : Fin m → Fin n}
    {c : Fin n → Fin m → ℂ}
    (hzexpand : ∀ r, z r = ∑ a : Fin m, c r a • z (I a)) :
    ∀ r s,
      sourceComplexGramDifferential d n z h r s =
        (∑ a : Fin m, c s a *
          sourceComplexGramDifferential d n z h r (I a)) +
        (∑ a : Fin m, c r a *
          sourceComplexGramDifferential d n z h s (I a)) -
        (∑ a : Fin m, ∑ b : Fin m, c r a * c s b *
          sourceComplexGramDifferential d n z h (I a) (I b)) := by
  intro r s
  have hdouble :
      (∑ x : Fin m, ∑ y : Fin m,
          c r x * c s y *
            sourceComplexMinkowskiInner d (z (I x)) (h (I y))) =
        (∑ y : Fin m, ∑ x : Fin m,
          c s y * c r x *
            sourceComplexMinkowskiInner d (h (I y)) (z (I x))) := by
    calc
      (∑ x : Fin m, ∑ y : Fin m,
          c r x * c s y *
            sourceComplexMinkowskiInner d (z (I x)) (h (I y)))
          =
        ∑ x : Fin m, ∑ y : Fin m,
          c r x * c s y *
            sourceComplexMinkowskiInner d (h (I y)) (z (I x)) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [sourceComplexMinkowskiInner_comm]
      _ = ∑ y : Fin m, ∑ x : Fin m,
          c r x * c s y *
            sourceComplexMinkowskiInner d (h (I y)) (z (I x)) := by
            rw [Finset.sum_comm]
      _ = ∑ y : Fin m, ∑ x : Fin m,
          c s y * c r x *
            sourceComplexMinkowskiInner d (h (I y)) (z (I x)) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            ring
  simp [sourceComplexGramDifferential_apply_eq_complexInner,
    sourceComplexMinkowskiInner_sum_smul_right,
    sourceComplexMinkowskiInner_comm,
    hzexpand r, hzexpand s, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [hdouble]
  ring_nf

/-- For two complex realizations with the same selected-row expansion
coefficients, equality of selected differential coordinates forces equality of
the full complex Gram differentials. -/
theorem sourceComplexGramDifferential_eq_of_sameGram_real_regular_of_selected_eq
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {z : Fin n → Fin (d + 1) → ℂ}
    {kx hz : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hzG :
      sourceMinkowskiGram d n z =
        sourceRealGramComplexify n (sourceRealMinkowskiGram d n x))
    (hsel :
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceComplexGramDifferential d n (realEmbed x) kx) =
        sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceComplexGramDifferential d n z hz)) :
    sourceComplexGramDifferential d n (realEmbed x) kx =
      sourceComplexGramDifferential d n z hz := by
  ext r s
  by_cases hn : n ≤ d + 1
  · have hsurj := sourceSelectedIndex_surjective_of_le d n hI hn
    rcases hsurj s with ⟨a, rfl⟩
    have h := congrFun (congrFun hsel r) a
    simpa [sourceSelectedComplexGramCoord_apply] using h
  · have hD : d + 1 ≤ n := by omega
    let m := min n (d + 1)
    have hzspan :
        Submodule.span ℂ
          (Set.range (fun a : Fin m => z (I a))) = ⊤ := by
      simpa [m] using
        sourceComplexRows_span_top_of_sameGram_real_regular
          d n hminor_x hzG hD
    rcases sourceComplexRows_eq_real_coefficients_of_sameGram_real_regular
        d n hminor_x hzspan hzG with
      ⟨c, hxexpand, hzexpand⟩
    have hsel_entry :
        ∀ i : Fin n, ∀ a : Fin m,
          sourceComplexGramDifferential d n (realEmbed x) kx i (I a) =
            sourceComplexGramDifferential d n z hz i (I a) := by
      intro i a
      have h := congrFun (congrFun hsel i) a
      simpa [sourceSelectedComplexGramCoord_apply, m] using h
    have hxform :=
      sourceComplexGramDifferential_selected_formula
        d n m (z := realEmbed x) (h := kx) (I := I) (c := c) hxexpand r s
    have hzform :=
      sourceComplexGramDifferential_selected_formula
        d n m (z := z) (h := hz) (I := I) (c := c) hzexpand r s
    rw [hxform, hzform]
    simp [hsel_entry]

/-- At a real nonzero-minor point, the complex selected-coordinate differential
is surjective onto the symmetric selected-coordinate data. -/
theorem sourceSelectedComplexGramDifferential_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x ≠ 0)
    {A : Fin n → Fin (min n (d + 1)) → ℂ}
    (hA : ∀ a b : Fin (min n (d + 1)), A (I a) b = A (I b) a) :
    ∃ k : Fin n → Fin (d + 1) → ℂ,
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceComplexGramDifferential d n (realEmbed x) k) = A := by
  let m := min n (d + 1)
  let Are : sourceSelectedSymCoordSubspace n m I :=
    ⟨fun i a => (A i a).re, by
      intro a b
      exact congrArg Complex.re (hA a b)⟩
  let Aim : sourceSelectedSymCoordSubspace n m I :=
    ⟨fun i a => (A i a).im, by
      intro a b
      exact congrArg Complex.im (hA a b)⟩
  have hsurj :=
    sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
      d n hI hJ hminor
  rcases hsurj Are with ⟨hre, hhre⟩
  rcases hsurj Aim with ⟨him, hhim⟩
  have hre_entry :
      ∀ i : Fin n, ∀ a : Fin m,
        sourceRealGramDifferential d n x hre i (I a) = (A i a).re := by
    intro i a
    have h :=
      congrArg
        (fun B : sourceSelectedSymCoordSubspace n m I =>
          (B : Fin n → Fin m → ℝ) i a) hhre
    simpa [sourceSelectedGramDifferentialToSym_apply, Are] using h
  have him_entry :
      ∀ i : Fin n, ∀ a : Fin m,
        sourceRealGramDifferential d n x him i (I a) = (A i a).im := by
    intro i a
    have h :=
      congrArg
        (fun B : sourceSelectedSymCoordSubspace n m I =>
          (B : Fin n → Fin m → ℝ) i a) hhim
    simpa [sourceSelectedGramDifferentialToSym_apply, Aim] using h
  refine ⟨realEmbed hre + Complex.I • realEmbed him, ?_⟩
  ext i a
  change
    sourceComplexGramDifferential d n (realEmbed x)
        (realEmbed hre + Complex.I • realEmbed him) i (I a) =
      A i a
  rw [map_add, map_smul]
  rw [sourceComplexGramDifferential_realEmbed]
  rw [sourceComplexGramDifferential_realEmbed]
  simp [sourceRealGramComplexify, hre_entry i a, him_entry i a,
    Complex.ext_iff]

/-- At a regular real source point, every complex tangent vector over the
complexified real Gram matrix is realized by the complex Gram differential at
the real embedding. -/
theorem sourceComplexGramTangent_subset_realEmbed_range_of_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    sourceComplexGramTangentSpaceAt d n
        (sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)) ⊆
      LinearMap.range (sourceComplexGramDifferential d n (realEmbed x)) := by
  rintro δ ⟨z, _hzreg, hzG, hzrange⟩
  rcases hzrange with ⟨hzvar, rfl⟩
  rcases exists_nonzero_minor_of_sourceGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  let m := min n (d + 1)
  let A : Fin n → Fin m → ℂ :=
    sourceSelectedComplexGramCoord n m I
      (sourceComplexGramDifferential d n z hzvar)
  have hA : ∀ a b : Fin m, A (I a) b = A (I b) a := by
    intro a b
    simp [A, sourceSelectedComplexGramCoord_apply,
      sourceComplexGramDifferential_symm d n z hzvar (I a) (I b)]
  rcases
      sourceSelectedComplexGramDifferential_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor hA with
    ⟨kx, hkx⟩
  refine ⟨kx, ?_⟩
  exact
    sourceComplexGramDifferential_eq_of_sameGram_real_regular_of_selected_eq
      d n hI hminor hzG (by simpa [A, m] using hkx)

/-- Complexifying a real source tangent vector gives a complex source tangent
vector at the complexified real Gram matrix. -/
theorem sourceRealGramTangent_complexify_subset_complexTangent
    (d n : ℕ)
    (G : Fin n → Fin n → ℝ) :
    sourceRealGramComplexify n '' sourceRealGramTangentSpaceAt d n G ⊆
      sourceComplexGramTangentSpaceAt d n (sourceRealGramComplexify n G) := by
  rintro δC ⟨δR, hδR, rfl⟩
  rcases hδR with ⟨x, hxreg, hxG, hδR⟩
  rcases hδR with ⟨h, rfl⟩
  refine ⟨realEmbed x, sourceComplex_regular_of_real_regular d n hxreg, ?_, ?_⟩
  · rw [sourceMinkowskiGram_realEmbed, hxG]
  · refine ⟨realEmbed h, ?_⟩
    rw [sourceComplexGramDifferential_realEmbed]

/-- The complex span of the real source tangent is contained in the complex
source tangent span. -/
theorem sourceRealGramTangent_complexified_span_le_complexTangent_span
    (d n : ℕ)
    (G : Fin n → Fin n → ℝ) :
    Submodule.span ℂ
        (sourceRealGramComplexify n '' sourceRealGramTangentSpaceAt d n G) ≤
      Submodule.span ℂ
        (sourceComplexGramTangentSpaceAt d n
          (sourceRealGramComplexify n G)) :=
  Submodule.span_mono
    (sourceRealGramTangent_complexify_subset_complexTangent d n G)

/-- At a regular real source point, the complex Gram differential range at its
real embedding is contained in the complexified real tangent span. -/
theorem sourceComplexGramDifferential_realEmbed_range_le_complexified_real_tangent_span_of_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    LinearMap.range
        (sourceComplexGramDifferential d n (realEmbed x)) ≤
      Submodule.span ℂ
        (sourceRealGramComplexify n ''
          sourceRealGramTangentSpaceAt d n
            (sourceRealMinkowskiGram d n x)) := by
  rw [sourceComplexGramDifferential_realEmbed_range_eq_complex_span]
  apply Submodule.span_le.mpr
  rintro δC ⟨δR, hδR, rfl⟩
  rcases hδR with ⟨h, rfl⟩
  exact Submodule.subset_span
    ⟨(sourceRealGramDifferential d n x) h,
      ⟨x, hreg, rfl, ⟨h, rfl⟩⟩, rfl⟩

/-- At a regular real source point, the complexified real tangent span equals the
complex tangent span of the Hall-Wightman scalar-product variety. -/
theorem sourceComplexifiedRealTangentEqualsComplexTangent_of_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    SourceComplexifiedRealTangentEqualsComplexTangent d n
      (sourceRealMinkowskiGram d n x) := by
  unfold SourceComplexifiedRealTangentEqualsComplexTangent
  apply le_antisymm
  · exact sourceRealGramTangent_complexified_span_le_complexTangent_span
      d n (sourceRealMinkowskiGram d n x)
  · apply Submodule.span_le.mpr
    intro δ hδ
    have hrange :
        δ ∈ LinearMap.range
          (sourceComplexGramDifferential d n (realEmbed x)) :=
      sourceComplexGramTangent_subset_realEmbed_range_of_regular d n hreg hδ
    exact
      sourceComplexGramDifferential_realEmbed_range_le_complexified_real_tangent_span_of_regular
        d n hreg hrange

/-- A small source neighborhood of a regular Jost point supplies a
Hall-Wightman real environment in scalar-product coordinates. -/
theorem sourceRealGramMap_realEnvironmentAt_of_regular
    {d : ℕ} [NeZero d]
    (n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x0)
    (hx0_jost : x0 ∈ JostSet d n)
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V)
    (hx0V : x0 ∈ V) :
    ∃ O : Set (Fin n → Fin n → ℝ),
      O ⊆ sourceRealMinkowskiGram d n '' V ∧
      IsHWRealEnvironment d n O := by
  let W : Set (Fin n → Fin (d + 1) → ℝ) := V ∩ JostSet d n
  have hW_open : IsOpen W := hV_open.inter isOpen_jostSet
  have hx0W : x0 ∈ W := ⟨hx0V, hx0_jost⟩
  rcases sourceRealGramMap_localRelOpenImage_in_open_of_regular
      d n hreg hW_open hx0W with
    ⟨U, _hUopen, _hx0U, hUW, O, hbaseO, hOrel, hOsubset, hOreal⟩
  have hOsubsetV : O ⊆ sourceRealMinkowskiGram d n '' V := by
    intro G hG
    rcases hOsubset hG with ⟨x, hxU, hGram⟩
    exact ⟨x, (hUW hxU).1, hGram⟩
  refine ⟨O, hOsubsetV, ?_⟩
  refine
    { nonempty := ⟨sourceRealMinkowskiGram d n x0, hbaseO⟩
      relOpen := hOrel
      realized_by_jost := ?_
      maximal_totally_real := ?_ }
  · intro G hG
    rcases hOreal G hG with ⟨x, hxU, hregx, hGram⟩
    exact ⟨x, (hUW hxU).2, hregx, hGram⟩
  · intro G hG
    rcases hOreal G hG with ⟨x, _hxU, hregx, hGram⟩
    simpa [hGram] using
      sourceComplexifiedRealTangentEqualsComplexTangent_of_regular
        d n hregx

end BHW
