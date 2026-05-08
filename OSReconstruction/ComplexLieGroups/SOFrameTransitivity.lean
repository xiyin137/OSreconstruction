import OSReconstruction.ComplexLieGroups.SOConnected

/-!
# SOComplex frame-transitivity support

This file contains the finite-dimensional row/column algebra used by the
signed-frame induction behind the determinant-one Witt normalization step.
The hard frame-transitivity theorem is still downstream; these lemmas make the
one-column descent explicit and reusable.
-/

noncomputable section

open Complex Matrix Classical

namespace SOComplex

/-- The `a`th prefix column of an ambient `m + r + 1` dimensional frame. -/
def prefixCol (m r : ℕ) (a : Fin r) : Fin (m + r + 1) :=
  ⟨a.val, by omega⟩

@[simp]
theorem prefixCol_zero {m r : ℕ} :
    prefixCol m (r + 1) (0 : Fin (r + 1)) = 0 := by
  ext
  simp [prefixCol]

@[simp]
theorem prefixCol_succ {m r : ℕ} (a : Fin r) :
    prefixCol m (r + 1) a.succ = (prefixCol m r a).succ := by
  ext
  simp [prefixCol]

@[simp]
theorem inv_val_apply {n : ℕ} (A : SOComplex n) (i j : Fin n) :
    (A⁻¹).val i j = A.val j i := by
  rfl

/-- The first coordinate of the inverse-transformed vector is its dot product
with the first column of the original special orthogonal matrix. -/
theorem inv_mulVec_zero_eq_sum_col {n : ℕ} [NeZero n]
    (A : SOComplex n) (w : Fin n → ℂ) :
    ((A⁻¹).val *ᵥ w) (0 : Fin n) =
      ∑ k : Fin n, A.val k (0 : Fin n) * w k := by
  change (∑ k : Fin n, (A⁻¹).val (0 : Fin n) k * w k) = _
  simp

/-- If the first column of `A` is `v / σ`, then every vector orthogonal to
`v` has zero first coordinate after applying `A⁻¹`. -/
theorem inv_mulVec_zero_eq_zero_of_signed_col_orth {n : ℕ} [NeZero n]
    (A : SOComplex n) {σ : ℂ} (hσ : σ ≠ 0)
    {v w : Fin n → ℂ}
    (hA : ∀ k : Fin n, σ * A.val k (0 : Fin n) = v k)
    (horth : ∑ k : Fin n, v k * w k = 0) :
    ((A⁻¹).val *ᵥ w) (0 : Fin n) = 0 := by
  have hmul : σ * ((A⁻¹).val *ᵥ w) (0 : Fin n) = 0 := by
    rw [inv_mulVec_zero_eq_sum_col]
    calc
      σ * (∑ k : Fin n, A.val k (0 : Fin n) * w k)
          = ∑ k : Fin n, σ * (A.val k (0 : Fin n) * w k) := by
              rw [Finset.mul_sum]
      _ = ∑ k : Fin n, v k * w k := by
              apply Finset.sum_congr rfl
              intro k _
              rw [← mul_assoc, hA k]
      _ = 0 := horth
  exact (mul_eq_zero.mp hmul).resolve_left hσ

/-- Special orthogonal matrices preserve the complex symmetric dot product. -/
theorem dot_mulVec_eq {n : ℕ} (A : SOComplex n)
    (v w : Fin n → ℂ) :
    (∑ k : Fin n, (A.val *ᵥ v) k * (A.val *ᵥ w) k) =
      ∑ k : Fin n, v k * w k := by
  have hvec : (A.val *ᵥ v) ᵥ* A.val = v := by
    calc
      (A.val *ᵥ v) ᵥ* A.val = (v ᵥ* A.val.transpose) ᵥ* A.val := by
          rw [Matrix.vecMul_transpose]
      _ = v ᵥ* (A.val.transpose * A.val) := by
          rw [Matrix.vecMul_vecMul]
      _ = v := by
          rw [A.orthogonal]
          simp
  calc
    (∑ k : Fin n, (A.val *ᵥ v) k * (A.val *ᵥ w) k)
        = (A.val *ᵥ v) ⬝ᵥ (A.val *ᵥ w) := by
            simp [dotProduct]
    _ = ((A.val *ᵥ v) ᵥ* A.val) ⬝ᵥ w := by
            rw [Matrix.dotProduct_mulVec]
    _ = v ⬝ᵥ w := by rw [hvec]
    _ = ∑ k : Fin n, v k * w k := by
            simp [dotProduct]

/-- Special orthogonal matrices preserve the square norm. -/
theorem sumSq_mulVec_eq {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    (∑ k : Fin n, (A.val *ᵥ v) k ^ 2) =
      ∑ k : Fin n, v k ^ 2 := by
  simpa [sq] using dot_mulVec_eq A v v

/-- Applying an element after its inverse recovers the original vector. -/
theorem mulVec_inv_mulVec {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    A.val *ᵥ ((A⁻¹).val *ᵥ v) = v := by
  have hmul : A.val * (A⁻¹).val = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change (A * A⁻¹).val = (1 : SOComplex n).val
    exact congrArg SOComplex.val (mul_inv_cancel A)
  calc
    A.val *ᵥ ((A⁻¹).val *ᵥ v) =
        (A.val * (A⁻¹).val) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
    _ = v := by
          rw [hmul]
          simp

/-- Applying the inverse after an element recovers the original vector. -/
theorem inv_mulVec_mulVec {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    (A⁻¹).val *ᵥ (A.val *ᵥ v) = v := by
  have hmul : (A⁻¹).val * A.val = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change (A⁻¹ * A).val = (1 : SOComplex n).val
    exact congrArg SOComplex.val (inv_mul_cancel A)
  calc
    (A⁻¹).val *ᵥ (A.val *ᵥ v) =
        ((A⁻¹).val * A.val) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
    _ = v := by
          rw [hmul]
          simp

/-- The first column of `A * embed B` is the first column of `A`. -/
theorem mul_embed_val_col_zero {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    (k : Fin (m + 2)) :
    (A * embed B).val k 0 = A.val k 0 := by
  change (A.val * (embed B).val) k 0 = A.val k 0
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

/-- The remaining columns of `A * embed B` are `A` applied to the embedded
tail columns of `B`. -/
theorem mul_embed_val_col_succ {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    (k : Fin (m + 2)) (j : Fin (m + 1)) :
    (A * embed B).val k j.succ =
      ∑ l : Fin (m + 1), A.val k l.succ * B.val l j := by
  change (A.val * (embed B).val) k j.succ = _
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

/-- If the zeroth coordinate vanishes, dropping it preserves the square norm. -/
theorem sum_tail_sq_eq_of_zero_head {m : ℕ}
    (v : Fin (m + 2) → ℂ) (h0 : v 0 = 0) :
    (∑ i : Fin (m + 1), v i.succ ^ 2) =
      ∑ k : Fin (m + 2), v k ^ 2 := by
  conv_rhs => rw [Fin.sum_univ_succ]
  simp [h0]

/-- If the zeroth coordinates vanish, dropping them preserves the dot product. -/
theorem sum_tail_mul_eq_of_zero_heads {m : ℕ}
    (v w : Fin (m + 2) → ℂ) (hv0 : v 0 = 0) (hw0 : w 0 = 0) :
    (∑ i : Fin (m + 1), v i.succ * w i.succ) =
      ∑ k : Fin (m + 2), v k * w k := by
  conv_rhs => rw [Fin.sum_univ_succ]
  simp [hv0, hw0]

/-- Tail square norm after the signed one-column normalization. -/
theorem tail_sq_eq_of_inv_mulVec_signed_col_orth {m : ℕ}
    (A : SOComplex (m + 2)) {σ τ : ℂ} (hσ : σ ≠ 0)
    {v w : Fin (m + 2) → ℂ}
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v k)
    (hvw : ∑ k : Fin (m + 2), v k * w k = 0)
    (hww : ∑ k : Fin (m + 2), w k ^ 2 = τ ^ 2) :
    (∑ i : Fin (m + 1), ((A⁻¹).val *ᵥ w) i.succ ^ 2) = τ ^ 2 := by
  let w' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ w
  have hw0 : w' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvw
  have hsq : ∑ k : Fin (m + 2), w' k ^ 2 = τ ^ 2 := by
    simpa [w'] using (sumSq_mulVec_eq (A⁻¹) w).trans hww
  calc
    (∑ i : Fin (m + 1), ((A⁻¹).val *ᵥ w) i.succ ^ 2)
        = ∑ i : Fin (m + 1), w' i.succ ^ 2 := by rfl
    _ = ∑ k : Fin (m + 2), w' k ^ 2 :=
        sum_tail_sq_eq_of_zero_head w' hw0
    _ = τ ^ 2 := hsq

/-- Tail dot product after the signed one-column normalization. -/
theorem tail_dot_eq_of_inv_mulVec_signed_col_orth {m : ℕ}
    (A : SOComplex (m + 2)) {σ : ℂ} (hσ : σ ≠ 0)
    {v w u : Fin (m + 2) → ℂ} {c : ℂ}
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v k)
    (hvw : ∑ k : Fin (m + 2), v k * w k = 0)
    (hvu : ∑ k : Fin (m + 2), v k * u k = 0)
    (hwu : ∑ k : Fin (m + 2), w k * u k = c) :
    (∑ i : Fin (m + 1),
      ((A⁻¹).val *ᵥ w) i.succ * ((A⁻¹).val *ᵥ u) i.succ) = c := by
  let w' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ w
  let u' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ u
  have hw0 : w' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvw
  have hu0 : u' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvu
  calc
    (∑ i : Fin (m + 1),
      ((A⁻¹).val *ᵥ w) i.succ * ((A⁻¹).val *ᵥ u) i.succ)
        = ∑ i : Fin (m + 1), w' i.succ * u' i.succ := by rfl
    _ = ∑ k : Fin (m + 2), w' k * u' k :=
        sum_tail_mul_eq_of_zero_heads w' u' hw0 hu0
    _ = ∑ k : Fin (m + 2), w k * u k := by
        simpa [w', u'] using dot_mulVec_eq (A⁻¹) w u
    _ = c := hwu

/-- Tail Gram table after one signed first-column normalization. -/
theorem tail_frame_dot_eq_of_inv_mulVec_signed_col_orth {m r : ℕ}
    (A : SOComplex (m + 2)) {σ : ℂ} (hσ : σ ≠ 0)
    {v₀ : Fin (m + 2) → ℂ}
    (v : Fin r → Fin (m + 2) → ℂ)
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v₀ k)
    (horth : ∀ a : Fin r, ∑ k : Fin (m + 2), v₀ k * v a k = 0)
    (a b : Fin r) :
    (∑ i : Fin (m + 1),
      ((A⁻¹).val *ᵥ v a) i.succ * ((A⁻¹).val *ᵥ v b) i.succ) =
      ∑ k : Fin (m + 2), v a k * v b k := by
  exact
    tail_dot_eq_of_inv_mulVec_signed_col_orth
      A hσ hA (horth a) (horth b) rfl

/-- The first column of the assembled matrix `A * embed B` keeps the signed
first-column data supplied by `A`. -/
theorem signed_mul_embed_col_zero_eq {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    {σ : ℂ} {v : Fin (m + 2) → ℂ}
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v k)
    (k : Fin (m + 2)) :
    σ * (A * embed B).val k 0 = v k := by
  rw [mul_embed_val_col_zero]
  exact hA k

/-- Final column rewrite for the signed-frame induction: if the recursive tail
matrix `B` has the signed tail coordinates of `A⁻¹ v` as column `j`, then
`A * embed B` has the original vector `v` as the corresponding successor
column. -/
theorem signed_mul_embed_col_succ_eq_of_tail {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    {σ : ℂ} {v : Fin (m + 2) → ℂ}
    (j : Fin (m + 1))
    (hB :
      ∀ l : Fin (m + 1),
        σ * B.val l j = ((A⁻¹).val *ᵥ v) l.succ)
    (hzero : ((A⁻¹).val *ᵥ v) (0 : Fin (m + 2)) = 0)
    (k : Fin (m + 2)) :
    σ * (A * embed B).val k j.succ = v k := by
  let w : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ v
  have htail :
      σ * (∑ l : Fin (m + 1), A.val k l.succ * B.val l j) =
        ∑ l : Fin (m + 1), A.val k l.succ * w l.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    calc
      σ * (A.val k l.succ * B.val l j)
          = A.val k l.succ * (σ * B.val l j) := by ring
      _ = A.val k l.succ * w l.succ := by rw [hB l]
  have hfull :
      (∑ l : Fin (m + 1), A.val k l.succ * w l.succ) =
        ∑ q : Fin (m + 2), A.val k q * w q := by
    conv_rhs => rw [Fin.sum_univ_succ]
    simp [w, hzero]
  calc
    σ * (A * embed B).val k j.succ
        = σ * (∑ l : Fin (m + 1), A.val k l.succ * B.val l j) := by
            rw [mul_embed_val_col_succ]
    _ = ∑ l : Fin (m + 1), A.val k l.succ * w l.succ := htail
    _ = ∑ q : Fin (m + 2), A.val k q * w q := hfull
    _ = (A.val *ᵥ w) k := by rfl
    _ = v k := by
        exact congrFun (mulVec_inv_mulVec A v) k

/-- Signed prefix-frame transitivity for the standard complex symmetric dot
form.  A dot-orthogonal prefix frame with diagonal signed squares `σ a ^ 2`
is realized as the corresponding signed prefix columns of some element of
`SOComplex`. -/
theorem exists_so_with_signedPrefixCols
    (m r : ℕ)
    (σ : Fin r → ℂ)
    (hσ : ∀ a : Fin r, σ a ≠ 0)
    (v : Fin r → Fin (m + r + 1) → ℂ)
    (hgram :
      ∀ a b : Fin r,
        (∑ k : Fin (m + r + 1), v a k * v b k) =
          if a = b then (σ a) ^ 2 else 0) :
    ∃ A : SOComplex (m + r + 1),
      ∀ (a : Fin r) (k : Fin (m + r + 1)),
        σ a * A.val k (prefixCol m r a) = v a k := by
  induction r with
  | zero =>
      refine ⟨1, ?_⟩
      intro a
      exact Fin.elim0 a
  | succ r ih =>
      let σ0 : ℂ := σ 0
      let v0 : Fin (m + (r + 1) + 1) → ℂ := v 0
      have hσ0 : σ0 ≠ 0 := hσ 0
      have hv0_sq : ∑ k : Fin (m + (r + 1) + 1), v0 k ^ 2 = σ0 ^ 2 := by
        have h := hgram 0 0
        simpa [v0, σ0, sq] using h
      obtain ⟨A0, hA0⟩ :=
        exists_so_with_firstCol_of_sq (m := m + r) σ0 hσ0 v0 hv0_sq
      let tailσ : Fin r → ℂ := fun a => σ a.succ
      let tailv : Fin r → Fin (m + r + 1) → ℂ :=
        fun a i => ((A0⁻¹).val *ᵥ v a.succ) i.succ
      have htailσ : ∀ a : Fin r, tailσ a ≠ 0 := by
        intro a
        exact hσ a.succ
      have horth :
          ∀ a : Fin r,
            ∑ k : Fin (m + (r + 1) + 1), v0 k * v a.succ k = 0 := by
        intro a
        have h := hgram 0 a.succ
        simpa [v0] using h
      have htailGram :
          ∀ a b : Fin r,
            (∑ k : Fin (m + r + 1), tailv a k * tailv b k) =
              if a = b then (tailσ a) ^ 2 else 0 := by
        intro a b
        calc
          (∑ k : Fin (m + r + 1), tailv a k * tailv b k)
              =
                ∑ k : Fin (m + (r + 1) + 1),
                  v a.succ k * v b.succ k := by
                  simpa [tailv] using
                    tail_frame_dot_eq_of_inv_mulVec_signed_col_orth
                      A0 hσ0 (fun a : Fin r => v a.succ) hA0 horth a b
          _ = if a = b then (tailσ a) ^ 2 else 0 := by
              have h := hgram a.succ b.succ
              by_cases hab : a = b
              · subst hab
                simpa [tailσ] using h
              · have hs : a.succ ≠ b.succ := fun h =>
                  hab (Fin.succ_injective _ h)
                simpa [tailσ, hs, hab] using h
      obtain ⟨B, hB⟩ := ih tailσ htailσ tailv htailGram
      refine ⟨A0 * embed B, ?_⟩
      intro a k
      refine Fin.cases ?_ ?_ a
      · change σ0 * (A0 * embed B).val k 0 = v0 k
        exact signed_mul_embed_col_zero_eq A0 B hA0 k
      · intro a
        have hzero :
            ((A0⁻¹).val *ᵥ v a.succ) (0 : Fin (m + (r + 1) + 1)) = 0 :=
          inv_mulVec_zero_eq_zero_of_signed_col_orth A0 hσ0 hA0 (horth a)
        simpa [tailσ, tailv] using
          signed_mul_embed_col_succ_eq_of_tail
            A0 B (prefixCol m r a) (hB a) hzero k

end SOComplex

end
