/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic
import OSReconstruction.SCV.IteratedCauchyIntegral
import OSReconstruction.SCV.EdgeOfWedge
import OSReconstruction.SCV.Analyticity
import OSReconstruction.SCV.EOWMultiDim
import OSReconstruction.SCV.MoebiusMap
import OSReconstruction.SCV.SeparatelyAnalytic

/-!
# Tube Domain Extension and the Edge-of-the-Wedge Theorem

This file proves the multi-dimensional edge-of-the-wedge theorem using
the iterated Cauchy integral approach.

## Main definitions

* `TubeDomain` — the tube domain `ℝᵐ + iC` for an open convex cone `C ⊂ ℝᵐ`

## Main results

* `edge_of_the_wedge_theorem` — the edge-of-the-wedge theorem as a theorem (not axiom)

## Strategy

The gap-point problem: for m ≥ 2, there exist z near the real subspace with
Im(z) ∉ C ∪ (-C) ∪ {0}. At such gap points, neither f₊ nor f₋ provides a value.

The solution: define the extension at gap points via the iterated Cauchy integral
```
  F(z) = (2πi)⁻ᵐ ∮...∮ bv(Re w) / ∏(wⱼ - zⱼ) dw₁⋯dwₘ
```
where the integration contours are chosen so all wⱼ stay real (on the real torus).
Then:
1. F is holomorphic on the polydisc (by `cauchyIntegralPolydisc_differentiableOn`)
2. F = f₊ on the intersection with the tube (by the identity theorem)
3. F = f₋ on the intersection with the opposite tube (by the identity theorem)

## References

* Bogoliubov, N.N. (1956). *On the theory of quantized fields*. ICM report.
* Rudin, W. (1971). *Lectures on the edge-of-the-wedge theorem*. CBMS 6.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-16.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

namespace SCV

/-! ### Tube domains -/

/-- The tube domain `T(C) = { z ∈ ℂᵐ : Im(z) ∈ C }` where `C ⊂ ℝᵐ` is an
    open convex cone. This is the natural domain of holomorphic extension
    for functions with boundary values on `ℝᵐ`. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The tube domain is open when the cone is open. -/
theorem tubeDomain_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain C) := by
  -- TubeDomain C = Im⁻¹(C) where Im : ℂᵐ → ℝᵐ is continuous
  exact hC.preimage (continuous_pi (fun i => Complex.continuous_im.comp (continuous_apply i)))

/-- The tube domain is connected when C is convex and nonempty. -/
theorem tubeDomain_isPreconnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC : Convex ℝ C) (_hne : C.Nonempty) :
    IsPreconnected (TubeDomain C) := by
  -- The tube domain is convex (hence preconnected): for z₁, z₂ ∈ T(C) and
  -- real t ∈ [0,1], Im(t z₁ + (1-t) z₂) = t Im(z₁) + (1-t) Im(z₂) ∈ C.
  apply Convex.isPreconnected
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  show (fun i => ((a • z₁ + b • z₂) i).im) ∈ C
  have key : (fun i => ((a • z₁ + b • z₂) i).im) =
      a • (fun i => (z₁ i).im) + b • (fun i => (z₂ i).im) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      smul_eq_mul]
  rw [key]
  exact hC hz₁ hz₂ ha hb hab

/-- The opposite tube domain. -/
theorem tubeDomain_neg {m : ℕ} (C : Set (Fin m → ℝ)) :
    TubeDomain (Neg.neg '' C) =
    { z : Fin m → ℂ | (fun i => -(z i).im) ∈ C } := by
  ext z
  simp only [TubeDomain, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, hyz⟩
    convert hy using 1
    ext i; have := congr_fun hyz i; simp only [Pi.neg_apply] at this; linarith
  · intro h
    exact ⟨fun i => -(z i).im, h, by ext i; simp⟩

/-- The real subspace (Im = 0) is the common boundary of T(C) and T(-C). -/
def realSubspace (m : ℕ) : Set (Fin m → ℂ) :=
  { z | ∀ i, (z i).im = 0 }

/-- The embedding of ℝᵐ into the real subspace of ℂᵐ. -/
def realEmbed {m : ℕ} (x : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ)

/-! ### Helper lemmas for the Edge-of-the-Wedge Theorem -/

/-- In dimension 1, an open convex cone not containing 0 consists entirely of
    vectors with positive 0-th component, or entirely of vectors with negative 0-th component. -/
lemma cone_fin1_pos_or_neg (C : Set (Fin 1 → ℝ))
    (hconv : Convex ℝ C) (h0 : (0 : Fin 1 → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin 1 → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty) :
    (∀ y ∈ C, y 0 > 0) ∨ (∀ y ∈ C, y 0 < 0) := by
  obtain ⟨y₀, hy₀⟩ := hCne
  -- y₀ ≠ 0 since 0 ∉ C
  have hy₀_ne : y₀ 0 ≠ 0 := by
    intro h; apply h0; convert hy₀ using 1; ext i; fin_cases i; exact h.symm
  -- Helper: if p ∈ C with p 0 > 0 and q ∈ C with q 0 < 0, then 0 ∈ C (contradiction)
  have no_mixed : ∀ p q : Fin 1 → ℝ, p ∈ C → q ∈ C → p 0 > 0 → q 0 < 0 → False := by
    intro p q hp hq hp0 hq0
    apply h0
    -- Scale q so that (s • q) 0 = -(p 0)
    set s := p 0 / (-(q 0)) with hs_def
    have hs_pos : 0 < s := div_pos hp0 (neg_pos.mpr hq0)
    have hsq : s • q ∈ C := hcone s q hs_pos hq
    -- Convex combination (1/2) • p + (1/2) • (s • q) ∈ C
    have hmid := hconv hp hsq (by positivity : (0 : ℝ) ≤ 1 / 2)
      (by positivity : (0 : ℝ) ≤ 1 / 2) (by ring : (1 : ℝ) / 2 + 1 / 2 = 1)
    -- (s • q) 0 = -(p 0)
    have hq0_ne : (q 0 : ℝ) ≠ 0 := ne_of_lt hq0
    have hsq0 : (s • q) 0 = -(p 0) := by
      simp only [Pi.smul_apply, smul_eq_mul, hs_def]
      field_simp
    -- Its 0-th component is 0
    have hval : ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • (s • q)) 0 = 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsq0]; ring
    have : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • (s • q) = 0 := by
      ext i; fin_cases i; simpa using hval
    rwa [this] at hmid
  -- Helper: y 0 = 0 means y = 0 (for Fin 1 → ℝ)
  have eq_zero_of_val : ∀ y : Fin 1 → ℝ, y 0 = 0 → y = 0 := by
    intro y h; ext i; fin_cases i; simpa using h
  rcases lt_or_gt_of_ne hy₀_ne with hy₀_neg | hy₀_pos
  · right; intro y hy
    rcases lt_or_eq_of_le (not_lt.mp (fun h => no_mixed y y₀ hy hy₀ h hy₀_neg)) with h | h
    · exact h
    · exfalso; exact h0 (eq_zero_of_val y h ▸ hy)
  · left; intro y hy
    rcases lt_or_eq_of_le (not_lt.mp (fun h => no_mixed y₀ y hy₀ hy hy₀_pos h)) with h | h
    · linarith
    · exfalso; exact h0 (eq_zero_of_val y h.symm ▸ hy)

/-- TubeDomain of positive cone in Fin 1 maps to the upper half-plane. -/
lemma tubeDomain_fin1_pos_subset_uhp (C : Set (Fin 1 → ℝ))
    (hC_pos : ∀ y ∈ C, y 0 > 0) :
    TubeDomain C ⊆ { z : Fin 1 → ℂ | (z 0).im > 0 } := by
  intro z hz
  simp only [TubeDomain, Set.mem_setOf_eq] at hz ⊢
  exact hC_pos _ hz

/-- TubeDomain of negative image of positive cone maps to the lower half-plane. -/
lemma tubeDomain_fin1_neg_subset_lhp (C : Set (Fin 1 → ℝ))
    (hC_pos : ∀ y ∈ C, y 0 > 0) :
    TubeDomain (Neg.neg '' C) ⊆ { z : Fin 1 → ℂ | (z 0).im < 0 } := by
  intro z hz
  simp only [TubeDomain, Set.mem_setOf_eq, Set.mem_image] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  show (z 0).im < 0
  have h1 : y 0 > 0 := hC_pos y hy
  have h2 : (z 0).im = -(y 0) := by
    have := congr_fun hyz 0; simp only [Pi.neg_apply] at this; linarith
  linarith

/-- Upper half-plane (in z 0) is contained in TubeDomain C when C contains all positive rays. -/
lemma uhp_subset_tubeDomain_fin1 (C : Set (Fin 1 → ℝ))
    (hcone : ∀ (t : ℝ) (y : Fin 1 → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty) (hC_pos : ∀ y ∈ C, y 0 > 0) :
    { z : Fin 1 → ℂ | (z 0).im > 0 } ⊆ TubeDomain C := by
  intro z hz
  simp only [TubeDomain, Set.mem_setOf_eq] at hz ⊢
  -- Im(z) = fun i => (z i).im. For this to be in C, we need (z 0).im > 0.
  obtain ⟨y₀, hy₀⟩ := hCne
  have hy₀_pos := hC_pos y₀ hy₀
  -- Scale y₀ to have y₀ 0 = (z 0).im
  set s := (z 0).im / (y₀ 0)
  have hs : 0 < s := div_pos hz hy₀_pos
  have hsm : s • y₀ ∈ C := hcone s y₀ hs hy₀
  convert hsm using 1
  ext i; fin_cases i
  simp [Pi.smul_apply, smul_eq_mul, s]
  field_simp

/-- C and -C are disjoint for an open convex cone with 0 ∉ C. -/
lemma cone_neg_disjoint {m : ℕ} (C : Set (Fin m → ℝ))
    (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (_hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C) :
    Disjoint C (Neg.neg '' C) := by
  rw [Set.disjoint_iff]
  intro y ⟨hy, hny⟩
  obtain ⟨y', hy', heq⟩ := hny
  -- y ∈ C and y = -y' with y' ∈ C
  have : y + y' = 0 := by
    ext i; have := congr_fun heq i; simp only [Pi.neg_apply] at this
    simp [Pi.add_apply]; linarith
  -- Convex combination: (1/2) • y + (1/2) • y' ∈ C
  have hmid := hconv hy hy' (by positivity : (0 : ℝ) ≤ 1/2)
    (by positivity : (0 : ℝ) ≤ 1/2) (by ring : (1 : ℝ)/2 + 1/2 = 1)
  -- (1/2) • y + (1/2) • y' = (1/2) • (y + y') = 0
  have : (1/2 : ℝ) • y + (1/2 : ℝ) • y' = 0 := by
    rw [← smul_add, this, smul_zero]
  rw [this] at hmid
  exact h0 hmid

/-- The tube domains T(C) and T(-C) are disjoint. -/
lemma tubeDomain_disjoint {m : ℕ} (C : Set (Fin m → ℝ))
    (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C) :
    Disjoint (TubeDomain C) (TubeDomain (Neg.neg '' C)) := by
  rw [Set.disjoint_iff]
  intro z ⟨hz1, hz2⟩
  have := (cone_neg_disjoint C hconv h0 hcone).le_bot ⟨hz1, hz2⟩
  exact this

/-! ### Coordinate change Φ and the m ≥ 2 extension -/

/-- The affine coordinate change Φ(w)_i = x₀_i + ∑_j w_j * (ys_j)_i. -/
private def Phi {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) :
    (Fin m → ℂ) → (Fin m → ℂ) :=
  fun w i => (x₀ i : ℂ) + ∑ j : Fin m, w j * ((ys j) i : ℂ)

private theorem Phi_zero {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) :
    Phi x₀ ys 0 = realEmbed x₀ := by
  ext i; simp [Phi, realEmbed]

private theorem Phi_differentiable {m : ℕ} (x₀ : Fin m → ℝ)
    (ys : Fin m → (Fin m → ℝ)) : Differentiable ℂ (Phi x₀ ys) :=
  differentiable_pi.mpr fun _ =>
    (differentiable_const _).add <|
      Differentiable.fun_sum fun j _ =>
        (differentiable_apply j).mul (differentiable_const _)

private theorem Phi_im {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ))
    (w : Fin m → ℂ) (i : Fin m) :
    (Phi x₀ ys w i).im = ∑ j : Fin m, (w j).im * (ys j) i := by
  simp [Phi, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, mul_zero]

/-- Φ maps the positive orthant into T(C). -/
private theorem Phi_pos_in_tube {m : ℕ} (hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) (hys : ∀ k, ys k ∈ C)
    (w : Fin m → ℂ) (hw : ∀ j, (w j).im > 0) :
    Phi x₀ ys w ∈ TubeDomain C := by
  simp only [TubeDomain, Set.mem_setOf_eq]
  have : (fun i => (Phi x₀ ys w i).im) = ∑ j : Fin m, (w j).im • ys j := by
    ext i; simp [Phi_im, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact convex_cone_sum_univ_mem hconv hcone hm hw hys

/-- Φ maps the negative orthant into T(-C). -/
private theorem Phi_neg_in_tube {m : ℕ} (hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) (hys : ∀ k, ys k ∈ C)
    (w : Fin m → ℂ) (hw : ∀ j, (w j).im < 0) :
    Phi x₀ ys w ∈ TubeDomain (Neg.neg '' C) := by
  simp only [TubeDomain, Set.mem_setOf_eq]
  have : (fun i => (Phi x₀ ys w i).im) = ∑ j : Fin m, (w j).im • ys j := by
    ext i; simp [Phi_im, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  refine ⟨∑ j, (-(w j).im) • ys j, ?_, ?_⟩
  · exact convex_cone_sum_univ_mem hconv hcone hm (fun j => by linarith [hw j]) hys
  · ext i; simp [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]

/-- When a single coordinate k has Im > 0 and all others are real,
Φ maps into T(C). (Because Im(Φ(w)) = Im(w_k) • ys_k ∈ C.) -/
private theorem Phi_single_im_pos_in_tube {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) (hys : ∀ k, ys k ∈ C)
    (w : Fin m → ℂ) (k : Fin m)
    (hk_pos : (w k).im > 0) (hothers : ∀ j, j ≠ k → (w j).im = 0) :
    Phi x₀ ys w ∈ TubeDomain C := by
  simp only [TubeDomain, Set.mem_setOf_eq]
  have him_eq : (fun i => (Phi x₀ ys w i).im) = (w k).im • ys k := by
    ext i; simp only [Phi_im, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_single k
      (fun j _ hj => by rw [hothers j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ k) h)
  rw [him_eq]; exact hcone _ _ hk_pos (hys k)

/-- Similarly for Im < 0 → T(-C). -/
private theorem Phi_single_im_neg_in_tube {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) (hys : ∀ k, ys k ∈ C)
    (w : Fin m → ℂ) (k : Fin m)
    (hk_neg : (w k).im < 0) (hothers : ∀ j, j ≠ k → (w j).im = 0) :
    Phi x₀ ys w ∈ TubeDomain (Neg.neg '' C) := by
  simp only [TubeDomain, Set.mem_setOf_eq]
  have him_eq : (fun i => (Phi x₀ ys w i).im) = (w k).im • ys k := by
    ext i; simp only [Phi_im, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_single k
      (fun j _ hj => by rw [hothers j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ k) h)
  rw [him_eq]
  refine ⟨(-(w k).im) • ys k, hcone _ _ (by linarith) (hys k), ?_⟩
  ext i; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]

/-- Φ maps real vectors to real-embedded points. -/
private theorem Phi_real {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ))
    (t : Fin m → ℝ) :
    Phi x₀ ys (fun j => (t j : ℂ)) =
      realEmbed (fun i => x₀ i + ∑ j, t j * (ys j) i) := by
  ext i; simp [Phi, realEmbed, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Phi commutes with complex conjugation (since x₀ and ys are real). -/
private theorem Phi_conj {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ))
    (w : Fin m → ℂ) :
    Phi x₀ ys (fun j => starRingEnd ℂ (w j)) =
      fun i => starRingEnd ℂ (Phi x₀ ys w i) := by
  ext i; simp only [Phi, map_add, map_sum, map_mul, Complex.conj_ofReal]

/-- Phi is a holomorphic equivalence: it has a differentiable two-sided inverse.
    This follows from the linear independence of ys, which makes the linear part
    of Phi an invertible ℂ-linear map (real-linear independence implies
    ℂ-linear independence for real vectors). -/
private lemma Phi_equiv {m : ℕ} (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ))
    (hli : LinearIndependent ℝ ys) :
    ∃ (Φ_inv : (Fin m → ℂ) → (Fin m → ℂ)),
      Differentiable ℂ Φ_inv ∧
      (∀ w, Φ_inv (Phi x₀ ys w) = w) ∧
      (∀ z, Phi x₀ ys (Φ_inv z) = z) := by
  -- The linear part of Phi corresponds to matrix M with M_{ij} = (ys_j)_i
  let M : Matrix (Fin m) (Fin m) ℂ := fun i j => ((ys j) i : ℂ)
  -- Phi(w) = realEmbed(x₀) + M.mulVec w
  have hPhi_eq : ∀ w, Phi x₀ ys w = realEmbed x₀ + M.mulVec w := by
    intro w; ext i
    simp only [Phi, realEmbed, Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  -- M.det is a unit: ys linearly independent → real matrix invertible → det(M) ≠ 0
  have hdet : IsUnit M.det := by
    let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of ys
    have hA_unit : IsUnit A :=
      Matrix.linearIndependent_rows_iff_isUnit.mp (by
        show LinearIndependent ℝ A.row
        simp only [Matrix.row_def, A]; exact hli)
    have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA_unit
    change IsUnit M.det
    have hM_eq : M = (Matrix.of ys).transpose.map Complex.ofRealHom := by
      ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, M]
    rw [hM_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    exact hdetA.map _
  -- Define Φ_inv(z) = M⁻¹.mulVec (z - realEmbed x₀)
  refine ⟨fun z => M⁻¹.mulVec (z - realEmbed x₀), ?_, ?_, ?_⟩
  -- Differentiable: each component is ∑ (const * (apply - const))
  · have hmv : Differentiable ℂ (fun v : Fin m → ℂ => M⁻¹.mulVec v) := by
      apply differentiable_pi.mpr; intro i
      simp only [Matrix.mulVec, dotProduct]
      exact Differentiable.fun_sum fun j _ =>
        (differentiable_const _).mul (differentiable_apply _)
    exact hmv.comp (differentiable_id.sub (differentiable_const _))
  -- Left inverse: M⁻¹.mulVec(Phi(w) - x₀) = M⁻¹.mulVec(M.mulVec w) = w
  · intro w
    simp only [hPhi_eq, add_sub_cancel_left]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  -- Right inverse: x₀ + M.mulVec(M⁻¹.mulVec(z - x₀)) = x₀ + (z - x₀) = z
  · intro z
    rw [hPhi_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    abel

/-- ContinuousAt of the scaled Möbius product map w ↦ (j ↦ δ · moebiusRudin(wⱼ/δ, l)).
    Factored out as a standalone lemma to avoid deterministic timeout in the main proof. -/
private lemma scaledMoebiusProd_continuousAt {m : ℕ} (δ : ℝ)
    (l : ℂ) (hl : ‖l‖ ≤ 1) (w₀ : Fin m → ℂ) (hw₀ : ∀ j, ‖w₀ j / (↑δ : ℂ)‖ < 1) :
    ContinuousAt (fun w : Fin m → ℂ => fun j => (↑δ : ℂ) * moebiusProd (fun k => w k / (↑δ : ℂ)) l j) w₀ := by
  -- Stage 1: w ↦ (k ↦ w k / δ) is ContinuousAt into Fin m → ℂ
  have h_div : ContinuousAt (fun w : Fin m → ℂ => fun k => w k / (↑δ : ℂ)) w₀ :=
    continuousAt_pi.mpr fun k => (continuous_apply k).continuousAt.div_const _
  -- Stage 2: (fun k => w₀ k / δ) is in the open unit polydisc
  have h_mem : (fun k => w₀ k / (↑δ : ℂ)) ∈ Metric.ball (0 : Fin m → ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]; exact hw₀
  -- Stage 3: moebiusProd(·, l) is ContinuousAt at w₀/δ
  have h_set_eq : {w : Fin m → ℂ | ∀ j, ‖w j‖ < 1} = Metric.ball 0 1 := by
    ext w; simp [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  have h_mp : ContinuousAt (fun w => moebiusProd w l) (fun k => w₀ k / (↑δ : ℂ)) :=
    (h_set_eq ▸ (moebiusProd_differentiable_w l hl)).continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds h_mem)
  -- Stage 4: Compose and scale componentwise
  have h_comp : ContinuousAt (fun w => moebiusProd (fun k => w k / (↑δ : ℂ)) l) w₀ :=
    ContinuousAt.comp (g := fun w => moebiusProd w l) h_mp h_div
  apply continuousAt_pi.mpr; intro j
  exact continuousAt_const.mul ((continuous_apply j).continuousAt.comp h_comp)

set_option maxHeartbeats 800000 in
/-- Parametric integral is DifferentiableAt via Leibniz rule with Cauchy estimate.
    Extracted from `rudin_orthant_extension` to reduce heartbeat pressure. -/
private lemma differentiableAt_parametric_integral
    {m : ℕ} (G : (Fin m → ℂ) → ℝ → ℂ)
    {z : Fin m → ℂ} {j : Fin m} {δ : ℝ}
    (hz : z ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    {ε' : ℝ} (hε'_pos : 0 < ε')
    (h_upd : ∀ ζ, dist ζ (z j) ≤ 2 * ε' →
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (h_upd_t : ∀ t ∈ Metric.ball (z j) ε', ∀ ζ ∈ Metric.closedBall t ε',
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (h_G_meas : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        AEStronglyMeasurable (G w)
          (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)))
    (M : ℝ) (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ, ‖G w θ‖ ≤ M)
    (h_G_diffAt : ∀ θ, Real.sin θ ≠ 0 → ∀ t,
        Function.update z j t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) →
        DifferentiableAt ℂ (fun ζ => G (Function.update z j ζ) θ) t)
    (hG_zero : ∀ w θ, Real.sin θ = 0 → G w θ = 0) :
    DifferentiableAt ℂ
        (fun ζ => ∫ θ in (-Real.pi)..Real.pi, G (Function.update z j ζ) θ) (z j) := by
  -- Cauchy estimate for the derivative
  have h_cauchy : ∀ θ : ℝ, Real.sin θ ≠ 0 → ∀ t ∈ Metric.ball (z j) ε',
      ‖deriv (fun ζ => G (Function.update z j ζ) θ) t‖ ≤ M / ε' := by
    intro θ hsin t ht
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hε'_pos
    · constructor
      · exact fun ζ hζ => (h_G_diffAt θ hsin ζ (h_upd_t t ht ζ
          (Metric.ball_subset_closedBall hζ))).differentiableWithinAt
      · rw [closure_ball t hε'_pos.ne']
        exact fun ζ hζ => (h_G_diffAt θ hsin ζ
          (h_upd_t t ht ζ hζ)).continuousAt.continuousWithinAt
    · exact fun ζ hζ => hM _ (h_upd_t t ht ζ (Metric.sphere_subset_closedBall hζ)) θ
  -- Define the derivative function F'
  set F' : ℂ → ℝ → ℂ := fun ζ θ =>
    if Real.sin θ = 0 then 0
    else deriv (fun ζ' => G (Function.update z j ζ') θ) ζ with hF'_def
  -- HasDerivAt: for all θ and t ∈ ball(z j, ε')
  have h_hasderiv : ∀ θ : ℝ, ∀ t ∈ Metric.ball (z j) ε',
      HasDerivAt (fun ζ => G (Function.update z j ζ) θ) (F' t θ) t := by
    intro θ t ht
    by_cases hsin : Real.sin θ = 0
    · simp only [F', if_pos hsin]
      have hG_eq : (fun ζ => G (Function.update z j ζ) θ) = fun _ => 0 := by
        ext ζ; exact hG_zero _ θ hsin
      rw [hG_eq]; exact hasDerivAt_const _ _
    · simp only [F', if_neg hsin]
      exact (h_G_diffAt θ hsin t
        (h_upd_t t ht t (Metric.mem_closedBall_self hε'_pos.le))).hasDerivAt
  -- Bound on F'
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM z hz 0)
  have h_F'_bound : ∀ θ : ℝ, ∀ t ∈ Metric.ball (z j) ε',
      ‖F' t θ‖ ≤ M / ε' := by
    intro θ t ht
    by_cases hsin : Real.sin θ = 0
    · simp only [F', if_pos hsin, norm_zero]
      exact div_nonneg hM_nn hε'_pos.le
    · simp only [F', if_neg hsin]; exact h_cauchy θ hsin t ht
  -- AEStronglyMeasurable of F'(z j, ·): difference quotient sequence
  have hF'_meas : AEStronglyMeasurable (F' (z j))
      (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    -- Sequence y_n = z j + ↑(ε'/(n+2))
    set y : ℕ → ℂ := fun n => z j + (↑(ε' / ((n : ℝ) + 2)) : ℂ)
    have hy_rpos : ∀ n : ℕ, (0 : ℝ) < ε' / ((n : ℝ) + 2) := fun n =>
      div_pos hε'_pos (by positivity)
    have hy_ball : ∀ n, y n ∈ Metric.ball (z j) ε' := fun n => by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hy_rpos n)]
      exact div_lt_self hε'_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hy_mem : ∀ n, Function.update z j (y n) ∈
        Metric.ball (0 : Fin m → ℂ) (δ / 2) := fun n =>
      h_upd_t (z j) (Metric.mem_ball_self hε'_pos) (y n)
        (Metric.ball_subset_closedBall (hy_ball n))
    have hy_ne : ∀ n, y n ≠ z j := fun n => by
      intro h; have := congr_arg (· - z j) h
      simp only [y, add_sub_cancel_left, sub_self] at this
      exact absurd (Complex.ofReal_eq_zero.mp this) (ne_of_gt (hy_rpos n))
    have hy_tend : Filter.Tendsto y Filter.atTop (nhdsWithin (z j) {z j}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · -- y n → z j: ε'/(n+2) → 0
        suffices h : Filter.Tendsto (fun n : ℕ => (↑(ε' / ((n : ℝ) + 2)) : ℂ))
            Filter.atTop (nhds 0) by
          have := h.const_add (z j); simp only [add_zero] at this; exact this
        rw [show (0 : ℂ) = (↑(0 : ℝ) : ℂ) from by simp]
        apply Filter.Tendsto.comp (Complex.continuous_ofReal.tendsto 0)
        apply squeeze_zero (fun n => le_of_lt (hy_rpos n))
        · intro n
          apply div_le_div_of_nonneg_left hε'_pos.le (by positivity : (0:ℝ) < (n:ℝ)+1)
          linarith [Nat.cast_nonneg (α := ℝ) n]
        · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          rw [show (0 : ℝ) = ε' * 0 from (mul_zero ε').symm]
          exact (tendsto_const_nhds.mul h1).congr fun n => by ring
      · exact Filter.Eventually.of_forall fun n =>
          Set.mem_compl_singleton_iff.mpr (hy_ne n)
    -- Difference quotients
    set dq : ℕ → ℝ → ℂ := fun n θ =>
      (y n - z j)⁻¹ • (G (Function.update z j (y n)) θ - G z θ)
    -- Each dq n is AEStronglyMeasurable
    have hdq_meas : ∀ n, AEStronglyMeasurable (dq n)
        (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := fun n => by
      refine ((h_G_meas _ (hy_mem n)).sub (h_G_meas z hz)).const_smul
        ((y n - z j)⁻¹) |>.congr ?_
      exact Filter.Eventually.of_forall fun θ => rfl
    -- dq n θ → F'(z j, θ) for a.e. θ
    have hdq_tend : ∀ θ, Filter.Tendsto (fun n => dq n θ) Filter.atTop
        (nhds (F' (z j) θ)) := by
      intro θ
      have h_slope := (h_hasderiv θ (z j) (Metric.mem_ball_self hε'_pos)).tendsto_slope
      -- h_slope : Tendsto (slope (fun ζ => G(update z j ζ, θ)) (z j)) (𝓝[≠] (z j)) (nhds ...)
      have h_eq : ∀ n, dq n θ =
          slope (fun ζ => G (Function.update z j ζ) θ) (z j) (y n) := by
        intro n; simp only [dq, slope, vsub_eq_sub]; congr 1; congr 1
        exact congr_arg (fun w => G w θ) (Function.update_eq_self j z).symm
      simp_rw [h_eq]; exact h_slope.comp hy_tend
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hdq_meas
      (Filter.Eventually.of_forall hdq_tend)
  -- G(update z j (z j)) is IntervalIntegrable (= G z, bounded + measurable)
  have hG_int : IntervalIntegrable (fun θ => G (Function.update z j (z j)) θ)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    have : (fun θ => G (Function.update z j (z j)) θ) = G z := by
      ext θ; rw [Function.update_eq_self]
    rw [this, intervalIntegrable_iff]
    exact MeasureTheory.IntegrableOn.of_bound
      (lt_of_le_of_lt (MeasureTheory.measure_mono Set.uIoc_subset_uIcc) measure_Icc_lt_top)
      (h_G_meas z hz)
      M (Filter.Eventually.of_forall fun θ => hM z hz θ)
  -- Apply Leibniz rule
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun ζ θ => G (Function.update z j ζ) θ) (F' := F')
    (Metric.ball_mem_nhds (z j) hε'_pos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds (z j) hε'_pos)
      fun ζ hζ => h_G_meas _
        (h_upd _ ((Metric.mem_ball.mp hζ).le.trans (by linarith))))
    hG_int
    hF'_meas
    (MeasureTheory.ae_of_all _ fun θ _ t ht => h_F'_bound θ t ht)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ t ht => h_hasderiv θ t ht)).2.differentiableAt

/-- For REAL ζ near 0, the Möbius circle integral reproduces bv(Re(Phi(ζ))).

    This is the key step in Rudin's proof (§4, p.11-12): when ζ is real, the Möbius
    map preserves the sign of Im(l), so the 1D function l ↦ f_plus(Phi(smp(ζ,l)))
    (upper half) and l ↦ f_minus(Phi(smp(ζ,l))) (lower half) form a standard 1D
    edge-of-the-wedge problem with NO gap. Applying edge_of_the_wedge_1d gives a
    holomorphic extension to the disc, and the mean value property follows. -/
private lemma rudin_mean_value_real {m : ℕ} (hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ)) (hys_mem : ∀ k, ys k ∈ C)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (bv x)))
    (δ : ℝ) (hδ : 0 < δ)
    (hball_comp : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ j, ‖w j / (↑δ : ℂ)‖ < 1)
    -- phi_re_in_E for ‖l‖ ≤ 2 (needed for EoW with a=-2, b=2)
    (phi_re_in_E : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ l, ‖l‖ ≤ 2 → (fun i => (Phi x₀ ys
          (fun j => (↑δ : ℂ) * moebiusProd (fun k => w k / (↑δ : ℂ)) l j) i).re) ∈ E)
    (ζ : Fin m → ℂ) (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_real : ∀ j, (ζ j).im = 0) :
    let smp : (Fin m → ℂ) → ℂ → (Fin m → ℂ) :=
      fun w l j => (↑δ : ℂ) * moebiusProd (fun k => w k / (↑δ : ℂ)) l j
    let G : (Fin m → ℂ) → ℝ → ℂ := fun w θ =>
      if 0 < Real.sin θ then
        f_plus (Phi x₀ ys (smp w (Complex.exp ((θ : ℂ) * I))))
      else if Real.sin θ < 0 then
        f_minus (Phi x₀ ys (smp w (Complex.exp ((θ : ℂ) * I))))
      else 0
    (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G ζ θ =
      bv (fun i => (Phi x₀ ys ζ i).re) := by
  intro smp G
  have hw : ∀ j, ‖ζ j / (↑δ : ℂ)‖ < 1 := hball_comp ζ hζ
  have hδ_ne : (↑δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hδ)
  have hζ_div_im : ∀ j, (ζ j / (↑δ : ℂ)).im = 0 := by
    intro j; rw [Complex.div_ofReal_im]
    exact div_eq_zero_iff.mpr (Or.inl (hζ_real j))
  -- Abbreviation for the scaled Möbius coordinates
  set wζ : Fin m → ℂ := fun k => ζ k / (↑δ : ℂ) with hwζ_def
  have hwζ_im : ∀ j, (wζ j).im = 0 := hζ_div_im
  have hwζ_norm : ∀ j, ‖wζ j‖ < 1 := hw
  -- For real ζ, Im(smp) has same sign as Im(l) (Rudin property (2))
  have hsmp_im_pos : ∀ l, 0 < l.im → ∀ j, 0 < (smp ζ l j).im := by
    intro l hl_pos j
    show 0 < ((↑δ : ℂ) * moebiusProd wζ l j).im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hδ (moebiusProd_im_pos_of_real hwζ_im hwζ_norm hl_pos j)
  have hsmp_im_neg : ∀ l, l.im < 0 → ∀ j, (smp ζ l j).im < 0 := by
    intro l hl_neg j
    show ((↑δ : ℂ) * moebiusProd wζ l j).im < 0
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hδ (moebiusProd_im_neg_of_real hwζ_im hwζ_norm hl_neg j)
  -- smp maps to TubeDomain C (resp. -C) when Im(l) > 0 (resp. < 0)
  have hsmp_tube_pos : ∀ l, 0 < l.im → Phi x₀ ys (smp ζ l) ∈ TubeDomain C :=
    fun l hl => Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ (hsmp_im_pos l hl)
  have hsmp_tube_neg : ∀ l, l.im < 0 → Phi x₀ ys (smp ζ l) ∈ TubeDomain (Neg.neg '' C) :=
    fun l hl => Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ (hsmp_im_neg l hl)
  -- bv_smp and gp/gm definitions
  let bv_smp : ℝ → ℂ := fun t =>
    bv (fun i => (Phi x₀ ys (smp ζ (t : ℂ)) i).re)
  let gp : ℂ → ℂ := fun l =>
    if l.im > 0 then f_plus (Phi x₀ ys (smp ζ l))
    else bv_smp l.re
  let gm : ℂ → ℂ := fun l =>
    if l.im < 0 then f_minus (Phi x₀ ys (smp ζ l))
    else bv_smp l.re
  have hζ_cb : ζ ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) :=
    Metric.ball_subset_closedBall hζ
  -- TubeDomain openness
  have htube_open : IsOpen (TubeDomain C) := tubeDomain_isOpen hC
  have htube_neg_open : IsOpen (TubeDomain (Neg.neg '' C)) := by
    convert tubeDomain_isOpen (hC.neg) using 1
    ext z; simp [TubeDomain]
  -- Step 1: gp is holomorphic on UHP
  have hgp_diff : DifferentiableOn ℂ gp EOW.UpperHalfPlane := by
    -- First show the composition is DifferentiableOn UHP
    have hdiff_comp : DifferentiableOn ℂ
        (fun l => f_plus (Phi x₀ ys (smp ζ l))) EOW.UpperHalfPlane := by
      intro l hl
      simp only [EOW.UpperHalfPlane, Set.mem_setOf_eq] at hl
      have hl_ne : l.im ≠ 0 := ne_of_gt hl
      have hsmp_da : DifferentiableAt ℂ (fun l => smp ζ l) l := by
        rw [differentiableAt_pi]; intro j
        show DifferentiableAt ℂ (fun l => (↑δ : ℂ) * moebiusProd wζ l j) l
        exact (differentiableAt_const _).mul
          (moebiusRudin_differentiableAt_of_real (hwζ_im j) hl_ne)
      have hphi_da := (Phi_differentiable x₀ ys).differentiableAt (x := smp ζ l)
      have hmem := hsmp_tube_pos l hl
      have hfp_da := hf_plus.differentiableAt (htube_open.mem_nhds hmem)
      exact (hfp_da.comp l (hphi_da.comp l hsmp_da)).differentiableWithinAt
    -- gp agrees with the composition on UHP
    exact hdiff_comp.congr (fun l hl => by
      simp only [EOW.UpperHalfPlane, Set.mem_setOf_eq] at hl
      simp only [gp, if_pos hl])
  -- Step 2: gm is holomorphic on LHP (symmetric)
  have hgm_diff : DifferentiableOn ℂ gm EOW.LowerHalfPlane := by
    have hdiff_comp : DifferentiableOn ℂ
        (fun l => f_minus (Phi x₀ ys (smp ζ l))) EOW.LowerHalfPlane := by
      intro l hl
      simp only [EOW.LowerHalfPlane, Set.mem_setOf_eq] at hl
      have hl_ne : l.im ≠ 0 := ne_of_lt hl
      have hsmp_da : DifferentiableAt ℂ (fun l => smp ζ l) l := by
        rw [differentiableAt_pi]; intro j
        show DifferentiableAt ℂ (fun l => (↑δ : ℂ) * moebiusProd wζ l j) l
        exact (differentiableAt_const _).mul
          (moebiusRudin_differentiableAt_of_real (hwζ_im j) hl_ne)
      have hphi_da := (Phi_differentiable x₀ ys).differentiableAt (x := smp ζ l)
      have hmem := hsmp_tube_neg l hl
      have hfm_da := hf_minus.differentiableAt (htube_neg_open.mem_nhds hmem)
      exact (hfm_da.comp l (hphi_da.comp l hsmp_da)).differentiableWithinAt
    exact hdiff_comp.congr (fun l hl => by
      simp only [EOW.LowerHalfPlane, Set.mem_setOf_eq] at hl
      simp only [gm, if_pos hl])
  -- Step 3: Boundary values match on (-2, 2)
  have hmatch : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp (x : ℂ) = gm (x : ℂ) := by
    intro x _ _
    simp only [gp, gm, Complex.ofReal_im, lt_irrefl, ite_false]
  -- Denominator bound: 2 * rudinC < 1 (used for continuity at real points with |l| < 2)
  have h2c : rudinC * 2 < 1 := by
    unfold rudinC
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by linarith), Real.sqrt_nonneg 2]
  -- smp is ContinuousAt at real l with |l| < 2
  have hsmp_ca_real : ∀ (l : ℂ), ‖l‖ < 2 →
      ContinuousAt (fun l' => smp ζ l') l := by
    intro l hl
    apply continuousAt_pi.mpr; intro j
    exact continuousAt_const.mul
      (moebiusRudin_differentiableAt_general
        (moebiusDenom_ne_zero_of_norm_prod (calc
          ‖(rudinC : ℂ) * l * wζ j‖
            = rudinC * ‖l‖ * ‖wζ j‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real,
                Real.norm_of_nonneg rudinC_pos.le]
          _ ≤ rudinC * 2 * ‖wζ j‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_of_lt hl) rudinC_pos.le) (norm_nonneg _)
          _ < rudinC * 2 * 1 :=
              mul_lt_mul_of_pos_left (hwζ_norm j) (mul_pos rudinC_pos (by norm_num))
          _ < 1 := by linarith))).continuousAt
  -- bv_smp is ContinuousAt for |t| < 2
  have hbv_smp_ca : ∀ (t : ℝ), |t| < 2 → ContinuousAt bv_smp t := by
    intro t ht
    have ht_norm : ‖(↑t : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
    have hcomp_ca : ContinuousAt (fun s : ℝ => Phi x₀ ys (smp ζ (↑s))) t :=
      (Phi_differentiable x₀ ys).continuous.continuousAt.comp
        ((hsmp_ca_real (↑t) ht_norm).comp Complex.continuous_ofReal.continuousAt)
    have hh_ca : ContinuousAt (fun s : ℝ => (fun i => (Phi x₀ ys (smp ζ (↑s)) i).re)) t :=
      continuousAt_pi.mpr fun i =>
        Complex.continuous_re.continuousAt.comp
          ((continuous_apply i).continuousAt.comp hcomp_ca)
    have hp_mem : (fun i => (Phi x₀ ys (smp ζ (↑t)) i).re) ∈ E :=
      phi_re_in_E ζ hζ_cb (↑t) (le_of_lt ht_norm)
    exact (hbv_cont.continuousAt (hE.mem_nhds hp_mem)).comp hh_ca
  -- gp agrees with bv_smp ∘ re on {im = 0}
  have hgp_eq_real : ∀ l : ℂ, l.im = 0 → gp l = bv_smp l.re := by
    intro l hl
    simp only [gp, show ¬(l.im > 0) from not_lt.mpr (le_of_eq hl), ite_false]
  -- gm agrees with bv_smp ∘ re on {im = 0}
  have hgm_eq_real : ∀ l : ℂ, l.im = 0 → gm l = bv_smp l.re := by
    intro l hl
    simp only [gm, show ¬(l.im < 0) from not_lt.mpr (ge_of_eq hl), ite_false]
  -- Helper: smp(ζ,↑x) is real when ζ and x are real
  have hsmp_im_real : ∀ (x : ℝ), ∀ j, (smp ζ (↑x) j).im = 0 := by
    intro x j
    show ((↑δ : ℂ) * moebiusProd wζ (↑x) j).im = 0
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_eq_zero_of_right _ (moebiusProd_real hwζ_im (Complex.ofReal_im x) j)
  -- Helper: Phi(smp(ζ,↑x)) = realEmbed(Re(Phi(smp(ζ,↑x)))) for real x
  have hPhi_realEmbed : ∀ (x : ℝ),
      Phi x₀ ys (smp ζ ↑x) =
        realEmbed (fun i => (Phi x₀ ys (smp ζ ↑x) i).re) := by
    intro x; ext i; apply Complex.ext
    · simp [realEmbed]
    · rw [show (realEmbed (fun i => (Phi x₀ ys (smp ζ ↑x) i).re) i).im = 0
          from Complex.ofReal_im _, Phi_im]
      simp only [hsmp_im_real x, zero_mul, Finset.sum_const_zero]
  -- Step 4: Continuous boundary values from UHP
  have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (gp (x : ℂ))) := by
    intro x hx_lo hx_hi
    simp only [hgp_eq_real (↑x) (Complex.ofReal_im x)]
    have hx_norm : ‖(↑x : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hp_mem : (fun i => (Phi x₀ ys (smp ζ ↑x) i).re) ∈ E :=
      phi_re_in_E ζ hζ_cb (↑x) (le_of_lt hx_norm)
    -- ContinuousAt of Phi ∘ smp ζ at ↑x
    have hca : ContinuousAt (fun l => Phi x₀ ys (smp ζ l)) (↑x) :=
      (Phi_differentiable x₀ ys).continuous.continuousAt.comp (hsmp_ca_real (↑x) hx_norm)
    -- Tendsto to nhds(realEmbed p) restricted from nhdsWithin
    have h_nhds : Filter.Tendsto (fun l => Phi x₀ ys (smp ζ l))
        (nhdsWithin (↑x) EOW.UpperHalfPlane)
        (nhds (realEmbed (fun i => (Phi x₀ ys (smp ζ ↑x) i).re))) :=
      (hPhi_realEmbed x) ▸ hca.tendsto.mono_left nhdsWithin_le_nhds
    -- On UHP, image lies in TubeDomain C
    have h_mem : ∀ᶠ l in nhdsWithin (↑x) EOW.UpperHalfPlane,
        Phi x₀ ys (smp ζ l) ∈ TubeDomain C :=
      eventually_nhdsWithin_of_forall fun l hl => hsmp_tube_pos l hl
    -- Tendsto to nhdsWithin(realEmbed p, TubeDomain C)
    have h_nhdsW := Filter.tendsto_inf.mpr ⟨h_nhds, Filter.tendsto_principal.mpr h_mem⟩
    -- Compose with hf_plus_bv and use congr' (gp = f_plus on UHP)
    exact ((hf_plus_bv _ hp_mem).comp h_nhdsW).congr'
      (eventually_nhdsWithin_of_forall fun l hl => by
        show f_plus (Phi x₀ ys (smp ζ l)) =
          if l.im > 0 then f_plus (Phi x₀ ys (smp ζ l)) else bv_smp l.re
        rw [if_pos (show l.im > 0 from hl)])
  -- Step 5: Continuous boundary values from LHP
  have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gm (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (gm (x : ℂ))) := by
    intro x hx_lo hx_hi
    simp only [hgm_eq_real (↑x) (Complex.ofReal_im x)]
    have hx_norm : ‖(↑x : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hp_mem : (fun i => (Phi x₀ ys (smp ζ ↑x) i).re) ∈ E :=
      phi_re_in_E ζ hζ_cb (↑x) (le_of_lt hx_norm)
    have hca : ContinuousAt (fun l => Phi x₀ ys (smp ζ l)) (↑x) :=
      (Phi_differentiable x₀ ys).continuous.continuousAt.comp (hsmp_ca_real (↑x) hx_norm)
    have h_nhds : Filter.Tendsto (fun l => Phi x₀ ys (smp ζ l))
        (nhdsWithin (↑x) EOW.LowerHalfPlane)
        (nhds (realEmbed (fun i => (Phi x₀ ys (smp ζ ↑x) i).re))) :=
      (hPhi_realEmbed x) ▸ hca.tendsto.mono_left nhdsWithin_le_nhds
    have h_mem : ∀ᶠ l in nhdsWithin (↑x) EOW.LowerHalfPlane,
        Phi x₀ ys (smp ζ l) ∈ TubeDomain (Neg.neg '' C) :=
      eventually_nhdsWithin_of_forall fun l hl => hsmp_tube_neg l hl
    have h_nhdsW := Filter.tendsto_inf.mpr ⟨h_nhds, Filter.tendsto_principal.mpr h_mem⟩
    exact ((hf_minus_bv _ hp_mem).comp h_nhdsW).congr'
      (eventually_nhdsWithin_of_forall fun l hl => by
        show f_minus (Phi x₀ ys (smp ζ l)) =
          if l.im < 0 then f_minus (Phi x₀ ys (smp ζ l)) else bv_smp l.re
        have hl' : l.im < 0 := hl
        rw [if_pos hl'])
  -- Step 6: Boundary values continuous along the real line
  have hbv_real : ∀ x₀ : ℝ, (-2 : ℝ) < x₀ → x₀ < 2 →
      Filter.Tendsto gp (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (gp (x₀ : ℂ))) := by
    intro t ht_lo ht_hi
    have hgp_at : gp (↑t) = bv_smp t := by
      simp only [gp, Complex.ofReal_im, lt_irrefl, ite_false, Complex.ofReal_re]
    rw [hgp_at]
    have htend : Filter.Tendsto (fun l : ℂ => bv_smp l.re)
        (nhdsWithin (↑t) {c : ℂ | c.im = 0}) (nhds (bv_smp t)) :=
      (hbv_smp_ca t (abs_lt.mpr ⟨by linarith, by linarith⟩)).tendsto.comp
        (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)
    exact htend.congr' (eventually_nhdsWithin_of_forall fun l hl =>
      (hgp_eq_real l hl).symm)
  -- Step 7: Apply edge_of_the_wedge_1d
  obtain ⟨U, F_disc, hU_open, _, _, hU_int, hF_holo, hF_gp, hF_gm, hball⟩ :=
    edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
      hgp_diff hgm_diff hgp_bv hgm_bv hmatch hbv_real
  -- Step 8: closedBall(0, 1) ⊆ U (since ball(0, 2) ⊆ U)
  have hcb_sub : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    calc Metric.closedBall (0 : ℂ) 1
        ⊆ Metric.ball (0 : ℂ) 2 := by
          intro z hz; simp [Metric.mem_closedBall, Metric.mem_ball] at hz ⊢; linarith
      _ = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) := by
          congr 1 <;> simp
      _ ⊆ U := hball
  -- Step 9: F_disc is DifferentiableAt on closedBall(0, |1|)
  have hF_da : ∀ z ∈ Metric.closedBall (0 : ℂ) (|1|), DifferentiableAt ℂ F_disc z := by
    intro z hz; rw [abs_one] at hz
    exact hF_holo.differentiableAt (hU_open.mem_nhds (hcb_sub hz))
  -- Step 10: Mean value property
  have hmv : Real.circleAverage F_disc 0 1 = F_disc 0 := by
    have : DiffContOnCl ℂ F_disc (Metric.ball 0 |1|) := by
      constructor
      · exact fun z hz => (hF_da z (Metric.ball_subset_closedBall hz)).differentiableWithinAt
      · simp only [abs_one]
        rw [closure_ball (0 : ℂ) one_ne_zero]
        exact fun z hz => (hF_da z (by rwa [abs_one])).continuousAt.continuousWithinAt
    exact this.circleAverage
  -- Step 11: F_disc(0) = bv(Re(Φ(ζ)))
  have hF0 : F_disc 0 = bv (fun i => (Phi x₀ ys ζ i).re) := by
    -- smp(ζ,0) = ζ (moebiusRudin(w,0) = w for all w)
    have hsmp_zero : smp ζ (0 : ℂ) = ζ := by
      ext j; show (↑δ : ℂ) * moebiusProd wζ 0 j = ζ j
      simp only [moebiusProd, moebiusRudin,
        zero_div, add_zero, mul_zero, zero_mul, div_one, wζ]
      exact mul_div_cancel₀ (ζ j) hδ_ne
    -- gp(0) = bv(Re(Phi(ζ)))
    have hgp_zero_val : gp (0 : ℂ) = bv (fun i => (Phi x₀ ys ζ i).re) := by
      -- gp(0) = bv_smp(0) since 0.im = 0 is not > 0
      have : gp (0 : ℂ) = bv_smp (0 : ℂ).re :=
        hgp_eq_real 0 Complex.zero_im
      rw [this, Complex.zero_re]
      -- bv_smp(0) = bv(Re(Phi(smp(ζ,↑0)))) = bv(Re(Phi(ζ)))
      show bv (fun i => (Phi x₀ ys (smp ζ ↑(0 : ℝ)) i).re) =
        bv (fun i => (Phi x₀ ys ζ i).re)
      rw [Complex.ofReal_zero, hsmp_zero]
    -- F_disc(0) = gp(0) by limit uniqueness
    -- 0 ∈ U
    have h0_mem : (0 : ℂ) ∈ U := hU_int 0 (by norm_num) (by norm_num)
    -- nhdsWithin 0 UHP is NeBot (0 is in closure of UHP)
    have h_nebot : Filter.NeBot (nhdsWithin (0 : ℂ) EOW.UpperHalfPlane) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro ε hε
      exact ⟨↑(ε / 2) * I,
        show (↑(ε / 2) * I).im > 0 by
          simp [Complex.mul_im, Complex.I_re, Complex.I_im]; linarith,
        show dist 0 (↑(ε / 2) * I) < ε by
          rw [dist_comm, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I,
            mul_one, Real.norm_eq_abs, abs_of_pos (by linarith : ε / 2 > 0)]
          linarith⟩
    -- F_disc → F_disc(0) from UHP
    have h1 : Filter.Tendsto F_disc (nhdsWithin 0 EOW.UpperHalfPlane) (nhds (F_disc 0)) :=
      (hF_holo.continuousOn.continuousAt (hU_open.mem_nhds h0_mem)).tendsto.mono_left
        nhdsWithin_le_nhds
    -- F_disc → gp(0) from UHP (since F_disc = gp on U ∩ UHP, and gp → gp(0))
    have h2 : Filter.Tendsto F_disc (nhdsWithin 0 EOW.UpperHalfPlane) (nhds (gp 0)) := by
      have h_agree : ∀ᶠ z in nhdsWithin (0 : ℂ) EOW.UpperHalfPlane, F_disc z = gp z := by
        filter_upwards [nhdsWithin_le_nhds (hU_open.mem_nhds h0_mem),
          self_mem_nhdsWithin] with z hz_U hz_UHP
        exact hF_gp z ⟨hz_U, hz_UHP⟩
      exact (hgp_bv 0 (by norm_num) (by norm_num)).congr'
        (h_agree.mono fun _ h => h.symm)
    rw [tendsto_nhds_unique h1 h2, hgp_zero_val]
  -- Step 12: Connect circleAverage to our integral
  have hresult : (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G ζ θ =
      Real.circleAverage F_disc 0 1 := by
    rw [Real.circleAverage_def]
    congr 1
    -- Helper: circleMap 0 1 θ = cexp (↑θ * I)
    have hcm_eq : ∀ θ : ℝ, circleMap 0 1 θ = cexp (↑θ * I) := fun θ => by
      simp [circleMap_zero]
    -- Helper: circleMap 0 1 θ ∈ U (via closedBall 0 1 ⊆ U)
    have hcm_U : ∀ θ : ℝ, circleMap 0 1 θ ∈ U := fun θ =>
      hcb_sub (Metric.mem_closedBall.mpr
        (by rw [dist_zero_right, norm_circleMap_zero]; norm_num))
    -- a.e. equality: G ζ θ = F_disc (circleMap 0 1 θ) for a.e. θ in (-π, π)
    have hle_pi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have hae : ∀ᵐ (θ : ℝ), θ ∈ Set.uIoc (-Real.pi) Real.pi →
        G ζ θ = F_disc (circleMap 0 1 θ) := by
      -- The set where they can disagree is {0, π}, which has measure zero
      have h_ae_compl : ({0, Real.pi}ᶜ : Set ℝ) ∈ ae volume := by
        rw [compl_mem_ae_iff]
        exact (Set.toFinite {(0 : ℝ), Real.pi}).measure_zero _
      filter_upwards [h_ae_compl] with θ hθ hθ_mem
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
      obtain ⟨hne0, hneπ⟩ := hθ
      -- Extract bounds from uIoc
      have hθ_lo : -Real.pi < θ := by
        have := hθ_mem.1; rwa [min_eq_left hle_pi] at this
      have hθ_hi : θ ≤ Real.pi := by
        have := hθ_mem.2; rwa [max_eq_right hle_pi] at this
      have hθ_lt_π : θ < Real.pi := lt_of_le_of_ne hθ_hi hneπ
      rw [hcm_eq θ]
      have hcm_U' : cexp (↑θ * I) ∈ U := by rw [← hcm_eq]; exact hcm_U θ
      by_cases hθ_pos : (0 : ℝ) < θ
      · -- Case θ > 0: sin θ > 0, both sides = f_plus(Phi(smp(ζ, exp(iθ))))
        have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_π
        have him : 0 < (cexp (↑θ * I)).im := by rwa [Complex.exp_ofReal_mul_I_im]
        have hmem : cexp (↑θ * I) ∈ U ∩ EOW.UpperHalfPlane := ⟨hcm_U', him⟩
        simp only [G, if_pos hsin_pos]
        rw [hF_gp _ hmem]
        simp only [gp, if_pos him]
      · -- Case θ ≤ 0, θ ≠ 0 ⟹ θ < 0: sin θ < 0
        have hθ_neg : θ < 0 := lt_of_le_of_ne (not_lt.mp hθ_pos) hne0
        have hsin_neg : Real.sin θ < 0 := by
          have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hθ_neg) (by linarith)
          linarith [Real.sin_neg θ]
        have him : (cexp (↑θ * I)).im < 0 := by rwa [Complex.exp_ofReal_mul_I_im]
        have hmem : cexp (↑θ * I) ∈ U ∩ EOW.LowerHalfPlane := ⟨hcm_U', him⟩
        simp only [G, if_neg (not_lt.mpr (le_of_lt hsin_neg)), if_pos hsin_neg]
        rw [hF_gm _ hmem]
        simp only [gm, if_pos him]
    -- Periodicity: F_disc ∘ circleMap 0 1 has period 2π
    have hperiodic : Function.Periodic (fun θ => F_disc (circleMap 0 1 θ)) (2 * Real.pi) :=
      fun θ => congr_arg F_disc (periodic_circleMap 0 1 θ)
    -- Shift integration domain from (-π, π) to (0, 2π)
    have hshift := hperiodic.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi from by ring,
        show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi from by ring] at hshift
    -- Combine: replace integrand a.e., then shift domain
    rw [intervalIntegral.integral_congr_ae hae, hshift]
  -- Combine
  rw [hresult, hmv, hF0]

-- rudin_mean_value_pos and rudin_mean_value_neg have been moved to
-- deprecated/rudin_mean_value_pos_neg.lean (they are no longer called;
-- the 1D line argument in rudin_orthant_extension bypasses them).

set_option maxHeartbeats 800000 in
/-- Rudin's Möbius integral extension in orthant coordinates.

    Given f_plus holomorphic on T(C) and f_minus on T(-C), with matching
    boundary values bv on E, there exists a holomorphic function F₀ on a
    neighborhood of 0 in w-coordinates (the orthant coordinates determined by
    m linearly independent vectors in C) that agrees with f_plus ∘ Phi on
    the positive orthant and with f_minus ∘ Phi on the negative orthant.

    The construction: F₀(w) = (1/2π) ∫_{-π}^{π} K(moebiusProd(w, e^{iθ}), θ) dθ
    where K dispatches to f_plus ∘ Phi or f_minus ∘ Phi based on sign of sin(θ).

    Holomorphicity: for each fixed θ, the integrand is holomorphic in w
    (composition of moebiusProd, Phi, and f_±). By Morera/Leibniz, the integral
    is holomorphic. Agreement: by the 1D edge-of-wedge theorem, the function
    λ ↦ K(moebiusProd(w, λ)) is holomorphic in the disc. The mean value
    property then gives F₀(w) = K(w) = f_±(Phi(w)) on the orthant tubes.

    References: Rudin, "Lectures on the edge-of-the-wedge theorem", §4. -/
private lemma rudin_orthant_extension {m : ℕ} (hm : 0 < m) (_hm2 : 2 ≤ m)
    (C : Set (Fin m → ℝ)) (_hC : IsOpen C) (hconv : Convex ℝ C)
    (_h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (_hCne : C.Nonempty)
    (x₀ : Fin m → ℝ) (ys : Fin m → (Fin m → ℝ))
    (hys_mem : ∀ k, ys k ∈ C) (_hys_li : LinearIndependent ℝ ys)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (_hE : IsOpen E) (_hx₀ : x₀ ∈ E)
    (_bv : (Fin m → ℝ) → ℂ) (_hbv_cont : ContinuousOn _bv E)
    (_hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (_bv x)))
    (_hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (_bv x))) :
    ∃ (ρ : ℝ), 0 < ρ ∧
      ∃ F₀ : (Fin m → ℂ) → ℂ,
        DifferentiableOn ℂ F₀ (Metric.ball 0 ρ) ∧
        (∀ w ∈ Metric.ball (0 : Fin m → ℂ) ρ,
          Phi x₀ ys w ∈ TubeDomain C → F₀ w = f_plus (Phi x₀ ys w)) ∧
        (∀ w ∈ Metric.ball (0 : Fin m → ℂ) ρ,
          Phi x₀ ys w ∈ TubeDomain (Neg.neg '' C) →
            F₀ w = f_minus (Phi x₀ ys w)) := by
  -- Step 0: Choose δ > 0 so that all Möbius images stay near x₀ (in E at boundary).
  -- The affine map A(v) = x₀ + M·v is continuous at 0 and maps 0 to x₀ ∈ E.
  -- By openness of E, there exists ε > 0 such that A(ball(0,ε)) ⊂ E.
  -- Set δ = ε/7: since ‖moebiusProd‖ ≤ 6, the scaled images have ‖smp_j‖ ≤ 6δ < ε.
  -- This ensures boundary images Re(Phi(smp)) ∈ E, giving us a bound on f_plus via bv.
  have hA_cont : Continuous (fun v : Fin m → ℝ => fun i => x₀ i + ∑ j, v j * (ys j) i) :=
    continuous_pi fun i => continuous_const.add
      (continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const)
  have hA_zero : (fun v : Fin m → ℝ => fun i => x₀ i + ∑ j, v j * (ys j) i) 0 = x₀ := by
    ext i; simp
  obtain ⟨ε, hε_pos, hε_sub⟩ : ∃ ε > 0, Metric.ball (0 : Fin m → ℝ) ε ⊆
      (fun v : Fin m → ℝ => fun i => x₀ i + ∑ j, v j * (ys j) i) ⁻¹' E := by
    have h_mem : (fun v : Fin m → ℝ => fun i => x₀ i + ∑ j, v j * (ys j) i) ⁻¹' E ∈
        nhds (0 : Fin m → ℝ) := by
      apply hA_cont.continuousAt.preimage_mem_nhds
      convert _hE.mem_nhds _hx₀ using 2
    exact Metric.nhds_basis_ball.mem_iff.mp h_mem
  set δ := ε / 11 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_ne : (↑δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hδ_pos)
  refine ⟨δ / 2, by positivity, ?_⟩
  -- Helper: w ∈ ball(0, δ/2) → ‖w_j/δ‖ < 1 for all j (needed for Möbius map)
  have ball_comp_lt_one : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
      ∀ j, ‖w j / (↑δ : ℂ)‖ < 1 := by
    intro w hw j
    rw [Metric.mem_ball, dist_zero_right] at hw
    have : ‖(↑δ : ℂ)‖ = δ := by
      simp [Complex.norm_real, abs_of_pos hδ_pos]
    rw [norm_div, this]
    calc ‖w j‖ / δ ≤ ‖w‖ / δ := by gcongr; exact norm_le_pi_norm w j
      _ < (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  -- Helper: ‖w_j/δ‖ ≤ 1 (non-strict, for norm bounds)
  have ball_comp_le_one : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
      ∀ j, ‖w j / (↑δ : ℂ)‖ ≤ 1 := by
    intro w hw j; exact le_of_lt (ball_comp_lt_one w hw j)
  -- Scaled Möbius product: smp(w, λ)_j = δ · moebiusRudin(w_j/δ, λ)
  -- Key properties:
  --   (1) smp(w, 0) = w  (by moebiusRudin_zero_right)
  --   (2) ‖smp(w,λ)_j‖ ≤ 6δ < ε  (by moebiusRudin_norm_le)
  --   (3) On unit circle: Im(smp_j) > 0 ⟺ sin θ > 0  (by moebiusRudin_im_pos_iff)
  --   (4) The scaling ensures boundary images Re(Phi(smp)) stay in E.
  let smp : (Fin m → ℂ) → ℂ → (Fin m → ℂ) :=
    fun w l j => (↑δ : ℂ) * moebiusProd (fun k => w k / (↑δ : ℂ)) l j
  -- Verify smp(w, 0) = w
  have smp_zero : ∀ w, smp w 0 = w := by
    intro w; ext j
    show (↑δ : ℂ) * moebiusProd (fun k => w k / (↑δ : ℂ)) 0 j = w j
    have h_mp0 := moebiusProd_zero_right (fun k => w k / (↑δ : ℂ))
    rw [h_mp0]
    exact (mul_comm _ _).trans (div_mul_cancel₀ _ hδ_ne)
  -- Helper: θ ↦ smp(w, e^{iθ}) is continuous for w ∈ ball(0, δ/2)
  have smp_theta_continuous : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
      Continuous (fun θ : ℝ => smp w (cexp ((↑θ : ℂ) * I))) := by
    intro w hw
    apply continuous_pi fun j => ?_
    show Continuous (fun θ : ℝ =>
      (↑δ : ℂ) * moebiusRudin (w j / (↑δ : ℂ)) (cexp ((↑θ : ℂ) * I)))
    exact continuous_const.mul
      (moebiusRudin_continuousOn.comp_continuous
        (continuous_const.prodMk ((Complex.continuous_ofReal.mul continuous_const).cexp))
        fun θ => Set.mem_prod.mpr
          ⟨by rw [Metric.mem_ball, dist_zero_right]; exact ball_comp_lt_one w hw j,
           by rw [Metric.mem_closedBall, dist_zero_right]
              exact (Complex.norm_exp_ofReal_mul_I θ).le⟩)
  -- The integrand G dispatches to f_plus or f_minus based on sign of sin θ.
  -- On the unit circle, for ‖w_j/δ‖ < 1:
  --   sin θ > 0 → all Im(smp_j) > 0 → Phi(smp) ∈ T(C) → f_plus applies
  --   sin θ < 0 → all Im(smp_j) < 0 → Phi(smp) ∈ T(-C) → f_minus applies
  let G : (Fin m → ℂ) → ℝ → ℂ := fun w θ =>
    if 0 < Real.sin θ then
      f_plus (Phi x₀ ys (smp w (Complex.exp ((θ : ℂ) * I))))
    else if Real.sin θ < 0 then
      f_minus (Phi x₀ ys (smp w (Complex.exp ((θ : ℂ) * I))))
    else 0
  -- F₀ = (1/2π) ∫_{-π}^{π} G(w, θ) dθ  (the scaled Rudin-Möbius circle integral)
  let F₀ : (Fin m → ℂ) → ℂ := fun w =>
    (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G w θ
  -- Extract DifferentiableOn as a hypothesis for use in Goals 2 and 3.
  have hF₀_diff : DifferentiableOn ℂ F₀ (Metric.ball 0 (δ / 2)) := by
    -- Uniform bound on G (needed for both ContinuousOn and separately holomorphic)
    have G_bound : ∃ M : ℝ, ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        ∀ θ : ℝ, ‖G w θ‖ ≤ M := by
        -- Bound G by constructing a continuous extension h on the compact set
        -- closedBall × sphere, then applying IsCompact.exists_bound_of_continuousOn.
        -- Helper: closedBall component bounds
        have hδ_cnorm : ‖(↑δ : ℂ)‖ = δ := by
          simp [Complex.norm_real, abs_of_pos hδ_pos]
        have cball_comp_le : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
            ∀ j, ‖w j / (↑δ : ℂ)‖ ≤ 1 := by
          intro w hw j
          rw [Metric.mem_closedBall, dist_zero_right] at hw
          rw [norm_div, hδ_cnorm]
          exact (div_le_one hδ_pos).mpr ((norm_le_pi_norm w j).trans (hw.trans (by linarith)))
        have cball_comp_le_half : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
            ∀ j, ‖w j / (↑δ : ℂ)‖ ≤ 1 / 2 := by
          intro w hw j
          rw [Metric.mem_closedBall, dist_zero_right] at hw
          rw [norm_div, hδ_cnorm]
          calc ‖w j‖ / δ ≤ ‖w‖ / δ := by gcongr; exact norm_le_pi_norm w j
            _ ≤ (δ / 2) / δ := by gcongr
            _ = 1 / 2 := by field_simp
        have cball_comp_lt : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
            ∀ j, ‖w j / (↑δ : ℂ)‖ < 1 := by
          intro w hw j; linarith [cball_comp_le_half w hw j]
        -- Helper: sphere norm
        have sphere_norm : ∀ l ∈ Metric.sphere (0 : ℂ) 1, ‖l‖ = 1 := by
          intro l hl; rwa [← dist_zero_right]
        -- Helper: smp Im = 0 at real unit boundary
        have smp_im_zero : ∀ w (l : ℂ), Complex.normSq l = 1 → l.im = 0 →
            ∀ j, (smp w l j).im = 0 := by
          intro w l hl_norm hl_im j
          show ((↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j).im = 0
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          exact mul_eq_zero_of_right _ (moebiusProd_real_of_unit_real hl_norm hl_im j)
        -- Helper: Re(Phi(z)_i) = x₀_i + ∑_j Re(z_j) * ys_j_i
        have Phi_re_eq : ∀ (z : Fin m → ℂ) (i : Fin m),
            (Phi x₀ ys z i).re = x₀ i + ∑ j, (z j).re * (ys j) i := by
          intro z i; simp only [Phi, Complex.add_re, Complex.ofReal_re]
          congr 1; trans ∑ j : Fin m, (z j * ↑(ys j i)).re
          · exact map_sum Complex.reCLM _ _
          · congr 1; ext j; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        -- Helper: Re(Phi(smp(w,l))) ∈ E
        have phi_re_in_E : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
            ∀ l, ‖l‖ ≤ 2 → (fun i => (Phi x₀ ys (smp w l) i).re) ∈ E := by
          intro w hw l hl
          suffices h : (fun j => (smp w l j).re) ∈ Metric.ball (0 : Fin m → ℝ) ε by
            have := hε_sub h; simp only [Set.mem_preimage] at this
            convert this using 1; ext i; exact Phi_re_eq (smp w l) i
          rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε_pos]
          intro j; rw [Real.norm_eq_abs]
          calc |(smp w l j).re| ≤ ‖smp w l j‖ := Complex.abs_re_le_norm _
            _ ≤ δ * 10 := by
                show ‖(↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j‖ ≤ _
                rw [norm_mul, hδ_cnorm]
                exact mul_le_mul_of_nonneg_left
                  (moebiusProd_norm_le_extended (cball_comp_le_half w hw) hl j) hδ_pos.le
            _ < ε := by rw [hδ_def]; linarith
        -- Helper: Phi(smp) = realEmbed(Re(Phi(smp))) at real unit boundary
        have phi_smp_realEmbed : ∀ w (l : ℂ), Complex.normSq l = 1 → l.im = 0 →
            Phi x₀ ys (smp w l) = realEmbed (fun i => (Phi x₀ ys (smp w l) i).re) := by
          intro w l hl_norm hl_im; ext i; apply Complex.ext
          · simp [realEmbed, Complex.ofReal_re]
          · rw [show (realEmbed (fun i => (Phi x₀ ys (smp w l) i).re) i).im = 0 from
                Complex.ofReal_im _, Phi_im]
            simp only [smp_im_zero w l hl_norm hl_im, zero_mul, Finset.sum_const_zero]
        -- Helper: normSq from sphere norm
        have sphere_normSq : ∀ l ∈ Metric.sphere (0 : ℂ) 1, Complex.normSq l = 1 := by
          intro l hl
          have h := sphere_norm l hl
          rw [Complex.normSq_eq_norm_sq, h]; norm_num
        -- Helper: Phi ∘ smp ContinuousOn (closedBall ×ˢ closedBall(0,1))
        have phi_smp_cont : ContinuousOn (fun p : (Fin m → ℂ) × ℂ =>
            Phi x₀ ys (smp p.1 p.2))
            (Metric.closedBall 0 (δ / 2) ×ˢ Metric.closedBall 0 1) := by
          apply (Phi_differentiable x₀ ys).continuous.comp_continuousOn
          apply continuousOn_pi.mpr; intro j
          show ContinuousOn (fun p : (Fin m → ℂ) × ℂ =>
            (↑δ : ℂ) * moebiusProd (fun k => p.1 k / ↑δ) p.2 j) _
          have h_proj : ContinuousOn (fun p : (Fin m → ℂ) × ℂ => (p.1 j / ↑δ, p.2))
              (Metric.closedBall 0 (δ / 2) ×ˢ Metric.closedBall 0 1) :=
            (((continuous_apply j).comp continuous_fst).div_const _ |>.prodMk
              continuous_snd).continuousOn
          have h_maps : Set.MapsTo (fun p : (Fin m → ℂ) × ℂ => (p.1 j / ↑δ, p.2))
              (Metric.closedBall 0 (δ / 2) ×ˢ Metric.closedBall 0 1)
              (Metric.ball 0 1 ×ˢ Metric.closedBall 0 1) := by
            intro ⟨w, l⟩ ⟨hw, hl⟩
            exact ⟨by rw [Metric.mem_ball, dist_zero_right]; exact cball_comp_lt w hw j,
              by rwa [Metric.mem_closedBall, dist_zero_right] at hl ⊢⟩
          exact continuousOn_const.mul (moebiusRudin_continuousOn.comp h_proj h_maps)
        -- Helper: Re ∘ Phi ∘ smp is ContinuousOn
        have re_phi_smp_cont : ContinuousOn (fun p : (Fin m → ℂ) × ℂ =>
            (fun i => (Phi x₀ ys (smp p.1 p.2) i).re))
            (Metric.closedBall 0 (δ / 2) ×ˢ Metric.closedBall 0 1) :=
          continuousOn_pi.mpr fun i =>
            Complex.continuous_re.comp_continuousOn
              ((continuous_apply i).comp_continuousOn phi_smp_cont)
        -- Helper: smp maps closedBall × {Im(l) > 0 on sphere} into T(C)
        have smp_pos_tube : ∀ p : (Fin m → ℂ) × ℂ,
            p ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1 →
            0 < p.2.im →
            Phi x₀ ys (smp p.1 p.2) ∈ TubeDomain C := by
          intro ⟨w, l⟩ ⟨hw, hl⟩ h_im
          apply Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem; intro j
          show 0 < ((↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j).im
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          exact mul_pos hδ_pos (moebiusProd_im_pos (cball_comp_lt w hw)
            (sphere_norm l hl) h_im j)
        have smp_neg_tube : ∀ p : (Fin m → ℂ) × ℂ,
            p ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1 →
            p.2.im < 0 →
            Phi x₀ ys (smp p.1 p.2) ∈ TubeDomain (Neg.neg '' C) := by
          intro ⟨w, l⟩ ⟨hw, hl⟩ h_im
          apply Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem; intro j
          show ((↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j).im < 0
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          exact mul_neg_of_pos_of_neg hδ_pos (moebiusProd_im_neg (cball_comp_lt w hw)
            (sphere_norm l hl) h_im j)
        -- Define the continuous extension h
        let h : (Fin m → ℂ) × ℂ → ℂ := fun ⟨w, l⟩ =>
          if 0 < l.im then f_plus (Phi x₀ ys (smp w l))
          else if l.im < 0 then f_minus (Phi x₀ ys (smp w l))
          else _bv (fun i => (Phi x₀ ys (smp w l) i).re)
        set S := Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1
        have hS_cpt : IsCompact S := (isCompact_closedBall (x := (0 : Fin m → ℂ)) (r := δ / 2)).prod (isCompact_sphere _ _)
        have hS_ne : S.Nonempty := ⟨(0, 1),
          Metric.mem_closedBall.mpr (by simp; positivity),
          Metric.mem_sphere.mpr (by simp [dist_zero_right])⟩
        -- ContinuousOn h S
        have h_cont : ContinuousOn h S := by
          intro ⟨w₀, l₀⟩ ⟨hw₀, hl₀⟩
          -- Phi ∘ smp is ContinuousWithinAt on S (from larger domain)
          have hS_sub : S ⊆ Metric.closedBall 0 (δ / 2) ×ˢ Metric.closedBall 0 1 :=
            Set.prod_mono le_rfl Metric.sphere_subset_closedBall
          have h_phi_cwa : ContinuousWithinAt (fun p : (Fin m → ℂ) × ℂ =>
              Phi x₀ ys (smp p.1 p.2)) S (w₀, l₀) :=
            (phi_smp_cont.mono hS_sub).continuousWithinAt ⟨hw₀, hl₀⟩
          -- Tube domain openness
          have h_tube_open : IsOpen (TubeDomain C) := tubeDomain_isOpen _hC
          have h_neg_tube_open : IsOpen (TubeDomain (Neg.neg '' C)) := by
            convert tubeDomain_isOpen (_hC.neg) using 1
            ext z; simp only [TubeDomain, Set.mem_setOf_eq, Set.image_neg_eq_neg]
          -- Open sets for im > 0 and im < 0 (used in all cases)
          have him_pos_open : IsOpen {p : (Fin m → ℂ) × ℂ | (0 : ℝ) < p.2.im} :=
            isOpen_lt continuous_const (continuous_im.comp continuous_snd)
          have him_neg_open : IsOpen {p : (Fin m → ℂ) × ℂ | p.2.im < (0 : ℝ)} :=
            isOpen_lt (continuous_im.comp continuous_snd) continuous_const
          by_cases h_pos : 0 < l₀.im
          · -- Case 1: l₀.im > 0 — h locally agrees with f_plus ∘ Phi ∘ smp
            have h_ev : h =ᶠ[nhdsWithin (w₀, l₀) S]
                fun p => f_plus (Phi x₀ ys (smp p.1 p.2)) := by
              filter_upwards [nhdsWithin_le_nhds (him_pos_open.mem_nhds h_pos)]
                with ⟨w, l⟩ him
              exact if_pos him
            exact (((hf_plus.differentiableAt (h_tube_open.mem_nhds
              (smp_pos_tube _ ⟨hw₀, hl₀⟩ h_pos))).continuousAt
              ).comp_continuousWithinAt
              (f := fun (p : (Fin m → ℂ) × ℂ) => Phi x₀ ys (smp p.1 p.2))
              h_phi_cwa).congr_of_eventuallyEq h_ev
              (show h (w₀, l₀) = _ from if_pos h_pos)
          · by_cases h_neg : l₀.im < 0
            · -- Case 2: l₀.im < 0 — h locally agrees with f_minus ∘ Phi ∘ smp
              have h_ev : h =ᶠ[nhdsWithin (w₀, l₀) S]
                  fun p => f_minus (Phi x₀ ys (smp p.1 p.2)) := by
                filter_upwards [nhdsWithin_le_nhds (him_neg_open.mem_nhds h_neg)]
                  with ⟨w, l⟩ him
                simp only [h, if_neg (not_lt.mpr him.le), if_pos him]
              exact (((hf_minus.differentiableAt (h_neg_tube_open.mem_nhds
                (smp_neg_tube _ ⟨hw₀, hl₀⟩ h_neg))).continuousAt
                ).comp_continuousWithinAt
                (f := fun (p : (Fin m → ℂ) × ℂ) => Phi x₀ ys (smp p.1 p.2))
                h_phi_cwa).congr_of_eventuallyEq h_ev
                (show h (w₀, l₀) = _ from by
                  simp only [h, if_neg (not_lt.mpr h_neg.le), if_pos h_neg]; rfl)
            · -- Case 3: l₀.im = 0 (boundary point)
              have him : l₀.im = 0 :=
                le_antisymm (not_lt.mp h_pos) (not_lt.mp h_neg)
              set x₀' := fun i => (Phi x₀ ys (smp w₀ l₀) i).re
              have hx₀'E : x₀' ∈ E :=
                phi_re_in_E w₀ hw₀ l₀ ((sphere_norm l₀ hl₀).le.trans (by norm_num))
              have h_val : h (w₀, l₀) = _bv x₀' := by
                show (if 0 < l₀.im then _ else if l₀.im < 0 then _ else _) = _
                rw [if_neg h_pos, if_neg h_neg]
              have h_phi_real : Phi x₀ ys (smp w₀ l₀) = realEmbed x₀' :=
                phi_smp_realEmbed w₀ l₀ (sphere_normSq l₀ hl₀) him
              -- CWA on {im > 0}: f_plus → _bv x₀' via boundary values
              have cwa_pos : ContinuousWithinAt h
                  (S ∩ {p | 0 < p.2.im}) (w₀, l₀) := by
                show Filter.Tendsto h _ (nhds (h (w₀, l₀)))
                rw [h_val]
                have h_maps : Set.MapsTo (fun p : (Fin m → ℂ) × ℂ =>
                    Phi x₀ ys (smp p.1 p.2)) (S ∩ {p | 0 < p.2.im}) (TubeDomain C) :=
                  fun p hp => smp_pos_tube p hp.1 hp.2
                have h_tendsto := (h_phi_cwa.mono
                  Set.inter_subset_left).tendsto_nhdsWithin h_maps
                rw [h_phi_real] at h_tendsto
                exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
                  fun p hp => show h p = _ from by
                    cases p with | mk w l => exact if_pos hp.2)).mpr
                  ((_hf_plus_bv x₀' hx₀'E).comp h_tendsto)
              -- CWA on {im < 0}: f_minus → _bv x₀' via boundary values
              have cwa_neg : ContinuousWithinAt h
                  (S ∩ {p | p.2.im < 0}) (w₀, l₀) := by
                show Filter.Tendsto h _ (nhds (h (w₀, l₀)))
                rw [h_val]
                have h_maps : Set.MapsTo (fun p : (Fin m → ℂ) × ℂ =>
                    Phi x₀ ys (smp p.1 p.2)) (S ∩ {p | p.2.im < 0})
                    (TubeDomain (Neg.neg '' C)) :=
                  fun p hp => smp_neg_tube p hp.1 hp.2
                have h_tendsto := (h_phi_cwa.mono
                  Set.inter_subset_left).tendsto_nhdsWithin h_maps
                rw [h_phi_real] at h_tendsto
                exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
                  fun p hp => show h p = _ from by
                    cases p with | mk w l =>
                      have him : l.im < 0 := hp.2
                      simp only [h, if_neg (not_lt.mpr him.le), if_pos him]; rfl)).mpr
                  ((_hf_minus_bv x₀' hx₀'E).comp h_tendsto)
              -- CWA on {im = 0}: _bv ∘ Re ∘ Phi ∘ smp is continuous
              have cwa_zero : ContinuousWithinAt h
                  (S ∩ {p | p.2.im = 0}) (w₀, l₀) := by
                show Filter.Tendsto h _ (nhds (h (w₀, l₀)))
                rw [h_val]
                have h_re_cwa : ContinuousWithinAt
                    (fun p : (Fin m → ℂ) × ℂ => fun i => (Phi x₀ ys (smp p.1 p.2) i).re)
                    (S ∩ {p | p.2.im = 0}) (w₀, l₀) :=
                  (re_phi_smp_cont.continuousWithinAt
                    (hS_sub ⟨hw₀, hl₀⟩)).mono
                    (Set.inter_subset_left.trans hS_sub)
                have h_re_maps : Set.MapsTo (fun p : (Fin m → ℂ) × ℂ =>
                    (fun i => (Phi x₀ ys (smp p.1 p.2) i).re))
                    (S ∩ {p | p.2.im = 0}) E :=
                  fun ⟨w, l⟩ ⟨⟨hw, hl⟩, _⟩ =>
                    phi_re_in_E w hw l ((sphere_norm l hl).le.trans (by norm_num))
                have h_composed : Filter.Tendsto
                    (fun p : (Fin m → ℂ) × ℂ =>
                      _bv (fun i => (Phi x₀ ys (smp p.1 p.2) i).re))
                    (nhdsWithin (w₀, l₀) (S ∩ {p | p.2.im = 0}))
                    (nhds (_bv x₀')) :=
                  Filter.Tendsto.comp
                    (_hbv_cont.continuousWithinAt hx₀'E)
                    (h_re_cwa.tendsto_nhdsWithin h_re_maps)
                exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
                  fun ⟨w, l⟩ ⟨_, him_mem⟩ =>
                    show h (w, l) =
                      _bv (fun i => (Phi x₀ ys (smp w l) i).re) from by
                    have him : l.im = 0 := him_mem
                    simp only [h, if_neg (not_lt.mpr (le_of_eq him)),
                      if_neg (not_lt.mpr (le_of_eq him.symm))])).mpr
                  h_composed
              -- Combine: S ⊆ (S ∩ {im > 0}) ∪ ((S ∩ {im < 0}) ∪ (S ∩ {im = 0}))
              exact (cwa_pos.union (cwa_neg.union cwa_zero)).mono
                (fun ⟨w, l⟩ hS => (lt_trichotomy l.im 0).elim
                  (fun h => Or.inr (Or.inl ⟨hS, h⟩))
                  (fun h => h.elim (fun h => Or.inr (Or.inr ⟨hS, h⟩))
                    (fun h => Or.inl ⟨hS, h⟩)))
        -- Extract bound
        obtain ⟨M, hM⟩ := hS_cpt.exists_bound_of_continuousOn h_cont
        have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM _ hS_ne.some_mem)
        refine ⟨M, fun w hw θ => ?_⟩
        set l := cexp ((↑θ : ℂ) * I) with hl_def
        have hl_sphere : l ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]; exact Complex.norm_exp_ofReal_mul_I θ
        have hwl : (w, l) ∈ S :=
          ⟨Metric.ball_subset_closedBall hw, hl_sphere⟩
        by_cases hsin_pos : 0 < Real.sin θ
        · -- sin θ > 0: G = h (both equal f_plus ∘ Phi ∘ smp)
          have hl_im : 0 < l.im := by
            show 0 < (cexp (↑θ * I)).im; rw [Complex.exp_ofReal_mul_I_im]; exact hsin_pos
          calc ‖G w θ‖ = ‖h (w, l)‖ := by
                simp only [G, h, if_pos hsin_pos, if_pos hl_im, ← hl_def]
            _ ≤ M := hM _ hwl
        · by_cases hsin_neg : Real.sin θ < 0
          · -- sin θ < 0: G = h (both equal f_minus ∘ Phi ∘ smp)
            have hl_im : l.im < 0 := by
              show (cexp (↑θ * I)).im < 0; rw [Complex.exp_ofReal_mul_I_im]; exact hsin_neg
            calc ‖G w θ‖ = ‖h (w, l)‖ := by
                  simp only [G, h, if_neg hsin_pos, if_pos hsin_neg,
                    if_neg (not_lt.mpr (le_of_lt hl_im)), if_pos hl_im, ← hl_def]
              _ ≤ M := hM _ hwl
          · -- sin θ = 0: G = 0
            simp only [G, if_neg hsin_pos, if_neg hsin_neg, norm_zero]
            exact hM_nn
    refine osgood_lemma Metric.isOpen_ball _ ?_ ?_
    · -- ContinuousOn F₀ (ball 0 (δ/2))
      obtain ⟨M, hM⟩ := G_bound
      -- ContinuousOn = ContinuousAt at each point (ball is open)
      intro w₀ hw₀
      apply ContinuousAt.continuousWithinAt
      show ContinuousAt (fun w => (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G w θ) w₀
      apply ContinuousAt.const_smul
      apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
      · -- AEStronglyMeasurable G w near w₀
        filter_upwards [Metric.isOpen_ball.mem_nhds hw₀] with w hw
        apply AEStronglyMeasurable.restrict
        -- G w is a nested piecewise of ContinuousOn functions on measurable sets
        have hs_pos : MeasurableSet {θ : ℝ | 0 < Real.sin θ} :=
          (isOpen_lt continuous_const Real.continuous_sin).measurableSet
        have hs_neg : MeasurableSet {θ : ℝ | Real.sin θ < 0} :=
          (isOpen_lt Real.continuous_sin continuous_const).measurableSet
        -- θ ↦ Phi(smp(w, e^{iθ})) is continuous
        have h_inner : Continuous (fun θ : ℝ => Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))) :=
          (Phi_differentiable x₀ ys).continuous.comp (smp_theta_continuous w hw)
        -- ContinuousOn for each branch (images stay in the respective tube domains)
        have hg_pos : AEStronglyMeasurable
            (fun θ : ℝ => f_plus (Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))))
            (volume.restrict {θ | 0 < Real.sin θ}) :=
          (hf_plus.continuousOn.comp h_inner.continuousOn fun θ hθ =>
            Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
              show 0 < ((↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) (cexp ((↑θ : ℂ) * I)) j).im
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_pos hδ_pos (moebiusProd_im_pos (ball_comp_lt_one w hw)
                (Complex.norm_exp_ofReal_mul_I θ)
                (by rwa [Complex.exp_ofReal_mul_I_im]) j)).aestronglyMeasurable hs_pos
        have hg_neg : AEStronglyMeasurable
            (fun θ : ℝ => f_minus (Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))))
            (volume.restrict {θ | Real.sin θ < 0}) :=
          (hf_minus.continuousOn.comp h_inner.continuousOn fun θ hθ =>
            Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
              show ((↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) (cexp ((↑θ : ℂ) * I)) j).im < 0
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_neg_of_pos_of_neg hδ_pos
                (moebiusProd_im_neg (ball_comp_lt_one w hw)
                  (Complex.norm_exp_ofReal_mul_I θ)
                  (by rwa [Complex.exp_ofReal_mul_I_im]) j)).aestronglyMeasurable hs_neg
        -- Nested piecewise: G w = {sin>0}.piecewise g_pos ({sin<0}.piecewise g_neg 0)
        -- Provide DecidablePred instances (noncomputable via Classical)
        letI : DecidablePred (· ∈ {θ : ℝ | 0 < Real.sin θ}) := fun _ => Classical.dec _
        letI : DecidablePred (· ∈ {θ : ℝ | Real.sin θ < 0}) := fun _ => Classical.dec _
        -- The piecewise may use different Decidable instances than G's if-then-else,
        -- so use .congr to handle the a.e. equality
        have G_unfold : ∀ w' θ, G w' θ =
            if 0 < Real.sin θ then f_plus (Phi x₀ ys (smp w' (cexp ((↑θ : ℂ) * I))))
            else if Real.sin θ < 0 then f_minus (Phi x₀ ys (smp w' (cexp ((↑θ : ℂ) * I))))
            else 0 := fun _ _ => rfl
        exact (hg_pos.piecewise hs_pos
          ((hg_neg.piecewise hs_neg
            (aestronglyMeasurable_const (b := (0 : ℂ)))).mono_measure
            Measure.restrict_le_self)).congr
          (Filter.Eventually.of_forall fun θ => by
            simp only [Set.piecewise, Set.mem_setOf_eq, G_unfold])
      · -- ‖G w θ‖ ≤ M near w₀
        filter_upwards [Metric.isOpen_ball.mem_nhds hw₀] with w hw
        filter_upwards with θ hθ
        exact hM w hw θ
      · -- Constant bound is interval integrable
        exact intervalIntegrable_const
      · -- Pointwise continuity: w ↦ G w θ is continuous at w₀ for a.e. θ
        filter_upwards with θ hθ
        -- Split by sign of sin θ (fixed, so the `if` reduces to one branch)
        -- Split by sign of sin θ (fixed, so the `if` reduces to one branch)
        set l := cexp ((θ : ℂ) * I)
        have hl_norm : ‖l‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
        -- Helper: ContinuousAt of smp(·, l) at w₀ (componentwise Möbius map)
        have h_smp_ca : ContinuousAt (fun x => smp x l) w₀ :=
          scaledMoebiusProd_continuousAt δ l hl_norm.le w₀ (ball_comp_lt_one w₀ hw₀)
        by_cases hsin_pos : 0 < Real.sin θ
        · -- sin θ > 0: G(·, θ) = f_plus ∘ Phi ∘ smp(·, l)
          have hG_eq : (fun x => G x θ) = fun x => f_plus (Phi x₀ ys (smp x l)) := by
            ext x; exact if_pos hsin_pos
          rw [hG_eq]
          have hl_im : 0 < l.im := by
            show 0 < (cexp (↑θ * I)).im; rw [Complex.exp_ofReal_mul_I_im]; exact hsin_pos
          have h_smp_im_pos : ∀ j, 0 < (smp w₀ l j).im := by
            intro j
            show 0 < ((↑δ : ℂ) * moebiusProd (fun k => w₀ k / ↑δ) l j).im
            rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
            exact mul_pos hδ_pos (moebiusProd_im_pos (ball_comp_lt_one w₀ hw₀) hl_norm hl_im j)
          exact ContinuousAt.comp
            (f := fun x => Phi x₀ ys (smp x l)) (g := f_plus)
            (hf_plus.continuousOn.continuousAt
              ((tubeDomain_isOpen _hC).mem_nhds
                (Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ h_smp_im_pos)))
            (ContinuousAt.comp (f := fun x => smp x l) (g := Phi x₀ ys)
              ((Phi_differentiable x₀ ys).continuous.continuousAt) h_smp_ca)
        · by_cases hsin_neg : Real.sin θ < 0
          · -- sin θ < 0: G(·, θ) = f_minus ∘ Phi ∘ smp(·, l)
            have hG_eq : (fun x => G x θ) = fun x => f_minus (Phi x₀ ys (smp x l)) := by
              ext x; exact (if_neg hsin_pos).trans (if_pos hsin_neg)
            rw [hG_eq]
            have hl_im : l.im < 0 := by
              show (cexp (↑θ * I)).im < 0; rw [Complex.exp_ofReal_mul_I_im]; exact hsin_neg
            have h_smp_im_neg : ∀ j, (smp w₀ l j).im < 0 := by
              intro j
              show ((↑δ : ℂ) * moebiusProd (fun k => w₀ k / ↑δ) l j).im < 0
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_neg_of_pos_of_neg hδ_pos
                (moebiusProd_im_neg (ball_comp_lt_one w₀ hw₀) hl_norm hl_im j)
            exact ContinuousAt.comp
              (f := fun x => Phi x₀ ys (smp x l)) (g := f_minus)
              (hf_minus.continuousOn.continuousAt
                ((by convert tubeDomain_isOpen (_hC.neg) using 1
                     ext z; simp only [TubeDomain, Set.mem_setOf_eq, Set.image_neg_eq_neg]
                  : IsOpen (TubeDomain (Neg.neg '' C))).mem_nhds
                  (Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ h_smp_im_neg)))
              (ContinuousAt.comp (f := fun x => smp x l) (g := Phi x₀ ys)
                ((Phi_differentiable x₀ ys).continuous.continuousAt) h_smp_ca)
          · -- sin θ = 0: G(·, θ) = 0
            have hG_eq : (fun x => G x θ) = fun _ => 0 := by
              ext x; exact (if_neg hsin_pos).trans (if_neg hsin_neg)
            rw [hG_eq]; exact continuousAt_const
    · -- Separately holomorphic: ∀ z ∈ ball, ∀ j, DifferentiableAt ℂ (fun ζ => F₀ (update z j ζ)) (z j)
      -- For fixed θ with sin θ ≠ 0, ζ ↦ G(update z j ζ, θ) is holomorphic
      -- (composition of holomorphic maps: moebiusProd, Phi, f_±).
      -- Leibniz rule (hasDerivAt_integral_of_dominated_loc_of_lip) with a
      -- Leibniz rule + Cauchy estimate.
      intro z hz j
      obtain ⟨M, hM⟩ := G_bound
      show DifferentiableAt ℂ
        (fun ζ => (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi,
          G (Function.update z j ζ) θ) (z j)
      suffices h_int : DifferentiableAt ℂ
          (fun ζ => ∫ θ in (-Real.pi)..Real.pi, G (Function.update z j ζ) θ) (z j) by
        set_option backward.isDefEq.respectTransparency false in
        exact h_int.const_smul ((2 * Real.pi)⁻¹ : ℝ)
      -- Neighborhood setup
      have hz_norm : ‖z‖ < δ / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hz
      set ε' := (δ / 2 - ‖z‖) / 4 with hε'_def
      have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
      -- update z j ζ ∈ ball(0, δ/2) for ζ ∈ closedBall(z j, 2ε')
      have h_upd : ∀ ζ, dist ζ (z j) ≤ 2 * ε' →
          Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
        intro ζ hζ; rw [Metric.mem_ball, dist_zero_right]
        have hζ_norm : ‖ζ‖ < δ / 2 := calc
          ‖ζ‖ ≤ ‖z j‖ + ‖ζ - z j‖ := norm_le_insert' ζ (z j)
          _ = ‖z j‖ + dist ζ (z j) := by rw [dist_eq_norm]
          _ ≤ ‖z‖ + 2 * ε' := by linarith [norm_le_pi_norm z j]
          _ < δ / 2 := by rw [hε'_def]; linarith
        refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_)
          (max_lt hz_norm hζ_norm)
        by_cases hjk : k = j
        · subst hjk; rw [Function.update_self]; exact le_max_right _ _
        · rw [Function.update_of_ne hjk]
          exact (norm_le_pi_norm z k).trans (le_max_left _ _)
      -- For t ∈ ball(z j, ε'), closedBall(t, ε') maps into ball via update
      have h_upd_t : ∀ t ∈ Metric.ball (z j) ε', ∀ ζ ∈ Metric.closedBall t ε',
          Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
        intro t ht ζ hζ; apply h_upd
        calc dist ζ (z j) ≤ dist ζ t + dist t (z j) := dist_triangle _ _ _
          _ ≤ ε' + ε' := by linarith [Metric.mem_closedBall.mp hζ, (Metric.mem_ball.mp ht).le]
          _ = 2 * ε' := by ring
      -- G(w, ·) is AEStronglyMeasurable for w ∈ ball(0, δ/2)
      have h_G_meas : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
          AEStronglyMeasurable (G w)
            (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
        intro w hw; apply AEStronglyMeasurable.restrict
        have hs_pos : MeasurableSet {θ : ℝ | 0 < Real.sin θ} :=
          (isOpen_lt continuous_const Real.continuous_sin).measurableSet
        have hs_neg : MeasurableSet {θ : ℝ | Real.sin θ < 0} :=
          (isOpen_lt Real.continuous_sin continuous_const).measurableSet
        have h_inner : Continuous (fun θ : ℝ => Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))) :=
          (Phi_differentiable x₀ ys).continuous.comp (smp_theta_continuous w hw)
        have hg_pos : AEStronglyMeasurable
            (fun θ : ℝ => f_plus (Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))))
            (MeasureTheory.volume.restrict {θ | 0 < Real.sin θ}) :=
          (hf_plus.continuousOn.comp h_inner.continuousOn fun θ hθ =>
            Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ fun k => by
              show 0 < ((↑δ : ℂ) * moebiusProd (fun i => w i / ↑δ) (cexp ((↑θ : ℂ) * I)) k).im
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_pos hδ_pos (moebiusProd_im_pos (ball_comp_lt_one w hw)
                (Complex.norm_exp_ofReal_mul_I θ) (by rwa [Complex.exp_ofReal_mul_I_im]) k)
            ).aestronglyMeasurable hs_pos
        have hg_neg : AEStronglyMeasurable
            (fun θ : ℝ => f_minus (Phi x₀ ys (smp w (cexp ((↑θ : ℂ) * I)))))
            (MeasureTheory.volume.restrict {θ | Real.sin θ < 0}) :=
          (hf_minus.continuousOn.comp h_inner.continuousOn fun θ hθ =>
            Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ fun k => by
              show ((↑δ : ℂ) * moebiusProd (fun i => w i / ↑δ) (cexp ((↑θ : ℂ) * I)) k).im < 0
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_neg_of_pos_of_neg hδ_pos (moebiusProd_im_neg (ball_comp_lt_one w hw)
                (Complex.norm_exp_ofReal_mul_I θ) (by rwa [Complex.exp_ofReal_mul_I_im]) k)
            ).aestronglyMeasurable hs_neg
        letI : DecidablePred (· ∈ {θ : ℝ | 0 < Real.sin θ}) := fun _ => Classical.dec _
        letI : DecidablePred (· ∈ {θ : ℝ | Real.sin θ < 0}) := fun _ => Classical.dec _
        exact (hg_pos.piecewise hs_pos
          ((hg_neg.piecewise hs_neg
            (aestronglyMeasurable_const (b := (0 : ℂ)))).mono_measure
            MeasureTheory.Measure.restrict_le_self)).congr
          (Filter.Eventually.of_forall fun θ => by
            simp only [Set.piecewise, Set.mem_setOf_eq]; rfl)
      -- DifferentiableAt of ζ ↦ G(update z j ζ, θ) for sin θ ≠ 0
      have h_G_diffAt : ∀ θ : ℝ, Real.sin θ ≠ 0 → ∀ t,
          Function.update z j t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) →
          DifferentiableAt ℂ (fun ζ => G (Function.update z j ζ) θ) t := by
        intro θ hsin t ht
        set l := cexp ((θ : ℂ) * I)
        have hl : ‖l‖ ≤ 1 := (Complex.norm_exp_ofReal_mul_I θ).le
        -- ζ ↦ smp(update z j ζ, l) is DifferentiableAt
        have h_smp_diff : DifferentiableAt ℂ
            (fun ζ => smp (Function.update z j ζ) l) t := by
          rw [differentiableAt_pi]; intro k
          show DifferentiableAt ℂ
            (fun ζ => (↑δ : ℂ) * moebiusRudin ((Function.update z j ζ k) / ↑δ) l) t
          by_cases hjk : k = j
          · subst hjk; simp only [Function.update_self]
            exact (differentiableAt_const _).mul
              ((moebiusRudin_differentiable_w l hl).differentiableAt
                (Metric.isOpen_ball.mem_nhds (by
                  rw [Metric.mem_ball, dist_zero_right]
                  simpa [Function.update_self] using ball_comp_lt_one _ ht k))
              |>.comp _ (differentiableAt_id.div (differentiableAt_const _) hδ_ne))
          · simp only [Function.update_of_ne hjk]
            exact differentiableAt_const _
        by_cases hsin_pos : 0 < Real.sin θ
        · -- sin θ > 0: G = f_plus ∘ Phi ∘ smp
          have hG_eq : (fun ζ => G (Function.update z j ζ) θ) =
              fun ζ => f_plus (Phi x₀ ys (smp (Function.update z j ζ) l)) := by
            ext ζ; exact if_pos hsin_pos
          rw [hG_eq]
          have h_tube : Phi x₀ ys (smp (Function.update z j t) l) ∈ TubeDomain C :=
            Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ fun k => by
              show 0 < ((↑δ : ℂ) * moebiusProd
                (fun i => (Function.update z j t) i / ↑δ) l k).im
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_pos hδ_pos (moebiusProd_im_pos (ball_comp_lt_one _ ht)
                (Complex.norm_exp_ofReal_mul_I θ)
                (by rwa [Complex.exp_ofReal_mul_I_im]) k)
          have h_phi_smp : DifferentiableAt ℂ
              (fun ζ => Phi x₀ ys (smp (Function.update z j ζ) l)) t :=
            (Phi_differentiable x₀ ys).differentiableAt.comp t h_smp_diff
          exact (hf_plus.differentiableAt
            ((tubeDomain_isOpen _hC).mem_nhds h_tube)).comp t h_phi_smp
        · -- sin θ < 0 (since sin θ ≠ 0)
          have hsin_neg : Real.sin θ < 0 :=
            lt_of_le_of_ne (not_lt.mp hsin_pos) hsin
          have hG_eq : (fun ζ => G (Function.update z j ζ) θ) =
              fun ζ => f_minus (Phi x₀ ys (smp (Function.update z j ζ) l)) := by
            ext ζ; exact (if_neg (not_lt.mpr (le_of_lt hsin_neg))).trans (if_pos hsin_neg)
          rw [hG_eq]
          have h_tube : Phi x₀ ys (smp (Function.update z j t) l) ∈
              TubeDomain (Neg.neg '' C) :=
            Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ fun k => by
              show ((↑δ : ℂ) * moebiusProd
                (fun i => (Function.update z j t) i / ↑δ) l k).im < 0
              rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
              exact mul_neg_of_pos_of_neg hδ_pos (moebiusProd_im_neg (ball_comp_lt_one _ ht)
                (Complex.norm_exp_ofReal_mul_I θ)
                (by rwa [Complex.exp_ofReal_mul_I_im]) k)
          have h_phi_smp : DifferentiableAt ℂ
              (fun ζ => Phi x₀ ys (smp (Function.update z j ζ) l)) t :=
            (Phi_differentiable x₀ ys).differentiableAt.comp t h_smp_diff
          exact (hf_minus.differentiableAt
            ((by convert tubeDomain_isOpen (_hC.neg) using 1
                 ext z; simp only [TubeDomain, Set.mem_setOf_eq, Set.image_neg_eq_neg]
              : IsOpen (TubeDomain (Neg.neg '' C))).mem_nhds h_tube)).comp t h_phi_smp
      exact differentiableAt_parametric_integral G hz hε'_pos h_upd h_upd_t h_G_meas M hM
        h_G_diffAt (fun w θ hsin => by
          simp only [G]
          exact (if_neg (by linarith [hsin])).trans (if_neg (by linarith [hsin])))
  -- Helper: Phi⁻¹(TubeDomain C) is convex (preimage of convex tube under affine Phi)
  have hPhi_preimg_conv : Convex ℝ {ζ : Fin m → ℂ | Phi x₀ ys ζ ∈ TubeDomain C} := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ a b ha hb hab
    simp only [Set.mem_setOf_eq, TubeDomain] at hζ₁ hζ₂ ⊢
    have h : (fun i => (Phi x₀ ys (a • ζ₁ + b • ζ₂) i).im) =
        a • (fun i => (Phi x₀ ys ζ₁ i).im) + b • (fun i => (Phi x₀ ys ζ₂ i).im) := by
      ext i; simp only [Phi_im, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
    rw [h]; exact hconv hζ₁ hζ₂ ha hb hab
  -- Helper: {ζ | ∀ j, Im(ζ_j) > 0} is open
  have hPosOctant_open : IsOpen {ζ : Fin m → ℂ | ∀ j, 0 < (ζ j).im} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply j))
  -- Helper: {ζ | ∀ j, Im(ζ_j) < 0} is open
  have hNegOctant_open : IsOpen {ζ : Fin m → ℂ | ∀ j, (ζ j).im < 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (Complex.continuous_im.comp (continuous_apply j)) continuous_const
  -- Helper: the test point z₀ = (δ/4) * I has all Im > 0, is in ball, and maps into T(C)
  set z₀ : Fin m → ℂ := fun _ => (↑(δ / 4) : ℂ) * Complex.I with hz₀_def
  have hz₀_im : ∀ j, (z₀ j).im = δ / 4 := by
    intro j; simp [z₀, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have hz₀_pos : ∀ j, 0 < (z₀ j).im := fun j => by rw [hz₀_im j]; positivity
  have hz₀_ball : z₀ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖z₀‖ = ‖(↑(δ / 4) : ℂ) * Complex.I‖ := by
          apply le_antisymm (pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun j => le_rfl)
          exact norm_le_pi_norm z₀ ⟨0, hm⟩
      _ = δ / 4 := by
          rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
      _ < δ / 2 := by linarith
  have hz₀_tube : Phi x₀ ys z₀ ∈ TubeDomain C := Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem z₀ hz₀_pos
  refine ⟨F₀, hF₀_diff, ?_, ?_⟩
  -- Goal 2: ∀ w ∈ ball, Phi w ∈ T(C) → F₀ w = f_plus (Phi w)
  · intro w hw hT
    suffices pos_agree : ∀ ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        (∀ j, 0 < (ζ j).im) → F₀ ζ = f_plus (Phi x₀ ys ζ) by
      -- Identity theorem: extend agreement from positive octant to full ball ∩ Phi⁻¹(T(C)).
      set U := Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ {ζ | Phi x₀ ys ζ ∈ TubeDomain C}
      have hU_open : IsOpen U :=
        Metric.isOpen_ball.inter ((tubeDomain_isOpen _hC).preimage (Phi_differentiable x₀ ys).continuous)
      -- F₀ is analytic on U (restriction from ball)
      have hF₀_anal : AnalyticOnNhd ℂ F₀ U := fun z hz =>
        SCV.differentiableOn_analyticAt Metric.isOpen_ball hF₀_diff hz.1
      -- f_plus ∘ Phi is analytic on U (composition of holomorphic maps)
      have hfp_diff_U : DifferentiableOn ℂ (fun ζ => f_plus (Phi x₀ ys ζ)) U :=
        hf_plus.comp (Phi_differentiable x₀ ys).differentiableOn (fun ζ hζ => hζ.2)
      have hfp_anal : AnalyticOnNhd ℂ (fun ζ => f_plus (Phi x₀ ys ζ)) U := fun z hz =>
        SCV.differentiableOn_analyticAt hU_open hfp_diff_U hz
      -- U is preconnected (convex ∩ convex, nonempty)
      have hU_conv : Convex ℝ U := convex_ball (0 : Fin m → ℂ) (δ / 2) |>.inter hPhi_preimg_conv
      have hU_preconn : IsPreconnected U := hU_conv.isPreconnected
      -- z₀ ∈ U
      have hz₀_U : z₀ ∈ U := ⟨hz₀_ball, hz₀_tube⟩
      -- F₀ and f_plus ∘ Phi agree near z₀ (positive octant is a neighborhood of z₀ in ball)
      have h_eq_near : F₀ =ᶠ[nhds z₀] fun ζ => f_plus (Phi x₀ ys ζ) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        exact ⟨Metric.ball 0 (δ / 2) ∩ {ζ | ∀ j, 0 < (ζ j).im},
          Filter.inter_mem (Metric.isOpen_ball.mem_nhds hz₀_ball)
            (hPosOctant_open.mem_nhds hz₀_pos),
          fun ζ ⟨hζ_ball, hζ_pos⟩ => pos_agree ζ hζ_ball hζ_pos⟩
      -- Apply identity theorem
      exact hF₀_anal.eqOn_of_preconnected_of_eventuallyEq hfp_anal hU_preconn hz₀_U h_eq_near ⟨hw, hT⟩
    -- 1D LINE ARGUMENT for pos_agree:
    -- For ζ with all Im > 0, define L(z)_j = Re(ζ_j) + z · Im(ζ_j).
    -- L(I) = ζ. Apply edge_of_the_wedge_1d along L to get F_1d on ball(0,2).
    -- Use rudin_mean_value_real to show F₀(L(t)) = F_1d(t) at real t near 0.
    -- Identity theorem extends agreement to z = I, giving F₀(ζ) = f_plus(Phi(ζ)).
    intro ζ hζ hζ_pos
    -- Rebuild helpers needed for rudin_mean_value_real
    have hδ_cnorm : ‖(↑δ : ℂ)‖ = δ := by simp [Complex.norm_real, abs_of_pos hδ_pos]
    have cball_half : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ j, ‖w j / (↑δ : ℂ)‖ ≤ 1 / 2 := by
      intro w hw j; rw [Metric.mem_closedBall, dist_zero_right] at hw; rw [norm_div, hδ_cnorm]
      calc ‖w j‖ / δ ≤ ‖w‖ / δ := by gcongr; exact norm_le_pi_norm w j
        _ ≤ (δ / 2) / δ := by gcongr
        _ = 1 / 2 := by field_simp
    have phi_re_E : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ l, ‖l‖ ≤ 2 → (fun i => (Phi x₀ ys (smp w l) i).re) ∈ E := by
      intro w hw l hl
      suffices h : (fun j => (smp w l j).re) ∈ Metric.ball (0 : Fin m → ℝ) ε by
        have := hε_sub h; simp only [Set.mem_preimage] at this
        convert this using 1; ext i; simp only [Phi, Complex.add_re, Complex.ofReal_re]
        congr 1; change ⇑Complex.reCLM (∑ j, smp w l j * ↑(ys j i)) = _
        rw [map_sum]; congr 1; ext j
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε_pos]; intro j; rw [Real.norm_eq_abs]
      calc |(smp w l j).re| ≤ ‖smp w l j‖ := Complex.abs_re_le_norm _
        _ ≤ δ * 10 := by
            show ‖(↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j‖ ≤ _
            rw [norm_mul, hδ_cnorm]; exact mul_le_mul_of_nonneg_left
              (moebiusProd_norm_le_extended (cball_half w hw) hl j) hδ_pos.le
        _ < ε := by rw [hδ_def]; linarith
    -- Define L(z)_j = Re(ζ_j) + z · Im(ζ_j) and prove key properties
    let L : ℂ → (Fin m → ℂ) := fun z j => ↑((ζ j).re) + z * ↑((ζ j).im)
    have hL_I : L I = ζ := by
      ext j; apply Complex.ext
      · simp [L, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      · simp [L, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    have hL_im : ∀ z j, (L z j).im = z.im * (ζ j).im := fun z j => by
      simp [L, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero]
    have hL_diff : Differentiable ℂ L := differentiable_pi.mpr fun j =>
      (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
    have hL_real : ∀ (t : ℝ) j, (L ↑t j).im = 0 := fun t j => by
      rw [hL_im]; simp [Complex.ofReal_im]
    -- Tube domain openness and membership
    have htube_open : IsOpen (TubeDomain C) := tubeDomain_isOpen _hC
    have htube_neg_open : IsOpen (TubeDomain (Neg.neg '' C)) := by
      convert tubeDomain_isOpen (_hC.neg) using 1; ext z; simp [TubeDomain]
    have hL_tube_pos : ∀ z, 0 < z.im → Phi x₀ ys (L z) ∈ TubeDomain C :=
      fun z hz => Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
        rw [hL_im]; exact mul_pos hz (hζ_pos j)
    have hL_tube_neg : ∀ z, z.im < 0 → Phi x₀ ys (L z) ∈ TubeDomain (Neg.neg '' C) :=
      fun z hz => Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
        rw [hL_im]; exact mul_neg_of_neg_of_pos hz (hζ_pos j)
    -- Phi ∘ L properties
    have hPhiL_diff : Differentiable ℂ (fun z => Phi x₀ ys (L z)) :=
      (Phi_differentiable x₀ ys).comp hL_diff
    have hPhiL_real : ∀ (t : ℝ),
        Phi x₀ ys (L ↑t) = realEmbed (fun i => (Phi x₀ ys (L ↑t) i).re) := by
      intro t; ext i; apply Complex.ext
      · simp [realEmbed]
      · rw [show (realEmbed _ i).im = 0 from Complex.ofReal_im _, Phi_im]
        simp only [hL_real t, zero_mul, Finset.sum_const_zero]
    have hζ_norm : ‖ζ‖ < δ / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hζ
    -- Re(Phi(L(t))) ∈ E for |t| ≤ 2
    have hPhiL_inE : ∀ (t : ℝ), |t| ≤ 2 →
        (fun i => (Phi x₀ ys (L ↑t) i).re) ∈ E := by
      intro t ht
      have hv : (fun j => (L (↑t : ℂ) j).re) ∈ Metric.ball (0 : Fin m → ℝ) ε := by
        rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε_pos]
        intro j; rw [Real.norm_eq_abs]
        have hLre : (L (↑t : ℂ) j).re = (ζ j).re + t * (ζ j).im := by
          simp [L, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hLre]
        calc |(ζ j).re + t * (ζ j).im| ≤ |(ζ j).re| + |t * (ζ j).im| := abs_add_le _ _
          _ = |(ζ j).re| + |t| * |(ζ j).im| := by rw [abs_mul]
          _ ≤ ‖ζ j‖ + |t| * ‖ζ j‖ := by
              linarith [Complex.abs_re_le_norm (ζ j),
                mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (ζ j)) (abs_nonneg t)]
          _ ≤ 3 * (δ / 2) := by
              have : (1 + |t|) * ‖ζ j‖ ≤ 3 * (δ / 2) := calc
                (1 + |t|) * ‖ζ j‖ ≤ (1 + 2) * ‖ζ‖ := by
                  apply mul_le_mul (by linarith) (norm_le_pi_norm ζ j)
                    (norm_nonneg _) (by linarith)
                _ = 3 * ‖ζ‖ := by ring
                _ ≤ 3 * (δ / 2) := by linarith [hζ_norm.le]
              linarith [this]
          _ < ε := by rw [hδ_def]; linarith
      have := hε_sub hv; simp only [Set.mem_preimage] at this
      convert this using 1; ext i; simp only [Phi, Complex.add_re, Complex.ofReal_re]
      congr 1; change ⇑Complex.reCLM (∑ j, L (↑t) j * ↑(ys j i)) = _
      rw [map_sum]; congr 1; ext j
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    -- Define boundary values, gp, gm for edge_of_the_wedge_1d along L
    let bv_line : ℝ → ℂ := fun t => _bv (fun i => (Phi x₀ ys (L ↑t) i).re)
    have hbv_line_ca : ∀ (t : ℝ), |t| < 2 → ContinuousAt bv_line t :=
      fun t ht => (_hbv_cont.continuousAt (_hE.mem_nhds (hPhiL_inE t ht.le))).comp
        (continuousAt_pi.mpr fun i => Complex.continuous_re.continuousAt.comp
          ((continuous_apply i).continuousAt.comp
            (hPhiL_diff.continuous.continuousAt.comp
              Complex.continuous_ofReal.continuousAt)))
    let gp : ℂ → ℂ := fun z =>
      if z.im > 0 then f_plus (Phi x₀ ys (L z)) else bv_line z.re
    let gm : ℂ → ℂ := fun z =>
      if z.im < 0 then f_minus (Phi x₀ ys (L z)) else bv_line z.re
    have hgp_eq_real : ∀ z : ℂ, z.im = 0 → gp z = bv_line z.re := fun z hz => by
      simp only [gp, show ¬(z.im > 0) from not_lt.mpr (le_of_eq hz), ite_false]
    -- gp holomorphic on UHP, gm holomorphic on LHP
    have hgp_diff : DifferentiableOn ℂ gp EOW.UpperHalfPlane := by
      intro z hz
      have hzim : z.im > 0 := hz
      have h1 : DifferentiableWithinAt ℂ (fun z => f_plus (Phi x₀ ys (L z))) EOW.UpperHalfPlane z :=
        ((hf_plus.differentiableAt (htube_open.mem_nhds (hL_tube_pos z hzim))).comp z
          hPhiL_diff.differentiableAt).differentiableWithinAt
      exact h1.congr (fun y hy => by simp [gp, show y.im > 0 from hy])
        (by simp [gp, show z.im > 0 from hzim])
    have hgm_diff : DifferentiableOn ℂ gm EOW.LowerHalfPlane := by
      intro z hz
      have hzim : z.im < 0 := hz
      have h1 : DifferentiableWithinAt ℂ (fun z => f_minus (Phi x₀ ys (L z))) EOW.LowerHalfPlane z :=
        ((hf_minus.differentiableAt (htube_neg_open.mem_nhds (hL_tube_neg z hzim))).comp z
          hPhiL_diff.differentiableAt).differentiableWithinAt
      exact h1.congr (fun y hy => by simp [gm, show y.im < 0 from hy])
        (by simp [gm, show z.im < 0 from hzim])
    -- Boundary conditions for edge_of_the_wedge_1d
    have hmatch_line : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp ↑x = gm ↑x := fun x _ _ => by
      simp only [gp, gm, Complex.ofReal_im, lt_irrefl, ite_false]
    have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
        Filter.Tendsto gp (nhdsWithin ↑x EOW.UpperHalfPlane) (nhds (gp ↑x)) := by
      intro x hx_lo hx_hi
      simp only [hgp_eq_real ↑x (Complex.ofReal_im x), Complex.ofReal_re]
      have hp := hPhiL_inE x (abs_lt.mpr ⟨by linarith, by linarith⟩).le
      exact ((_hf_plus_bv _ hp).comp (Filter.tendsto_inf.mpr
        ⟨(hPhiL_real x) ▸ hPhiL_diff.continuous.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds,
         Filter.tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun z hz =>
           hL_tube_pos z hz)⟩)).congr'
        (eventually_nhdsWithin_of_forall fun z (hz : z.im > 0) => by
          show f_plus _ = gp z; simp [gp, if_pos hz])
    have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
        Filter.Tendsto gm (nhdsWithin ↑x EOW.LowerHalfPlane) (nhds (gm ↑x)) := by
      intro x hx_lo hx_hi
      simp only [show gm ↑x = bv_line x by simp [gm, Complex.ofReal_im]]
      have hp := hPhiL_inE x (abs_lt.mpr ⟨by linarith, by linarith⟩).le
      exact ((_hf_minus_bv _ hp).comp (Filter.tendsto_inf.mpr
        ⟨(hPhiL_real x) ▸ hPhiL_diff.continuous.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds,
         Filter.tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun z hz =>
           hL_tube_neg z hz)⟩)).congr'
        (eventually_nhdsWithin_of_forall fun z (hz : z.im < 0) => by
          show f_minus _ = gm z; simp [gm, if_pos hz])
    have hbv_real : ∀ x₁ : ℝ, (-2 : ℝ) < x₁ → x₁ < 2 →
        Filter.Tendsto gp (nhdsWithin ↑x₁ {c : ℂ | c.im = 0}) (nhds (gp ↑x₁)) := by
      intro t ht_lo ht_hi
      simp only [hgp_eq_real ↑t (Complex.ofReal_im t), Complex.ofReal_re]
      exact ((hbv_line_ca t (abs_lt.mpr ⟨by linarith, by linarith⟩)).tendsto.comp
        (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)).congr'
        (eventually_nhdsWithin_of_forall fun z hz => (hgp_eq_real z hz).symm)
    -- Apply edge_of_the_wedge_1d along L
    obtain ⟨U_L, F_1d, hUL_open, hUL_conv, _, hUL_int, hF1d_holo, hF1d_gp, _, hball_L⟩ :=
      edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
        hgp_diff hgm_diff hgp_bv hgm_bv hmatch_line hbv_real
    have hball_sub : Metric.ball (0 : ℂ) 2 ⊆ U_L := by
      calc Metric.ball (0 : ℂ) 2
          = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) := by
            congr 1 <;> simp
        _ ⊆ U_L := hball_L
    -- F_1d(I) = f_plus(Phi(ζ))
    have hF1d_I : F_1d I = f_plus (Phi x₀ ys ζ) := by
      have hI_U : I ∈ U_L := hball_sub (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)
      rw [hF1d_gp I ⟨hI_U, show I.im > 0 by simp [Complex.I_im]⟩]
      simp [gp, hL_I]
    -- F_1d(t) = bv_line(t) for real t ∈ (-2, 2) (limit uniqueness: F_1d = gp on UHP)
    have hF1d_real : ∀ (t : ℝ), -2 < t → t < 2 → F_1d ↑t = bv_line t := by
      intro t ht_lo ht_hi
      have h_mem := hUL_int t ht_lo ht_hi
      have h_nebot : Filter.NeBot (nhdsWithin (↑t : ℂ) EOW.UpperHalfPlane) := by
        rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
        intro ε' hε'
        exact ⟨↑t + ↑(ε' / 2) * I,
          show (↑t + ↑(ε' / 2) * I).im > 0 by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]; linarith,
          by rw [dist_comm, dist_eq_norm,
               show ↑t + ↑(ε' / 2) * I - ↑t = ↑(ε' / 2) * I by push_cast; ring,
               norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
               abs_of_pos (by linarith : ε' / 2 > 0)]; linarith⟩
      have h_agree : ∀ᶠ z in nhdsWithin (↑t : ℂ) EOW.UpperHalfPlane, F_1d z = gp z := by
        filter_upwards [nhdsWithin_le_nhds (hUL_open.mem_nhds h_mem),
          self_mem_nhdsWithin] with z hz_U hz_UHP
        exact hF1d_gp z ⟨hz_U, hz_UHP⟩
      exact tendsto_nhds_unique
        ((hF1d_holo.continuousOn.continuousAt (hUL_open.mem_nhds h_mem)).tendsto.mono_left
          nhdsWithin_le_nhds)
        ((hgp_bv t ht_lo ht_hi).congr' (h_agree.mono fun _ h => h.symm))
        |>.trans (by rw [hgp_eq_real ↑t (Complex.ofReal_im t), Complex.ofReal_re])
    -- F₀(L(t)) = bv_line(t) for real t near 0 (via rudin_mean_value_real)
    -- L(0) ∈ ball(0, δ/2), so by continuity, L(↑t) ∈ ball for |t| small enough
    have hL0_ball : L 0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
      rw [Metric.mem_ball, dist_zero_right]; simp only [L, zero_mul, add_zero]
      calc ‖fun j => (↑((ζ j).re) : ℂ)‖ ≤ ‖ζ‖ :=
            pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun j => by
              rw [Complex.norm_real]; exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm ζ j)
        _ < δ / 2 := hζ_norm
    obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp
      (hL_diff.continuous.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hL0_ball))
    -- For |t| < ε₀, L(↑t) ∈ ball(0, δ/2), so rudin_mean_value_real applies
    have hF0L_real : ∀ (t : ℝ), |t| < ε₀ → F₀ (L ↑t) = bv_line t := by
      intro t ht
      have hLt_ball : L ↑t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) :=
        hε₀_sub (show (↑t : ℂ) ∈ Metric.ball 0 ε₀ by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact ht)
      exact rudin_mean_value_real hm C _hC hconv hcone x₀ ys hys_mem f_plus f_minus
        hf_plus hf_minus E _hE _bv _hbv_cont _hf_plus_bv _hf_minus_bv
        δ hδ_pos ball_comp_lt_one phi_re_E (L ↑t) hLt_ball (hL_real t)
    -- IDENTITY THEOREM: F₀ ∘ L = F_1d on a connected open set containing 0 and I.
    -- Define V = L⁻¹(ball(0, δ/2)) ∩ U_L (open, convex, contains 0 and I).
    set V := L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ U_L with hV_def
    have hpre_conv : Convex ℝ (L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
      intro z₁ hz₁ z₂ hz₂ a b ha hb hab
      simp only [Set.mem_preimage] at hz₁ hz₂ ⊢
      have : L (a • z₁ + b • z₂) = a • L z₁ + b • L z₂ := by
        ext j; simp only [L, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
        have hab' : (↑a : ℂ) + ↑b = 1 := by exact_mod_cast hab
        linear_combination -(↑((ζ j).re : ℝ) : ℂ) * hab'
      rw [this]; exact (convex_ball (0 : Fin m → ℂ) (δ / 2)) hz₁ hz₂ ha hb hab
    have hV_open : IsOpen V := (Metric.isOpen_ball.preimage hL_diff.continuous).inter hUL_open
    have hV_conv : Convex ℝ V := hpre_conv.inter hUL_conv
    have hV_preconn : IsPreconnected V := hV_conv.isPreconnected
    have h0_V : (0 : ℂ) ∈ V := ⟨hL0_ball, hball_sub (by
      rw [Metric.mem_ball, dist_zero_right]; simp)⟩
    have hI_V : I ∈ V := ⟨show L I ∈ _ by rw [hL_I]; rwa [Metric.mem_ball, dist_zero_right],
      hball_sub (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)⟩
    -- h := F₀ ∘ L - F_1d is analytic on V and zero at real points near 0
    let h : ℂ → ℂ := fun z => F₀ (L z) - F_1d z
    have hh_anal : AnalyticOnNhd ℂ h V := by
      intro z hz
      have h1 : AnalyticAt ℂ (fun z => F₀ (L z)) z :=
        ((hF₀_diff.comp hL_diff.differentiableOn fun z hz => hz).mono
          Set.inter_subset_left).analyticAt (hV_open.mem_nhds hz)
      have h2 : AnalyticAt ℂ F_1d z :=
        (hF1d_holo.mono Set.inter_subset_right).analyticAt (hV_open.mem_nhds hz)
      exact h1.sub h2
    -- h = 0 frequently near 0 (h(↑t) = 0 for real t near 0)
    set c := min (ε₀ / 2) 1 with hc_def
    have hc_pos : 0 < c := by positivity
    have hh_zero : ∀ (t : ℝ), 0 < |t| → |t| < c → h ↑t = 0 := by
      intro t _ ht_c
      have ht_ε₀ : |t| < ε₀ := lt_of_lt_of_le ht_c ((min_le_left _ _).trans (by linarith))
      have ht_2 : -2 < t ∧ t < 2 := by
        obtain ⟨h1, h2⟩ := abs_le.mp ht_c.le
        exact ⟨by linarith [min_le_right (ε₀ / 2) (1 : ℝ)], by linarith [min_le_right (ε₀ / 2) (1 : ℝ)]⟩
      show F₀ (L ↑t) - F_1d ↑t = 0
      rw [hF0L_real t ht_ε₀, hF1d_real t ht_2.1 ht_2.2, sub_self]
    have hh_freq : Filter.Frequently (fun z => h z = 0) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
      rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
      intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
      obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
      set s := min (c / 2) (r / 2) with hs_def
      have hs_pos : 0 < s := by positivity
      have hs_ne : (↑s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
      have hs_in : (↑s : ℂ) ∈ U' ∩ {(0 : ℂ)}ᶜ := by
        constructor
        · exact hr_sub (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hs_pos]; linarith [min_le_right (c / 2) (r / 2)])
        · exact hs_ne
      exact hU'_sub hs_in (hh_zero s (by rw [abs_of_pos hs_pos]; positivity)
        (by rw [abs_of_pos hs_pos]; linarith [min_le_left (c / 2) (r / 2)]))
    -- Apply identity theorem: h ≡ 0 on V
    have hh_eqOn : Set.EqOn h 0 V :=
      hh_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hV_preconn h0_V hh_freq
    -- Conclude: F₀(ζ) = F₀(L(I)) = F_1d(I) = f_plus(Phi(ζ))
    have hh_I := hh_eqOn hI_V
    simp only [h, Pi.zero_apply, sub_eq_zero] at hh_I
    rw [hL_I] at hh_I; exact hh_I.trans hF1d_I
  -- Goal 3: ∀ w ∈ ball, Phi w ∈ T(-C) → F₀ w = f_minus (Phi w)
  · intro w hw hT
    suffices neg_agree : ∀ ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        (∀ j, (ζ j).im < 0) → F₀ ζ = f_minus (Phi x₀ ys ζ) by
      -- Identity theorem: symmetric to Goal 2 with T(-C) and negative octant.
      set U := Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ {ζ | Phi x₀ ys ζ ∈ TubeDomain (Neg.neg '' C)}
      have hU_open : IsOpen U := by
        apply IsOpen.inter Metric.isOpen_ball
        apply IsOpen.preimage (Phi_differentiable x₀ ys).continuous
        convert tubeDomain_isOpen (_hC.neg) using 1
        ext z; simp only [TubeDomain, Set.mem_setOf_eq, Set.image_neg_eq_neg]
      have hF₀_anal : AnalyticOnNhd ℂ F₀ U := fun z hz =>
        SCV.differentiableOn_analyticAt Metric.isOpen_ball hF₀_diff hz.1
      have hfm_diff_U : DifferentiableOn ℂ (fun ζ => f_minus (Phi x₀ ys ζ)) U :=
        hf_minus.comp (Phi_differentiable x₀ ys).differentiableOn (fun ζ hζ => hζ.2)
      have hfm_anal : AnalyticOnNhd ℂ (fun ζ => f_minus (Phi x₀ ys ζ)) U := fun z hz =>
        SCV.differentiableOn_analyticAt hU_open hfm_diff_U hz
      -- Phi⁻¹(T(-C)) is convex
      have hPhi_preimg_neg_conv : Convex ℝ {ζ : Fin m → ℂ | Phi x₀ ys ζ ∈ TubeDomain (Neg.neg '' C)} := by
        intro ζ₁ hζ₁ ζ₂ hζ₂ a b ha hb hab
        simp only [Set.mem_setOf_eq, TubeDomain] at hζ₁ hζ₂ ⊢
        have h : (fun i => (Phi x₀ ys (a • ζ₁ + b • ζ₂) i).im) =
            a • (fun i => (Phi x₀ ys ζ₁ i).im) + b • (fun i => (Phi x₀ ys ζ₂ i).im) := by
          ext i; simp only [Phi_im, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero]
          simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
        rw [h]
        -- Need: Neg.neg '' C is convex
        have hNegC_conv : Convex ℝ (Neg.neg '' C) := by
          rw [Set.image_neg_eq_neg]; exact hconv.neg
        exact hNegC_conv hζ₁ hζ₂ ha hb hab
      have hU_conv : Convex ℝ U := (convex_ball (0 : Fin m → ℂ) (δ / 2)).inter hPhi_preimg_neg_conv
      have hU_preconn : IsPreconnected U := hU_conv.isPreconnected
      -- Negative test point z₁ = -(δ/4)*I
      set z₁ : Fin m → ℂ := fun _ => -((↑(δ / 4) : ℂ) * Complex.I) with hz₁_def
      have hz₁_im : ∀ j, (z₁ j).im = -(δ / 4) := by
        intro j; simp [z₁, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have hz₁_neg : ∀ j, (z₁ j).im < 0 := fun j => by rw [hz₁_im j]; linarith [hδ_pos]
      have hz₁_ball : z₁ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖z₁‖ = ‖-((↑(δ / 4) : ℂ) * Complex.I)‖ := by
              apply le_antisymm (pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun j => le_rfl)
              exact norm_le_pi_norm z₁ ⟨0, hm⟩
          _ = δ / 4 := by
              rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
                abs_of_pos (by positivity)]
          _ < δ / 2 := by linarith
      have hz₁_tube : Phi x₀ ys z₁ ∈ TubeDomain (Neg.neg '' C) :=
        Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem z₁ hz₁_neg
      have hz₁_U : z₁ ∈ U := ⟨hz₁_ball, hz₁_tube⟩
      have h_eq_near : F₀ =ᶠ[nhds z₁] fun ζ => f_minus (Phi x₀ ys ζ) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        exact ⟨Metric.ball 0 (δ / 2) ∩ {ζ | ∀ j, (ζ j).im < 0},
          Filter.inter_mem (Metric.isOpen_ball.mem_nhds hz₁_ball)
            (hNegOctant_open.mem_nhds hz₁_neg),
          fun ζ ⟨hζ_ball, hζ_neg⟩ => neg_agree ζ hζ_ball hζ_neg⟩
      exact hF₀_anal.eqOn_of_preconnected_of_eventuallyEq hfm_anal hU_preconn hz₁_U h_eq_near ⟨hw, hT⟩
    -- 1D LINE ARGUMENT for neg_agree (symmetric to pos_agree with f_plus/f_minus swapped):
    -- For ζ with all Im < 0, L maps UHP → negative octant, LHP → positive octant.
    -- gp = f_minus ∘ Phi ∘ L on UHP, gm = f_plus ∘ Phi ∘ L on LHP.
    -- F_1d(I) = gp(I) = f_minus(Phi(ζ)).
    intro ζ hζ hζ_neg
    -- Rebuild helpers needed for rudin_mean_value_real
    have hδ_cnorm : ‖(↑δ : ℂ)‖ = δ := by simp [Complex.norm_real, abs_of_pos hδ_pos]
    have cball_half : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ j, ‖w j / (↑δ : ℂ)‖ ≤ 1 / 2 := by
      intro w hw j; rw [Metric.mem_closedBall, dist_zero_right] at hw; rw [norm_div, hδ_cnorm]
      calc ‖w j‖ / δ ≤ ‖w‖ / δ := by gcongr; exact norm_le_pi_norm w j
        _ ≤ (δ / 2) / δ := by gcongr
        _ = 1 / 2 := by field_simp
    have phi_re_E : ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ l, ‖l‖ ≤ 2 → (fun i => (Phi x₀ ys (smp w l) i).re) ∈ E := by
      intro w hw l hl
      suffices h : (fun j => (smp w l j).re) ∈ Metric.ball (0 : Fin m → ℝ) ε by
        have := hε_sub h; simp only [Set.mem_preimage] at this
        convert this using 1; ext i; simp only [Phi, Complex.add_re, Complex.ofReal_re]
        congr 1; change ⇑Complex.reCLM (∑ j, smp w l j * ↑(ys j i)) = _
        rw [map_sum]; congr 1; ext j
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε_pos]; intro j; rw [Real.norm_eq_abs]
      calc |(smp w l j).re| ≤ ‖smp w l j‖ := Complex.abs_re_le_norm _
        _ ≤ δ * 10 := by
            show ‖(↑δ : ℂ) * moebiusProd (fun k => w k / ↑δ) l j‖ ≤ _
            rw [norm_mul, hδ_cnorm]; exact mul_le_mul_of_nonneg_left
              (moebiusProd_norm_le_extended (cball_half w hw) hl j) hδ_pos.le
        _ < ε := by rw [hδ_def]; linarith
    -- Define L(z)_j = Re(ζ_j) + z · Im(ζ_j) and prove key properties
    let L : ℂ → (Fin m → ℂ) := fun z j => ↑((ζ j).re) + z * ↑((ζ j).im)
    have hL_I : L I = ζ := by
      ext j; apply Complex.ext
      · simp [L, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      · simp [L, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    have hL_im : ∀ z j, (L z j).im = z.im * (ζ j).im := fun z j => by
      simp [L, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        mul_zero]
    have hL_diff : Differentiable ℂ L := differentiable_pi.mpr fun j =>
      (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
    have hL_real : ∀ (t : ℝ) j, (L ↑t j).im = 0 := fun t j => by
      rw [hL_im]; simp [Complex.ofReal_im]
    -- Tube domain openness and membership (SWAPPED from pos_agree)
    have htube_open : IsOpen (TubeDomain C) := tubeDomain_isOpen _hC
    have htube_neg_open : IsOpen (TubeDomain (Neg.neg '' C)) := by
      convert tubeDomain_isOpen (_hC.neg) using 1; ext z; simp [TubeDomain]
    -- UHP → negative octant (since Im(ζ_j) < 0)
    have hL_tube_neg_uhp : ∀ z, 0 < z.im → Phi x₀ ys (L z) ∈ TubeDomain (Neg.neg '' C) :=
      fun z hz => Phi_neg_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
        rw [hL_im]; exact mul_neg_of_pos_of_neg hz (hζ_neg j)
    -- LHP → positive octant (since Im(ζ_j) < 0)
    have hL_tube_pos_lhp : ∀ z, z.im < 0 → Phi x₀ ys (L z) ∈ TubeDomain C :=
      fun z hz => Phi_pos_in_tube hm C hconv hcone x₀ ys hys_mem _ fun j => by
        rw [hL_im]; exact mul_pos_of_neg_of_neg hz (hζ_neg j)
    -- Phi ∘ L properties
    have hPhiL_diff : Differentiable ℂ (fun z => Phi x₀ ys (L z)) :=
      (Phi_differentiable x₀ ys).comp hL_diff
    have hPhiL_real : ∀ (t : ℝ),
        Phi x₀ ys (L ↑t) = realEmbed (fun i => (Phi x₀ ys (L ↑t) i).re) := by
      intro t; ext i; apply Complex.ext
      · simp [realEmbed]
      · rw [show (realEmbed _ i).im = 0 from Complex.ofReal_im _, Phi_im]
        simp only [hL_real t, zero_mul, Finset.sum_const_zero]
    have hζ_norm : ‖ζ‖ < δ / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hζ
    -- Re(Phi(L(t))) ∈ E for |t| ≤ 2
    have hPhiL_inE : ∀ (t : ℝ), |t| ≤ 2 →
        (fun i => (Phi x₀ ys (L ↑t) i).re) ∈ E := by
      intro t ht
      have hv : (fun j => (L (↑t : ℂ) j).re) ∈ Metric.ball (0 : Fin m → ℝ) ε := by
        rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε_pos]
        intro j; rw [Real.norm_eq_abs]
        have hLre : (L (↑t : ℂ) j).re = (ζ j).re + t * (ζ j).im := by
          simp [L, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hLre]
        calc |(ζ j).re + t * (ζ j).im| ≤ |(ζ j).re| + |t * (ζ j).im| := abs_add_le _ _
          _ = |(ζ j).re| + |t| * |(ζ j).im| := by rw [abs_mul]
          _ ≤ ‖ζ j‖ + |t| * ‖ζ j‖ := by
              linarith [Complex.abs_re_le_norm (ζ j),
                mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (ζ j)) (abs_nonneg t)]
          _ ≤ 3 * (δ / 2) := by
              have : (1 + |t|) * ‖ζ j‖ ≤ 3 * (δ / 2) := calc
                (1 + |t|) * ‖ζ j‖ ≤ (1 + 2) * ‖ζ‖ := by
                  apply mul_le_mul (by linarith) (norm_le_pi_norm ζ j)
                    (norm_nonneg _) (by linarith)
                _ = 3 * ‖ζ‖ := by ring
                _ ≤ 3 * (δ / 2) := by linarith [hζ_norm.le]
              linarith [this]
          _ < ε := by rw [hδ_def]; linarith
      have := hε_sub hv; simp only [Set.mem_preimage] at this
      convert this using 1; ext i; simp only [Phi, Complex.add_re, Complex.ofReal_re]
      congr 1; change ⇑Complex.reCLM (∑ j, L (↑t) j * ↑(ys j i)) = _
      rw [map_sum]; congr 1; ext j
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    -- Define boundary values, gp, gm for edge_of_the_wedge_1d along L
    -- SWAPPED: gp uses f_minus (UHP→neg octant), gm uses f_plus (LHP→pos octant)
    let bv_line : ℝ → ℂ := fun t => _bv (fun i => (Phi x₀ ys (L ↑t) i).re)
    have hbv_line_ca : ∀ (t : ℝ), |t| < 2 → ContinuousAt bv_line t :=
      fun t ht => (_hbv_cont.continuousAt (_hE.mem_nhds (hPhiL_inE t ht.le))).comp
        (continuousAt_pi.mpr fun i => Complex.continuous_re.continuousAt.comp
          ((continuous_apply i).continuousAt.comp
            (hPhiL_diff.continuous.continuousAt.comp
              Complex.continuous_ofReal.continuousAt)))
    let gp : ℂ → ℂ := fun z =>
      if z.im > 0 then f_minus (Phi x₀ ys (L z)) else bv_line z.re
    let gm : ℂ → ℂ := fun z =>
      if z.im < 0 then f_plus (Phi x₀ ys (L z)) else bv_line z.re
    have hgp_eq_real : ∀ z : ℂ, z.im = 0 → gp z = bv_line z.re := fun z hz => by
      simp only [gp, show ¬(z.im > 0) from not_lt.mpr (le_of_eq hz), ite_false]
    -- gp holomorphic on UHP (uses f_minus, since L maps UHP → neg octant)
    have hgp_diff : DifferentiableOn ℂ gp EOW.UpperHalfPlane := by
      intro z hz
      have hzim : z.im > 0 := hz
      have h1 : DifferentiableWithinAt ℂ (fun z => f_minus (Phi x₀ ys (L z))) EOW.UpperHalfPlane z :=
        ((hf_minus.differentiableAt (htube_neg_open.mem_nhds (hL_tube_neg_uhp z hzim))).comp z
          hPhiL_diff.differentiableAt).differentiableWithinAt
      exact h1.congr (fun y hy => by simp [gp, show y.im > 0 from hy])
        (by simp [gp, show z.im > 0 from hzim])
    -- gm holomorphic on LHP (uses f_plus, since L maps LHP → pos octant)
    have hgm_diff : DifferentiableOn ℂ gm EOW.LowerHalfPlane := by
      intro z hz
      have hzim : z.im < 0 := hz
      have h1 : DifferentiableWithinAt ℂ (fun z => f_plus (Phi x₀ ys (L z))) EOW.LowerHalfPlane z :=
        ((hf_plus.differentiableAt (htube_open.mem_nhds (hL_tube_pos_lhp z hzim))).comp z
          hPhiL_diff.differentiableAt).differentiableWithinAt
      exact h1.congr (fun y hy => by simp [gm, show y.im < 0 from hy])
        (by simp [gm, show z.im < 0 from hzim])
    -- Boundary conditions for edge_of_the_wedge_1d
    have hmatch_line : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp ↑x = gm ↑x := fun x _ _ => by
      simp only [gp, gm, Complex.ofReal_im, lt_irrefl, ite_false]
    have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
        Filter.Tendsto gp (nhdsWithin ↑x EOW.UpperHalfPlane) (nhds (gp ↑x)) := by
      intro x hx_lo hx_hi
      simp only [hgp_eq_real ↑x (Complex.ofReal_im x), Complex.ofReal_re]
      have hp := hPhiL_inE x (abs_lt.mpr ⟨by linarith, by linarith⟩).le
      exact ((_hf_minus_bv _ hp).comp (Filter.tendsto_inf.mpr
        ⟨(hPhiL_real x) ▸ hPhiL_diff.continuous.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds,
         Filter.tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun z hz =>
           hL_tube_neg_uhp z hz)⟩)).congr'
        (eventually_nhdsWithin_of_forall fun z (hz : z.im > 0) => by
          show f_minus _ = gp z; simp [gp, if_pos hz])
    have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
        Filter.Tendsto gm (nhdsWithin ↑x EOW.LowerHalfPlane) (nhds (gm ↑x)) := by
      intro x hx_lo hx_hi
      simp only [show gm ↑x = bv_line x by simp [gm, Complex.ofReal_im]]
      have hp := hPhiL_inE x (abs_lt.mpr ⟨by linarith, by linarith⟩).le
      exact ((_hf_plus_bv _ hp).comp (Filter.tendsto_inf.mpr
        ⟨(hPhiL_real x) ▸ hPhiL_diff.continuous.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds,
         Filter.tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun z hz =>
           hL_tube_pos_lhp z hz)⟩)).congr'
        (eventually_nhdsWithin_of_forall fun z (hz : z.im < 0) => by
          show f_plus _ = gm z; simp [gm, if_pos hz])
    have hbv_real : ∀ x₁ : ℝ, (-2 : ℝ) < x₁ → x₁ < 2 →
        Filter.Tendsto gp (nhdsWithin ↑x₁ {c : ℂ | c.im = 0}) (nhds (gp ↑x₁)) := by
      intro t ht_lo ht_hi
      simp only [hgp_eq_real ↑t (Complex.ofReal_im t), Complex.ofReal_re]
      exact ((hbv_line_ca t (abs_lt.mpr ⟨by linarith, by linarith⟩)).tendsto.comp
        (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)).congr'
        (eventually_nhdsWithin_of_forall fun z hz => (hgp_eq_real z hz).symm)
    -- Apply edge_of_the_wedge_1d along L
    obtain ⟨U_L, F_1d, hUL_open, hUL_conv, _, hUL_int, hF1d_holo, hF1d_gp, _, hball_L⟩ :=
      edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
        hgp_diff hgm_diff hgp_bv hgm_bv hmatch_line hbv_real
    have hball_sub : Metric.ball (0 : ℂ) 2 ⊆ U_L := by
      calc Metric.ball (0 : ℂ) 2
          = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) := by
            congr 1 <;> simp
        _ ⊆ U_L := hball_L
    -- F_1d(I) = f_minus(Phi(ζ)) (SWAPPED from pos_agree)
    have hF1d_I : F_1d I = f_minus (Phi x₀ ys ζ) := by
      have hI_U : I ∈ U_L := hball_sub (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)
      rw [hF1d_gp I ⟨hI_U, show I.im > 0 by simp [Complex.I_im]⟩]
      simp [gp, hL_I]
    -- F_1d(t) = bv_line(t) for real t ∈ (-2, 2) (limit uniqueness)
    have hF1d_real : ∀ (t : ℝ), -2 < t → t < 2 → F_1d ↑t = bv_line t := by
      intro t ht_lo ht_hi
      have h_mem := hUL_int t ht_lo ht_hi
      have h_nebot : Filter.NeBot (nhdsWithin (↑t : ℂ) EOW.UpperHalfPlane) := by
        rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
        intro ε' hε'
        exact ⟨↑t + ↑(ε' / 2) * I,
          show (↑t + ↑(ε' / 2) * I).im > 0 by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]; linarith,
          by rw [dist_comm, dist_eq_norm,
               show ↑t + ↑(ε' / 2) * I - ↑t = ↑(ε' / 2) * I by push_cast; ring,
               norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
               abs_of_pos (by linarith : ε' / 2 > 0)]; linarith⟩
      have h_agree : ∀ᶠ z in nhdsWithin (↑t : ℂ) EOW.UpperHalfPlane, F_1d z = gp z := by
        filter_upwards [nhdsWithin_le_nhds (hUL_open.mem_nhds h_mem),
          self_mem_nhdsWithin] with z hz_U hz_UHP
        exact hF1d_gp z ⟨hz_U, hz_UHP⟩
      exact tendsto_nhds_unique
        ((hF1d_holo.continuousOn.continuousAt (hUL_open.mem_nhds h_mem)).tendsto.mono_left
          nhdsWithin_le_nhds)
        ((hgp_bv t ht_lo ht_hi).congr' (h_agree.mono fun _ h => h.symm))
        |>.trans (by rw [hgp_eq_real ↑t (Complex.ofReal_im t), Complex.ofReal_re])
    -- F₀(L(t)) = bv_line(t) for real t near 0 (via rudin_mean_value_real)
    have hL0_ball : L 0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
      rw [Metric.mem_ball, dist_zero_right]; simp only [L, zero_mul, add_zero]
      calc ‖fun j => (↑((ζ j).re) : ℂ)‖ ≤ ‖ζ‖ :=
            pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun j => by
              rw [Complex.norm_real]; exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm ζ j)
        _ < δ / 2 := hζ_norm
    obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp
      (hL_diff.continuous.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hL0_ball))
    have hF0L_real : ∀ (t : ℝ), |t| < ε₀ → F₀ (L ↑t) = bv_line t := by
      intro t ht
      have hLt_ball : L ↑t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) :=
        hε₀_sub (show (↑t : ℂ) ∈ Metric.ball 0 ε₀ by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact ht)
      exact rudin_mean_value_real hm C _hC hconv hcone x₀ ys hys_mem f_plus f_minus
        hf_plus hf_minus E _hE _bv _hbv_cont _hf_plus_bv _hf_minus_bv
        δ hδ_pos ball_comp_lt_one phi_re_E (L ↑t) hLt_ball (hL_real t)
    -- IDENTITY THEOREM: F₀ ∘ L = F_1d on connected open set containing 0 and I.
    set V := L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ U_L with hV_def
    have hpre_conv : Convex ℝ (L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
      intro z₁ hz₁ z₂ hz₂ a b ha hb hab
      simp only [Set.mem_preimage] at hz₁ hz₂ ⊢
      have : L (a • z₁ + b • z₂) = a • L z₁ + b • L z₂ := by
        ext j; simp only [L, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
        have hab' : (↑a : ℂ) + ↑b = 1 := by exact_mod_cast hab
        linear_combination -(↑((ζ j).re : ℝ) : ℂ) * hab'
      rw [this]; exact (convex_ball (0 : Fin m → ℂ) (δ / 2)) hz₁ hz₂ ha hb hab
    have hV_open : IsOpen V := (Metric.isOpen_ball.preimage hL_diff.continuous).inter hUL_open
    have hV_conv : Convex ℝ V := hpre_conv.inter hUL_conv
    have hV_preconn : IsPreconnected V := hV_conv.isPreconnected
    have h0_V : (0 : ℂ) ∈ V := ⟨hL0_ball, hball_sub (by
      rw [Metric.mem_ball, dist_zero_right]; simp)⟩
    have hI_V : I ∈ V := ⟨show L I ∈ _ by rw [hL_I]; rwa [Metric.mem_ball, dist_zero_right],
      hball_sub (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)⟩
    -- h := F₀ ∘ L - F_1d is analytic on V and zero at real points near 0
    let h : ℂ → ℂ := fun z => F₀ (L z) - F_1d z
    have hh_anal : AnalyticOnNhd ℂ h V := by
      intro z hz
      have h1 : AnalyticAt ℂ (fun z => F₀ (L z)) z :=
        ((hF₀_diff.comp hL_diff.differentiableOn fun z hz => hz).mono
          Set.inter_subset_left).analyticAt (hV_open.mem_nhds hz)
      have h2 : AnalyticAt ℂ F_1d z :=
        (hF1d_holo.mono Set.inter_subset_right).analyticAt (hV_open.mem_nhds hz)
      exact h1.sub h2
    set c := min (ε₀ / 2) 1 with hc_def
    have hc_pos : 0 < c := by positivity
    have hh_zero : ∀ (t : ℝ), 0 < |t| → |t| < c → h ↑t = 0 := by
      intro t _ ht_c
      have ht_ε₀ : |t| < ε₀ := lt_of_lt_of_le ht_c ((min_le_left _ _).trans (by linarith))
      have ht_2 : -2 < t ∧ t < 2 := by
        obtain ⟨h1, h2⟩ := abs_le.mp ht_c.le
        exact ⟨by linarith [min_le_right (ε₀ / 2) (1 : ℝ)], by linarith [min_le_right (ε₀ / 2) (1 : ℝ)]⟩
      show F₀ (L ↑t) - F_1d ↑t = 0
      rw [hF0L_real t ht_ε₀, hF1d_real t ht_2.1 ht_2.2, sub_self]
    have hh_freq : Filter.Frequently (fun z => h z = 0) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
      rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
      intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
      obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
      set s := min (c / 2) (r / 2) with hs_def
      have hs_pos : 0 < s := by positivity
      have hs_ne : (↑s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
      have hs_in : (↑s : ℂ) ∈ U' ∩ {(0 : ℂ)}ᶜ := by
        constructor
        · exact hr_sub (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hs_pos]; linarith [min_le_right (c / 2) (r / 2)])
        · exact hs_ne
      exact hU'_sub hs_in (hh_zero s (by rw [abs_of_pos hs_pos]; positivity)
        (by rw [abs_of_pos hs_pos]; linarith [min_le_left (c / 2) (r / 2)]))
    -- Apply identity theorem: h ≡ 0 on V
    have hh_eqOn : Set.EqOn h 0 V :=
      hh_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hV_preconn h0_V hh_freq
    -- Conclude: F₀(ζ) = F₀(L(I)) = F_1d(I) = f_minus(Phi(ζ))
    have hh_I := hh_eqOn hI_V
    simp only [h, Pi.zero_apply, sub_eq_zero] at hh_I
    rw [hL_I] at hh_I; exact hh_I.trans hF1d_I

/-- The m ≥ 2 case of local edge-of-the-wedge extension. -/
private lemma eow_extension_m2 {m : ℕ} (hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (bv x)))
    (x₀ : Fin m → ℝ) (hx₀ : x₀ ∈ E) (hm2 : 2 ≤ m) :
    ∃ (P : Set (Fin m → ℂ)) (F_loc : (Fin m → ℂ) → ℂ),
      IsOpen P ∧ Convex ℝ P ∧
      (∀ z ∈ P, (fun i => starRingEnd ℂ (z i)) ∈ P) ∧
      realEmbed x₀ ∈ P ∧ DifferentiableOn ℂ F_loc P ∧
      (∀ z ∈ P ∩ TubeDomain C, F_loc z = f_plus z) ∧
      (∀ z ∈ P ∩ TubeDomain (Neg.neg '' C), F_loc z = f_minus z) := by
  -- Step 1: Get m linearly independent vectors in C
  obtain ⟨ys, hys_mem, hys_li⟩ := open_set_contains_basis (by omega : 0 < m) C hC hCne
  -- Step 2: Get the holomorphic inverse of Phi
  obtain ⟨Φ_inv, hΦ_inv_diff, hΦ_left, hΦ_right⟩ := Phi_equiv x₀ ys hys_li
  -- Step 3: Apply Rudin's Möbius integral construction (Rudin §4)
  obtain ⟨ρ, hρ_pos, F₀, hF₀_diff, hF₀_eq_plus, hF₀_eq_minus⟩ :=
    rudin_orthant_extension hm hm2 C hC hconv h0 hcone hCne x₀ ys hys_mem hys_li
      f_plus f_minus hf_plus hf_minus E hE hx₀ bv hbv_cont hf_plus_bv hf_minus_bv
  -- Step 4: Define P = Φ_inv⁻¹(B(0, ρ)) and F_loc = F₀ ∘ Φ_inv
  --
  -- P is the preimage of the ball in orthant coordinates under Φ_inv.
  -- Since Φ_inv is continuous, P is open. Since Phi and Φ_inv are inverses,
  -- P = Phi(B(0, ρ)), an affine image of a convex set.
  -- F_loc = F₀ ∘ Φ_inv is holomorphic (composition of holomorphic maps).
  set P := Φ_inv ⁻¹' Metric.ball (0 : Fin m → ℂ) ρ with hP_def
  set F_loc := F₀ ∘ Φ_inv with hFloc_def
  -- Step 5: P = Phi '' B(0, ρ)
  have hP_eq : P = Phi x₀ ys '' Metric.ball (0 : Fin m → ℂ) ρ := by
    ext z; simp only [hP_def, Set.mem_preimage, Set.mem_image, Metric.mem_ball]
    exact ⟨fun hz => ⟨Φ_inv z, hz, hΦ_right z⟩,
           fun ⟨w, hw, hzw⟩ => by rwa [← hzw, hΦ_left]⟩
  -- Step 6: Verify properties
  refine ⟨P, F_loc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsOpen P: preimage of open set under continuous map
  · exact Metric.isOpen_ball.preimage hΦ_inv_diff.continuous
  -- Convex ℝ P: P = Phi '' B(0, ρ), affine image of convex ball
  · rw [hP_eq]
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    obtain ⟨w₁, hw₁, rfl⟩ := hz₁
    obtain ⟨w₂, hw₂, rfl⟩ := hz₂
    refine ⟨a • w₁ + b • w₂, (convex_ball 0 ρ) hw₁ hw₂ ha hb hab, ?_⟩
    -- Phi(a•w₁+b•w₂) = a•Phi(w₁)+b•Phi(w₂) when a+b=1
    ext i
    simp only [Phi, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
      add_mul, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add, mul_add]
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    linear_combination -↑(x₀ i) * hab'
  -- Conjugation symmetric: Phi commutes with conjugation (x₀, ys are real)
  · intro z hz
    show Φ_inv (fun i => starRingEnd ℂ (z i)) ∈ Metric.ball 0 ρ
    -- Φ_inv commutes with conjugation (since Phi does)
    have hΦ_inv_conj : Φ_inv (fun i => starRingEnd ℂ (z i)) =
        fun j => starRingEnd ℂ (Φ_inv z j) := by
      have h1 := Phi_conj x₀ ys (Φ_inv z)
      -- h1 : Phi(conj(Φ_inv z)) = conj(Phi(Φ_inv z))
      have h2 : (fun i => starRingEnd ℂ (Phi x₀ ys (Φ_inv z) i)) =
          fun i => starRingEnd ℂ (z i) := by
        ext i; congr 1; exact congr_fun (hΦ_right z) i
      rw [h2] at h1; rw [← h1]; exact hΦ_left _
    rw [hΦ_inv_conj]
    -- ‖conj(w)‖ = ‖w‖
    have hz' : Φ_inv z ∈ Metric.ball (0 : Fin m → ℂ) ρ := hz
    rw [Metric.mem_ball, dist_zero_right] at hz' ⊢
    suffices h : ‖fun j => starRingEnd ℂ (Φ_inv z j)‖ = ‖Φ_inv z‖ by rw [h]; exact hz'
    simp only [Pi.norm_def]
    congr 1; apply Finset.sup_congr rfl; intro b _
    exact RCLike.nnnorm_conj _
  -- realEmbed x₀ ∈ P: since Φ_inv(realEmbed x₀) = Φ_inv(Phi(0)) = 0 ∈ B(0, ρ)
  · show Φ_inv (realEmbed x₀) ∈ Metric.ball 0 ρ
    rw [show Φ_inv (realEmbed x₀) = 0 from by rw [← Phi_zero x₀ ys, hΦ_left]]
    exact Metric.mem_ball_self hρ_pos
  -- DifferentiableOn ℂ F_loc P: composition of holomorphic maps
  · exact hF₀_diff.comp hΦ_inv_diff.differentiableOn (fun _ hz => hz)
  -- Agreement with f_plus on P ∩ T(C):
  -- F_loc(z) = F₀(Φ_inv z), and Φ_inv z ∈ ball with Phi(Φ_inv z) = z ∈ T(C),
  -- so hF₀_eq_plus gives F₀(Φ_inv z) = f_plus(Phi(Φ_inv z)) = f_plus(z).
  · intro z ⟨hzP, hzT⟩
    show F₀ (Φ_inv z) = f_plus z
    rw [hF₀_eq_plus (Φ_inv z) hzP (by rw [hΦ_right]; exact hzT), hΦ_right]
  -- Agreement with f_minus on P ∩ T(-C): symmetric
  · intro z ⟨hzP, hzT⟩
    show F₀ (Φ_inv z) = f_minus z
    rw [hF₀_eq_minus (Φ_inv z) hzP (by rw [hΦ_right]; exact hzT), hΦ_right]

/-! ### Local Extension Lemma -/

/-- **Local holomorphic extension near a real point.**

    For each x₀ ∈ E, there exists a neighborhood P of realEmbed x₀ and a
    holomorphic function F_loc on P that agrees with f₊ on T(C) and f₋ on T(-C).

    For m = 1: there are no gap points (Im(z) ∈ C ∪ (-C) for all z near ℝ), so the
    extension is the standard glued function (Morera's theorem argument).

    For m ≥ 2: gap points (Im(z) ∉ C ∪ (-C) ∪ {0}) are filled by the iterated
    Cauchy integral of bv over a real box. The Cauchy transform is separately
    holomorphic in each variable and continuous, hence jointly holomorphic by
    Osgood's lemma. Agreement with f₊/f₋ follows from contour deformation. -/
private lemma local_eow_extension {m : ℕ} (hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (bv x)))
    (x₀ : Fin m → ℝ) (hx₀ : x₀ ∈ E) :
    ∃ (P : Set (Fin m → ℂ)) (F_loc : (Fin m → ℂ) → ℂ),
      IsOpen P ∧ Convex ℝ P ∧
      (∀ z ∈ P, (fun i => starRingEnd ℂ (z i)) ∈ P) ∧
      realEmbed x₀ ∈ P ∧ DifferentiableOn ℂ F_loc P ∧
      (∀ z ∈ P ∩ TubeDomain C, F_loc z = f_plus z) ∧
      (∀ z ∈ P ∩ TubeDomain (Neg.neg '' C), F_loc z = f_minus z) := by
  by_cases hm1 : m = 1
  · -- m = 1: bridge to 1D edge-of-the-wedge theorem
    subst hm1
    -- Helper: Fin 1 functions are determined by value at 0
    have fun_eq : ∀ (w : Fin 1 → ℂ), w = fun _ => w 0 :=
      fun w => funext (fun i => congr_arg w (Subsingleton.elim i 0))
    have fun_eq_r : ∀ (w : Fin 1 → ℝ), w = fun _ => w 0 :=
      fun w => funext (fun i => congr_arg w (Subsingleton.elim i 0))
    -- Classify cone as positive or negative
    rcases cone_fin1_pos_or_neg C hconv h0 hcone hCne with hC_pos | hC_neg
    · -- Positive cone: TubeDomain C ≈ upper half-plane
      -- Embedding: ℂ → Fin 1 → ℂ
      have embed_diff : Differentiable ℂ (fun z : ℂ => (fun (_ : Fin 1) => z)) :=
        differentiable_pi.mpr (fun _ => differentiable_id)
      -- UHP maps to TubeDomain C under embedding
      have embed_uhp_tc : ∀ z : ℂ, z.im > 0 →
          (fun (_ : Fin 1) => z) ∈ TubeDomain C :=
        fun z hz => uhp_subset_tubeDomain_fin1 C hcone hCne hC_pos
          (show ((fun (_ : Fin 1) => z) 0).im > 0 from hz)
      -- LHP maps to TubeDomain (-C) under embedding
      have embed_lhp_tcn : ∀ z : ℂ, z.im < 0 →
          (fun (_ : Fin 1) => z) ∈ TubeDomain (Neg.neg '' C) := by
        intro z hz
        show (fun i => ((fun (_ : Fin 1) => z) i).im) ∈ Neg.neg '' C
        simp only
        -- Need: (fun _ => z.im) ∈ Neg.neg '' C, i.e., ∃ y ∈ C, (fun _ => z.im) = -y
        obtain ⟨y₀, hy₀⟩ := hCne
        have hy₀_pos := hC_pos y₀ hy₀
        set s := -z.im / y₀ 0
        have hs : 0 < s := div_pos (neg_pos.mpr hz) hy₀_pos
        refine ⟨s • y₀, hcone s y₀ hs hy₀, ?_⟩
        ext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        fin_cases i; simp only [s, Fin.zero_eta]; field_simp
      -- Find interval (a, b) around x₀ 0 contained in E
      have hE_r : IsOpen {t : ℝ | (fun (_ : Fin 1) => t) ∈ E} :=
        hE.preimage (continuous_pi (fun _ => continuous_id))
      have hx₀_r : x₀ 0 ∈ {t : ℝ | (fun (_ : Fin 1) => t) ∈ E} := by
        show (fun _ => x₀ 0) ∈ E; rwa [← fun_eq_r x₀]
      obtain ⟨ε, hε, hball_E⟩ := Metric.isOpen_iff.mp hE_r _ hx₀_r
      set a := x₀ 0 - ε / 2 with ha_def
      set b := x₀ 0 + ε / 2 with hb_def
      have hab : a < b := by linarith
      -- Helper: points in (a,b) are in E
      have interval_in_E : ∀ x : ℝ, a < x → x < b → (fun (_ : Fin 1) => x) ∈ E := by
        intro x hax hxb
        apply hball_E; rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
      -- Define 1D functions with correct boundary values
      let fp : ℂ → ℂ := fun z =>
        if z.im > 0 then f_plus (fun _ => z) else bv (fun _ => z.re)
      let fm : ℂ → ℂ := fun z =>
        if z.im < 0 then f_minus (fun _ => z) else bv (fun _ => z.re)
      -- Verify 1D hypotheses
      have hfp_diff : DifferentiableOn ℂ fp EOW.UpperHalfPlane :=
        (hf_plus.comp embed_diff.differentiableOn
          (fun z hz => embed_uhp_tc z hz)).congr
          (fun z hz => if_pos hz)
      have hfm_diff : DifferentiableOn ℂ fm EOW.LowerHalfPlane :=
        (hf_minus.comp embed_diff.differentiableOn
          (fun z hz => embed_lhp_tcn z hz)).congr
          (fun z hz => if_pos hz)
      have hmatch : ∀ x : ℝ, a < x → x < b → fp ↑x = fm ↑x := by
        intro x _ _
        show (if (x : ℂ).im > 0 then _ else _) = (if (x : ℂ).im < 0 then _ else _)
        simp [Complex.ofReal_im]
      -- Helper: embed maps nhdsWithin to nhdsWithin for UHP
      have embed_tendsto_uhp : ∀ x : ℝ,
          Filter.Tendsto (fun z : ℂ => (fun _ : Fin 1 => z))
            (nhdsWithin (↑x) EOW.UpperHalfPlane)
            (nhdsWithin (realEmbed (fun _ => x)) (TubeDomain C)) :=
        fun x => ((continuous_pi fun _ => continuous_id).continuousWithinAt).tendsto_nhdsWithin
          (fun z hz => embed_uhp_tc z hz)
      -- Helper: embed maps nhdsWithin to nhdsWithin for LHP
      have embed_tendsto_lhp : ∀ x : ℝ,
          Filter.Tendsto (fun z : ℂ => (fun _ : Fin 1 => z))
            (nhdsWithin (↑x) EOW.LowerHalfPlane)
            (nhdsWithin (realEmbed (fun _ => x)) (TubeDomain (Neg.neg '' C))) :=
        fun x => ((continuous_pi fun _ => continuous_id).continuousWithinAt).tendsto_nhdsWithin
          (fun z hz => embed_lhp_tcn z hz)
      -- Boundary value tendsto from above
      have hcont_plus : ∀ x : ℝ, a < x → x < b →
          Filter.Tendsto fp (nhdsWithin ↑x EOW.UpperHalfPlane) (nhds (fp ↑x)) := by
        intro x hax hxb
        have hx_E := interval_in_E x hax hxb
        have hfp_x : fp ↑x = bv (fun _ => x) := by simp [fp, Complex.ofReal_im]
        rw [hfp_x]
        -- fp = f_plus ∘ embed on UHP
        have key : fp =ᶠ[nhdsWithin (↑x) EOW.UpperHalfPlane]
            (fun z => f_plus (fun _ => z)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im > 0)
          exact if_pos hz
        unfold Filter.Tendsto
        rw [Filter.map_congr key]
        exact (hf_plus_bv (fun _ => x) hx_E).comp (embed_tendsto_uhp x)
      -- Boundary value tendsto from below
      have hcont_minus : ∀ x : ℝ, a < x → x < b →
          Filter.Tendsto fm (nhdsWithin ↑x EOW.LowerHalfPlane) (nhds (fm ↑x)) := by
        intro x hax hxb
        have hx_E := interval_in_E x hax hxb
        have hfm_x : fm ↑x = bv (fun _ => x) := by simp [fm, Complex.ofReal_im]
        rw [hfm_x]
        have key : fm =ᶠ[nhdsWithin (↑x) EOW.LowerHalfPlane]
            (fun z => f_minus (fun _ => z)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0)
          exact if_pos hz
        unfold Filter.Tendsto
        rw [Filter.map_congr key]
        exact (hf_minus_bv (fun _ => x) hx_E).comp (embed_tendsto_lhp x)
      -- Continuity along the real line
      have hbv_cont_1d : ∀ x₀' : ℝ, a < x₀' → x₀' < b →
          Filter.Tendsto fp (nhdsWithin ↑x₀' {c : ℂ | c.im = 0}) (nhds (fp ↑x₀')) := by
        intro x hax hxb
        have hfp_x : fp ↑x = bv (fun _ => x) := by simp [fp, Complex.ofReal_im]
        rw [hfp_x]
        have hx_E := interval_in_E x hax hxb
        -- On {c | c.im = 0}, fp = bv ∘ (fun z => fun _ => z.re)
        have key : fp =ᶠ[nhdsWithin (↑x) {c : ℂ | c.im = 0}]
            (fun z => bv (fun _ => z.re)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im = 0)
          show (if z.im > 0 then _ else _) = _
          simp [hz]
        -- bv ∘ (fun z => fun _ => z.re) is continuous at ↑x
        have hca : ContinuousAt (fun z : ℂ => bv (fun _ : Fin 1 => z.re)) ↑x :=
          ((hbv_cont (fun _ => x) hx_E).continuousAt (hE.mem_nhds hx_E)).comp
            (continuous_pi (fun _ => Complex.continuous_re)).continuousAt
        unfold Filter.Tendsto
        rw [Filter.map_congr key]
        exact hca.tendsto.mono_left nhdsWithin_le_nhds
      -- Apply the 1D edge-of-the-wedge theorem
      obtain ⟨U_1d, F_1d, hU_open, hU_conv, hU_conj, hU_int, hF_diff, hF_plus, hF_minus,
          _hball⟩ :=
        edge_of_the_wedge_1d a b hab fp fm hfp_diff hfm_diff
          hcont_plus hcont_minus hmatch hbv_cont_1d
      -- Convert back to Fin 1 → ℂ
      refine ⟨{w | w 0 ∈ U_1d}, F_1d ∘ (· 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- P is open (preimage of open under continuous projection)
        exact hU_open.preimage (continuous_apply 0)
      · -- P is convex (preimage of convex under linear map)
        exact hU_conv.linear_preimage (LinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℂ) 0)
      · -- P is conjugation-symmetric
        intro z hz
        exact hU_conj (z 0) hz
      · -- realEmbed x₀ ∈ P
        show (realEmbed x₀) 0 ∈ U_1d
        simp only [realEmbed]
        exact hU_int (x₀ 0) (by linarith) (by linarith)
      · -- F_loc is holomorphic on P
        exact hF_diff.comp ((differentiable_pi (𝕜 := ℂ)).mp differentiable_id 0).differentiableOn
          (fun w hw => hw)
      · -- F_loc = f_plus on P ∩ TubeDomain C
        intro w ⟨hw_P, hw_tc⟩
        have him : (w 0).im > 0 := hC_pos _ hw_tc
        show F_1d (w 0) = f_plus w
        rw [hF_plus (w 0) ⟨hw_P, him⟩]
        show fp (w 0) = f_plus w
        exact (if_pos him).trans (congr_arg f_plus (fun_eq w).symm)
      · -- F_loc = f_minus on P ∩ TubeDomain (-C)
        intro w ⟨hw_P, hw_tc⟩
        have him : (w 0).im < 0 :=
          tubeDomain_fin1_neg_subset_lhp C hC_pos hw_tc
        show F_1d (w 0) = f_minus w
        rw [hF_minus (w 0) ⟨hw_P, him⟩]
        show fm (w 0) = f_minus w
        exact (if_pos him).trans (congr_arg f_minus (fun_eq w).symm)
    · -- Negative cone case: TubeDomain C ≈ lower half-plane
      have embed_diff : Differentiable ℂ (fun z : ℂ => (fun (_ : Fin 1) => z)) :=
        differentiable_pi.mpr (fun _ => differentiable_id)
      have fun_eq : ∀ (w : Fin 1 → ℂ), w = fun _ => w 0 :=
        fun w => funext (fun i => congr_arg w (Subsingleton.elim i 0))
      have fun_eq_r : ∀ (w : Fin 1 → ℝ), w = fun _ => w 0 :=
        fun w => funext (fun i => congr_arg w (Subsingleton.elim i 0))
      -- TubeDomain C ⊂ LHP (negative cone)
      have tc_subset_lhp : TubeDomain C ⊆ { z : Fin 1 → ℂ | (z 0).im < 0 } :=
        fun z hz => hC_neg _ hz
      -- TubeDomain (-C) ⊂ UHP (negation of negative cone)
      have tcn_subset_uhp : TubeDomain (Neg.neg '' C) ⊆ { z : Fin 1 → ℂ | (z 0).im > 0 } := by
        intro z hz
        simp only [TubeDomain, Set.mem_setOf_eq, Set.mem_image] at hz
        obtain ⟨y, hy, hyz⟩ := hz
        have := congr_fun hyz 0; simp only [Pi.neg_apply] at this
        show (z 0).im > 0; linarith [hC_neg y hy]
      -- LHP ⊆ TubeDomain C (every z with im < 0 is in tube)
      have lhp_subset_tc : { z : Fin 1 → ℂ | (z 0).im < 0 } ⊆ TubeDomain C := by
        intro z hz
        show (fun i => (z i).im) ∈ C
        obtain ⟨y₀, hy₀⟩ := hCne
        have hy₀_neg := hC_neg y₀ hy₀
        have hy₀_ne : (y₀ 0 : ℝ) ≠ 0 := ne_of_lt hy₀_neg
        set s := (z 0).im / (y₀ 0)
        have hs : 0 < s := div_pos_of_neg_of_neg hz hy₀_neg
        convert hcone s y₀ hs hy₀ using 1
        ext i; fin_cases i
        simp only [Pi.smul_apply, smul_eq_mul, s, Fin.zero_eta]
        field_simp [hy₀_ne]
      -- UHP ⊆ TubeDomain (-C)
      have uhp_subset_tcn : { z : Fin 1 → ℂ | (z 0).im > 0 } ⊆ TubeDomain (Neg.neg '' C) := by
        intro z (hz : (z 0).im > 0)
        show (fun i => (z i).im) ∈ Neg.neg '' C
        obtain ⟨y₀, hy₀⟩ := hCne
        have hy₀_neg := hC_neg y₀ hy₀
        have hy₀_ne : (y₀ 0 : ℝ) ≠ 0 := ne_of_lt hy₀_neg
        set s := -(z 0).im / (y₀ 0)
        have hs : 0 < s := div_pos_of_neg_of_neg (by linarith) hy₀_neg
        refine ⟨s • y₀, hcone s y₀ hs hy₀, ?_⟩
        ext i; fin_cases i
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, s, Fin.zero_eta]
        field_simp
      -- Find interval around x₀ 0
      have hE_r : IsOpen {t : ℝ | (fun (_ : Fin 1) => t) ∈ E} :=
        hE.preimage (continuous_pi (fun _ => continuous_id))
      have hx₀_r : x₀ 0 ∈ {t : ℝ | (fun (_ : Fin 1) => t) ∈ E} := by
        show (fun _ => x₀ 0) ∈ E; rwa [← fun_eq_r x₀]
      obtain ⟨ε, hε, hball_E⟩ := Metric.isOpen_iff.mp hE_r _ hx₀_r
      set a := x₀ 0 - ε / 2 with ha_def
      set b := x₀ 0 + ε / 2 with hb_def
      have hab : a < b := by linarith
      have interval_in_E : ∀ x : ℝ, a < x → x < b → (fun (_ : Fin 1) => x) ∈ E := by
        intro x hax hxb
        apply hball_E; rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
      -- Define 1D functions: fp on UHP uses f_minus, fm on LHP uses f_plus
      let fp : ℂ → ℂ := fun z =>
        if z.im > 0 then f_minus (fun _ => z) else bv (fun _ => z.re)
      let fm : ℂ → ℂ := fun z =>
        if z.im < 0 then f_plus (fun _ => z) else bv (fun _ => z.re)
      have hfp_diff : DifferentiableOn ℂ fp EOW.UpperHalfPlane :=
        (hf_minus.comp embed_diff.differentiableOn
          (fun z hz => uhp_subset_tcn hz)).congr (fun z hz => if_pos hz)
      have hfm_diff : DifferentiableOn ℂ fm EOW.LowerHalfPlane :=
        (hf_plus.comp embed_diff.differentiableOn
          (fun z hz => lhp_subset_tc hz)).congr (fun z hz => if_pos hz)
      have hmatch : ∀ x : ℝ, a < x → x < b → fp ↑x = fm ↑x := by
        intro x _ _; show (if (x : ℂ).im > 0 then _ else _) = (if (x : ℂ).im < 0 then _ else _)
        simp [Complex.ofReal_im]
      -- Tendsto helpers
      have embed_tendsto_uhp : ∀ x : ℝ,
          Filter.Tendsto (fun z : ℂ => (fun _ : Fin 1 => z))
            (nhdsWithin (↑x) EOW.UpperHalfPlane)
            (nhdsWithin (realEmbed (fun _ => x)) (TubeDomain (Neg.neg '' C))) :=
        fun x => ((continuous_pi fun _ => continuous_id).continuousWithinAt).tendsto_nhdsWithin
          (fun z hz => uhp_subset_tcn hz)
      have embed_tendsto_lhp : ∀ x : ℝ,
          Filter.Tendsto (fun z : ℂ => (fun _ : Fin 1 => z))
            (nhdsWithin (↑x) EOW.LowerHalfPlane)
            (nhdsWithin (realEmbed (fun _ => x)) (TubeDomain C)) :=
        fun x => ((continuous_pi fun _ => continuous_id).continuousWithinAt).tendsto_nhdsWithin
          (fun z hz => lhp_subset_tc hz)
      have hcont_plus : ∀ x : ℝ, a < x → x < b →
          Filter.Tendsto fp (nhdsWithin ↑x EOW.UpperHalfPlane) (nhds (fp ↑x)) := by
        intro x hax hxb
        have hx_E := interval_in_E x hax hxb
        have hfp_x : fp ↑x = bv (fun _ => x) := by simp [fp, Complex.ofReal_im]
        rw [hfp_x]
        have key : fp =ᶠ[nhdsWithin (↑x) EOW.UpperHalfPlane]
            (fun z => f_minus (fun _ => z)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im > 0); exact if_pos hz
        unfold Filter.Tendsto; rw [Filter.map_congr key]
        exact (hf_minus_bv (fun _ => x) hx_E).comp (embed_tendsto_uhp x)
      have hcont_minus : ∀ x : ℝ, a < x → x < b →
          Filter.Tendsto fm (nhdsWithin ↑x EOW.LowerHalfPlane) (nhds (fm ↑x)) := by
        intro x hax hxb
        have hx_E := interval_in_E x hax hxb
        have hfm_x : fm ↑x = bv (fun _ => x) := by simp [fm, Complex.ofReal_im]
        rw [hfm_x]
        have key : fm =ᶠ[nhdsWithin (↑x) EOW.LowerHalfPlane]
            (fun z => f_plus (fun _ => z)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0); exact if_pos hz
        unfold Filter.Tendsto; rw [Filter.map_congr key]
        exact (hf_plus_bv (fun _ => x) hx_E).comp (embed_tendsto_lhp x)
      have hbv_cont_1d : ∀ x₀' : ℝ, a < x₀' → x₀' < b →
          Filter.Tendsto fp (nhdsWithin ↑x₀' {c : ℂ | c.im = 0}) (nhds (fp ↑x₀')) := by
        intro x hax hxb
        have hfp_x : fp ↑x = bv (fun _ => x) := by simp [fp, Complex.ofReal_im]
        rw [hfp_x]
        have hx_E := interval_in_E x hax hxb
        have key : fp =ᶠ[nhdsWithin (↑x) {c : ℂ | c.im = 0}]
            (fun z => bv (fun _ => z.re)) := by
          filter_upwards [self_mem_nhdsWithin] with z (hz : z.im = 0)
          show (if z.im > 0 then _ else _) = _; simp [hz]
        have hca : ContinuousAt (fun z : ℂ => bv (fun _ : Fin 1 => z.re)) ↑x :=
          ((hbv_cont (fun _ => x) hx_E).continuousAt (hE.mem_nhds hx_E)).comp
            (continuous_pi (fun _ => Complex.continuous_re)).continuousAt
        unfold Filter.Tendsto; rw [Filter.map_congr key]
        exact hca.tendsto.mono_left nhdsWithin_le_nhds
      -- Apply 1D EOW
      obtain ⟨U_1d, F_1d, hU_open, hU_conv, hU_conj, hU_int, hF_diff, hF_plus_1d, hF_minus_1d,
          _hball⟩ :=
        edge_of_the_wedge_1d a b hab fp fm hfp_diff hfm_diff
          hcont_plus hcont_minus hmatch hbv_cont_1d
      -- Convert back to Fin 1 → ℂ
      refine ⟨{w | w 0 ∈ U_1d}, F_1d ∘ (· 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hU_open.preimage (continuous_apply 0)
      · exact hU_conv.linear_preimage (LinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℂ) 0)
      · intro z hz; exact hU_conj (z 0) hz
      · show (realEmbed x₀) 0 ∈ U_1d; simp only [realEmbed]
        exact hU_int (x₀ 0) (by linarith) (by linarith)
      · exact hF_diff.comp ((differentiable_pi (𝕜 := ℂ)).mp differentiable_id 0).differentiableOn
          (fun w hw => hw)
      · -- F_loc = f_plus on P ∩ TubeDomain C (C maps to LHP)
        intro w ⟨hw_P, hw_tc⟩
        have him : (w 0).im < 0 := tc_subset_lhp hw_tc
        show F_1d (w 0) = f_plus w
        rw [hF_minus_1d (w 0) ⟨hw_P, him⟩]
        show fm (w 0) = f_plus w
        exact (if_pos him).trans (congr_arg f_plus (fun_eq w).symm)
      · -- F_loc = f_minus on P ∩ TubeDomain (-C) (-C maps to UHP)
        intro w ⟨hw_P, hw_tc⟩
        have him : (w 0).im > 0 := tcn_subset_uhp hw_tc
        show F_1d (w 0) = f_minus w
        rw [hF_plus_1d (w 0) ⟨hw_P, him⟩]
        show fp (w 0) = f_minus w
        exact (if_pos him).trans (congr_arg f_minus (fun_eq w).symm)
  · -- m ≥ 2: Coordinate change + iterated 1D EOW + Osgood.
    have hm2 : 2 ≤ m := by omega
    exact eow_extension_m2 hm C hC hconv h0 hcone hCne f_plus f_minus
      hf_plus hf_minus E hE bv hbv_cont hf_plus_bv hf_minus_bv x₀ hx₀ hm2

/-- Any nonempty open set in ℂᵐ containing a real point meets the tube domain T(C).
    This is because we can perturb the imaginary part of the real point into C. -/
lemma nonempty_open_real_inter_tubeDomain {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (V : Set (Fin m → ℂ)) (hV : IsOpen V)
    (x : Fin m → ℝ) (hx : realEmbed x ∈ V) :
    (V ∩ TubeDomain C).Nonempty := by
  obtain ⟨y₀, hy₀⟩ := hCne
  -- Path: t ↦ x + t * I * y₀ (in ℂᵐ)
  set g : ℝ → (Fin m → ℂ) := fun t => fun i => (x i : ℂ) + ↑t * I * ↑(y₀ i)
  have hg_cont : Continuous g := continuous_pi fun i =>
    continuous_const.add (((continuous_ofReal.mul continuous_const).mul continuous_const))
  have hg_zero : g 0 = realEmbed x := by ext i; simp [g, realEmbed]
  -- Preimage of V under g is open and contains 0
  have hV_pre : IsOpen (g ⁻¹' V) := hg_cont.isOpen_preimage V hV
  have h0_mem : (0 : ℝ) ∈ g ⁻¹' V := by show g 0 ∈ V; rw [hg_zero]; exact hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV_pre 0 h0_mem
  -- Take t = ε / 2 > 0
  have hε2 : ε / 2 > 0 := by linarith
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε2]; linarith
  refine ⟨g (ε / 2), hball hmem, ?_⟩
  -- g(ε/2) ∈ TubeDomain C: Im(g(ε/2)) = (ε/2) • y₀ ∈ C
  show (fun i => (g (ε / 2) i).im) ∈ C
  have key : (fun i => (g (ε / 2) i).im) = (ε / 2) • y₀ := by
    ext i; simp [g, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
  rw [key]
  exact hcone _ y₀ hε2 hy₀

/-- Any two local extensions from the same family agree on overlaps.

    This follows from the identity theorem: both F_loc x₁ and F_loc x₂ agree
    with f_plus on the tube domain portion. On a connected overlap that meets T(C),
    the identity theorem forces F_loc x₁ = F_loc x₂ everywhere on the overlap. -/
private lemma local_extensions_consistent {m : ℕ} (_hm : 0 < m)
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (_hconv : Convex ℝ C) (_h0 : (0 : Fin m → ℝ) ∉ C)
    (_hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (_hCne : C.Nonempty)
    (f_plus : (Fin m → ℂ) → ℂ) (_hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (E : Set (Fin m → ℝ)) (_hE : IsOpen E)
    (P_loc : (Fin m → ℝ) → Set (Fin m → ℂ))
    (F_loc : (Fin m → ℝ) → (Fin m → ℂ) → ℂ)
    (hP_open : ∀ x₀ ∈ E, IsOpen (P_loc x₀))
    (hP_conv : ∀ x₀ ∈ E, Convex ℝ (P_loc x₀))
    (hP_tube_inter : ∀ x₁ x₂ : Fin m → ℝ, x₁ ∈ E → x₂ ∈ E →
      (P_loc x₁ ∩ P_loc x₂).Nonempty → (P_loc x₁ ∩ P_loc x₂ ∩ TubeDomain C).Nonempty)
    (_hx_mem : ∀ x₀ ∈ E, realEmbed x₀ ∈ P_loc x₀)
    (hF_diff : ∀ x₀ ∈ E, DifferentiableOn ℂ (F_loc x₀) (P_loc x₀))
    (hF_eq_plus : ∀ x₀ ∈ E, ∀ z ∈ P_loc x₀ ∩ TubeDomain C, F_loc x₀ z = f_plus z) :
    ∀ (x₁ x₂ : Fin m → ℝ), x₁ ∈ E → x₂ ∈ E →
      ∀ w ∈ P_loc x₁ ∩ P_loc x₂, F_loc x₁ w = F_loc x₂ w := by
  intro x₁ x₂ hx₁ hx₂ w hw
  set V := P_loc x₁ ∩ P_loc x₂ with hV_def
  have hV_open : IsOpen V := (hP_open x₁ hx₁).inter (hP_open x₂ hx₂)
  have hV_conv : Convex ℝ V := (hP_conv x₁ hx₁).inter (hP_conv x₂ hx₂)
  have hV_ne : V.Nonempty := ⟨w, hw⟩
  have hV_preconn : IsPreconnected V := hV_conv.isPreconnected
  -- Get a point z₀ ∈ V ∩ TubeDomain C
  obtain ⟨z₀, hz₀_V, hz₀_tc⟩ := hP_tube_inter x₁ x₂ hx₁ hx₂ hV_ne
  -- Both F_loc are analytic on V (open, holomorphic on open subset)
  have hF₁_ana : AnalyticOnNhd ℂ (F_loc x₁) V := fun z hz =>
    differentiableOn_analyticAt hV_open
      ((hF_diff x₁ hx₁).mono Set.inter_subset_left) hz
  have hF₂_ana : AnalyticOnNhd ℂ (F_loc x₂) V := fun z hz =>
    differentiableOn_analyticAt hV_open
      ((hF_diff x₂ hx₂).mono Set.inter_subset_right) hz
  -- They agree near z₀: both equal f_plus on the open set V ∩ TubeDomain C
  have hFeq : F_loc x₁ =ᶠ[nhds z₀] F_loc x₂ := by
    filter_upwards [hV_open.mem_nhds hz₀_V, (tubeDomain_isOpen hC).mem_nhds hz₀_tc]
      with z hz_V hz_tc
    exact (hF_eq_plus x₁ hx₁ z ⟨hz_V.1, hz_tc⟩).trans
      (hF_eq_plus x₂ hx₂ z ⟨hz_V.2, hz_tc⟩).symm
  -- Identity theorem: analytic functions agreeing near z₀ on a preconnected set agree everywhere
  exact hF₁_ana.eqOn_of_preconnected_of_eventuallyEq hF₂_ana hV_preconn hz₀_V hFeq hw

/-! ### Edge-of-the-Wedge Theorem -/

/-- **The Edge-of-the-Wedge Theorem** (Bogoliubov, 1956).

    Two holomorphic functions on opposite tube domains with matching continuous
    boundary values on a real open set extend to a unique holomorphic function
    on a complex neighborhood.

    This is the theorem that replaces the axiom `edge_of_the_wedge` in
    `AnalyticContinuation.lean`. The proof constructs the extension at gap points
    via the iterated Cauchy integral on polydiscs centered at real points.

    **Proof sketch:**
    For each x₀ ∈ E, choose a polydisc P(x₀, r) centered at the real point x₀.
    1. Define F on P via `cauchyIntegralPolydisc bv x₀ r z`
    2. F is holomorphic on P (by `cauchyIntegralPolydisc_differentiableOn`)
    3. F = f₊ on P ∩ T(C) (both agree with bv on the real slice, identity theorem)
    4. F = f₋ on P ∩ T(-C) (same argument)
    5. U = ⋃_{x₀} P(x₀, r(x₀)) is the desired open neighborhood
    6. Uniqueness: any holomorphic G on U agreeing with f₊ on U ∩ T(C) equals F,
       by the identity theorem (U ∩ T(C) is open and nonempty). -/
theorem edge_of_the_wedge_theorem {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus
        (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (realEmbed x) (TubeDomain (Neg.neg '' C))) (nhds (bv x))) :
    ∃ (U : Set (Fin m → ℂ)) (F : (Fin m → ℂ) → ℂ),
      IsOpen U ∧
      (∀ x ∈ E, realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ TubeDomain C, F z = f_plus z) ∧
      (∀ z ∈ U ∩ TubeDomain (Neg.neg '' C), F z = f_minus z) ∧
      -- Uniqueness: any holomorphic function on U agreeing with f_plus on the
      -- positive tube must agree with F everywhere on U.
      (∀ (G : (Fin m → ℂ) → ℂ), DifferentiableOn ℂ G U →
        (∀ z ∈ U ∩ TubeDomain C, G z = f_plus z) → ∀ z ∈ U, G z = F z) := by
  -- Case split on m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- m = 0: contradiction. Fin 0 → ℝ is a subsingleton, so C.Nonempty gives 0 ∈ C.
    exfalso
    obtain ⟨y, hy⟩ := hCne
    have : y = (0 : Fin 0 → ℝ) := Subsingleton.elim y 0
    rw [this] at hy
    exact h0 hy
  · -- m ≥ 1: construct global extension from local patches
    -- Step 1: Get local extensions for each x₀ ∈ E
    -- For x₀ ∉ E, provide trivial data to make choose non-dependent
    have loc : ∀ x₀ : Fin m → ℝ, ∃ (P : Set (Fin m → ℂ)) (F_loc : (Fin m → ℂ) → ℂ),
        (x₀ ∈ E → IsOpen P) ∧ (x₀ ∈ E → Convex ℝ P) ∧
        (x₀ ∈ E → ∀ z ∈ P, (fun i => starRingEnd ℂ (z i)) ∈ P) ∧
        (x₀ ∈ E → realEmbed x₀ ∈ P) ∧
        (x₀ ∈ E → DifferentiableOn ℂ F_loc P) ∧
        (x₀ ∈ E → ∀ z ∈ P ∩ TubeDomain C, F_loc z = f_plus z) ∧
        (x₀ ∈ E → ∀ z ∈ P ∩ TubeDomain (Neg.neg '' C), F_loc z = f_minus z) := by
      intro x₀
      by_cases hx₀ : x₀ ∈ E
      · obtain ⟨P, Fl, h1, h1b, h1c, h2, h3, h4, h5⟩ := local_eow_extension hm C hC hconv h0
          hcone hCne f_plus f_minus hf_plus hf_minus E hE bv hbv_cont
          hf_plus_bv hf_minus_bv x₀ hx₀
        exact ⟨P, Fl, fun _ => h1, fun _ => h1b, fun _ => h1c,
          fun _ => h2, fun _ => h3, fun _ => h4, fun _ => h5⟩
      · exact ⟨∅, 0, fun h => absurd h hx₀, fun h => absurd h hx₀, fun h => absurd h hx₀,
          fun h => absurd h hx₀, fun h => absurd h hx₀, fun h => absurd h hx₀,
          fun h => absurd h hx₀⟩
    choose P_loc F_loc hP_open hP_conv hP_conj hx_mem hF_diff hF_eq_plus hF_eq_minus using loc
    -- Derive: any nonempty overlap of patches meets the tube domain
    have hP_tube_inter : ∀ x₁ x₂ : Fin m → ℝ, x₁ ∈ E → x₂ ∈ E →
        (P_loc x₁ ∩ P_loc x₂).Nonempty →
        (P_loc x₁ ∩ P_loc x₂ ∩ TubeDomain C).Nonempty := by
      intro x₁ x₂ hx₁ hx₂ ⟨z, hz₁, hz₂⟩
      -- conj(z) is in both patches
      have hcz₁ := hP_conj x₁ hx₁ z hz₁
      have hcz₂ := hP_conj x₂ hx₂ z hz₂
      -- The midpoint (z + conj z)/2 = realEmbed(Re z) is in both patches (by convexity)
      set zc : Fin m → ℂ := fun i => starRingEnd ℂ (z i)
      set xr : Fin m → ℝ := fun i => (z i).re
      have hmid_eq : (1/2 : ℝ) • z + (1/2 : ℝ) • zc = realEmbed xr := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, realEmbed, xr, zc]
        rw [← mul_add, Complex.add_conj]
        push_cast; ring
      have hmid₁ : realEmbed xr ∈ P_loc x₁ := hmid_eq ▸
        (hP_conv x₁ hx₁) hz₁ hcz₁ (by norm_num) (by norm_num) (by norm_num)
      have hmid₂ : realEmbed xr ∈ P_loc x₂ := hmid_eq ▸
        (hP_conv x₂ hx₂) hz₂ hcz₂ (by norm_num) (by norm_num) (by norm_num)
      -- Near the real point, tube domain points exist
      exact nonempty_open_real_inter_tubeDomain C hcone hCne _
        ((hP_open x₁ hx₁).inter (hP_open x₂ hx₂)) xr ⟨hmid₁, hmid₂⟩
    -- Step 2: Define global U and F
    set U : Set (Fin m → ℂ) := ⋃ x ∈ E, P_loc x with hU_def
    -- F is defined via F_loc: for z ∈ P_loc(x₀), F(z) = F_loc(x₀)(z).
    -- Consistency (independence of x₀) follows from the identity theorem.
    -- For z ∉ U, F(z) = 0 (irrelevant, since we only need DifferentiableOn on U).
    letI : ∀ (p : Prop), Decidable p := Classical.dec
    let F : (Fin m → ℂ) → ℂ := fun z =>
      if h : ∃ x ∈ E, z ∈ P_loc x then F_loc h.choose z
      else 0
    -- Step 3: Verify all properties
    refine ⟨U, F, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- U is open
      exact isOpen_biUnion (fun x hx => hP_open x hx)
    · -- realEmbed x ∈ U for all x ∈ E
      intro x hx; exact Set.mem_biUnion hx (hx_mem x hx)
    · -- F is holomorphic on U
      intro z hz
      rw [hU_def, Set.mem_iUnion₂] at hz
      obtain ⟨x₀, hx₀, hz_P⟩ := hz
      have hP_nhds : P_loc x₀ ∈ nhds z := (hP_open x₀ hx₀).mem_nhds hz_P
      -- F =ᶠ F_loc x₀ near z
      have hFeq : F =ᶠ[nhds z] F_loc x₀ := by
        filter_upwards [hP_nhds] with w hw
        -- F w = F_loc (choose w) w by dif_pos
        -- F_loc (choose w) w = F_loc x₀ w by consistency
        have hw_ex : ∃ x ∈ E, w ∈ P_loc x := ⟨x₀, hx₀, hw⟩
        have step1 : F w = F_loc hw_ex.choose w := dif_pos hw_ex
        have step2 : F_loc hw_ex.choose w = F_loc x₀ w :=
          local_extensions_consistent hm C hC hconv h0 hcone hCne f_plus hf_plus
            E hE P_loc F_loc hP_open hP_conv hP_tube_inter hx_mem hF_diff hF_eq_plus
            hw_ex.choose x₀ hw_ex.choose_spec.1 hx₀ w ⟨hw_ex.choose_spec.2, hw⟩
        exact step1.trans step2
      -- F_loc x₀ is differentiable at z (interior of open P_loc x₀)
      have hdiff : DifferentiableAt ℂ (F_loc x₀) z :=
        (hF_diff x₀ hx₀ z hz_P).differentiableAt hP_nhds
      exact (hdiff.congr_of_eventuallyEq hFeq).differentiableWithinAt
    · -- F = f_plus on U ∩ T(C)
      intro z ⟨hz_U, hz_tc⟩
      obtain ⟨x, hx, hz_P⟩ := Set.mem_iUnion₂.mp hz_U
      have hz_ex : ∃ x ∈ E, z ∈ P_loc x := ⟨x, hx, hz_P⟩
      have step1 : F z = F_loc hz_ex.choose z := dif_pos hz_ex
      exact step1.trans (hF_eq_plus hz_ex.choose hz_ex.choose_spec.1 z
        ⟨hz_ex.choose_spec.2, hz_tc⟩)
    · -- F = f_minus on U ∩ T(-C)
      intro z ⟨hz_U, hz_tc⟩
      obtain ⟨x, hx, hz_P⟩ := Set.mem_iUnion₂.mp hz_U
      have hz_ex : ∃ x ∈ E, z ∈ P_loc x := ⟨x, hx, hz_P⟩
      have step1 : F z = F_loc hz_ex.choose z := dif_pos hz_ex
      exact step1.trans (hF_eq_minus hz_ex.choose hz_ex.choose_spec.1 z
        ⟨hz_ex.choose_spec.2, hz_tc⟩)
    · -- Uniqueness: G = f_plus on U ∩ T(C) implies G = F on U
      intro G hG_diff hG_eq z hz
      rw [hU_def, Set.mem_iUnion₂] at hz
      obtain ⟨x₀, hx₀, hz_P⟩ := hz
      -- F = F_loc x₀ on P_loc x₀ (by consistency)
      have hF_eq_Floc : ∀ w ∈ P_loc x₀, F w = F_loc x₀ w := by
        intro w hw
        have hw_ex : ∃ x ∈ E, w ∈ P_loc x := ⟨x₀, hx₀, hw⟩
        exact (dif_pos hw_ex).trans
          (local_extensions_consistent hm C hC hconv h0 hcone hCne f_plus hf_plus
            E hE P_loc F_loc hP_open hP_conv hP_tube_inter hx_mem hF_diff hF_eq_plus
            hw_ex.choose x₀ hw_ex.choose_spec.1 hx₀ w ⟨hw_ex.choose_spec.2, hw⟩)
      -- G and F agree on P_loc x₀ ∩ TubeDomain C (both equal f_plus)
      have hGF_agree : ∀ w ∈ P_loc x₀ ∩ TubeDomain C, G w = F w := by
        intro w ⟨hw_P, hw_tc⟩
        exact (hG_eq w ⟨Set.mem_biUnion hx₀ hw_P, hw_tc⟩).trans
          ((hF_eq_Floc w hw_P).trans (hF_eq_plus x₀ hx₀ w ⟨hw_P, hw_tc⟩)).symm
      -- P_loc x₀ ∩ TubeDomain C is nonempty
      obtain ⟨z₀, hz₀_P, hz₀_tc⟩ := nonempty_open_real_inter_tubeDomain C hcone hCne
        _ (hP_open x₀ hx₀) _ (hx_mem x₀ hx₀)
      -- Both analytic on P_loc x₀
      have hG_ana : AnalyticOnNhd ℂ G (P_loc x₀) := fun w hw =>
        differentiableOn_analyticAt (hP_open x₀ hx₀)
          (hG_diff.mono (Set.subset_biUnion_of_mem hx₀)) hw
      have hF_ana : AnalyticOnNhd ℂ F (P_loc x₀) := fun w hw =>
        differentiableOn_analyticAt (hP_open x₀ hx₀)
          ((hF_diff x₀ hx₀).congr hF_eq_Floc) hw
      -- G =ᶠ F near z₀ (they agree on the open set P_loc x₀ ∩ TubeDomain C)
      have hGF_near : G =ᶠ[nhds z₀] F := by
        filter_upwards [(hP_open x₀ hx₀).mem_nhds hz₀_P,
          (tubeDomain_isOpen hC).mem_nhds hz₀_tc] with w hw_P hw_tc
        exact hGF_agree w ⟨hw_P, hw_tc⟩
      -- Identity theorem on the preconnected set P_loc x₀
      exact hG_ana.eqOn_of_preconnected_of_eventuallyEq hF_ana
        (hP_conv x₀ hx₀).isPreconnected hz₀_P hGF_near hz_P

end SCV

end
