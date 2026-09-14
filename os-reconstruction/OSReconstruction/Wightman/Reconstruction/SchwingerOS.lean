/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Mathlib429Compat
import OSReconstruction.Specification
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.WithSeminorms










set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped SchwartzMap
open scoped Convolution
open scoped Pointwise
open Topology

variable (d : ℕ) [NeZero d]

set_option linter.unusedSectionVars false













/-- The OS inner product with explicit summation bounds. -/
def OSInnerProductN (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (F G : BorchersSequence d) (N₁ N₂ : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N₁,
    ∑ m ∈ Finset.range N₂,
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

/-- The standard OS inner product equals the naturally bounded version. -/
theorem OSInnerProduct_eq_N (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (F G : BorchersSequence d) :
    OSInnerProduct d S F G = OSInnerProductN d S F G (F.bound + 1) (G.bound + 1) :=
  rfl

/-- The genuine zero-diagonal compatibility condition for the OS tensor terms
    appearing in `OSInnerProduct`.

    This is the precise hypothesis needed for additive manipulations on the
    Euclidean side after the hard cut to `ZeroDiagonalSchwartz`. -/
def OSTensorAdmissible (F G : BorchersSequence d) : Prop :=
  ∀ n m, VanishesToInfiniteOrderOnCoincidence
    ((F.funcs n).osConjTensorProduct (G.funcs m))

@[simp]
theorem SchwartzNPoint.osConj_zero {n : ℕ} :
    (0 : SchwartzNPoint d n).osConj = 0 := by
  ext x
  simp [SchwartzNPoint.osConj]

theorem SchwartzNPoint.osConj_add {n : ℕ} (f g : SchwartzNPoint d n) :
    (f + g).osConj = f.osConj + g.osConj := by
  ext x
  simp [SchwartzNPoint.osConj]

theorem SchwartzNPoint.osConj_smul {n : ℕ} (c : ℂ) (f : SchwartzNPoint d n) :
    (c • f).osConj = starRingEnd ℂ c • f.osConj := by
  ext x
  simp [SchwartzNPoint.osConj, smul_eq_mul]

/-- The OS conjugation as a continuous real-linear map. This is the honest
topological form of sesquilinearity on complex Schwartz space. -/
def SchwartzNPoint.osConjRLM {n : ℕ} :
    SchwartzNPoint d n →L[ℝ] SchwartzNPoint d n where
  toLinearMap :=
    { toFun := SchwartzNPoint.osConj (d := d)
      map_add' := SchwartzNPoint.osConj_add (d := d)
      map_smul' := by
        intro c f
        simpa using (SchwartzNPoint.osConj_smul (d := d) (c : ℂ) f) }
  cont := by
    let L : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzNPoint.osConj (d := d)
        map_add' := SchwartzNPoint.osConj_add (d := d)
        map_smul' := by
          intro c f
          simpa using (SchwartzNPoint.osConj_smul (d := d) (c : ℂ) f) }
    apply Seminorm.continuous_from_bounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      L
    intro q
    rcases q with ⟨k, l⟩
    refine ⟨{(k, l)}, 1, ?_⟩
    intro f
    simpa [Finset.sup_singleton] using
      (SchwartzNPoint.seminorm_osConj_le (d := d) k l f)

/-- The OS conjugation is continuous on Schwartz n-point space. -/
theorem SchwartzNPoint.osConj_continuous {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.osConj) :=
  (SchwartzNPoint.osConjRLM (d := d) : SchwartzNPoint d n →L[ℝ] SchwartzNPoint d n).continuous

@[simp]
theorem SchwartzNPoint.osConjTensorProduct_zero_left {m k : ℕ}
    (g : SchwartzNPoint d k) :
    (0 : SchwartzNPoint d m).osConjTensorProduct g = 0 := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_zero,
    SchwartzMap.tensorProduct_zero_left]

@[simp]
theorem SchwartzNPoint.osConjTensorProduct_zero_right {m k : ℕ}
    (f : SchwartzNPoint d m) :
    f.osConjTensorProduct (0 : SchwartzNPoint d k) = 0 := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_zero_right]

theorem SchwartzNPoint.osConjTensorProduct_add_right {m k : ℕ}
    (f : SchwartzNPoint d m) (g₁ g₂ : SchwartzNPoint d k) :
    f.osConjTensorProduct (g₁ + g₂) =
      f.osConjTensorProduct g₁ + f.osConjTensorProduct g₂ := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_add_right]

theorem SchwartzNPoint.osConjTensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : SchwartzNPoint d m) (g : SchwartzNPoint d k) :
    (f₁ + f₂).osConjTensorProduct g =
      f₁.osConjTensorProduct g + f₂.osConjTensorProduct g := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_add,
    SchwartzMap.tensorProduct_add_left]

theorem SchwartzNPoint.osConjTensorProduct_smul_right {m k : ℕ}
    (f : SchwartzNPoint d m) (c : ℂ) (g : SchwartzNPoint d k) :
    f.osConjTensorProduct (c • g) = c • (f.osConjTensorProduct g) := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_smul_right]

theorem SchwartzNPoint.osConjTensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : SchwartzNPoint d m) (g : SchwartzNPoint d k) :
    (c • f).osConjTensorProduct g = starRingEnd ℂ c • (f.osConjTensorProduct g) := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_smul,
    SchwartzMap.tensorProduct_smul_left]

/-- The OS conjugated tensor product is jointly continuous in both tensor
blocks. The left slot continuity is only topological, not complex linear. -/
theorem SchwartzNPoint.osConjTensorProduct_continuous {n m : ℕ} :
    Continuous (fun fg : SchwartzNPoint d n × SchwartzNPoint d m =>
      fg.1.osConjTensorProduct fg.2) := by
  have hos : Continuous (fun fg : SchwartzNPoint d n × SchwartzNPoint d m =>
      (fg.1.osConj, fg.2)) :=
    (SchwartzNPoint.osConj_continuous (d := d)).prodMap continuous_id
  simpa [SchwartzNPoint.osConjTensorProduct] using
    (SchwartzMap.tensorProduct_continuous (E := SpacetimeDim d)).comp hos

/-- Ordered positive-time topological support is enough to guarantee that every
    OS tensor term of two Borchers sequences already lies in `°S`. -/
theorem OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
    (F G : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    OSTensorAdmissible d F G := by
  intro n m
  exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d) (f := F.funcs n) (g := G.funcs m) (hF n) (hG m)

/-- The honest Euclidean Borchers algebra for OS reflection positivity:
    finitely supported sequences whose every component is topologically supported
    in the ordered positive-time region. On this subtype the OS tensor terms are
    automatically admissible. -/
structure PositiveTimeBorchersSequence (d : ℕ) where
  toBorchersSequence : BorchersSequence d
  ordered_tsupport : ∀ n,
    tsupport ((toBorchersSequence.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n

namespace PositiveTimeBorchersSequence

variable {d : ℕ}

/-- The positive-time Borchers sequence concentrated in degree `n` with component `f`. -/
def single (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence := BorchersSequence.single n f
  ordered_tsupport m := by
    by_cases h : m = n
    · subst h
      simpa using hf
    · have hzero :
        (((BorchersSequence.single n f).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ) = 0 := by
        simp [BorchersSequence.single, h]
      rw [hzero]
      simpa using (empty_subset (OrderedPositiveTimeRegion d m) :
        (∅ : Set (NPointDomain d m)) ⊆ OrderedPositiveTimeRegion d m)

instance : Coe (PositiveTimeBorchersSequence d) (BorchersSequence d) :=
  ⟨PositiveTimeBorchersSequence.toBorchersSequence⟩

instance : Zero (PositiveTimeBorchersSequence d) where
  zero :=
    ⟨0, fun n => by
      simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
        (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)⟩

instance : Add (PositiveTimeBorchersSequence d) where
  add F G :=
    ⟨(F : BorchersSequence d) + (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) +
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.add_funcs] using hx
      have hx'' := (tsupport_add
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.ordered_tsupport n hxF)
        (fun hxG => G.ordered_tsupport n hxG)⟩

instance : Neg (PositiveTimeBorchersSequence d) where
  neg F := ⟨-(F : BorchersSequence d), fun n => by
    rw [show (((-(F : BorchersSequence d)).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) = -(((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) by rfl]
    rw [tsupport_neg]
    exact F.ordered_tsupport n⟩

instance : SMul ℂ (PositiveTimeBorchersSequence d) where
  smul c F :=
    ⟨c • (F : BorchersSequence d), fun n =>
      (tsupport_smul_subset_right
        (fun _ : NPointDomain d n => c)
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))).trans (F.ordered_tsupport n)⟩

instance : Sub (PositiveTimeBorchersSequence d) where
  sub F G :=
    ⟨(F : BorchersSequence d) - (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) -
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.sub_funcs] using hx
      have hx'' := (tsupport_sub
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.ordered_tsupport n hxF)
        (fun hxG => G.ordered_tsupport n hxG)⟩

@[simp] theorem zero_toBorchersSequence :
    ((0 : PositiveTimeBorchersSequence d) : BorchersSequence d) = 0 := rfl

@[simp] theorem add_toBorchersSequence (F G : PositiveTimeBorchersSequence d) :
    ((F + G : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) + (G : BorchersSequence d) := rfl

@[simp] theorem neg_toBorchersSequence (F : PositiveTimeBorchersSequence d) :
    ((-F : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      - (F : BorchersSequence d) := rfl

@[simp] theorem smul_toBorchersSequence (c : ℂ) (F : PositiveTimeBorchersSequence d) :
    ((c • F : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      c • (F : BorchersSequence d) := rfl

@[simp] theorem sub_toBorchersSequence (F G : PositiveTimeBorchersSequence d) :
    ((F - G : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) - (G : BorchersSequence d) := rfl

@[simp] theorem single_toBorchersSequence (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    ((single n f hf : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      BorchersSequence.single n f := rfl

/-- On the honest positive-time Euclidean Borchers algebra, OS tensor terms are
    automatically zero-diagonal admissible. -/
theorem ostensorAdmissible [NeZero d] (F G : PositiveTimeBorchersSequence d) :
    OSTensorAdmissible d (F : BorchersSequence d) (G : BorchersSequence d) :=
  OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d) (F : BorchersSequence d) (G : BorchersSequence d)
    F.ordered_tsupport G.ordered_tsupport

end PositiveTimeBorchersSequence

/-- Pointwise block-swap identity for the OS-conjugated tensor product.

    This is the OS analogue of `conjTP_eq_borchersConj_conjTP`: applying the
    OS involution to `g.osConjTensorProduct f` swaps the two tensor blocks and
    yields `f.osConjTensorProduct g` after the canonical `n + m = m + n`
    reindexing. -/
private theorem osConjTP_eq_osConj_osConjTP {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d m) (g : SchwartzNPoint d n)
    (x : NPointDomain d (n + m)) :
    ((g.osConjTensorProduct f).osConj) x =
      (f.osConjTensorProduct g) (fun i => x (finAddFlip i)) := by
  have hfarg :
      splitLast n m (timeReflectionN d x) =
        timeReflectionN d (splitFirst m n (fun i => x (finAddFlip i))) := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitFirst, splitLast, timeReflectionN, timeReflection,
        finAddFlip_apply_castAdd]
    · simp [splitFirst, splitLast, timeReflectionN, timeReflection, hμ,
        finAddFlip_apply_castAdd]
  have hgarg :
      timeReflectionN d (splitFirst n m (timeReflectionN d x)) =
        splitLast m n (fun i => x (finAddFlip i)) := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitFirst, splitLast, timeReflectionN, timeReflection,
        finAddFlip_apply_natAdd]
    · simp [splitFirst, splitLast, timeReflectionN, timeReflection, hμ,
        finAddFlip_apply_natAdd]
  simp only [SchwartzNPoint.osConj_apply, SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, map_mul, starRingEnd_self_apply]
  rw [mul_comm]
  rw [hfarg, hgarg]

/-- Extending the second OS summation range does not change the value. -/
theorem OSInnerProductN_extend_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₂ : G.bound + 1 ≤ N₂) :
    OSInnerProductN d S F G N₁ N₂ = OSInnerProductN d S F G N₁ (G.bound + 1) := by
  unfold OSInnerProductN
  apply Finset.sum_congr rfl
  intro n _
  symm
  apply Finset.sum_subset (Finset.range_mono hN₂)
  intro m hm₂ hm₁
  have hm : G.bound < m := by
    simp only [Finset.mem_range] at hm₁ hm₂
    omega
  rw [G.bound_spec m hm, SchwartzNPoint.osConjTensorProduct_zero_right,
    ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]

/-- Extending the first OS summation range does not change the value. -/
theorem OSInnerProductN_extend_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) :
    OSInnerProductN d S F G N₁ N₂ = OSInnerProductN d S F G (F.bound + 1) N₂ := by
  unfold OSInnerProductN
  symm
  apply Finset.sum_subset (Finset.range_mono hN₁)
  intro n hn₂ hn₁
  have hn : F.bound < n := by
    simp only [Finset.mem_range] at hn₁ hn₂
    omega
  apply Finset.sum_eq_zero
  intro m _
  rw [F.bound_spec n hn, SchwartzNPoint.osConjTensorProduct_zero_left,
    ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]

/-- The OS inner product can be computed using any sufficiently large bounds. -/
theorem OSInnerProduct_eq_extended (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) (hN₂ : G.bound + 1 ≤ N₂) :
    OSInnerProduct d S F G = OSInnerProductN d S F G N₁ N₂ := by
  rw [OSInnerProduct_eq_N,
    ← OSInnerProductN_extend_right d S hlin F G (F.bound + 1) N₂ hN₂,
    ← OSInnerProductN_extend_left d S hlin F G N₁ N₂ hN₁]

/-- For concentrated Borchers sequences, the OS inner product reduces to the
single tensor term. -/
theorem OSInnerProduct_single_single (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    OSInnerProduct d S (BorchersSequence.single n f) (BorchersSequence.single m g) =
      S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  unfold OSInnerProduct
  rw [BorchersSequence.single_bound, BorchersSequence.single_bound, Finset.sum_range_succ]
  have hleft :
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range (m + 1),
          S (i + j) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs i).osConjTensorProduct
              ((BorchersSequence.single m g).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
    apply Finset.sum_eq_zero
    intro j hj
    rw [BorchersSequence.single_funcs_ne hi_ne, SchwartzNPoint.osConjTensorProduct_zero_left,
      ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]
  rw [hleft, zero_add, BorchersSequence.single_funcs_eq, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        S (n + j) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct ((BorchersSequence.single m g).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]

/-- For an arbitrary left Borchers vector, the OS inner product against a concentrated
right factor reduces to the single tensor term in each left component. -/
theorem OSInnerProduct_right_single (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F : BorchersSequence d)
    {m : ℕ} (g : SchwartzNPoint d m) :
    OSInnerProduct d S F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct g)) := by
  unfold OSInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  rw [BorchersSequence.single_bound, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        S (n + j) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct ((BorchersSequence.single m g).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]

/-- The OS inner product against an arbitrary right Borchers vector is the finite sum
of its concentrated right components. -/
theorem OSInnerProduct_eq_sum_right_singles (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) :
    OSInnerProduct d S F G =
      ∑ m ∈ Finset.range (G.bound + 1),
        OSInnerProduct d S F (BorchersSequence.single m (G.funcs m)) := by
  unfold OSInnerProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simpa [OSInnerProduct] using
    (OSInnerProduct_right_single (d := d) S hlin F (g := G.funcs m)).symm

/-- The OS inner product depends only on `funcs`, not on `bound`. -/
theorem OSInnerProduct_congr_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G₁ G₂ : BorchersSequence d)
    (h : ∀ n, G₁.funcs n = G₂.funcs n) :
    OSInnerProduct d S F G₁ = OSInnerProduct d S F G₂ := by
  rw [OSInnerProduct_eq_extended d S hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_left _ _)),
      OSInnerProduct_eq_extended d S hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_right _ _))]
  simp only [OSInnerProductN]
  congr 1
  ext n
  congr 1
  ext m
  rw [h m]

/-- The OS inner product depends only on `funcs`, not on `bound` (left argument). -/
theorem OSInnerProduct_congr_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F₁ F₂ G : BorchersSequence d)
    (h : ∀ n, F₁.funcs n = F₂.funcs n) :
    OSInnerProduct d S F₁ G = OSInnerProduct d S F₂ G := by
  rw [OSInnerProduct_eq_extended d S hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_left _ _)) le_rfl,
      OSInnerProduct_eq_extended d S hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_right _ _)) le_rfl]
  simp only [OSInnerProductN]
  congr 1
  ext n
  congr 1
  ext m
  rw [h n]

/-- The OS inner product with zero in the right argument vanishes. -/
theorem OSInnerProduct_zero_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F : BorchersSequence d) :
    OSInnerProduct d S F 0 = 0 := by
  unfold OSInnerProduct
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct ((0 : BorchersSequence d).funcs m)) = 0 := by
    rw [BorchersSequence.zero_funcs, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := (0 : SchwartzNPoint d (n + m)))
        (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))]
    rfl
  rw [hzero]
  exact (hlin _).map_zero

/-- The OS inner product is additive in the second argument. -/
theorem OSInnerProduct_add_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G₁ G₂ : BorchersSequence d)
    (hFG₁ : OSTensorAdmissible d F G₁)
    (hFG₂ : OSTensorAdmissible d F G₂) :
    OSInnerProduct d S F (G₁ + G₂) =
      OSInnerProduct d S F G₁ + OSInnerProduct d S F G₂ := by
  have hN₁ : F.bound + 1 ≤ F.bound + 1 := le_rfl
  have hN₂_sum : (G₁ + G₂).bound + 1 ≤ max G₁.bound G₂.bound + 1 := le_rfl
  have hN₂_1 : G₁.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₂_2 : G₂.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  rw [OSInnerProduct_eq_extended d S hlin F (G₁ + G₂)
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_sum,
      OSInnerProduct_eq_extended d S hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_1,
      OSInnerProduct_eq_extended d S hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_2]
  unfold OSInnerProductN
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hsum :=
    ZeroDiagonalSchwartz.ofClassical_add_of_vanishes
      ((F.funcs n).osConjTensorProduct (G₁.funcs m))
      ((F.funcs n).osConjTensorProduct (G₂.funcs m))
      (hFG₁ n m) (hFG₂ n m)
  rw [BorchersSequence.add_funcs,
    SchwartzNPoint.osConjTensorProduct_add_right, hsum, (hlin _).map_add]

/-- The OS inner product is additive in the first argument. -/
theorem OSInnerProduct_add_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F₁ F₂ G : BorchersSequence d)
    (hF₁G : OSTensorAdmissible d F₁ G)
    (hF₂G : OSTensorAdmissible d F₂ G) :
    OSInnerProduct d S (F₁ + F₂) G =
      OSInnerProduct d S F₁ G + OSInnerProduct d S F₂ G := by
  have hN₁_sum : (F₁ + F₂).bound + 1 ≤ max F₁.bound F₂.bound + 1 := le_rfl
  have hN₁_1 : F₁.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₁_2 : F₂.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  have hN₂ : G.bound + 1 ≤ G.bound + 1 := le_rfl
  rw [OSInnerProduct_eq_extended d S hlin (F₁ + F₂) G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_sum hN₂,
      OSInnerProduct_eq_extended d S hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_1 hN₂,
      OSInnerProduct_eq_extended d S hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_2 hN₂]
  unfold OSInnerProductN
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hsum :=
    ZeroDiagonalSchwartz.ofClassical_add_of_vanishes
      ((F₁.funcs n).osConjTensorProduct (G.funcs m))
      ((F₂.funcs n).osConjTensorProduct (G.funcs m))
      (hF₁G n m) (hF₂G n m)
  rw [BorchersSequence.add_funcs,
    SchwartzNPoint.osConjTensorProduct_add_left, hsum, (hlin _).map_add]

/-- The OS inner product is linear in the second argument. -/
theorem OSInnerProduct_smul_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (c : ℂ) (F G : BorchersSequence d) :
    OSInnerProduct d S F (c • G) = c * OSInnerProduct d S F G := by
  simp only [OSInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound]
  simp_rw [SchwartzNPoint.osConjTensorProduct_smul_right,
    ZeroDiagonalSchwartz.ofClassical_smul, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext n
  rw [Finset.mul_sum]

/-- The OS inner product is conjugate linear in the first argument. -/
theorem OSInnerProduct_smul_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (c : ℂ) (F G : BorchersSequence d) :
    OSInnerProduct d S (c • F) G = starRingEnd ℂ c * OSInnerProduct d S F G := by
  simp only [OSInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound]
  simp_rw [SchwartzNPoint.osConjTensorProduct_smul_left,
    ZeroDiagonalSchwartz.ofClassical_smul, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext n
  rw [Finset.mul_sum]

/-- The Schwinger functional packaged as a continuous linear map on the honest
zero-diagonal test space. -/
def OsterwalderSchraderAxioms.schwingerCLM
    (OS : OsterwalderSchraderAxioms d) (n : ℕ) :
    ZeroDiagonalSchwartz d n →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := OS.S n
      map_add' := (OS.E0_linear n).map_add
      map_smul' := (OS.E0_linear n).map_smul }
  cont := OS.E0_tempered n

/-- Real linear change of variables `(u, ξ) ↦ (x₀, x₁) = (u, u + ξ)` for the
two-point Euclidean spacetime domain. This is the first concrete coordinate
change behind the one-difference-variable reduction of the two-point Schwinger
function. -/
def twoPointCenterDiffLinearEquiv (d : ℕ) :
    NPointDomain d 2 ≃ₗ[ℝ] NPointDomain d 2 where
  toFun z i :=
    if hi : i = 0 then z 0 else z 0 + z 1
  map_add' z w := by
    ext i μ
    fin_cases i
    · simp
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp [h10]
      ring
  map_smul' c z := by
    ext i μ
    fin_cases i
    · simp
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp [h10]
      ring
  invFun x i :=
    if hi : i = 0 then x 0 else x 1 - x 0
  left_inv z := by
    ext i μ
    fin_cases i <;> simp
  right_inv x := by
    ext i μ
    fin_cases i <;> simp [sub_eq_add_neg]

/-- Continuous version of `twoPointCenterDiffLinearEquiv`. -/
def twoPointCenterDiffCLE (d : ℕ) :
    NPointDomain d 2 ≃L[ℝ] NPointDomain d 2 :=
  (twoPointCenterDiffLinearEquiv d).toContinuousLinearEquiv

/-- Regard a one-point Schwartz function as a Schwartz function on `Fin 1 → E`. -/
def onePointToFin1CLM (d : ℕ) :
    SchwartzSpacetime d →L[ℂ] SchwartzMap (Fin 1 → SpacetimeDim d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d))

@[simp] theorem onePointToFin1CLM_apply {d : ℕ}
    (f : SchwartzSpacetime d) (x : Fin 1 → SpacetimeDim d) :
    onePointToFin1CLM d f x = f (x 0) := by
  simp [onePointToFin1CLM]

/-- For a center-variable Schwartz cutoff `χ(u)` and a difference-variable
Schwartz test `h(ξ)`, this is the associated two-point Schwartz function
`(x₀, x₁) ↦ χ(x₀) h(x₁ - x₀)`. -/
def twoPointDifferenceLift {d : ℕ}
    (χ h : SchwartzSpacetime d) : SchwartzNPoint d 2 :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm)
    (χ.prependField (onePointToFin1CLM d h))

/-- If all n-fold product tensors lie in the zero-diagonal subspace, they form a
continuous multilinear map into `ZeroDiagonalSchwartz`. -/
def ZeroDiagonalSchwartz.productTensorMLM {d n : ℕ}
    (hvanish : ∀ fs : Fin n → SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d)
      (ZeroDiagonalSchwartz d n) where
  toMultilinearMap :=
    { toFun := fun fs => ⟨SchwartzMap.productTensor fs, hvanish fs⟩
      map_update_add' := by
        intro hdec m i x y
        letI := hdec
        apply Subtype.ext
        change SchwartzMap.productTensor (Function.update m i (x + y)) =
          SchwartzMap.productTensor (Function.update m i x) +
            SchwartzMap.productTensor (Function.update m i y)
        ext z
        have h :=
          congrArg (fun F : SchwartzNPoint d n => F z)
            (SchwartzMap.productTensor_update_add
              (E := SpacetimeDim d) (n := n) i m x y)
        simpa [SchwartzMap.productTensor_apply, Function.update] using h
      map_update_smul' := by
        intro hdec m i c x
        letI := hdec
        apply Subtype.ext
        change SchwartzMap.productTensor (Function.update m i (c • x)) =
          c • SchwartzMap.productTensor (Function.update m i x)
        ext z
        have h :=
          congrArg (fun F : SchwartzNPoint d n => F z)
            (SchwartzMap.productTensor_update_smul
              (E := SpacetimeDim d) (n := n) i m c x)
        simpa [SchwartzMap.productTensor_apply, Function.update, smul_eq_mul] using h }
  cont := (SchwartzMap.productTensor_continuous (E := SpacetimeDim d)).subtype_mk _

@[simp]
theorem ZeroDiagonalSchwartz.productTensorMLM_apply {d n : ℕ}
    (hvanish : ∀ fs : Fin n → SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs))
    (fs : Fin n → SchwartzSpacetime d) :
    ZeroDiagonalSchwartz.productTensorMLM (d := d) hvanish fs =
      ⟨SchwartzMap.productTensor fs, hvanish fs⟩ := rfl

/-- On admissible factorized tests, the Schwinger functional is a continuous
multilinear form in the individual Schwartz factors. -/
def OsterwalderSchraderAxioms.productTensorSchwingerMLM
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (hvanish : ∀ fs : Fin n → SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).compContinuousMultilinearMap
    (ZeroDiagonalSchwartz.productTensorMLM (d := d) hvanish)

@[simp]
theorem OsterwalderSchraderAxioms.productTensorSchwingerMLM_apply
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (hvanish : ∀ fs : Fin n → SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs))
    (fs : Fin n → SchwartzSpacetime d) :
    OsterwalderSchraderAxioms.productTensorSchwingerMLM (d := d) OS hvanish fs =
      OS.S n ⟨SchwartzMap.productTensor fs, hvanish fs⟩ := rfl

/-- The abstract OS inner product is Hermitian.

    This is the Euclidean analogue of `WightmanInnerProduct_hermitian`. The
    proof uses only the corrected OS reality condition together with
    permutation symmetry to swap the tensor blocks after applying the OS
    involution. -/
private theorem cast_zeroDiagonalSchwartz_apply {d k₁ k₂ : ℕ}
    (hk : k₁ = k₂) (f : ZeroDiagonalSchwartz d k₁) (x : NPointDomain d k₂) :
    (cast (congrArg (ZeroDiagonalSchwartz d) hk) f).1 x =
      f.1 (fun i => x (Fin.cast hk i)) := by
  cases hk
  rfl

private theorem S_eq_of_cast {d : ℕ}
    (S : (k : ℕ) → ZeroDiagonalSchwartz d k → ℂ)
    (k₁ k₂ : ℕ) (hk : k₁ = k₂)
    (f : ZeroDiagonalSchwartz d k₁) (g : ZeroDiagonalSchwartz d k₂)
    (hfg : ∀ x, f.1 x = g.1 (fun i => x (Fin.cast hk.symm i))) :
    S k₁ f = S k₂ g := by
  subst hk
  have hfg' : f = g := by
    apply Subtype.ext
    ext x
    simpa using hfg x
  simpa [hfg']

private def blockSwapPerm (m n : ℕ) : Equiv.Perm (Fin (n + m)) where
  toFun := fun i =>
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Fin.cast (Nat.add_comm m n).symm i)
  invFun := fun i =>
    Fin.cast (Nat.add_comm m n)
      ((finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm i)
  left_inv := by
    intro i
    simp
  right_inv := by
    intro i
    simp

@[simp] private theorem blockSwapPerm_cast_eq_finAddFlip {m n : ℕ}
    (i : Fin (m + n)) :
    blockSwapPerm m n (Fin.cast (Nat.add_comm m n) i) =
      (finAddFlip : Fin (m + n) ≃ Fin (n + m)) i := by
  simp [blockSwapPerm]

theorem OSInnerProduct_hermitian {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d)
    (hFG : OSTensorAdmissible d F G)
    (hGF : OSTensorAdmissible d G F) :
    OSInnerProduct d OS.S F G = starRingEnd ℂ (OSInnerProduct d OS.S G F) := by
  simp only [OSInnerProduct, map_sum]
  rw [Finset.sum_comm]
  congr 1
  ext n
  congr 1
  ext m
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := (F.funcs m).osConjTensorProduct (G.funcs n)) (hFG m n),
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := (G.funcs n).osConjTensorProduct (F.funcs m)) (hGF n m)]
  let A : ZeroDiagonalSchwartz d (n + m) :=
    ⟨(G.funcs n).osConjTensorProduct (F.funcs m), hGF n m⟩
  let C' : ZeroDiagonalSchwartz d (m + n) :=
    ⟨(F.funcs m).osConjTensorProduct (G.funcs n), hFG m n⟩
  let C : ZeroDiagonalSchwartz d (n + m) :=
    cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C'
  let B : ZeroDiagonalSchwartz d (n + m) :=
    ⟨reindexSchwartz (d := d) (σ := (finAddFlip : Fin (m + n) ≃ Fin (n + m))) C'.1,
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        (d := d) (f := C'.1) C'.2
        (finAddFlip : Fin (m + n) ≃ Fin (n + m))⟩
  have hreal : starRingEnd ℂ (OS.S (n + m) A) = OS.S (n + m) B := by
    refine OS.E0_reality (n := n + m) (f := A) (g := B) ?_
    intro x
    simpa [A, B, C', reindexSchwartz_apply, SchwartzNPoint.osConj_apply] using
      (osConjTP_eq_osConj_osConjTP (d := d) (n := n) (m := m)
        (f := F.funcs m) (g := G.funcs n) x).symm
  have hcast : OS.S (m + n) C' = OS.S (n + m) C := by
    refine S_eq_of_cast OS.S (m + n) (n + m) (Nat.add_comm m n) C' C ?_
    intro x
    rw [show C = cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C' by rfl]
    rw [cast_zeroDiagonalSchwartz_apply (hk := Nat.add_comm m n) (f := C')
      (x := fun i => x (Fin.cast (Nat.add_comm m n).symm i))]
    simp
  have hperm : OS.S (n + m) C = OS.S (n + m) B := by
    refine OS.E3_symmetric (n := n + m) (σ := blockSwapPerm m n) (f := C) (g := B) ?_
    intro x
    rw [show C = cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C' by rfl]
    rw [cast_zeroDiagonalSchwartz_apply (hk := Nat.add_comm m n) (f := C')
      (x := fun i => x (blockSwapPerm m n i))]
    simp [B, C', reindexSchwartz_apply]
  calc
    OS.S (m + n) C' = OS.S (n + m) C := hcast
    _ = OS.S (n + m) B := hperm
    _ = starRingEnd ℂ (OS.S (n + m) A) := hreal.symm

namespace OSReconstruction

@[simp] theorem osArityLinearSchwartzSeminorm_zero
    (d s : Nat) (f : SchwartzNPoint d 0) :
    osArityLinearSchwartzSeminorm d 0 s f = ‖f 0‖ := by
  have hindices : Finset.Iic ((0, 0) : Nat × Nat) = {(0, 0)} := by
    ext ⟨p, q⟩
    simp
  simp only [osArityLinearSchwartzSeminorm, zero_mul,
    hindices, Finset.sup_singleton]
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound Real 0 0 f (norm_nonneg _)
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  · exact SchwartzMap.norm_le_seminorm Real f 0

theorem osArityLinearSchwartzSeminorm_mono
    (d n : Nat) {s t : Nat} (hst : s ≤ t)
    (f : SchwartzNPoint d n) :
    osArityLinearSchwartzSeminorm d n s f ≤
      osArityLinearSchwartzSeminorm d n t f := by
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro i hi
  apply Seminorm.le_finset_sup_apply
  exact Finset.mem_Iic.mpr
    ((Finset.mem_Iic.mp hi).trans
      ⟨Nat.mul_le_mul_left n hst, Nat.mul_le_mul_left n hst⟩)

/-- Increasing the defining order preserves the same growth constants. -/
def OSArityLinearGrowthCondition.withSobolevIndex
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSArityLinearGrowthCondition d OS)
    (s : Nat) (hs : lgc.sobolev_index ≤ s) :
    OSArityLinearGrowthCondition d OS where
  normalized_zero := lgc.normalized_zero
  sobolev_index := s
  alpha := lgc.alpha
  beta := lgc.beta
  gamma := lgc.gamma
  alpha_pos := lgc.alpha_pos
  beta_pos := lgc.beta_pos
  growth_estimate := by
    intro n f
    apply (lgc.growth_estimate n f).trans
    apply mul_le_mul_of_nonneg_left
      (osArityLinearSchwartzSeminorm_mono d n hs f.1)
    exact mul_nonneg
      (mul_nonneg lgc.alpha_pos.le (pow_nonneg lgc.beta_pos.le _))
      (Real.rpow_nonneg (by positivity) _)

@[simp] theorem OSArityLinearGrowthCondition.withSobolevIndex_sobolev_index
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (lgc : OSArityLinearGrowthCondition d OS)
    (s : Nat) (hs : lgc.sobolev_index ≤ s) :
    (lgc.withSobolevIndex s hs).sobolev_index = s := rfl

end OSReconstruction

namespace PositiveTimeBorchersSequence

variable {d : ℕ} [NeZero d]

/-- The OS sesquilinear form on the honest positive-time Euclidean Borchers algebra. -/
def osInner (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) : ℂ :=
  OSInnerProduct d OS.S (F : BorchersSequence d) (G : BorchersSequence d)

@[simp] theorem osInner_zero_right (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    osInner OS F 0 = 0 := by
  unfold osInner
  simpa using OSInnerProduct_zero_right (d := d) OS.S OS.E0_linear (F : BorchersSequence d)

theorem osInner_add_right (OS : OsterwalderSchraderAxioms d)
    (F G₁ G₂ : PositiveTimeBorchersSequence d) :
    osInner OS F (G₁ + G₂) = osInner OS F G₁ + osInner OS F G₂ := by
  unfold osInner
  simpa using OSInnerProduct_add_right (d := d) OS.S OS.E0_linear
    (F : BorchersSequence d) (G₁ : BorchersSequence d) (G₂ : BorchersSequence d)
    (ostensorAdmissible F G₁) (ostensorAdmissible F G₂)

theorem osInner_add_left (OS : OsterwalderSchraderAxioms d)
    (F₁ F₂ G : PositiveTimeBorchersSequence d) :
    osInner OS (F₁ + F₂) G = osInner OS F₁ G + osInner OS F₂ G := by
  unfold osInner
  simpa using OSInnerProduct_add_left (d := d) OS.S OS.E0_linear
    (F₁ : BorchersSequence d) (F₂ : BorchersSequence d) (G : BorchersSequence d)
    (ostensorAdmissible F₁ G) (ostensorAdmissible F₂ G)

theorem osInner_smul_right (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F G : PositiveTimeBorchersSequence d) :
    osInner OS F (c • G) = c * osInner OS F G := by
  unfold osInner
  simpa using OSInnerProduct_smul_right (d := d) OS.S OS.E0_linear
    c (F : BorchersSequence d) (G : BorchersSequence d)

theorem osInner_smul_left (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F G : PositiveTimeBorchersSequence d) :
    osInner OS (c • F) G = starRingEnd ℂ c * osInner OS F G := by
  unfold osInner
  simpa using OSInnerProduct_smul_left (d := d) OS.S OS.E0_linear
    c (F : BorchersSequence d) (G : BorchersSequence d)

theorem osInner_neg_right (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS F (-G) = -osInner OS F G := by
  have hcongr :
      osInner OS F (-G) = osInner OS F ((-1 : ℂ) • G) := by
    unfold osInner
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear
      (F : BorchersSequence d)
      ((-G : PositiveTimeBorchersSequence d) : BorchersSequence d)
      ((((-1 : ℂ) • G : PositiveTimeBorchersSequence d)) : BorchersSequence d) ?_
    intro n
    simpa [BorchersSequence.neg_funcs, BorchersSequence.smul_funcs] using
      (neg_one_smul ((G : BorchersSequence d).funcs n : SchwartzNPoint d n))
  rw [hcongr, osInner_smul_right]
  ring

theorem osInner_neg_left (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS (-F) G = -osInner OS F G := by
  have hcongr :
      osInner OS (-F) G = osInner OS ((-1 : ℂ) • F) G := by
    unfold osInner
    refine OSInnerProduct_congr_left d OS.S OS.E0_linear
      ((-F : PositiveTimeBorchersSequence d) : BorchersSequence d)
      ((((-1 : ℂ) • F : PositiveTimeBorchersSequence d)) : BorchersSequence d)
      (G : BorchersSequence d) ?_
    intro n
    simpa [BorchersSequence.neg_funcs, BorchersSequence.smul_funcs] using
      (neg_one_smul ((F : BorchersSequence d).funcs n : SchwartzNPoint d n))
  rw [hcongr, osInner_smul_left]
  simp

theorem osInner_sub_right (OS : OsterwalderSchraderAxioms d)
    (F G₁ G₂ : PositiveTimeBorchersSequence d) :
    osInner OS F (G₁ - G₂) = osInner OS F G₁ - osInner OS F G₂ := by
  calc
    osInner OS F (G₁ - G₂) = osInner OS F (G₁ + -G₂) := by rfl
    _ = osInner OS F G₁ + osInner OS F (-G₂) := osInner_add_right OS F G₁ (-G₂)
    _ = osInner OS F G₁ + (-osInner OS F G₂) := by rw [osInner_neg_right]
    _ = osInner OS F G₁ - osInner OS F G₂ := by ring

theorem osInner_sub_left (OS : OsterwalderSchraderAxioms d)
    (F₁ F₂ G : PositiveTimeBorchersSequence d) :
    osInner OS (F₁ - F₂) G = osInner OS F₁ G - osInner OS F₂ G := by
  calc
    osInner OS (F₁ - F₂) G = osInner OS (F₁ + -F₂) G := by rfl
    _ = osInner OS F₁ G + osInner OS (-F₂) G := osInner_add_left OS F₁ (-F₂) G
    _ = osInner OS F₁ G + (-osInner OS F₂ G) := by rw [osInner_neg_left]
    _ = osInner OS F₁ G - osInner OS F₂ G := by ring

theorem osInner_hermitian (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS F G = starRingEnd ℂ (osInner OS G F) := by
  unfold osInner
  simpa using OSInnerProduct_hermitian (d := d) OS
    (F : BorchersSequence d) (G : BorchersSequence d)
    (ostensorAdmissible F G) (ostensorAdmissible G F)

theorem osInner_nonneg_self (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ (osInner OS F F).re :=
  OS.E2_reflection_positive (F : BorchersSequence d) F.ordered_tsupport

private theorem osInner_quadratic_re (OS : OsterwalderSchraderAxioms d)
    (X Y : PositiveTimeBorchersSequence d) (t : ℝ) :
    (osInner OS (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re =
    (osInner OS X X).re +
      2 * (osInner OS X Y).re * t +
      (osInner OS Y Y).re * t ^ 2 := by
  rw [osInner_add_left, osInner_add_right, osInner_add_right,
    osInner_smul_right, osInner_smul_left, osInner_smul_left, osInner_smul_right,
    osInner_hermitian]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
  have hherm_re : (osInner OS Y X).re = (osInner OS X Y).re := by
    have h := congrArg Complex.re (osInner_hermitian OS X Y)
    simpa using h.symm
  rw [hherm_re]
  ring

/-- Null vectors for the honest positive-time OS form are orthogonal to every
    positive-time Borchers vector. This is the Euclidean analogue of
    `null_inner_product_zero` on the Wightman side and is the key algebraic input
    for an honest OS GNS quotient. -/
theorem null_osInner_zero (OS : OsterwalderSchraderAxioms d)
    (X Y : PositiveTimeBorchersSequence d)
    (hX : (osInner OS X X).re = 0) :
    osInner OS X Y = 0 := by
  set w := osInner OS X Y with hw
  have hre : w.re = 0 := by
    apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
    rw [mul_zero]
    apply quadratic_nonneg_linear_zero (osInner OS Y Y).re
    · exact osInner_nonneg_self OS Y
    · intro t
      rw [show (osInner OS Y Y).re * t ^ 2 + 2 * w.re * t =
          (osInner OS (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re from by
            rw [osInner_quadratic_re, hX]
            ring]
      exact osInner_nonneg_self OS (X + (↑t : ℂ) • Y)
  have him : w.im = 0 := by
    have hIw : osInner OS X (Complex.I • Y) = Complex.I * w := by
      rw [osInner_smul_right]
    have hIw_re : (Complex.I * w).re = -w.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have hre_Z : (osInner OS X (Complex.I • Y)).re = 0 := by
      apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
      rw [mul_zero]
      apply quadratic_nonneg_linear_zero (osInner OS (Complex.I • Y) (Complex.I • Y)).re
      · exact osInner_nonneg_self OS (Complex.I • Y)
      · intro t
        rw [show (osInner OS (Complex.I • Y) (Complex.I • Y)).re * t ^ 2 +
            2 * (osInner OS X (Complex.I • Y)).re * t =
            (osInner OS (X + (↑t : ℂ) • (Complex.I • Y))
              (X + (↑t : ℂ) • (Complex.I • Y))).re from by
              rw [osInner_quadratic_re, hX]
              ring]
        exact osInner_nonneg_self OS (X + (↑t : ℂ) • (Complex.I • Y))
    rw [hIw, hIw_re] at hre_Z
    linarith
  exact Complex.ext hre him

/-- The honest positive-time OS form against an arbitrary right factor is the finite
sum of its concentrated right components. -/
theorem osInner_eq_sum_right_singles (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS F G =
      ∑ m ∈ Finset.range (((G : BorchersSequence d).bound + 1)),
        osInner OS F
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m)) := by
  unfold osInner
  rw [OSInnerProduct_eq_sum_right_singles (d := d) OS.S OS.E0_linear
    (F := (F : BorchersSequence d)) (G := (G : BorchersSequence d))]
  apply Finset.sum_congr rfl
  intro m hm
  simp [PositiveTimeBorchersSequence.single_toBorchersSequence]

theorem osInner_expand_diff (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS (F - G) (F - G) =
      osInner OS F F + osInner OS G G - osInner OS F G - osInner OS G F := by
  rw [osInner_sub_left, osInner_sub_right, osInner_sub_right]
  ring

end PositiveTimeBorchersSequence

/-- The honest OS null-space relation on the positive-time Euclidean Borchers algebra.
    Two vectors are equivalent iff their difference has zero OS norm. -/
def osBorchersSetoid {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) :
    Setoid (PositiveTimeBorchersSequence d) where
  r F G := (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re = 0
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro F
      rw [PositiveTimeBorchersSequence.osInner_expand_diff]
      ring_nf
      simp
    · intro F G hFG
      have hfuncs_neg :
          ∀ n,
            (((G - F : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
              (((-(F - G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
        intro n
        simp [sub_eq_add_neg]
      have hneg :
          PositiveTimeBorchersSequence.osInner OS (G - F) (G - F) =
            PositiveTimeBorchersSequence.osInner OS (-(F - G)) (-(F - G)) := by
        unfold PositiveTimeBorchersSequence.osInner
        exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs_neg).trans
          (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs_neg)
      have hsymm :
          (PositiveTimeBorchersSequence.osInner OS (G - F) (G - F)).re =
            (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re := by
        rw [hneg, PositiveTimeBorchersSequence.osInner_neg_left,
          PositiveTimeBorchersSequence.osInner_neg_right, neg_neg]
      exact hsymm.trans hFG
    · intro F G H hFG hGH
      let A : PositiveTimeBorchersSequence d := F - G
      let B : PositiveTimeBorchersSequence d := G - H
      have hA : PositiveTimeBorchersSequence.osInner OS A A = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS A A hFG
      have hB : PositiveTimeBorchersSequence.osInner OS B B = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS B B hGH
      have hAB : PositiveTimeBorchersSequence.osInner OS A B = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS A B hFG
      have hBA : PositiveTimeBorchersSequence.osInner OS B A = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS B A hGH
      have hsum :
          PositiveTimeBorchersSequence.osInner OS (A + B) (A + B) = 0 := by
        rw [PositiveTimeBorchersSequence.osInner_add_left,
          PositiveTimeBorchersSequence.osInner_add_right,
          PositiveTimeBorchersSequence.osInner_add_right, hA, hAB, hBA, hB]
        ring
      have hkey :
          ∀ n,
            (((F - H : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
              (((A + B : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
        intro n
        simp [A, B, sub_eq_add_neg]
      have hFH :
          PositiveTimeBorchersSequence.osInner OS (F - H) (F - H) =
            PositiveTimeBorchersSequence.osInner OS (A + B) (A + B) := by
        unfold PositiveTimeBorchersSequence.osInner
        exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hkey).trans
          (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hkey)
      rw [hFH]
      exact congrArg Complex.re hsum

/-- The honest Euclidean pre-Hilbert space: quotient of positive-time Borchers
    sequences by the OS null space. -/
def OSPreHilbertSpace {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) : Type :=
  Quotient (osBorchersSetoid OS)

/-- The OS inner product on the Euclidean GNS quotient. -/
def OSPreHilbertSpace.innerProduct {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) :
    OSPreHilbertSpace OS → OSPreHilbertSpace OS → ℂ :=
  Quotient.lift₂ (PositiveTimeBorchersSequence.osInner OS) (by
    intro a₁ a₂ b₁ b₂ ha hb
    have ha_eq :
        ∀ G : PositiveTimeBorchersSequence d,
          PositiveTimeBorchersSequence.osInner OS a₁ G =
            PositiveTimeBorchersSequence.osInner OS b₁ G := by
      intro G
      have h := PositiveTimeBorchersSequence.null_osInner_zero OS (a₁ - b₁) G ha
      rwa [PositiveTimeBorchersSequence.osInner_sub_left, sub_eq_zero] at h
    have hb_eq :
        ∀ F : PositiveTimeBorchersSequence d,
          PositiveTimeBorchersSequence.osInner OS F a₂ =
            PositiveTimeBorchersSequence.osInner OS F b₂ := by
      intro F
      have h := PositiveTimeBorchersSequence.null_osInner_zero OS (a₂ - b₂) F hb
      rw [PositiveTimeBorchersSequence.osInner_sub_left, sub_eq_zero] at h
      calc
        PositiveTimeBorchersSequence.osInner OS F a₂ =
            starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS a₂ F) := by
              rw [PositiveTimeBorchersSequence.osInner_hermitian]
        _ = starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS b₂ F) := by rw [h]
        _ = starRingEnd ℂ (starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS F b₂)) := by
              rw [PositiveTimeBorchersSequence.osInner_hermitian]
        _ = PositiveTimeBorchersSequence.osInner OS F b₂ := by simp
    rw [ha_eq a₂, hb_eq b₁])

namespace OSPreHilbertSpace

variable {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d)

/-- Two positive-time Borchers sequences with identical components represent the
    same class in the honest OS quotient. -/
theorem osBorchersSetoid_of_funcs_eq (F G : PositiveTimeBorchersSequence d)
    (h : ∀ n, ((F : BorchersSequence d).funcs n) = ((G : BorchersSequence d).funcs n)) :
    osBorchersSetoid OS F G := by
  show (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re = 0
  have hzero :
      ∀ n,
        (((F - G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((0 : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [h n]
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS (F - G) (F - G) =
        PositiveTimeBorchersSequence.osInner OS 0 0 := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hzero).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hzero)
  rw [hcongr]
  simp

/-- Addition respects the OS null relation. -/
theorem add_respects_equiv (F₁ G₁ F₂ G₂ : PositiveTimeBorchersSequence d)
    (h₁ : osBorchersSetoid OS F₁ G₁) (h₂ : osBorchersSetoid OS F₂ G₂) :
    osBorchersSetoid OS (F₁ + F₂) (G₁ + G₂) := by
  have h1_null : PositiveTimeBorchersSequence.osInner OS (F₁ - G₁) (F₁ - G₁) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₁ - G₁) (F₁ - G₁) h₁
  have h2_null : PositiveTimeBorchersSequence.osInner OS (F₂ - G₂) (F₂ - G₂) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₂ - G₂) (F₂ - G₂) h₂
  have h12_null : PositiveTimeBorchersSequence.osInner OS (F₁ - G₁) (F₂ - G₂) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₁ - G₁) (F₂ - G₂) h₁
  have h21_null : PositiveTimeBorchersSequence.osInner OS (F₂ - G₂) (F₁ - G₁) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₂ - G₂) (F₁ - G₁) h₂
  show (PositiveTimeBorchersSequence.osInner OS
    ((F₁ + F₂) - (G₁ + G₂)) ((F₁ + F₂) - (G₁ + G₂))).re = 0
  have hfuncs :
      ∀ n,
        ((((F₁ + F₂) - (G₁ + G₂) : PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n) =
          ((((F₁ - G₁) + (F₂ - G₂) : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n) := by
    intro n
    simp [sub_eq_add_neg]
    abel
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((F₁ + F₂) - (G₁ + G₂))
          ((F₁ + F₂) - (G₁ + G₂)) =
        PositiveTimeBorchersSequence.osInner OS ((F₁ - G₁) + (F₂ - G₂))
          ((F₁ - G₁) + (F₂ - G₂)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_add_left,
    PositiveTimeBorchersSequence.osInner_add_right,
    PositiveTimeBorchersSequence.osInner_add_right,
    h1_null, h12_null, h21_null, h2_null]
  simp

/-- Negation respects the OS null relation. -/
theorem neg_respects_equiv (F G : PositiveTimeBorchersSequence d)
    (h : osBorchersSetoid OS F G) :
    osBorchersSetoid OS (-F) (-G) := by
  show (PositiveTimeBorchersSequence.osInner OS ((-F) - (-G)) ((-F) - (-G))).re = 0
  have hfuncs :
      ∀ n,
        ((((-F) - (-G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((-(F - G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [sub_eq_add_neg]
    abel
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((-F) - (-G)) ((-F) - (-G)) =
        PositiveTimeBorchersSequence.osInner OS (-(F - G)) (-(F - G)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_neg_left,
    PositiveTimeBorchersSequence.osInner_neg_right, neg_neg]
  exact h

/-- Scalar multiplication respects the OS null relation. -/
theorem smul_respects_equiv (c : ℂ) (F G : PositiveTimeBorchersSequence d)
    (h : osBorchersSetoid OS F G) :
    osBorchersSetoid OS (c • F) (c • G) := by
  have hnull : PositiveTimeBorchersSequence.osInner OS (F - G) (F - G) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F - G) (F - G) h
  show (PositiveTimeBorchersSequence.osInner OS ((c • F) - (c • G)) ((c • F) - (c • G))).re = 0
  have hfuncs :
      ∀ n,
        ((((c • F) - (c • G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          ((((c • (F - G)) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simpa [BorchersSequence.sub_funcs, BorchersSequence.smul_funcs] using
      (smul_sub c ((F : BorchersSequence d).funcs n) ((G : BorchersSequence d).funcs n)).symm
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((c • F) - (c • G)) ((c • F) - (c • G)) =
        PositiveTimeBorchersSequence.osInner OS (c • (F - G)) (c • (F - G)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_smul_left,
    PositiveTimeBorchersSequence.osInner_smul_right, hnull]
  simp

instance instZero : Zero (OSPreHilbertSpace OS) where
  zero := Quotient.mk _ (0 : PositiveTimeBorchersSequence d)

instance instAdd : Add (OSPreHilbertSpace OS) where
  add := Quotient.map₂ (· + ·)
    (fun _ _ h₁ _ _ h₂ => add_respects_equiv OS _ _ _ _ h₁ h₂)

instance instNeg : Neg (OSPreHilbertSpace OS) where
  neg := Quotient.map (- ·) (fun _ _ h => neg_respects_equiv OS _ _ h)

instance instSMul : SMul ℂ (OSPreHilbertSpace OS) where
  smul c := Quotient.map (c • ·) (fun _ _ h => smul_respects_equiv OS c _ _ h)

instance instSub : Sub (OSPreHilbertSpace OS) where
  sub a b := a + (-b)

/-- If two positive-time sequences have identical components, their OS quotient
    classes are equal. -/
theorem mk_eq_of_funcs_eq (F G : PositiveTimeBorchersSequence d)
    (h : ∀ n, ((F : BorchersSequence d).funcs n) = ((G : BorchersSequence d).funcs n)) :
    (Quotient.mk (osBorchersSetoid OS) F : OSPreHilbertSpace OS) =
      Quotient.mk (osBorchersSetoid OS) G :=
  Quotient.sound (osBorchersSetoid_of_funcs_eq OS F G h)

instance instAddCommGroup : AddCommGroup (OSPreHilbertSpace OS) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        induction c using Quotient.inductionOn with
        | h H =>
          exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_assoc])
  zero_add a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  add_zero a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  add_comm a b := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_comm])
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℂ (OSPreHilbertSpace OS) where
  one_smul a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  mul_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [mul_smul])
  smul_zero c := by
    exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  smul_add c a b := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [smul_add])
  add_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_smul])
  zero_smul a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)

instance instInner : Inner ℂ (OSPreHilbertSpace OS) where
  inner := OSPreHilbertSpace.innerProduct OS

@[simp] theorem inner_eq (F G : PositiveTimeBorchersSequence d) :
    @inner ℂ (OSPreHilbertSpace OS) (instInner OS) ⟦F⟧ ⟦G⟧ =
      PositiveTimeBorchersSequence.osInner OS F G := rfl

theorem inner_conj_symm (x y : OSPreHilbertSpace OS) :
    starRingEnd ℂ (@inner ℂ _ (instInner OS) y x) =
      @inner ℂ _ (instInner OS) x y := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      simpa using (PositiveTimeBorchersSequence.osInner_hermitian OS F G).symm

theorem inner_re_nonneg (x : OSPreHilbertSpace OS) :
    0 ≤ RCLike.re (@inner ℂ _ (instInner OS) x x) := by
  induction x using Quotient.inductionOn with
  | h F =>
    exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

theorem inner_add_left (x y z : OSPreHilbertSpace OS) :
    @inner ℂ _ (instInner OS) (x + y) z =
      @inner ℂ _ (instInner OS) x z + @inner ℂ _ (instInner OS) y z := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      induction z using Quotient.inductionOn with
      | h H =>
        exact PositiveTimeBorchersSequence.osInner_add_left OS F G H

theorem inner_smul_left (x y : OSPreHilbertSpace OS) (r : ℂ) :
    @inner ℂ _ (instInner OS) (r • x) y =
      starRingEnd ℂ r * @inner ℂ _ (instInner OS) x y := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      exact PositiveTimeBorchersSequence.osInner_smul_left OS r F G

theorem inner_definite (x : OSPreHilbertSpace OS)
    (h : @inner ℂ _ (instInner OS) x x = 0) : x = 0 := by
  induction x using Quotient.inductionOn with
  | h F =>
    apply Quotient.sound
    show (PositiveTimeBorchersSequence.osInner OS (F - 0) (F - 0)).re = 0
    have hfuncs :
        ∀ n,
          (((F - (0 : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n) =
            ((F : BorchersSequence d).funcs n) := by
      intro n
      simp
    have hcongr :
        PositiveTimeBorchersSequence.osInner OS (F - 0) (F - 0) =
          PositiveTimeBorchersSequence.osInner OS F F := by
      unfold PositiveTimeBorchersSequence.osInner
      exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
        (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
    have h' : PositiveTimeBorchersSequence.osInner OS F F = 0 := h
    rw [hcongr, h']
    simp

/-- The `InnerProductSpace.Core` instance on the honest Euclidean OS quotient. -/
instance instCore : InnerProductSpace.Core ℂ (OSPreHilbertSpace OS) where
  toCore := {
    toInner := instInner OS
    conj_inner_symm := inner_conj_symm OS
    re_inner_nonneg := inner_re_nonneg OS
    add_left := inner_add_left OS
    smul_left := inner_smul_left OS
  }
  definite := inner_definite OS

/-- The normed additive group structure induced by the honest OS inner product. -/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (OSPreHilbertSpace OS) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (instCore OS)

/-- The pre-Hilbert space structure on the honest Euclidean OS quotient. -/
noncomputable instance instInnerProductSpace :
    @InnerProductSpace ℂ (OSPreHilbertSpace OS) _
      (instNormedAddCommGroup OS).toSeminormedAddCommGroup :=
  @InnerProductSpace.ofCore ℂ _ _ _ _ (instCore OS).toCore

end OSPreHilbertSpace

-- `wightman_to_os` and `os_to_wightman` moved to Reconstruction/Main.lean
-- (proved via WickRotation.lean: wightman_to_os_full, os_to_wightman_full)

end
