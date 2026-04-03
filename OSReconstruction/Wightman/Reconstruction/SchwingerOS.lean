import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Schwinger/OS Reconstruction Layer

This file contains the Euclidean/Schwinger-side infrastructure used by the
OS reconstruction route: the OS inner product, positive-time Borchers
sequences, the OS pre-Hilbert quotient, and the current two-point Schwinger
reduction shell.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped SchwartzMap
open scoped Convolution
open scoped Pointwise
open Topology

variable (d : ℕ) [NeZero d]

set_option linter.unusedSectionVars false

def OSInnerProduct (S : SchwingerFunctions d) (F G : BorchersSequence d) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

/-! ### OS Inner Product Algebra

The standard OS semigroup/spectral argument needs sesquilinearity of the
reflection-positive form. Since `S n` is part of E0 and therefore a tempered
distribution, the required linearity is part of the correct interface. The
lemmas below mirror the existing `WightmanInnerProduct` algebra.

Because `OSInnerProduct` is totalized via `ZeroDiagonalSchwartz.ofClassical`,
additivity theorems must explicitly assume that the relevant OS tensor terms
really lie in `°S`; otherwise the fallback zero branch can destroy algebraic
identities. -/

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

theorem OSTensorAdmissible.zero_right (F : BorchersSequence d) :
    OSTensorAdmissible d F 0 := by
  intro n m
  simpa [BorchersSequence.zero_funcs] using
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))

theorem OSTensorAdmissible.zero_left (G : BorchersSequence d) :
    OSTensorAdmissible d (0 : BorchersSequence d) G := by
  intro n m
  simpa [BorchersSequence.zero_funcs] using
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))

theorem OSTensorAdmissible.add_right {F G₁ G₂ : BorchersSequence d}
    (hFG₁ : OSTensorAdmissible d F G₁)
    (hFG₂ : OSTensorAdmissible d F G₂) :
    OSTensorAdmissible d F (G₁ + G₂) := by
  intro n m
  simpa [BorchersSequence.add_funcs, SchwartzNPoint.osConjTensorProduct_add_right] using
    (hFG₁ n m).add (hFG₂ n m)

theorem OSTensorAdmissible.add_left {F₁ F₂ G : BorchersSequence d}
    (hF₁G : OSTensorAdmissible d F₁ G)
    (hF₂G : OSTensorAdmissible d F₂ G) :
    OSTensorAdmissible d (F₁ + F₂) G := by
  intro n m
  simpa [BorchersSequence.add_funcs, SchwartzNPoint.osConjTensorProduct_add_left] using
    (hF₁G n m).add (hF₂G n m)

theorem OSTensorAdmissible.smul_right {F G : BorchersSequence d}
    (hFG : OSTensorAdmissible d F G) (c : ℂ) :
    OSTensorAdmissible d F (c • G) := by
  intro n m
  simpa [BorchersSequence.smul_funcs, SchwartzNPoint.osConjTensorProduct_smul_right] using
    (hFG n m).smul c

theorem OSTensorAdmissible.smul_left {F G : BorchersSequence d}
    (hFG : OSTensorAdmissible d F G) (c : ℂ) :
    OSTensorAdmissible d (c • F) G := by
  intro n m
  simpa [BorchersSequence.smul_funcs, SchwartzNPoint.osConjTensorProduct_smul_left] using
    (hFG n m).smul (starRingEnd ℂ c)

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

/-- Single/single OS evaluation with one inserted test on the right. This is the
basic concentrated `k = 3` shell for the direct operator-construction route. -/
theorem OSInnerProduct_single_fieldOperatorAction_single
    (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (h : SchwartzSpacetime d) :
    OSInnerProduct d S (BorchersSequence.single n f)
      (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g)) =
        S (n + (m + 1)) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (SchwartzMap.prependField h g))) := by
  have hcongr :
      OSInnerProduct d S (BorchersSequence.single n f)
        (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g)) =
      OSInnerProduct d S (BorchersSequence.single n f)
        (BorchersSequence.single (m + 1) (SchwartzMap.prependField h g)) := by
    refine OSInnerProduct_congr_right d S hlin
      (BorchersSequence.single n f)
      (Reconstruction.fieldOperatorAction h (BorchersSequence.single m g))
      (BorchersSequence.single (m + 1) (SchwartzMap.prependField h g)) ?_
    intro k
    exact Reconstruction.fieldOperatorAction_single_funcs
      (d := d) (f := h) (n := m) (k := k) (g := g)
  rw [hcongr]
  simpa [add_assoc] using
    OSInnerProduct_single_single (d := d) S hlin n (m + 1) f
      (SchwartzMap.prependField h g)

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

/-- The OS inner product with zero in the left argument vanishes. -/
theorem OSInnerProduct_zero_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (G : BorchersSequence d) :
    OSInnerProduct d S 0 G = 0 := by
  unfold OSInnerProduct
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
        (((0 : BorchersSequence d).funcs n).osConjTensorProduct (G.funcs m)) = 0 := by
    rw [BorchersSequence.zero_funcs, SchwartzNPoint.osConjTensorProduct_zero_left,
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

/-- The Osterwalder-Schrader axioms E0-E4 for Euclidean field theory.

    From OS I (1973):
    - E0: Temperedness (Sₙ ∈ S'(ℝ^{dn}))
    - E1: Euclidean invariance
    - E2: Reflection positivity: Σₙ,ₘ Sₙ₊ₘ(Θf* × fₘ) ≥ 0 for f ∈ S₊
    - E3: Symmetry: Sₙ(f) = Sₙ(f^π) for all permutations π
    - E4: Cluster property

    **Important**: As shown in OS II (1975), these axioms alone may NOT be
    sufficient to reconstruct a Wightman QFT. The linear growth condition E0'
    is needed. See `OSLinearGrowthCondition`.

    **Critical correction**: the heart of OS reconstruction is precisely the
    passage from Euclidean data defined only on the zero-diagonal test space
    `°S` to full tempered Wightman distributions on Schwartz space. The Euclidean
    starting point must therefore be stated on `ZeroDiagonalSchwartz` itself,
    not on a fictitious full-Schwartz Schwinger theory. -/
structure OsterwalderSchraderAxioms (d : ℕ) [NeZero d] where
  /-- The honest zero-diagonal Euclidean Schwinger family. -/
  S : SchwingerFunctions d
  /-- E0: Temperedness on the OS-I zero-diagonal test space `°S`.

      The literal OS-I Schwinger functions are distributions on the coincidence-free
      test space, not a priori on the full Schwartz space. Any later extension to
      all of `SchwartzNPoint` is extra structure beyond this axiom surface.

      The point is that inverse-power coincidence singularities are compatible
      with `°S`: zero-diagonal test functions vanish to arbitrarily high order on
      the coincidence locus, so kernels of finite singular order still define the
      honest Euclidean pairing there. This is why the corrected OS axiom is stated
      on `ZeroDiagonalSchwartz`, not on full Schwartz space. -/
  E0_tempered : ∀ n, Continuous (S n)
  /-- E0 also includes linearity on the honest Euclidean test space `°S`. -/
  E0_linear : ∀ n, IsLinearMap ℂ (S n)
  /-- E0 also includes the Schwinger reality condition induced by Wightman
      Hermiticity:
      `conj (S_n(f)) = S_n(f.osConj)`.

      The transformed test function is supplied as a zero-diagonal witness rather
      than by asserting a full-Schwartz Euclidean theory. -/
  E0_reality : ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
    starRingEnd ℂ (S n f) = S n g
  /-- E1a: Translation invariance.
      S_n(x₁+a,...,xₙ+a) = S_n(x₁,...,xₙ) for all a ∈ ℝ^{d+1}. -/
  E1_translation_invariant : ∀ (n : ℕ) (a : SpacetimeDim d)
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x i + a)) →
    S n f = S n g
  /-- E1b: Rotation invariance under SO(d+1).
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(d+1).
      Together with E1a, this gives Euclidean covariance under ℝ^{d+1} ⋊ SO(d+1).
      Note: Full O(d+1) invariance (including improper rotations with det=-1)
      would require parity invariance, which is not implied by the Wightman axioms. -/
  E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    R.transpose * R = 1 → R.det = 1 →
    ∀ (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
    S n f = S n g
  /-- E2: Reflection positivity - the crucial axiom for Hilbert space construction.
      For test functions whose topological support lies in the OS-I ordered positive-time region
      `0 < x₁⁰ < ... < xₙ⁰`,
      `Σₙ,ₘ S_{n+m}(θf̄ₙ ⊗ fₘ) ≥ 0`
      where θ is time reflection θ(τ,x⃗) = (-τ,x⃗) and f̄ is complex conjugation.
      This uses `OSInnerProduct` (time reflection + conjugation), the correct
      inner product for the Euclidean framework.
      This ensures the reconstructed inner product is positive definite. -/
  E2_reflection_positive : ∀ (F : BorchersSequence d),
    (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) →
    (OSInnerProduct d S F F).re ≥ 0
  /-- E3: Permutation symmetry - Schwinger functions are symmetric under
      permutation of arguments: S_n(x_{σ(1)},...,x_{σ(n)}) = S_n(x₁,...,xₙ)
      for all permutations σ ∈ Sₙ. -/
  E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
    S n f = S n g
  /-- E4: Cluster property - factorization at large separations.
      lim_{|a|→∞} S_{n+m}(x₁,...,xₙ,y₁+a,...,yₘ+a) = S_n(x₁,...,xₙ) · S_m(y₁,...,yₘ)
      This reflects the uniqueness of the vacuum in the reconstructed theory.

      Expressed via the connected n-point functions: the connected part Sₙᶜ vanishes
      for n ≥ 2 at large separations. Equivalently, for product test functions
      with widely separated supports, S_{n+m} factorizes. -/
  E4_cluster : ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m),
    -- Cluster property: as spatial separation increases, S_{n+m} factorizes.
    -- For any ε > 0, there exists R > 0 such that for spatial translation a with |a| > R,
    -- |S_{n+m}(f ⊗ τ_a g) - S_n(f) · S_m(g)| < ε
    -- where τ_a g is g translated by a in all m coordinates.
    -- The translation a must be purely spatial (a 0 = 0): Euclidean time shifts
    -- correspond to imaginary Minkowski time, leaving the cluster property's domain.
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        -- For any Schwartz function g_a that is the translation of g by a:
        ∀ (g_a : ZeroDiagonalSchwartz d m),
          (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
            (∀ x : NPointDomain d (n + m),
              fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
            ‖S (n + m) fg_a - S n f * S m g‖ < ε

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

/-- At one point, the zero-diagonal condition is vacuous, so Euclidean
translation invariance specializes directly to full Schwartz space. -/
theorem OsterwalderSchraderAxioms.schwinger_one_translation_invariant
    (OS : OsterwalderSchraderAxioms d) (a : SpacetimeDim d)
    (f g : SchwartzNPoint d 1)
    (hfg : ∀ x, g x = f (fun i => x i + a)) :
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical f) =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical g) := by
  have hf : VanishesToInfiniteOrderOnCoincidence (d := d) f :=
    VanishesToInfiniteOrderOnCoincidence.one (d := d) f
  have hg : VanishesToInfiniteOrderOnCoincidence (d := d) g :=
    VanishesToInfiniteOrderOnCoincidence.one (d := d) g
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f) hf,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := g) hg]
  exact OS.E1_translation_invariant 1 a ⟨f, hf⟩ ⟨g, hg⟩ hfg

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

@[simp] theorem twoPointCenterDiffCLE_symm_apply_zero {d : ℕ}
    (x : NPointDomain d 2) :
    (twoPointCenterDiffCLE d).symm x 0 = x 0 := by
  simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

@[simp] theorem twoPointCenterDiffCLE_symm_apply_one {d : ℕ}
    (x : NPointDomain d 2) :
    (twoPointCenterDiffCLE d).symm x 1 = x 1 - x 0 := by
  simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

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

@[simp] theorem twoPointDifferenceLift_apply {d : ℕ}
    (χ h : SchwartzSpacetime d) (x : NPointDomain d 2) :
    twoPointDifferenceLift χ h x = χ (x 0) * h (x 1 - x 0) := by
  simp [twoPointDifferenceLift, SchwartzMap.prependField_apply]

/-- For a center cutoff `χ(u)` and a right-factor test `g(x₁)`, this is the
product-shell two-point Schwartz function `(x₀, x₁) ↦ χ(x₀) g(x₁)`.

After the center/difference change of variables `(u, ξ) ↦ (u, u + ξ)`, this
becomes the sheared shell `(u, ξ) ↦ χ(u) g(u + ξ)`. This is the natural shell
that comes directly from the semigroup-side one-point pair construction. -/
def twoPointProductLift {d : ℕ}
    (χ g : SchwartzSpacetime d) : SchwartzNPoint d 2 :=
  (onePointToFin1CLM d χ).tensorProduct (onePointToFin1CLM d g)

@[simp] theorem twoPointProductLift_apply {d : ℕ}
    (χ g : SchwartzSpacetime d) (x : NPointDomain d 2) :
    twoPointProductLift χ g x = χ (x 0) * g (x 1) := by
  change ((onePointToFin1CLM d χ).tensorProduct (onePointToFin1CLM d g)) x =
    χ (x 0) * g (x 1)
  rw [SchwartzMap.tensorProduct_apply]
  simp [onePointToFin1CLM_apply, splitFirst, splitLast]

/-- The two-point center/difference shear `(u, ξ) ↦ (u, u + ξ)` preserves
Lebesgue measure. -/
theorem twoPointCenterDiff_measurePreserving {d : ℕ} :
    MeasureTheory.MeasurePreserving
      ((twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv)
      MeasureTheory.volume MeasureTheory.volume := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  have hshear :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.shearAddRight (SpacetimeDim d))
        MeasureTheory.volume MeasureTheory.volume := by
    simpa using
      (MeasureTheory.measurePreserving_prod_add
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))
  convert heprod.symm.comp (hshear.comp heprod) using 1
  ext z i μ
  fin_cases i <;>
    simp [eprod, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
      MeasurableEquiv.shearAddRight]

/-- Rewriting the witness integral against a two-point center/difference lift in
center/difference coordinates. -/
theorem integral_mul_twoPointDifferenceLift_eq_centerDiff {d : ℕ}
    (Ψ : NPointDomain d 2 → ℂ)
    (χ h : SchwartzSpacetime d) :
    ∫ x : NPointDomain d 2, Ψ x * (twoPointDifferenceLift χ h) x =
      ∫ z : NPointDomain d 2,
        Ψ ((twoPointCenterDiffCLE d) z) * (χ (z 0) * h (z 1)) := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    twoPointCenterDiff_measurePreserving (d := d)
  calc
    ∫ x : NPointDomain d 2, Ψ x * (twoPointDifferenceLift χ h) x
      = ∫ z : NPointDomain d 2,
          (fun x : NPointDomain d 2 => Ψ x * (twoPointDifferenceLift χ h) x) (e z) := by
            symm
            exact hmp.integral_comp' (f := e)
              (g := fun x : NPointDomain d 2 => Ψ x * (twoPointDifferenceLift χ h) x)
    _ = ∫ z : NPointDomain d 2,
          Ψ ((twoPointCenterDiffCLE d) z) * (χ (z 0) * h (z 1)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            simp [e, twoPointDifferenceLift_apply, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

/-- Rewriting the witness integral against a two-point product-shell test in
center/difference coordinates. This exposes the semigroup-side shear
`(u, ξ) ↦ χ(u) g(u + ξ)` explicitly. -/
theorem integral_mul_twoPointProductLift_eq_centerShear {d : ℕ}
    (Ψ : NPointDomain d 2 → ℂ)
    (χ g : SchwartzSpacetime d) :
    ∫ x : NPointDomain d 2, Ψ x * (twoPointProductLift χ g) x =
      ∫ z : NPointDomain d 2,
        Ψ ((twoPointCenterDiffCLE d) z) * (χ (z 0) * g (z 0 + z 1)) := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    twoPointCenterDiff_measurePreserving (d := d)
  calc
    ∫ x : NPointDomain d 2, Ψ x * (twoPointProductLift χ g) x
      = ∫ z : NPointDomain d 2,
          (fun x : NPointDomain d 2 => Ψ x * (twoPointProductLift χ g) x) (e z) := by
            symm
            exact hmp.integral_comp' (f := e)
              (g := fun x : NPointDomain d 2 => Ψ x * (twoPointProductLift χ g) x)
    _ = ∫ z : NPointDomain d 2,
          Ψ ((twoPointCenterDiffCLE d) z) * (χ (z 0) * g (z 0 + z 1)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            simp [e, twoPointProductLift_apply, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

private theorem continuous_twoPointDiff (d : ℕ) :
    Continuous (fun x : NPointDomain d 2 => x 1 - x 0) := by
  exact (continuous_apply (1 : Fin 2)).sub (continuous_apply (0 : Fin 2))

private theorem tsupport_precomp_subset_twoPoint {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {g : X → Y} (hg : Continuous g) :
    tsupport (fun x => f (g x)) ⊆ g ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hg)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

/-- The support of the two-point difference lift is controlled by the support of
the difference-variable test. This is the honest admissibility input for the
two-point Schwinger reduction. -/
theorem tsupport_twoPointDifferenceLift_subset_diff_preimage {d : ℕ}
    (χ h : SchwartzSpacetime d) :
    tsupport ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) ⊆
      (fun x : NPointDomain d 2 => x 1 - x 0) ⁻¹' tsupport (h : SpacetimeDim d → ℂ) := by
  refine (tsupport_mul_subset_right
    (f := fun x : NPointDomain d 2 => χ (x 0))
    (g := fun x : NPointDomain d 2 => h (x 1 - x 0))).trans ?_
  exact tsupport_precomp_subset_twoPoint (f := (h : SpacetimeDim d → ℂ))
    (g := fun x : NPointDomain d 2 => x 1 - x 0) (continuous_twoPointDiff d)

/-- If the difference-variable test is supported away from `0`, then the lifted
two-point test is automatically zero-diagonal. -/
theorem twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport {d : ℕ}
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hxlift hxcoin
  have hdiff_mem :
      x 1 - x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact (tsupport_twoPointDifferenceLift_subset_diff_preimage χ h hxlift)
  rcases hxcoin with ⟨i, j, hij, hijEq⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  ·
    have hdiff0 : x 1 - x 0 = 0 := by
      simpa [sub_eq_add_neg] using congrArg (fun z => z - x 0) hijEq.symm
    exact h0 (hdiff0 ▸ hdiff_mem)
  ·
    have hdiff0 : x 1 - x 0 = 0 := by
      have hzero : 0 = x 1 - x 0 := by
        simpa [sub_eq_add_neg] using congrArg (fun z => x 1 - z) hijEq
      exact hzero.symm
    exact h0 (hdiff0 ▸ hdiff_mem)
  · exact (hij rfl).elim

/-- The reduced one-variable test space used by the honest two-point Schwinger
difference pairing: Schwartz functions with compact support contained in the
positive-time half-space. This is a genuine `ℂ`-submodule. -/
def positiveTimeCompactSupportSubmodule (d : ℕ) :
    Submodule ℂ (SchwartzSpacetime d) where
  carrier := {h : SchwartzSpacetime d |
    tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
      HasCompactSupport (h : SpacetimeDim d → ℂ)}
  zero_mem' := by
    constructor
    · simp
    · simpa using (HasCompactSupport.zero :
        HasCompactSupport ((0 : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
  add_mem' := by
    intro h g hh hg
    constructor
    · intro x hx
      have hx' := tsupport_add (h : SpacetimeDim d → ℂ) (g : SpacetimeDim d → ℂ) hx
      exact hx'.elim (fun hx_h => hh.1 hx_h) (fun hx_g => hg.1 hx_g)
    · simpa using hh.2.add hg.2
  smul_mem' := by
    intro c h hh
    constructor
    · exact (tsupport_smul_subset_right
        (fun _ : SpacetimeDim d => c) (h : SpacetimeDim d → ℂ)).trans hh.1
    · simpa [Pi.smul_apply] using
        (HasCompactSupport.smul_left (f := fun _ : SpacetimeDim d => c)
          (f' := (h : SpacetimeDim d → ℂ)) hh.2)

/-- Any reduced positive-time compactly supported Schwartz test is supported
away from the origin. -/
theorem zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule {d : ℕ}
    (h : positiveTimeCompactSupportSubmodule d) :
    (0 : SpacetimeDim d) ∉ tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  intro hmem
  have := h.property.1 hmem
  simpa using this

/-- Inclusion of the positive-time compact-support reduced test space into the
ambient Schwartz space. -/
def positiveTimeCompactSupportValCLM (d : ℕ) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] SchwartzSpacetime d where
  toLinearMap := (positiveTimeCompactSupportSubmodule d).subtype
  cont := continuous_subtype_val

@[simp] theorem positiveTimeCompactSupportValCLM_apply {d : ℕ}
    (h : positiveTimeCompactSupportSubmodule d) :
    (positiveTimeCompactSupportValCLM d h : SchwartzSpacetime d) =
      (h : SchwartzSpacetime d) := by
  rfl

/-- The convolution of two reduced positive-time compact-support Schwartz tests
again lies in the same reduced domain. This is the natural one-variable
smoothing operator on the honest Schwinger difference-test space. -/
def positiveTimeCompactSupportConvolution {d : ℕ}
    (g h : positiveTimeCompactSupportSubmodule d) :
    positiveTimeCompactSupportSubmodule d := by
  let fconv : SpacetimeDim d → ℂ :=
    ((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, MeasureTheory.volume]
      ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  have hconv_compact : HasCompactSupport fconv := by
    simpa [fconv] using
      (g.property.2.convolution (L := ContinuousLinearMap.lsmul ℝ ℂ) h.property.2)
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) fconv := by
    have hg_loc :
        MeasureTheory.LocallyIntegrable
          ((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) MeasureTheory.volume := by
      haveI : (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)).HasTemperateGrowth :=
        MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
      exact ((g : SchwartzSpacetime d).integrable (μ := MeasureTheory.volume)).locallyIntegrable
    simpa [fconv] using
      h.property.2.contDiff_convolution_right
        (L := ContinuousLinearMap.lsmul ℝ ℂ) (μ := MeasureTheory.volume) hg_loc
        ((h : SchwartzSpacetime d).smooth' :
          ContDiff ℝ (⊤ : ℕ∞) ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
  let convS : SchwartzSpacetime d := hconv_compact.toSchwartzMap hconv_smooth
  have hconv_eq : (convS : SpacetimeDim d → ℂ) = fconv := by
    ext x
    simpa [convS] using HasCompactSupport.toSchwartzMap_toFun hconv_compact hconv_smooth x
  refine ⟨convS, ?_⟩
  constructor
  · intro x hx
    have hx' : x ∈ tsupport fconv := by
      simpa [hconv_eq] using hx
    have hsum_closed : IsClosed
        (tsupport ((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) +
          tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
      exact (g.property.2.isCompact.add h.property.2.isCompact).isClosed
    have htsupp_subset :
        tsupport fconv ⊆
          tsupport ((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) +
            tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
      refine closure_minimal ?_ hsum_closed
      exact (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.lsmul ℝ ℂ)).trans
        (Set.add_subset_add subset_closure subset_closure)
    have hxsum :
        x ∈ tsupport ((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) +
          tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
      exact htsupp_subset hx'
    rcases hxsum with ⟨u, hu, v, hv, rfl⟩
    have hu_pos : 0 < u 0 := g.property.1 hu
    have hv_pos : 0 < v 0 := h.property.1 hv
    simpa using add_pos hu_pos hv_pos
  · simpa [hconv_eq] using hconv_compact

@[simp] theorem positiveTimeCompactSupportConvolution_apply {d : ℕ}
    (g h : positiveTimeCompactSupportSubmodule d) (x : SpacetimeDim d) :
    ((positiveTimeCompactSupportConvolution g h : positiveTimeCompactSupportSubmodule d) :
        SchwartzSpacetime d) x =
      MeasureTheory.convolution (L := ContinuousLinearMap.lsmul ℝ ℂ)
        (μ := MeasureTheory.volume)
        (((g : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) x := by
  rfl

theorem positiveTimeCompactSupportConvolution_apply_eq_integral_translate {d : ℕ}
    (h g : positiveTimeCompactSupportSubmodule d) (x : SpacetimeDim d) :
    ((positiveTimeCompactSupportConvolution h g : positiveTimeCompactSupportSubmodule d) :
        SchwartzSpacetime d) x =
      ∫ ξ : SpacetimeDim d,
        ((h : SchwartzSpacetime d) ξ) *
          (SCV.translateSchwartz (-ξ) (g : SchwartzSpacetime d)) x := by
  rw [positiveTimeCompactSupportConvolution_apply]
  simp [MeasureTheory.convolution, SCV.translateSchwartz_apply, sub_eq_add_neg]

/-- The natural reduced one-variable Schwartz test space for the two-point
Schwinger difference distribution: functions whose support avoids the origin.
This is exactly the condition needed for `twoPointDifferenceLift χ h` to lie in
`ZeroDiagonalSchwartz d 2`. -/
def zeroOriginAvoidingSubmodule (d : ℕ) :
    Submodule ℂ (SchwartzSpacetime d) where
  carrier := {h : SchwartzSpacetime d |
    (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)}
  zero_mem' := by
    simp
  add_mem' := by
    intro h g hh hg
    intro hmem
    have hmem' := tsupport_add (h : SpacetimeDim d → ℂ) (g : SpacetimeDim d → ℂ) hmem
    exact hmem'.elim hh hg
  smul_mem' := by
    intro c h hh
    intro hmem
    exact hh ((tsupport_smul_subset_right
      (fun _ : SpacetimeDim d => c) (h : SpacetimeDim d → ℂ)) hmem)

/-- Inclusion of the zero-origin-avoiding reduced test space into the ambient
Schwartz space. -/
def zeroOriginAvoidingValCLM (d : ℕ) :
    zeroOriginAvoidingSubmodule d →L[ℂ] SchwartzSpacetime d where
  toLinearMap := (zeroOriginAvoidingSubmodule d).subtype
  cont := continuous_subtype_val

@[simp] theorem zeroOriginAvoidingValCLM_apply {d : ℕ}
    (h : zeroOriginAvoidingSubmodule d) :
    (zeroOriginAvoidingValCLM d h : SchwartzSpacetime d) =
      (h : SchwartzSpacetime d) := by
  rfl

/-- Positive-time compactly supported reduced tests automatically lie in the
zero-origin-avoiding reduced test space. -/
def positiveTimeCompactSupportToZeroOriginAvoidingCLM (d : ℕ) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] zeroOriginAvoidingSubmodule d :=
  (positiveTimeCompactSupportValCLM d).codRestrict (zeroOriginAvoidingSubmodule d)
    zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule

@[simp] theorem positiveTimeCompactSupportToZeroOriginAvoidingCLM_apply {d : ℕ}
    (h : positiveTimeCompactSupportSubmodule d) :
    (positiveTimeCompactSupportToZeroOriginAvoidingCLM d h : SchwartzSpacetime d) =
      (h : SchwartzSpacetime d) := by
  rfl

/-- Under the support-away-from-zero hypothesis on `h`, the center-variable lift
lands honestly in the Schwinger test space `ZeroDiagonalSchwartz d 2`. -/
def twoPointDifferenceLiftZeroDiagCLM {d : ℕ}
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    SchwartzSpacetime d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
      (SchwartzMap.prependFieldCLMLeft (onePointToFin1CLM d h))).codRestrict
    (zeroDiagonalSubmodule d 2)
    (fun χ => twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0)

@[simp] theorem twoPointDifferenceLiftZeroDiagCLM_apply {d : ℕ}
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d) :
    (twoPointDifferenceLiftZeroDiagCLM h h0 χ).1 = twoPointDifferenceLift χ h := by
  rfl

@[simp] theorem twoPointDifferenceLiftZeroDiagCLM_eq_ofClassical {d : ℕ}
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d) :
    twoPointDifferenceLiftZeroDiagCLM h h0 χ =
      ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h) := by
  let hv := twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0
  apply Subtype.ext
  rw [twoPointDifferenceLiftZeroDiagCLM_apply, ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := twoPointDifferenceLift χ h) hv]

/-- Continuous linear family of two-point center/difference lifts with the
center test fixed and the reduced difference test varying in the natural
zero-origin-avoiding domain. -/
def twoPointDifferenceLiftFixedCenterZeroDiagCLM {d : ℕ}
    (χ : SchwartzSpacetime d) :
    zeroOriginAvoidingSubmodule d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
      ((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
        ((onePointToFin1CLM d).comp (zeroOriginAvoidingValCLM d)))).codRestrict
      (zeroDiagonalSubmodule d 2)
      (fun h =>
        twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ
          ((zeroOriginAvoidingValCLM d) h) h.property))

@[simp] theorem twoPointDifferenceLiftFixedCenterZeroDiagCLM_apply {d : ℕ}
    (χ : SchwartzSpacetime d)
    (h : zeroOriginAvoidingSubmodule d) :
    (twoPointDifferenceLiftFixedCenterZeroDiagCLM χ h).1 =
      twoPointDifferenceLift χ (h : SchwartzSpacetime d) := by
  rfl

@[simp] theorem twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical {d : ℕ}
    (χ : SchwartzSpacetime d)
    (h : zeroOriginAvoidingSubmodule d) :
    twoPointDifferenceLiftFixedCenterZeroDiagCLM χ h =
      ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ (h : SchwartzSpacetime d)) := by
  let hv :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ (h : SchwartzSpacetime d) h.property
  apply Subtype.ext
  rw [twoPointDifferenceLiftFixedCenterZeroDiagCLM_apply,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ (h : SchwartzSpacetime d)) hv]

/-- The honest two-point Schwinger difference functional on the natural reduced
zero-origin-avoiding one-variable Schwartz test space, for a fixed center cutoff
`χ`. This is the canonical reduced Schwinger object behind the kernel
representation problem. -/
def OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d) :
    zeroOriginAvoidingSubmodule d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
    (twoPointDifferenceLiftFixedCenterZeroDiagCLM χ)

@[simp] theorem OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (h : zeroOriginAvoidingSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM (d := d) OS χ) h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) := by
  simp [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM,
    twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical,
    ContinuousLinearMap.comp_apply, OsterwalderSchraderAxioms.schwingerCLM]

/-- Continuous linear family of two-point center/difference lifts with the
center test fixed and the positive-time compact difference test varying in the
second slot. The codomain is honestly `ZeroDiagonalSchwartz d 2`, because
positive-time support keeps the difference variable away from the diagonal. -/
def twoPointDifferenceLiftPositiveZeroDiagCLM {d : ℕ}
    (χ : SchwartzSpacetime d) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
      ((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
        ((onePointToFin1CLM d).comp (positiveTimeCompactSupportValCLM d)))).codRestrict
      (zeroDiagonalSubmodule d 2)
      (fun h =>
        twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ
          ((positiveTimeCompactSupportValCLM d) h)
          (zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule h)))

@[simp] theorem twoPointDifferenceLiftPositiveZeroDiagCLM_apply {d : ℕ}
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    (twoPointDifferenceLiftPositiveZeroDiagCLM χ h).1 =
      twoPointDifferenceLift χ (h : SchwartzSpacetime d) := by
  rfl

@[simp] theorem twoPointDifferenceLiftPositiveZeroDiagCLM_eq_ofClassical {d : ℕ}
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    twoPointDifferenceLiftPositiveZeroDiagCLM χ h =
      ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ (h : SchwartzSpacetime d)) := by
  let hv :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ (h : SchwartzSpacetime d)
      (zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule h)
  apply Subtype.ext
  rw [twoPointDifferenceLiftPositiveZeroDiagCLM_apply,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ (h : SchwartzSpacetime d)) hv]

/-- The honest two-point Schwinger difference functional on the reduced
positive-time compact-support test space, for a fixed center cutoff `χ`. -/
def OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
    (twoPointDifferenceLiftPositiveZeroDiagCLM χ)

@[simp] theorem OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM (d := d) OS χ) h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) := by
  simp [OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM,
    twoPointDifferenceLiftPositiveZeroDiagCLM_eq_ofClassical,
    ContinuousLinearMap.comp_apply, OsterwalderSchraderAxioms.schwingerCLM]

@[simp] theorem OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_restrict_positive
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM (d := d) OS χ)
        ((positiveTimeCompactSupportToZeroOriginAvoidingCLM d) h) =
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM (d := d) OS χ) h := by
  simp [OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_apply,
    OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply]

/-- Translating the center-variable test is exactly diagonal Euclidean
translation of the lifted two-point test. -/
theorem twoPointDifferenceLift_translate_center {d : ℕ}
    (a : SpacetimeDim d) (χ h : SchwartzSpacetime d) :
    ∀ x : NPointDomain d 2,
      twoPointDifferenceLift (SCV.translateSchwartz a χ) h x =
        twoPointDifferenceLift χ h (fun i => x i + a) := by
  intro x
  have hdiff : (x 1 + a) - (x 0 + a) = x 1 - x 0 := by
    abel_nf
  simp [twoPointDifferenceLift_apply, SCV.translateSchwartz_apply, hdiff]

/-- Honest Schwinger-side two-point translation shell: for admissible factorized
two-point tests, translating the center-variable test does not change the
two-point Schwinger value. -/
theorem OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
    (OS : OsterwalderSchraderAxioms d) (a : SpacetimeDim d)
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift (SCV.translateSchwartz a χ) h)) := by
  have hχ : VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0
  have hχa : VanishesToInfiniteOrderOnCoincidence
      (twoPointDifferenceLift (SCV.translateSchwartz a χ) h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport (SCV.translateSchwartz a χ) h h0
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := twoPointDifferenceLift χ h) hχ,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointDifferenceLift (SCV.translateSchwartz a χ) h) hχa]
  exact OS.E1_translation_invariant 2 a
    ⟨twoPointDifferenceLift χ h, hχ⟩
    ⟨twoPointDifferenceLift (SCV.translateSchwartz a χ) h, hχa⟩
    (twoPointDifferenceLift_translate_center a χ h)

/-- For fixed admissible difference-variable test `h`, the corresponding
center-slot two-point Schwinger functional is translation-invariant. -/
theorem OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLiftCLM_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∀ a : SpacetimeDim d,
      ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
        (twoPointDifferenceLiftZeroDiagCLM h h0)).comp (SCV.translateSchwartzCLM a)
        =
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
        (twoPointDifferenceLiftZeroDiagCLM h h0) := by
  intro a
  ext χ
  change OS.S 2 (twoPointDifferenceLiftZeroDiagCLM h h0 (SCV.translateSchwartzCLM a χ)) =
    OS.S 2 (twoPointDifferenceLiftZeroDiagCLM h h0 χ)
  simpa [twoPointDifferenceLiftZeroDiagCLM_eq_ofClassical, ContinuousLinearMap.comp_apply] using
    (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
      (d := d) (OS := OS) (a := a) (χ := χ) (h := h) h0).symm

/-- Two-point Schwinger reduction: the admissible factorized two-point family
depends only on the difference-variable test. -/
theorem OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
        c * ∫ x : SpacetimeDim d, χ x := by
  obtain ⟨c, hc⟩ := OSReconstruction.exists_eq_const_integralCLM_of_translationInvariant
    (((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
      (twoPointDifferenceLiftZeroDiagCLM h h0)))
    (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLiftCLM_translation_invariant
      (d := d) (OS := OS) (h := h) h0)
  refine ⟨c, ?_⟩
  intro χ
  have hχ :
      ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
        (twoPointDifferenceLiftZeroDiagCLM h h0)) χ
        =
      (c • (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))) χ := by
    exact congrArg (fun L : SchwartzSpacetime d →L[ℂ] ℂ => L χ) hc
  simpa [twoPointDifferenceLiftZeroDiagCLM_eq_ofClassical, ContinuousLinearMap.comp_apply,
    SchwartzMap.integralCLM_apply, smul_eq_mul] using hχ

/-- Normalized-center form of the two-point Schwinger reduction. Once a center
Schwartz cutoff `χ₀` with integral `1` is fixed, every admissible lifted
two-point value is obtained by scaling the single value at `χ₀` by `∫ χ`. -/
theorem OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) *
        ∫ x : SpacetimeDim d, χ x := by
  obtain ⟨c, hc⟩ :=
    OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral
      (d := d) OS h h0
  have hχ₀_eval :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) = c := by
    simpa [hχ₀] using hc χ₀
  have hc' : c = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    simpa using hχ₀_eval.symm
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
      = c * ∫ x : SpacetimeDim d, χ x := hc χ
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) *
          ∫ x : SpacetimeDim d, χ x := by rw [hc']

/-- On the natural reduced zero-origin-avoiding one-variable test space, the
two-point Schwinger difference functional is independent of the chosen
normalized center cutoff, up to the expected scalar factor `∫ χ`. -/
theorem OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (h : zeroOriginAvoidingSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) =
      (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM (d := d) OS χ₀) h
        * ∫ x : SpacetimeDim d, χ x := by
  rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply]
  exact OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
    (d := d) OS (h : SchwartzSpacetime d) h.property χ₀ hχ₀ χ

/-- On the reduced positive-time compact-support test space, the two-point
Schwinger difference functional is independent of the chosen normalized center
cutoff, up to the expected scalar factor `∫ χ`. -/
theorem OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_eq_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) =
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM (d := d) OS χ₀) h
        * ∫ x : SpacetimeDim d, χ x := by
  have h0 :
      (0 : SpacetimeDim d) ∉ tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
    zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule h
  rw [OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_apply]
  exact OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
    (d := d) OS (h : SchwartzSpacetime d) h0 χ₀ hχ₀ χ

/-- The two-point difference lift after swapping the two Euclidean arguments.
Pointwise this is the negative-difference shell `χ(x₁) * h(x₀ - x₁)`. -/
def twoPointSwappedDifferenceLift
    (χ h : SchwartzSpacetime d) : SchwartzNPoint d 2 :=
  reindexSchwartz (d := d) (Equiv.swap (0 : Fin 2) (1 : Fin 2))
    (twoPointDifferenceLift χ h)

/-- The swapped two-point difference shell, packaged on the honest
zero-diagonal test space. -/
def twoPointSwappedDifferenceLiftZeroDiag
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ZeroDiagonalSchwartz d 2 :=
  ⟨twoPointSwappedDifferenceLift (d := d) χ h,
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      (d := d)
      (f := twoPointDifferenceLift χ h)
      (twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0)
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))⟩

@[simp] theorem twoPointSwappedDifferenceLift_apply
    (χ h : SchwartzSpacetime d) (x : NPointDomain d 2) :
    twoPointSwappedDifferenceLift (d := d) χ h x =
      χ (x 1) * h (x 0 - x 1) := by
  simp [twoPointSwappedDifferenceLift, twoPointDifferenceLift_apply]

@[simp] theorem twoPointSwappedDifferenceLift_centerDiff_apply
    (χ h : SchwartzSpacetime d) (z : NPointDomain d 2) :
    twoPointSwappedDifferenceLift (d := d) χ h ((twoPointCenterDiffCLE d) z) =
      χ (z 0 + z 1) * h (-z 1) := by
  simp [twoPointSwappedDifferenceLift, twoPointDifferenceLift_apply,
    twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

/-- Specialized `E3` for the two-point difference shell: swapping the two
Euclidean arguments turns `χ(x₀) h(x₁ - x₀)` into the negative-difference shell
`χ(x₁) h(x₀ - x₁)` without changing the Schwinger value. -/
theorem OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_eq_swapped
    (OS : OsterwalderSchraderAxioms d)
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ h h0) := by
  let hf :
      VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0
  let fZ : ZeroDiagonalSchwartz d 2 :=
    ⟨twoPointDifferenceLift χ h, hf⟩
  let gZ : ZeroDiagonalSchwartz d 2 :=
    twoPointSwappedDifferenceLiftZeroDiag (d := d) χ h h0
  have hE3 :
      OS.S 2 fZ = OS.S 2 gZ := by
    refine OS.E3_symmetric (n := 2) (σ := Equiv.swap (0 : Fin 2) (1 : Fin 2)) fZ gZ ?_
    intro x
    simp [fZ, gZ, twoPointSwappedDifferenceLiftZeroDiag, twoPointSwappedDifferenceLift]
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ h) hf]
  simpa [fZ, gZ] using hE3

/-- The swapped negative-difference shell satisfies the same center-value
reduction as the positive-difference shell, by combining the standard
two-point center-value theorem with `E3`. -/
theorem OsterwalderSchraderAxioms.schwinger_twoPointSwappedDifferenceLift_eq_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ h h0) =
      OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ h h0) *
        ∫ x : SpacetimeDim d, χ x := by
  calc
    OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ h h0)
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
          symm
          exact OS.schwinger_twoPointDifferenceLift_eq_swapped (d := d) χ h h0
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) *
          ∫ x : SpacetimeDim d, χ x := by
            exact OS.twoPointDifferenceLift_eq_centerValue
              (d := d) h h0 χ₀ hχ₀ χ
    _ = OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ h h0) *
          ∫ x : SpacetimeDim d, χ x := by
            rw [OS.schwinger_twoPointDifferenceLift_eq_swapped (d := d) χ₀ h h0]

/-- Varying one factor of a product tensor and then evaluating the Schwinger
functional gives a continuous linear functional in that slot, provided the
updated product tensors remain zero-diagonal. -/
def OsterwalderSchraderAxioms.productTensorSlotCLM
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d)
    (hvanish : ∀ f : SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence
        (SchwartzMap.productTensor (Function.update fs i f))) :
    SchwartzSpacetime d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
    (ZeroDiagonalSchwartz.productTensorUpdateCLM (d := d) i fs hvanish)

@[simp]
theorem OsterwalderSchraderAxioms.productTensorSlotCLM_apply
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d)
    (hvanish : ∀ f : SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence
        (SchwartzMap.productTensor (Function.update fs i f)))
    (f : SchwartzSpacetime d) :
    OsterwalderSchraderAxioms.productTensorSlotCLM (d := d) OS i fs hvanish f =
      OS.S n ⟨SchwartzMap.productTensor (Function.update fs i f), hvanish f⟩ := by
  rfl

/-- On factorized tests that stay in the zero-diagonal subspace, the Schwinger
functional is jointly continuous in all tensor factors. -/
theorem OsterwalderSchraderAxioms.productTensorContinuous
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (hvanish : ∀ fs : Fin n → SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)) :
    Continuous (fun fs : Fin n → SchwartzSpacetime d =>
      OS.S n ⟨SchwartzMap.productTensor fs, hvanish fs⟩) := by
  let tensorMap : (Fin n → SchwartzSpacetime d) → ZeroDiagonalSchwartz d n :=
    fun fs => ⟨SchwartzMap.productTensor fs, hvanish fs⟩
  have htensor : Continuous tensorMap := by
    exact (SchwartzMap.productTensor_continuous (E := SpacetimeDim d)).subtype_mk _
  exact (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).continuous.comp htensor

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

/-- The linear growth condition E0' from OS II (1975).

    This replaces the simple temperedness E0 with a stronger condition:
    There exist s ∈ ℤ₊ and constants α, β, γ such that for σₙ ≤ αβⁿ(n!)^γ,
      |Sₙ(f)| ≤ σₙ ‖f‖_{s,n}

    This condition controls the growth of the distribution order as n → ∞,
    which is essential for proving temperedness of the reconstructed
    Wightman distributions.

    The key point is that this growth hypothesis belongs on the Euclidean side
    before reconstruction; it does not erase the main difficulty. The theorem
    still has to manufacture full tempered Wightman distributions starting only
    from Schwinger data whose honest Euclidean test space is `°S`. -/
structure OSLinearGrowthCondition (d : ℕ) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  /-- E0' normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  /-- The Sobolev index s -/
  sobolev_index : ℕ
  /-- Factorial growth bound constants: σₙ ≤ α · βⁿ · (n!)^γ -/
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  /-- The bounds are positive -/
  alpha_pos : alpha > 0
  beta_pos : beta > 0
  /-- The linear growth estimate: |Sₙ(f)| ≤ σₙ · ‖f‖_{s,n}
      where σₙ ≤ α · βⁿ · (n!)^γ bounds the distribution order growth,
      and ‖f‖_{s,n} is the Schwartz seminorm of order s on n-point functions.

      This is equation (4.1) of OS II: |Sₙ(f)| ≤ σₙ |f|_s
      where |f|_s = SchwartzMap.seminorm ℝ s s (f). -/
  growth_estimate : ∀ (n : ℕ) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      SchwartzMap.seminorm ℝ sobolev_index sobolev_index f.1

/-- The honest zero-diagonal Schwinger family underlying an OS package.

    Public reconstruction theorems should be stated in terms of this actual
    Euclidean datum on `ZeroDiagonalSchwartz`. -/
def OsterwalderSchraderAxioms.schwinger {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) : SchwingerFunctions d :=
  OS.S

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

@[simp] theorem osInner_zero_left (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    osInner OS 0 F = 0 := by
  unfold osInner
  simpa using OSInnerProduct_zero_left (d := d) OS.S OS.E0_linear (F : BorchersSequence d)

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

/-- The zero-diagonal Wick-rotation relation between Wightman functions and their
    honest OS-I Euclidean counterparts.

    Formally: there exists a holomorphic function on the forward tube
    (the "analytic continuation") that:
    1. Has distributional boundary values equal to the Wightman functions W_n
    2. When restricted to Euclidean points (via Wick rotation) and paired with
       zero-diagonal test functions, reproduces the Euclidean family S_n on `°S`

    This is the honest Wightman -> OS-I surface.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def IsWickRotationPair {d : ℕ} [NeZero d]
    (S : SchwingerFunctions d) (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ (n : ℕ), ∃ (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
    -- F_analytic is holomorphic on the forward tube
    DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
    -- Boundary values of F_analytic = W_n (as distributions):
    -- For each test function f and approach direction η ∈ ForwardConeAbs,
    -- lim_{ε→0⁺} ∫ F_analytic(x + iε·η) f(x) dx = W_n(f)
    (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f))) ∧
    -- Euclidean restriction gives S_n on the zero-diagonal OS-I domain.
    (∀ (f : ZeroDiagonalSchwartz d n),
      S n f = ∫ x : NPointDomain d n,
        F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x))

-- `wightman_to_os` and `os_to_wightman` moved to Reconstruction/Main.lean
-- (proved via WickRotation.lean: wightman_to_os_full, os_to_wightman_full)

end
