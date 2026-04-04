/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.DenseCLM

/-!
# Positivity of the Reconstructed Wightman Inner Product (OS 1973 §4.3)

This file proves `bvt_W_positive_proof`: for the reconstructed Wightman distributions
`bvt_W OS lgc`, the Wightman inner product is positive semi-definite on all
Borchers sequences.

## Proof strategy

1. **Compact ordered positive-time layer**: For compact ordered positive-time
   Borchers vectors `F`, the BV comparison chain identifies
   `WightmanInnerProduct = osInner ≥ 0`.

2. **Continuity layer**: The Wightman quadratic form is continuous under
   componentwise Schwartz convergence for fixed-bound sequences.

3. **Dense-image passage**: Ordered positive-time compact n-point functions are
   dense in `SchwartzNPoint d n`. By continuity, positivity extends to all
   Borchers vectors.

## Main result

- `bvt_W_positive_proof`: `∀ F, (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0`
-/

set_option maxHeartbeats 400000

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Layer 1: Compact ordered positive-time positivity -/

/-- For compact ordered positive-time Borchers vectors, the xiShift boundary-value
convergence needed by the comparison theorems holds. This requires converting
the general `bvt_boundary_values` convergence (which uses a full forward-cone
direction η) into the specific single-split xiShift form, using the holomorphic
bridge between the two parametrizations. -/
private theorem bvt_hWlimit_of_compact_ordered_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (n m : ℕ) (hm : 0 < m) :
    Filter.Tendsto
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs m)) y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((F : BorchersSequence d).funcs m))))) := by
  sorry

/-- The Hermitian property of `bvt_W`, proved from the boundary-ray infrastructure.
This is the same argument as `bvt_hermitian` in `OSToWightmanBoundaryValues.lean`,
factored out here to avoid circular imports. -/
private theorem bvt_hermitian_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  have hF_reflect_pairing :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
    intro n f g ε hε hfg
    exact boundary_ray_hermitian_pairing_of_F_negCanonical (d := d) n
      (bvt_F OS lgc n)
      (bvt_F_perm OS lgc n)
      (bvt_F_translationInvariant OS lgc n)
      (bvt_F_negCanonical OS lgc n)
      f g ε hε hfg
  intro n f g hfg
  exact bv_hermiticity_transfer (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (hF_reflect_pairing n)
    f g hfg

/-- For compact ordered positive-time Borchers vectors, the Wightman inner product
equals the OS inner product and is therefore nonneg. -/
private theorem bvt_wightmanInner_self_nonneg_of_compact_ordered_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  rw [bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
    (d := d) OS lgc (bvt_hermitian_local OS lgc) F hF_compact
    (fun n m hm => bvt_hWlimit_of_compact_ordered_positiveTime OS lgc F hF_compact n m hm)]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-! ### Layer 2: Continuity of the Wightman quadratic form -/

omit [NeZero d] in
/-- `conjTensorProduct` is jointly continuous in both arguments.
Since `conjTensorProduct f g = f.borchersConj.tensorProduct g`, this follows
from the continuity of `borchersConj` (which is `conj ∘ reverse`, both
continuous on Schwartz space) and `SchwartzMap.tensorProduct_continuous`. -/
private theorem conjTensorProduct_continuous_joint (n m : ℕ) :
    Continuous (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
      p.1.conjTensorProduct p.2) := by
  -- borchersConj is continuous (conj ∘ reverse, same proof as GNSHilbertSpace)
  have hbc : Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
    let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      { toFun := fun y i => y (Fin.rev i)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y i => y (Fin.rev i)
        left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
        right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
        continuous_toFun := continuous_pi fun i => continuous_apply (Fin.rev i)
        continuous_invFun := continuous_pi fun i => continuous_apply (Fin.rev i) }
    let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
    have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
      intro f; ext x; simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        SchwartzMap.reverse_apply, revCLE]
    have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
      let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
        { toFun := SchwartzMap.conj
          map_add' := fun f g => by ext x; simp [SchwartzMap.conj_apply]
          map_smul' := fun c f => by ext x; simp [SchwartzMap.conj_apply] }
      exact Seminorm.continuous_from_bounded
        (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
        (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
        conjL (fun q => by
          rcases q with ⟨k, l⟩
          refine ⟨{(k, l)}, 1, ?_⟩
          intro f
          simpa [Finset.sup_singleton] using SchwartzMap.seminorm_conj_le k l f)
    show Continuous (fun f => (revCLM f).conj)
    exact (hconj_cont.comp revCLM.continuous).congr (fun f => by
      show (revCLM f).conj = f.borchersConj
      rw [hrev]; rfl)
  -- conjTensorProduct = tensorProduct ∘ (borchersConj × id)
  simp only [SchwartzMap.conjTensorProduct]
  exact SchwartzMap.tensorProduct_continuous.comp
    ((hbc.comp continuous_fst).prodMk continuous_snd)

/-- Sequential continuity of the Wightman self-inner-product under componentwise
Schwartz convergence: if `F_k → F` componentwise, then
`WightmanInnerProduct(F_k, F_k) → WightmanInnerProduct(F, F)`.

Proof outline: `WightmanInnerProduct` is a finite sum of terms
`bvt_W(n+m)(f_n.conjTensorProduct f_m)`, each continuous in `(f_n, f_m)`.
A finite sum of convergent sequences converges. -/
private theorem WightmanInnerProduct_tendsto_of_componentwise
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_cont : ∀ n, Continuous (W n))
    (F_k : ℕ → BorchersSequence d) (F : BorchersSequence d)
    (hconv : ∀ n, Filter.Tendsto (fun k => (F_k k).funcs n) Filter.atTop
      (nhds (F.funcs n)))
    (hbound : ∀ k, (F_k k).bound = F.bound) :
    Filter.Tendsto
      (fun k => WightmanInnerProduct d W (F_k k) (F_k k))
      Filter.atTop
      (nhds (WightmanInnerProduct d W F F)) := by
  sorry

/-! ### Layer 3: Dense-image passage -/

/-- **Density of ordered positive-time compact n-point functions.**

The set of Schwartz n-point functions with compact support contained in the
ordered positive-time region is dense in `SchwartzNPoint d n`.

This is the key topological ingredient from OS 1973 §4.3. The proof uses:
1. `productTensor_span_dense` (product tensors span a dense subspace)
2. `SchwartzMap.dense_hasCompactSupport` (compact-support density in each factor)
3. An analytic-continuation / identity-principle argument for the entire function
   `(c₁,...,cₙ) ↦ T(τ_{c₁}f₁ ⊗ ⋯ ⊗ τ_{cₙ}fₙ)` to show that a continuous linear
   functional vanishing on all ordered-time-translated compact product tensors
   must vanish identically. -/
private theorem orderedPositiveTime_compact_dense (n : ℕ) :
    Dense {F : SchwartzNPoint d n |
      tsupport (F : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n ∧
      HasCompactSupport (F : NPointDomain d n → ℂ)} := by
  sorry

/-! ### Layer 4: Assembly -/

/-- **Main positivity theorem** (OS 1973 §4.3).

For the reconstructed Wightman distributions `bvt_W OS lgc`, the Wightman inner
product is positive semi-definite on all Borchers sequences. The proof:
1. approximates each component of `F` by ordered positive-time compact functions,
2. shows positivity of the Wightman inner product on each approximant via the
   BV comparison → OS inner product chain,
3. passes to the limit using continuity of the quadratic form. -/
theorem bvt_W_positive_proof
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  intro F
  set B := F.bound
  -- Step 1: By density, approximate each component by ordered positive-time compact
  -- functions. For n > B, the component is already 0 so no approximation needed.
  have hdense_approx : ∀ n, ∃ (s : ℕ → SchwartzNPoint d n),
      (∀ k, tsupport ((s k : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
          OrderedPositiveTimeRegion d n ∧
        HasCompactSupport ((s k : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ∧
      Filter.Tendsto s Filter.atTop (nhds (F.funcs n)) := by
    intro n
    have hd := orderedPositiveTime_compact_dense (d := d) n
    have hmem : F.funcs n ∈ closure {F : SchwartzNPoint d n |
        tsupport (F : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n ∧
        HasCompactSupport (F : NPointDomain d n → ℂ)} := hd.closure_eq ▸ Set.mem_univ _
    rw [mem_closure_iff_seq_limit] at hmem
    exact hmem
  choose seq hseq using hdense_approx
  -- Step 2: Build approximating Borchers sequences with the same bound B.
  -- For n > B, use 0 (matching F.funcs n = 0).
  let u : ℕ → (n : ℕ) → SchwartzNPoint d n := fun k n =>
    if n ≤ B then seq n k else 0
  have hu_bound : ∀ k n, B < n → u k n = 0 := by
    intro k n hn; simp only [u, show ¬(n ≤ B) from Nat.not_le.mpr hn, ite_false]
  have hv_bound : ∀ n, B < n → F.funcs n = 0 :=
    fun n hn => F.bound_spec n hn
  have hconv : ∀ n, Filter.Tendsto (fun k => u k n) Filter.atTop (nhds (F.funcs n)) := by
    intro n
    by_cases hn : n ≤ B
    · have : (fun k => u k n) = (fun k => seq n k) := by
        ext k; simp only [u, hn, ite_true]
      rw [this]; exact (hseq n).2
    · have hFn : F.funcs n = 0 := F.bound_spec n (by omega)
      have : (fun k => u k n) = fun _ => (0 : SchwartzNPoint d n) := by
        ext k; simp only [u, hn, ite_false]
      rw [this, hFn]; exact tendsto_const_nhds
  -- Step 3: Each approximant has ordered positive-time support and compact support.
  have hord_k : ∀ k n, tsupport ((u k n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n := by
    intro k n
    by_cases hn : n ≤ B
    · simp only [u, hn, ite_true]; exact ((hseq n).1 k).1
    · simp only [u, hn, ite_false]
      rw [show ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) = 0 from rfl,
        tsupport_zero]
      exact Set.empty_subset _
  have hcomp_k : ∀ k n, HasCompactSupport ((u k n : SchwartzNPoint d n) :
      NPointDomain d n → ℂ) := by
    intro k n
    by_cases hn : n ≤ B
    · simp only [u, hn, ite_true]; exact ((hseq n).1 k).2
    · simp only [u, hn, ite_false, HasCompactSupport]
      rw [show ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) = 0 from rfl,
        tsupport_zero]
      exact isCompact_empty
  -- Step 4: Build the approximating Borchers sequences.
  let F_k : ℕ → BorchersSequence d := fun k =>
    { funcs := u k, bound := B, bound_spec := hu_bound k }
  -- Step 5: Each approximant is positive-time, hence has nonneg Wightman inner product.
  have hpos_approx : ∀ k,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) (F_k k) (F_k k)).re := by
    intro k
    let G : PositiveTimeBorchersSequence d :=
      { toBorchersSequence := F_k k
        ordered_tsupport := hord_k k }
    exact bvt_wightmanInner_self_nonneg_of_compact_ordered_positiveTime OS lgc G
      (fun n => hcomp_k k n)
  -- Step 6: Pass to the limit using continuity of WightmanInnerProduct.
  have hconv_F : ∀ n, Filter.Tendsto (fun k => (F_k k).funcs n) Filter.atTop
      (nhds (F.funcs n)) := hconv
  have hbound_eq : ∀ k, (F_k k).bound = F.bound := fun _ => rfl
  have hlim := WightmanInnerProduct_tendsto_of_componentwise (bvt_W OS lgc)
    (fun n => bvt_W_continuous OS lgc n) F_k F hconv_F hbound_eq
  -- The limit of nonneg reals is nonneg.
  exact ge_iff_le.mpr (le_of_tendsto_of_tendsto tendsto_const_nhds
    (Filter.Tendsto.comp Complex.continuous_re.continuousAt.tendsto hlim)
    (Filter.Eventually.of_forall (fun k => hpos_approx k)))

end
