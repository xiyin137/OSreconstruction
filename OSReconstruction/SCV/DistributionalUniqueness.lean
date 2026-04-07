/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.TubeDistributions
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Distributional Uniqueness on Tube Domains (Weak Hypothesis Version)

This file proves distributional uniqueness for holomorphic functions on tube
domains using ONLY the weak distributional boundary-value hypothesis, without
requiring `HasFourierLaplaceReprRegular`.

The key technique is **mollification**: given G holomorphic on T(C) with
distributional BV → 0, we convolve G with a Schwartz test function ψ in the
real direction. The convolution G*ψ is holomorphic on T(C), has continuous
boundary values = 0 (from the distributional BV hypothesis), and therefore
vanishes identically by the proved `distributional_uniqueness_tube_of_regular`
machinery (specifically, the 1D EOW slicing argument). Taking ψ → δ gives G = 0.

## Main Results

* `distributional_uniqueness_tube_of_zero_bv`: If G is holomorphic on T(C) and
  its distributional boundary values vanish, then G = 0 on T(C).

## References

* Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25
* Classical mollification argument for distributional boundary values
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped Convolution

namespace SCV

variable {m : ℕ}

/-! ### Schwartz Translation -/

/-- Translate a Schwartz function: `(translateSchwartz t₀ f)(x) = f(x + t₀)`.
    This is Schwartz because translation by a fixed vector preserves rapid decay. -/
def translateSchwartz (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  ⟨fun x => f (x + t₀),
   f.smooth'.comp (contDiff_id.add contDiff_const),
   fun k n => by
     obtain ⟨Ck, hCk⟩ := f.decay' k n
     obtain ⟨C0, hC0⟩ := f.decay' 0 n
     -- Chain rule: D^n (f ∘ (· + t₀)) x = D^n f (x + t₀)
     have hderiv : ∀ x, iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x =
         iteratedFDeriv ℝ n f.toFun (x + t₀) :=
       fun x => iteratedFDeriv_comp_add_right n t₀ x
     -- From 0-th decay: ‖D^n f(y)‖ ≤ C0 for all y
     have hC0' : ∀ y, ‖iteratedFDeriv ℝ n f.toFun y‖ ≤ C0 := by
       intro y; have := hC0 y; simp [pow_zero] at this; linarith
     -- Bound: ‖x‖ ≤ ‖x+t₀‖ + ‖t₀‖ (triangle inequality)
     -- So ‖x‖^k ≤ (‖x+t₀‖ + ‖t₀‖)^k
     -- And (a+b)^k ≤ 2^k * (a^k + b^k) for a,b ≥ 0
     refine ⟨2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0), fun x => ?_⟩
     show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x‖ ≤ _
     rw [hderiv]
     have hnorm_x : ‖x‖ ≤ ‖x + t₀‖ + ‖t₀‖ := by
       calc ‖x‖ = ‖(x + t₀) - t₀‖ := by ring_nf
         _ ≤ ‖x + t₀‖ + ‖t₀‖ := norm_sub_le _ _
     have hnn_deriv : 0 ≤ ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := norm_nonneg _
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖
         ≤ (‖x + t₀‖ + ‖t₀‖) ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr
       _ ≤ (2 ^ (k - 1) * (‖x + t₀‖ ^ k + ‖t₀‖ ^ k)) *
           ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr; exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
       _ = 2 ^ (k - 1) * (‖x + t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ +
           ‖t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖) := by ring
       _ ≤ 2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0) := by
           gcongr
           · exact hCk (x + t₀)
           · exact hC0' (x + t₀)⟩

/-- The translate of a Schwartz function evaluates as expected. -/
@[simp]
theorem translateSchwartz_apply (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) : translateSchwartz t₀ f x = f (x + t₀) := rfl

/-- Translation on Schwartz space as a continuous linear map. -/
noncomputable def translateSchwartzCLM (t₀ : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ := by
  let g : (Fin m → ℝ) → Fin m → ℝ := fun x => x + t₀
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1 + ‖t₀‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖t₀‖ := by
      calc
        ‖x‖ = ‖(x + t₀) - t₀‖ := by simp
        _ ≤ ‖g x‖ + ‖t₀‖ := by simpa [g] using norm_sub_le (x + t₀) t₀
    have hfac : ‖g x‖ + ‖t₀‖ ≤ (1 + ‖t₀‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg t₀]
    have hpow : (1 + ‖g x‖) ^ (1 : ℕ) = 1 + ‖g x‖ := by simp
    rw [hpow]
    exact le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem translateSchwartzCLM_apply (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    translateSchwartzCLM t₀ f = translateSchwartz t₀ f := by
  ext x
  rfl

/-- Real translations of a Schwartz function have polynomial seminorm growth in
the translation parameter. This is the quantitative translation estimate needed
when a tempered functional is evaluated on shifted test families. -/
theorem seminorm_translateSchwartz_le
    (k l : ℕ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    ∃ (D : ℝ), 0 ≤ D ∧ ∀ (a : Fin m → ℝ),
      (SchwartzMap.seminorm ℂ k l) (translateSchwartz a f) ≤ D * (1 + ‖a‖) ^ k := by
  obtain ⟨Ck, hCk⟩ := f.decay' k l
  obtain ⟨C0, hC0⟩ := f.decay' 0 l
  have hC0' : ∀ y, ‖iteratedFDeriv ℝ l f.toFun y‖ ≤ C0 := by
    intro y
    have hy := hC0 y
    simp [pow_zero] at hy
    linarith
  have hCk_nn : 0 ≤ Ck :=
    le_trans (mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _)) (hCk 0)
  have hC0_nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0' 0)
  set D := 2 ^ (k - 1) * (Ck + C0)
  have hD_nn : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by linarith)
  refine ⟨D, hD_nn, fun a => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ k l _ <| mul_nonneg hD_nn
    (pow_nonneg (by linarith [norm_nonneg a]) k)
  intro x
  have hcoe : (⇑(translateSchwartz a f) : (Fin m → ℝ) → ℂ) = fun z => f (z + a) :=
    funext fun _ => rfl
  rw [hcoe, iteratedFDeriv_comp_add_right]
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by ring_nf
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have h1a : 1 ≤ 1 + ‖a‖ := le_add_of_nonneg_right (norm_nonneg a)
  have hkey : Ck + ‖a‖ ^ k * C0 ≤ (1 + ‖a‖) ^ k * (Ck + C0) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left hCk_nn (one_le_pow₀ h1a)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg a) (le_add_of_nonneg_left zero_le_one) k) hC0_nn
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖
        ≤ (‖x + a‖ + ‖a‖) ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ := by
          gcongr
    _ ≤ (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
          ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ := by
          gcongr
          exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
    _ = 2 ^ (k - 1) * (‖x + a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ +
          ‖a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖) := by ring
    _ ≤ 2 ^ (k - 1) * (Ck + ‖a‖ ^ k * C0) := by
          gcongr
          · exact hCk (x + a)
          · exact hC0' (x + a)
    _ ≤ 2 ^ (k - 1) * ((1 + ‖a‖) ^ k * (Ck + C0)) := by
          gcongr
    _ = D * (1 + ‖a‖) ^ k := by
          simp only [D]
          ring

/-- Reflection of a Schwartz function in the real variables. -/
def reflectSchwartz (f : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : (Fin m → ℝ) ≃ₗᵢ[ℝ] (Fin m → ℝ)).toContinuousLinearEquiv) f

/-- The reflected Schwartz function evaluates as expected. -/
@[simp]
theorem reflectSchwartz_apply (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) : reflectSchwartz f x = f (-x) := by
  simp [reflectSchwartz]

/-- The support of a translated Schwartz function is the pullback of the original
    support under the real translation `x ↦ x + t₀`. -/
theorem mem_support_translateSchwartz_iff (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (x : Fin m → ℝ) :
    x ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ↔
      x + t₀ ∈ Function.support (f : (Fin m → ℝ) → ℂ) := by
  simp [translateSchwartz_apply, Function.mem_support]

/-- Support transport for translated Schwartz functions. This is the exact support
    bookkeeping needed in the mollification step of distributional EOW: if `f` is
    supported in `U`, then `translateSchwartz t₀ f` is supported in the translated
    preimage `{x | x + t₀ ∈ U}`. -/
theorem support_translateSchwartz_subset_preimage (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆
      {x | x + t₀ ∈ U} := by
  intro x hx
  exact hU ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- A convenient open-set version of support transport: if every support point `y`
    of `f` satisfies `y - t₀ ∈ U`, then the support of `translateSchwartz t₀ f`
    is contained in `U`. This is the form needed when a compactly supported mollifier
    is translated inside a fixed real neighborhood. -/
theorem support_translateSchwartz_subset (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : ∀ y ∈ Function.support (f : (Fin m → ℝ) → ℂ), y - t₀ ∈ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U := by
  intro x hx
  simpa using hU (x + t₀) ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- If the support of a Schwartz function is compact and its translate at `t₀`
    is contained in an open set `U`, then the translated support stays inside `U`
    for all nearby centers. This is the local support-stability input needed in
    the mollifier argument for distributional edge-of-the-wedge. -/
theorem exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
    (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hK_compact : IsCompact (Function.support (f : (Fin m → ℝ) → ℂ)))
    (U : Set (Fin m → ℝ)) (hU_open : IsOpen U)
    (hU : Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V,
      Function.support (translateSchwartz t f : (Fin m → ℝ) → ℂ) ⊆ U := by
  let K : Set (Fin m → ℝ) := Function.support (f : (Fin m → ℝ) → ℂ)
  have hbase : ∀ y ∈ K, y - t₀ ∈ U := by
    intro y hy
    have hyt : y - t₀ ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) := by
      rw [mem_support_translateSchwartz_iff]
      simpa
    exact hU hyt
  have hloc :
      ∀ x : K,
        ∃ Vx Wx : Set (Fin m → ℝ),
          Vx ∈ 𝓝 x.1 ∧ Wx ∈ 𝓝 t₀ ∧ IsOpen Vx ∧ x.1 ∈ Vx ∧
            Vx ×ˢ Wx ⊆ {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} := by
    intro x
    have hprod_mem :
        {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} ∈ 𝓝 (x.1, t₀) := by
      exact (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds
        (hU_open.mem_nhds (hbase x.1 x.2))
    rcases mem_nhds_prod_iff.mp hprod_mem with ⟨Vx0, hVx0, Wx, hWx, hsub⟩
    refine ⟨interior Vx0, Wx, ?_, hWx, isOpen_interior, ?_, ?_⟩
    · exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hVx0)
    · exact mem_interior_iff_mem_nhds.mpr hVx0
    · exact Set.Subset.trans (Set.prod_mono interior_subset (Subset.rfl)) hsub
  choose V W hV_nhds hW_nhds hV_open hxV hVW using hloc
  obtain ⟨s, hscover⟩ := hK_compact.elim_finite_subcover (fun x : K => V x)
    (fun x => hV_open x) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hN_nhds_aux : ∀ s : Finset K, (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := by
    classical
    intro s
    exact (biInter_finset_mem s).2 fun x hx => hW_nhds x
  have hN_nhds : (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := hN_nhds_aux s
  let N : Set (Fin m → ℝ) := ⋂ x ∈ s, W x
  refine ⟨N, hN_nhds, ?_⟩
  intro t ht z hz
  have hy : z + t ∈ K := (mem_support_translateSchwartz_iff t f z).mp hz
  have hycover : z + t ∈ ⋃ x ∈ s, V x := hscover hy
  rcases mem_iUnion.mp hycover with ⟨x, hycover⟩
  rcases mem_iUnion.mp hycover with ⟨hxs, hzV⟩
  have htW : t ∈ W x := by
    have ht' : t ∈ N := ht
    simp [N] at ht'
    exact ht' x.1 x.2 hxs
  have hpair : ((z + t), t) ∈ V x ×ˢ W x := ⟨hzV, htW⟩
  have hsub : (z + t) - t ∈ U := hVW x hpair
  simpa using hsub

/-- If a continuous linear functional vanishes on all Schwartz functions
    supported in an open set `U`, then it also vanishes on all nearby translates
    of a compactly supported Schwartz function whose translate at `t₀` is
    contained in `U`. This is the local vanishing step needed for mollified
    boundary traces in the distributional EOW argument. -/
theorem map_translateSchwartz_eq_zero_nhds_of_support_subset
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (U : Set (Fin m → ℝ)) (hT_zero : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Function.support (φ : (Fin m → ℝ) → ℂ) ⊆ U → T φ = 0)
    (t₀ : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (hU_open : IsOpen U)
    (hsub : Function.support (translateSchwartz t₀ ψ : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V, T (translateSchwartz t ψ) = 0 := by
  obtain ⟨V, hV, hVsub⟩ :=
    exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
      t₀ ψ hψ_compact U hU_open hsub
  refine ⟨V, hV, ?_⟩
  intro t ht
  exact hT_zero (translateSchwartz t ψ) (hVsub t ht)

private theorem iteratedFDeriv_sub_schwartz (f g : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (x : Fin m → ℝ) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg : (⇑(f - g) : (Fin m → ℝ) → ℂ) = (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt, hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

/-- Translation by `t • η` is continuous in the Schwartz topology when the
    translated test function has compact support. This is the exact moving-mollifier
    input needed for weak boundary-value uniqueness arguments. -/
theorem tendsto_translateSchwartz_smul_nhds_of_isCompactSupport
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (t₀ : ℝ) :
    Tendsto (fun t : ℝ => translateSchwartz (t • η) ψ) (𝓝 t₀)
      (𝓝 (translateSchwartz (t₀ • η) ψ)) := by
  let K : Set (Fin m → ℝ) := Function.support (ψ : (Fin m → ℝ) → ℂ)
  have hK_closed : IsClosed K := hψ_compact.isClosed
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have ht₀J : t₀ ∈ J := by
    constructor <;> linarith
  let Ktrans : Set (Fin m → ℝ) :=
    (fun p : (Fin m → ℝ) × ℝ => p.1 - p.2 • η) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod isCompact_Icc).image ?_
    exact continuous_fst.sub (continuous_snd.smul continuous_const)
  let q : (Fin m → ℝ) → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := by
    exact continuous_norm.pow k
  obtain ⟨B, hB⟩ := hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (Fin m → ℝ) × ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2 • η)
  have hH_cont : Continuous H := by
    let A : (Fin m → ℝ) × ℝ → Fin m → ℝ := fun p => p.1 + p.2 • η
    have hA : Continuous A := by
      exact continuous_fst.add (continuous_snd.smul continuous_const)
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod isCompact_Icc).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 t₀ := by
    refine Icc_mem_nhds ?_ ?_
    · linarith
    · linarith
  have hball_nhds : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with t ht
  have htJ : t ∈ J := ht.1
  have htdist : dist t t₀ < δ := ht.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_t : (x, t) ∈ Ktrans ×ˢ J := ⟨hx, htJ⟩
    have hpair_t₀ : (x, t₀) ∈ Ktrans ×ˢ J := ⟨hx, ht₀J⟩
    have hpair_dist : dist (x, t) (x, t₀) < δ := by
      simpa [Prod.dist_eq] using htdist
    have hderiv_close :
        ‖H (x, t) - H (x, t₀)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_t _ hpair_t₀ hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by
        simp [q]
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n
            (⇑(translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)) x =
          H (x, t) - H (x, t₀) := by
      have htrans_t :
          iteratedFDeriv ℝ n (⇑(translateSchwartz (t • η) ψ)) x = H (x, t) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t • η) x)
      have htrans_t₀ :
          iteratedFDeriv ℝ n (⇑(translateSchwartz (t₀ • η) ψ)) x = H (x, t₀) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t₀ • η) x)
      rw [iteratedFDeriv_sub_schwartz]
      rw [htrans_t, htrans_t₀]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, t) - H (x, t₀)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K, tsupport, hK_closed.closure_eq] using hy'
    have hx_not_t : x + t • η ∉ K := by
      intro hxt
      exact hx ⟨(x + t • η, t), ⟨hxt, htJ⟩, by
        ext i
        simp⟩
    have hx_not_t₀ : x + t₀ • η ∉ K := by
      intro hxt
      exact hx ⟨(x + t₀ • η, t₀), ⟨hxt, ht₀J⟩, by
        ext i
        simp⟩
    have hzero_t :
        iteratedFDeriv ℝ n (⇑ψ) (x + t • η) = 0 := by
      by_contra hne
      exact hx_not_t (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_t₀ :
        iteratedFDeriv ℝ n (⇑ψ) (x + t₀ • η) = 0 := by
      by_contra hne
      exact hx_not_t₀ (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n
            (⇑(translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz (t • η) ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t • η) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t • η) x)]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz (t₀ • η) ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t₀ • η) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t₀ • η) x)]
      simp [hzero_t, hzero_t₀]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- If `T` is a continuous linear functional on Schwartz space and `ψ` has compact
    support, then the moving-mollifier pairing `t ↦ T(translateSchwartz (t • η) ψ)`
    is continuous. This is the boundary-trace continuity input needed in the
    mollifier proof of distributional edge-of-the-wedge. -/
theorem continuous_apply_translateSchwartz_smul_of_isCompactSupport
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ))) :
    Continuous (fun t : ℝ => T (translateSchwartz (t • η) ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  show Tendsto (fun t : ℝ => T (translateSchwartz (t • η) ψ)) (𝓝 t₀)
    (𝓝 (T (translateSchwartz (t₀ • η) ψ)))
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀)

/-- Sequence-version payoff for the moving-mollifier route: if `Tₙ → 0` pointwise
    on Schwartz space and the translation centers `tₙ → t₀`, then the paired values
    `Tₙ(translateSchwartz (tₙ • η) ψ)` also tend to `0`. This is the exact way the
    Banach-Steinhaus theorem in `SchwartzComplete.lean` enters the distributional
    edge-of-the-wedge proof. -/
theorem tendsto_apply_translateSchwartz_smul_zero_of_tendsto
    {T : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun n => T n f) atTop (nhds 0))
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : ℕ → ℝ} {t₀ : ℝ}
    (hu : Tendsto u atTop (nhds t₀)) :
    Tendsto (fun n => T n (translateSchwartz (u n • η) ψ)) atTop (nhds 0) := by
  apply SchwartzMap.tempered_apply_tendsto_zero_of_tendsto hT
  exact (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀).comp hu

/-- Filter-version moving-mollifier payoff for the zero-limit case.

If `Tᵢ → 0` pointwise on Schwartz space along a countably generated filter `l`,
and the translation centers `uᵢ → t₀`, then the paired values
`Tᵢ(translateSchwartz (uᵢ • η) ψ)` also tend to `0`. This is the form needed
for weak boundary-value limits indexed by `nhdsWithin 0 (Set.Ioi 0)`. -/
theorem tendsto_apply_translateSchwartz_smul_zero_of_tendsto_filter
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {T : α → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun a => T a f) l (nhds 0))
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : α → ℝ} {t₀ : ℝ}
    (hu : Tendsto u l (nhds t₀)) :
    Tendsto (fun a => T a (translateSchwartz (u a • η) ψ)) l (nhds 0) := by
  apply SchwartzMap.tempered_apply_tendsto_zero_of_tendsto_filter hT
  exact (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀).comp hu

/-- Full real-translation continuity in the Schwartz topology for compactly
    supported test functions. This is the version needed for real-direction
    tube convolution, not just the scalar `t • η` specialization. -/
theorem tendsto_translateSchwartz_nhds_of_isCompactSupport
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (t₀ : Fin m → ℝ) :
    Tendsto (fun t : Fin m → ℝ => translateSchwartz t ψ) (𝓝 t₀)
      (𝓝 (translateSchwartz t₀ ψ)) := by
  let K : Set (Fin m → ℝ) := tsupport (ψ : (Fin m → ℝ) → ℂ)
  have hK_closed : IsClosed K := isClosed_tsupport _
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set (Fin m → ℝ) := Metric.closedBall t₀ 1
  have ht₀J : t₀ ∈ J := Metric.mem_closedBall_self (by positivity)
  have hJ_compact : IsCompact J := isCompact_closedBall _ _
  let Ktrans : Set (Fin m → ℝ) :=
    (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.1 - p.2) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod hJ_compact).image ?_
    exact continuous_fst.sub continuous_snd
  let q : (Fin m → ℝ) → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := continuous_norm.pow k
  obtain ⟨B, hB⟩ :=
    hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (Fin m → ℝ) × (Fin m → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2)
  have hH_cont : Continuous H := by
    let A : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ := fun p => p.1 + p.2
    have hA : Continuous A := continuous_fst.add continuous_snd
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod hJ_compact).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 t₀ := Metric.closedBall_mem_nhds _ (by positivity)
  have hball_nhds : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with t ht
  have htJ : t ∈ J := ht.1
  have htdist : dist t t₀ < δ := ht.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n (translateSchwartz t ψ - translateSchwartz t₀ ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_t : (x, t) ∈ Ktrans ×ˢ J := ⟨hx, htJ⟩
    have hpair_t₀ : (x, t₀) ∈ Ktrans ×ˢ J := ⟨hx, ht₀J⟩
    have hpair_dist : dist (x, t) (x, t₀) < δ := by
      simpa [Prod.dist_eq] using htdist
    have hderiv_close : ‖H (x, t) - H (x, t₀)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_t _ hpair_t₀ hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by simp [q]
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ - translateSchwartz t₀ ψ)) x =
          H (x, t) - H (x, t₀) := by
      have htrans_t :
          iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ)) x = H (x, t) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t x)
      have htrans_t₀ :
          iteratedFDeriv ℝ n (⇑(translateSchwartz t₀ ψ)) x = H (x, t₀) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t₀ x)
      rw [iteratedFDeriv_sub_schwartz, htrans_t, htrans_t₀]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, t) - H (x, t₀)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K] using hy'
    have hx_not_t : x + t ∉ K := by
      intro hxt
      exact hx ⟨(x + t, t), ⟨hxt, htJ⟩, by ext i; simp⟩
    have hx_not_t₀ : x + t₀ ∉ K := by
      intro hxt
      exact hx ⟨(x + t₀, t₀), ⟨hxt, ht₀J⟩, by ext i; simp⟩
    have hzero_t : iteratedFDeriv ℝ n (⇑ψ) (x + t) = 0 := by
      by_contra hne
      exact hx_not_t (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_t₀ : iteratedFDeriv ℝ n (⇑ψ) (x + t₀) = 0 := by
      by_contra hne
      exact hx_not_t₀ (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ - translateSchwartz t₀ ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t x)]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz t₀ ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t₀) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t₀ x)]
      simp [hzero_t, hzero_t₀]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- If `T` is a continuous linear functional on Schwartz space and `ψ` has compact
    support, then the full real-translation pairing `t ↦ T(translateSchwartz t ψ)`
    is continuous. -/
theorem continuous_apply_translateSchwartz_of_isCompactSupport
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ)) :
    Continuous (fun t : Fin m → ℝ => T (translateSchwartz t ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀)

/-- Nonzero-limit Banach-Steinhaus payoff for translated compactly supported
    Schwartz tests. This is the exact form needed when a mollified boundary trace
    converges to a continuous boundary functional, not just to `0`. -/
theorem tendsto_apply_translateSchwartz_of_tendsto
    {Tseq : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun n => Tseq n f) atTop (nhds (T f)))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    {u : ℕ → Fin m → ℝ} {t₀ : Fin m → ℝ}
    (hu : Tendsto u atTop (nhds t₀)) :
    Tendsto (fun n => Tseq n (translateSchwartz (u n) ψ)) atTop
      (nhds (T (translateSchwartz t₀ ψ))) := by
  apply SchwartzMap.tempered_apply_tendsto_of_tendsto hT
  exact (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀).comp hu

/-- Filter-version Banach-Steinhaus payoff for translated compactly supported
    Schwartz tests with a nonzero pointwise limit. -/
theorem tendsto_apply_translateSchwartz_of_tendsto_filter
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {Tseq : α → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun a => Tseq a f) l (nhds (T f)))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    {u : α → Fin m → ℝ} {t₀ : Fin m → ℝ}
    (hu : Tendsto u l (nhds t₀)) :
    Tendsto (fun a => Tseq a (translateSchwartz (u a) ψ)) l
      (nhds (T (translateSchwartz t₀ ψ))) := by
  apply SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hT
  exact (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀).comp hu

/-- Integration against a continuous kernel over a closed ball defines a continuous
Schwartz functional.

This is the truncation step for the weak distributional-EOW argument: one first
constructs compact-ball slice functionals, then recovers the full slice
functional as a pointwise limit. -/
theorem exists_closedBall_integral_clm
    {g : (Fin m → ℝ) → ℂ} (R : ℕ)
    (hg_cont : Continuous g) :
    ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        T ψ = ∫ x in Metric.closedBall (0 : Fin m → ℝ) (R : ℝ), g x * ψ x := by
  let s : Set (Fin m → ℝ) := Metric.closedBall (0 : Fin m → ℝ) (R : ℝ)
  have hs_compact : IsCompact s := isCompact_closedBall _ _
  have hs_meas : MeasurableSet s := hs_compact.measurableSet
  obtain ⟨C, hC⟩ := hs_compact.exists_bound_of_continuousOn hg_cont.continuousOn
  let C' : ℝ := max C 0
  have hC'_nonneg : 0 ≤ C' := by
    simp [C']
  have hs_fin : volume s < ⊤ := measure_closedBall_lt_top
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun ψ : SchwartzMap (Fin m → ℝ) ℂ => ∫ x in s, g x * ψ x) ?_ ?_ ?_, ?_⟩
  · intro ψ φ
    simpa [mul_add] using
      (MeasureTheory.integral_add
        (μ := volume.restrict s)
        (f := fun x : Fin m → ℝ => g x * ψ x)
        (g := fun x : Fin m → ℝ => g x * φ x)
        ((hg_cont.mul ψ.continuous).continuousOn.integrableOn_compact hs_compact)
        ((hg_cont.mul φ.continuous).continuousOn.integrableOn_compact hs_compact))
  · intro a ψ
    have hmul :
        (fun x : Fin m → ℝ => g x * (a * ψ x)) =
          fun x => a * (g x * ψ x) := by
      funext x
      ring
    change ∫ x in s, g x * (a * ψ x) = a * ∫ x in s, g x * ψ x
    rw [hmul]
    simpa using
      (MeasureTheory.integral_const_mul a (fun x : Fin m → ℝ => g x * ψ x) : _)
  · refine ⟨{(0, 0)}, C' * (volume s).toReal, ?_, ?_⟩
    · exact mul_nonneg hC'_nonneg ENNReal.toReal_nonneg
    · intro ψ
      calc
        ‖∫ x in s, g x * ψ x‖
            ≤ (C' * SchwartzMap.seminorm ℂ 0 0 ψ) * (volume s).toReal := by
              refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_fin ?_
              intro x hx
              have hgx : ‖g x‖ ≤ C' := le_trans (hC x hx) (le_max_left _ _)
              calc
                ‖g x * ψ x‖ = ‖g x‖ * ‖ψ x‖ := norm_mul _ _
                _ ≤ C' * SchwartzMap.seminorm ℂ 0 0 ψ := by
                  gcongr
                  simpa using (SchwartzMap.le_seminorm ℂ 0 0 ψ x)
        _ = (C' * (volume s).toReal) * SchwartzMap.seminorm ℂ 0 0 ψ := by
              ring
        _ = (C' * (volume s).toReal) * ({(0, 0)} : Finset (ℕ × ℕ)).sup
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
              simp [mul_left_comm, mul_comm]
  · intro ψ
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `g` is continuous and defines an absolutely convergent pairing with every
Schwartz test function, then the map `ψ ↦ ∫ g(x) ψ(x) dx` is a continuous linear
functional on Schwartz space.

The proof is the standard truncation argument: integrate first over compact balls,
obtain continuous linear maps on Schwartz space, and then pass to the pointwise
limit using `continuousLinearMapOfTendsto` on the barrelled Schwartz space. -/
theorem exists_integral_clm_of_continuous
    {g : (Fin m → ℝ) → ℂ} (hg_cont : Continuous g)
    (hg_int : ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      Integrable (fun x : Fin m → ℝ => g x * ψ x)) :
    ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, T ψ = ∫ x, g x * ψ x := by
  let TRc : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    fun R => (exists_closedBall_integral_clm R hg_cont).choose
  let TR : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ := fun R => (TRc R).restrictScalars ℝ
  have hTR :
      ∀ R ψ,
        TR R ψ = ∫ x in Metric.closedBall (0 : Fin m → ℝ) (R : ℝ), g x * ψ x := by
    intro R ψ
    simpa [TR] using (exists_closedBall_integral_clm R hg_cont).choose_spec ψ
  let f : SchwartzMap (Fin m → ℝ) ℂ → ℂ := fun ψ => ∫ x, g x * ψ x
  have hconv : Tendsto (fun R ψ => TR R ψ) atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro ψ
    have hmono : Monotone (fun R : ℕ => Metric.closedBall (0 : Fin m → ℝ) (R : ℝ)) := by
      intro i j hij
      exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
    have hint :
        IntegrableOn (fun x : Fin m → ℝ => g x * ψ x)
          (⋃ R : ℕ, Metric.closedBall (0 : Fin m → ℝ) (R : ℝ)) volume := by
      simpa [Metric.iUnion_closedBall_nat] using hg_int ψ
    convert
      MeasureTheory.tendsto_setIntegral_of_monotone
        (f := fun x : Fin m → ℝ => g x * ψ x)
        (μ := volume)
        (s := fun R : ℕ => Metric.closedBall (0 : Fin m → ℝ) (R : ℝ))
        (hsm := fun R => (isCompact_closedBall (0 : Fin m → ℝ) (R : ℝ)).measurableSet)
        hmono hint
    · exact hTR _ ψ
    · simp [Metric.iUnion_closedBall_nat]
  set_option backward.isDefEq.respectTransparency false in
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ :=
    continuousLinearMapOfTendsto (fun R => (TR R : _ →L[ℝ] ℂ)) hconv
  refine ⟨T, ?_⟩
  intro ψ
  simp [T, f, continuousLinearMapOfTendsto]

/-- Weak boundary-value zero is stable under translating a compactly supported
    Schwartz test function in the real directions.

    This is the direct mollifier input: the boundary-zero hypothesis for `G`
    against a fixed translated test function is exactly the boundary trace of the
    real-direction mollification centered at the corresponding real point. -/
theorem tendsto_boundary_pairing_translate_zero_of_zero_bv
    {C : Set (Fin m → ℝ)} {G : (Fin m → ℂ) → ℂ}
    (h_bv_zero : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Tendsto
        (fun ε : ℝ => ∫ x : Fin m → ℝ,
          G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) (x₀ : Fin m → ℝ) :
    Tendsto
      (fun ε : ℝ => ∫ x : Fin m → ℝ,
        G (fun i => ((x₀ i + x i : ℝ) : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have h := h_bv_zero (translateSchwartz (-x₀) ψ) η hη
  refine Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa [translateSchwartz_apply, add_assoc, add_left_comm, add_comm] using
    (MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (Fin m → ℝ)))
      (fun t : Fin m → ℝ =>
        G (fun i => (t i : ℂ) + ε * (η i : ℂ) * Complex.I) *
          translateSchwartz (-x₀) ψ t)
      x₀).symm

/-- Banach-Steinhaus payoff for mollified boundary traces on a tube domain.

If the boundary slice functionals `T_y` converge pointwise to `0` as `y → 0`
within the cone `C`, then the mollified boundary trace
`w ↦ T_{im w}(translateSchwartz(-re w) ψ)` tends to `0` as `w` approaches the
real edge from inside the tube.

This is the exact `nhdsWithin` boundary-trace theorem needed to feed
`uniqueness_of_boundary_trace_zero` once the weak boundary values are promoted
to a family of continuous linear functionals on Schwartz space. -/
theorem tendsto_mollified_boundary_zero_of_clm_zero
    {C : Set (Fin m → ℝ)}
    {T : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun y => T y f) (nhdsWithin 0 C) (nhds 0))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (x₀ : Fin m → ℝ) :
    Tendsto
      (fun w : Fin m → ℂ =>
        T (fun i => (w i).im) (translateSchwartz (fun i => - (w i).re) ψ))
      (nhdsWithin (realEmbed x₀) (TubeDomain C))
      (nhds 0) := by
  let l := nhdsWithin (realEmbed x₀) (TubeDomain C)
  have him :
      Tendsto (fun w : Fin m → ℂ => fun i => (w i).im) l (nhdsWithin 0 C) := by
    let imMap : (Fin m → ℂ) → (Fin m → ℝ) := fun w i => (w i).im
    have him_cont : Continuous imMap := by
      refine continuous_pi ?_
      intro i
      exact Complex.continuous_im.comp (continuous_apply i)
    have him_maps : MapsTo imMap (TubeDomain C) C := by
      intro w hw
      simpa [imMap] using hw
    simpa [l, imMap, realEmbed] using
      him_cont.continuousAt.continuousWithinAt.tendsto_nhdsWithin him_maps
  have hre :
      Tendsto (fun w : Fin m → ℂ => fun i => - (w i).re) l (nhds (fun i => - x₀ i)) := by
    let reMap : (Fin m → ℂ) → (Fin m → ℝ) := fun w i => - (w i).re
    have hre_cont : Continuous reMap := by
      refine continuous_pi ?_
      intro i
      exact (Complex.continuous_re.comp (continuous_apply i)).neg
    simpa [l, reMap, realEmbed] using
      hre_cont.continuousAt.tendsto.comp
        (tendsto_id'.2 (show l ≤ nhds (realEmbed x₀) by
          exact nhdsWithin_le_nhds))
  have hu :
      Tendsto
        (fun w : Fin m → ℂ => translateSchwartz (fun i => - (w i).re) ψ)
        l
        (nhds (translateSchwartz (fun i => - x₀ i) ψ)) :=
    (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact (fun i => - x₀ i)).comp hre
  have hT_comp :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun w : Fin m → ℂ => T (fun i => (w i).im) f) l (nhds 0) := by
    intro f
    exact (hT f).comp him
  exact SchwartzMap.tempered_apply_tendsto_zero_of_tendsto_filter hT_comp hu

/-! ### Real-direction mollification on the upper half-plane -/

/-- Real-direction mollification of an upper-half-plane holomorphic function is
continuous on the upper half-plane when the Schwartz kernel has compact support.

This is the first analytic step in the weak-BV uniqueness route: continuity comes
for free from compact support, before proving holomorphicity by Morera. -/
theorem continuousOn_realMollify_upperHalfPlane
    {g : ℂ → ℂ}
    (hg : ContinuousOn g EOW.UpperHalfPlane)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : ℝ → ℂ))) :
    ContinuousOn
      (fun z : ℂ => ∫ t : ℝ, g (z + t) * ψ t)
      EOW.UpperHalfPlane := by
  let k : Set ℝ := Function.support (ψ : ℝ → ℂ)
  have hk : IsCompact k := hψ_compact
  let f : ℂ → ℝ → ℂ := fun z t => g (z + t) * ψ t
  have hf : ContinuousOn f.uncurry (EOW.UpperHalfPlane ×ˢ univ) := by
    intro p hp
    rcases hp with ⟨hpU, -⟩
    have hp_shift : p.1 + (p.2 : ℂ) ∈ EOW.UpperHalfPlane := by
      change 0 < (p.1 + (p.2 : ℂ)).im
      simpa using hpU
    have hg_at : ContinuousAt g (p.1 + (p.2 : ℂ)) :=
      (hg (p.1 + (p.2 : ℂ)) hp_shift).continuousAt
        (EOW.upperHalfPlane_isOpen.mem_nhds hp_shift)
    have hleft : ContinuousAt (fun q : ℂ × ℝ => g (q.1 + (q.2 : ℂ))) p :=
      ContinuousAt.comp hg_at <|
        (continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd)).continuousAt
    have hright : ContinuousAt (fun q : ℂ × ℝ => ψ q.2) p :=
      ContinuousAt.comp ψ.continuous.continuousAt continuous_snd.continuousAt
    simpa [f] using (hleft.mul hright).continuousWithinAt
  have hfs : ∀ p, ∀ x, p ∈ EOW.UpperHalfPlane → x ∉ k → f p x = 0 := by
    intro p x _ hx
    simp [k] at hx
    simp [f, hx]
  simpa [f] using
    continuousOn_integral_of_compact_support
      (μ := volume) hk hf hfs

/-- Real-direction mollification of an upper-half-plane holomorphic function is
holomorphic on the upper half-plane when the Schwartz kernel has compact support.

This is the analytic core of the mollifier route to distributional uniqueness:
compact support of `ψ` makes differentiation under the integral sign local and
reduces the needed bound to continuity of `deriv g` on a translated compact set. -/
theorem differentiableOn_realMollify_upperHalfPlane
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g EOW.UpperHalfPlane)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : ℝ → ℂ))) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ t : ℝ, g (z + t) * ψ t)
      EOW.UpperHalfPlane := by
  intro z hz
  obtain ⟨R, hRpos, hRsub⟩ :=
    Metric.isOpen_iff.mp EOW.upperHalfPlane_isOpen z hz
  let r : ℝ := R / 2
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  let s : Set ℂ := Metric.ball z r
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hrpos
  have hs_sub : s ⊆ EOW.UpperHalfPlane := by
    intro x hx
    apply hRsub
    have hxR : dist x z < R := by
      calc
        dist x z < r := hx
        _ < R := by
          dsimp [r]
          linarith
    simpa [Metric.mem_ball] using hxR
  let F : ℂ → ℝ → ℂ := fun w t => g (w + (t : ℂ)) * ψ t
  let F' : ℂ → ℝ → ℂ := fun w t => deriv g (w + (t : ℂ)) * ψ t
  have hψ_cs : HasCompactSupport (ψ : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hψ_compact (by intro t ht; exact ht)
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := by
    filter_upwards [hs] with w hw
    have hwU : w ∈ EOW.UpperHalfPlane := hs_sub hw
    have hshiftU : ∀ t : ℝ, w + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (w + (t : ℂ)).im
      simpa using hwU
    have hcont_shift : Continuous fun t : ℝ => g (w + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgw : ContinuousAt g (w + (t : ℂ)) :=
        ((hg (w + (t : ℂ)) (hshiftU t)).differentiableAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : ℝ => w + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hgw hadd_t rfl
    have hcont_w : Continuous fun t : ℝ => g (w + (t : ℂ)) * ψ t :=
      hcont_shift.mul ψ.continuous
    exact hcont_w.aestronglyMeasurable
  have hF_int : Integrable (F z) volume := by
    have hshiftU : ∀ t : ℝ, z + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (z + (t : ℂ)).im
      simpa using hz
    have hcont_shift : Continuous fun t : ℝ => g (z + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgz : ContinuousAt g (z + (t : ℂ)) :=
        ((hg (z + (t : ℂ)) (hshiftU t)).differentiableAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : ℝ => z + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hgz hadd_t rfl
    have hz_cont : Continuous fun t : ℝ => g (z + (t : ℂ)) * ψ t :=
      hcont_shift.mul ψ.continuous
    have hF_support_subset : Function.support (F z) ⊆ Function.support (ψ : ℝ → ℂ) := by
      intro t ht
      by_contra hnot
      have hψt : ψ t = 0 := by
        simpa [Function.mem_support] using hnot
      have hFt : F z t = 0 := by
        simp [F, hψt]
      exact ht (by simp [hFt])
    have hF_support : HasCompactSupport (F z) :=
      HasCompactSupport.of_support_subset_isCompact hψ_compact hF_support_subset
    exact hz_cont.integrable_of_hasCompactSupport hF_support
  have hg_deriv_cont : ContinuousOn (deriv g) EOW.UpperHalfPlane :=
    (hg.deriv EOW.upperHalfPlane_isOpen).continuousOn
  let K : Set ℂ :=
    (Metric.closedBall z r ×ˢ Function.support (ψ : ℝ → ℂ)).image
      (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ))
  have hK_compact : IsCompact K := by
    exact
      ((isCompact_closedBall z r).prod hψ_compact).image <|
        (continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd))
  have hK_sub : K ⊆ EOW.UpperHalfPlane := by
    intro w hw
    rcases hw with ⟨⟨x, t⟩, hx, rfl⟩
    rcases hx with ⟨hxball, _⟩
    have hxU : x ∈ EOW.UpperHalfPlane := by
      apply hRsub
      have hxR : dist x z < R := by
        calc
          dist x z ≤ r := hxball
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hxR
    change 0 < (x + (t : ℂ)).im
    simpa using hxU
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn (hg_deriv_cont.mono hK_sub)
  let bound : ℝ → ℝ := fun t => C * ‖ψ t‖
  have hF'_meas : AEStronglyMeasurable (F' z) volume := by
    have hz_shift : ∀ t : ℝ, z + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (z + (t : ℂ)).im
      simpa using hz
    have hderiv_shift : Continuous fun t : ℝ => deriv g (z + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hderiv_at : ContinuousAt (deriv g) (z + (t : ℂ)) :=
        (hg_deriv_cont (z + (t : ℂ)) (hz_shift t)).continuousAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hz_shift t))
      have hadd_t : ContinuousAt (fun s : ℝ => z + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hderiv_at hadd_t rfl
    have hz_cont : Continuous fun t : ℝ => deriv g (z + (t : ℂ)) * ψ t :=
      hderiv_shift.mul ψ.continuous
    exact hz_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · simp [F', bound, hψt]
    · have hwK : w + (t : ℂ) ∈ K := by
        refine ⟨⟨w, t⟩, ?_, rfl⟩
        refine ⟨?_, by simp [Function.mem_support, hψt]⟩
        simpa [s, Metric.mem_ball, Metric.mem_closedBall] using le_of_lt hw
      have hderiv_bound : ‖deriv g (w + t)‖ ≤ C := hC _ hwK
      calc
        ‖F' w t‖ = ‖deriv g (w + t)‖ * ‖ψ t‖ := by
          simp [F']
        _ ≤ C * ‖ψ t‖ := by
          exact mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
        _ = bound t := by simp [bound]
  have hbound_cont : Continuous bound := continuous_const.mul ψ.continuous.norm
  have hbound_support_subset : Function.support bound ⊆ Function.support (ψ : ℝ → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hbt : bound t = 0 := by simp [bound, hψt]
    exact ht (by simp [hbt])
  have hbound_compact : HasCompactSupport bound :=
    HasCompactSupport.of_support_subset_isCompact hψ_compact hbound_support_subset
  have hbound_int : Integrable bound volume :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ s, HasDerivAt (F · t) (F' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    have hwU : w ∈ EOW.UpperHalfPlane := hs_sub hw
    have hshiftU : w + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      change 0 < (w + (t : ℂ)).im
      simpa using hwU
    have hderiv_g : HasDerivAt g (deriv g (w + (t : ℂ))) (w + (t : ℂ)) :=
      ((hg (w + (t : ℂ)) hshiftU).differentiableAt
        (EOW.upperHalfPlane_isOpen.mem_nhds hshiftU)).hasDerivAt
    have htrans : HasDerivAt (fun u : ℂ => u + (t : ℂ)) 1 w := by
      simpa using (hasDerivAt_id w).add_const (t : ℂ)
    have hcomp : HasDerivAt (fun u : ℂ => g ((fun v : ℂ => v + (t : ℂ)) u))
        (deriv g (w + (t : ℂ))) w :=
      by simpa [one_mul] using hderiv_g.comp w htrans
    simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hcomp.mul_const (ψ t)
  have hderiv :
      HasDerivAt
        (fun w : ℂ => ∫ t : ℝ, F w t)
        (∫ t : ℝ, F' z t)
        z := by
    exact
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [F] using hderiv.differentiableAt.differentiableWithinAt

/-- Real-direction mollification of a holomorphic function on a tube domain is again
holomorphic on the same tube domain, provided the Schwartz kernel has compact support.

This is the multidimensional analytic step needed for the weak-BV uniqueness route:
real translation does not change the imaginary part, so the mollified function stays
inside the same tube domain, and compact support of the kernel makes differentiation
under the integral sign local. -/
theorem differentiableOn_realMollify_tubeDomain
    {C : Set (Fin m → ℝ)} (hC : IsOpen C)
    {g : (Fin m → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g (TubeDomain C))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ)) :
    DifferentiableOn ℂ
      (fun z : Fin m → ℂ => ∫ t : Fin m → ℝ, g (z + realEmbed t) * ψ t)
      (TubeDomain C) := by
  intro z hz
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp (tubeDomain_isOpen hC) z hz
  let r : ℝ := R / 2
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  let s : Set (Fin m → ℂ) := Metric.ball z r
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hrpos
  have hs_sub : s ⊆ TubeDomain C := by
    intro x hx
    exact hRsub <| by
      have hxR : dist x z < R := by
        calc
          dist x z < r := hx
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hxR
  let F : (Fin m → ℂ) → (Fin m → ℝ) → ℂ := fun w t => g (w + realEmbed t) * ψ t
  let F' : (Fin m → ℂ) → (Fin m → ℝ) → ((Fin m → ℂ) →L[ℂ] ℂ) :=
    fun w t => (ψ t) • fderiv ℂ g (w + realEmbed t)
  have hψ_tsupport_compact : IsCompact (tsupport (ψ : (Fin m → ℝ) → ℂ)) := by
    simpa [HasCompactSupport] using hψ_compact
  have hrealEmbed_cont : Continuous (fun t : Fin m → ℝ => realEmbed t) := by
    refine continuous_pi ?_
    intro i
    exact Complex.continuous_ofReal.comp (continuous_apply i)
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := by
    filter_upwards [hs] with w hw
    have hwU : w ∈ TubeDomain C := hs_sub hw
    have hshiftU : ∀ t : Fin m → ℝ, w + realEmbed t ∈ TubeDomain C := by
      intro t
      simpa [TubeDomain, realEmbed, Complex.add_im, Complex.ofReal_im, Set.mem_setOf_eq]
        using hwU
    have hcont_shift : Continuous fun t : Fin m → ℝ => g (w + realEmbed t) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgw : ContinuousAt g (w + realEmbed t) :=
        ((hg (w + realEmbed t) (hshiftU t)).differentiableAt
          ((tubeDomain_isOpen hC).mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : Fin m → ℝ => w + realEmbed s) t := by
        exact (continuous_const.add hrealEmbed_cont).continuousAt
      exact ContinuousAt.comp_of_eq hgw hadd_t rfl
    have hcont_w : Continuous fun t : Fin m → ℝ => g (w + realEmbed t) * ψ t :=
      hcont_shift.mul ψ.continuous
    exact hcont_w.aestronglyMeasurable
  have hF_int : Integrable (F z) volume := by
    have hshiftU : ∀ t : Fin m → ℝ, z + realEmbed t ∈ TubeDomain C := by
      intro t
      simpa [TubeDomain, realEmbed, Complex.add_im, Complex.ofReal_im, Set.mem_setOf_eq]
        using hz
    have hcont_shift : Continuous fun t : Fin m → ℝ => g (z + realEmbed t) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgz : ContinuousAt g (z + realEmbed t) :=
        ((hg (z + realEmbed t) (hshiftU t)).differentiableAt
          ((tubeDomain_isOpen hC).mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : Fin m → ℝ => z + realEmbed s) t := by
        exact (continuous_const.add hrealEmbed_cont).continuousAt
      exact ContinuousAt.comp_of_eq hgz hadd_t rfl
    have hz_cont : Continuous fun t : Fin m → ℝ => g (z + realEmbed t) * ψ t :=
      hcont_shift.mul ψ.continuous
    have hF_support_subset : Function.support (F z) ⊆ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
      intro t ht
      by_contra hnot
      have hψt : ψ t = 0 := by
        simpa [Function.mem_support] using hnot
      have hFt : F z t = 0 := by
        simp [F, hψt]
      exact ht (by simp [hFt])
    have hF_support : HasCompactSupport (F z) := by
      rw [HasCompactSupport]
      refine hψ_compact.of_isClosed_subset isClosed_closure ?_
      exact closure_minimal (fun t ht => subset_tsupport _ (hF_support_subset ht)) (isClosed_tsupport _)
    exact hz_cont.integrable_of_hasCompactSupport hF_support
  have hg_contDiff : ContDiffOn ℂ 1 g (TubeDomain C) := by
    exact
      (hg.analyticOnNhd_of_finiteDimensional (tubeDomain_isOpen hC)).contDiffOn_of_completeSpace
  have hg_fderiv_cont : ContinuousOn (fderiv ℂ g) (TubeDomain C) :=
    hg_contDiff.continuousOn_fderiv_of_isOpen (tubeDomain_isOpen hC) le_rfl
  let K : Set (Fin m → ℂ) :=
    (Metric.closedBall z r ×ˢ tsupport (ψ : (Fin m → ℝ) → ℂ)).image
      (fun p : (Fin m → ℂ) × (Fin m → ℝ) => p.1 + realEmbed p.2)
  have hK_compact : IsCompact K := by
    exact
      ((isCompact_closedBall z r).prod hψ_tsupport_compact).image <|
        (continuous_fst.add (hrealEmbed_cont.comp continuous_snd))
  have hK_sub : K ⊆ TubeDomain C := by
    intro w hw
    rcases hw with ⟨⟨x, t⟩, hx, rfl⟩
    rcases hx with ⟨hxball, _⟩
    have hxU : x ∈ TubeDomain C := by
      apply hRsub
      have hxR : dist x z < R := by
        calc
          dist x z ≤ r := hxball
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hxR
    simpa [TubeDomain, realEmbed, Complex.add_im, Complex.ofReal_im, Set.mem_setOf_eq]
      using hxU
  obtain ⟨Cbound, hCbound⟩ :=
    hK_compact.exists_bound_of_continuousOn (hg_fderiv_cont.mono hK_sub)
  let bound : (Fin m → ℝ) → ℝ := fun t => Cbound * ‖ψ t‖
  have hF'_meas : AEStronglyMeasurable (F' z) volume := by
    have hz_shift : ∀ t : Fin m → ℝ, z + realEmbed t ∈ TubeDomain C := by
      intro t
      simpa [TubeDomain, realEmbed, Complex.add_im, Complex.ofReal_im, Set.mem_setOf_eq]
        using hz
    have hfderiv_shift : Continuous fun t : Fin m → ℝ => fderiv ℂ g (z + realEmbed t) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hderiv_at : ContinuousAt (fderiv ℂ g) (z + realEmbed t) :=
        (hg_fderiv_cont (z + realEmbed t) (hz_shift t)).continuousAt
          ((tubeDomain_isOpen hC).mem_nhds (hz_shift t))
      have hadd_t : ContinuousAt (fun s : Fin m → ℝ => z + realEmbed s) t := by
        exact (continuous_const.add hrealEmbed_cont).continuousAt
      exact ContinuousAt.comp_of_eq hderiv_at hadd_t rfl
    have hF'cont : Continuous fun t : Fin m → ℝ => F' z t := by
      simpa [F'] using ψ.continuous.smul hfderiv_shift
    exact hF'cont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · have hzeroF' : F' w t = 0 := by
        ext v
        simp [F', hψt]
      have hzeroBound : bound t = 0 := by simp [bound, hψt]
      rw [hzeroF', norm_zero, hzeroBound]
    · have hwK : w + realEmbed t ∈ K := by
        refine ⟨⟨w, t⟩, ?_, rfl⟩
        refine ⟨?_, subset_tsupport _ (by simpa [Function.mem_support] using hψt)⟩
        simpa [s, Metric.mem_ball, Metric.mem_closedBall] using le_of_lt hw
      have hfderiv_bound : ‖fderiv ℂ g (w + realEmbed t)‖ ≤ Cbound := hCbound _ hwK
      calc
        ‖F' w t‖ = ‖ψ t‖ * ‖fderiv ℂ g (w + realEmbed t)‖ := by
          simpa [F'] using norm_smul (ψ t) (fderiv ℂ g (w + realEmbed t))
        _ ≤ ‖ψ t‖ * Cbound := by
          exact mul_le_mul_of_nonneg_left hfderiv_bound (norm_nonneg _)
        _ = bound t := by ring
  have hbound_cont : Continuous bound := continuous_const.mul ψ.continuous.norm
  have hbound_support_subset : Function.support bound ⊆ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hbt : bound t = 0 := by simp [bound, hψt]
    exact ht (by simp [hbt])
  have hbound_compact : HasCompactSupport bound := by
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (fun t ht => subset_tsupport _ (hbound_support_subset ht)) (isClosed_tsupport _)
  have hbound_int : Integrable bound volume :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ s, HasFDerivAt (F · t) (F' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    have hwU : w ∈ TubeDomain C := hs_sub hw
    have hshiftU : w + realEmbed t ∈ TubeDomain C := by
      simpa [TubeDomain, realEmbed, Complex.add_im, Complex.ofReal_im, Set.mem_setOf_eq]
        using hwU
    have hderiv_g : HasFDerivAt g (fderiv ℂ g (w + realEmbed t)) (w + realEmbed t) :=
      ((hg (w + realEmbed t) hshiftU).differentiableAt
        ((tubeDomain_isOpen hC).mem_nhds hshiftU)).hasFDerivAt
    have htrans :
        HasFDerivAt (fun u : Fin m → ℂ => u + realEmbed t)
          (ContinuousLinearMap.id ℂ (Fin m → ℂ)) w := by
      simpa using
        ((ContinuousLinearMap.id ℂ (Fin m → ℂ)).hasFDerivAt).add_const (realEmbed t)
    have hcomp :
        HasFDerivAt (fun u : Fin m → ℂ => g (u + realEmbed t))
          (fderiv ℂ g (w + realEmbed t)) w := by
      simpa using hderiv_g.comp w htrans
    simpa [F, F'] using hcomp.mul_const (ψ t)
  have hderiv :
      HasFDerivAt
        (fun w : Fin m → ℂ => ∫ t : Fin m → ℝ, F w t)
        (∫ t : Fin m → ℝ, F' z t)
        z := by
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [F] using hderiv.differentiableAt.differentiableWithinAt

/-- Approximate-identity convergence for the real-direction mollification of a
holomorphic tube function at an interior point, using normalized bump functions.

This is the final analytic step needed after showing every compactly supported
real mollification vanishes: if the bump support shrinks to `0`, the mollified
values converge back to the original interior value. -/
theorem tendsto_realMollify_normedBump_tubeDomain
    {C : Set (Fin m → ℝ)} {G : (Fin m → ℂ) → ℂ}
    (hC : IsOpen C) (hG_cont : ContinuousOn G (TubeDomain C))
    {z : Fin m → ℂ} (hz : z ∈ TubeDomain C)
    {ι : Type*} {φ : ι → ContDiffBump (0 : Fin m → ℝ)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto
      (fun i => ∫ t : Fin m → ℝ,
        G (z + realEmbed t) * (((φ i).normed volume t : ℝ) : ℂ))
      l
      (nhds (G z)) := by
  let g : (Fin m → ℝ) → ℂ := fun t => G (z - realEmbed t)
  have hg_cont : Continuous g := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hzt : z - realEmbed t ∈ TubeDomain C := by
      simpa [TubeDomain, realEmbed, Complex.sub_im, Complex.ofReal_im, Set.mem_setOf_eq]
        using hz
    have hsub_cont : Continuous fun u : Fin m → ℝ => z - realEmbed u := by
      refine continuous_pi ?_
      intro i
      exact continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i))
    exact ContinuousAt.comp
      ((hG_cont (z - realEmbed t) hzt).continuousAt
        ((tubeDomain_isOpen hC).mem_nhds hzt))
      hsub_cont.continuousAt
  have hconv :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      (φ := φ) (l := l) hφ hg_cont 0
  have hreal0 : realEmbed (0 : Fin m → ℝ) = 0 := by
    ext i
    simp [realEmbed]
  have hg0 : g 0 = G z := by
    simp [g, hreal0]
  have hconv' :
      Tendsto
        (fun i => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0)
        l
        (𝓝 (G z)) := by
    simpa [hg0] using hconv
  have hEq :
      (fun i => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0) =
      (fun i => ∫ t : Fin m → ℝ,
        G (z + realEmbed t) * (((φ i).normed volume t : ℝ) : ℂ)) := by
    funext i
    have hreal_neg : ∀ t : Fin m → ℝ, -realEmbed (-t) = realEmbed t := by
      intro t
      ext j
      simp [realEmbed]
    simp only [MeasureTheory.convolution, g, ContinuousLinearMap.lsmul_apply, sub_eq_add_neg,
      hreal_neg, zero_add]
    congr 1; ext t
    change ↑((φ i).normed volume t) * G (z + realEmbed t) =
      G (z + realEmbed t) * ↑((φ i).normed volume t)
    ring
  simpa [hEq] using hconv'

/-- Local distribution-theory lemma: if a continuous function pairs to zero against every
    compactly supported Schwartz test function supported in an open set `U`, then it vanishes
    pointwise on `U`. -/
theorem eq_zero_on_open_of_compactSupport_schwartz_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)]
    {g : E → ℂ} (hg : Continuous g)
    {U : Set E} (hU : IsOpen U)
    (hint : ∀ f : SchwartzMap E ℂ,
      HasCompactSupport (f : E → ℂ) →
      Function.support (f : E → ℂ) ⊆ U →
      ∫ x : E, g x * f x = 0) :
    ∀ x ∈ U, g x = 0 := by
  intro x hx
  obtain ⟨χ, hχ_tsupport, hχ_compact, hχ_smooth, _, hχx⟩ :=
    exists_contDiff_tsupport_subset (s := U) (x := x) (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  have hχC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (χ y : ℂ)) := by
    rw [contDiff_infty] at hχ_smooth
    rw [contDiff_infty]
    intro n
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hχ_smooth n)
  have hχC_compact : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχ_compact.comp_left Complex.ofReal_zero
  have hχC_support : Function.support (fun y => (χ y : ℂ)) = Function.support χ := by
    ext y
    simp [Function.mem_support]
  have hχC_tsupport : tsupport (fun y => (χ y : ℂ)) = tsupport χ := by
    simp [tsupport, hχC_support]
  let χS : SchwartzMap E ℂ := hχC_compact.toSchwartzMap hχC_smooth
  have hχS_apply : ∀ y, χS y = (χ y : ℂ) :=
    HasCompactSupport.toSchwartzMap_toFun hχC_compact hχC_smooth
  have hχ_temp : (fun y => (χ y : ℂ)).HasTemperateGrowth := by
    simpa [χS, hχS_apply] using χS.hasTemperateGrowth
  have hprod_zero :
      ∀ φ : SchwartzMap E ℂ,
        HasCompactSupport (φ : E → ℂ) →
        ∫ y : E, ((χ y : ℂ) * g y) * φ y = 0 := by
    intro φ hφ_compact
    let φχ : SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun y => (χ y : ℂ)) φ
    have hφχ_compact : HasCompactSupport (φχ : E → ℂ) := by
      rw [HasCompactSupport]
      have htsub :
          tsupport (φχ : E → ℂ) ⊆ tsupport (fun y => (χ y : ℂ)) := by
        intro z hz
        exact (SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ) (g := fun y => (χ y : ℂ))
          (f := φ) hz).2
      exact IsCompact.of_isClosed_subset hχC_compact (isClosed_tsupport _) htsub
    have hφχ_support : Function.support (φχ : E → ℂ) ⊆ U := by
      intro y hy
      have hy_support_prod : y ∈ Function.support (fun z => (χ z : ℂ) * φ z) := by
        simpa [φχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp] using hy
      have hy_supportC : y ∈ Function.support (fun y => (χ y : ℂ)) :=
        Function.support_mul_subset_left (fun y => (χ y : ℂ)) (fun y => φ y) hy_support_prod
      have hy_support : y ∈ Function.support χ := by
        rwa [hχC_support] at hy_supportC
      have hy_tsupport : y ∈ tsupport χ := subset_closure hy_support
      exact hχ_tsupport hy_tsupport
    have hzero := hint φχ hφχ_compact hφχ_support
    simpa [φχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp, mul_assoc, mul_left_comm, mul_comm]
      using hzero
  have hχg_cont : Continuous (fun y : E => (χ y : ℂ) * g y) :=
    (Complex.ofRealCLM.continuous.comp hχ_smooth.continuous).mul hg
  have hχg_locInt : LocallyIntegrableOn (fun y : E => (χ y : ℂ) * g y) univ volume :=
    (hχg_cont.locallyIntegrable).locallyIntegrableOn univ
  have hχg_ae_zero : ∀ᵐ y, ((χ y : ℂ) * g y) = 0 := by
    have hχg_ae_zero' :
        ∀ᵐ y, y ∈ univ → ((χ y : ℂ) * g y) = 0 := by
      refine isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hχg_locInt ?_
      intro ρ hρ_smooth hρ_compact _
      have hρC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (ρ y : ℂ)) := by
        rw [contDiff_infty] at hρ_smooth
        rw [contDiff_infty]
        intro n
        exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hρ_smooth n)
      have hρC_compact : HasCompactSupport (fun y => (ρ y : ℂ)) :=
        hρ_compact.comp_left Complex.ofReal_zero
      let ρS : SchwartzMap E ℂ := hρC_compact.toSchwartzMap hρC_smooth
      have hρS_compact : HasCompactSupport (ρS : E → ℂ) :=
        by simpa [ρS] using hρC_compact
      have hzero := hprod_zero ρS hρS_compact
      have hρS_apply : ∀ y, ρS y = (ρ y : ℂ) :=
        HasCompactSupport.toSchwartzMap_toFun hρC_compact hρC_smooth
      convert hzero using 1
      congr 1; ext y
      show ↑(ρ y) * (↑(χ y) * g y) = (↑(χ y) * g y) * ρS y
      rw [hρS_apply]; ring
    filter_upwards [hχg_ae_zero'] with y hy
    exact hy (by simp)
  have hχg_support_null : volume (Function.support fun y : E => (χ y : ℂ) * g y) = 0 := by
    rw [show Function.support (fun y : E => (χ y : ℂ) * g y) = {y | ((χ y : ℂ) * g y) ≠ 0} by
      ext y; simp [Function.mem_support]]
    rw [← MeasureTheory.ae_iff]
    filter_upwards [hχg_ae_zero] with y hy
    simp [hy]
  have hx_eq : ((χ x : ℂ) * g x) = 0 := by
    by_contra hneq
    have hx_support : x ∈ Function.support fun y : E => (χ y : ℂ) * g y := by
      simpa [Function.mem_support] using hneq
    have hpos :
        0 < volume (Function.support fun y : E => (χ y : ℂ) * g y) :=
      IsOpen.measure_pos volume hχg_cont.isOpen_support ⟨x, hx_support⟩
    exact (ne_of_gt hpos) hχg_support_null
  rw [show (χ x : ℂ) = 1 by simp [hχx]] at hx_eq
  simpa using hx_eq

/-- Local equality version of
    `eq_zero_on_open_of_compactSupport_schwartz_integral_zero`. -/
theorem eqOn_open_of_compactSupport_schwartz_integral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)]
    {g h : E → ℂ} (hg : Continuous g) (hh : Continuous h)
    {U : Set E} (hU : IsOpen U)
    (hint : ∀ f : SchwartzMap E ℂ,
      HasCompactSupport (f : E → ℂ) →
      Function.support (f : E → ℂ) ⊆ U →
      ∫ x : E, g x * f x = ∫ x : E, h x * f x) :
    Set.EqOn g h U := by
  intro x hx
  have hzero :
      ∀ f : SchwartzMap E ℂ,
        HasCompactSupport (f : E → ℂ) →
        Function.support (f : E → ℂ) ⊆ U →
        ∫ y : E, (g y - h y) * f y = 0 := by
    intro f hf_compact hf_support
    have hEq := hint f hf_compact hf_support
    have hg_li : MeasureTheory.LocallyIntegrable g := hg.locallyIntegrable
    have hh_li : MeasureTheory.LocallyIntegrable h := hh.locallyIntegrable
    have hg_int : Integrable (fun y : E => g y * f y) := by
      simpa [mul_comm] using
        hg_li.integrable_smul_right_of_hasCompactSupport f.continuous hf_compact
    have hh_int : Integrable (fun y : E => h y * f y) := by
      simpa [mul_comm] using
        hh_li.integrable_smul_right_of_hasCompactSupport f.continuous hf_compact
    have hfun :
        (fun y : E => (g y - h y) * f y) =
          fun y : E => g y * f y - h y * f y := by
      funext y
      ring
    have hcalc :
        ∫ y : E, (g y - h y) * f y
          = (∫ x : E, g x * f x) - ∫ x : E, h x * f x := by
      rw [hfun, integral_sub hg_int hh_int]
    exact hcalc.trans <| sub_eq_zero.mpr hEq
  have hdiff_cont : Continuous (fun y => g y - h y) := hg.sub hh
  have hpoint :=
    eq_zero_on_open_of_compactSupport_schwartz_integral_zero hdiff_cont hU hzero x hx
  exact sub_eq_zero.mp hpoint

/-- Local-open equality version of
    `eqOn_open_of_compactSupport_schwartz_integral_eq`.

    This is the form needed in distributional EOW arguments: the two traces are only
    known to be continuous on an open real neighborhood `U`, and the pairing equality
    is only available for compactly supported Schwartz tests supported inside `U`. -/
theorem eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)]
    {g h : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (hint : ∀ f : SchwartzMap E ℂ,
      HasCompactSupport (f : E → ℂ) →
      tsupport (f : E → ℂ) ⊆ U →
      ∫ x : E, g x * f x = ∫ x : E, h x * f x) :
    Set.EqOn g h U := by
  classical
  intro x hx
  obtain ⟨χ, hχ_tsupport, hχ_compact, hχ_smooth, _, hχx⟩ :=
    exists_contDiff_tsupport_subset (s := U) (x := x) (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  have hχC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (χ y : ℂ)) := by
    rw [contDiff_infty] at hχ_smooth
    rw [contDiff_infty]
    intro n
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hχ_smooth n)
  have hχC_compact : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχ_compact.comp_left Complex.ofReal_zero
  have hχC_support : Function.support (fun y => (χ y : ℂ)) = Function.support χ := by
    ext y
    simp [Function.mem_support]
  have hχC_tsupport : tsupport (fun y => (χ y : ℂ)) = tsupport χ := by
    simp [tsupport, hχC_support]
  let χS : SchwartzMap E ℂ := hχC_compact.toSchwartzMap hχC_smooth
  have hχS_apply : ∀ y, χS y = (χ y : ℂ) :=
    HasCompactSupport.toSchwartzMap_toFun hχC_compact hχC_smooth
  have hχ_temp : (fun y => (χ y : ℂ)).HasTemperateGrowth := by
    simpa [χS, hχS_apply] using χS.hasTemperateGrowth
  let gχ : E → ℂ := fun y => if y ∈ U then (χ y : ℂ) * g y else 0
  let hχf : E → ℂ := fun y => if y ∈ U then (χ y : ℂ) * h y else 0
  have hgχ_cont : Continuous gχ := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hyU : y ∈ U
    · let ψ : E → ℂ := fun z => (χ z : ℂ) * g z
      have hψ_cont : ContinuousOn ψ U := by
        exact ((Complex.ofRealCLM.continuous.comp hχ_smooth.continuous).continuousOn).mul hg
      have hψ_contAt : ContinuousAt ψ y :=
        (hψ_cont y hyU).continuousAt (hU.mem_nhds hyU)
      have hEq : ψ =ᶠ[𝓝 y] gχ := by
        filter_upwards [hU.mem_nhds hyU] with z hz
        simp [ψ, gχ, hz]
      exact hψ_contAt.congr hEq
    · have hy_not_tsupport : y ∉ tsupport χ := by
        intro hy_tsupport
        exact hyU (hχ_tsupport hy_tsupport)
      have hχ0 : χ =ᶠ[𝓝 y] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hy_not_tsupport
      have hgχ0 : gχ =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hχ0] with z hz
        by_cases hzU : z ∈ U
        · simp [gχ, hzU, hz]
        · simp [gχ, hzU]
      exact hgχ0.continuousAt
  have hhχ_cont : Continuous hχf := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hyU : y ∈ U
    · let ψ : E → ℂ := fun z => (χ z : ℂ) * h z
      have hψ_cont : ContinuousOn ψ U := by
        exact ((Complex.ofRealCLM.continuous.comp hχ_smooth.continuous).continuousOn).mul hh
      have hψ_contAt : ContinuousAt ψ y :=
        (hψ_cont y hyU).continuousAt (hU.mem_nhds hyU)
      have hEq : ψ =ᶠ[𝓝 y] hχf := by
        filter_upwards [hU.mem_nhds hyU] with z hz
        simp [ψ, hχf, hz]
      exact hψ_contAt.congr hEq
    · have hy_not_tsupport : y ∉ tsupport χ := by
        intro hy_tsupport
        exact hyU (hχ_tsupport hy_tsupport)
      have hχ0 : χ =ᶠ[𝓝 y] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hy_not_tsupport
      have hhχ0 : hχf =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hχ0] with z hz
        by_cases hzU : z ∈ U
        · simp [hχf, hzU, hz]
        · simp [hχf, hzU]
      exact hhχ0.continuousAt
  have hglobal :
      ∀ f : SchwartzMap E ℂ,
        HasCompactSupport (f : E → ℂ) →
        tsupport (f : E → ℂ) ⊆ (Set.univ : Set E) →
        ∫ y : E, gχ y * f y = ∫ y : E, hχf y * f y := by
    intro f hf_compact _
    let fχ : SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun y => (χ y : ℂ)) f
    have hfχ_compact : HasCompactSupport (fχ : E → ℂ) := by
      rw [HasCompactSupport]
      have htsub :
          tsupport (fχ : E → ℂ) ⊆ tsupport (fun y => (χ y : ℂ)) := by
        intro z hz
        exact (SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ) (g := fun y => (χ y : ℂ))
          (f := f) hz).2
      exact IsCompact.of_isClosed_subset hχC_compact (isClosed_tsupport _) htsub
    have hfχ_tsupport : tsupport (fχ : E → ℂ) ⊆ U := by
      intro y hy
      have hyχ : y ∈ tsupport (fun z => (χ z : ℂ)) :=
        (SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ) (g := fun z => (χ z : ℂ)) (f := f) hy).2
      exact hχ_tsupport (by simpa [hχC_tsupport] using hyχ)
    have hEqg :
        ∫ y : E, gχ y * f y = ∫ y : E, g y * fχ y := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro y
      by_cases hyU : y ∈ U
      · simp [gχ, fχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp, hyU, mul_assoc,
          mul_comm]
      · have hy_not_tsupport : y ∉ tsupport χ := by
          intro hy_tsupport
          exact hyU (hχ_tsupport hy_tsupport)
        have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy_not_tsupport
        simp [gχ, fχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp, hyU, hχ_zero]
    have hEqh :
        ∫ y : E, hχf y * f y = ∫ y : E, h y * fχ y := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro y
      by_cases hyU : y ∈ U
      · simp [hχf, fχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp, hyU, mul_assoc,
          mul_comm]
      · have hy_not_tsupport : y ∉ tsupport χ := by
          intro hy_tsupport
          exact hyU (hχ_tsupport hy_tsupport)
        have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy_not_tsupport
        simp [hχf, fχ, SchwartzMap.smulLeftCLM_apply_apply hχ_temp, hyU, hχ_zero]
    calc
      ∫ y : E, gχ y * f y = ∫ y : E, g y * fχ y := hEqg
      _ = ∫ y : E, h y * fχ y := hint fχ hfχ_compact hfχ_tsupport
      _ = ∫ y : E, hχf y * f y := hEqh.symm
  have hEq_global :
      Set.EqOn gχ hχf Set.univ :=
    eqOn_open_of_compactSupport_schwartz_integral_eq hgχ_cont hhχ_cont isOpen_univ
      (fun f hf_compact _ => hglobal f hf_compact (by intro y hy; simp))
  have hxEq : gχ x = hχf x := hEq_global (by simp : x ∈ Set.univ)
  simpa [gχ, hχf, hx, hχx] using hxEq

/-! ### Uniqueness from Boundary Zero + ContinuousWithinAt

This is the 1D EOW slicing argument factored out from
`distributional_uniqueness_tube_of_regular`. It requires:
1. G holomorphic on T(C)
2. G = 0 on the real boundary (pointwise)
3. ContinuousWithinAt G (TubeDomain C) (realEmbed x) for all x

No `HasFourierLaplaceReprRegular` is needed. -/

/-- If G is holomorphic on T(C), vanishes on the real boundary, and is
    continuous within the tube at each boundary point, then G vanishes
    identically on T(C). Uses 1D EOW slicing. -/
theorem uniqueness_of_boundary_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0)
    (hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  -- 1D slice: φ(w) = x₀ + w * y₀ maps UHP → T(C)
  let y₀ : Fin m → ℝ := fun i => (z i).im
  let x₀ : Fin m → ℝ := fun i => (z i).re
  have hy₀ : y₀ ∈ C := hz
  let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
  let g : ℂ → ℂ := G ∘ φ
  have hg_real : ∀ t : ℝ, g (t : ℂ) = 0 := by
    intro t
    show G (φ (t : ℂ)) = 0
    have hφ_real : φ (t : ℂ) = realEmbed (fun i => x₀ i + t * y₀ i) := by
      ext i; simp [φ, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
    rw [hφ_real]; exact hG_boundary _
  have hz_eq : φ I = z := by
    ext i; simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
  suffices h : g I = 0 by
    show G z = 0; rw [show G z = g I from by simp [g, hz_eq]]; exact h
  have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
    intro w hw
    show (fun i => (φ w i).im) ∈ C
    have him : (fun i => (φ w i).im) = w.im • y₀ := by
      ext i; simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [him]; exact hcone w.im hw y₀ hy₀
  have hφ_cont : Continuous φ :=
    continuous_pi fun i =>
      (continuous_const.add (continuous_id.mul continuous_const))
  have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
    show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
    exact hG_diff.comp (fun w _ => by
      apply DifferentiableAt.differentiableWithinAt
      exact differentiableAt_pi.mpr fun i =>
        (differentiableAt_const _).add
          (differentiableAt_id.mul (differentiableAt_const _)))
      (fun w hw => hφ_UHP w hw)
  have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
    intro t; ext i; simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
  have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (g ↑x₁)) := by
    intro x₁ _ _
    show ContinuousWithinAt (G ∘ φ) EOW.UpperHalfPlane ↑x₁
    have h := hG_cont (fun i => x₀ i + x₁ * y₀ i)
    rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
      (hφ_real_embed x₁).symm] at h
    exact h.comp hφ_cont.continuousAt.continuousWithinAt (fun w hw => hφ_UHP w hw)
  have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g ↑x₁)) := by
    intro x₁ _ _
    rw [hg_real x₁]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
    have : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw])
    rw [this]; exact (hg_real w.re).symm
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
      g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      (fun x₁ _ _ => by show g ↑x₁ = 0; exact hg_real x₁)
      hbv_cont
  have hI_in_U : I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
  have h_neg_I_in_U : -I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have hU_conn : IsConnected U :=
      ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
    have h_neg_I_LHP : (-I).im < 0 := by simp [Complex.neg_im, Complex.I_im]
    have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
        nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
          ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
      filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
      simp [hF_minus w ⟨hwU, hwLHP⟩]
    exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
  have hI_UHP : I.im > 0 := by simp [Complex.I_im]
  rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
  exact hF_zero_on_U I hI_in_U

/-- If a holomorphic function on a tube domain has zero boundary trace in the
    distributional/limit sense, then it vanishes identically on the tube.

    Unlike `uniqueness_of_boundary_zero`, this theorem does not assume the
    ambient total function is already defined correctly on the real boundary.
    It is the theorem shape needed for mollified weak boundary-value arguments. -/
theorem uniqueness_of_boundary_trace_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_trace : ∀ x : Fin m → ℝ,
      Filter.Tendsto G (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds 0)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  let y₀ : Fin m → ℝ := fun i => (z i).im
  let x₀ : Fin m → ℝ := fun i => (z i).re
  have hy₀ : y₀ ∈ C := hz
  let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
  let g : ℂ → ℂ := G ∘ φ
  let gPlus : ℂ → ℂ := fun w => if w.im = 0 then 0 else g w
  have hz_eq : φ I = z := by
    ext i
    simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
  suffices h : gPlus I = 0 by
    have hI : gPlus I = g I := by simp [gPlus]
    show G z = 0
    rw [show G z = g I from by simp [g, hz_eq], ← hI]
    exact h
  have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
    intro w hw
    show (fun i => (φ w i).im) ∈ C
    have him : (fun i => (φ w i).im) = w.im • y₀ := by
      ext i
      simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [him]
    exact hcone w.im hw y₀ hy₀
  have hφ_cont : Continuous φ :=
    continuous_pi fun i =>
      (continuous_const.add (continuous_id.mul continuous_const))
  have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
    show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
    exact hG_diff.comp
      (fun w _ => by
        apply DifferentiableAt.differentiableWithinAt
        exact differentiableAt_pi.mpr fun i =>
          (differentiableAt_const _).add
            (differentiableAt_id.mul (differentiableAt_const _)))
      (fun w hw => hφ_UHP w hw)
  have hgPlus_diff : DifferentiableOn ℂ gPlus EOW.UpperHalfPlane := by
    intro w hw
    refine (hg_diff w hw).congr ?_ ?_
    · intro z hz
      have hz' : z.im > 0 := by
        simpa [EOW.UpperHalfPlane] using hz
      simp [gPlus, ne_of_gt hz']
    · have hw' : w.im > 0 := by
        simpa [EOW.UpperHalfPlane] using hw
      simp [gPlus, ne_of_gt hw']
  have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
    intro t
    ext i
    simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
  have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto gPlus (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (gPlus ↑x₁)) := by
    intro x₁ _ _
    have htrace := hG_trace (fun i => x₀ i + x₁ * y₀ i)
    rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
      (hφ_real_embed x₁).symm] at htrace
    have hφ_tendsto :
        Tendsto φ (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane)
          (nhdsWithin (φ ↑x₁) (TubeDomain C)) :=
      (hφ_cont.continuousAt.continuousWithinAt.tendsto_nhdsWithin
        (fun w hw => hφ_UHP w hw))
    have hcomp := htrace.comp hφ_tendsto
    have hval : gPlus ↑x₁ = 0 := by simp [gPlus]
    rw [hval]
    refine Tendsto.congr' ?_ hcomp
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w.im > 0 := by
      simpa [EOW.UpperHalfPlane] using hw
    simp [gPlus, g, ne_of_gt hw']
  have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto gPlus (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
        (nhds (gPlus ↑x₁)) := by
    intro x₁ _ _
    have hval : gPlus ↑x₁ = 0 := by simp [gPlus]
    rw [hval]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
    simp [gPlus, hw]
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
      gPlus 0
      hgPlus_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      (fun x₁ _ _ => by simp [gPlus])
      hbv_cont
  have hI_in_U : I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
  have h_neg_I_in_U : -I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have hU_conn : IsConnected U :=
      ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
    have h_neg_I_LHP : (-I).im < 0 := by
      simp [Complex.neg_im, Complex.I_im]
    have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
        nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
          ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
      filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
      simp [hF_minus w ⟨hwU, hwLHP⟩]
    exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
  have hI_UHP : I.im > 0 := by simp [Complex.I_im]
  rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
  exact hF_zero_on_U I hI_in_U

/-- A local 1D uniqueness theorem for holomorphic functions on the upper
    half-plane with zero continuous boundary values on an interval.

    This is the exact local endpoint needed in mollifier-based distributional
    edge-of-the-wedge arguments: once the mollified boundary trace vanishes on
    an interval `(a,b)`, the holomorphic function vanishes on the canonical ball
    produced by `edge_of_the_wedge_1d`. -/
theorem uniqueness_of_boundary_zero_on_interval (a b : ℝ) (hab : a < b)
    {g : ℂ → ℂ}
    (hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane)
    (hg_boundary : ∀ x : ℝ, a < x → x < b → g (x : ℂ) = 0)
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto g (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (g x)))
    (hbv_cont : ∀ x₀ : ℝ, a < x₀ → x₀ < b →
      Filter.Tendsto g (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g x₀))) :
    ∀ z ∈ Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2), z.im > 0 → g z = 0 := by
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d a b hab g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      hg_boundary
      hbv_cont
  let mid : ℂ := (((a + b) / 2 : ℝ) : ℂ)
  let rad : ℝ := (b - a) / 2
  have hrad : 0 < rad := by
    dsimp [rad]
    linarith
  let w0 : ℂ := mid - ((rad / 2 : ℝ) : ℂ) * Complex.I
  have hw0_ball : w0 ∈ Metric.ball mid rad := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [w0, mid, rad]
    have hnorm : ‖(((b - a) / 4 : ℝ) : ℂ) * Complex.I‖ = (b - a) / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      have : 0 ≤ (b - a) / 4 := by linarith
      simp [abs_of_nonneg this]
    have hsub : w0 - mid = -((((b - a) / 4 : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp [w0, mid, rad]
      · simp [w0, mid, rad]
        ring_nf
    rw [hsub, norm_neg, hnorm]
    linarith
  have hw0_U : w0 ∈ U := hU_ball hw0_ball
  have hw0_LHP : w0 ∈ EOW.LowerHalfPlane := by
    change w0.im < 0
    simp [w0, mid, rad]
    linarith
  have hU_conn : IsConnected U := by
    refine ⟨?_, hU_conv.isPreconnected⟩
    exact ⟨w0, hw0_U⟩
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have h_freq : ∃ᶠ w in nhdsWithin w0 ({w0}ᶜ), F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin w0 ({w0}ᶜ) := by
        exact nhdsWithin_le_nhds
          ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hw0_U, hw0_LHP⟩)
      filter_upwards [hmem] with w hw
      exact hF_minus w hw
    intro w hw
    exact (identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) w0 hw0_U h_freq) hw
  intro z hz hzUHP
  have hzU : z ∈ U := hU_ball hz
  calc
    g z = F z := (hF_plus z ⟨hzU, hzUHP⟩).symm
    _ = 0 := hF_zero_on_U z hzU

/-- Tube-domain uniqueness from weak boundary-value zero along every cone ray.

For each compactly supported real mollifier `ψ`, the real-direction convolution
of `G` is holomorphic on the tube. Restricting that mollified function to the
one-dimensional slice `ζ ↦ re z + ζ • im z`, the weak boundary-value-zero
hypothesis shows that the boundary trace vanishes on the whole real axis. The
one-dimensional interval uniqueness theorem then forces the mollified function
to vanish at `ζ = I`, and an approximate-identity argument recovers `G z = 0`.

This is the honest weak theorem underlying `distributional_uniqueness_forwardTube`:
no boundary continuity or regularity package is assumed a priori, but the
boundary pairings are required to be actual integrable slices rather than
vacuous Bochner integrals. -/
theorem distributional_uniqueness_tube_of_zero_bv
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_int : ∀ y ∈ C, ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      Integrable (fun x : Fin m → ℝ =>
        G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x))
    (h_bv_zero : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Tendsto
        (fun ε : ℝ => ∫ x : Fin m → ℝ,
          G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  let x₀ : Fin m → ℝ := fun i => (z i).re
  let y₀ : Fin m → ℝ := fun i => (z i).im
  have hy₀ : y₀ ∈ C := hz
  let φ : ℕ → ContDiffBump (0 : Fin m → ℝ) := fun n =>
    { rIn := (2 * (n + 1 : ℝ))⁻¹
      rOut := ((n + 1 : ℝ))⁻¹
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
        field_simp [hn.ne']
        ring_nf
        linarith }
  have hφ_tendsto : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have hplus : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa [φ] using
      tendsto_inv_atTop_zero.comp hplus
  let ψ : ℕ → SchwartzMap (Fin m → ℝ) ℂ := fun n =>
    let ψR : (Fin m → ℝ) → ℂ := fun x => (((φ n).normed volume x : ℝ) : ℂ)
    let hψR_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ψR := by
      simpa [ψR] using
        (Complex.ofRealCLM.contDiff.comp ((φ n).contDiff_normed (μ := volume)))
    let hψR_compact : HasCompactSupport ψR := by
      exact ((φ n).hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero
    hψR_compact.toSchwartzMap hψR_smooth
  have hψ_apply : ∀ n x, ψ n x = (((φ n).normed volume x : ℝ) : ℂ) := by
    intro n x
    simp [ψ]
  have hψ_compact :
      ∀ n, HasCompactSupport ((ψ n : (Fin m → ℝ) → ℂ)) := by
    intro n
    simpa [ψ] using (((φ n).hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero)
  have hmoll_zero :
      ∀ n, ∫ t : Fin m → ℝ, G (z + realEmbed t) * ψ n t = 0 := by
    intro n
    let M : (Fin m → ℂ) → ℂ := fun w => ∫ t : Fin m → ℝ, G (w + realEmbed t) * ψ n t
    have hM_diff : DifferentiableOn ℂ M (TubeDomain C) :=
      differentiableOn_realMollify_tubeDomain hC hG_diff (ψ n) (hψ_compact n)
    let line : ℂ → (Fin m → ℂ) := fun w i => (x₀ i : ℂ) + w * (y₀ i : ℂ)
    let g : ℂ → ℂ := M ∘ line
    let gPlus : ℂ → ℂ := fun w => if w.im = 0 then 0 else g w
    have hExistsCLM :
        ∀ ε : ℝ, 0 < ε →
          ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
            ∀ ψ' : SchwartzMap (Fin m → ℝ) ℂ,
              T ψ' =
                ∫ x : Fin m → ℝ,
                  G (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) * ψ' x := by
      intro ε hε
      let gε : (Fin m → ℝ) → ℂ := fun x =>
        G (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I)
      have hgε_cont : Continuous gε := by
        refine continuous_iff_continuousAt.2 ?_
        intro x
        have hεy : ε • y₀ ∈ C := hcone ε hε y₀ hy₀
        have hxTube :
            (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) ∈ TubeDomain C := by
          change
            (fun i => ((x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I).im) ∈ C
          simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
            mul_assoc, mul_comm, mul_left_comm] using hεy
        have hcontG : ContinuousAt G (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) :=
          (hG_diff.continuousOn
            (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) hxTube).continuousAt
              ((tubeDomain_isOpen hC).mem_nhds hxTube)
        have harg_cont :
            Continuous (fun u : Fin m → ℝ =>
              fun i => (u i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) := by
          refine continuous_pi ?_
          intro i
          exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
        exact hcontG.comp harg_cont.continuousAt
      have hgε_int :
          ∀ ψ' : SchwartzMap (Fin m → ℝ) ℂ,
            Integrable (fun x : Fin m → ℝ =>
              G (fun i => (x i : ℂ) + ε * (y₀ i : ℂ) * Complex.I) * ψ' x) := by
        intro ψ'
        have hεy : ε • y₀ ∈ C := hcone ε hε y₀ hy₀
        simpa using hG_int (ε • y₀) hεy ψ'
      exact exists_integral_clm_of_continuous hgε_cont hgε_int
    have hline_UHP : ∀ w : ℂ, w.im > 0 → line w ∈ TubeDomain C := by
      intro w hw
      change (fun i => (line w i).im) ∈ C
      have him : (fun i => (line w i).im) = w.im • y₀ := by
        ext i
        simp [line, x₀, y₀, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [him]
      exact hcone w.im hw y₀ hy₀
    have hline_cont : Continuous line :=
      continuous_pi fun i =>
        (continuous_const.add (continuous_id.mul continuous_const))
    have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
      show DifferentiableOn ℂ (M ∘ line) EOW.UpperHalfPlane
      exact hM_diff.comp
        (fun w _ => by
          apply DifferentiableAt.differentiableWithinAt
          exact differentiableAt_pi.mpr fun i =>
            (differentiableAt_const _).add
              (differentiableAt_id.mul (differentiableAt_const _)))
        (fun w hw => hline_UHP w hw)
    have hgPlus_diff : DifferentiableOn ℂ gPlus EOW.UpperHalfPlane := by
      intro w hw
      refine (hg_diff w hw).congr ?_ ?_
      · intro z hz
        have hz' : z.im > 0 := by simpa [EOW.UpperHalfPlane] using hz
        simp [gPlus, ne_of_gt hz']
      · have hw' : w.im > 0 := by simpa [EOW.UpperHalfPlane] using hw
        simp [gPlus, ne_of_gt hw']
    have hline_real : ∀ a : ℝ, line (a : ℂ) = realEmbed (x₀ + a • y₀) := by
      intro a
      ext i
      simp [line, x₀, y₀, realEmbed]
    have htrace_plus :
        ∀ a : ℝ, -3 < a → a < 3 →
          Tendsto gPlus (nhdsWithin (a : ℂ) EOW.UpperHalfPlane) (nhds (gPlus a)) := by
      intro a _ _
      have hga : gPlus (a : ℂ) = 0 := by simp [gPlus]
      rw [hga]
      let l := nhdsWithin (a : ℂ) EOW.UpperHalfPlane
      let Tslice : ℂ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ := fun w =>
        if hw : 0 < w.im then
          (hExistsCLM w.im hw).choose
        else 0
      have him :
          Tendsto (fun w : ℂ => w.im) l (nhdsWithin 0 (Set.Ioi 0)) := by
        let imMap : ℂ → ℝ := fun w => w.im
        have him_cont : Continuous imMap := Complex.continuous_im
        have him_maps : MapsTo imMap EOW.UpperHalfPlane (Set.Ioi 0) := by
          intro w hw
          simpa [imMap, EOW.UpperHalfPlane] using hw
        simpa [l, imMap] using
          him_cont.continuousAt.continuousWithinAt.tendsto_nhdsWithin him_maps
      have hre :
          Tendsto (fun w : ℂ => - (x₀ + (w.re) • y₀)) l (nhds (- (x₀ + a • y₀))) := by
        have hcont :
            Continuous (fun w : ℂ => - (x₀ + (w.re) • y₀)) := by
          refine continuous_pi ?_
          intro i
          exact (continuous_const.add (Complex.continuous_re.mul continuous_const)).neg
        simpa [l] using
          hcont.continuousAt.tendsto.comp
            (tendsto_id'.2 (show l ≤ nhds (a : ℂ) by exact nhdsWithin_le_nhds))
      have hT_comp :
          ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
            Tendsto (fun w : ℂ => Tslice w f) l (nhds 0) := by
        intro f
        have hray := h_bv_zero f y₀ hy₀
        refine Tendsto.congr' ?_ (hray.comp him)
        filter_upwards [self_mem_nhdsWithin] with w hw
        have hw' : 0 < w.im := by simpa [EOW.UpperHalfPlane] using hw
        simpa [Tslice, hw'] using ((hExistsCLM w.im hw').choose_spec f).symm
      have hzero :=
        SchwartzMap.tempered_apply_tendsto_zero_of_tendsto_filter hT_comp
          ((tendsto_translateSchwartz_nhds_of_isCompactSupport
              (ψ n) (hψ_compact n) (- (x₀ + a • y₀))).comp hre)
      refine Tendsto.congr' ?_ hzero
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : 0 < w.im := by simpa [EOW.UpperHalfPlane] using hw
      have hgplusw : gPlus w = g w := by
        simpa [gPlus] using (if_neg (ne_of_gt hw') : ite (w.im = 0) 0 (g w) = g w)
      have hswap :
          ∫ t : Fin m → ℝ, G (line w + realEmbed t) * ψ n t =
            ∫ t : Fin m → ℝ, G (realEmbed t + line w) * ψ n t := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with t
        have hpt : line w + realEmbed t = realEmbed t + line w := by
          ext i
          simp [line, realEmbed, add_comm]
        rw [hpt]
      have hshift :
          g w =
            ∫ t : Fin m → ℝ,
              G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                (ψ n) (t + (-(x₀ + (w.re) • y₀))) := by
        have hpre :
            ∫ t : Fin m → ℝ, G (realEmbed t + line w) * ψ n t =
              ∫ x : Fin m → ℝ,
                (G fun i => ↑((x + (x₀ + w.re • y₀)) i) + ↑w.im * ↑(y₀ i) * I) *
                  (ψ n) (x + (x₀ + w.re • y₀) + -(x₀ + w.re • y₀)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          have hwdecomp : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
            simp [Complex.re_add_im]
          have harg :
              realEmbed x + line w =
                fun i => ↑((x + (x₀ + w.re • y₀)) i) + ↑w.im * ↑(y₀ i) * I := by
            ext i
            rw [hwdecomp]
            simp [line, realEmbed, add_assoc, add_left_comm, add_comm, mul_add, mul_left_comm,
              mul_comm]
          have hcancelx :
              x + (x₀ + w.re • y₀) + -(x₀ + w.re • y₀) = x := by
            ext i
            simp [add_assoc]
          rw [harg, hcancelx]
        have hshift_raw0 :=
          (MeasureTheory.integral_add_right_eq_self
            (μ := (volume : Measure (Fin m → ℝ)))
            (fun t : Fin m → ℝ =>
              G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                (ψ n) (t + (-(x₀ + (w.re) • y₀))))
            (x₀ + (w.re) • y₀))
        have hshift_raw :
            ∫ t : Fin m → ℝ, G (realEmbed t + line w) * ψ n t =
              ∫ t : Fin m → ℝ,
                G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                  (ψ n) (t + (-(x₀ + (w.re) • y₀))) := by
          exact hpre.trans hshift_raw0
        calc
          g w = ∫ t : Fin m → ℝ, G (line w + realEmbed t) * ψ n t := by simp [g, M]
          _ = ∫ t : Fin m → ℝ, G (realEmbed t + line w) * ψ n t := hswap
          _ = ∫ t : Fin m → ℝ,
                G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                  (ψ n) (t + (-(x₀ + (w.re) • y₀))) := hshift_raw
      have htarget :
          ∫ t : Fin m → ℝ,
            G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
              translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n) t =
            ∫ t : Fin m → ℝ,
              G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                (ψ n) (t + (-(x₀ + (w.re) • y₀))) := by
        simp [translateSchwartz_apply]
      have hspec :
          ∫ t : Fin m → ℝ,
            G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
              translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n) t =
            Tslice w (translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n)) := by
        simpa [Tslice, hw'] using
          ((hExistsCLM w.im hw').choose_spec
            (translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n))).symm
      have harg_eq :
          (((fun t => translateSchwartz t (ψ n)) ∘ fun w => -(x₀ + w.re • y₀)) w) =
            translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n) := rfl
      calc
        (Tslice w) (((fun t => translateSchwartz t (ψ n)) ∘ fun w => -(x₀ + w.re • y₀)) w)
            = (Tslice w) (translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n)) := by
                rfl
        _ = ∫ t : Fin m → ℝ,
              G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                translateSchwartz (- (x₀ + (w.re) • y₀)) (ψ n) t := by
                  symm
                  exact hspec
        _ = ∫ t : Fin m → ℝ,
              G (fun i => (t i : ℂ) + (w.im : ℂ) * (y₀ i : ℂ) * Complex.I) *
                (ψ n) (t + (-(x₀ + (w.re) • y₀))) := by
                  exact htarget
        _ = g w := by symm; exact hshift
        _ = gPlus w := by symm; exact hgplusw
    have htrace_boundary :
        ∀ a : ℝ, -3 < a → a < 3 →
          Tendsto gPlus (nhdsWithin (a : ℂ) {c : ℂ | c.im = 0}) (nhds (gPlus a)) := by
      intro a _ _
      have hga : gPlus (a : ℂ) = 0 := by simp [gPlus]
      rw [hga]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp [gPlus, hw]
    have hboundary_zero : ∀ a : ℝ, -3 < a → a < 3 → gPlus (a : ℂ) = 0 := by
      intro a _ _
      simp [gPlus]
    have hIinball : Complex.I ∈ Metric.ball (((( -3 : ℝ) + 3) / 2 : ℝ) : ℂ) ((3 - (-3)) / 2) := by
      norm_num [Metric.mem_ball]
    have hIim : 0 < Complex.I.im := by
      simp
    have hzero := uniqueness_of_boundary_zero_on_interval (-3) 3 (by norm_num)
      hgPlus_diff hboundary_zero htrace_plus htrace_boundary
      Complex.I hIinball hIim
    have hline_I : line Complex.I = z := by
      ext i
      calc
        line Complex.I i
            = (x₀ i : ℂ) + Complex.I * (y₀ i : ℂ) := by simp [line]
        _ = ((z i).re : ℂ) + Complex.I * ((z i).im : ℂ) := by simp [x₀, y₀]
        _ = z i := by simpa [mul_comm] using (Complex.re_add_im (z i))
    have hgI : gPlus Complex.I = g Complex.I := by
      norm_num [gPlus]
    rw [hgI] at hzero
    simpa [g, M, hline_I] using hzero
  have hconv :
      Tendsto (fun n => ∫ t : Fin m → ℝ, G (z + realEmbed t) * ψ n t) atTop (𝓝 (G z)) := by
    simpa [hψ_apply] using
      (tendsto_realMollify_normedBump_tubeDomain hC hG_diff.continuousOn hz
        (φ := φ) (l := atTop) hφ_tendsto)
  have hzero_seq :
      Tendsto (fun n => ∫ t : Fin m → ℝ, G (z + realEmbed t) * ψ n t) atTop (𝓝 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.Eventually.of_forall hmoll_zero] with n hn
    simpa using hn.symm
  exact tendsto_nhds_unique hconv hzero_seq

/-- Tube-domain uniqueness from an explicit family of continuous boundary-value
    functionals vanishing at the edge.

    This is the theorem shape actually produced by the mollifier route for
    distributional edge-of-the-wedge: one first constructs continuous linear
    functionals `T y` describing the boundary slices of `G`, proves `T y → 0`
    as `y → 0` within the cone, and then concludes `G = 0` on the whole tube. -/
theorem distributional_uniqueness_tube_of_zero_bv_of_clm
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (T : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (hT_eval : ∀ y ∈ C, ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      T y ψ =
        ∫ x : Fin m → ℝ,
          G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x)
    (hT_zero : ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun y => T y ψ) (nhdsWithin 0 C) (nhds 0)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  have hmoll_zero :
      ∀ (ψ : SchwartzMap (Fin m → ℝ) ℂ)
        (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ)),
        ∀ z ∈ TubeDomain C,
          (∫ t : Fin m → ℝ, G (z + realEmbed t) * ψ t) = 0 := by
    intro ψ hψ_compact z hz
    let M : (Fin m → ℂ) → ℂ := fun w => ∫ t : Fin m → ℝ, G (w + realEmbed t) * ψ t
    have hM_diff : DifferentiableOn ℂ M (TubeDomain C) :=
      differentiableOn_realMollify_tubeDomain hC hG_diff ψ hψ_compact
    have hM_trace :
        ∀ x : Fin m → ℝ,
          Tendsto M (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds 0) := by
      intro x
      have hzero :=
        tendsto_mollified_boundary_zero_of_clm_zero hT_zero ψ hψ_compact x
      refine Tendsto.congr' ?_ hzero
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hwC : (fun i => (w i).im) ∈ C := hw
      have hcancel : (fun i => (w i).re) + (fun i => - (w i).re) = 0 := by
        ext i
        simp
      rw [hT_eval _ hwC]
      have hshift :
          ∫ x : Fin m → ℝ,
            G (fun i => (w i).re + ((x i : ℂ) + (w i).im * Complex.I)) * ψ x =
          ∫ x : Fin m → ℝ,
            G (fun i => (x i : ℂ) + (w i).im * Complex.I) *
              ψ (x + fun i => - (w i).re) := by
        simpa [hcancel, realEmbed, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
          mul_assoc]
          using
            (MeasureTheory.integral_add_right_eq_self
              (μ := (volume : Measure (Fin m → ℝ)))
              (fun x : Fin m → ℝ =>
                G (fun i => (x i : ℂ) + (w i).im * Complex.I) *
                  ψ (x + fun i => - (w i).re))
              (fun i => (w i).re))
      have htarget :
          ∫ x : Fin m → ℝ,
            G (fun i => (x i : ℂ) + (w i).im * Complex.I) *
              translateSchwartz (fun i => - (w i).re) ψ x =
          ∫ x : Fin m → ℝ,
            G (fun i => (x i : ℂ) + (w i).im * Complex.I) *
              ψ (x + fun i => - (w i).re) := by
        simp [translateSchwartz_apply]
      rw [htarget, ← hshift]
      change
        ∫ x : Fin m → ℝ, (G fun i => ↑(w i).re + (↑(x i) + ↑(w i).im * Complex.I)) * ψ x =
          ∫ t : Fin m → ℝ, G (w + realEmbed t) * ψ t
      congr 1 with t
      have hpoint :
          G (fun i => ↑(w i).re + (↑(t i) + ↑(w i).im * Complex.I)) = G (w + realEmbed t) := by
        congr 1
        ext i
        calc
          ((w i).re : ℂ) + ((t i : ℂ) + (w i).im * Complex.I)
              = (((w i).re : ℂ) + (w i).im * Complex.I) + (t i : ℂ) := by abel
          _ = w i + (t i : ℂ) := by rw [Complex.re_add_im]
      rw [hpoint]
    exact uniqueness_of_boundary_trace_zero hC hconv hne hcone hM_diff hM_trace z hz
  intro z hz
  let y : Fin m → ℝ := fun i => (z i).im
  have hy : y ∈ C := hz
  let g : (Fin m → ℝ) → ℂ := fun x =>
    G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
  have hg_cont : Continuous g := by
    refine continuous_iff_continuousAt.2 ?_
    intro x
    have hxC : (fun i => ((x i : ℂ) + (y i : ℂ) * Complex.I).im) ∈ C := by
      simpa [y, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
        using hy
    have hG_cont : ContinuousAt G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) :=
      ((hG_diff _ hxC).differentiableAt
        ((tubeDomain_isOpen hC).mem_nhds hxC)).continuousAt
    have hmap_cont :
        ContinuousAt (fun x : Fin m → ℝ => fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) x := by
      exact
        (continuous_pi fun i =>
          (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const).continuousAt
    exact ContinuousAt.comp_of_eq hG_cont hmap_cont rfl
  have hzero_int :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        ∫ x : Fin m → ℝ, g x * φ x = 0 := by
    intro φ hφ_compact
    have himag :
        (fun i => (y i : ℂ) * Complex.I) ∈ TubeDomain C := by
      simpa [TubeDomain, y, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re] using hy
    have hmoll := hmoll_zero φ hφ_compact (fun i => (y i : ℂ) * Complex.I) himag
    simpa [g, realEmbed, y, Complex.re_add_im, add_comm, add_left_comm, add_assoc] using hmoll
  have hg_zero :
      ∀ x : Fin m → ℝ, g x = 0 := by
    have hzero_univ :=
      eq_zero_on_open_of_compactSupport_schwartz_integral_zero hg_cont isOpen_univ
        (fun φ hφ_compact _ => hzero_int φ hφ_compact)
    intro x
    simpa using hzero_univ x (by simp)
  simpa [g, y, Complex.re_add_im] using hg_zero (fun i => (z i).re)

end SCV

end
