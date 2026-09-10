/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.SCV.DistributionalUniqueness

/-!
# Locally Uniform Limits and Distributional Pairings

A locally uniform limit on an open carrier may be passed through pairing with
a Schwartz test supported in that carrier. This is the analytic last mile for
regularized local representatives of a fixed Schwartz distribution.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical UniformConvergence

namespace SCV

/-- Pairing with a compactly supported Schwartz test preserves locally uniform
convergence on the open carrier containing its support, along an arbitrary
nontrivial filter. -/
theorem tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn_filter
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → E → ℂ} {f : E → ℂ} {U : Set E}
    (hU : IsOpen U)
    (hF_cont : ∀ q, ContinuousOn (F q) U)
    (hF : TendstoLocallyUniformlyOn F f l U)
    (φ : SchwartzMap E ℂ)
    (hφ : SupportsInOpen (φ : E → ℂ) U) :
    Tendsto
      (fun q => ∫ x : E, F q x * φ x)
      l
      (nhds (∫ x : E, f x * φ x)) := by
  have hf_cont : ContinuousOn f U :=
    hF.continuousOn
      (Filter.Eventually.frequently
        (Filter.Eventually.of_forall hF_cont))
  have hF_int :
      ∀ q, Integrable (fun x : E => F q x * φ x) := by
    intro q
    exact
      integrable_continuousOn_mul_schwartz_of_supportsInOpen
        hU (hF_cont q) hφ
  have hf_int : Integrable (fun x : E => f x * φ x) :=
    integrable_continuousOn_mul_schwartz_of_supportsInOpen
      hU hf_cont hφ
  have huniform :
      TendstoUniformlyOn F f l
        (tsupport (φ : E → ℂ)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      hφ.1).mp (hF.mono hφ.2)
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  let M : ℝ := ∫ x : E, ‖φ x‖
  have hM_nonneg : 0 ≤ M := by
    exact integral_nonneg fun x => norm_nonneg (φ x)
  have hM_one_pos : 0 < M + 1 := by
    linarith
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε hM_one_pos
  have hsmall :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) δ hδ
  filter_upwards [hsmall] with q hq
  have hpoint :
      ∀ x : E,
        ‖F q x * φ x - f x * φ x‖ ≤ δ * ‖φ x‖ := by
    intro x
    by_cases hx : x ∈ tsupport (φ : E → ℂ)
    · have hclose : ‖F q x - f x‖ < δ := by
        simpa [dist_eq_norm, norm_sub_rev] using hq x hx
      calc
        ‖F q x * φ x - f x * φ x‖ =
            ‖F q x - f x‖ * ‖φ x‖ := by
              rw [← sub_mul, norm_mul]
        _ ≤ δ * ‖φ x‖ :=
          mul_le_mul_of_nonneg_right hclose.le (norm_nonneg _)
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport hx
      simp [hφx]
  have hupper_int :
      Integrable (fun x : E => δ * ‖φ x‖) := by
    exact
      ((φ.continuous.norm.integrable_of_hasCompactSupport hφ.1.norm).const_mul δ)
  have hnorm :
      ‖(∫ x : E, F q x * φ x) -
          ∫ x : E, f x * φ x‖ ≤ δ * M := by
    rw [← integral_sub (hF_int q) hf_int]
    calc
      ‖∫ x : E, (F q x * φ x - f x * φ x)‖
          ≤ ∫ x : E, ‖F q x * φ x - f x * φ x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : E, δ * ‖φ x‖ := by
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hupper_int
          (Filter.Eventually.of_forall hpoint)
      _ = δ * M := by
        simp [M, integral_const_mul]
  have hδM : δ * M < ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM_one_pos]
    nlinarith
  simpa [dist_eq_norm] using hnorm.trans_lt hδM

/-- `atTop` specialization retained for the stage-limit callers. -/
theorem tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {F : ℕ → E → ℂ} {f : E → ℂ} {U : Set E}
    (hU : IsOpen U)
    (hF_cont : ∀ q, ContinuousOn (F q) U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (φ : SchwartzMap E ℂ)
    (hφ : SupportsInOpen (φ : E → ℂ) U) :
    Tendsto
      (fun q => ∫ x : E, F q x * φ x)
      atTop
      (nhds (∫ x : E, f x * φ x)) :=
  tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn_filter
    hU hF_cont hF φ hφ

/-- A finite-dimensional Vitali--Montel theorem with convergence prescribed
only distributionally on a nonempty open patch of the totally real locus.

Compact-local boundedness makes the holomorphic family compact in the
compact-open topology. Every cluster limit induces the same distribution on
the real patch. Distributional uniqueness for continuous functions identifies
their real traces pointwise, and the totally-real identity theorem then
identifies the holomorphic cluster limits. Thus the whole sequence converges
locally uniformly, and its real trace represents the prescribed
distribution. -/
theorem
    exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_distributional_real_limit
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : ℕ → (κ → ℂ) → ℂ}
    {U : Set (κ → ℂ)}
    {V : Set (κ → ℝ)}
    {T : SchwartzMap (κ → ℝ) ℂ → ℂ}
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, (fun i => (x i : ℂ)) ∈ U)
    (hF_hol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbound :
      ∀ K : Set (κ → ℂ), IsCompact K → K ⊆ U →
        ∃ C : ℝ, 0 < C ∧
          ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (hreal :
      ∀ φ : SchwartzMap (κ → ℝ) ℂ,
        SupportsInOpen (φ : (κ → ℝ) → ℂ) V →
          Tendsto
            (fun n =>
              ∫ x : κ → ℝ, F n (fun i => (x i : ℂ)) * φ x)
            atTop (nhds (T φ))) :
    ∃ limit : (κ → ℂ) → ℂ,
      TendstoLocallyUniformlyOn F limit atTop U ∧
        DifferentiableOn ℂ limit U ∧
        ∀ φ : SchwartzMap (κ → ℝ) ℂ,
          SupportsInOpen (φ : (κ → ℝ) → ℂ) V →
            ∫ x : κ → ℝ, limit (fun i => (x i : ℂ)) * φ x =
              T φ := by
  have hequicont : EquicontinuousOn F U := by
    intro z hz
    apply EquicontinuousAt.equicontinuousWithinAt
    obtain ⟨R, hR, hball⟩ :=
      Metric.isOpen_iff.mp hU_open z hz
    let r : ℝ := R / 2
    have hr : 0 < r := half_pos hR
    let K : Set (κ → ℂ) := Metric.closedBall z r
    have hK_compact : IsCompact K := isCompact_closedBall z r
    have hK_sub : K ⊆ U := by
      intro q hq
      apply hball
      rw [Metric.mem_ball]
      exact (Metric.mem_closedBall.mp hq).trans_lt (by
        dsimp [r]
        linarith)
    obtain ⟨C, hC, hCbound⟩ :=
      hbound K hK_compact hK_sub
    let modulus : (κ → ℂ) → ℝ :=
      fun q => (2 * C / r) * dist q z
    have hmodulus :
        Tendsto modulus (nhds z) (nhds 0) := by
      have hdist :
          Tendsto (fun q : κ → ℂ => dist q z)
            (nhds z) (nhds 0) := by
        simpa using
          ((tendsto_id : Tendsto id (nhds z) (nhds z)).dist
            (tendsto_const_nhds :
              Tendsto (fun _ : κ → ℂ => z) (nhds z) (nhds z)))
      simpa [modulus] using hdist.const_mul (2 * C / r)
    apply
      Metric.equicontinuousAt_of_continuity_modulus
        modulus hmodulus F
    filter_upwards [Metric.ball_mem_nhds z hr] with q hq
    intro n
    have hball_r_sub : Metric.ball z r ⊆ U :=
      fun w hw => hK_sub (Metric.ball_subset_closedBall hw)
    have hdiff :
        DifferentiableOn ℂ (F n) (Metric.ball z r) :=
      (hF_hol n).mono hball_r_sub
    have hzK : z ∈ K := by
      exact Metric.mem_closedBall.mpr (by simpa using le_of_lt hr)
    have hmaps :
        MapsTo (F n) (Metric.ball z r)
          (Metric.closedBall (F n z) (2 * C)) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖F n w - F n z‖ ≤ ‖F n w‖ + ‖F n z‖ :=
          norm_sub_le _ _
        _ ≤ C + C := by
          exact add_le_add
            (hCbound n w (Metric.ball_subset_closedBall hw))
            (hCbound n z hzK)
        _ = 2 * C := by ring
    simpa [modulus, mul_comm, dist_comm] using
      dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hq
  let D := {z : κ → ℂ // z ∈ U}
  let 𝔖 : Set (Set D) := {K | IsCompact K}
  let approx : ℕ → D → ℂ := fun n z => F n z
  let G : ℕ → (D →ᵤ[𝔖] ℂ) :=
    fun n => UniformOnFun.ofFun 𝔖 (approx n)
  let eval : (D →ᵤ[𝔖] ℂ) → D → ℂ :=
    UniformOnFun.toFun 𝔖
  have hcompact :
      IsCompact (closure (Set.range G)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := 𝔖) (F := eval)
    · intro K hK
      exact hK
    · have hid :
          UniformOnFun.ofFun 𝔖 ∘ eval =
            (id : (D →ᵤ[𝔖] ℂ) → (D →ᵤ[𝔖] ℂ)) := by
        funext f
        simp [eval]
      rw [hid]
      exact IsClosedEmbedding.id
    · intro K _hK
      have hsub :
          Equicontinuous (U.restrict ∘ F) :=
        equicontinuous_restrict_iff F |>.2 hequicont
      let pick : Set.range G → ℕ :=
        fun f => Classical.choose f.property
      have hfamily :
          eval ∘ ((↑) : Set.range G → (D →ᵤ[𝔖] ℂ)) =
            (U.restrict ∘ F) ∘ pick := by
        funext f
        have hpick := Classical.choose_spec f.property
        funext z
        change eval f z = F (pick f) z
        rw [show f.1 = G (pick f) by
          simpa [pick] using hpick.symm]
        simp [eval, G, approx, D]
      rw [hfamily]
      exact (hsub.equicontinuousOn K).comp pick
    · intro K _hK z _hz
      obtain ⟨C, _hC, hCbound⟩ :=
        hbound {z.1} isCompact_singleton (by
          intro w hw
          simpa only [Set.mem_singleton_iff] using hw ▸ z.2)
      refine ⟨Metric.closedBall 0 C, isCompact_closedBall 0 C, ?_⟩
      intro f hf
      rcases hf with ⟨n, rfl⟩
      rw [Metric.mem_closedBall]
      simpa [eval, G, approx, dist_zero_right] using
        hCbound n z.1 (Set.mem_singleton z.1)
  have hcover : ⋃₀ 𝔖 = Set.univ := by
    ext z
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact
      ⟨{z}, by simpa [𝔖] using isCompact_singleton,
        Set.mem_singleton z⟩
  letI : T2Space (D →ᵤ[𝔖] ℂ) :=
    UniformOnFun.t2Space_of_covering hcover
  letI : LocallyCompactSpace D :=
    hU_open.locallyCompactSpace
  let ambient :
      (D →ᵤ[𝔖] ℂ) → (κ → ℂ) → ℂ :=
    fun f z => if hz : z ∈ U then eval f ⟨z, hz⟩ else 0
  let realEmbed : (κ → ℝ) → (κ → ℂ) :=
    fun x i => (x i : ℂ)
  have hrealEmbed_cont : Continuous realEmbed := by
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp (continuous_apply i)
  have hcluster_properties :
      ∀ y : D →ᵤ[𝔖] ℂ, MapClusterPt y atTop G →
        DifferentiableOn ℂ (ambient y) U ∧
          ∀ φ : SchwartzMap (κ → ℝ) ℂ,
            SupportsInOpen (φ : (κ → ℝ) → ℂ) V →
              ∫ x : κ → ℝ, ambient y (realEmbed x) * φ x =
                T φ := by
    intro y hy
    obtain ⟨p, hp_le, hGy⟩ :=
      mapClusterPt_iff_ultrafilter.mp hy
    have hlocal_subtype :
        TendstoLocallyUniformly
          (fun n (z : D) => F n z)
          (eval y) p := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      have huniform :=
        (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hGy)
          K (by simpa [𝔖] using hK)
      simpa [G, eval, approx, Function.comp_def] using huniform
    have hlocal_ambient :
        TendstoLocallyUniformlyOn F (ambient y) p U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      simpa [ambient, D, eval, Function.comp_def] using hlocal_subtype
    constructor
    · exact hlocal_ambient.differentiableOn_finite
        (Filter.Eventually.of_forall hF_hol) hU_open
    · intro φ hφ
      have hlocal_real :
          TendstoLocallyUniformlyOn
            (fun n x => F n (realEmbed x))
            (fun x => ambient y (realEmbed x)) p V :=
        hlocal_ambient.comp realEmbed hV_sub
          hrealEmbed_cont.continuousOn
      have hcont_real :
          ∀ n,
            ContinuousOn (fun x => F n (realEmbed x)) V := by
        intro n
        exact (hF_hol n).continuousOn.comp
          hrealEmbed_cont.continuousOn hV_sub
      exact tendsto_nhds_unique
        (tendsto_integral_mul_schwartz_of_tendstoLocallyUniformlyOn_filter
          hV_open hcont_real hlocal_real φ hφ)
        ((hreal φ hφ).mono_left hp_le)
  have hG_mem :
      ∀ᶠ n in atTop, G n ∈ closure (Set.range G) :=
    Filter.Eventually.of_forall fun n =>
      subset_closure (Set.mem_range_self n)
  have hG_map :
      Filter.map G atTop ≤
        Filter.principal (closure (Set.range G)) := by
    rw [Filter.le_principal_iff]
    exact hG_mem
  obtain ⟨y₀, _hy₀_mem, hy₀_cluster⟩ :=
    hcompact.exists_mapClusterPt hG_map
  have hy₀_properties :=
    hcluster_properties y₀ hy₀_cluster
  have hunique :
      ∀ y ∈ closure (Set.range G), MapClusterPt y atTop G → y = y₀ := by
    intro y _hy_mem hy_cluster
    have hy_properties :=
      hcluster_properties y hy_cluster
    have hy_real_cont :
        ContinuousOn (fun x => ambient y (realEmbed x)) V :=
      hy_properties.1.continuousOn.comp
        hrealEmbed_cont.continuousOn hV_sub
    have hy₀_real_cont :
        ContinuousOn (fun x => ambient y₀ (realEmbed x)) V :=
      hy₀_properties.1.continuousOn.comp
        hrealEmbed_cont.continuousOn hV_sub
    have hreal_eq :
        Set.EqOn
          (fun x => ambient y (realEmbed x))
          (fun x => ambient y₀ (realEmbed x)) V := by
      apply
        eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
          hV_open hy_real_cont hy₀_real_cont
      intro φ hφ_compact hφ_support
      exact
        (hy_properties.2 φ ⟨hφ_compact, hφ_support⟩).trans
          (hy₀_properties.2 φ ⟨hφ_compact, hφ_support⟩).symm
    have hambient_eq :
        Set.EqOn (ambient y) (ambient y₀) U := by
      exact
        holomorphic_eq_of_eq_on_open_real_of_connected_finite
          hU_open hU_conn
          hy_properties.1 hy₀_properties.1
          hV_open hV_ne hV_sub hreal_eq
    funext z
    have hz_eq := hambient_eq z.property
    simpa [ambient, eval, z.property] using hz_eq
  have hG_tendsto :
      Tendsto G atTop (nhds y₀) :=
    hcompact.tendsto_nhds_of_unique_mapClusterPt hG_mem hunique
  have hlocal_subtype :
      TendstoLocallyUniformly
        (fun n (z : D) => F n z)
        (eval y₀) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have huniform :=
      (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hG_tendsto)
        K (by simpa [𝔖] using hK)
    simpa [G, eval, approx, Function.comp_def] using huniform
  let limit : (κ → ℂ) → ℂ := ambient y₀
  have hlocal :
      TendstoLocallyUniformlyOn F limit atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa [limit, ambient, D, eval, Function.comp_def] using
      hlocal_subtype
  refine ⟨limit, hlocal, ?_, ?_⟩
  · exact hlocal.differentiableOn_finite
      (Filter.Eventually.of_forall hF_hol) hU_open
  · intro φ hφ
    exact hy₀_properties.2 φ hφ

end SCV
