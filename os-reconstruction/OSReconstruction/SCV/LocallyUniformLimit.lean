/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.TotallyRealIdentity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Locally Uniform Limits in Finite-Dimensional Complex Space

This file lifts the one-variable locally uniform limit theorem for holomorphic
functions to functions on `Fin m → ℂ`. The proof restricts to every coordinate
line and then applies Osgood's lemma.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical UniformConvergence

namespace SCV

/-- A sequence that is uniformly Cauchy on a relative neighborhood of every
point of `U` has a locally uniform limit on `U` whenever the target is
complete.

This is the local form needed for Banach-valued Taylor constructions: the
uniform Cauchy estimate may be proved on a different internal closed set near
each point, while completeness supplies the pointwise limits. -/
theorem exists_tendstoLocallyUniformlyOn_of_locally_uniformCauchy
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → X → E} {U : Set X}
    (hCauchy :
      ∀ x ∈ U, ∃ V ∈ 𝓝[U] x,
        UniformCauchySeqOn F atTop V) :
    ∃ f : X → E, TendstoLocallyUniformlyOn F f atTop U := by
  have hpointwise :
      ∀ x : X, ∃ y : E,
        x ∈ U → Tendsto (fun n => F n x) atTop (𝓝 y) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨V, hV_nhds, hV_cauchy⟩ := hCauchy x hx
      have hxV : x ∈ V := mem_of_mem_nhdsWithin hx hV_nhds
      obtain ⟨y, hy⟩ :=
        cauchySeq_tendsto_of_complete (hV_cauchy.cauchySeq hxV)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hxU => (hx hxU).elim⟩
  choose f hf using hpointwise
  refine ⟨f, ?_⟩
  intro u hu x hx
  obtain ⟨V, hV_nhds, hV_cauchy⟩ := hCauchy x hx
  let W := V ∩ U
  have hW_nhds : W ∈ 𝓝[U] x := by
    exact inter_mem hV_nhds self_mem_nhdsWithin
  have hW_cauchy : UniformCauchySeqOn F atTop W :=
    hV_cauchy.mono inter_subset_left
  have hW_tendsto :
      TendstoUniformlyOn F f atTop W :=
    hW_cauchy.tendstoUniformlyOn_of_tendsto fun y hy =>
      hf y hy.2
  exact ⟨W, hW_nhds, hW_tendsto u hu⟩

/-- A locally uniform limit of holomorphic functions on an open subset of
`Fin m → ℂ` is holomorphic. -/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn_fin
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {m : ℕ} {φ : Filter ι} [φ.NeBot]
    {F : ι → (Fin m → ℂ) → E} {f : (Fin m → ℂ) → E}
    {U : Set (Fin m → ℂ)}
    (hF : TendstoLocallyUniformlyOn F f φ U)
    (hF_hol : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) :
    DifferentiableOn ℂ f U := by
  apply osgood_lemma hU f
  · exact hF.continuousOn
      (Eventually.frequently (hF_hol.mono fun _ hn => hn.continuousOn))
  · intro z hz i
    let line : ℂ → (Fin m → ℂ) := Function.update z i
    let V : Set ℂ := line ⁻¹' U
    have hline_cont : Continuous line := by
      apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [line, Function.update_self]
        change Continuous (id : ℂ → ℂ)
        exact continuous_id
      · simpa [line, Function.update, hji] using
          (continuous_const : Continuous fun _ : ℂ => z j)
    have hline_diff : Differentiable ℂ line := by
      rw [differentiable_pi]
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [line] using (differentiable_id : Differentiable ℂ fun w : ℂ => w)
      · simpa [line, Function.update, hji] using
          (differentiable_const (c := z j) : Differentiable ℂ fun _ : ℂ => z j)
    have hV : IsOpen V := hU.preimage hline_cont
    have hzi : z i ∈ V := by
      simpa [V, line] using hz
    have hF_line :
        TendstoLocallyUniformlyOn
          (fun n => F n ∘ line) (f ∘ line) φ V :=
      hF.comp line (mapsTo_preimage _ _) hline_cont.continuousOn
    have hF_line_hol :
        ∀ᶠ n in φ, DifferentiableOn ℂ (F n ∘ line) V := by
      filter_upwards [hF_hol] with n hn
      exact hn.comp hline_diff.differentiableOn (mapsTo_preimage _ _)
    have hline_limit_hol :=
      hF_line.differentiableOn hF_line_hol hV
    change DifferentiableAt ℂ (f ∘ Function.update z i) (z i)
    exact hline_limit_hol.differentiableAt (hV.mem_nhds hzi)

/-- A locally uniform limit of holomorphic functions on a finite complex
coordinate space is holomorphic. -/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn_finite
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Fintype κ] [DecidableEq κ]
    {φ : Filter ι} [φ.NeBot]
    {F : ι → (κ → ℂ) → E} {f : (κ → ℂ) → E}
    {U : Set (κ → ℂ)}
    (hF : TendstoLocallyUniformlyOn F f φ U)
    (hF_hol : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) :
    DifferentiableOn ℂ f U := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let L : (κ → ℂ) ≃L[ℂ] (Fin (Fintype.card κ) → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin (Fintype.card κ) => ℂ) e
  let V : Set (Fin (Fintype.card κ) → ℂ) := L.symm ⁻¹' U
  let G : ι → (Fin (Fintype.card κ) → ℂ) → E :=
    fun n => F n ∘ L.symm
  let g : (Fin (Fintype.card κ) → ℂ) → E := f ∘ L.symm
  have hV : IsOpen V := hU.preimage L.symm.continuous
  have hG : TendstoLocallyUniformlyOn G g φ V := by
    exact hF.comp L.symm (mapsTo_preimage _ _) L.symm.continuous.continuousOn
  have hG_hol : ∀ᶠ n in φ, DifferentiableOn ℂ (G n) V := by
    filter_upwards [hF_hol] with n hn
    exact hn.comp L.symm.differentiable.differentiableOn (mapsTo_preimage _ _)
  have hg : DifferentiableOn ℂ g V :=
    hG.differentiableOn_fin hG_hol hV
  have hcomp :
      DifferentiableOn ℂ (g ∘ L) U :=
    hg.comp L.differentiable.differentiableOn fun z hz => by
      simpa [V] using hz
  simpa [g, L, Function.comp_def] using hcomp

/-- Locally uniform Cauchy control of finite-dimensional Banach-valued
holomorphic approximants constructs a holomorphic limit. -/
theorem exists_tendstoLocallyUniformlyOn_differentiableOn_fin_of_locally_uniformCauchy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {m : ℕ} {F : ℕ → (Fin m → ℂ) → E}
    {U : Set (Fin m → ℂ)}
    (hCauchy :
      ∀ x ∈ U, ∃ V ∈ 𝓝[U] x,
        UniformCauchySeqOn F atTop V)
    (hF_hol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) :
    ∃ f : (Fin m → ℂ) → E,
      TendstoLocallyUniformlyOn F f atTop U ∧
        DifferentiableOn ℂ f U := by
  obtain ⟨f, hf⟩ :=
    exists_tendstoLocallyUniformlyOn_of_locally_uniformCauchy hCauchy
  refine ⟨f, hf, ?_⟩
  exact hf.differentiableOn_fin
    (Filter.Eventually.of_forall hF_hol) hU

/-- A finite-dimensional Vitali--Montel theorem with convergence prescribed
on a nonempty open patch of the totally real locus.

Compact-local boundedness gives equicontinuity by the Schwarz estimate.
Arzela--Ascoli supplies compactness in the compact-open topology, and the
totally-real identity theorem makes every cluster limit equal. -/
theorem exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_tendsto_on_open_real
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : ℕ → (κ → ℂ) → ℂ}
    {U : Set (κ → ℂ)}
    {V : Set (κ → ℝ)}
    {edge : (κ → ℝ) → ℂ}
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
      ∀ x ∈ V,
        Tendsto (fun n => F n (fun i => (x i : ℂ)))
          atTop (nhds (edge x))) :
    ∃ limit : (κ → ℂ) → ℂ,
      TendstoLocallyUniformlyOn F limit atTop U ∧
        DifferentiableOn ℂ limit U ∧
        ∀ x ∈ V, limit (fun i => (x i : ℂ)) = edge x := by
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
  let T : (D →ᵤ[𝔖] ℂ) → D → ℂ :=
    UniformOnFun.toFun 𝔖
  have hcompact :
      IsCompact (closure (Set.range G)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := 𝔖) (F := T)
    · intro K hK
      exact hK
    · have hid :
          UniformOnFun.ofFun 𝔖 ∘ T =
            (id : (D →ᵤ[𝔖] ℂ) → (D →ᵤ[𝔖] ℂ)) := by
        funext f
        simp [T]
      rw [hid]
      exact IsClosedEmbedding.id
    · intro K _hK
      have hsub :
          Equicontinuous (U.restrict ∘ F) :=
        equicontinuous_restrict_iff F |>.2 hequicont
      let pick : Set.range G → ℕ :=
        fun f => Classical.choose f.property
      have hfamily :
          T ∘ ((↑) : Set.range G → (D →ᵤ[𝔖] ℂ)) =
            (U.restrict ∘ F) ∘ pick := by
        funext f
        have hpick := Classical.choose_spec f.property
        funext z
        change T f z = F (pick f) z
        rw [show f.1 = G (pick f) by
          simpa [pick] using hpick.symm]
        simp [T, G, approx, D]
      rw [hfamily]
      exact (hsub.equicontinuousOn K).comp pick
    · intro K _hK z _hz
      obtain ⟨C, hC, hCbound⟩ :=
        hbound {z.1} isCompact_singleton (by
          intro w hw
          simpa only [Set.mem_singleton_iff] using hw ▸ z.2)
      refine ⟨Metric.closedBall 0 C, isCompact_closedBall 0 C, ?_⟩
      intro f hf
      rcases hf with ⟨n, rfl⟩
      rw [Metric.mem_closedBall]
      simpa [T, G, approx, dist_zero_right] using
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
    fun f z => if hz : z ∈ U then T f ⟨z, hz⟩ else 0
  have hcluster_properties :
      ∀ y : D →ᵤ[𝔖] ℂ, MapClusterPt y atTop G →
        DifferentiableOn ℂ (ambient y) U ∧
          ∀ x ∈ V,
            ambient y (fun i => (x i : ℂ)) = edge x := by
    intro y hy
    obtain ⟨p, hp_le, hGy⟩ :=
      mapClusterPt_iff_ultrafilter.mp hy
    have hlocal_subtype :
        TendstoLocallyUniformly
          (fun n (z : D) => F n z)
          (T y) p := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      have huniform :=
        (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hGy)
          K (by simpa [𝔖] using hK)
      simpa [G, T, approx, Function.comp_def] using huniform
    have hlocal_ambient :
        TendstoLocallyUniformlyOn F (ambient y) p U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      simpa [ambient, D, T, Function.comp_def] using hlocal_subtype
    constructor
    · exact hlocal_ambient.differentiableOn_finite
        (Filter.Eventually.of_forall hF_hol) hU_open
    · intro x hx
      exact tendsto_nhds_unique
        (hlocal_ambient.tendsto_at (hV_sub x hx))
        ((hreal x hx).mono_left hp_le)
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
    have hambient_eq :
        Set.EqOn (ambient y) (ambient y₀) U := by
      exact
        holomorphic_eq_of_eq_on_open_real_of_connected_finite
          hU_open hU_conn
          hy_properties.1 hy₀_properties.1
          hV_open hV_ne hV_sub
          (fun x hx =>
            (hy_properties.2 x hx).trans
              (hy₀_properties.2 x hx).symm)
    funext z
    have hz_eq := hambient_eq z.property
    have hy : (UniformOnFun.toFun 𝔖 y) z = y z :=
      congrFun (UniformOnFun.ofFun_toFun y) z
    have hy₀ : (UniformOnFun.toFun 𝔖 y₀) z = y₀ z :=
      congrFun (UniformOnFun.ofFun_toFun y₀) z
    have hmid : (UniformOnFun.toFun 𝔖 y) z = (UniformOnFun.toFun 𝔖 y₀) z := by
      simpa only [ambient, z.property, ↓reduceDIte, T] using hz_eq
    exact Eq.trans hy.symm (Eq.trans hmid hy₀)
  have hG_tendsto :
      Tendsto G atTop (nhds y₀) :=
    hcompact.tendsto_nhds_of_unique_mapClusterPt hG_mem hunique
  have hlocal_subtype :
      TendstoLocallyUniformly
        (fun n (z : D) => F n z)
        (T y₀) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have huniform :=
      (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hG_tendsto)
        K (by simpa [𝔖] using hK)
    simpa [G, T, approx, Function.comp_def] using huniform
  let limit : (κ → ℂ) → ℂ := ambient y₀
  have hlocal :
      TendstoLocallyUniformlyOn F limit atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa [limit, ambient, D, T, Function.comp_def] using
      hlocal_subtype
  refine ⟨limit, hlocal, ?_, ?_⟩
  · exact hlocal.differentiableOn_finite
      (Filter.Eventually.of_forall hF_hol) hU_open
  · intro x hx
    exact tendsto_nhds_unique
      (hlocal.tendsto_at (hV_sub x hx))
      (hreal x hx)

end SCV
