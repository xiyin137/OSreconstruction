import OSReconstruction.SCV.SchwartzComplete

/-!
# Dense Boundary-Value Extension

This file records the functional-analytic bridge used in distributional
boundary-value arguments: convergence on a dense class of test functions, plus
either an eventual uniform operator bound or eventual equicontinuity at zero,
extends to convergence on all tests.
-/

noncomputable section

open Filter Topology
open scoped Topology

namespace SCV

theorem tendsto_clm_apply_of_dense_of_eventually_bound
    {𝕜 : Type*} [NormedField 𝕜]
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {α : Type*} {l : Filter α} [NeBot l]
    {T : α → E →L[𝕜] F} {S : E →L[𝕜] F}
    {D : Set E}
    (hD : Dense D)
    (h_onD : ∀ x ∈ D, Tendsto (fun a => T a x) l (nhds (S x)))
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ x : E, ‖(T a - S) x‖ ≤ C * ‖x‖) :
    ∀ x : E, Tendsto (fun a => T a x) l (nhds (S x)) := by
  classical
  rcases h_bound with ⟨C, hC_nonneg, hC_bound⟩
  intro x
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hC1_pos : 0 < C + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hx_closure : x ∈ closure D := by
    simp [hD.closure_eq]
  rcases Metric.mem_closure_iff.mp hx_closure δ hδ_pos with
    ⟨y, hyD, hy_dist⟩
  have hy_norm : ‖x - y‖ < δ := by
    simpa [dist_eq_norm] using hy_dist
  have hhalf : C * ‖x - y‖ ≤ ε / 2 := by
    have hle₁ : C * ‖x - y‖ ≤ C * δ := by
      nlinarith [hy_norm, hC_nonneg]
    have hle₂ : C * δ ≤ (C + 1) * δ := by
      nlinarith [hδ_pos]
    have hδ_eq : (C + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp [hC1_pos.ne']
    linarith
  have h_y := (Metric.tendsto_nhds.mp (h_onD y hyD)) (ε / 2) (by linarith)
  filter_upwards [hC_bound, h_y] with a hCa hya
  have hsplit :
      T a x - S x = (T a - S) (x - y) + (T a y - S y) := by
    have hTx : T a x = T a (x - y) + T a y := by
      calc
        T a x = T a ((x - y) + y) := by simp
        _ = T a (x - y) + T a y := by rw [map_add]
    have hSx : S x = S (x - y) + S y := by
      calc
        S x = S ((x - y) + y) := by simp
        _ = S (x - y) + S y := by rw [map_add]
    rw [hTx, hSx]
    simp [ContinuousLinearMap.sub_apply]
    abel
  calc
    dist (T a x) (S x) = ‖T a x - S x‖ := by
      rw [dist_eq_norm]
    _ = ‖(T a - S) (x - y) + (T a y - S y)‖ := by
      rw [hsplit]
    _ ≤ ‖(T a - S) (x - y)‖ + ‖T a y - S y‖ := norm_add_le _ _
    _ < ε := by
      have hfirst : ‖(T a - S) (x - y)‖ ≤ ε / 2 :=
        (hCa (x - y)).trans hhalf
      have hsecond : ‖T a y - S y‖ < ε / 2 := by
        simpa [dist_eq_norm] using hya
      linarith

theorem tendsto_clm_apply_of_dense_span_of_eventually_bound
    {𝕜 : Type*} [NormedField 𝕜]
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {α : Type*} {l : Filter α} [NeBot l]
    {T : α → E →L[𝕜] F} {S : E →L[𝕜] F}
    {D : Set E}
    (hD :
      Dense (((Submodule.span 𝕜 D : Submodule 𝕜 E) : Set E)))
    (h_onD : ∀ x ∈ D, Tendsto (fun a => T a x) l (nhds (S x)))
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ x : E, ‖(T a - S) x‖ ≤ C * ‖x‖) :
    ∀ x : E, Tendsto (fun a => T a x) l (nhds (S x)) := by
  classical
  let M : Submodule 𝕜 E := Submodule.span 𝕜 D
  have h_onM : ∀ x ∈ (M : Set E), Tendsto (fun a => T a x) l (nhds (S x)) := by
    intro x hx
    change x ∈ Submodule.span 𝕜 D at hx
    refine Submodule.span_induction ?pD ?p0 ?padd ?psmul hx
    · intro y hy
      exact h_onD y hy
    · simp
    · intro y z _hy _hz hy_tendsto hz_tendsto
      simpa [map_add] using hy_tendsto.add hz_tendsto
    · intro c y _hy hy_tendsto
      simpa [map_smulₛₗ] using hy_tendsto.const_smul c
  exact
    tendsto_clm_apply_of_dense_of_eventually_bound
      (hD := hD) h_onM h_bound

theorem tendsto_clm_apply_of_dense_of_eventually_equicontinuous
    {𝕜 : Type*} [Ring 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
    {α : Type*} {l : Filter α} [NeBot l]
    {T : α → E →L[𝕜] F} {S : E →L[𝕜] F}
    {D : Set E}
    (hD : Dense D)
    (h_onD : ∀ x ∈ D, Tendsto (fun a => T a x) l (nhds (S x)))
    (h_equicont :
      ∀ W ∈ nhds (0 : F), ∃ U ∈ nhds (0 : E),
        ∀ᶠ a in l, ∀ x ∈ U, (T a - S) x ∈ W) :
    ∀ x : E, Tendsto (fun a => T a x) l (nhds (S x)) := by
  classical
  intro x
  rw [tendsto_nhds]
  intro W hWopen hxW
  have hWzero : {z : F | S x + z ∈ W} ∈ nhds (0 : F) := by
    have hWnhds : W ∈ nhds (S x) := hWopen.mem_nhds hxW
    have hcont : ContinuousAt (fun z : F => S x + z) (0 : F) := by fun_prop
    simpa using hcont.preimage_mem_nhds (by simpa using hWnhds)
  rcases exists_nhds_zero_half hWzero with ⟨V, hV, hVadd⟩
  rcases h_equicont V hV with ⟨U, hU, hUevent⟩
  have hUx : {y : E | x - y ∈ U} ∈ nhds x := by
    have hcont : ContinuousAt (fun y : E => x - y) x := by fun_prop
    have hpre := hcont.preimage_mem_nhds (by simpa using hU)
    simpa using hpre
  rcases hD.inter_nhds_nonempty hUx with ⟨y, hyD, hyU⟩
  have hy_tendsto := h_onD y hyD
  have hy_event : ∀ᶠ a in l, T a y - S y ∈ V := by
    have hsub_nhds : {z : F | z - S y ∈ V} ∈ nhds (S y) := by
      have hcont : ContinuousAt (fun z : F => z - S y) (S y) := by fun_prop
      have hpre := hcont.preimage_mem_nhds (by simpa using hV)
      simpa using hpre
    exact hy_tendsto hsub_nhds
  filter_upwards [hUevent, hy_event] with a hUa hya
  have hx_split :
      T a x - S x = (T a - S) (x - y) + (T a y - S y) := by
    have hTx : T a x = T a (x - y) + T a y := by
      calc
        T a x = T a ((x - y) + y) := by simp
        _ = T a (x - y) + T a y := by rw [map_add]
    have hSx : S x = S (x - y) + S y := by
      calc
        S x = S ((x - y) + y) := by simp
        _ = S (x - y) + S y := by rw [map_add]
    rw [hTx, hSx]
    simp [ContinuousLinearMap.sub_apply]
    abel
  have hsum_mem :
      (T a - S) (x - y) + (T a y - S y) ∈ {z : F | S x + z ∈ W} :=
    hVadd ((T a - S) (x - y)) (hUa (x - y) hyU) (T a y - S y) hya
  have hmem : S x + (T a x - S x) ∈ W := by
    rw [hx_split]
    exact hsum_mem
  simpa using hmem

theorem tendsto_clm_apply_of_dense_span_of_eventually_equicontinuous
    {𝕜 : Type*} [Ring 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F]
    {α : Type*} {l : Filter α} [NeBot l]
    {T : α → E →L[𝕜] F} {S : E →L[𝕜] F}
    {D : Set E}
    (hD :
      Dense (((Submodule.span 𝕜 D : Submodule 𝕜 E) : Set E)))
    (h_onD : ∀ x ∈ D, Tendsto (fun a => T a x) l (nhds (S x)))
    (h_equicont :
      ∀ W ∈ nhds (0 : F), ∃ U ∈ nhds (0 : E),
        ∀ᶠ a in l, ∀ x ∈ U, (T a - S) x ∈ W) :
    ∀ x : E, Tendsto (fun a => T a x) l (nhds (S x)) := by
  classical
  let M : Submodule 𝕜 E := Submodule.span 𝕜 D
  have h_onM : ∀ x ∈ (M : Set E), Tendsto (fun a => T a x) l (nhds (S x)) := by
    intro x hx
    change x ∈ Submodule.span 𝕜 D at hx
    refine Submodule.span_induction ?pD ?p0 ?padd ?psmul hx
    · intro y hy
      exact h_onD y hy
    · simpa using tendsto_const_nhds
    · intro y z _hy _hz hy_tendsto hz_tendsto
      simpa [map_add] using hy_tendsto.add hz_tendsto
    · intro c y _hy hy_tendsto
      simpa [map_smulₛₗ] using hy_tendsto.const_smul c
  exact
    tendsto_clm_apply_of_dense_of_eventually_equicontinuous
      (hD := hD) h_onM h_equicont

/-- Local closure form of the dense boundary-value extension.

If a single test lies in the closure of the span of the generator class, then
convergence on that generator class plus eventual equicontinuity of the
differences gives convergence at that test.  This is the Banach-Steinhaus
step used after a product cutoff localizes a compact source to one Lemma 5.1
window; the supported generators need not be dense in the whole Schwartz
space. -/
theorem tendsto_clm_apply_of_mem_closure_span_of_eventually_equicontinuous
    {𝕜 : Type*} [Ring 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F]
    {α : Type*} {l : Filter α} [NeBot l]
    {T : α → E →L[𝕜] F} {S : E →L[𝕜] F}
    {D : Set E} {x : E}
    (hx :
      x ∈ closure (((Submodule.span 𝕜 D : Submodule 𝕜 E) : Set E)))
    (h_onD : ∀ y ∈ D, Tendsto (fun a => T a y) l (nhds (S y)))
    (h_equicont :
      ∀ W ∈ nhds (0 : F), ∃ U ∈ nhds (0 : E),
        ∀ᶠ a in l, ∀ y ∈ U, (T a - S) y ∈ W) :
    Tendsto (fun a => T a x) l (nhds (S x)) := by
  classical
  let M : Submodule 𝕜 E := Submodule.span 𝕜 D
  have h_onM : ∀ y ∈ (M : Set E), Tendsto (fun a => T a y) l (nhds (S y)) := by
    intro y hy
    change y ∈ Submodule.span 𝕜 D at hy
    refine Submodule.span_induction ?pD ?p0 ?padd ?psmul hy
    · intro z hz
      exact h_onD z hz
    · simpa using tendsto_const_nhds
    · intro y z _hy _hz hy_tendsto hz_tendsto
      simpa [map_add] using hy_tendsto.add hz_tendsto
    · intro c y _hy hy_tendsto
      simpa [map_smulₛₗ] using hy_tendsto.const_smul c
  rw [tendsto_nhds]
  intro W hWopen hxW
  have hWzero : {z : F | S x + z ∈ W} ∈ nhds (0 : F) := by
    have hWnhds : W ∈ nhds (S x) := hWopen.mem_nhds hxW
    have hcont : ContinuousAt (fun z : F => S x + z) (0 : F) := by fun_prop
    simpa using hcont.preimage_mem_nhds (by simpa using hWnhds)
  rcases exists_nhds_zero_half hWzero with ⟨V, hV, hVadd⟩
  rcases h_equicont V hV with ⟨U, hU, hUevent⟩
  have hUx : {y : E | x - y ∈ U} ∈ nhds x := by
    have hcont : ContinuousAt (fun y : E => x - y) x := by fun_prop
    have hpre := hcont.preimage_mem_nhds (by simpa using hU)
    simpa using hpre
  have hclosure :
      x ∈ closure ((M : Set E)) := by
    simpa [M] using hx
  rcases mem_closure_iff_nhds.mp hclosure _ hUx with ⟨y, hy⟩
  have hyU : x - y ∈ U := hy.1
  have hyM : y ∈ (M : Set E) := hy.2
  have hy_tendsto := h_onM y hyM
  have hy_event : ∀ᶠ a in l, T a y - S y ∈ V := by
    have hsub_nhds : {z : F | z - S y ∈ V} ∈ nhds (S y) := by
      have hcont : ContinuousAt (fun z : F => z - S y) (S y) := by fun_prop
      have hpre := hcont.preimage_mem_nhds (by simpa using hV)
      simpa using hpre
    exact hy_tendsto hsub_nhds
  filter_upwards [hUevent, hy_event] with a hUa hya
  have hx_split :
      T a x - S x = (T a - S) (x - y) + (T a y - S y) := by
    have hTx : T a x = T a (x - y) + T a y := by
      calc
        T a x = T a ((x - y) + y) := by simp
        _ = T a (x - y) + T a y := by rw [map_add]
    have hSx : S x = S (x - y) + S y := by
      calc
        S x = S ((x - y) + y) := by simp
        _ = S (x - y) + S y := by rw [map_add]
    rw [hTx, hSx]
    simp [ContinuousLinearMap.sub_apply]
    abel
  have hsum_mem :
      (T a - S) (x - y) + (T a y - S y) ∈ {z : F | S x + z ∈ W} :=
    hVadd ((T a - S) (x - y)) (hUa (x - y) hyU) (T a y - S y) hya
  have hmem : S x + (T a x - S x) ∈ W := by
    rw [hx_split]
    exact hsum_mem
  simpa using hmem

/-- Banach-Steinhaus turns pointwise boundedness of a family of tempered
distributions into the eventual equicontinuity-at-zero hypothesis used by the
dense boundary-value extension theorem.

This is the locally convex replacement for a normed operator-bound assumption
when the domain is a Schwartz space. -/
theorem tempered_eventually_equicontinuous_of_pointwise_bounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {α : Type*} {l : Filter α}
    {T : α → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f : SchwartzMap E F, ∃ C : ℝ, ∀ a : α, ‖T a f‖ ≤ C) :
    ∀ W ∈ nhds (0 : G), ∃ U ∈ nhds (0 : SchwartzMap E F),
      ∀ᶠ a in l, ∀ f ∈ U, T a f ∈ W := by
  classical
  obtain ⟨s, C, hCne, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound (E := E) (F := F) (G := G) hT
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast (show 0 < C from pos_iff_ne_zero.mpr hCne)
  let p : Seminorm ℝ (SchwartzMap E F) := s.sup (schwartzSeminormFamily ℝ E F)
  have hp_cont : Continuous p := by
    refine Seminorm.continuous_of_le ?_
      (show p ≤ ∑ i ∈ s, schwartzSeminormFamily ℝ E F i by
        simpa [p] using Seminorm.finset_sup_le_sum
          (schwartzSeminormFamily ℝ E F) s)
    change Continuous (fun x => Seminorm.coeFnAddMonoidHom ℝ (SchwartzMap E F)
      (∑ i ∈ s, schwartzSeminormFamily ℝ E F i) x)
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      (schwartz_withSeminorms ℝ E F).continuous_seminorm i
  intro W hW
  rcases Metric.mem_nhds_iff.mp hW with ⟨ε, hε, hεW⟩
  let δ : ℝ := ε / (2 * (C : ℝ))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  let U : Set (SchwartzMap E F) := {f | p f < δ}
  have hU : U ∈ nhds (0 : SchwartzMap E F) := by
    have hpre : p ⁻¹' Metric.ball (0 : ℝ) δ ∈ nhds (0 : SchwartzMap E F) := by
      have hp0 : p (0 : SchwartzMap E F) = 0 := by simp [p]
      exact hp_cont.continuousAt.preimage_mem_nhds (by
        simpa [hp0] using Metric.ball_mem_nhds (0 : ℝ) hδpos)
    refine mem_of_superset hpre ?_
    intro f hf
    have hpf_nonneg : 0 ≤ p f := apply_nonneg p f
    have hdist : dist (p f) 0 < δ := by simpa using hf
    simpa [U, Real.dist_eq, abs_of_nonneg hpf_nonneg] using hdist
  refine ⟨U, hU, ?_⟩
  filter_upwards [] with a f hf
  have hpf_lt : p f < δ := hf
  have hnorm_lt : ‖T a f‖ < ε := by
    calc
      ‖T a f‖ ≤ (C : ℝ) * p f := hbound a f
      _ < (C : ℝ) * δ := by nlinarith [hpf_lt, hCpos]
      _ = ε / 2 := by
        dsimp [δ]
        field_simp [show (C : ℝ) ≠ 0 by exact_mod_cast hCne]
      _ < ε := by linarith
  exact hεW (by simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt)

end SCV
