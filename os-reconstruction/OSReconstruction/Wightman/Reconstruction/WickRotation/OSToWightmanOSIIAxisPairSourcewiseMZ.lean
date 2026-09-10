/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZApproximation














noncomputable section

open Complex Topology MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- Exact producer contract for a source-parametric spatial flat cross.

Bounds may depend on the source tuple. They are used only to construct the
fixed-source normal-family limit; source continuity is recovered separately
from continuous multilinear Gaussian approximants. -/
structure OSIIAxisPairSourcewiseFlatCrossData (d k : ℕ) [NeZero d] where
  flatCross :
    (Fin k → SchwartzSpacetime d) → OSIIAxisPairFlatCrossData d
  realEdge :
    (osiiAxisPairIndex d → ℝ) →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin k => SchwartzSpacetime d) ℂ
  flatCross_realEdge :
    ∀ (fs : Fin k → SchwartzSpacetime d)
      (x : osiiAxisPairIndex d → ℝ),
      (flatCross fs).family.realEdge x = realEdge x fs
  realEdgeBound : (Fin k → SchwartzSpacetime d) → ℝ
  realEdge_bound :
    ∀ (fs : Fin k → SchwartzSpacetime d)
      (x : osiiAxisPairIndex d → ℝ),
      ‖(flatCross fs).family.realEdge x‖ ≤ realEdgeBound fs
  chartBound : (Fin k → SchwartzSpacetime d) → ℝ
  chartBound_pos :
    ∀ fs : Fin k → SchwartzSpacetime d, 0 < chartBound fs
  chart_bound :
    ∀ (fs : Fin k → SchwartzSpacetime d)
      (a : osiiAxisPairIndex d)
      (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
      |w.im| < Real.pi / 2 →
        ‖(flatCross fs).family.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤
            chartBound fs

namespace OSIIAxisPairSourcewiseFlatCrossData

/-- Assemble a source-parametric flat cross from spatially faithful semigroup
packet families.

The packet layer supplies the one-variable holomorphic branches and their
coherence. This adapter retains the common continuous multilinear real edge
and the fixed-source bounds consumed by Gaussian MZ continuation. -/
noncomputable def ofPacketFamilies
    {n m : ℕ} {T : ℝ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (packetFamily :
      (Fin k → SchwartzSpacetime d) →
        OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (packet_continuous :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (a : osiiAxisPairIndex d),
        ContinuousOn
          (fun p : (osiiAxisPairIndex d → ℝ) × ℂ =>
            ((packetFamily fs).packet p.1 a).branch OS lgc
              (Complex.exp p.2))
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}))
    (realEdge :
      (osiiAxisPairIndex d → ℝ) →
        ContinuousMultilinearMap ℂ
          (fun _ : Fin k => SchwartzSpacetime d) ℂ)
    (realEdge_eq :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (x : osiiAxisPairIndex d → ℝ),
        (packetFamily fs).realEdge x = realEdge x fs)
    (realEdgeBound : (Fin k → SchwartzSpacetime d) → ℝ)
    (realEdge_bound :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (x : osiiAxisPairIndex d → ℝ),
        ‖(packetFamily fs).realEdge x‖ ≤ realEdgeBound fs)
    (chartBound : (Fin k → SchwartzSpacetime d) → ℝ)
    (chartBound_pos :
      ∀ fs : Fin k → SchwartzSpacetime d, 0 < chartBound fs)
    (chart_bound :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (a : osiiAxisPairIndex d)
        (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
        |w.im| < Real.pi / 2 →
          ‖(packetFamily fs).toDirectionalBranchFamily.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤
              chartBound fs) :
    OSIIAxisPairSourcewiseFlatCrossData d k where
  flatCross := fun fs =>
    (packetFamily fs).toFlatCrossData_of_packet_continuous
      (packet_continuous fs)
  realEdge := realEdge
  flatCross_realEdge := by
    intro fs x
    exact realEdge_eq fs x
  realEdgeBound := realEdgeBound
  realEdge_bound := realEdge_bound
  chartBound := chartBound
  chartBound_pos := chartBound_pos
  chart_bound := chart_bound

end OSIIAxisPairSourcewiseFlatCrossData

namespace OSIIAxisPairSourcewiseMZFamily

set_option backward.isDefEq.respectTransparency false in
omit [NeZero d] in
/-- A pointwise limit of continuous linear functionals on Schwartz space is
continuous. The barrelled-space Banach-Steinhaus theorem is packaged by
`continuousLinearMapOfTendsto`. -/
theorem continuous_of_pointwise_tendsto_clm
    (T : ℕ → SchwartzSpacetime d →L[ℂ] ℂ)
    (f : SchwartzSpacetime d → ℂ)
    (hT : ∀ φ : SchwartzSpacetime d,
      Filter.Tendsto (fun n => T n φ) Filter.atTop (nhds (f φ))) :
    Continuous f := by
  have hTR :
      Filter.Tendsto
        (fun n φ => (T n).restrictScalars ℝ φ)
        Filter.atTop (nhds f) := by
    rw [tendsto_pi_nhds]
    intro φ
    simpa using hT φ
  let L : SchwartzSpacetime d →L[ℝ] ℂ :=
    continuousLinearMapOfTendsto
      (fun n => (T n).restrictScalars ℝ) hTR
  simpa [L, continuousLinearMapOfTendsto] using L.continuous

set_option backward.isDefEq.respectTransparency false in
omit [NeZero d] in
/-- A pointwise-bounded family of continuous linear Schwartz functionals can
be integrated against an integrable scalar kernel.  Banach-Steinhaus supplies
the locally uniform source bound needed by dominated convergence. -/
theorem continuous_integral_mul_of_pointwise_bounded_clm
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (K : α → ℂ)
    (T : α → SchwartzSpacetime d →L[ℂ] ℂ)
    (hK : Integrable (fun x => ‖K x‖) μ)
    (hT_meas : ∀ f : SchwartzSpacetime d,
      AEStronglyMeasurable (fun x => K x * T x f) μ)
    (hT_bounded : ∀ f : SchwartzSpacetime d,
      ∃ B : ℝ, ∀ x, ‖T x f‖ ≤ B) :
    Continuous (fun f : SchwartzSpacetime d =>
      ∫ x, K x * T x f ∂μ) := by
  have hT_vonN :
      ∀ f : SchwartzSpacetime d,
        Bornology.IsVonNBounded ℝ (Set.range fun x => T x f) := by
    intro f
    obtain ⟨B, hB⟩ := hT_bounded f
    exact (NormedSpace.isVonNBounded_iff' ℝ).2
      ⟨B, by
        intro z hz
        obtain ⟨x, rfl⟩ := hz
        exact hB x⟩
  have hT_equicont :
      Equicontinuous
        ((↑) ∘ fun x => (T x).restrictScalars ℝ) :=
    (PolynormableSpace.banach_steinhaus hT_vonN).equicontinuous
  rw [continuous_iff_continuousAt]
  intro f₀
  obtain ⟨B, hB⟩ := hT_bounded f₀
  apply continuousAt_of_dominated
      (bound := fun x => ‖K x‖ * (B + 1))
  · exact Filter.Eventually.of_forall hT_meas
  · filter_upwards
      [Metric.equicontinuousAt_iff_right.mp
        (hT_equicont f₀) 1 one_pos] with f hf
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      gcongr
      calc
        ‖T x f‖ ≤ ‖T x f - T x f₀‖ + ‖T x f₀‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ 1 + B := by
          have hdist := hf x
          rw [dist_comm, dist_eq_norm] at hdist
          exact add_le_add (le_of_lt hdist) (hB x)
        _ = B + 1 := add_comm _ _
  · exact hK.mul_const (B + 1)
  · exact Filter.Eventually.of_forall fun x =>
      continuousAt_const.mul (T x).continuous.continuousAt

set_option backward.isDefEq.respectTransparency false in
omit [NeZero d] in
/-- Gaussian specialization of
`continuous_integral_mul_of_pointwise_bounded_clm`. -/
theorem continuous_gaussianRegularization_of_pointwise_bounded_clm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (hc : 0 < c)
    (z : ι → ℂ)
    (T :
      EuclideanSpace ℝ ι →
        SchwartzSpacetime d →L[ℂ] ℂ)
    (hT_meas : ∀ f : SchwartzSpacetime d,
      AEStronglyMeasurable (fun x => T x f))
    (hT_bounded : ∀ f : SchwartzSpacetime d,
      ∃ B : ℝ, ∀ x, ‖T x f‖ ≤ B) :
    Continuous (fun f : SchwartzSpacetime d =>
      SCV.gaussianRegularization c (fun x => T x f) z) := by
  rw [show
    (fun f : SchwartzSpacetime d =>
      SCV.gaussianRegularization c (fun x => T x f) z) =
        fun f =>
          ∫ x, SCV.gaussianKernel c z x * T x f by
    funext f
    rfl]
  have hkernel :
      Integrable
        (fun x : EuclideanSpace ℝ ι =>
          SCV.gaussianKernel c z x) := by
    simpa using
      (SCV.integrable_gaussianKernel_mul_of_bounded
        c hc z
        (f := fun _ : EuclideanSpace ℝ ι => (1 : ℂ))
        (by fun_prop)
        1
        (by simp))
  apply continuous_integral_mul_of_pointwise_bounded_clm
      volume (SCV.gaussianKernel c z) T
  · exact hkernel.norm
  · intro f
    exact hkernel.1.mul (hT_meas f)
  · exact hT_bounded

/-- Integrating an integrable family of multilinear scalar maps preserves
algebraic multilinearity.  Continuity is supplied separately. -/
noncomputable def integralMultilinearMap
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α)
    (K : α → ℂ)
    (T : α →
      MultilinearMap ℂ
        (fun _ : ι => SchwartzSpacetime d) ℂ)
    (hInt : ∀ fs : ι → SchwartzSpacetime d,
      Integrable (fun x => K x * T x fs) μ) :
    MultilinearMap ℂ
      (fun _ : ι => SchwartzSpacetime d) ℂ where
  toFun := fun fs => ∫ x, K x * T x fs ∂μ
  map_update_add' := by
    intro hdec fs i f g
    letI := hdec
    rw [show
      (fun x => K x * T x (Function.update fs i (f + g))) =
        fun x =>
          K x * T x (Function.update fs i f) +
            K x * T x (Function.update fs i g) by
      funext x
      rw [(T x).map_update_add]
      ring]
    exact integral_add
      (hInt (Function.update fs i f))
      (hInt (Function.update fs i g))
  map_update_smul' := by
    intro hdec fs i c f
    letI := hdec
    rw [show
      (fun x => K x * T x (Function.update fs i (c • f))) =
        fun x => c • (K x * T x (Function.update fs i f)) by
      funext x
      rw [(T x).map_update_smul]
      simp [smul_eq_mul, mul_left_comm]]
    exact integral_smul c
      (fun x => K x * T x (Function.update fs i f))

end OSIIAxisPairSourcewiseMZFamily

namespace OSIIAxisPairSourcewiseFlatCrossData

namespace GaussianCMMFamily

/-- Real-valued Schwartz functions embedded into complex-valued Schwartz
functions. -/
noncomputable def complexifyRealSchwartz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    SchwartzMap E ℝ →L[ℝ] SchwartzMap E ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

/-- The `m`-th product-aware real Hermite basis vector on `k` spacetime
factors. -/
noncomputable def realProductHermite
    (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Fin k → Fin (d + 1) → ℝ) ℝ :=
  (GaussianField.productRapidDecayEquiv k hk).symm
    (GaussianField.RapidDecaySeq.basisVec m)

/-- The one-factor complex Hermite tests whose product is
`realProductHermite`. -/
noncomputable def productHermiteFactor
    (hk : 0 < k) (m : ℕ) (i : Fin k) :
    SchwartzSpacetime d :=
  complexifyRealSchwartz
    (GaussianField.DyninMityaginSpace.basis
      (E := SchwartzMap (Fin (d + 1) → ℝ) ℝ)
      (GaussianField.productBasisIndices
        (D := Fin (d + 1) → ℝ) k hk m i))

theorem complexifyRealSchwartz_realProductHermite
    (hk : 0 < k) (m : ℕ) :
    complexifyRealSchwartz (realProductHermite (d := d) hk m) =
      SchwartzMap.productTensor (productHermiteFactor (d := d) hk m) := by
  ext x
  have hreal :=
    GaussianField.productRapidDecayEquiv_symm_basisVec_isProductHermite
      k hk m x
  have hreal' :
      ((GaussianField.productRapidDecayEquiv
        (D := Fin (d + 1) → ℝ) k hk).symm
          (GaussianField.RapidDecaySeq.basisVec m)) x =
        ∏ i, GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap (Fin (d + 1) → ℝ) ℝ)
          (GaussianField.productBasisIndices
            (D := Fin (d + 1) → ℝ) k hk m i) (x i) := by
    exact hreal
  simp only [complexifyRealSchwartz, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, SchwartzMap.productTensor_apply,
    productHermiteFactor, realProductHermite]
  rw [hreal']
  simp

private theorem basis_growth_finset_sup_normTarget
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (s_idx : Finset
      (GaussianField.DyninMityaginSpace.ι (E := SchwartzMap D ℝ))) :
    ∃ C > 0, ∃ s : ℕ, ∀ m : ℕ,
      (s_idx.sup GaussianField.DyninMityaginSpace.p)
          (GaussianField.DyninMityaginSpace.basis
            (E := SchwartzMap D ℝ) m) ≤
        C * (1 + (m : ℝ)) ^ s := by
  induction s_idx using Finset.cons_induction with
  | empty =>
      exact ⟨1, one_pos, 0, fun m => by simp [Finset.sup_empty]⟩
  | cons a s_rest ha ih =>
      obtain ⟨C₁, hC₁, s₁, h₁⟩ :=
        GaussianField.DyninMityaginSpace.basis_growth
          (E := SchwartzMap D ℝ) a
      obtain ⟨C₂, hC₂, s₂, h₂⟩ := ih
      refine ⟨C₁ + C₂, by linarith, max s₁ s₂, fun m => ?_⟩
      rw [Finset.sup_cons]
      apply sup_le
      · calc
          GaussianField.DyninMityaginSpace.p a
              (GaussianField.DyninMityaginSpace.basis m)
              ≤ C₁ * (1 + (m : ℝ)) ^ s₁ := h₁ m
          _ ≤ C₁ * (1 + (m : ℝ)) ^ (max s₁ s₂ : ℕ) := by
            gcongr
            · linarith [Nat.cast_nonneg (α := ℝ) m]
            · exact Nat.le_max_left s₁ s₂
          _ ≤ (C₁ + C₂) * (1 + (m : ℝ)) ^ (max s₁ s₂ : ℕ) := by
            gcongr
            linarith
      · calc
          (s_rest.sup GaussianField.DyninMityaginSpace.p)
              (GaussianField.DyninMityaginSpace.basis m)
              ≤ C₂ * (1 + (m : ℝ)) ^ s₂ := h₂ m
          _ ≤ C₂ * (1 + (m : ℝ)) ^ (max s₁ s₂ : ℕ) := by
            gcongr
            · linarith [Nat.cast_nonneg (α := ℝ) m]
            · exact Nat.le_max_right s₁ s₂
          _ ≤ (C₁ + C₂) * (1 + (m : ℝ)) ^ (max s₁ s₂ : ℕ) := by
            gcongr
            linarith

/-- Continuous multilinear maps into a normed target have polynomial norm
growth on tuples of real Schwartz Hermite basis vectors. -/
theorem norm_multilinear_on_basis_bound
    {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ)
    (Φ : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => SchwartzMap D ℝ) G) :
    ∃ C > 0, ∃ s : ℕ, ∀ ks : Fin n → ℕ,
      ‖Φ (fun i =>
        GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap D ℝ) (ks i))‖ ≤
        C * ∏ i : Fin n, (1 + (ks i : ℝ)) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨‖Φ (fun i => Fin.elim0 i)‖ + 1, by positivity, 0, fun ks => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    have hks :
        (fun i : Fin 0 =>
          GaussianField.DyninMityaginSpace.basis
            (E := SchwartzMap D ℝ) (ks i)) =
          fun i : Fin 0 => Fin.elim0 i := by
      ext i
      exact Fin.elim0 i
    rw [hks]
    linarith [norm_nonneg (Φ (fun i => Fin.elim0 i))]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hPreimage :
        Φ ⁻¹' {x : G | ‖x‖ < 1} ∈
          nhds (0 : Fin n → SchwartzMap D ℝ) := by
      apply Φ.cont.continuousAt.preimage_mem_nhds
      show {x : G | ‖x‖ < 1} ∈ nhds (Φ 0)
      rw [Φ.map_zero]
      exact IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by simp)
    rw [nhds_pi, Filter.mem_pi] at hPreimage
    obtain ⟨w, _, t, ht_mem, ht_sub⟩ := hPreimage
    have hU_nhds :
        (⋂ i : Fin n, t i) ∈ nhds (0 : SchwartzMap D ℝ) :=
      Filter.iInter_mem.mpr fun i => ht_mem i
    rw [(GaussianField.DyninMityaginSpace.h_with
      (E := SchwartzMap D ℝ)).hasBasis_zero_ball.mem_iff] at hU_nhds
    obtain ⟨⟨sfin, δ⟩, hδ, hball_sub⟩ := hU_nhds
    change 0 < δ at hδ
    change
      (sfin.sup GaussianField.DyninMityaginSpace.p).ball 0 δ ⊆ _
        at hball_sub
    have h_ball :
        ∀ fs : Fin n → SchwartzMap D ℝ,
          (∀ i, (sfin.sup GaussianField.DyninMityaginSpace.p) (fs i) < δ) →
            ‖Φ fs‖ < 1 := by
      intro fs hfs
      have hfs_in_U : ∀ i, fs i ∈ ⋂ j : Fin n, t j := fun i =>
        hball_sub (by rw [Seminorm.mem_ball, sub_zero]; exact hfs i)
      exact ht_sub fun i _ => Set.mem_iInter.mp (hfs_in_U i) i
    obtain ⟨C_basis, hC_basis, s_basis, h_basis⟩ :=
      basis_growth_finset_sup_normTarget sfin
    refine
      ⟨(2 * (C_basis + 1) / δ) ^ n, by positivity, s_basis, fun ks => ?_⟩
    set q := sfin.sup GaussianField.DyninMityaginSpace.p
    set c : Fin n → ℝ := fun i =>
      2 * (q (GaussianField.DyninMityaginSpace.basis
        (E := SchwartzMap D ℝ) (ks i)) + 1) / δ
    set gs : Fin n → SchwartzMap D ℝ := fun i =>
      (c i)⁻¹ • GaussianField.DyninMityaginSpace.basis
        (E := SchwartzMap D ℝ) (ks i)
    have hc_pos : ∀ i, 0 < c i := fun i => by
      simp only [c]
      positivity
    have hc_ne : ∀ i, c i ≠ 0 := fun i => ne_of_gt (hc_pos i)
    have h_eq :
        (fun i =>
          GaussianField.DyninMityaginSpace.basis
            (E := SchwartzMap D ℝ) (ks i)) =
          fun i => c i • gs i := by
      ext i
      simp only [gs, smul_smul, mul_inv_cancel₀ (hc_ne i), one_smul]
    have hgs : ∀ i, q (gs i) < δ := by
      intro i
      simp only [gs, map_smul_eq_mul]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (hc_pos i).le)]
      set qi := q (GaussianField.DyninMityaginSpace.basis
        (E := SchwartzMap D ℝ) (ks i))
      have hqi : 0 ≤ qi := by positivity
      rw [show c i = 2 * (qi + 1) / δ from rfl, inv_div]
      calc
        δ / (2 * (qi + 1)) * qi =
            δ * qi / (2 * (qi + 1)) := by ring
        _ < δ * (qi + 1) / (2 * (qi + 1)) :=
          div_lt_div_of_pos_right (by nlinarith) (by positivity)
        _ = δ / 2 := by
          rw [mul_div_mul_right _ _
            (show (0 : ℝ) < qi + 1 by linarith).ne']
        _ < δ := by linarith
    have hΦ_gs : ‖Φ gs‖ < 1 := h_ball gs hgs
    rw [h_eq, Φ.map_smul_univ c gs, norm_smul]
    have h_prod_pos : 0 < ∏ i, c i :=
      Finset.prod_pos fun i _ => hc_pos i
    rw [Real.norm_eq_abs, abs_of_pos h_prod_pos]
    calc
      (∏ i, c i) * ‖Φ gs‖ ≤ (∏ i, c i) * 1 :=
        mul_le_mul_of_nonneg_left hΦ_gs.le h_prod_pos.le
      _ = ∏ i : Fin n, c i := mul_one _
      _ ≤ ∏ i : Fin n,
          (2 * (C_basis + 1) / δ *
            (1 + (ks i : ℝ)) ^ s_basis) := by
        apply Finset.prod_le_prod
          (fun i _ => (hc_pos i).le)
          (fun i _ => ?_)
        show
          2 * (q (GaussianField.DyninMityaginSpace.basis (ks i)) + 1) / δ ≤
            2 * (C_basis + 1) / δ *
              (1 + (ks i : ℝ)) ^ s_basis
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hδ.le
        have hx : (1 : ℝ) ≤ (1 + (ks i : ℝ)) ^ s_basis :=
          one_le_pow₀
            (le_add_of_nonneg_right (Nat.cast_nonneg (ks i)))
        nlinarith [h_basis (ks i)]
      _ = (2 * (C_basis + 1) / δ) ^ n *
          ∏ i : Fin n, (1 + (ks i : ℝ)) ^ s_basis := by
        rw [show
          (fun i =>
            2 * (C_basis + 1) / δ *
              (1 + (ks i : ℝ)) ^ s_basis) =
            fun i =>
              (fun _ : Fin n => 2 * (C_basis + 1) / δ) i *
                (1 + (ks i : ℝ)) ^ s_basis from rfl,
          Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]

/-- Polynomially encoded Hermite indices give polynomial norm growth for any
continuous multilinear map into a normed real target. -/
theorem norm_multilinear_on_basis_polyBounded
    {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ)
    (Φ : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => SchwartzMap D ℝ) G)
    (βs : ℕ → Fin n → ℕ)
    (hβ : ∃ D_enc > 0, ∃ q : ℕ, ∀ m i,
      (βs m i : ℝ) ≤ D_enc * (1 + (m : ℝ)) ^ q) :
    ∃ C > 0, ∃ p : ℕ, ∀ m,
      ‖Φ (fun i =>
        GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap D ℝ) (βs m i))‖ ≤
        C * (1 + (m : ℝ)) ^ p := by
  obtain ⟨C, hC, s, h_bound⟩ :=
    norm_multilinear_on_basis_bound n Φ
  obtain ⟨D_enc, hD, q, hβ_bound⟩ := hβ
  refine
    ⟨C * (D_enc + 1) ^ (n * s), by positivity, n * s * q, fun m => ?_⟩
  have h_base : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ q :=
    one_le_pow₀ (by
      linarith [Nat.cast_nonneg (α := ℝ) m] :
        (1 : ℝ) ≤ 1 + (m : ℝ))
  set A := (D_enc + 1) * (1 + (m : ℝ)) ^ q
  have hA : 0 < A := by positivity
  have h_each :
      ∀ i, (1 + (βs m i : ℝ)) ^ s ≤ A ^ s := by
    intro i
    apply pow_le_pow_left₀ (by positivity)
    calc
      (1 : ℝ) + (βs m i : ℝ)
          ≤ 1 + D_enc * (1 + (m : ℝ)) ^ q := by
            linarith [hβ_bound m i]
      _ ≤ (D_enc + 1) * (1 + (m : ℝ)) ^ q := by
        nlinarith
  calc
    ‖Φ (fun i =>
      GaussianField.DyninMityaginSpace.basis (βs m i))‖
        ≤ C * ∏ i : Fin n, (1 + (βs m i : ℝ)) ^ s :=
      h_bound (βs m)
    _ ≤ C * ∏ _i : Fin n, A ^ s :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod
          (fun i _ => by positivity)
          (fun i _ => h_each i))
        hC.le
    _ = C * A ^ (Finset.card (Finset.univ : Finset (Fin n)) * s) := by
      rw [Finset.prod_const]
      ring
    _ = C * A ^ (n * s) := by rw [Finset.card_fin]
    _ = C * (D_enc + 1) ^ (n * s) *
        (1 + (m : ℝ)) ^ (n * s * q) := by
      rw [show A = (D_enc + 1) * (1 + (m : ℝ)) ^ q from rfl,
        mul_pow, ← pow_mul]
      ring

noncomputable def realPartSchwartz :
    SchwartzNPoint d k →L[ℝ]
      SchwartzMap (Fin k → Fin (d + 1) → ℝ) ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM

noncomputable def imaginaryPartSchwartz :
    SchwartzNPoint d k →L[ℝ]
      SchwartzMap (Fin k → Fin (d + 1) → ℝ) ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM

theorem complexifyRealSchwartz_realPart_add_I_imaginaryPart
    (f : SchwartzNPoint d k) :
    complexifyRealSchwartz (realPartSchwartz f) +
        Complex.I • complexifyRealSchwartz (imaginaryPartSchwartz f) =
      f := by
  ext x
  simp only [complexifyRealSchwartz, realPartSchwartz,
    imaginaryPartSchwartz, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (f x)

end GaussianCMMFamily

end OSIIAxisPairSourcewiseFlatCrossData

end OSReconstruction
