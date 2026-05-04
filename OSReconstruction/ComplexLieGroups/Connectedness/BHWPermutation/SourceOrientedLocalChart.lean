import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankBridge

/-!
# Local chart packets for the oriented source variety

This file records the topology/continuity layer used by the strict BHW/Jost
source-patch route.  The analytic chart producers remain separate; the results
here say that once such a local inverse chart is available, it yields a small
connected relatively open patch in the oriented source variety.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace SCV

/-- Finite-dimensional SCV identity theorem in the form used by local chart
arguments: a holomorphic scalar on a connected open coordinate domain which
vanishes on a nonempty relatively open subset vanishes everywhere. -/
theorem identity_theorem_connected_open_zero
    {m : ℕ}
    {Ω R : Set (Fin m → ℂ)}
    {φ : (Fin m → ℂ) → ℂ}
    (hΩ_open : IsOpen Ω)
    (hΩ_conn : IsConnected Ω)
    (hφ : DifferentiableOn ℂ φ Ω)
    (hR_relOpen : ∃ O, IsOpen O ∧ R = O ∩ Ω)
    (hR_ne : R.Nonempty)
    (hzero : Set.EqOn φ 0 R) :
    Set.EqOn φ 0 Ω := by
  classical
  rcases hR_ne with ⟨z0, hz0R⟩
  rcases hR_relOpen with ⟨O, hO_open, hR_eq⟩
  have hz0OΩ : z0 ∈ O ∩ Ω := by
    simpa [hR_eq] using hz0R
  have hzero_eventually :
      φ =ᶠ[𝓝 z0] (0 : (Fin m → ℂ) → ℂ) := by
    filter_upwards [(hO_open.inter hΩ_open).mem_nhds hz0OΩ] with z hz
    exact hzero (by
      rw [hR_eq]
      exact hz)
  exact identity_theorem_SCV hΩ_open hΩ_conn hφ
    (differentiableOn_const (0 : ℂ)) hz0OΩ.2 hzero_eventually

end SCV

namespace BHW

variable {d n : ℕ}

/-- A local inverse chart on an oriented-source-variety patch.  The model space
is an explicit parameter, rather than a bundled field, so downstream lemmas can
use the normed-space instances directly. -/
structure LocalBiholomorphOnSourceOrientedVariety
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    (Ω : Set (SourceOrientedGramData d n))
    (chart : SourceOrientedGramData d n → M) where
  inv : M → SourceOrientedGramData d n
  left_inv_on : ∀ G ∈ Ω, inv (chart G) = G
  right_inv_on : ∀ y ∈ chart '' Ω, chart (inv y) = y
  inv_mem_on : ∀ y ∈ chart '' Ω, inv y ∈ Ω
  chart_continuousOn : ContinuousOn chart Ω
  inv_differentiableOn : DifferentiableOn ℂ inv (chart '' Ω)
  inv_continuousOn : ContinuousOn inv (chart '' Ω)

/-- A differentiability-on set can be proved from local differentiable models
which agree with the target function on each local patch. -/
theorem differentiableOn_of_local_agreement
    {M N : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N]
    {V : Set M}
    {f : M → N}
    (hlocal :
      ∀ y ∈ V, ∃ O φ,
        IsOpen O ∧ y ∈ O ∧
        DifferentiableOn ℂ φ (O ∩ V) ∧
        Set.EqOn f φ (O ∩ V)) :
    DifferentiableOn ℂ f V := by
  refine differentiableOn_of_locally_differentiableOn ?_
  intro y hyV
  rcases hlocal y hyV with ⟨O, φ, hO_open, hyO, hφ, hEq⟩
  refine ⟨O, hO_open, hyO, ?_⟩
  have hφ' : DifferentiableOn ℂ φ (V ∩ O) := by
    simpa [Set.inter_comm] using hφ
  exact hφ'.congr (by
    intro z hz
    exact hEq ⟨hz.2, hz.1⟩)

namespace LocalBiholomorphOnSourceOrientedVariety

/-- Restricting the source patch also restricts inverse membership. -/
theorem inv_mem_restrict
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {Ω Ω0 : Set (SourceOrientedGramData d n)}
    {chart : SourceOrientedGramData d n → M}
    (hchart :
      LocalBiholomorphOnSourceOrientedVariety d n Ω0 chart)
    (hΩ_sub : Ω ⊆ Ω0) :
    ∀ y ∈ chart '' Ω, hchart.inv y ∈ Ω := by
  rintro y ⟨G, hGΩ, rfl⟩
  simpa [hchart.left_inv_on G (hΩ_sub hGΩ)]

/-- The inverse image of a model-open set contained in the chart image is
relatively open in the oriented source variety. -/
theorem inv_image_open_relOpen
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {Ω : Set (SourceOrientedGramData d n)}
    {chart : SourceOrientedGramData d n → M}
    (hΩ_rel : IsRelOpenInSourceOrientedGramVariety d n Ω)
    (hchart : LocalBiholomorphOnSourceOrientedVariety d n Ω chart)
    {O : Set M}
    (hO_open : IsOpen O)
    (hO_sub : O ⊆ chart '' Ω) :
    IsRelOpenInSourceOrientedGramVariety d n (hchart.inv '' O) := by
  classical
  let invFun : M → SourceOrientedGramData d n := hchart.inv
  rcases hΩ_rel with ⟨UΩ, hUΩ_open, hΩ_eq⟩
  rcases (continuousOn_iff'.mp hchart.chart_continuousOn) O hO_open with
    ⟨Uchart, hUchart_open, hpre_eq⟩
  refine ⟨Uchart ∩ UΩ, hUchart_open.inter hUΩ_open, ?_⟩
  ext G
  constructor
  · rintro ⟨y, hyO, hGy⟩
    subst hGy
    have hyim : y ∈ chart '' Ω := hO_sub hyO
    have hinvΩ : invFun y ∈ Ω := hchart.inv_mem_on y hyim
    have hpre : invFun y ∈ chart ⁻¹' O := by
      simpa [invFun, hchart.right_inv_on y hyim] using hyO
    have hleft : invFun y ∈ Uchart ∩ Ω := by
      rw [← hpre_eq]
      exact ⟨hpre, hinvΩ⟩
    have hinvΩ_as :
        invFun y ∈ UΩ ∩ sourceOrientedGramVariety d n := by
      simpa [hΩ_eq] using hinvΩ
    exact ⟨⟨hleft.1, hinvΩ_as.1⟩, hinvΩ_as.2⟩
  · intro hG
    have hGΩ : G ∈ Ω := by
      simpa [hΩ_eq] using
        (show G ∈ UΩ ∩ sourceOrientedGramVariety d n from
          ⟨hG.1.2, hG.2⟩)
    have hpre_inter : G ∈ chart ⁻¹' O ∩ Ω := by
      rw [hpre_eq]
      exact ⟨hG.1.1, hGΩ⟩
    refine ⟨chart G, hpre_inter.1, ?_⟩
    exact hchart.left_inv_on G hGΩ

/-- A germ-holomorphic oriented source scalar pulls back to a differentiable
function in any local chart coordinates. -/
theorem germ_to_chart
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {Ω Ω0 U : Set (SourceOrientedGramData d n)}
    {chart : SourceOrientedGramData d n → M}
    {Φ : SourceOrientedGramData d n → ℂ}
    (hchart : LocalBiholomorphOnSourceOrientedVariety d n Ω0 chart)
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (hΩ_rel : IsRelOpenInSourceOrientedGramVariety d n Ω)
    (hΩ_sub_U : Ω ⊆ U)
    (hΩ_sub_chart : Ω ⊆ Ω0) :
    DifferentiableOn ℂ
      (fun y => Φ (hchart.inv y)) (chart '' Ω) := by
  classical
  refine differentiableOn_of_local_agreement ?_
  intro y hyV
  have hyV0 : y ∈ chart '' Ω0 :=
    Set.mem_of_subset_of_mem (Set.image_mono hΩ_sub_chart) hyV
  have hinvΩ : hchart.inv y ∈ Ω :=
    LocalBiholomorphOnSourceOrientedVariety.inv_mem_restrict
      (d := d) (n := n) hchart hΩ_sub_chart y hyV
  rcases hΦ (hchart.inv y) (hΩ_sub_U hinvΩ) with
    ⟨U0, Ψ, hU0_open, hInvU0, hΨ_holo, hEq, _hU0_sub⟩
  rcases (continuousOn_iff.mp hchart.inv_continuousOn)
      y hyV0 U0 hU0_open hInvU0 with
    ⟨O, hO_open, hyO, hO_sub⟩
  refine ⟨O, fun y' => Ψ (hchart.inv y'), hO_open, hyO, ?_, ?_⟩
  · exact
      hΨ_holo.comp
        (hchart.inv_differentiableOn.mono
          (by
            intro y' hy'
            exact Set.mem_of_subset_of_mem
              (Set.image_mono hΩ_sub_chart) hy'.2))
        (by
          intro y' hy'
          exact hO_sub ⟨hy'.1, Set.mem_of_subset_of_mem
            (Set.image_mono hΩ_sub_chart) hy'.2⟩)
  · intro y' hy'
    have hinvΩ' : hchart.inv y' ∈ Ω :=
      LocalBiholomorphOnSourceOrientedVariety.inv_mem_restrict
        (d := d) (n := n) hchart hΩ_sub_chart y' hy'.2
    have hinvVar : hchart.inv y' ∈ sourceOrientedGramVariety d n :=
      IsRelOpenInSourceOrientedGramVariety.subset hΩ_rel hinvΩ'
    exact
      hEq
        ⟨hO_sub ⟨hy'.1, Set.mem_of_subset_of_mem
          (Set.image_mono hΩ_sub_chart) hy'.2⟩,
          hinvVar⟩

/-- A relatively open subpatch of a chart domain maps to a relatively open set
inside the corresponding model-coordinate chart image. -/
theorem image_relOpenIn_chart
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {Ω Ω0 S : Set (SourceOrientedGramData d n)}
    {chart : SourceOrientedGramData d n → M}
    (hchart : LocalBiholomorphOnSourceOrientedVariety d n Ω0 chart)
    (hΩ_sub : Ω ⊆ Ω0)
    (hS_rel : ∃ O, IsOpen O ∧ S = O ∩ Ω) :
    ∃ Ochart : Set M,
      IsOpen Ochart ∧ chart '' S = Ochart ∩ chart '' Ω := by
  classical
  rcases hS_rel with ⟨O, hO_open, hS_eq⟩
  have himage_sub : chart '' Ω ⊆ chart '' Ω0 := Set.image_mono hΩ_sub
  rcases (continuousOn_iff'.mp
      (hchart.inv_continuousOn.mono himage_sub)) O hO_open with
    ⟨Ochart, hOchart_open, hpre_eq⟩
  refine ⟨Ochart, hOchart_open, ?_⟩
  ext y
  constructor
  · rintro ⟨G, hGS, rfl⟩
    have hGΩO : G ∈ O ∩ Ω := by
      simpa [hS_eq] using hGS
    have hyΩ : chart G ∈ chart '' Ω := ⟨G, hGΩO.2, rfl⟩
    have hy_pre : chart G ∈ hchart.inv ⁻¹' O ∩ chart '' Ω := by
      constructor
      · simpa [hchart.left_inv_on G (hΩ_sub hGΩO.2)] using hGΩO.1
      · exact hyΩ
    have hy_U : chart G ∈ Ochart := by
      have hy_UΩ : chart G ∈ Ochart ∩ chart '' Ω := by
        rw [← hpre_eq]
        exact hy_pre
      exact hy_UΩ.1
    exact ⟨hy_U, hyΩ⟩
  · intro hy
    rcases hy.2 with ⟨G, hGΩ, rfl⟩
    have hy_pre : chart G ∈ hchart.inv ⁻¹' O ∩ chart '' Ω := by
      rw [hpre_eq]
      exact hy
    have hGO : G ∈ O := by
      simpa [hchart.left_inv_on G (hΩ_sub hGΩ)] using hy_pre.1
    refine ⟨G, ?_, rfl⟩
    rw [hS_eq]
    exact ⟨hGO, hGΩ⟩

/-- Postcompose the model-coordinate chart by a continuous linear equivalence.
This keeps the same source patch and transports the local inverse through the
inverse coordinate equivalence. -/
noncomputable def postcomp_continuousLinearEquiv
    {M N : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N]
    {Ω : Set (SourceOrientedGramData d n)}
    {chart : SourceOrientedGramData d n → M}
    (hchart : LocalBiholomorphOnSourceOrientedVariety d n Ω chart)
    (e : M ≃L[ℂ] N) :
    LocalBiholomorphOnSourceOrientedVariety d n Ω
      (fun G => e (chart G)) := by
  classical
  let chart' : SourceOrientedGramData d n → N := fun G => e (chart G)
  let inv' : N → SourceOrientedGramData d n := fun y => hchart.inv (e.symm y)
  have himage_eq : chart' '' Ω = e '' (chart '' Ω) := by
    ext y
    constructor
    · rintro ⟨G, hGΩ, rfl⟩
      exact ⟨chart G, ⟨G, hGΩ, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨G, hGΩ, rfl⟩, rfl⟩
      exact ⟨G, hGΩ, rfl⟩
  refine
    { inv := inv'
      left_inv_on := ?_
      right_inv_on := ?_
      inv_mem_on := ?_
      chart_continuousOn := ?_
      inv_differentiableOn := ?_
      inv_continuousOn := ?_ }
  · intro G hGΩ
    simp [inv', hchart.left_inv_on G hGΩ]
  · intro y hy
    rcases hy with ⟨G, hGΩ, rfl⟩
    simp [inv', hchart.left_inv_on G hGΩ]
  · intro y hy
    rcases hy with ⟨G, hGΩ, rfl⟩
    simp [inv', hchart.left_inv_on G hGΩ, hGΩ]
  · change ContinuousOn (e ∘ chart) Ω
    exact e.continuous.comp_continuousOn hchart.chart_continuousOn
  · change DifferentiableOn ℂ inv' (chart' '' Ω)
    rw [himage_eq]
    exact hchart.inv_differentiableOn.comp
      (e.symm.differentiableOn)
      (by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        simp [hx])
  · change ContinuousOn inv' (chart' '' Ω)
    rw [himage_eq]
    exact hchart.inv_continuousOn.comp
      (e.symm.continuous.continuousOn)
      (by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        simp [hx])

end LocalBiholomorphOnSourceOrientedVariety

/-- A connected local patch of the oriented source variety around a chosen
center. -/
structure SourceOrientedVarietyLocalConnectedPatchData
    (d n : ℕ)
    (G0 : SourceOrientedGramData d n) where
  V : Set (SourceOrientedGramData d n)
  center_mem : G0 ∈ V
  V_relOpen : IsRelOpenInSourceOrientedGramVariety d n V
  V_connected : IsConnected V

/-- Every point in an open domain of a complex normed vector space has a small
connected ball on which a continuous local inverse remains inside a prescribed
ambient-open target. -/
theorem exists_connected_ball_in_localInverse_domain
    {M E : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [TopologicalSpace E]
    {Dom : Set M}
    {inv : M → E}
    {y0 : M}
    {N0 : Set E}
    (hDom_open : IsOpen Dom)
    (hy0Dom : y0 ∈ Dom)
    (hinv_cont : ContinuousOn inv Dom)
    (hN0_open : IsOpen N0)
    (hy0N0 : inv y0 ∈ N0) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball y0 ε ⊆ Dom ∧
      (∀ y ∈ Metric.ball y0 ε, inv y ∈ N0) ∧
      IsConnected (Metric.ball y0 ε) := by
  classical
  rcases Metric.isOpen_iff.mp hDom_open y0 hy0Dom with
    ⟨εD, hεD, hballD⟩
  rcases
    (continuousOn_iff.mp hinv_cont)
      y0 hy0Dom N0 hN0_open hy0N0 with
    ⟨O, hO_open, hy0O, hO_sub⟩
  rcases Metric.isOpen_iff.mp hO_open y0 hy0O with
    ⟨εO, hεO, hballO⟩
  let ε := min εD εO
  have hε : 0 < ε := lt_min hεD hεO
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · intro y hy
    have hyD : y ∈ Metric.ball y0 εD := by
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _))
    exact hballD hyD
  · intro y hy
    have hyO : y ∈ Metric.ball y0 εO := by
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hyD : y ∈ Metric.ball y0 εD := by
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _))
    exact hO_sub ⟨hballO hyO, hballD hyD⟩
  · exact (convex_ball y0 ε).isConnected
      ⟨y0, Metric.mem_ball_self hε⟩

/-- Max-rank local chart data for the oriented source variety.  The actual
full-frame/small-arity producers are downstream; this packet captures the
topological chart consequences needed by the local connected-basis proof. -/
structure SourceOrientedMaxRankChartData
    (d n : ℕ)
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    (G0 : SourceOrientedGramData d n) where
  Ω : Set (SourceOrientedGramData d n)
  Ω_relOpen : IsRelOpenInSourceOrientedGramVariety d n Ω
  center_mem : G0 ∈ Ω
  Ω_maxRank : Ω ⊆ {G | SourceOrientedMaxRankAt d n G}
  chart : SourceOrientedGramData d n → M
  chart_open : IsOpen (chart '' Ω)
  chart_biholomorphic :
    LocalBiholomorphOnSourceOrientedVariety d n Ω chart

namespace SourceOrientedVarietyGermHolomorphicOn

/-- On a max-rank local chart patch, a germ-holomorphic oriented source scalar
has a differentiable model-coordinate representative. -/
theorem to_maxRank_chart
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    {Φ : SourceOrientedGramData d n → ℂ}
    {U Ω : Set (SourceOrientedGramData d n)}
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ U)
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    (hΩ_rel : IsRelOpenInSourceOrientedGramVariety d n Ω)
    (hΩ_sub : Ω ⊆ U)
    (hΩ_sub_chart : Ω ⊆ C.Ω) :
    ∃ φc : M → ℂ,
      DifferentiableOn ℂ φc (C.chart '' Ω) ∧
      ∀ G ∈ Ω, φc (C.chart G) = Φ G := by
  let φc : M → ℂ := fun y => Φ (C.chart_biholomorphic.inv y)
  refine ⟨φc, ?_, ?_⟩
  · exact
      LocalBiholomorphOnSourceOrientedVariety.germ_to_chart
        (d := d) (n := n)
        (Ω := Ω) (Ω0 := C.Ω) (U := U)
        (chart := C.chart) (Φ := Φ)
        C.chart_biholomorphic hΦ hΩ_rel hΩ_sub hΩ_sub_chart
  · intro G hGΩ
    simp [φc, C.chart_biholomorphic.left_inv_on G (hΩ_sub_chart hGΩ)]

end SourceOrientedVarietyGermHolomorphicOn

/-- A noncomputable coordinate equivalence from any finite-dimensional complex
normed vector space to its `Fin finrank` coordinate model. -/
noncomputable def finiteDimensionalCoordinateEquiv
    (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M]
    [FiniteDimensional ℂ M] :
    M ≃L[ℂ] (Fin (Module.finrank ℂ M) → ℂ) :=
  ((Module.finBasis ℂ M).equivFun).toContinuousLinearEquiv

namespace SourceOrientedMaxRankChartData

/-- Postcompose a max-rank chart by a continuous linear coordinate equivalence.
This lets analytic chart producers use their natural finite product/slice model
while the identity theorem consumes a concrete coordinate model. -/
noncomputable def postcomp_continuousLinearEquiv
    {M N : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    (e : M ≃L[ℂ] N) :
    SourceOrientedMaxRankChartData d n (M := N) G0 := by
  let chart' : SourceOrientedGramData d n → N := fun G => e (C.chart G)
  have himage_eq : chart' '' C.Ω = e '' (C.chart '' C.Ω) := by
    ext y
    constructor
    · rintro ⟨G, hGΩ, rfl⟩
      exact ⟨C.chart G, ⟨G, hGΩ, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨G, hGΩ, rfl⟩, rfl⟩
      exact ⟨G, hGΩ, rfl⟩
  refine
    { Ω := C.Ω
      Ω_relOpen := C.Ω_relOpen
      center_mem := C.center_mem
      Ω_maxRank := C.Ω_maxRank
      chart := chart'
      chart_open := ?_
      chart_biholomorphic := ?_ }
  · rw [himage_eq]
    exact e.isOpenMap _ C.chart_open
  · exact C.chart_biholomorphic.postcomp_continuousLinearEquiv e

/-- Specialize a max-rank chart to a concrete finite coordinate model. -/
noncomputable def to_finiteCoordinateChart
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {m : ℕ} (e : M ≃L[ℂ] (Fin m → ℂ)) :
    SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0 :=
  C.postcomp_continuousLinearEquiv e

/-- Any finite-dimensional max-rank chart can be put in its `Fin finrank`
coordinate model. -/
noncomputable def to_finrankCoordinateChart
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [FiniteDimensional ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0) :
    SourceOrientedMaxRankChartData d n
      (M := Fin (Module.finrank ℂ M) → ℂ) G0 :=
  C.to_finiteCoordinateChart (finiteDimensionalCoordinateEquiv M)

/-- The inverse chart has a small connected coordinate ball around the center
which remains inside any prescribed ambient-open neighborhood of the center. -/
theorem exists_connected_chartBall
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (C.chart G0) ε ⊆ C.chart '' C.Ω ∧
      (∀ y ∈ Metric.ball (C.chart G0) ε,
        C.chart_biholomorphic.inv y ∈ N0) ∧
      IsConnected (Metric.ball (C.chart G0) ε) := by
  exact
    exists_connected_ball_in_localInverse_domain
      C.chart_open
      ⟨G0, C.center_mem, rfl⟩
      C.chart_biholomorphic.inv_continuousOn
      hN0_open
      (by
        simpa [C.chart_biholomorphic.left_inv_on G0 C.center_mem]
          using hG0N0)

/-- Pulling a coordinate ball back through a local inverse gives a relatively
open oriented-source-variety patch. -/
theorem inv_image_openBall_relOpen
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {ε : ℝ}
    (hball : Metric.ball (C.chart G0) ε ⊆ C.chart '' C.Ω) :
    IsRelOpenInSourceOrientedGramVariety d n
      (C.chart_biholomorphic.inv '' Metric.ball (C.chart G0) ε) := by
  exact
    LocalBiholomorphOnSourceOrientedVariety.inv_image_open_relOpen
      (d := d) (n := n)
      C.Ω_relOpen C.chart_biholomorphic Metric.isOpen_ball hball

/-- A max-rank chart produces a connected relatively open local patch inside
any ambient-open neighborhood of its center. -/
theorem connectedPatch_inside_open
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ P : SourceOrientedVarietyLocalConnectedPatchData d n G0,
      P.V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  classical
  rcases C.exists_connected_chartBall hN0_open hG0N0 with
    ⟨ε, hε, hball_dom, hball_N0, hball_conn⟩
  let B : Set M := Metric.ball (C.chart G0) ε
  let V : Set (SourceOrientedGramData d n) :=
    C.chart_biholomorphic.inv '' B
  have hcenter : G0 ∈ V := by
    refine ⟨C.chart G0, ?_, ?_⟩
    · exact Metric.mem_ball_self hε
    · exact C.chart_biholomorphic.left_inv_on G0 C.center_mem
  have hrel : IsRelOpenInSourceOrientedGramVariety d n V := by
    exact C.inv_image_openBall_relOpen hball_dom
  have hconn : IsConnected V := by
    have hcont : ContinuousOn C.chart_biholomorphic.inv B :=
      C.chart_biholomorphic.inv_continuousOn.mono hball_dom
    simpa [V, B] using hball_conn.image C.chart_biholomorphic.inv hcont
  have hsub : V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
    rintro G ⟨y, hyB, rfl⟩
    constructor
    · exact hball_N0 y hyB
    · exact IsRelOpenInSourceOrientedGramVariety.subset C.Ω_relOpen
        (C.chart_biholomorphic.inv_mem_on y (hball_dom hyB))
  exact
    ⟨{ V := V
       center_mem := hcenter
       V_relOpen := hrel
       V_connected := hconn }, hsub⟩

/-- Shrink a max-rank local chart around the center so that the shrunken patch
is relatively open, stays in a prescribed relatively open set, and has an open
connected model-coordinate image. -/
theorem shrink_to_relOpen
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hG0U : G0 ∈ U) :
    ∃ Ω : Set (SourceOrientedGramData d n),
      G0 ∈ Ω ∧
      IsRelOpenInSourceOrientedGramVariety d n Ω ∧
      Ω ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Ω ⊆ C.Ω ∧
      IsOpen (C.chart '' Ω) ∧
      IsConnected (C.chart '' Ω) := by
  classical
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  have hG0U0var :
      G0 ∈ U0 ∩ sourceOrientedGramVariety d n := by
    simpa [hU_eq] using hG0U
  rcases C.exists_connected_chartBall hU0_open hG0U0var.1 with
    ⟨ε, hε, hball_dom, hball_U0, hball_conn⟩
  let B : Set M := Metric.ball (C.chart G0) ε
  let Ωsmall : Set (SourceOrientedGramData d n) :=
    C.chart_biholomorphic.inv '' B
  have hcenter : G0 ∈ Ωsmall := by
    refine ⟨C.chart G0, ?_, ?_⟩
    · exact Metric.mem_ball_self hε
    · exact C.chart_biholomorphic.left_inv_on G0 C.center_mem
  have hrel : IsRelOpenInSourceOrientedGramVariety d n Ωsmall := by
    exact C.inv_image_openBall_relOpen hball_dom
  have hΩC : Ωsmall ⊆ C.Ω := by
    rintro G ⟨y, hyB, rfl⟩
    exact C.chart_biholomorphic.inv_mem_on y (hball_dom hyB)
  have hsub :
      Ωsmall ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} := by
    rintro G ⟨y, hyB, rfl⟩
    have hinvCΩ : C.chart_biholomorphic.inv y ∈ C.Ω :=
      C.chart_biholomorphic.inv_mem_on y (hball_dom hyB)
    have hinvVar :
        C.chart_biholomorphic.inv y ∈ sourceOrientedGramVariety d n :=
      IsRelOpenInSourceOrientedGramVariety.subset C.Ω_relOpen hinvCΩ
    constructor
    · rw [hU_eq]
      exact ⟨hball_U0 y hyB, hinvVar⟩
    · exact C.Ω_maxRank hinvCΩ
  have hchart_image_eq : C.chart '' Ωsmall = B := by
    ext y
    constructor
    · rintro ⟨G, hGΩ, rfl⟩
      rcases hGΩ with ⟨x, hxB, rfl⟩
      simpa [C.chart_biholomorphic.right_inv_on x (hball_dom hxB)]
        using hxB
    · intro hyB
      refine ⟨C.chart_biholomorphic.inv y, ⟨y, hyB, rfl⟩, ?_⟩
      exact C.chart_biholomorphic.right_inv_on y (hball_dom hyB)
  refine ⟨Ωsmall, hcenter, hrel, hsub, hΩC, ?_, ?_⟩
  · rw [hchart_image_eq]
    exact Metric.isOpen_ball
  · rw [hchart_image_eq]
    exact hball_conn

/-- Local identity step at a max-rank point, assuming the supplied local chart
uses a finite coordinate model.  This is the chart-local analytic continuation
piece used by the max-rank branch of the oriented source-variety identity
principle. -/
theorem local_identity_near_point
    {m : ℕ}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
    {U A : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_relOpen : IsRelOpenInSourceOrientedGramVariety d n U)
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (hG0U : G0 ∈ U)
    (hA_rel :
      ∃ A0, IsOpen A0 ∧
        A = A0 ∩ (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hG0cl : G0 ∈ closure A)
    (hA_zero : Set.EqOn H 0 A) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      V ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn H 0 V := by
  classical
  obtain ⟨Ω, hG0Ω, hΩ_rel, hΩ_sub_Umax, hΩ_sub_C,
    hΩ_chart_open, hΩ_chart_conn⟩ := C.shrink_to_relOpen hU_relOpen hG0U
  obtain ⟨φc, hφc_holo, hφc_eq⟩ :=
    SourceOrientedVarietyGermHolomorphicOn.to_maxRank_chart
      (d := d) (n := n) hH C hΩ_rel
      (by intro G hGΩ; exact (hΩ_sub_Umax hGΩ).1)
      hΩ_sub_C
  rcases hA_rel with ⟨A0, hA0_open, hA_eq⟩
  have hΩ_rel_saved := hΩ_rel
  rcases hΩ_rel with ⟨Ω0, hΩ0_open, hΩ_eq⟩
  have hG0Ω0 : G0 ∈ Ω0 := by
    have htmp : G0 ∈ Ω0 ∩ sourceOrientedGramVariety d n := by
      simpa [hΩ_eq] using hG0Ω
    exact htmp.1
  have hA_meets_Ω : (A ∩ Ω).Nonempty := by
    rw [mem_closure_iff] at hG0cl
    rcases hG0cl Ω0 hΩ0_open hG0Ω0 with ⟨G, hGΩ0, hGA⟩
    have hGvar : G ∈ sourceOrientedGramVariety d n := by
      rw [hA_eq] at hGA
      exact IsRelOpenInSourceOrientedGramVariety.subset
        hU_relOpen hGA.2.1
    have hGΩ : G ∈ Ω := by
      rw [hΩ_eq]
      exact ⟨hGΩ0, hGvar⟩
    exact ⟨G, hGA, hGΩ⟩
  let Rchart : Set (Fin m → ℂ) := C.chart '' (A ∩ Ω)
  have hRchart_ne : Rchart.Nonempty := by
    rcases hA_meets_Ω with ⟨G, hGA, hGΩ⟩
    exact ⟨C.chart G, G, ⟨hGA, hGΩ⟩, rfl⟩
  have hAΩ_rel_in_Ω : ∃ O, IsOpen O ∧ A ∩ Ω = O ∩ Ω := by
    refine ⟨A0, hA0_open, ?_⟩
    ext G
    constructor
    · intro hG
      have hGA0 : G ∈ A0 := by
        rw [hA_eq] at hG
        exact hG.1.1
      exact ⟨hGA0, hG.2⟩
    · intro hG
      constructor
      · rw [hA_eq]
        exact ⟨hG.1, hΩ_sub_Umax hG.2⟩
      · exact hG.2
  obtain ⟨Ochart, hOchart_open, hRchart_eq⟩ :=
    LocalBiholomorphOnSourceOrientedVariety.image_relOpenIn_chart
      (d := d) (n := n) C.chart_biholomorphic hΩ_sub_C hAΩ_rel_in_Ω
  have hRchart_relOpen :
      ∃ O, IsOpen O ∧ Rchart = O ∩ C.chart '' Ω :=
    ⟨Ochart, hOchart_open, hRchart_eq⟩
  have hRchart_zero : Set.EqOn φc 0 Rchart := by
    rintro y ⟨G, hGAΩ, rfl⟩
    have hφHG : φc (C.chart G) = H G := hφc_eq G hGAΩ.2
    have hHG0 : H G = 0 := hA_zero hGAΩ.1
    simpa [hφHG] using hHG0
  have hφc_zero : Set.EqOn φc 0 (C.chart '' Ω) :=
    SCV.identity_theorem_connected_open_zero hΩ_chart_open hΩ_chart_conn
      hφc_holo hRchart_relOpen hRchart_ne hRchart_zero
  refine ⟨Ω, hG0Ω, hΩ_rel_saved, hΩ_sub_Umax, ?_⟩
  intro G hGΩ
  have hφHG : φc (C.chart G) = H G := hφc_eq G hGΩ
  have hφ0 : φc (C.chart G) = 0 := hφc_zero ⟨G, hGΩ, rfl⟩
  simpa [hφHG] using hφ0

/-- Local identity step at a max-rank point for any finite-dimensional chart
model, after transporting the model to finite coordinates. -/
theorem local_identity_near_point_finiteDimensional
    {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [FiniteDimensional ℂ M]
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedMaxRankChartData d n (M := M) G0)
    {U A : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_relOpen : IsRelOpenInSourceOrientedGramVariety d n U)
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (hG0U : G0 ∈ U)
    (hA_rel :
      ∃ A0, IsOpen A0 ∧
        A = A0 ∩ (U ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hG0cl : G0 ∈ closure A)
    (hA_zero : Set.EqOn H 0 A) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      V ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn H 0 V := by
  exact
    (C.to_finrankCoordinateChart.local_identity_near_point
      hU_relOpen hH hG0U hA_rel hG0cl hA_zero)

end SourceOrientedMaxRankChartData

end BHW
