/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialHermite
import OSReconstruction.SCV.DistributionalUniqueness
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The diagonal in `ℕ × ℕ` is cofinal for the product order. -/
theorem tendsto_natDiagonal_atTop :
    Tendsto (fun N : ℕ => (N, N)) atTop atTop := by
  rw [tendsto_atTop]
  intro p
  filter_upwards [eventually_ge_atTop (max p.1 p.2)] with N hN
  exact ⟨le_trans (le_max_left _ _) hN, le_trans (le_max_right _ _) hN⟩

/-- Locally uniform convergence may be restricted along any cofinal map of
the approximation index. -/
theorem TendstoLocallyUniformlyOn.comp_index
    {ι κ α β : Type*}
    [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β}
    {p : Filter ι} {q : Filter κ} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f p s)
    (g : κ → ι)
    (hg : Tendsto g q p) :
    TendstoLocallyUniformlyOn (fun a => F (g a)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hF⟩ := h u hu x hx
  refine ⟨t, ht, ?_⟩
  exact hg.eventually hF

/-- Locally uniform convergence in the first approximation index and
compact-uniform convergence in the second imply joint locally uniform
convergence in the product order. -/
theorem tendstoLocallyUniformlyOn_prod_of_first_of_uniform_second
    {α E : Type*}
    [PseudoMetricSpace α] [LocallyCompactSpace α]
    [PseudoMetricSpace E]
    {F : ℕ → ℕ → α → E}
    {G : ℕ → α → E}
    {f : α → E}
    {U : Set α}
    (hU_open : IsOpen U)
    (hfirst :
      TendstoLocallyUniformlyOn G f atTop U)
    (hsecond :
      ∀ K : Set α, K ⊆ U → IsCompact K →
        TendstoUniformlyOn
          (fun shell (p : ℕ × α) => F p.1 shell p.2)
          (fun p => G p.1 p.2)
          atTop (Set.univ ×ˢ K)) :
    TendstoLocallyUniformlyOn
      (fun p : ℕ × ℕ => F p.1 p.2)
      f atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU_open]
  intro K hK_domain hK_compact
  have hfirstK :
      TendstoUniformlyOn G f atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      hK_compact).mp (hfirst.mono hK_domain)
  have hsecondK := hsecond K hK_domain hK_compact
  rw [Metric.tendstoUniformlyOn_iff] at hfirstK hsecondK ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hfirst_eventually := hfirstK (ε / 2) hε2
  have hsecond_eventually := hsecondK (ε / 2) hε2
  have hfst :
      Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact Filter.tendsto_fst
  have hsnd :
      Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact Filter.tendsto_snd
  filter_upwards
    [hfst.eventually hfirst_eventually,
      hsnd.eventually hsecond_eventually] with
      p hp_first hp_second
  intro z hz
  calc
    dist (f z) (F p.1 p.2 z)
        ≤ dist (f z) (G p.1 z) +
            dist (G p.1 z) (F p.1 p.2 z) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add
        (by simpa [dist_comm] using hp_first z hz)
        (by
          simpa [dist_comm] using
            hp_second (p.1, z) ⟨Set.mem_univ _, hz⟩)
    _ = ε := by ring

/-- Chapter V approximants with independent time-smearing and spatial-shell
indices. Joint convergence is taken in the product order on `ℕ × ℕ`. -/
structure GeneratorSpatialTwoScaleApproximationFamily (d k : ℕ) where
  domain : GeneratorIndex k → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  approximation :
    GeneratorIndex k → ℕ → ℕ →
      OSIITimeGapSpace k → OSIISpatialDistribution d k
  approximation_weaklyHolomorphic :
    ∀ i timeScale shell,
      OSIIWeaklyHolomorphicOn
        (approximation i timeScale shell) (domain i)
  scalarLimit :
    GeneratorIndex k → OSIITimeGapSpace k →
      SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ
  locallyUniform :
    ∀ i χ,
      TendstoLocallyUniformlyOn
        (fun (p : ℕ × ℕ) z => approximation i p.1 p.2 z χ)
        (fun z => scalarLimit i z χ)
        atTop (domain i)

namespace GeneratorSpatialTwoScaleApproximationFamily

variable {d k : ℕ}

/-- Reparameterize every generator chart by a continuous complex-linear
equivalence. This is useful when the analytic construction is naturally
expressed in split-native coordinates while overlap gluing uses one common
physical coordinate system. -/
noncomputable def precomp
    (A : GeneratorSpatialTwoScaleApproximationFamily d k)
    (e : GeneratorIndex k →
      OSIITimeGapSpace k ≃L[ℂ] OSIITimeGapSpace k) :
    GeneratorSpatialTwoScaleApproximationFamily d k where
  domain := fun i => e i ⁻¹' A.domain i
  domain_open := fun i =>
    (A.domain_open i).preimage (e i).continuous
  approximation := fun i timeScale shell z =>
    A.approximation i timeScale shell (e i z)
  approximation_weaklyHolomorphic := by
    intro i timeScale shell χ
    exact
      (A.approximation_weaklyHolomorphic i timeScale shell χ).comp
        (e i).differentiable.differentiableOn
        (Set.mapsTo_preimage (e i) (A.domain i))
  scalarLimit := fun i z χ => A.scalarLimit i (e i z) χ
  locallyUniform := by
    intro i χ
    exact
      (A.locallyUniform i χ).comp (e i)
        (Set.mapsTo_preimage (e i) (A.domain i))
        (e i).continuous.continuousOn

/-- Restrict a jointly convergent two-scale family to the cofinal diagonal. -/
noncomputable def diagonal
    (A : GeneratorSpatialTwoScaleApproximationFamily d k) :
    GeneratorSpatialApproximationFamily d k where
  domain := A.domain
  domain_open := A.domain_open
  approximation := fun i N => A.approximation i N N
  approximation_weaklyHolomorphic := fun i N =>
    A.approximation_weaklyHolomorphic i N N
  scalarLimit := A.scalarLimit
  locallyUniform := by
    intro i χ
    exact TendstoLocallyUniformlyOn.comp_index (A.locallyUniform i χ)
      (fun N : ℕ => (N, N)) tendsto_natDiagonal_atTop

@[simp] theorem diagonal_domain
    (A : GeneratorSpatialTwoScaleApproximationFamily d k)
    (i : GeneratorIndex k) :
    A.diagonal.domain i = A.domain i := rfl

@[simp] theorem diagonal_approximation
    (A : GeneratorSpatialTwoScaleApproximationFamily d k)
    (i : GeneratorIndex k) (N : ℕ)
    (z : OSIITimeGapSpace k) :
    A.diagonal.approximation i N z =
      A.approximation i N N z := rfl

/-- Common positive-real data stated before diagonalization. The substantive
input is joint convergence of the time-smearing/Hermite-shell approximants to
one split-independent spatial orbit. -/
structure CommonPositiveRealEdgeData
    (A : GeneratorSpatialTwoScaleApproximationFamily d k) where
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  orbit : (Fin k → ℝ) → OSIISpatialDistribution d k
  real_mem :
    ∀ i τ, τ ∈ realRegion →
      osiiPositiveRealTimeEmbed τ ∈ A.domain i
  approximation_tendsto_orbit :
    ∀ i τ, τ ∈ realRegion → ∀ χ,
      Tendsto
        (fun p : ℕ × ℕ =>
          A.approximation i p.1 p.2
            (osiiPositiveRealTimeEmbed τ) χ)
        atTop (𝓝 (orbit τ χ))

namespace CommonPositiveRealEdgeData

/-- A common distributional real trace forces all splitwise locally uniform
limits to have one pointwise positive-real edge. -/
noncomputable def ofCommonDistributionalTrace
    [NeZero k]
    (A : GeneratorSpatialTwoScaleApproximationFamily d k)
    (realRegion : Set (Fin k → ℝ))
    (realRegion_open : IsOpen realRegion)
    (realRegion_nonempty : realRegion.Nonempty)
    (real_mem :
      ∀ i τ, τ ∈ realRegion →
        osiiPositiveRealTimeEmbed τ ∈ A.domain i)
    (trace :
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        SchwartzMap (Fin k → ℝ) ℂ → ℂ)
    (represents :
      ∀ (i : GeneratorIndex k)
        (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
        (φ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.SupportsInOpen
            (φ : (Fin k → ℝ) → ℂ) realRegion →
          ∫ τ : Fin k → ℝ,
              A.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ * φ τ =
            trace χ φ) :
    A.CommonPositiveRealEdgeData := by
  let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
  let orbit : (Fin k → ℝ) → OSIISpatialDistribution d k :=
    fun τ => A.diagonal.distribution i₀ (osiiPositiveRealTimeEmbed τ)
  refine
    { realRegion := realRegion
      realRegion_open := realRegion_open
      realRegion_nonempty := realRegion_nonempty
      orbit := orbit
      real_mem := real_mem
      approximation_tendsto_orbit := ?_ }
  intro i τ hτ χ
  have hi_mem := real_mem i τ hτ
  have hi₀_mem := real_mem i₀ τ hτ
  have hi_hol :
      DifferentiableOn ℂ
        (fun z => A.scalarLimit i z χ) (A.domain i) :=
    (A.locallyUniform i χ).differentiableOn_finite
      (Filter.Eventually.of_forall fun p =>
        A.approximation_weaklyHolomorphic i p.1 p.2 χ)
      (A.domain_open i)
  have hi₀_hol :
      DifferentiableOn ℂ
        (fun z => A.scalarLimit i₀ z χ) (A.domain i₀) :=
    (A.locallyUniform i₀ χ).differentiableOn_finite
      (Filter.Eventually.of_forall fun p =>
        A.approximation_weaklyHolomorphic i₀ p.1 p.2 χ)
      (A.domain_open i₀)
  have hi_cont :
      ContinuousOn
        (fun ξ : Fin k → ℝ =>
          A.scalarLimit i (osiiPositiveRealTimeEmbed ξ) χ)
        realRegion :=
    hi_hol.continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun ξ hξ => real_mem i ξ hξ)
  have hi₀_cont :
      ContinuousOn
        (fun ξ : Fin k → ℝ =>
          A.scalarLimit i₀ (osiiPositiveRealTimeEmbed ξ) χ)
        realRegion :=
    hi₀_hol.continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun ξ hξ => real_mem i₀ ξ hξ)
  have heq :
      A.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ =
        A.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ := by
    have heqOn :=
      SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
        realRegion_open hi_cont hi₀_cont
        (fun φ hφ_compact hφ_support =>
          (represents i χ φ ⟨hφ_compact, hφ_support⟩).trans
            (represents i₀ χ φ ⟨hφ_compact, hφ_support⟩).symm)
    exact heqOn hτ
  have hlimit :=
    (A.locallyUniform i χ).tendsto_at hi_mem
  have horbit :
      orbit τ χ =
        A.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ := by
    exact
      A.diagonal.distribution_apply_of_mem
        i₀ (osiiPositiveRealTimeEmbed τ) hi₀_mem χ
  rw [horbit, ← heq]
  exact hlimit

/-- Joint two-scale convergence gives the existing common edge after
restriction to the cofinal diagonal. -/
noncomputable def toDiagonal
    (A : GeneratorSpatialTwoScaleApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData) :
    A.diagonal.CommonPositiveRealEdgeData :=
  GeneratorSpatialApproximationFamily.CommonPositiveRealEdgeData.ofApproximationTendsto
    A.diagonal
    E.realRegion E.realRegion_open E.realRegion_nonempty E.orbit
    (by
      intro i τ hτ
      simpa using E.real_mem i τ hτ)
    (by
      intro i τ hτ χ
      simpa using
        (E.approximation_tendsto_orbit i τ hτ χ).comp
          tendsto_natDiagonal_atTop)

end CommonPositiveRealEdgeData

end GeneratorSpatialTwoScaleApproximationFamily

end OSIIChapterV
end OSReconstruction
