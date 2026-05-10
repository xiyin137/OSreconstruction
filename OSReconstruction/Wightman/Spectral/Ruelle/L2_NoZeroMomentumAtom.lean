/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Spectral.Ruelle.L5_SpectralRiemannLebesgue
import OSReconstruction.Wightman.Reconstruction.GNSHilbertSpace
import OSReconstruction.GeneralResults.SNAGTheorem

/-!
# L2: Spatial-cobounded decay of GNS matrix coefficients on the vacuum complement

**Status (2026-05-07): conditional theorem with precision-split hypotheses.**
Per PR #82 review (xiyin137), this file decomposes the L2 target into named
sub-lemmas making explicit which step depends on which input.

## Target

For `Φ, ψ ⊥ Ω` in the GNS Hilbert space, the matrix element `⟨Φ, U(a) ψ⟩`
decays to `0` as the spatial part of `a` goes to infinity (along the
cobounded filter on `SpacetimeDim d`, restricted to `a 0 = 0`).

This is the GNS Hilbert-space form of "no zero-momentum atom on the
vacuum complement, plus AC spatial marginal" — the spectral content of
R4 needed to discharge `RuelleAnalyticClusterHypotheses.pointwise` via
the SCV bridge.

## Precision split

The cobounded decay is broken into independent inputs:

1. **`gns_ray_decay`**: ray-style decay along a single nonzero spatial
   direction `a`. *Proved* directly from the existing
   `gns_cluster_completion` (in `GNSHilbertSpace.lean:1917`).

2. **`L2SpectralData`**: structure packaging the spectral-measure inputs
   needed to lift ray decay to cobounded decay:
   * SNAG joint spectral measure of spatial translations.
   * `no_zero_atom`: spectral measure has no atom at zero spatial
     momentum on `Ω⊥`. (Provable from ray decay + SNAG, but currently
     opaque.)
   * `ac_spatial_marginal`: AC spatial marginal of the spectral
     measure restricted to the pair `(Φ, ψ)`. (Textbook claim; cite
     Glimm-Jaffe §6.2, Reed-Simon II §IX.8.)
   * `matrix_element_eq`: bridge identity between matrix element and
     spatial Fourier transform of the spectral measure.

3. **`gns_orthogonal_spatial_cobounded_decay`**: the L2 target,
   *proved conditionally* on `L2SpectralData` by applying `L5` to the
   spectral measure.

This way:
* The proved part is visible (steps 1 + the conditional reduction).
* The textbook-input parts are explicit (`L2SpectralData` fields are
  named and documented).
* `RuelleAnalyticClusterHypotheses.pointwise` can be discharged with
  appropriate `L2SpectralData` instances supplied at call sites.

## References

* Streater-Wightman §3.5 — vacuum uniqueness ⇔ cluster decomposition.
* Glimm-Jaffe Ch 19 + §6.2 — spectral support and AC marginal for
  truncated states.
* Reed-Simon II §IX.8 — spectral theorem for unbounded operators on
  Hilbert space.
* Araki-Hepp-Ruelle 1962 — pointwise analytic cluster on the standard
  forward tube.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Bornology PreHilbertSpace

namespace OSReconstruction
namespace Ruelle

variable {d : ℕ} [NeZero d]

/-! ### Step 1: ray decay (proved) -/

/-- **Ray decay**: for `Φ : PreHilbert`, `ψ : GNSHilbert`, both with
zero vacuum projection, the matrix element `⟨Φ, U(r·a) ψ⟩` decays
to `0` along the scaling ray `r → ∞`, for any nonzero spatial
direction `a`.

This is a direct specialization of `gns_cluster_completion` to the
Φ, ψ ⊥ Ω case (the disconnected piece `⟨Φ, Ω⟩ ⟨Ω, ψ⟩` vanishes by
orthogonality). -/
theorem gns_ray_decay
    (Wfn : WightmanFunctions d)
    (Φ : PreHilbertSpace Wfn) (ψ : GNSHilbertSpace Wfn)
    (hΦ : @inner ℂ _ _ (gnsVacuum Wfn) (Φ : GNSHilbertSpace Wfn) = 0)
    (hψ : @inner ℂ _ _ (gnsVacuum Wfn) ψ = 0)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0) :
    Tendsto
      (fun r : ℝ => @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (r • a)) ψ))
      atTop
      (nhds (0 : ℂ)) := by
  have h := gns_cluster_completion Wfn Φ ψ a ha0 ha_nonzero
  -- Limit equals ⟨Φ, Ω⟩ * ⟨Ω, ψ⟩. Compute this is 0.
  have h_inner_Ω_ψ : @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn) = 0 := by
    -- ⟨Φ, Ω⟩ = conj(⟨Ω, Φ⟩) = conj(0) = 0
    have := inner_conj_symm (𝕜 := ℂ) (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn)
    rw [hΦ] at this
    simpa using this.symm
  rw [show (0 : ℂ) = (@inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn)) *
      (@inner ℂ _ _ (gnsVacuum Wfn) ψ) from by rw [h_inner_Ω_ψ, hψ]; ring]
  exact h

/-! ### Step 2: spectral data packet (conditional input) -/

/-- **Spectral data for the GNS spacetime translation rep on a pair of
states orthogonal to the vacuum.**

The off-diagonal sesquilinear spectral measure `μ_{Φ,ψ}` is in general
a **complex** measure (the matrix element `⟨Φ, U(a) ψ⟩` is not
positive-definite for `Φ ≠ ψ`, so by Bochner is not the Fourier
transform of a positive measure). Polarization decomposes it into
four diagonal positive measures.

This structure packages the polarization-form spectral data: four
positive measures `μₖ` (`k = 0, 1, 2, 3`) plus four AC-marginal claims
plus the polarized bridge identity. Each `μₖ` corresponds to the
diagonal SNAG measure of the polarization vector `Φ + iᵏ ψ`. -/
structure L2SpectralData
    (Wfn : WightmanFunctions d) (Φ ψ : GNSHilbertSpace Wfn) : Prop where
  /-- Four polarization-piece positive measures, each with AC spatial
  marginal, and the polarized bridge identity. -/
  data :
    ∃ (μ : Fin 4 → Measure (Fin (d + 1) → ℝ)),
      (∀ k, IsFiniteMeasure (μ k)) ∧
      -- AC spatial marginal of each piece.
      (∀ k, spatialMarginal (μ k) ≪
        (MeasureTheory.volume : Measure (Fin d → ℝ))) ∧
      -- Polarized bridge: ⟨Φ, U(a) ψ⟩ = (1/4) Σ i^k ∫ exp(i a·p) dμ_k.
      ∀ a : SpacetimeDim d, a 0 = 0 →
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ) =
          (1 / 4 : ℂ) * ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
            ∫ p : Fin (d + 1) → ℝ,
              Complex.exp (Complex.I *
                (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)

/-! ### Step 3: cobounded decay (conditional theorem)

**Note (2026-05-09)**: An earlier draft of this file shipped a
production axiom `gns_l2_spectral_data_axiom : L2SpectralData Wfn Φ ψ`
discharging the spectral-data hypothesis unconditionally for any
Wightman family. That axiom was withdrawn after the PR-#86 review
([@xiyin137](https://github.com/xiyin137)): per the project's axiom
discipline, new production axioms should encode classical background
infrastructure (SNAG, Bochner, Schwartz-Fubini, Vladimirov-style
SCV/FA) rather than QFT-specific consequences such as the GNS-spectral
AC marginal claim. `L2SpectralData` is kept as a conditional structure;
downstream consumers must supply it explicitly. The textbook discharge
(SNAG + polarization + spectrum support + AC marginal) is documented
in the structure's docstring as the proof obligation that future work
will need to discharge as theorems rather than axioms.

References for the discharge content:
* Glimm-Jaffe, *Quantum Physics*, §6.2 (spectral support of vacuum
  expectation values; mass hyperboloid analysis).
* Reed-Simon, *Methods of Modern Mathematical Physics II*, §IX.8
  (SNAG / Stone's theorem and absolutely continuous spectral measures).
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.5. -/

/-- **L2 (conditional)**: spatial-cobounded decay of GNS matrix
coefficients on the vacuum complement, given the spectral data packet.

Proof: combine `L2SpectralData.matrix_element_eq` (matrix element =
spatial Fourier transform of `μ`) with `L5` (`spectral_riemann_lebesgue`,
applied to `μ` with its AC spatial marginal) to conclude the matrix
element decays to 0 along the spatial-cobounded filter.

The proof is purely a reduction; the QFT content is in the
`L2SpectralData` hypothesis. -/
theorem gns_orthogonal_spatial_cobounded_decay_of
    (Wfn : WightmanFunctions d)
    (Φ ψ : GNSHilbertSpace Wfn)
    (hL2 : L2SpectralData Wfn Φ ψ) :
    Tendsto
      (fun a : SpacetimeDim d =>
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ))
      (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d))
      (nhds (0 : ℂ)) := by
  obtain ⟨μ, h_finite, h_AC, h_bridge⟩ := hL2.data
  -- For each polarization piece μ k, apply L5.
  -- spatialOf projects SpacetimeDim d → (Fin d → ℝ).
  set spatialOf : SpacetimeDim d → (Fin d → ℝ) :=
    fun a i => a (Fin.succ i) with hsp_def
  have h_sp_cont : Continuous spatialOf :=
    continuous_pi (fun _ => continuous_apply _)
  -- spatialOf preserves cobounded: it's a continuous linear surjection between
  -- finite-dim spaces with bounded inverse via `Fin.cons 0`.
  -- Actually simpler: spatialOf has a continuous linear right inverse
  --   (a_sp ↦ Fin.cons 0 a_sp), and this gives cobounded → cobounded.
  have h_sp_cobounded :
      Filter.Tendsto spatialOf
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (Bornology.cobounded (Fin d → ℝ)) := by
    -- Strategy: reduce to "‖spatialOf a‖ → ∞" along the inf filter, using
    -- `‖a‖ = ‖spatialOf a‖` whenever `a 0 = 0`.
    rw [Filter.tendsto_def]
    intro S hS
    -- For S ∈ cobounded, Sᶜ is bounded.
    -- S ∈ cobounded ⇔ Sᶜ is bounded.
    have hSc_bdd : Bornology.IsBounded (Sᶜ : Set (Fin d → ℝ)) := by
      rw [Bornology.isBounded_def, compl_compl]
      exact hS
    obtain ⟨R, hR⟩ : ∃ R, Sᶜ ⊆ Metric.closedBall (0 : Fin d → ℝ) R :=
      hSc_bdd.subset_closedBall (0 : Fin d → ℝ)
    -- spatialOf⁻¹ S contains {a 0 = 0} ∩ {a : ‖a‖ > R}, both in their filters.
    refine Filter.mem_of_superset (?_ : {a : SpacetimeDim d | a 0 = 0} ∩
        {a : SpacetimeDim d | R < ‖a‖} ∈ _)
      (?_ : {a : SpacetimeDim d | a 0 = 0} ∩
          {a : SpacetimeDim d | R < ‖a‖} ⊆ spatialOf ⁻¹' S)
    · refine Filter.inter_mem ?_ ?_
      · exact Filter.mem_inf_of_left (Filter.mem_principal_self _)
      · refine Filter.mem_inf_of_right ?_
        rw [Metric.cobounded_eq_cocompact, Filter.mem_cocompact]
        refine ⟨Metric.closedBall (0 : SpacetimeDim d) R,
          isCompact_closedBall _ _, fun a ha => ?_⟩
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at ha
        simp only [Set.mem_setOf_eq]
        linarith
    · -- Inclusion: a 0 = 0 + ‖a‖ > R → spatialOf a ∉ closedBall(0, R) → spatialOf a ∈ S.
      rintro a ⟨ha0, ha_norm⟩
      simp only [Set.mem_setOf_eq] at ha_norm
      -- ‖a‖ = ‖spatialOf a‖ when a 0 = 0.
      have h_norm_eq : ‖spatialOf a‖ = ‖a‖ := by
        -- Sup norm; both = max over indices, with a 0 = 0 contributing 0 in full norm.
        simp only [Pi.norm_def, Pi.nnnorm_def, hsp_def]
        congr 1
        apply le_antisymm
        · -- spatialOf side ≤ full side
          refine Finset.sup_le (fun i _ => ?_)
          exact Finset.le_sup (f := fun j : Fin (d + 1) => ‖a j‖₊)
            (Finset.mem_univ (Fin.succ i))
        · -- full side ≤ spatialOf side (using a 0 = 0).
          refine Finset.sup_le (fun i _ => ?_)
          rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, rfl⟩
          · subst hi
            have h_a0_zero : ‖a 0‖₊ = 0 := by
              rw [nnnorm_eq_zero]
              -- Need: a 0 = 0 from ha0; conclude ‖a 0‖ = 0.
              -- ha0 says a 0 = 0 (for the function a : SpacetimeDim d).
              -- a 0 : Fin (d+1) → ℝ; we need this is 0 in that space.
              -- Wait: a : SpacetimeDim d, so a 0 is a real number? Let me check.
              -- Actually SpacetimeDim d := Fin (d+1) → ℝ. So a : Fin (d+1) → ℝ,
              -- and a 0 : ℝ.
              exact ha0
            rw [h_a0_zero]
            exact zero_le _
          · exact Finset.le_sup (f := fun j : Fin d => ‖a (Fin.succ j)‖₊)
              (Finset.mem_univ j)
      -- Show spatialOf a ∈ S via spatialOf a ∉ Sᶜ.
      simp only [Set.mem_preimage]
      by_contra h_not_in_S
      have h_in_Sc : spatialOf a ∈ Sᶜ := h_not_in_S
      have h_in_ball : spatialOf a ∈ Metric.closedBall (0 : Fin d → ℝ) R := hR h_in_Sc
      simp only [Metric.mem_closedBall, dist_zero_right] at h_in_ball
      -- ‖spatialOf a‖ ≤ R, but ‖a‖ > R, and ‖spatialOf a‖ = ‖a‖. Contradiction.
      have : ‖a‖ ≤ R := h_norm_eq ▸ h_in_ball
      linarith
  -- For each k, apply L5 to μ k, compose with spatialOf, get Tendsto → 0.
  have h_each_decay : ∀ k : Fin 4,
      Filter.Tendsto
        (fun a : SpacetimeDim d =>
          ∫ p : Fin (d + 1) → ℝ,
            Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k))
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds (0 : ℂ)) := by
    intro k
    haveI : IsFiniteMeasure (μ k) := h_finite k
    have h_L5_k := spectral_riemann_lebesgue (μ k) (h_AC k)
    exact h_L5_k.comp h_sp_cobounded
  -- The polarized sum: Σ k, i^k * (decay term k) → Σ k, i^k * 0 = 0.
  have h_sum_decay :
      Filter.Tendsto
        (fun a : SpacetimeDim d =>
          ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
            ∫ p : Fin (d + 1) → ℝ,
              Complex.exp (Complex.I *
                (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k))
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds (0 : ℂ)) := by
    have h_zero_sum : (0 : ℂ) = ∑ k : Fin 4, Complex.I ^ (k : ℕ) * (0 : ℂ) := by
      simp
    rw [h_zero_sum]
    exact tendsto_finset_sum _ (fun k _ =>
      ((h_each_decay k).const_mul (Complex.I ^ (k : ℕ))))
  -- (1/4) * (sum) → (1/4) * 0 = 0.
  have h_quarter_decay :
      Filter.Tendsto
        (fun a : SpacetimeDim d =>
          (1 / 4 : ℂ) * ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
            ∫ p : Fin (d + 1) → ℝ,
              Complex.exp (Complex.I *
                (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k))
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds (0 : ℂ)) := by
    have h_zero : (0 : ℂ) = (1 / 4 : ℂ) * 0 := by simp
    rw [h_zero]
    exact h_sum_decay.const_mul _
  -- Use eventual equality: on {a 0 = 0}, matrix element = polarized sum.
  refine h_quarter_decay.congr' ?_
  refine Filter.Eventually.mono (Filter.mem_inf_of_left
    (Filter.mem_principal_self {a : SpacetimeDim d | a 0 = 0})) ?_
  intro a ha0
  exact (h_bridge a ha0).symm

end Ruelle
end OSReconstruction

end
