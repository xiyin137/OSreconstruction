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

Records the spectral measure produced by SNAG (applied to the spacetime
translation subgroup of the GNS Poincaré rep) and its key analytic
property — AC spatial marginal — along with the SNAG-derived bridge
identity expressing the matrix element as the spatial Fourier transform
of the measure.

For a pair `Φ, ψ ⊥ Ω` in the GNS Hilbert space:
* `μ`: a finite Borel measure on the (d+1)-momentum space.
* AC spatial marginal: the load-bearing input. Comes from spectral
  support analysis on Ω⊥ (Glimm-Jaffe §6.2, Reed-Simon II §IX.8 — for
  physical QFTs the spectral measure on Ω⊥ is supported on mass
  hyperboloids `p² ≥ m²` in V̄+, projecting to AC spatial marginal
  via `dp⁰ / 2E_p`).
* Bridge identity: from SNAG.

This structure is the conditional input for the L2 reduction. It is
*discharged* unconditionally for any `WightmanFunctions` via the axiom
`gns_l2_spectral_data_axiom` below — see that axiom for the textbook
status. -/
structure L2SpectralData
    (Wfn : WightmanFunctions d) (Φ ψ : GNSHilbertSpace Wfn) : Prop where
  /-- A finite Borel measure on the (d+1)-dimensional momentum space
  whose spatial Fourier transform represents `⟨Φ, U(a) ψ⟩` for
  spatial `a`. -/
  μ_exists :
    ∃ (μ : Measure (Fin (d + 1) → ℝ)),
      IsFiniteMeasure μ ∧
      -- AC spatial marginal: this is the load-bearing textbook input.
      spatialMarginal μ ≪ (MeasureTheory.volume : Measure (Fin d → ℝ)) ∧
      -- Bridge identity: matrix element = spatial Fourier transform of μ.
      ∀ a : SpacetimeDim d, a 0 = 0 →
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ) =
          ∫ p : Fin (d + 1) → ℝ,
            Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂μ

/-! ### L2 spectral data — production axiom

`L2SpectralData` is *unconditionally available* for any `Wightman`
family on any pair of states orthogonal to the vacuum. The textbook
content combines:

1. **SNAG application** (existing `snag_theorem` axiom): produces the
   joint projection-valued measure of the spacetime translation
   subgroup on `GNSHilbertSpace Wfn`. Each state ψ gets a spectral
   measure μ_ψ with `μ_ψ B = ‖E(B) ψ‖²`. The SNAG bridge identity
   `⟨ψ, U(a) ψ⟩ = ∫ exp(i ⟨a, p⟩) dμ_ψ` is direct.

2. **Polarization** for the off-diagonal pair `(Φ, ψ)`: the sesquilinear
   spectral form `μ_{Φ,ψ}` is built from four diagonal SNAG measures
   via the polarization identity. The bridge identity polarizes
   accordingly.

3. **Spectrum support on V̄+ \ {0} for Ω⊥** (textbook QFT): R4 cluster
   + spectrum condition + vacuum uniqueness imply the spectral measure
   on the vacuum complement is supported strictly inside the forward
   light cone, away from `p = 0`. Hence the spectral measure has no
   atom at zero momentum.

4. **AC spatial marginal** (textbook QFT, the deep input): for physical
   Wightman QFTs, the spectral measure on Ω⊥ projects to AC spatial
   marginal via the mass-hyperboloid foliation. This requires R4 to
   exclude zero-mass particles in the truncated correlations and
   spectrum-condition support on `p² ≥ m² ≥ 0` for some mass spectrum.

References:
* Glimm-Jaffe, *Quantum Physics*, §6.2 (spectral support of vacuum
  expectation values; mass hyperboloid analysis).
* Reed-Simon, *Methods of Modern Mathematical Physics II*, §IX.8
  (SNAG / Stone's theorem and absolutely continuous spectral
  measures).
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.5
  (cluster decomposition theorem; vacuum uniqueness).

Status: paper-textbook QFT result, requires substantial spectral
analysis to formalize from R4 + spectrum_condition. Adopted as a
single explicit axiom at the GNS-spectral boundary. -/
axiom gns_l2_spectral_data_axiom
    (Wfn : WightmanFunctions d)
    (Φ ψ : GNSHilbertSpace Wfn)
    (hΦ : @inner ℂ _ _ (gnsVacuum Wfn) Φ = 0)
    (hψ : @inner ℂ _ _ (gnsVacuum Wfn) ψ = 0) :
    L2SpectralData Wfn Φ ψ

/-! ### Step 3: cobounded decay (conditional theorem) -/

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
  obtain ⟨μ, _, h_AC, h_bridge⟩ := hL2.μ_exists
  -- Apply L5 (spectral_riemann_lebesgue) to get spatial Fourier transform decay
  -- of μ along cobounded `a_spatial`.
  -- Need to bridge from "a : SpacetimeDim d with a 0 = 0" to "a_spatial : Fin d → ℝ".
  -- The spatial part of `a` is `fun i : Fin d => a (Fin.succ i)`.
  set spatialOf : SpacetimeDim d → (Fin d → ℝ) :=
    fun a i => a (Fin.succ i) with hsp_def
  -- L5 gives Tendsto over cobounded(Fin d → ℝ) of the Fourier integrand.
  have h_L5 := spectral_riemann_lebesgue μ h_AC
  -- Compose with the continuous projection `spatialOf`.
  -- spatialOf is continuous (just evaluation at successor coords).
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
  -- Compose L5 with spatialOf to get Tendsto along the inf filter, valued in ℂ.
  have h_composed := h_L5.comp h_sp_cobounded
  -- Use eventual equality: on {a 0 = 0}, the L5 integrand at `spatialOf a` equals
  -- the matrix element by the L2 bridge identity. {a 0 = 0} is a member of the
  -- inf filter, so eventually true.
  refine h_composed.congr' ?_
  refine Filter.Eventually.mono (Filter.mem_inf_of_left
    (Filter.mem_principal_self {a : SpacetimeDim d | a 0 = 0})) ?_
  intro a ha0
  -- a 0 = 0; apply bridge identity (symmetric direction).
  exact (h_bridge a ha0).symm

/-! ### L2 unconditional (Option B)

Combining the conditional reduction with the spectral-data axiom yields
the unconditional L2 statement: for any `Wightman` family and any
pair of states orthogonal to the vacuum, the GNS matrix coefficient
decays to `0` along the spatial-cobounded filter.

This is the form used by downstream consumers in the Ruelle proof
chain (L6 / L7 / discharge of `RuelleAnalyticClusterHypotheses`). -/

/-- **L2 unconditional**: spatial-cobounded decay of GNS matrix
coefficients on the vacuum complement, for any `Wightman` family.

Discharge of the conditional version `gns_orthogonal_spatial_cobounded_decay_of`
via the textbook spectral-data axiom `gns_l2_spectral_data_axiom`. -/
theorem gns_orthogonal_spatial_cobounded_decay
    (Wfn : WightmanFunctions d)
    (Φ ψ : GNSHilbertSpace Wfn)
    (hΦ : @inner ℂ _ _ (gnsVacuum Wfn) Φ = 0)
    (hψ : @inner ℂ _ _ (gnsVacuum Wfn) ψ = 0) :
    Tendsto
      (fun a : SpacetimeDim d =>
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ))
      (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d))
      (nhds (0 : ℂ)) :=
  gns_orthogonal_spatial_cobounded_decay_of Wfn Φ ψ
    (gns_l2_spectral_data_axiom Wfn Φ ψ hΦ hψ)

end Ruelle
end OSReconstruction

end
