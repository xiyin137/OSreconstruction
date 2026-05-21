/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RuelleClusterBound

/-!
# L4: Uniform-in-`a` polynomial bound on `W_analytic_BHW` along spacelike
shifts

**Status (2026-05-07): conditional theorem with structural spectral input.**

## Target

The `bound` field of `RuelleAnalyticClusterHypotheses Wfn n m`: there exist
constants `C > 0`, `N M : ℕ`, `R > 0` such that for every pair of forward-tube
configurations `z₁ ∈ ForwardTube d n`, `z₂ ∈ ForwardTube d m`, every real
spatial shift `a` (`a 0 = 0`) with squared spatial norm exceeding `R^2`, and
under the hypothesis that the joint configuration `(z₁, z₂ + (0, a))` lies
in the analytic domain `PermutedExtendedTube d (n + m)`,
```
‖(W_analytic_BHW Wfn (n + m)).val (Fin.append z₁ (z₂ + (0, a)))‖
    ≤ C · (1 + ‖z₁‖ + ‖z₂‖) ^ N
        · (1 + (tubeBoundaryDist z₁)⁻¹) ^ M
        · (1 + (tubeBoundaryDist z₂)⁻¹) ^ M
```
The boundary-distance regulator `(1 + (tubeBoundaryDist z)⁻¹)^M` matches
Streater-Wightman Theorem 3.1.1; the unregulated form was found vacuous
during the PR-#86 vetting (free-field counterexample;
see `docs/ruelle_bound_vacuity_concern.md`).
with `C, N, M` independent of `a`.

This is Ruelle 1962 Theorem 2 / Araki-Hepp-Ruelle 1962 / Streater-Wightman §3.4.

## Structural reduction

`L4SpectralData Wfn n m` packages the Laplace-representation content needed
to prove L4 from the |exp(i p · a)| = 1 cancellation: a **polarized
spectral-measure family** parameterized by `(z₁, z₂)`, giving the joint
analytic continuation as a Fourier transform in the spatial-shift parameter
`a`, with each polarization piece's total mass polynomially bounded in
`(‖z₁‖, ‖z₂‖)`.

The proof of `ruelle_analytic_cluster_bound_of` is a triangle-inequality +
|exp(i p · a)| = 1 argument: the modulus of each Fourier integral is at
most the total mass of its measure, which is bounded by `C · (1 + ‖z₁‖ +
‖z₂‖) ^ N` by the polynomial-bound hypothesis. The polarized sum's
modulus is then bounded by `(1/4) · 4 · C · (1 + ‖z₁‖ + ‖z₂‖) ^ N
= C · (1 + ‖z₁‖ + ‖z₂‖) ^ N`.

## Discharge (conditional only — no production axiom)

`L4SpectralData` is **kept as a conditional input**; this file ships
the conditional reduction `ruelle_analytic_cluster_bound_of` only.
A production axiom `wightman_l4_spectral_data_axiom` was drafted in
PR-#86 and **withdrawn (2026-05-09)** on review by
[@xiyin137](https://github.com/xiyin137): per the project's axiom
discipline, new production axioms encode classical background
infrastructure (SNAG, Bochner tube, Schwartz-Fubini, Vladimirov-style
SCV/FA), not QFT-specific consequences such as the polarized Fourier
representation of `W_analytic_BHW`. Downstream consumers must supply
`L4SpectralData` explicitly, or future work will discharge it as a
theorem.

The textbook discharge content (a future-work proof obligation, not
an axiom commitment) combines:

1. **Spectral resolution** of multi-time matrix elements via the GNS
   spacetime translation rep (SNAG theorem).
2. **Polarization** of off-diagonal sesquilinear forms into four positive
   measures.
3. **Polynomial growth in `(z₁, z₂)`** of each polarization piece's total
   mass with boundary regulator: matches
   `fourierLaplaceExtMultiDim_vladimirov_growth`
   (proved in `OSReconstruction/SCV/PaleyWienerSchwartz.lean:3286`)
   on the FL-extension side, transported via
   `bv_implies_fourier_support` + `fl_representation_from_bv` (existing
   SCV axioms) to the `W_analytic_BHW` side.
4. **|exp(i p · a)| = 1** for real spatial shifts: the modulus of
   `exp(i p · a)` is `1` for real spatial `a`, regardless of support,
   hence the bound is uniform in `a` (this part is captured by the
   conditional reduction in this file).

## References

* Ruelle 1962, *On the asymptotic condition in quantum field theory*,
  Helv. Phys. Acta 35 — original cluster theorem.
* Araki-Hepp-Ruelle 1962, *On the asymptotic behaviour of Wightman
  functions in space-like directions*, Helv. Phys. Acta 35, Theorem 2 —
  pointwise version on the standard forward tube.
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.4 —
  textbook account.
* Glimm-Jaffe, *Quantum Physics*, §6.2 — spectral analysis of vacuum
  expectation values.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Bornology Complex

namespace OSReconstruction
namespace Ruelle

variable {d : ℕ} [NeZero d]

/-! ### Spectral data packet (conditional input) -/

/-- **L4 spectral data**: polarization-piece Laplace representation of the
joint analytic continuation along the spatial-shift parameter, with
polynomial mass bound in `(‖z₁‖, ‖z₂‖)`.

For each pair `(z₁, z₂) ∈ ForwardTube d n × ForwardTube d m`, the data
provides four positive finite measures `μ k : Fin 4 → Measure (Fin (d+1) → ℝ)`
such that:

* The joint analytic continuation `W_analytic_BHW Wfn (n + m)` evaluated on
  the Wick configuration `(z₁, z₂ + (0, a))` (real spatial shift `a` with
  `a 0 = 0`, in the joint analytic domain) equals the polarized Fourier
  integral
  `(1/4) Σ_k iᵏ ∫ exp(i Σ_i a (succ i) · p (succ i)) dμ_k(p)`.
* Each `μ k` has total mass at most `C · (1 + ‖z₁‖ + ‖z₂‖) ^ N` for fixed
  constants `C, N` independent of `(z₁, z₂)`.

The polynomial bound on the masses is the spectral-content hypothesis: it
encodes the polynomial growth of the underlying Wightman spectral
distribution in the spatial-momentum direction. The constants `C, N, R`
are global (independent of `(z₁, z₂)`).

The Fourier representation in `a` is justified by Bochner's theorem applied
to each polarization vector — the off-diagonal matrix element is not in
itself positive-definite in `a`, but its polarization decomposition yields
four positive-definite functions of `a`, each represented as the Fourier
transform of a positive measure. -/
structure L4SpectralData
    (Wfn : WightmanFunctions d) (n m : ℕ) : Prop where
  data :
    ∃ (C : ℝ) (N M : ℕ) (R : ℝ),
      0 < C ∧ 0 < R ∧
      ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
      ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
        z₁ ∈ ForwardTube d n →
        z₂ ∈ ForwardTube d m →
        ∃ (μ : Fin 4 → Measure (Fin (d + 1) → ℝ)),
          (∀ k, IsFiniteMeasure (μ k)) ∧
          (∀ k, ((μ k) Set.univ).toReal ≤
            C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
              * (1 + (tubeBoundaryDist z₁)⁻¹) ^ M
              * (1 + (tubeBoundaryDist z₂)⁻¹) ^ M) ∧
          ∀ (a : SpacetimeDim d), a 0 = 0 →
            (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
            (Fin.append z₁
                (fun k μ_idx => z₂ k μ_idx +
                  (if μ_idx = 0 then (0 : ℂ) else (a μ_idx : ℂ)))) ∈
              PermutedExtendedTube d (n + m) →
            (W_analytic_BHW Wfn (n + m)).val
                (Fin.append z₁
                  (fun k μ_idx => z₂ k μ_idx +
                    (if μ_idx = 0 then (0 : ℂ) else (a μ_idx : ℂ)))) =
              (1 / 4 : ℂ) * ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
                ∫ p : Fin (d + 1) → ℝ,
                  Complex.exp (Complex.I *
                    (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)

/-! ### L4 conditional theorem -/

/-- **L4 (conditional)**: the uniform-in-`a` polynomial bound on
`W_analytic_BHW`, given the spectral data packet.

Proof: the polarized Fourier integrals are estimated by triangle inequality.
Each `|exp(i Σ a (succ i) · p (succ i))|` is bounded above by `1` (modulus
of complex exponential of an imaginary-part-zero argument), so each Fourier
integral is bounded above by the total mass of its measure — which is
polynomially bounded in `(‖z₁‖, ‖z₂‖)` by hypothesis, *independently* of
`a`. The (1/4) · 4 = 1 factor in the polarized sum gives the final bound
with the same constant `C`. -/
theorem ruelle_analytic_cluster_bound_of
    (Wfn : WightmanFunctions d) (n m : ℕ) (hL4 : L4SpectralData Wfn n m) :
    ∃ (C : ℝ) (N M : ℕ) (R : ℝ),
      0 < C ∧ 0 < R ∧
      ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
      ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
        z₁ ∈ ForwardTube d n →
        z₂ ∈ ForwardTube d m →
        ∀ (a : SpacetimeDim d), a 0 = 0 →
          (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
          (Fin.append z₁
              (fun k μ_idx => z₂ k μ_idx +
                (if μ_idx = 0 then (0 : ℂ) else (a μ_idx : ℂ)))) ∈
            PermutedExtendedTube d (n + m) →
          ‖(W_analytic_BHW Wfn (n + m)).val
              (Fin.append z₁
                (fun k μ_idx => z₂ k μ_idx +
                  (if μ_idx = 0 then (0 : ℂ) else (a μ_idx : ℂ))))‖
            ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
                * (1 + (tubeBoundaryDist z₁)⁻¹) ^ M
                * (1 + (tubeBoundaryDist z₂)⁻¹) ^ M := by
  obtain ⟨C, N, M, R, hC, hR, h⟩ := hL4.data
  refine ⟨C, N, M, R, hC, hR, ?_⟩
  intro z₁ z₂ hz₁ hz₂ a ha₀ ha_R hPET
  obtain ⟨μ, h_finite, h_mass, h_bridge⟩ := h z₁ z₂ hz₁ hz₂
  -- Apply the polarized representation, then bound by triangle inequality.
  rw [h_bridge a ha₀ ha_R hPET]
  -- The expression is `(1/4) · Σ_k iᵏ · ∫ exp(i a·p) dμ_k`.
  -- ‖(1/4) · Σ‖ ≤ (1/4) · Σ ‖i^k · ∫‖ ≤ (1/4) · Σ 1 · μ_k.univ.
  set bound := C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
                * (1 + (tubeBoundaryDist z₁)⁻¹) ^ M
                * (1 + (tubeBoundaryDist z₂)⁻¹) ^ M with hbound_def
  -- Bound each Fourier integral by μ_k.univ.toReal.
  have h_each_bound : ∀ k : Fin 4,
      ‖∫ p : Fin (d + 1) → ℝ,
          Complex.exp (Complex.I *
            (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖
        ≤ ((μ k) Set.univ).toReal := by
    intro k
    haveI : IsFiniteMeasure (μ k) := h_finite k
    -- ‖∫ f dμ‖ ≤ ∫ ‖f‖ dμ ≤ ∫ 1 dμ = μ.univ.toReal.
    calc ‖∫ p, Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖
        ≤ ∫ p, ‖Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ)))‖ ∂(μ k) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ _ : Fin (d + 1) → ℝ, (1 : ℝ) ∂(μ k) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro p
          show ‖Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ)))‖ = 1
          rw [show Complex.I *
                (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ)) =
              ((∑ i : Fin d, a (Fin.succ i) * p i.succ : ℝ) : ℂ) * Complex.I by
            push_cast
            ring]
          exact Complex.norm_exp_ofReal_mul_I _
      _ = ((μ k) Set.univ).toReal := by
          rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
          rfl
  -- Now: ‖(1/4) · Σ_k iᵏ · ∫_k‖ ≤ (1/4) · Σ_k ‖iᵏ‖ · ‖∫_k‖ ≤ (1/4) · Σ_k 1 · μ_k.univ.toReal
  -- ≤ (1/4) · 4 · bound = bound.
  calc ‖(1 / 4 : ℂ) * ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
            ∫ p, Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖
      ≤ ‖(1 / 4 : ℂ)‖ * ‖∑ k : Fin 4, Complex.I ^ (k : ℕ) *
            ∫ p, Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖ := by
        rw [norm_mul]
    _ ≤ ‖(1 / 4 : ℂ)‖ * ∑ k : Fin 4, ‖Complex.I ^ (k : ℕ) *
            ∫ p, Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact norm_sum_le _ _
    _ = ‖(1 / 4 : ℂ)‖ * ∑ k : Fin 4, ‖Complex.I ^ (k : ℕ)‖ *
            ‖∫ p, Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂(μ k)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_mul]
    _ ≤ ‖(1 / 4 : ℂ)‖ * ∑ k : Fin 4, 1 * ((μ k) Set.univ).toReal := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul
        · -- ‖I^k‖ ≤ 1.
          rw [norm_pow, Complex.norm_I, one_pow]
        · exact h_each_bound k
        · exact norm_nonneg _
        · exact zero_le_one
    _ ≤ ‖(1 / 4 : ℂ)‖ * ∑ _ : Fin 4, 1 * bound := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ zero_le_one
        exact h_mass k
    _ = bound := by
        simp [Finset.sum_const]

/-! ### L4 production axiom withdrawn

**Status (2026-05-09): production axiom withdrawn after PR-#86 review;
conditional reduction kept.**

An earlier draft of this file (2026-05-08) shipped a production axiom
`wightman_l4_spectral_data_axiom : L4SpectralData Wfn n m` discharging
the L4 hypothesis unconditionally for any Wightman family. The axiom
was withdrawn after the PR-#86 review
([@xiyin137](https://github.com/xiyin137)): per the project's axiom
discipline, new production axioms should encode classical background
infrastructure (SNAG, Bochner, Schwartz-Fubini, Vladimirov-style
SCV/FA) rather than QFT-specific consequences such as the polarized
Fourier representation of `W_analytic_BHW`. `L4SpectralData` is kept
as a conditional structure; downstream consumers must supply it
explicitly.

The textbook discharge content (formerly the axiom's justification)
is the proof obligation that future work will need to discharge as
theorems rather than axioms. It combines:

1. **Spectral resolution** of multi-time matrix elements via SNAG.
2. **Polarization** of off-diagonal sesquilinear forms.
3. **Polynomial growth + boundary regulator** of each polarization
   piece's total mass: matches `fourierLaplaceExtMultiDim_vladimirov_growth`
   (proved in `OSReconstruction/SCV/PaleyWienerSchwartz.lean:3286`)
   on the FL-extension side, transported via
   `bv_implies_fourier_support` + `fl_representation_from_bv` to the
   `W_analytic_BHW` side.
4. **|exp(i p · a)| = 1** for real spatial shifts (used in the
   conditional proof above).

References for the discharge content:
* Streater-Wightman, *PCT, Spin and Statistics, and All That*,
  Theorem 3.1.1 and §3.5.
* Bogoliubov-Logunov-Todorov, *Axiomatic QFT*, Theorem 11.2.
* Glimm-Jaffe, *Quantum Physics*, §6.2.
* Reed-Simon II §IX.8.

The downstream cluster proof (`W_analytic_cluster_integral_via_ruelle`)
remains `sorry`'d at the dominator-integrability step; see
`docs/ruelle_bound_vacuity_concern.md` for the IBP rework plan. -/

end Ruelle
end OSReconstruction

end
