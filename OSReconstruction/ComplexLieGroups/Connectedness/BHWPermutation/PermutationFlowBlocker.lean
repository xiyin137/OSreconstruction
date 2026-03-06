import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.D1OrbitSet

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- Deferred geometric input for the nontrivial permutation branch.

Mathematical meaning:
for a fixed permutation `σ` with `σ ≠ 1` and `n ≥ 2`, prove that the seed set
`permSeedSet (d := d) n σ` is connected. This is purely geometric/topological
and independent of the analytic data of a field `F`.

Here
`permSeedSet (d := d) n σ = ExtendedTube d n ∩ PermutedForwardTube d n σ⁻¹`,
so explicitly
`permSeedSet = {z | z ∈ ExtendedTube d n ∧ permAct (d := d) σ⁻¹ z ∈ ForwardTube d n}`.
Equivalently: points `z` already in ET whose inverse-`σ` reorder lies in the
forward tube.

Role in the BHW pipeline:
this connectedness is converted (via
`isConnected_permSeedSet_iff_permForwardOverlapSet`) to connectedness of the
forward-overlap set, which is then used by the identity-theorem step that
propagates permutation equality of `extendF` on overlap domains.

This single blocker is shared by both nontrivial dimension branches (`d ≥ 2`
and `d = 1`) in `iterated_eow_permutation_extension`.

Numerical status (heuristic):
- Refined campaign (2026-03-05), `d=1,n=2` slice:
  `/private/tmp/permseed_d1n2_refined.py` (8 seeds × 2 eps × k ∈ {5,10,20,40,80}).
  `SUPPORTED` in ALL 80 trials (n_components=1, largest_frac=1.0).
- Root cause of earlier mixed result: old sampler used Im(θ) ∈ [-1,1] which
  MISSES the valid boost range Im(θ) ∈ (π/2, 3π/2) ≈ (1.57, 4.71) required
  for the d=1,n=2 swap case. The "potential falsifier" was a sampling artifact
  (sparse, biased coverage of permSeedSet), not genuine disconnectedness.
- Implication: numerical evidence now strongly supports the assertion for d=1,n=2. -/
theorem blocker_isConnected_permSeedSet_nontrivial
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (_hσ : σ ≠ 1)
    (_hn : ¬ n ≤ 1) :
    IsConnected (permSeedSet (d := d) n σ) := by
  sorry

/-- Deferred `d = 1` overlap-invariance bridge for permutation iteration.

Mathematical meaning:
assume `F` satisfies the standard BHW hypotheses on `ForwardTube 1 n`
(holomorphy, restricted Lorentz invariance, boundary continuity, and local
commutativity). For nontrivial permutation data (`σ ≠ 1`, `n ≥ 2`), show:

if `z` and `σ · z` both lie in `ExtendedTube 1 n`, then
`extendF F (σ · z) = extendF F z`.

Role in the BHW pipeline:
this is exactly the missing `hExtPerm` input for the `d = 1` branch of
`iterated_eow_permutation_extension`, after the `d = 0` case is excluded and
the `d ≥ 2` branch is handled separately.

Numerical status (heuristic, finite ansatz):
- Relative-defect metric used:
  `δ(inv) = |g(inv)| / (|f(inv)| + |f_swap(inv)|)`, where
  `g(q0,q1,p,s) = f(q0,q1,p,s) - f(q1,q0,p,-s)`.
- Run (2026-03-04, seeds `20261300..20261303`) from
  `/private/tmp/d1n2_forwardwitness_relative_defect.py` with degree-3
  antisymmetric ansatz, `source_samples=1200`, `wide_samples=8000`.
- On sampled forwardizable domain (`wide`):
  `δ_p99 ≈ [5.33e-15, 8.47e-15]`,
  `δ_max ≈ [4.75e-14, 7.80e-14]`.
- On sampled source domain:
  `δ_p99 ≈ [1.33e-14, 1.81e-13]`,
  `δ_max ≈ [1.06e-13, 3.42e-12]`.
- `δ` was defined on all sampled points (`defined_fraction = 1.0` in all seeds).
- Interpretation: in this tested ansatz class, the relative antisymmetry defect
  is numerically very small on both source and wide samples.
- Implication for assertion validity (under this tested ansatz + `δ` metric):
  **no numerical falsifier detected**; the sampled data are supportive of the
  lemma assertion. -/
theorem blocker_iterated_eow_hExtPerm_d1_nontrivial
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (_hσ : σ ≠ 1)
    (_hn : ¬ n ≤ 1) :
    ∀ (z : Fin n → Fin (1 + 1) → ℂ),
      z ∈ ExtendedTube 1 n →
      (fun k => z (σ k)) ∈ ExtendedTube 1 n →
      extendF F (fun k => z (σ k)) = extendF F z := by
  let _ := hF_holo
  let _ := hF_lorentz
  let _ := hF_bv
  let _ := hF_local
  sorry

end BHW
