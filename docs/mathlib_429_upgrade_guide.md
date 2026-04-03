# Mathlib v4.28 → v4.29 Upgrade Guide

## Root Cause: `backward.isDefEq.respectTransparency`

Lean 4.29 defaults to `backward.isDefEq.respectTransparency = true`, which makes
typeclass synthesis stricter about definitional equality. The `NormedSpace ℝ ℂ` instance
(via `InnerProductSpace ℝ ℂ`) carries a `SMul` that doesn't unify with the one expected
by `NormedSpace.toNormSMulClass` at this stricter level.

**Fix (from CoolRmal on mathlib4#37600):** Use `set_option backward.isDefEq.respectTransparency false in`
before affected defs/theorems. This restores the old (looser) definitional equality checking
for that specific declaration, allowing the typeclass chain to unify. Can be applied per-declaration
or used to construct global instances in a compat file.

See: leanprover-community/mathlib4#37600
Zulip thread: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/583495228

## Compat File (`Mathlib429Compat.lean`)

Provides these instances using `set_option backward.isDefEq.respectTransparency false`:
- `NormSMulClass ℝ ℂ`
- `IsBoundedSMul ℝ ℂ`
- `IsScalarTower ℝ ℂ ℂ`
- `SMulCommClass ℂ ℝ ℂ`
- `SMulCommClass ℝ ℂ ℂ`

Import with `import OSReconstruction.Mathlib429Compat` in files that need these.

## File-by-File Fixes

### 1. Lorentz.lean (~lines 559, 657)
**Issue:** `unfold MinkowskiSpace.metricSignature` creates syntactic mismatch with `diagonal (metricSignature d)`.
**Fix:** Only `unfold IsLorentzMatrix minkowskiMatrix` (not `metricSignature`). Use `noncomm_ring` for `-η * η * -η = η * η * η`. For `parity_mul_timeReversal`, use `exact neg_neg _` instead of `neg_neg` in simp list.

### 2. IteratedCauchyIntegral.lean (~lines 526, 540)
**Issue:** `mem_sphere_iff_norm` is now `@[simp high]`, so `simp` unfolds sphere membership to `‖x - c‖ = r`.
**Fix:** Replace `simp [Fin.snoc_last]; exact hs` with `simpa [Fin.snoc_last] using hs`.

### 3. vNA/Unbounded/Basic.lean (~lines 342, 365, 367)
**Issue:** `IsUniformAddGroup T.domain` not synthesized. `let` binding blocks `rw`.
**Fix:** Add `haveI : IsUniformAddGroup T.domain` via `isUniformEmbedding_subtype_val.isUniformInducing.isUniformAddGroup T.domain.subtype`. Add `dsimp only [φ_ext]` before `rw [h, hφ']`.

### 4. FourierLaplaceCore.lean (6 locations)
**Issue:** `rw [deriv_const_mul_field]` fails — higher-order pattern matching stricter.
**Fix:** Replace with explicit `HasDerivAt` + `.deriv` approach. E.g., compute the derivative via `(hExp.const_mul c).deriv` then rewrite with the result.

### 5. SOConnected.lean (~lines 1444-1445)
**Issue:** `simp [embed]` no longer reduces `embedVal` on Fin indices.
**Fix:** Use `show (embed ...).val ... = _` then `simp [embed, embedVal]`.

### 6. ComplexSchwartz.lean (~lines 87, 120)
**Issue:** `↑a * ↑(f x) = a • ↑(f x)` not closed by simp.
**Fix:** Add `exact (Complex.real_smul).symm`. Use `smul_comm` / `mul_smul_comm` for `I * a` scalar commutativity.

### 7. SemigroupBochner.lean (~line 409)
**Issue:** `simp_rw [integral_const_mul]` pattern matching fails.
**Fix:** `congr 1 with i; congr 1 with j; exact (integral_const_mul _ _).symm`.

### 8. SeparatelyAnalytic.lean (~line 320)
**Issue:** `FiniteDimensional ℝ ℂ` not synthesized.
**Fix:** Add `import Mathlib.LinearAlgebra.Complex.FiniteDimensional`.

### 9. Poincare1D.lean (~line 128)
**Issue:** `fun_prop` fails for `AEStronglyMeasurable (fun t => ‖t‖ ^ k • f t)` because `ContinuousSMul ℝ ℂ` missing.
**Fix:** `import OSReconstruction.Mathlib429Compat`. Rewrite measurability via `Complex.continuous_ofReal` composition.

### 10. UniversalProjection.lean (~line 426)
**Issue:** `PiLp.inner_apply` now produces `∑ inner ℝ ...` not `∑ mul`.
**Fix:** After `rw [PiLp.inner_apply]`, add `congr 1; ext x; simp [inner, mul_comm]`.

### 11. ZeroMeanFourierTransport.lean (~line 125, 181)
**Issue:** `EuclideanSpace.inner_single_right` doesn't simplify inside `smulLeftCLM` lambda. `ξ i` now shows as `ξ.ofLp i`.
**Fix:** Use `have key : ... = ... := by ext ξ; simp [inner]` then `rw [key]`. For scalar cancellation use `smul_comm` or `Algebra.smul_def`.

### 12. SchwartzComplete.lean (multiple)
**Issue:** TopologicalSpace/UniformSpace diamond. `(𝓝 0).IsCountablyGenerated`, `ContinuousSMul ℝ 𝓢(E,F)`, `BarrelledSpace` fail.
**Fix:** Use `set_option backward.isDefEq.respectTransparency false in` on affected theorems. Normalize topology with explicit `change`. Use `@WithSeminorms.banach_steinhaus` with explicit instances.

### 13. SelfAdjointFunctionalViaRMK.lean (multiple)
**Issue:** `SMulCommClass ℂ ℝ H` missing. `NonnegSpectrumClass` synthesis timeout.
**Fix:** `haveI : SMulCommClass ℂ ℝ H := SMulCommClass.symm ℝ ℂ H`. `haveI : NonnegSpectrumClass ℝ (H →L[ℂ] H) := CStarAlgebra.instNonnegSpectrumClass`. `set_option maxHeartbeats 400000` for timeouts.

### 14. SpectralFunctionalViaRMK.lean (~line 286)
**Issue:** `cfc_smul` needs `IsScalarTower ℝ ℂ (H →L[ℂ] H)`.
**Fix:** Replace `cfc_smul` with `cfc_const_mul`, rewriting `•` to `*` first. Or use `set_option backward.isDefEq.respectTransparency false in`.

### 15. SchwartzTensorProduct.lean
**Issue:** `LinearMap.CompatibleSMul` needs `ContinuousSMul`.
**Fix:** `import OSReconstruction.Mathlib429Compat`.

### Cascading files (also need fixes)
- **GeodesicConvexity.lean** — `star_mul'` simp change
- **JostPoints.lean** — `simp [p]; omega` for Fin bound
- **SemigroupRoots.lean** — `set_option backward.isDefEq.respectTransparency false` for `IsScalarTower ℝ≥0`
- **TubeDomainExtension.lean** — `convert h.const_smul ((2 * ↑Real.pi)⁻¹ : ℂ)` to avoid `SMulCommClass`
- **ComplexSemigroup.lean** — `set_option synthInstance.maxHeartbeats 80000` for `NonnegSpectrumClass`
- **SliceIntegral.lean** — `simp` + eta reduction changes
- **LaplaceSchwartz.lean** — `integral_conj` and `integral_const_mul` pattern matching
- **Adjacency.lean** — `hU_eq ▸ Set.mem_univ b` instead of `simp [hU_eq]`
- **OperatorDistribution.lean** — `limUnder` → `Filter.limUnder`
- **SchwartzPartialEval.lean** — `(G := F)` renamed parameter in `compContinuousLinearMapL`
- **DistributionalUniqueness.lean** — cascading from SchwartzComplete topology changes
- **PaleyWiener.lean** — `integral_const_mul`, `inner ℝ` unfold, `Complex.real_smul`
- **SpectralMeasurePolarizedViaRMK.lean** — `IsScalarTower ℝ ℂ H`, import compat
- **Unbounded/Spectral.lean** — `simp` changes for `integral_smul_nnreal_measure`
- **Bochner/Applications.lean, Convergence.lean** — `integral_re` pattern matching

## Infrastructure Changes
- `lean-toolchain`: `v4.28.0` → `v4.29.0`
- `lakefile.toml`: Mathlib `v4.28.0` → `v4.29.0`, GaussianField → `36ae6dd`, add HilleYosida `main`
- New file: `OSReconstruction/Mathlib429Compat.lean`
