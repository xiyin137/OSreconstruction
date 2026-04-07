# Regression: `inferInstance` fails for `NormSMulClass ℝ ℂ` / `ContinuousSMul ℝ ℂ` in v4.29.0

## Minimal reproducer

```lean
import Mathlib

-- These all FAIL:
noncomputable example : NormSMulClass ℝ ℂ := inferInstance
noncomputable example : IsBoundedSMul ℝ ℂ := inferInstance
noncomputable example : ContinuousSMul ℝ ℂ := inferInstance

-- NormedSpace ℝ ℂ is synthesized:
noncomputable example : NormedSpace ℝ ℂ := inferInstance

-- And explicit application succeeds:
noncomputable example : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
```

**Tested on:** Lean 4.29.0, Mathlib `8a178386ffc0` (tag `v4.29.0`), macOS Darwin 24.6.0.

## Observed behavior

Typeclass synthesis finds `NormedSpace ℝ ℂ` (via `InnerProductSpace.toNormedSpace` from `instInnerProductSpaceRealComplex`) but then fails to produce `NormSMulClass ℝ ℂ`. The synthesis trace with `set_option trace.Meta.synthInstance true`:

```
[Meta.synthInstance] ❌ NormSMulClass ℝ ℂ
  [Meta.synthInstance.instances] #[@NormMulClass.toNormSMulClass, @NormedSpace.toNormSMulClass]
  [Meta.synthInstance.apply] ❌ apply @NormedSpace.toNormSMulClass to NormSMulClass ℝ ℂ
    [Meta.synthInstance.tryResolve] ❌ NormSMulClass ℝ ℂ ≟ NormSMulClass ?m.7 ?m.8
      [Meta.synthInstance] ✅ NormedSpace ℝ ℂ
        [Meta.synthInstance.apply] ✅ apply @InnerProductSpace.toNormedSpace to NormedSpace ℝ ℂ
```

The failure occurs at the final unification step: `NormedSpace.toNormSMulClass` is selected and `NormedSpace ℝ ℂ` is synthesized, but the resulting `NormSMulClass ℝ ℂ` cannot be unified with the goal. This may indicate a definitional-equality mismatch in the `SMul` or `Norm` structure carried by the `InnerProductSpace` instance path, or a post-refactor gap in the instance graph. We have not pinpointed which specific instance disagrees.

## Representative downstream breakage

In a theorem about Schwartz space integrability, `fun_prop` fails to close `AEStronglyMeasurable` because `Continuous.smul` requires `ContinuousSMul ℝ ℂ`:

```lean
-- Proof that worked in v4.28.0, fails in v4.29.0:
theorem schwartz_poly_integrable_Ioi (f : SchwartzMap ℝ ℂ) (k : ℕ) (x : ℝ) :
    IntegrableOn (fun t => (‖t‖ ^ k : ℝ) • (f : ℝ → ℂ) t) (Ioi x) volume := by
  rw [IntegrableOn, ← integrable_norm_iff (by fun_prop)]
  --                                        ^^^^^^^^
  -- fun_prop fails: cannot prove
  --   AEStronglyMeasurable (fun t => ‖t‖ ^ k • f t) (volume.restrict (Ioi x))
  -- because Continuous.smul needs ContinuousSMul ℝ ℂ
  sorry
```

(Note: `IsScalarTower ℝ ℂ E` also fails to synthesize in some contexts. This may be the same root cause or a separate coherence issue; we have not confirmed they share a single fix.)

## Workaround

The following explicit instances restore the synthesis chain as a local compatibility shim:

```lean
noncomputable instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
noncomputable instance : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
```

## Context

We encountered this while upgrading a downstream Lean 4 project. We understand that the `NormSMulClass` mixin refactor (#24003) and the `InnerProductSpace ℝ ℂ` coherence fix (51ef4a96ee) are well-motivated. See also the discussion at #24011 about instance priorities in normed modules. This report is intended to help identify whether the synthesis failure is an expected gap that needs a bridging instance, or an unintended regression in the instance path that should be repaired upstream.
