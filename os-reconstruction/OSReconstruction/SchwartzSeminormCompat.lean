/-
Copyright (c) 2026 OSReconstruction Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

/-!
# Scalar-field independence of the Schwartz seminorms

Mathlib's `SchwartzMap.seminorm` is `@[no_expose]`, so under the module system the
definitional identities `SchwartzMap.seminorm ℂ k n f = SchwartzMap.seminorm ℝ k n f` and
`schwartzSeminormFamily 𝕜 E F p f = SchwartzMap.seminorm 𝕜 p.1 p.2 f` are no longer
available by `rfl`/`change` to importing modules. These two lemmas restore them as
rewrite rules.
-/

namespace SchwartzMap

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Schwartz seminorm does not depend on the scalar field. -/
theorem seminorm_eq_real (k n : ℕ) (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 k n f = SchwartzMap.seminorm ℝ k n f := by
  rw [SchwartzMap.seminorm_apply, SchwartzMap.seminorm_apply]

/-- `schwartzSeminormFamily` evaluated at a pair, as a rewrite rule. -/
theorem schwartzSeminormFamily_apply' (p : ℕ × ℕ) (f : 𝓢(E, F)) :
    schwartzSeminormFamily 𝕜 E F p f = SchwartzMap.seminorm 𝕜 p.1 p.2 f := rfl

end SchwartzMap
