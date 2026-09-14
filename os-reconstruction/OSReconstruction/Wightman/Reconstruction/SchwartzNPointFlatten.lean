import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions

/-!
# Flattened n-point Schwartz coordinates

Shared coordinate maps for both reconstruction directions. These declarations
were previously housed in the E-to-R semigroup construction.
-/

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
abbrev flattenSchwartzNPoint {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1)).symm

omit [NeZero d] in
abbrev unflattenSchwartzNPoint {n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivReal n (d + 1))

omit [NeZero d] in
@[simp] theorem flattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzNPoint d n) (u : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d) f u = f ((flattenCLEquivReal n (d + 1)).symm u) := rfl

omit [NeZero d] in
@[simp] theorem unflattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (x : NPointDomain d n) :
    unflattenSchwartzNPoint (d := d) f x = f (flattenCLEquivReal n (d + 1) x) := rfl
