/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.Wightman.Spacetime.Metric
import OSReconstruction.Wightman.Groups.Lorentz

/-!
# Bridge Lemmas for Axiom Replacement

This file proves equivalences between the type systems used in the
`ComplexLieGroups/` and `SCV/` infrastructure modules and the types used
in `Wightman/Reconstruction/AnalyticContinuation.lean`.

These bridge lemmas enable the axioms `edge_of_the_wedge` and
`bargmann_hall_wightman` to be replaced with theorems from the
infrastructure modules.

## Key equivalences

* `minkowskiSignature_eq_metricSignature` — the metric signature functions agree
* `lorentzGroupEquiv` — equivalence between `LorentzLieGroup.FullLorentzGroup`
  and `FullLorentzGroup`
* `lorentzGroupToWightman` — preferred conversion for the default connected
  Lorentz group on the `LorentzLieGroup` side
* `inOpenForwardCone_iff` — forward cone conditions agree
* `complexLorentzGroup_metric_compat` — ComplexLorentzGroup satisfies the Wightman metric condition

## Import structure

This file imports from:
- `ComplexLieGroups/` (via Connectedness.lean) — no `[NeZero d]` required
- `SCV/` (via TubeDomainExtension.lean) — tube domain definitions
- `Wightman/Spacetime/Metric.lean` — lightweight, defines `metricSignature`, `minkowskiNormSq`
- `Wightman/Groups/Lorentz.lean` — lightweight, defines `FullLorentzGroup`,
  and the default connected `LorentzGroup`

It does NOT import `AnalyticContinuation.lean` (which contains the axioms and
heavy dependencies on distributions/Schwartz space), avoiding circular imports.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Complex Topology Matrix

variable {d : ℕ} [NeZero d]

/-! ### Metric signature equivalence -/

/-- The metric signature in `LorentzLieGroup` equals the one in `MinkowskiSpace`.
    Both are `fun i => if i = 0 then -1 else 1`. -/
theorem minkowskiSignature_eq_metricSignature :
    LorentzLieGroup.minkowskiSignature d = MinkowskiSpace.metricSignature d := rfl

/-- The Minkowski matrix in `LorentzLieGroup` equals the one in `MinkowskiSpace`. -/
theorem lorentzLieGroup_minkowskiMatrix_eq :
    LorentzLieGroup.minkowskiMatrix d = minkowskiMatrix d :=
  congr_arg Matrix.diagonal minkowskiSignature_eq_metricSignature

/-! ### IsLorentzMatrix equivalence -/

/-- The two `IsLorentzMatrix` predicates are equivalent. -/
theorem isLorentzMatrix_iff (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    LorentzLieGroup.IsLorentzMatrix d Λ ↔ IsLorentzMatrix d Λ := by
  unfold LorentzLieGroup.IsLorentzMatrix IsLorentzMatrix
  rw [lorentzLieGroup_minkowskiMatrix_eq]

/-! ### LorentzGroup equivalence -/

/-- Equivalence between the ambient full Lorentz groups from `LorentzLieGroup`
    and `Wightman/Groups/Lorentz`.
    The underlying matrices are identical. -/
def lorentzGroupEquiv : LorentzLieGroup.FullLorentzGroup d ≃ FullLorentzGroup d where
  toFun Λ := ⟨Λ.val, (isLorentzMatrix_iff Λ.val).mp Λ.prop⟩
  invFun Λ := ⟨Λ.val, (isLorentzMatrix_iff Λ.val).mpr Λ.prop⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The equivalence preserves the underlying matrix. -/
@[simp]
 theorem lorentzGroupEquiv_val (Λ : LorentzLieGroup.FullLorentzGroup d) :
    (lorentzGroupEquiv Λ).val = Λ.val := rfl

/-- The inverse equivalence preserves the underlying matrix. -/
@[simp]
theorem lorentzGroupEquiv_symm_val (Λ : FullLorentzGroup d) :
    (lorentzGroupEquiv.symm Λ).val = Λ.val := rfl

/-! ### IsProper and IsOrthochronous compatibility -/

/-- `IsProperLorentz` from `LorentzLieGroup` corresponds to `IsProper` from Wightman. -/
theorem isProperLorentz_iff_isProper (Λ : LorentzLieGroup.FullLorentzGroup d) :
    LorentzLieGroup.IsProperLorentz d Λ ↔
    FullLorentzGroup.IsProper (lorentzGroupEquiv Λ) := by
  simp [LorentzLieGroup.IsProperLorentz, FullLorentzGroup.IsProper]

/-- `IsOrthochronous` from LorentzLieGroup corresponds to `IsOrthochronous` from Wightman. -/
theorem isOrthochronous_iff (Λ : LorentzLieGroup.FullLorentzGroup d) :
    LorentzLieGroup.IsOrthochronous d Λ ↔
    FullLorentzGroup.IsOrthochronous (lorentzGroupEquiv Λ) := by
  simp [LorentzLieGroup.IsOrthochronous, FullLorentzGroup.IsOrthochronous]

/-! ### Connected Lorentz group conversion -/

/-- Convert from the default connected `LorentzGroup` on the `LorentzLieGroup`
    side to the default connected `LorentzGroup` in the Wightman layer. -/
def lorentzGroupToWightman
    (Λ : LorentzLieGroup.LorentzGroup d) :
    LorentzGroup d :=
  ⟨Λ.val.val,
    (isLorentzMatrix_iff Λ.val.val).mp Λ.val.prop,
    (isProperLorentz_iff_isProper Λ.val).mp Λ.prop.1,
    (isOrthochronous_iff Λ.val).mp Λ.prop.2⟩

/-- Convert from the new default connected `LorentzGroup` (Wightman) to
    the default connected `LorentzGroup` on the `LorentzLieGroup` side. -/
def wightmanToLorentzGroup
    (Λ : LorentzGroup d) :
    LorentzLieGroup.LorentzGroup d :=
  ⟨lorentzGroupEquiv.symm Λ.toFull,
    (isProperLorentz_iff_isProper _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact LorentzGroup.det_eq_one Λ),
    (isOrthochronous_iff _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact LorentzGroup.zero_zero_ge_one Λ)⟩

/-- The underlying matrix is preserved by the conversion. -/
@[simp]
theorem lorentzGroupToWightman_val_val
    (Λ : LorentzLieGroup.LorentzGroup d) :
    (lorentzGroupToWightman Λ).val = Λ.val.val := rfl

/-! ### InOpenForwardCone equivalence -/

/-- The `InOpenForwardCone` from `BHW` (using `minkowskiSignature` and `x^2`)
    is equivalent to the Wightman version (using `metricSignature` and `x * x`). -/
theorem inOpenForwardCone_iff (η : Fin (d + 1) → ℝ) :
    BHW.InOpenForwardCone d η ↔
    (η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0) := by
  unfold BHW.InOpenForwardCone MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by
    convert h2 using 1; apply Finset.sum_congr rfl; intro i _
    rw [minkowskiSignature_eq_metricSignature]; ring⟩

/-- The `BHW.ForwardTube` from `Connectedness.lean` is the same as the Wightman
    `ForwardTube` (once `InOpenForwardCone` equivalence is applied).

    This restates `BHW.ForwardTube` using `MinkowskiSpace.minkowskiNormSq`,
    matching the Wightman `ForwardTube` definition. -/
theorem forwardTube_eq_wightman :
    BHW.ForwardTube d n = { z | ∀ k : Fin n,
      let prev : Fin (d + 1) → ℂ := if _ : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
      let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
      η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0 } := by
  ext z
  simp only [BHW.ForwardTube, Set.mem_setOf_eq]
  exact forall_congr' fun k => inOpenForwardCone_iff _

/-! ### ComplexLorentzGroup metric compatibility -/

/-- Our `ComplexLorentzGroup`'s metric condition satisfies the exact formula
    used in `AnalyticContinuation.lean` (which uses `metricSignature` instead
    of `minkowskiSignature`).

    This allows constructing elements of the Wightman `ComplexLorentzGroup` from
    our `ComplexLorentzGroup`. -/
theorem complexLorentzGroup_metric_compat (Λ : ComplexLorentzGroup d)
    (μ ν : Fin (d + 1)) :
    ∑ α : Fin (d + 1),
      (MinkowskiSpace.metricSignature d α : ℂ) * Λ.val α μ * Λ.val α ν =
    if μ = ν then (MinkowskiSpace.metricSignature d μ : ℂ) else 0 := by
  -- minkowskiSignature = metricSignature definitionally
  exact Λ.metric_preserving μ ν

/-! ### TubeDomain equivalence -/

/-- `SCV.TubeDomain` is definitionally equal to the `TubeDomain` defined in
    `AnalyticContinuation.lean`: both are `{ z | (fun i => (z i).im) ∈ C }`.

    `SCV.realEmbed x = fun i => (x i : ℂ)` matches the inline lambda
    `(fun i => (x i : ℂ))` used in the `edge_of_the_wedge` axiom. -/
theorem tubeDomain_eq_def {m : ℕ} (C : Set (Fin m → ℝ)) :
    SCV.TubeDomain C = { z : Fin m → ℂ | (fun i => (z i).im) ∈ C } := rfl

theorem realEmbed_eq_def {m : ℕ} (x : Fin m → ℝ) :
    SCV.realEmbed x = fun i => (x i : ℂ) := rfl

/-! ### Spacelike condition equivalence -/

/-- The spacelike condition in `BHW.bargmann_hall_wightman_theorem`
    (using `minkowskiSignature` and `x^2`) is equivalent to the one in
    the `bargmann_hall_wightman` axiom (using `minkowskiNormSq`). -/
theorem spacelike_condition_iff (v : Fin (d + 1) → ℝ) :
    (∑ μ, LorentzLieGroup.minkowskiSignature d μ * v μ ^ 2 > 0) ↔
    (MinkowskiSpace.minkowskiNormSq d v > 0) := by
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro h <;> convert h using 1 <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    rw [minkowskiSignature_eq_metricSignature] <;> ring

/-! ### complexLorentzAction equivalence -/

/-- `BHW.complexLorentzAction Λ z k μ = ∑ ν, Λ.val μ ν * z k ν`, which is the
    same formula used inline in the `bargmann_hall_wightman` axiom. -/
theorem complexLorentzAction_eq (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1)) :
    BHW.complexLorentzAction Λ z k μ = ∑ ν, Λ.val μ ν * z k ν := rfl

/-! ## How to replace the axioms

### Replacing `edge_of_the_wedge`

In `AnalyticContinuation.lean`:

1. Add `import OSReconstruction.SCV.TubeDomainExtension`
2. The local `TubeDomain` (line 450) is definitionally `SCV.TubeDomain`.
   Either delete it or prove `TubeDomain C = SCV.TubeDomain C := rfl`.
3. `SCV.realEmbed x = fun i => (x i : ℂ)` (see `realEmbed_eq_def`).
4. Replace the axiom body with:
   ```
   theorem edge_of_the_wedge ... :=
     SCV.edge_of_the_wedge_theorem C hC hconv h0 hcone hCne f_plus f_minus
       hf_plus hf_minus E hE bv hbv_cont hf_plus_bv hf_minus_bv
   ```
   Types align directly including the new uniqueness clause.

### Replacing `bargmann_hall_wightman`

In `AnalyticContinuation.lean`:

1. Add `import OSReconstruction.ComplexLieGroups.Connectedness`
2. Add `import OSReconstruction.Bridge.AxiomBridge`
3. Prove `BHW.ForwardTube d n = ForwardTube d n` using `inOpenForwardCone_iff`:
   ```
   theorem BHW_forwardTube_eq : BHW.ForwardTube d n = ForwardTube d n := by
     ext z; simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
     exact forall_congr' fun k => inOpenForwardCone_iff _
   ```
4. Convert between the default connected Lorentz groups on the two sides:
   Use `wightmanToLorentzGroup` / `lorentzGroupToWightman`.
   The underlying matrices are preserved (`lorentzGroupToWightman_val_val`).
5. Convert between the two `ComplexLorentzGroup` types:
   Use `complexLorentzGroup_metric_compat` to build elements of the Wightman
   `ComplexLorentzGroup` from our `ComplexLorentzGroup`.
6. Convert the spacelike condition via `spacelike_condition_iff`.
7. The new `hF_bv` hypothesis: rewrite via `BHW_forwardTube_eq`.
8. Build `BHW.PermutedExtendedTube d n = PermutedExtendedTube d n` using the
   ForwardTube and ComplexLorentzGroup conversions above.
9. Both uniqueness clauses transfer via the set equalities.
-/

end
