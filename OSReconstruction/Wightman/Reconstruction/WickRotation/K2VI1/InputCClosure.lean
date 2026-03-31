import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2Density

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Final-stage closure bridge for the `k = 2` OS route: once a measurable
polynomially bounded Euclidean kernel already matches `OS.S 2` on the compact
origin-avoiding difference-shell generators, it automatically matches on every
classical two-point difference shell. The remaining assembly seam can therefore
be localized to the reduced origin-avoiding shell class. -/
theorem differenceShell_agreement_of_zeroOriginAvoidingCompact_local
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hShell0 :
      ∀ (χ h : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) →
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
          OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (χ h : SchwartzSpacetime d) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  let A : Set (ZeroDiagonalSchwartz d 2) :=
    {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  let B : Submodule ℂ (ZeroDiagonalSchwartz d 2) := Submodule.span ℂ A
  let L :=
    OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
  let S := OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2
  have hBzero_span : ∀ ⦃f : ZeroDiagonalSchwartz d 2⦄,
      f ∈ Submodule.span ℂ A → L f = S f := by
    intro f hf
    exact
      Submodule.span_induction
        (s := A)
        (p := fun x _ => L x = S x)
        (mem := by
          intro g hg
          rcases hg with ⟨χg, hg, hg0, hg_compact, rfl⟩
          exact hShell0 χg hg hg0 hg_compact)
        (zero := by simp [L, S])
        (add := by
          intro x y hx hy hx_eq hy_eq
          simp [L, S, hx_eq, hy_eq])
        (smul := by
          intro c x hx hx_eq
          simp [L, S, hx_eq])
        hf
  have hBzero : ∀ f ∈ B, L f = S f := by
    intro f hf
    have hf' : f ∈ Submodule.span ℂ A := by
      simpa [B] using hf
    exact hBzero_span hf'
  have hclosed :
      IsClosed {f : ZeroDiagonalSchwartz d 2 | L f = S f} := by
    exact isClosed_eq L.continuous S.continuous
  have hsubset :
      (B : Set (ZeroDiagonalSchwartz d 2)) ⊆ {f : ZeroDiagonalSchwartz d 2 | L f = S f} := by
    intro f hf
    exact hBzero f hf
  have hclosure_subset :
      (B.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) ⊆
        {f : ZeroDiagonalSchwartz d 2 | L f = S f} :=
    closure_minimal hsubset hclosed
  have hmem :
      ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h) ∈
        (B.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
    simpa [A, B] using
      _root_.differenceShell_mem_topologicalClosure_zeroOriginAvoidingCompact_span
        (d := d) χ h
  exact hclosure_subset hmem

end OSReconstruction
