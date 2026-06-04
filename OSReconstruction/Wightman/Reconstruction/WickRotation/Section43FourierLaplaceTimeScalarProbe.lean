import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct

/-!
# Section 4.3 Finite-Time Scalar Probes

This companion keeps the scalar-probe construction for finite time-product
tensors out of the already-large product file.  It is the neutral
nuclear-extension step used by the OS-II product-tensor lane: a continuous
multilinear functional of the one-dimensional time factors has a scalar
continuous linear extension to the full finite-time Schwartz space.
-/

noncomputable section

open scoped Topology

namespace OSReconstruction

/-- Finite-time product tensors have the expected scalar probe obtained by
transporting the existing Schwartz nuclear extension through the
`Fin n -> ℝ` / `Fin n -> Fin 1 -> ℝ` equivalence.

This is the neutral probe-construction step needed before the OS-II
Schwinger-specific scalar probes are instantiated. -/
theorem exists_section43TimeProductTensor_scalarProbe
    (n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap ℝ ℂ) ℂ) :
    ∃ (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap ℝ ℂ,
        T (section43TimeProductTensor fs) = Phi fs := by
  let toTime : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  let PhiOne : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin 1 → ℝ) ℂ) ℂ :=
    Phi.compContinuousLinearMap (fun _ : Fin n => toTime)
  obtain ⟨W, hW, _hWuniq⟩ := schwartz_nuclear_extension 0 n PhiOne
  let toOneProduct :
      SchwartzMap (Fin n → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin n → Fin 1 → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43TimeAsOnePointCLE n).symm
  refine ⟨W.comp toOneProduct, ?_⟩
  intro fs
  calc
    (W.comp toOneProduct) (section43TimeProductTensor fs)
        = W (SchwartzMap.productTensor
            (fun i : Fin n =>
              SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (fs i))) := by
          rw [ContinuousLinearMap.comp_apply]
          exact congrArg W (section43TimeAsOnePoint_productTensor fs)
    _ = PhiOne
        (fun i : Fin n =>
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (fs i)) := by
          exact hW _
    _ = Phi fs := by
          have harg :
              (fun i : Fin n =>
                toTime
                  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (fs i))) = fs := by
            funext i
            ext x
            simp [toTime, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
          simp [PhiOne, harg]

end OSReconstruction
