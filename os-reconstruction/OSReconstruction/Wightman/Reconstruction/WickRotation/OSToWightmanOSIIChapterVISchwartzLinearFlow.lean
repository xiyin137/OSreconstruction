import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISchwartzLinearAction
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Integrating a Schwartz distributional linear Ward identity

Differentiate compact source orbits in the checked Schwartz topology, then
use compact-source density for the full distributional invariance statement.
-/

noncomputable section

open Complex Set Topology
open scoped Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction.OSIIChapterVI

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]

private theorem dense_compact_schwartz :
    Dense {phi : SchwartzMap E Complex | HasCompactSupport (phi : E -> Complex)} := by
  let m := Module.finrank Real E
  let c := (Module.finBasis Real E).equivFunL
  let C : SchwartzMap (Fin m -> Real) Complex →L[Complex] SchwartzMap E Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex c
  have hsurj : Function.Surjective C := by
    intro phi
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv Complex c.symm phi, ?_⟩
    ext x
    change phi (c.symm (c x)) = phi x
    rw [c.symm_apply_apply]
  have hd := hsurj.denseRange.dense_image C.continuous
    (SchwartzMap.dense_hasCompactSupport (m := m))
  apply hd.mono
  rintro phi ⟨psi, hpsi, rfl⟩
  exact hpsi.comp_homeomorph c.toHomeomorph

/-- An actual smooth linear flow integrates its Ward identity on every
compact Schwartz source. The derivative hypothesis fixes the action
convention: `e'(t)x = e(t)(A x)`. -/
theorem compactLinearFlow_pairing_eq
    (T : SchwartzMap E Complex →L[Complex] Complex)
    (A : E →L[Real] E)
    (hWard : ∀ psi : SchwartzMap E Complex, T (linearVectorFieldCLM A psi) = 0)
    (e : Real -> E ≃L[Real] E)
    (he : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (hzero : ∀ x : E, e 0 x = x)
    (hflow : ∀ (t : Real) (x : E),
      HasDerivAt (fun u : Real => e u x) (e t (A x)) t)
    (phi : SchwartzMap E Complex) (hphi : HasCompactSupport (phi : E -> Complex))
    (t : Real) :
    T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi) = T phi := by
  have hd (s : Real) : HasDerivAt
      (fun u : Real => T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e u) phi))
      0 s := by
    have h := hasDerivAt_compactLinearAction_pairing T e he hinv phi hphi s
      (linearVectorFieldCLM A
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e s) phi)) (by
        intro x
        have hsource : linearVectorFieldCLM A
            (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e s) phi) x =
            fderiv Real (phi : E -> Complex) (e s x) (e s (A x)) := by
          rw [linearVectorFieldCLM_apply]
          change fderiv Real ((phi : E -> Complex) ∘ (e s)) x (A x) = _
          rw [(e s).comp_right_fderiv]
          rfl
        rw [hsource]
        exact (phi.hasFDerivAt (e s x)).comp_hasDerivAt s (hflow s x))
    simpa only [hWard] using h
  have hc := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hbase : SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e 0) phi = phi := by
    ext x
    change phi (e 0 x) = phi x
    rw [hzero]
  simpa only [hbase] using hc

/-- The same finite-flow invariance for all Schwartz sources, obtained
only after both sides are continuous functionals on the full source space. -/
theorem linearFlow_pairing_eq
    (T : SchwartzMap E Complex →L[Complex] Complex)
    (A : E →L[Real] E)
    (hWard : ∀ psi : SchwartzMap E Complex, T (linearVectorFieldCLM A psi) = 0)
    (e : Real -> E ≃L[Real] E)
    (he : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (hzero : ∀ x : E, e 0 x = x)
    (hflow : ∀ (t : Real) (x : E),
      HasDerivAt (fun u : Real => e u x) (e t (A x)) t)
    (phi : SchwartzMap E Complex) (t : Real) :
    T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi) = T phi := by
  refine dense_compact_schwartz.induction
    (fun psi hpsi => compactLinearFlow_pairing_eq T A hWard e he hinv hzero hflow psi hpsi t)
    (isClosed_eq (T.continuous.comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t)).continuous) T.continuous) phi

end OSReconstruction.OSIIChapterVI
