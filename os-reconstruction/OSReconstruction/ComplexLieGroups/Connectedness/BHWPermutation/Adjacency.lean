/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW



/-- The full extension of F to the permuted extended tube.
    For z ∈ PermutedExtendedTube, choose a preimage: z = Λ·(π·w) with w ∈ FT,
    and define fullExtendF(z) = F(w). Well-definedness uses complex Lorentz
    invariance + permutation invariance (from local commutativity + edge-of-the-wedge). -/
noncomputable def fullExtendF
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k))
    then F h.choose_spec.choose_spec.choose
    else 0

/-- **Lorentz-permutation commutation** (definitional).
    The complex Lorentz action acts on the μ-index (spacetime), while
    permutations act on the k-index (particle). They commute:
    Λ·(π·w) = π·(Λ·w) definitionally. -/
theorem lorentz_perm_commute (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ) (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
    fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ; simp only [complexLorentzAction]

end BHW
