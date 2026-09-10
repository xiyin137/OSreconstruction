/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialAssembly














noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Scalar generator modes together with continuous coefficient extraction
from the spatial Schwartz space.

In the intended Hermite application, `coefficient m` extracts the `m`-th
spatial Hermite coefficient and `mode i m` is the Chapter V mixed Hilbert
pairing attached to that mode and split `i`. -/
structure GeneratorSpatialFiniteShellData (d k : ℕ) where
  domain : GeneratorIndex k → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  coefficient :
    ℕ → SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ
  mode :
    GeneratorIndex k → ℕ → OSIITimeGapSpace k → ℂ
  mode_holomorphic :
    ∀ i m, DifferentiableOn ℂ (mode i m) (domain i)

namespace GeneratorSpatialFiniteShellData

variable {d k : ℕ}

/-- The finite spatial-distribution shell obtained by summing the first `N`
scalar modes against their continuous spatial coefficient maps. -/
noncomputable def finiteShell
    (B : GeneratorSpatialFiniteShellData d k)
    (i : GeneratorIndex k)
    (N : ℕ)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d k :=
  ∑ m ∈ Finset.range N, (B.mode i m z) • B.coefficient m

@[simp]
theorem finiteShell_apply
    (B : GeneratorSpatialFiniteShellData d k)
    (i : GeneratorIndex k)
    (N : ℕ)
    (z : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    B.finiteShell i N z χ =
      ∑ m ∈ Finset.range N,
        B.mode i m z * B.coefficient m χ := by
  simp [finiteShell]

/-- Every finite shell is weakly holomorphic because it is a finite sum of
holomorphic scalar modes with constant spatial coefficients. -/
theorem finiteShell_weaklyHolomorphic
    (B : GeneratorSpatialFiniteShellData d k)
    (i : GeneratorIndex k)
    (N : ℕ) :
    OSIIWeaklyHolomorphicOn
      (B.finiteShell i N) (B.domain i) := by
  intro χ
  apply
    (DifferentiableOn.sum
      (u := Finset.range N)
      (fun m _ =>
        (B.mode_holomorphic i m).mul
          (differentiableOn_const
            (c := B.coefficient m χ)))).congr
  intro z hz
  simp [finiteShell_apply]

/-- The exact remaining convergence condition for the finite spatial shells.

This statement contains no hidden continuity requirement in the spatial test:
each finite shell is already a continuous linear functional, and the limiting
continuity is recovered later by Banach-Steinhaus. -/
def LocallyUniformCauchy
    (B : GeneratorSpatialFiniteShellData d k) : Prop :=
  ∀ i χ z, z ∈ B.domain i →
    ∃ V ∈ 𝓝[B.domain i] z,
      UniformCauchySeqOn
        (fun N w => B.finiteShell i N w χ) atTop V

/-- Locally uniform Cauchy control of the finite mode sums constructs the
sourcewise approximation family consumed by spatial assembly. -/
noncomputable def toApproximationFamily
    (B : GeneratorSpatialFiniteShellData d k)
    (hB : B.LocallyUniformCauchy) :
    GeneratorSpatialApproximationFamily d k :=
  GeneratorSpatialApproximationFamily.ofLocallyUniformCauchy
    B.domain B.domain_open
    (fun i N => B.finiteShell i N)
    (fun i N => B.finiteShell_weaklyHolomorphic i N)
    hB

/-- The approximation family produced from finite shells uses exactly the
finite mode sum at every approximation index. -/
@[simp]
theorem toApproximationFamily_approximation
    (B : GeneratorSpatialFiniteShellData d k)
    (hB : B.LocallyUniformCauchy)
    (i : GeneratorIndex k)
    (N : ℕ)
    (z : OSIITimeGapSpace k) :
    (B.toApproximationFamily hB).approximation i N z =
      B.finiteShell i N z := by
  rfl

end GeneratorSpatialFiniteShellData

end OSIIChapterV
end OSReconstruction
