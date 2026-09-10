/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import OSReconstruction.SCV.EuclideanWeylOpen
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalTestDistribution















noncomputable section

open Complex Set TopologicalSpace Topology
open scoped Classical Distributions Manifold

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The strict-positive reduced-gap chamber as an open set, for the global
LF test-function space used by the partition step. -/
def initialPhysicalStrictPositiveOpen :
    Opens (NPointDomain d k) :=
  ⟨initialReducedStrictPositiveGapRegion d k,
    isOpen_initialReducedStrictPositiveGapRegion⟩

omit [NeZero k] in
@[simp]
theorem coe_initialPhysicalStrictPositiveOpen :
    (initialPhysicalStrictPositiveOpen (d := d) (k := k) :
      Set (NPointDomain d k)) =
      initialReducedStrictPositiveGapRegion d k :=
  rfl

/-- A compactly supported reduced Schwartz source whose support lies in an
open set, bundled as an LF test on that open set. -/
def initialPhysicalSchwartzToTestFunction
    (U : Opens (NPointDomain d k))
    (φ : SchwartzNPoint d k)
    (hφ_compact :
      HasCompactSupport (φ : NPointDomain d k → ℂ))
    (hφ_support :
      tsupport (φ : NPointDomain d k → ℂ) ⊆ U) :
    TestFunction U ℂ ⊤ where
  toFun := φ
  contDiff' := φ.smooth ⊤
  hasCompactSupport' := hφ_compact
  tsupport_subset' := hφ_support

omit [NeZero d] [NeZero k] in
@[simp]
theorem coe_initialPhysicalSchwartzToTestFunction
    (U : Opens (NPointDomain d k))
    (φ : SchwartzNPoint d k)
    (hφ_compact :
      HasCompactSupport (φ : NPointDomain d k → ℂ))
    (hφ_support :
      tsupport (φ : NPointDomain d k → ℂ) ⊆ U) :
    (initialPhysicalSchwartzToTestFunction
        (d := d) (k := k) U φ hφ_compact hφ_support :
      NPointDomain d k → ℂ) =
      φ :=
  rfl

omit [NeZero d] [NeZero k] in
/-- The LF smooth-test inclusion returns the original Schwartz source after
bundling it as a compactly supported test. -/
theorem initialPhysicalTestToSchwartzCLM_schwartzToTestFunction
    (U : Opens (NPointDomain d k))
    (φ : SchwartzNPoint d k)
    (hφ_compact :
      HasCompactSupport (φ : NPointDomain d k → ℂ))
    (hφ_support :
      tsupport (φ : NPointDomain d k → ℂ) ⊆ U) :
    initialPhysicalTestToSchwartzCLM
        (d := d) (k := k) U
        (initialPhysicalSchwartzToTestFunction
          (d := d) (k := k) U φ hφ_compact hφ_support) =
      φ := by
  rw [initialPhysicalTestToSchwartzCLM_apply]
  ext x
  rfl

namespace InitialPhysicalLocalTestAtlasPartitionData

end InitialPhysicalLocalTestAtlasPartitionData

end OSIIChapterV
end OSReconstruction
