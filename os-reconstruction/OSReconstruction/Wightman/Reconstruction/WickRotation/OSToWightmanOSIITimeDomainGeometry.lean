import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeParametricContinuation
import Mathlib.Analysis.Convex.PathConnected

/-!
# Geometry of the OS-II time domain

These pure domain facts are shared by qualitative Ward continuation and the
quantitative rank construction. Neither consumer needs to import the other.
-/

open Complex Set

namespace OSReconstruction
namespace OSIIChapterV

/-- The product right half-plane is convex. -/
theorem convex_osiiTimeRightHalfPlane (k : Nat) :
    Convex Real (osiiTimeRightHalfPlane k) := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
  change 0 < a * (x i).re + b * (y i).re
  rcases ha.eq_or_lt with rfl | ha
  · have hb_one : b = 1 := by linarith
    simpa [hb_one] using hy i
  rcases hb.eq_or_lt with rfl | hb
  · have ha_one : a = 1 := by linarith
    simpa [ha_one] using hx i
  exact add_pos (mul_pos ha (hx i)) (mul_pos hb (hy i))

/-- The nonempty product right half-plane is connected. -/
theorem isConnected_osiiTimeRightHalfPlane (k : Nat) :
    IsConnected (osiiTimeRightHalfPlane k) := by
  apply (convex_osiiTimeRightHalfPlane k).isConnected
  exact ⟨fun _ => (1 : Complex), by norm_num [osiiTimeRightHalfPlane]⟩

end OSIIChapterV
end OSReconstruction
