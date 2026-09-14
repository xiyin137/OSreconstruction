import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# Flat-coordinate distribution pairings

This small utility keeps the measure-preserving flattening step independent
of the physical-seed and continuation atlases. Any flattened local
distribution representation can be pulled back to the native reduced
configuration space.
-/

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]

omit [NeZero d] [NeZero k] in
/-- A flattened support-local representation gives the corresponding native
reduced-point pairing after the measure-preserving coordinate change. -/
theorem flatPairing_of_represents
    (T : SchwartzNPoint d k →L[Complex] Complex)
    (H : (Fin (k * (d + 1)) -> Real) -> Complex)
    (V : Set (Fin (k * (d + 1)) -> Real))
    (hrep : SCV.RepresentsDistributionOn
      (T.comp (unflattenSchwartzNPoint (d := d))) H V)
    (f : SchwartzNPoint d k)
    (hf : SCV.SupportsInOpen
      ((flattenSchwartzNPoint (d := d) f :
        SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
          (Fin (k * (d + 1)) -> Real) -> Complex) V) :
    T f =
      ∫ x : NPointDomain d k,
        H (flattenCLEquivReal k (d + 1) x) * f x := by
  have h := hrep (flattenSchwartzNPoint (d := d) f) hf
  have hunflatten :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) f) = f := by
    ext x
    simp
  change
    T (unflattenSchwartzNPoint (d := d)
        (flattenSchwartzNPoint (d := d) f)) =
      ∫ y : Fin (k * (d + 1)) -> Real,
        H y * flattenSchwartzNPoint (d := d) f y at h
  rw [hunflatten] at h
  calc
    T f = ∫ y : Fin (k * (d + 1)) -> Real,
        H y * flattenSchwartzNPoint (d := d) f y := h
    _ = ∫ x : NPointDomain d k,
        H (flattenCLEquivReal k (d + 1) x) *
          flattenSchwartzNPoint (d := d) f
            (flattenCLEquivReal k (d + 1) x) := by
          simpa using
            (integral_flatten_change_of_variables k (d + 1)
              (fun y : Fin (k * (d + 1)) -> Real =>
                H y * flattenSchwartzNPoint (d := d) f y))
    _ = ∫ x : NPointDomain d k,
        H (flattenCLEquivReal k (d + 1) x) * f x := by
          congr 1
          funext x
          congr 1
          apply congrArg (fun z : NPointDomain d k => f z)
          ext i mu
          simp [flattenCLEquivReal_apply]

end OSReconstruction
