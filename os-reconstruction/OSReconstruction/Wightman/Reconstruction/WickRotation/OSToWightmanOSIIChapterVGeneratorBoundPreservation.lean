/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIComplexSemigroupContraction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates











noncomputable section

open Complex Set Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : Nat} [NeZero d]

/-- The genuine split-coordinate generator uses the original-OS complex
semigroup in its distinguished bridge, without a growth-condition argument. -/
@[simp]
theorem generatorSemigroupPairing_apply
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS)
    (right : (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS)
    (w : OSIITimeGapSpace k) :
    osiiSemigroupMixedHilbertPairing OS left right
        (i.splitCoordinatesCLM w) =
      @inner Complex (OSHilbertSpace OS) _
        (left (fun a => -star (w (i.leftGlobalIndex a))))
        (osiiOriginalOSHilbertComplex OS (w i.bridgeGlobalIndex)
          (right (fun b => w (i.rightGlobalIndex b)))) := by
  rfl

/-- The actual original-OS generator has its sharp Hilbert Cauchy--Schwarz
bound without the false legacy arity-growth assumption. -/
theorem norm_generatorSemigroupPairing_le_norm_mul
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS)
    (right : (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS)
    (w : OSIITimeGapSpace k)
    (hbridge : 0 < (w i.bridgeGlobalIndex).re) :
    ‖osiiSemigroupMixedHilbertPairing OS left right
        (i.splitCoordinatesCLM w)‖ <=
      ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ *
        ‖right (fun b => w (i.rightGlobalIndex b))‖ := by
  rw [generatorSemigroupPairing_apply]
  calc
    ‖@inner Complex (OSHilbertSpace OS) _
        (left (fun a => -star (w (i.leftGlobalIndex a))))
        (osiiOriginalOSHilbertComplex OS
          (w i.bridgeGlobalIndex)
          (right (fun b => w (i.rightGlobalIndex b))))‖ <=
        ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ *
          ‖osiiOriginalOSHilbertComplex OS
            (w i.bridgeGlobalIndex)
            (right (fun b => w (i.rightGlobalIndex b)))‖ :=
      norm_inner_le_norm _ _
    _ <=
        ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ *
          (‖osiiOriginalOSHilbertComplex OS
              (w i.bridgeGlobalIndex)‖ *
            ‖right (fun b => w (i.rightGlobalIndex b))‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ <=
        ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ *
          (1 * ‖right (fun b => w (i.rightGlobalIndex b))‖) := by
      gcongr
      exact osiiOriginalOSHilbertComplex_norm_le_one OS _ hbridge
    _ =
        ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ *
          ‖right (fun b => w (i.rightGlobalIndex b))‖ := by ring

/-- Unequal reflected squared energies control the genuine original-OS
generator by their exact geometric mean. -/
theorem norm_generatorSemigroupPairing_le_sqrt_mul_of_norm_sq_le
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS)
    (right : (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS)
    (w : OSIITimeGapSpace k)
    (hbridge : 0 < (w i.bridgeGlobalIndex).re)
    (Bleft Bright : Real)
    (hleft_nonneg : 0 <= Bleft)
    (hright_nonneg : 0 <= Bright)
    (hleft :
      ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ ^ 2 <= Bleft)
    (hright :
      ‖right (fun b => w (i.rightGlobalIndex b))‖ ^ 2 <= Bright) :
    ‖osiiSemigroupMixedHilbertPairing OS left right
        (i.splitCoordinatesCLM w)‖ <=
      Real.sqrt (Bleft * Bright) := by
  let L := left (fun a => -star (w (i.leftGlobalIndex a)))
  let R := right (fun b => w (i.rightGlobalIndex b))
  apply
    (norm_generatorSemigroupPairing_le_norm_mul
      OS i left right w hbridge).trans
  refine
    (Real.le_sqrt
      (mul_nonneg (norm_nonneg L) (norm_nonneg R))
      (mul_nonneg hleft_nonneg hright_nonneg)).2 ?_
  rw [mul_pow]
  have hleft' : ‖L‖ ^ 2 <= Bleft := by simpa [L] using hleft
  have hright' : ‖R‖ ^ 2 <= Bright := by simpa [R] using hright
  exact mul_le_mul hleft' hright' (sq_nonneg _) hleft_nonneg

/-- Compatibility wrapper for the growth-free reflected geometric mean. -/
theorem norm_generatorSemigroupCandidate_le_sqrt_mul_of_norm_sq_le
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS)
    (right : (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS)
    (w : OSIITimeGapSpace k)
    (hbridge : 0 < (w i.bridgeGlobalIndex).re)
    (Bleft Bright : Real)
    (hleft_nonneg : 0 <= Bleft)
    (hright_nonneg : 0 <= Bright)
    (hleft :
      ‖left (fun a => -star (w (i.leftGlobalIndex a)))‖ ^ 2 <= Bleft)
    (hright :
      ‖right (fun b => w (i.rightGlobalIndex b))‖ ^ 2 <= Bright) :
    ‖generatorSemigroupCandidate OS lgc i left right w‖ <=
      Real.sqrt (Bleft * Bright) :=
  norm_generatorSemigroupPairing_le_sqrt_mul_of_norm_sq_le
    OS i left right w hbridge Bleft Bright
      hleft_nonneg hright_nonneg hleft hright

end OSIIChapterV
end OSReconstruction
