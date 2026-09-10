/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation628Propagation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation

















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

/-- The arity and finite-depth part of the normalized OS II `(6.28)`
majorant. -/
def osiiVI2ArityDepthMajorant
    (alpha : Real) (beta k N : Nat) : Real :=
  alpha * (k : Real) ^ (beta * k) * osiiVI2DepthFactor beta k N

theorem osiiVI2ArityDepthMajorant_nonneg
    {alpha : Real} (halpha : 0 <= alpha)
    (beta k N : Nat) :
    0 <= osiiVI2ArityDepthMajorant alpha beta k N := by
  unfold osiiVI2ArityDepthMajorant osiiVI2DepthFactor
  positivity

/-- The numerical induction in OS II `(6.29)`.  The additional
`2 ^ (beta * k)` at the successor depth is exactly what permits both lower
arities to be bounded by `2 * k`. -/
theorem osiiVI2ArityDepthMajorant_split_sqrt_le
    (alpha : Real) (halpha : 0 <= alpha)
    (beta k M a b : Nat)
    (hk : 0 < k)
    (hab : a + b = 2 * k) :
    Real.sqrt
      (osiiVI2ArityDepthMajorant alpha beta a M *
        osiiVI2ArityDepthMajorant alpha beta b M) <=
      osiiVI2ArityDepthMajorant alpha beta k (M + 1) := by
  have ha_le : a <= 2 * k := by omega
  have hb_le : b <= 2 * k := by omega
  have ha_cast : (a : Real) <= 2 * k := by exact_mod_cast ha_le
  have hb_cast : (b : Real) <= 2 * k := by exact_mod_cast hb_le
  have ha_pow :
      (a : Real) ^ (beta * a) <=
        (2 * k : Real) ^ (beta * a) :=
    pow_le_pow_left₀ (by positivity) ha_cast _
  have hb_pow :
      (b : Real) ^ (beta * b) <=
        (2 * k : Real) ^ (beta * b) :=
    pow_le_pow_left₀ (by positivity) hb_cast _
  have harity :
      (a : Real) ^ (beta * a) * (b : Real) ^ (beta * b) <=
        ((2 : Real) ^ (beta * k) *
          (k : Real) ^ (beta * k)) ^ 2 := by
    calc
      (a : Real) ^ (beta * a) * (b : Real) ^ (beta * b) <=
          (2 * k : Real) ^ (beta * a) *
            (2 * k : Real) ^ (beta * b) :=
        mul_le_mul ha_pow hb_pow (by positivity) (by positivity)
      _ = ((2 : Real) ^ (beta * k) *
            (k : Real) ^ (beta * k)) ^ 2 := by
        rw [← pow_add]
        have hexp : beta * a + beta * b = (beta * k) * 2 := by
          calc
            beta * a + beta * b = beta * (a + b) := by ring
            _ = beta * (2 * k) := by rw [hab]
            _ = (beta * k) * 2 := by ring
        rw [hexp, pow_mul, mul_pow]
  have hdepth :
      osiiVI2DepthFactor beta a M * osiiVI2DepthFactor beta b M =
        (osiiVI2DepthFactor beta k M) ^ 2 := by
    unfold osiiVI2DepthFactor
    rw [← pow_add]
    have hexp :
        beta * a * M + beta * b * M = (beta * k * M) * 2 := by
      calc
        beta * a * M + beta * b * M = beta * (a + b) * M := by ring
        _ = beta * (2 * k) * M := by rw [hab]
        _ = (beta * k * M) * 2 := by ring
    rw [hexp, pow_mul]
  have htarget_nonneg :
      0 <= osiiVI2ArityDepthMajorant alpha beta k (M + 1) :=
    osiiVI2ArityDepthMajorant_nonneg halpha beta k (M + 1)
  refine Real.sqrt_le_iff.2 ⟨htarget_nonneg, ?_⟩
  rw [osiiVI2ArityDepthMajorant, osiiVI2ArityDepthMajorant,
    osiiVI2ArityDepthMajorant, mul_pow]
  rw [show osiiVI2DepthFactor beta k (M + 1) =
      (2 : Real) ^ (beta * k) * osiiVI2DepthFactor beta k M by
    unfold osiiVI2DepthFactor
    rw [← pow_add]
    congr 1
    ring]
  rw [mul_pow]
  calc
    (alpha * (a : Real) ^ (beta * a) *
        osiiVI2DepthFactor beta a M) *
      (alpha * (b : Real) ^ (beta * b) *
        osiiVI2DepthFactor beta b M) =
        alpha ^ 2 *
          ((a : Real) ^ (beta * a) * (b : Real) ^ (beta * b)) *
          (osiiVI2DepthFactor beta k M) ^ 2 := by
      rw [← hdepth]
      ring
    _ <= alpha ^ 2 *
        (((2 : Real) ^ (beta * k) *
          (k : Real) ^ (beta * k)) ^ 2) *
        (osiiVI2DepthFactor beta k M) ^ 2 := by
      gcongr
    _ = alpha ^ 2 * ((k : Real) ^ (beta * k)) ^ 2 *
        ((2 : Real) ^ (beta * k) *
          osiiVI2DepthFactor beta k M) ^ 2 := by
      ring

namespace OSIIChapterV

variable {d k : Nat} [NeZero d]

end OSIIChapterV
end OSReconstruction
