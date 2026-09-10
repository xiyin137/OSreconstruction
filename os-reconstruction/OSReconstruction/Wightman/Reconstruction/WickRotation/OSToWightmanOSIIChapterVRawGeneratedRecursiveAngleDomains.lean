/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedLogarithmicDomains














noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

private theorem raw_argumentGeneratorPoint_smul
    {k : Nat} (i : GeneratorIndex k)
    (r : Real)
    (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real) :
    osiiArgumentGeneratorPoint i
        (r • left) (r * theta) (r • right) =
      r • osiiArgumentGeneratorPoint i left theta right := by
  funext j
  simp only [osiiArgumentGeneratorPoint, Pi.smul_apply]
  split_ifs <;> simp

private theorem raw_argumentDiagonal_smul
    {n : Nat} (hn : 1 <= n)
    (r : Real) (x : Fin n -> Real) :
    osiiArgumentDiagonal hn (r • x) =
      r • osiiArgumentDiagonal hn x := by
  funext j
  simp only [osiiArgumentDiagonal, Pi.smul_apply]
  split_ifs <;> simp

private theorem raw_strict_bridge_smul_lt
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) :
    |r * (Real.pi / 2)| < Real.pi / 2 := by
  calc
    |r * (Real.pi / 2)| = r * |Real.pi / 2| := by
      rw [abs_mul, abs_of_nonneg hr0]
    _ = r * (Real.pi / 2) := by
      rw [abs_of_nonneg (by positivity)]
    _ < 1 * (Real.pi / 2) :=
      mul_lt_mul_of_pos_right hr1 (by positivity)
    _ = Real.pi / 2 := one_mul _

/-- A strict radial contraction of the recursive-angle mixed corner is
generated without a vacuum-tail constructor.

The successor step is exactly the two-generator midpoint computation from
OS II page 296.  The only use of scalarZero is the retained real germ in
the zero-tail branch. -/
theorem rawStrict_mixedAnglePoint_smul_mem
    (N s t : Nat)
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) :
    OSIIRawStrictGeneratedLogarithmicArgument .mixed ((t + 1) + s) N
      (r • osiiMixedAnglePoint N s (t + 1)) := by
  induction N generalizing s t with
  | zero =>
      have hzero :
          osiiMixedAnglePoint 0 s (t + 1) =
            (0 : Fin ((t + 1) + s) -> Real) := by
        funext j
        simp [osiiMixedAnglePoint]
      rw [hzero, smul_zero]
      exact OSIIRawStrictGeneratedLogarithmicArgument.initialMixedZero _
  | succ N ih =>
      cases s with
      | zero =>
          have hzero :
              osiiMixedAnglePoint (N + 1) 0 (t + 1) =
                (0 : Fin ((t + 1) + 0) -> Real) := by
            funext j
            simp [osiiMixedAnglePoint]
            omega
          rw [hzero, smul_zero]
          apply OSIIRawStrictGeneratedLogarithmicArgument.mixedOfDiagonal
              (t + 1) (by omega) (N + 1) (0 : Fin (t + 1) -> Real)
          · rfl
          · convert
              (OSIIRawStrictGeneratedLogarithmicArgument.scalarZero
                (2 * (t + 1) - 1) (N + 1)) using 1
            funext j
            simp [osiiArgumentDiagonal]
      | succ s =>
          have hleftLarge :
              OSIIRawStrictGeneratedLogarithmicArgument .mixed
                (2 * (t + 1) + (s + 1)) N
                (r • osiiMixedAnglePoint N (s + 1) (2 * (t + 1))) := by
            simpa only [Nat.mul_add, Nat.add_assoc] using
              ih (s + 1) (2 * t + 1)
          have hsmall :
              OSIIRawStrictGeneratedLogarithmicArgument .mixed
                (1 + s) N
                (r • osiiMixedAnglePoint N s 1) :=
            ih s 0
          have hfirst :
              OSIIRawStrictGeneratedLogarithmicArgument .scalar
                (2 * ((t + 1) + (s + 1)) - 1) (N + 1)
                (r • osiiFirstRecursiveAngleGeneratorPoint N s t) := by
            have hgen :=
              OSIIRawStrictGeneratedLogarithmicArgument.generatorMemSucc
                (osiiFirstRecursiveAngleSplit s t) N
                (r • osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))
                (r * (Real.pi / 2))
                (r • osiiMixedAnglePoint N s 1)
                hleftLarge hsmall
                (raw_strict_bridge_smul_lt hr0 hr1)
            convert hgen using 1
            simpa [osiiFirstRecursiveAngleGeneratorPoint] using
              (raw_argumentGeneratorPoint_smul
                (osiiFirstRecursiveAngleSplit s t) r
                (osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))
                (Real.pi / 2) (osiiMixedAnglePoint N s 1)).symm
          have hsecond :
              OSIIRawStrictGeneratedLogarithmicArgument .scalar
                (2 * ((t + 1) + (s + 1)) - 1) (N + 1)
                (r • osiiSecondRecursiveAngleGeneratorPoint N s t) := by
            have htheta :
                |r * (-(Real.pi / 2))| < Real.pi / 2 := by
              simpa [abs_neg] using
                (raw_strict_bridge_smul_lt hr0 hr1)
            have hgen :=
              OSIIRawStrictGeneratedLogarithmicArgument.generatorMemSucc
                (osiiSecondRecursiveAngleSplit s t) N
                (r • osiiMixedAnglePoint N s 1)
                (r * (-(Real.pi / 2)))
                (r • osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))
                hsmall hleftLarge htheta
            convert hgen using 1
            simpa [osiiSecondRecursiveAngleGeneratorPoint] using
              (raw_argumentGeneratorPoint_smul
                (osiiSecondRecursiveAngleSplit s t) r
                (osiiMixedAnglePoint N s 1) (-(Real.pi / 2))
                (osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))).symm
          have hmid :=
            OSIIRawStrictGeneratedLogarithmicArgument.scalarConvex
              hfirst hsecond (1 / 2 : Real) (1 / 2 : Real)
              (by norm_num) (by norm_num) (by norm_num)
          have hmid_eq :
              (1 / 2 : Real) •
                  (r • osiiFirstRecursiveAngleGeneratorPoint N s t) +
                (1 / 2 : Real) •
                  (r • osiiSecondRecursiveAngleGeneratorPoint N s t) =
                r • osiiArgumentDiagonal (by omega)
                  (osiiMixedAnglePoint (N + 1) (s + 1) (t + 1)) := by
            calc
              (1 / 2 : Real) •
                    (r • osiiFirstRecursiveAngleGeneratorPoint N s t) +
                  (1 / 2 : Real) •
                    (r • osiiSecondRecursiveAngleGeneratorPoint N s t) =
                  r • ((1 / 2 : Real) •
                      osiiFirstRecursiveAngleGeneratorPoint N s t +
                    (1 / 2 : Real) •
                      osiiSecondRecursiveAngleGeneratorPoint N s t) := by
                simp [smul_add, smul_smul, mul_comm]
              _ = r • osiiArgumentDiagonal (by omega)
                    (osiiMixedAnglePoint (N + 1) (s + 1) (t + 1)) := by
                congr 1
                rw [← osiiRecursiveAngleGenerator_midpoint_eq_diagonal N s t]
                funext j
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                ring
          apply OSIIRawStrictGeneratedLogarithmicArgument.mixedOfDiagonal
              ((t + 1) + (s + 1)) (by omega) (N + 1)
              (r • osiiMixedAnglePoint (N + 1) (s + 1) (t + 1))
          · simp [Pi.smul_apply, osiiMixedAnglePoint]
          · rw [raw_argumentDiagonal_smul]
            rw [← hmid_eq]
            exact hmid

/-- Every strict recursive-angle mixed box belongs to the raw mixed carrier.

For positive tail arity, choose one radius strictly between the largest
coordinate-to-aperture ratio and one, then fill the box below the scaled
positive corner by mixed hyperrectangle closure. -/
theorem rawStrict_recursiveAngle_mixedBox_subset
    (k N : Nat) :
    {x : Fin (k + 1) -> Real |
        x 0 = 0 ∧
          forall j : Fin k,
            |x j.succ| < osiiRecursiveAngleAperture k N j} <=
      osiiRawStrictGeneratedMixedLogarithmicBase (k + 1) N := by
  intro x hx
  by_cases hk : k = 0
  · subst k
    have hxzero : x = 0 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx.1
      · exact Fin.elim0 j
    subst x
    have hzero :=
      rawStrict_mixedAnglePoint_smul_mem N 0 0
        (r := 0) (by norm_num) (by norm_num)
    simpa [osiiMixedAnglePoint] using hzero
  · have hfin : (Finset.univ : Finset (Fin k)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
    let ratio : Fin k -> Real :=
      fun j => |x j.succ| / osiiRecursiveAngleAperture k N j
    let M : Real := Finset.univ.sup' hfin ratio
    have haperture :
        forall j, 0 < osiiRecursiveAngleAperture k N j :=
      fun j => (abs_nonneg (x j.succ)).trans_lt (hx.2 j)
    have hratio_nonneg : forall j, 0 <= ratio j := by
      intro j
      exact div_nonneg (abs_nonneg _) (haperture j).le
    have hM_nonneg : 0 <= M := by
      obtain ⟨j, hj⟩ := hfin
      exact
        (hratio_nonneg j).trans
          (Finset.le_sup' ratio hj)
    have hM_lt_one : M < 1 := by
      rw [Finset.sup'_lt_iff]
      intro j _hj
      exact (div_lt_one (haperture j)).2 (hx.2 j)
    let r : Real := (M + 1) / 2
    have hr_pos : 0 < r := by
      dsimp [r]
      linarith
    have hr_lt_one : r < 1 := by
      dsimp [r]
      linarith
    have hcard : 1 + k = k + 1 := by omega
    let corner : Fin (k + 1) -> Real :=
      fun j =>
        (r • osiiMixedAnglePoint N k 1) ((finCongr hcard).symm j)
    have hcornerRaw :
        OSIIRawStrictGeneratedLogarithmicArgument .mixed (1 + k) N
          (r • osiiMixedAnglePoint N k 1) := by
      simpa only [Nat.zero_add] using
        rawStrict_mixedAnglePoint_smul_mem N k 0 hr_pos.le hr_lt_one
    have hcorner :
        OSIIRawStrictGeneratedLogarithmicArgument .mixed (k + 1) N
          corner :=
      OSIIRawStrictGeneratedLogarithmicArgument.reindex hcard hcornerRaw
    apply
      OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
        hcorner x
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hx.1, abs_zero]
      exact abs_nonneg _
    · have hratio_le : ratio j <= M :=
        Finset.le_sup' ratio (Finset.mem_univ j)
      have hMr : M <= r := by
        dsimp [r]
        linarith
      have hdiv :
          |x j.succ| / osiiRecursiveAngleAperture k N j <= r :=
        hratio_le.trans hMr
      have hx_le :
          |x j.succ| <= r * osiiRecursiveAngleAperture k N j :=
        (div_le_iff₀ (haperture j)).mp hdiv
      simpa [corner, Pi.smul_apply, osiiMixedAnglePoint,
        osiiRecursiveAngleAperture, abs_of_pos hr_pos,
        abs_of_nonneg (recursiveAngle_nonneg (j.val + 1) N),
        mul_comm] using hx_le

end OSIIChapterV
end OSReconstruction
