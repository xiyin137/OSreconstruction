/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedLogarithmicDomains





















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The analytically realizable version of the generated scalar/mixed
logarithmic recurrence.  It differs from
`OSIIGeneratedLogarithmicArgument` only at generator insertion, where the
bridge angle is strict. -/
inductive OSIIStrictGeneratedLogarithmicArgument :
    OSIILogarithmicArgumentKind ->
      (n N : Nat) -> (Fin n -> Real) -> Prop where
  | initialMixedZero (n : Nat) :
      OSIIStrictGeneratedLogarithmicArgument
        .mixed n 0 (0 : Fin n -> Real)
  | scalarConvex
      {k N : Nat} {x y : Fin k -> Real}
      (hx : OSIIStrictGeneratedLogarithmicArgument .scalar k N x)
      (hy : OSIIStrictGeneratedLogarithmicArgument .scalar k N y)
      (a b : Real) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
      OSIIStrictGeneratedLogarithmicArgument
        .scalar k N (a • x + b • y)
  | mixedHyperrectangle
      {n N : Nat} {x : Fin n -> Real}
      (hx : OSIIStrictGeneratedLogarithmicArgument .mixed n N x)
      (y : Fin n -> Real)
      (hy : forall i, |y i| <= |x i|) :
      OSIIStrictGeneratedLogarithmicArgument .mixed n N y
  | generatorMemSucc
      {k : Nat} (i : GeneratorIndex k) (N : Nat)
      (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real)
      (hleft :
        OSIIStrictGeneratedLogarithmicArgument .mixed i.n N left)
      (hright :
        OSIIStrictGeneratedLogarithmicArgument .mixed i.m N right)
      (htheta : |theta| < Real.pi / 2) :
      OSIIStrictGeneratedLogarithmicArgument .scalar k (N + 1)
        (osiiArgumentGeneratorPoint i left theta right)
  | mixedOfDiagonal
      (n : Nat) (hn : 1 <= n) (N : Nat) (x : Fin n -> Real)
      (hx0 : x ⟨0, hn⟩ = 0)
      (hx :
        OSIIStrictGeneratedLogarithmicArgument .scalar (2 * n - 1) N
          (osiiArgumentDiagonal hn x)) :
      OSIIStrictGeneratedLogarithmicArgument .mixed n N x
  | mixedTailMemScalar
      (k N : Nat) (x : Fin (k + 1) -> Real)
      (hx :
        OSIIStrictGeneratedLogarithmicArgument .mixed (k + 1) N x) :
      OSIIStrictGeneratedLogarithmicArgument .scalar k N (Fin.tail x)

/-- The strict generated scalar base at one arity and depth. -/
def osiiStrictGeneratedLogarithmicBase (k N : Nat) :
    Set (Fin k -> Real) :=
  {x | OSIIStrictGeneratedLogarithmicArgument .scalar k N x}

namespace OSIIStrictGeneratedLogarithmicArgument

/-- Forgetting strictness gives a point of the closed generated recurrence. -/
theorem toGenerated
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIStrictGeneratedLogarithmicArgument kind n N x) :
    OSIIGeneratedLogarithmicArgument kind n N x := by
  induction hx with
  | initialMixedZero n =>
      exact OSIIGeneratedLogarithmicArgument.initialMixedZero n
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      exact
        OSIIGeneratedLogarithmicArgument.scalarConvex
          ihx ihy a b ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      exact OSIIGeneratedLogarithmicArgument.mixedHyperrectangle ih y hy
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      exact
        OSIIGeneratedLogarithmicArgument.generatorMemSucc
          i N left theta right ihleft ihright htheta.le
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      exact
        OSIIGeneratedLogarithmicArgument.mixedOfDiagonal
          n hn N x hx0 ih
  | mixedTailMemScalar k N x hx ih =>
      exact
        OSIIGeneratedLogarithmicArgument.mixedTailMemScalar k N x ih

/-- Every coordinate of a strict generated argument lies in the open
principal strip. -/
theorem coordinate_abs_lt_pi_div_two
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIStrictGeneratedLogarithmicArgument kind n N x) :
    forall i, |x i| < Real.pi / 2 := by
  induction hx with
  | initialMixedZero n =>
      intro i
      simpa using (show (0 : Real) < Real.pi / 2 by positivity)
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      intro i
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
      rw [abs_lt]
      exact
        (convex_Ioo (-(Real.pi / 2)) (Real.pi / 2))
          (abs_lt.mp (ihx i)) (abs_lt.mp (ihy i))
          ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      intro i
      exact (hy i).trans_lt (ih i)
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      intro j
      simp only [osiiArgumentGeneratorPoint]
      split_ifs with hjleft hjbridge
      · simpa using ihleft
          ⟨i.n - 1 - j.val, by
            have hn := i.hn
            omega⟩
      · simpa using htheta
      · exact ihright
          ⟨j.val - (i.n - 1), by
            have hn := i.hn
            have hm := i.hm
            have hnm := i.hnm
            omega⟩
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro i
      let j : Fin (2 * n - 1) :=
        ⟨n - 1 + i.val, by omega⟩
      have hj := ih j
      simpa [j, osiiArgumentDiagonal] using hj
  | mixedTailMemScalar k N x hx ih =>
      intro i
      exact ih i.succ

private theorem argumentGeneratorPoint_smul
    {k : Nat} (i : GeneratorIndex k)
    (r : Real)
    (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real) :
    osiiArgumentGeneratorPoint i
        (r • left) (r * theta) (r • right) =
      r • osiiArgumentGeneratorPoint i left theta right := by
  funext j
  simp only [osiiArgumentGeneratorPoint, Pi.smul_apply]
  split_ifs <;> simp

private theorem argumentDiagonal_smul
    {n : Nat} (hn : 1 <= n)
    (r : Real) (x : Fin n -> Real) :
    osiiArgumentDiagonal hn (r • x) =
      r • osiiArgumentDiagonal hn x := by
  funext j
  simp only [osiiArgumentDiagonal, Pi.smul_apply]
  split_ifs <;> simp

/-- A strict radial contraction of any closed generated argument belongs to
the strict generated recurrence.

This is the central bridge between the exact closed recursive-angle
bookkeeping and the open analytic continuation target. -/
theorem smul_toStrict
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIGeneratedLogarithmicArgument kind n N x)
    (r : Real) (hr0 : 0 <= r) (hr1 : r < 1) :
    OSIIStrictGeneratedLogarithmicArgument kind n N (r • x) := by
  induction hx with
  | initialMixedZero n =>
      simpa using
        OSIIStrictGeneratedLogarithmicArgument.initialMixedZero n
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      have hconvex :=
        OSIIStrictGeneratedLogarithmicArgument.scalarConvex
          ihx ihy
          a b ha hb hab
      simpa [smul_add, smul_smul, mul_comm] using hconvex
  | @mixedHyperrectangle n N x hx y hy ih =>
      apply
        OSIIStrictGeneratedLogarithmicArgument.mixedHyperrectangle
          (x := r • x) ih (r • y)
      intro i
      change |r * y i| <= |r * x i|
      rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left (hy i) hr0
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      have htheta' : |r * theta| < Real.pi / 2 := by
        calc
          |r * theta| = r * |theta| := by
            rw [abs_mul, abs_of_nonneg hr0]
          _ <= r * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left htheta hr0
          _ < 1 * (Real.pi / 2) :=
            mul_lt_mul_of_pos_right hr1 (by positivity)
          _ = Real.pi / 2 := one_mul _
      have hgenerator :=
        OSIIStrictGeneratedLogarithmicArgument.generatorMemSucc
          i N (r • left) (r * theta) (r • right)
          ihleft ihright htheta'
      simpa [argumentGeneratorPoint_smul] using hgenerator
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      apply
        OSIIStrictGeneratedLogarithmicArgument.mixedOfDiagonal
          n hn N (r • x)
      · simp [Pi.smul_apply, hx0]
      · simpa [argumentDiagonal_smul] using ih
  | mixedTailMemScalar k N x hx ih =>
      have htail :=
        OSIIStrictGeneratedLogarithmicArgument.mixedTailMemScalar
          k N (r • x) ih
      simpa [Fin.tail, Pi.smul_apply] using htail

/-- Every strict generated scalar base contains its origin. -/
theorem scalar_zero_mem
    (n N : Nat) :
    OSIIStrictGeneratedLogarithmicArgument .scalar n N
      (0 : Fin n -> Real) := by
  have hclosed :=
    OSIIGeneratedLogarithmicArgument.scalar_zero_mem n N
  simpa using
    smul_toStrict hclosed 0 (by norm_num) (by norm_num)

end OSIIStrictGeneratedLogarithmicArgument

theorem strictGeneratedScalarBase_subset_generated
    (k N : Nat) :
    osiiStrictGeneratedLogarithmicBase k N <=
      osiiGeneratedLogarithmicBase k N := by
  intro x hx
  exact hx.toGenerated

/-- Every point of the strict recursive-angle box belongs to the strict
generated scalar base.

For positive arity, take the maximum coordinate-to-aperture ratio, choose a
slightly larger radius still below one, and rescale into the closed recursive
box.  The result then follows from `smul_toStrict`. -/
theorem strict_recursiveAngle_box_subset
    (k N : Nat) :
    {x : Fin k -> Real |
        forall i, |x i| < osiiRecursiveAngleAperture k N i} <=
      osiiStrictGeneratedLogarithmicBase k N := by
  intro x hx
  by_cases hk : k = 0
  · subst k
    have hxzero : x = 0 := Subsingleton.elim _ _
    subst x
    exact
      OSIIStrictGeneratedLogarithmicArgument.scalar_zero_mem 0 N
  · have hfin : (Finset.univ : Finset (Fin k)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
    let ratio : Fin k -> Real :=
      fun i => |x i| / osiiRecursiveAngleAperture k N i
    let M : Real := Finset.univ.sup' hfin ratio
    have haperture :
        forall i, 0 < osiiRecursiveAngleAperture k N i :=
      fun i => (abs_nonneg (x i)).trans_lt (hx i)
    have hratio_nonneg : forall i, 0 <= ratio i := by
      intro i
      exact div_nonneg (abs_nonneg _) (haperture i).le
    have hM_nonneg : 0 <= M := by
      obtain ⟨i, hi⟩ := hfin
      exact
        (hratio_nonneg i).trans
          (Finset.le_sup' ratio hi)
    have hM_lt_one : M < 1 := by
      rw [Finset.sup'_lt_iff]
      intro i _hi
      exact (div_lt_one (haperture i)).2 (hx i)
    let r : Real := (M + 1) / 2
    have hr_pos : 0 < r := by
      dsimp [r]
      linarith
    have hr_lt_one : r < 1 := by
      dsimp [r]
      linarith
    let y : Fin k -> Real := fun i => x i / r
    have hybox :
        y ∈ osiiClosedArgumentBox
          (osiiRecursiveAngleAperture k N) := by
      intro i
      have hratio_le : ratio i <= M :=
        Finset.le_sup' ratio (Finset.mem_univ i)
      have hx_le :
          |x i| <= r * osiiRecursiveAngleAperture k N i := by
        have hMr : M <= r := by
          dsimp [r]
          linarith
        have hdiv :
            |x i| / osiiRecursiveAngleAperture k N i <= r :=
          hratio_le.trans hMr
        exact (div_le_iff₀ (haperture i)).mp hdiv
      rw [show |y i| = |x i| / r by
        simp [y, abs_div, abs_of_pos hr_pos]]
      exact (div_le_iff₀ hr_pos).2 <| by
        simpa [mul_comm] using hx_le
    have hyclosed :
        OSIIGeneratedLogarithmicArgument .scalar k N y :=
      osiiGeneratedLogarithmicArgumentDomainSystem.recursiveAngle_box_subset
        N k hybox
    have hstrict :=
      OSIIStrictGeneratedLogarithmicArgument.smul_toStrict
        hyclosed r hr_pos.le hr_lt_one
    have hscale : r • y = x := by
      funext i
      change r * (x i / r) = x i
      field_simp [hr_pos.ne']
    simpa [hscale] using hstrict

/-- Every recursive-angle physical sector lies in the time-argument carrier
of the corresponding strict generated scalar base. -/
theorem strict_recursiveAngle_sector_subset_argumentCarrier
    (k N : Nat) :
    osiiTimeArgumentSector (osiiRecursiveAngleAperture k N) <=
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBase k N) := by
  intro z hz
  refine ⟨hz.1, strict_recursiveAngle_box_subset k N ?_⟩
  intro i
  simpa [osiiTimeArgumentVector] using hz.2 i

end OSIIChapterV
end OSReconstruction
