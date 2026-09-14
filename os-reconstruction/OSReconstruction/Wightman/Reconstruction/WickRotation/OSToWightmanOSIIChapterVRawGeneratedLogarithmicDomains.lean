/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedLogarithmicDomains

















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The strict generated recurrence before vacuum-tail readout.

`scalarZero` records the retained positive-real germ at every stage.  The
only depth-raising constructor is the non-vacuum generator; in particular
there is no analogue of `mixedTailMemScalar` here. -/
inductive OSIIRawStrictGeneratedLogarithmicArgument :
    OSIILogarithmicArgumentKind ->
      (n N : Nat) -> (Fin n -> Real) -> Prop where
  | scalarZero (k N : Nat) :
      OSIIRawStrictGeneratedLogarithmicArgument
        .scalar k N (0 : Fin k -> Real)
  | initialMixedZero (n : Nat) :
      OSIIRawStrictGeneratedLogarithmicArgument
        .mixed n 0 (0 : Fin n -> Real)
  | scalarConvex
      {k N : Nat} {x y : Fin k -> Real}
      (hx : OSIIRawStrictGeneratedLogarithmicArgument .scalar k N x)
      (hy : OSIIRawStrictGeneratedLogarithmicArgument .scalar k N y)
      (a b : Real) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
      OSIIRawStrictGeneratedLogarithmicArgument
        .scalar k N (a • x + b • y)
  | mixedHyperrectangle
      {n N : Nat} {x : Fin n -> Real}
      (hx : OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x)
      (y : Fin n -> Real)
      (hy : forall i, |y i| <= |x i|) :
      OSIIRawStrictGeneratedLogarithmicArgument .mixed n N y
  | generatorMemSucc
      {k : Nat} (i : GeneratorIndex k) (N : Nat)
      (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real)
      (hleft :
        OSIIRawStrictGeneratedLogarithmicArgument .mixed i.n N left)
      (hright :
        OSIIRawStrictGeneratedLogarithmicArgument .mixed i.m N right)
      (htheta : |theta| < Real.pi / 2) :
      OSIIRawStrictGeneratedLogarithmicArgument .scalar k (N + 1)
        (osiiArgumentGeneratorPoint i left theta right)
  | mixedOfDiagonal
      (n : Nat) (hn : 1 <= n) (N : Nat) (x : Fin n -> Real)
      (hx0 : x ⟨0, hn⟩ = 0)
      (hx :
        OSIIRawStrictGeneratedLogarithmicArgument .scalar (2 * n - 1) N
          (osiiArgumentDiagonal hn x)) :
      OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x

/-- The raw strict scalar base `C_k^(N)`. -/
def osiiRawStrictGeneratedLogarithmicBase (k N : Nat) :
    Set (Fin k -> Real) :=
  {x | OSIIRawStrictGeneratedLogarithmicArgument .scalar k N x}

/-- The raw strict mixed base `D_n^(N)` in logarithmic coordinates. -/
def osiiRawStrictGeneratedMixedLogarithmicBase (n N : Nat) :
    Set (Fin n -> Real) :=
  {x | OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x}

namespace OSIIRawStrictGeneratedLogarithmicArgument

/-- Reindex a raw argument along an equality of finite arities. -/
theorem reindex
    {kind : OSIILogarithmicArgumentKind}
    {n m N : Nat} (h : n = m)
    {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    OSIIRawStrictGeneratedLogarithmicArgument kind m N
      (fun j : Fin m => x ((finCongr h).symm j)) := by
  subst m
  simpa

/-- The raw recurrence embeds into the legacy strict
carrier.  The only nontrivial case is the retained real germ, supplied by the
legacy carrier's proved zero membership. -/
theorem toStrictGenerated
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    OSIIStrictGeneratedLogarithmicArgument kind n N x := by
  induction hx with
  | scalarZero k N =>
      exact OSIIStrictGeneratedLogarithmicArgument.scalar_zero_mem k N
  | initialMixedZero n =>
      exact OSIIStrictGeneratedLogarithmicArgument.initialMixedZero n
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.scalarConvex
          ihx ihy a b ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.mixedHyperrectangle ih y hy
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.generatorMemSucc
          i N left theta right ihleft ihright htheta
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.mixedOfDiagonal
          n hn N x hx0 ih

private theorem mixed_head_eq_zero_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar => True
    | .mixed => forall hn : 1 <= n, x ⟨0, hn⟩ = 0 := by
  induction hx with
  | scalarZero k N =>
      trivial
  | initialMixedZero n =>
      intro hn
      rfl
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      trivial
  | mixedHyperrectangle hx y hy ih =>
      intro hn
      have hbound := hy ⟨0, hn⟩
      rw [ih hn, abs_zero] at hbound
      exact abs_eq_zero.mp
        (le_antisymm hbound (abs_nonneg _))
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      trivial
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro _
      exact hx0

/-- Every raw mixed argument keeps the distinguished zero head coordinate.
This is the source-side condition needed to form its reflected scalar
diagonal without adding a vacuum-tail constructor to the raw recurrence. -/
theorem mixed_head_eq_zero
    {n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x) :
    x ⟨0, hn⟩ = 0 :=
  mixed_head_eq_zero_aux hx hn

private theorem depth_succ_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar =>
        OSIIRawStrictGeneratedLogarithmicArgument .scalar n (N + 1) x
    | .mixed =>
        1 <= n ->
          OSIIRawStrictGeneratedLogarithmicArgument .mixed n (N + 1) x := by
  induction hx with
  | scalarZero k N =>
      exact OSIIRawStrictGeneratedLogarithmicArgument.scalarZero k (N + 1)
  | initialMixedZero n =>
      intro hn
      apply OSIIRawStrictGeneratedLogarithmicArgument.mixedOfDiagonal
        n hn 1 (0 : Fin n -> Real)
      · rfl
      · have hdiag :
            osiiArgumentDiagonal hn (0 : Fin n -> Real) =
              (0 : Fin (2 * n - 1) -> Real) := by
          funext j
          simp [osiiArgumentDiagonal]
        rw [hdiag]
        exact OSIIRawStrictGeneratedLogarithmicArgument.scalarZero
          (2 * n - 1) 1
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      exact OSIIRawStrictGeneratedLogarithmicArgument.scalarConvex
        ihx ihy a b ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      intro hn
      exact OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
        (ih hn) y hy
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      exact OSIIRawStrictGeneratedLogarithmicArgument.generatorMemSucc
        i (N + 1) left theta right
        (ihleft i.hn) (ihright i.hm) htheta
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro _hn
      exact OSIIRawStrictGeneratedLogarithmicArgument.mixedOfDiagonal
        n hn (N + 1) x hx0 ih

/-- Positive-arity raw mixed arguments persist at the next outer depth.

The arity condition is genuine: the raw recurrence deliberately has no
depth-positive empty mixed source.  Every reflected lower source used by
equation (6.29') has positive mixed arity. -/
theorem mixed_depth_succ
    {n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x) :
    OSIIRawStrictGeneratedLogarithmicArgument .mixed n (N + 1) x :=
  depth_succ_aux hx hn

/-- The zero mixed source persists at every outer depth.

This is the raw one-particle endpoint used by rooted generator splits; it
comes from the initial mixed zero and ordinary positive-arity depth
monotonicity, not from a vacuum-tail scalar constructor. -/
theorem mixed_zero
    (n N : Nat) (hn : 1 <= n) :
    OSIIRawStrictGeneratedLogarithmicArgument
      .mixed n N (0 : Fin n -> Real) := by
  induction N with
  | zero =>
      exact initialMixedZero n
  | succ N ih =>
      exact ih.mixed_depth_succ hn

private theorem coordinatewise_closed_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar =>
        forall y : Fin n -> Real,
          (forall i, |y i| <= |x i|) ->
          OSIIRawStrictGeneratedLogarithmicArgument .scalar n N y
    | .mixed => True := by
  induction hx with
  | scalarZero k N =>
      intro y hy
      have hy0 : y = 0 := by
        funext i
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa using hy i
        · exact abs_nonneg _
      subst y
      exact scalarZero k N
  | initialMixedZero n =>
      trivial
  | @scalarConvex k N x y hx hy a b ha hb hab ihx ihy =>
      intro z hz
      let c : Fin k -> Real := fun i => a * x i + b * y i
      let ratio : Fin k -> Real :=
        fun i => if c i = 0 then 0 else z i / c i
      have hz_c : forall i, |z i| <= |c i| := by
        intro i
        simpa [c] using hz i
      have hratio : forall i, |ratio i| <= 1 := by
        intro i
        by_cases hci : c i = 0
        · simp [ratio, hci]
        · have hcpos : 0 < |c i| := abs_pos.mpr hci
          simp only [ratio, hci, ↓reduceIte, abs_div]
          exact (div_le_one hcpos).2 (hz_c i)
      have hx' :
          OSIIRawStrictGeneratedLogarithmicArgument .scalar k N
            (fun i => ratio i * x i) := by
        apply ihx
        intro i
        rw [abs_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hratio i) (abs_nonneg (x i))).trans_eq (one_mul _)
      have hy' :
          OSIIRawStrictGeneratedLogarithmicArgument .scalar k N
            (fun i => ratio i * y i) := by
        apply ihy
        intro i
        rw [abs_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hratio i) (abs_nonneg (y i))).trans_eq (one_mul _)
      have hratio_c : forall i, ratio i * c i = z i := by
        intro i
        by_cases hci : c i = 0
        · have hzi_abs : |z i| = 0 :=
            le_antisymm (by simpa [hci] using hz_c i) (abs_nonneg _)
          have hzi : z i = 0 := abs_eq_zero.mp hzi_abs
          simp [ratio, hci, hzi]
        · simp [ratio, hci]
      have hcomb :=
        OSIIRawStrictGeneratedLogarithmicArgument.scalarConvex
          hx' hy' a b ha hb hab
      have hcomb_eq :
          a • (fun i => ratio i * x i) +
              b • (fun i => ratio i * y i) =
            z := by
        funext i
        change
          a * (ratio i * x i) + b * (ratio i * y i) = z i
        calc
          a * (ratio i * x i) + b * (ratio i * y i) =
              ratio i * c i := by
                simp only [c]
                ring
          _ = z i := hratio_c i
      rw [hcomb_eq] at hcomb
      exact hcomb
  | mixedHyperrectangle hx y hy ih =>
      trivial
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      intro y hy
      let left' : Fin i.n -> Real :=
        osiiMixedArgumentOfTail i.hn
          (fun a => -y (i.leftGlobalIndex a))
      let right' : Fin i.m -> Real :=
        osiiMixedArgumentOfTail i.hm
          (fun b => y (i.rightGlobalIndex b))
      have hleft' :
          OSIIRawStrictGeneratedLogarithmicArgument .mixed i.n N left' := by
        apply OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
          hleft left'
        apply abs_osiiMixedArgumentOfTail_le i.hn
          (mixed_head_eq_zero i.hn hleft)
        intro a
        simpa [left'] using hy (i.leftGlobalIndex a)
      have hright' :
          OSIIRawStrictGeneratedLogarithmicArgument .mixed i.m N right' := by
        apply OSIIRawStrictGeneratedLogarithmicArgument.mixedHyperrectangle
          hright right'
        apply abs_osiiMixedArgumentOfTail_le i.hm
          (mixed_head_eq_zero i.hm hright)
        intro b
        simpa [right'] using hy (i.rightGlobalIndex b)
      have htheta' : |y i.bridgeGlobalIndex| < Real.pi / 2 := by
        have hbridge :
            |y i.bridgeGlobalIndex| <= |theta| := by
          simpa using hy i.bridgeGlobalIndex
        exact hbridge.trans_lt htheta
      have hgen :=
        OSIIRawStrictGeneratedLogarithmicArgument.generatorMemSucc
          i N left' (y i.bridgeGlobalIndex) right'
          hleft' hright' htheta'
      simpa [left', right',
        osiiArgumentGeneratorPoint_reconstruct] using hgen
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      trivial

/-- Raw scalar carriers are solid under coordinatewise shrinking of principal
arguments. This is proved from the non-vacuum generator grammar itself; no
same-stage vacuum readout is used. -/
theorem scalar_hyperrectangle
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument .scalar n N x)
    (y : Fin n -> Real)
    (hy : forall i, |y i| <= |x i|) :
    OSIIRawStrictGeneratedLogarithmicArgument .scalar n N y :=
  coordinatewise_closed_aux hx y hy

private theorem mixed_diagonal_mem_scalar_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar => True
    | .mixed =>
        forall hn : 1 <= n,
          OSIIRawStrictGeneratedLogarithmicArgument .scalar
            (2 * n - 1) N (osiiArgumentDiagonal hn x) := by
  induction hx with
  | scalarZero k N =>
      trivial
  | initialMixedZero n =>
      intro hn
      have hdiag :
          osiiArgumentDiagonal hn (0 : Fin n -> Real) =
            (0 : Fin (2 * n - 1) -> Real) := by
        funext j
        simp [osiiArgumentDiagonal]
      rw [hdiag]
      exact scalarZero (2 * n - 1) 0
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      trivial
  | @mixedHyperrectangle n N x hx y hy ih =>
      intro hn
      apply scalar_hyperrectangle (ih hn) (osiiArgumentDiagonal hn y)
      intro j
      by_cases hj : j.val < n - 1
      · simpa [osiiArgumentDiagonal, hj] using
          hy ⟨n - 1 - j.val, by omega⟩
      · simpa [osiiArgumentDiagonal, hj] using
          hy ⟨j.val - (n - 1), by omega⟩
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      trivial
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro hn'
      simpa using hx

/-- The reflected scalar diagonal of every raw mixed argument belongs to the
raw scalar carrier at the same outer depth. This is the exact lower-source
entry point for equation (6.29'). -/
theorem mixed_diagonal_mem_scalar
    {n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument .mixed n N x) :
    OSIIRawStrictGeneratedLogarithmicArgument .scalar
      (2 * n - 1) N (osiiArgumentDiagonal hn x) :=
  mixed_diagonal_mem_scalar_aux hx hn

end OSIIRawStrictGeneratedLogarithmicArgument

/-- Raw scalar stages are contained in the legacy strict scalar stages. -/
theorem rawStrictGeneratedScalarBase_subset_strictGenerated
    (k N : Nat) :
    osiiRawStrictGeneratedLogarithmicBase k N <=
      osiiStrictGeneratedLogarithmicBase k N := by
  intro x hx
  exact hx.toStrictGenerated

end OSIIChapterV
end OSReconstruction
