/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import OSReconstruction.SCV.GaussianSolidShift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedClosureRank

















noncomputable section

open Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace OSIIStrictGeneratedLogarithmicArgumentAtRank

private theorem argumentGeneratorPoint_smul_ranked
    {k : Nat} (i : GeneratorIndex k)
    (r : Real)
    (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real) :
    osiiArgumentGeneratorPoint i
        (r • left) (r * theta) (r • right) =
      r • osiiArgumentGeneratorPoint i left theta right := by
  funext j
  simp only [osiiArgumentGeneratorPoint, Pi.smul_apply]
  split_ifs <;> simp

private theorem argumentDiagonal_smul_ranked
    {n : Nat} (hn : 1 <= n)
    (r : Real) (x : Fin n -> Real) :
    osiiArgumentDiagonal hn (r • x) =
      r • osiiArgumentDiagonal hn x := by
  funext j
  simp only [osiiArgumentDiagonal, Pi.smul_apply]
  split_ifs <;> simp

/-- Multiplication by a scalar in `[0,1]` preserves an analytic-rank
stratum. -/
theorem smul_of_nonneg_le_one
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x)
    (r : Real) (hr0 : 0 <= r) (hr1 : r <= 1) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank kind n N (r • x) := by
  cases kind with
  | scalar =>
      apply scalar_hyperrectangle hx
      intro i
      change |r * x i| <= |x i|
      rw [abs_mul, abs_of_nonneg hr0]
      exact
        (mul_le_mul_of_nonneg_right hr1 (abs_nonneg (x i))
          ).trans_eq (one_mul _)
  | mixed =>
      apply mixedHyperrectangle hx
      intro i
      change |r * x i| <= |x i|
      rw [abs_mul, abs_of_nonneg hr0]
      exact
        (mul_le_mul_of_nonneg_right hr1 (abs_nonneg (x i))
          ).trans_eq (one_mul _)

private theorem exists_one_lt_mul_lt_ranked
    {a b : Real} (ha : 0 <= a) (hab : a < b) :
    ∃ q : Real, 1 < q ∧ q * a < b := by
  by_cases ha0 : a = 0
  · refine ⟨2, by norm_num, ?_⟩
    simpa [ha0] using hab
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let q : Real := (1 + b / a) / 2
    have hone : 1 < b / a := (one_lt_div ha_pos).2 hab
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      linarith
    · apply (lt_div_iff₀ ha_pos).1
      dsimp [q]
      linarith

private theorem rescale_ranked_expansion
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    {q Q : Real}
    (hQ :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N (Q • x))
    (hQ_pos : 0 < Q)
    (hq_nonneg : 0 <= q)
    (hqQ : q < Q) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank kind n N (q • x) := by
  have hratio_nonneg : 0 <= q / Q :=
    div_nonneg hq_nonneg hQ_pos.le
  have hratio_le : q / Q <= 1 :=
    (div_le_one hQ_pos).2 hqQ.le
  have hscaled :=
    smul_of_nonneg_le_one hQ (q / Q)
      hratio_nonneg hratio_le
  have hmul : q / Q * Q = q := by
    field_simp [hQ_pos.ne']
  simpa [smul_smul, hmul] using hscaled

/-- Every ranked strict-generated argument has a nontrivial radial
enlargement in the same analytic-rank stratum. -/
theorem exists_one_lt_smul
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    ∃ q : Real, 1 < q ∧
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N (q • x) := by
  induction hx with
  | scalarZero n N =>
      refine ⟨2, by norm_num, ?_⟩
      simpa using
        OSIIStrictGeneratedLogarithmicArgumentAtRank.scalarZero n N
  | initialMixedZero n =>
      refine ⟨2, by norm_num, ?_⟩
      simpa using
        OSIIStrictGeneratedLogarithmicArgumentAtRank.initialMixedZero n
  | weaken hx ih =>
      obtain ⟨q, hq, hqx⟩ := ih
      exact ⟨q, hq, weaken hqx⟩
  | @scalarConvex rank k N x y hx hy a b ha hb hab ihx ihy =>
      obtain ⟨qx, hqx, hxq⟩ := ihx
      obtain ⟨qy, hqy, hyq⟩ := ihy
      let Q : Real := min qx qy
      let q : Real := (1 + Q) / 2
      have hQ : 1 < Q := lt_min hqx hqy
      have hq : 1 < q := by
        dsimp [q]
        linarith
      have hqQ : q < Q := by
        dsimp [q]
        linarith
      have hq_nonneg : 0 <= q :=
        (by norm_num : (0 : Real) <= 1).trans hq.le
      have hxq' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar k N (q • x) :=
        rescale_ranked_expansion hxq
          (lt_trans (by norm_num) hqx)
          hq_nonneg
          (hqQ.trans_le (min_le_left qx qy))
      have hyq' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar k N (q • y) :=
        rescale_ranked_expansion hyq
          (lt_trans (by norm_num) hqy)
          hq_nonneg
          (hqQ.trans_le (min_le_right qx qy))
      refine ⟨q, hq, ?_⟩
      have hconv :=
        scalarConvex hxq' hyq' a b ha hb hab
      simpa [smul_add, smul_smul, mul_comm, mul_left_comm,
        mul_assoc] using hconv
  | @mixedHyperrectangle rank n N x hx y hy ih =>
      obtain ⟨q, hq, hxq⟩ := ih
      refine ⟨q, hq, ?_⟩
      apply mixedHyperrectangle hxq (q • y)
      intro i
      change |q * y i| <= |q * x i|
      have hq_nonneg : 0 <= q :=
        (by norm_num : (0 : Real) <= 1).trans hq.le
      rw [abs_mul, abs_mul, abs_of_nonneg hq_nonneg]
      exact mul_le_mul_of_nonneg_left (hy i) hq_nonneg
  | @generatorMemSucc rank k i N left theta right
      hleft hright htheta ihleft ihright =>
      obtain ⟨ql, hql, hleftq⟩ := ihleft
      obtain ⟨qr, hqr, hrightq⟩ := ihright
      obtain ⟨qt, hqt, hthetaq⟩ :=
        exists_one_lt_mul_lt_ranked (abs_nonneg theta) htheta
      let Q : Real := min ql (min qr qt)
      let q : Real := (1 + Q) / 2
      have hQ : 1 < Q := lt_min hql (lt_min hqr hqt)
      have hq : 1 < q := by
        dsimp [q]
        linarith
      have hqQ : q < Q := by
        dsimp [q]
        linarith
      have hq_nonneg : 0 <= q :=
        (by norm_num : (0 : Real) <= 1).trans hq.le
      have hleftq' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.n N (q • left) :=
        rescale_ranked_expansion hleftq
          (lt_trans (by norm_num) hql) hq_nonneg
          (hqQ.trans_le (min_le_left ql (min qr qt)))
      have hrightq' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.m N (q • right) :=
        rescale_ranked_expansion hrightq
          (lt_trans (by norm_num) hqr) hq_nonneg
          (hqQ.trans_le
            ((min_le_right ql (min qr qt)).trans
              (min_le_left qr qt)))
      have hthetaq' : |q * theta| < Real.pi / 2 := by
        have hq_qt :
            q < qt :=
          hqQ.trans_le
            ((min_le_right ql (min qr qt)).trans
              (min_le_right qr qt))
        rw [abs_mul, abs_of_nonneg hq_nonneg]
        exact
          (mul_le_mul_of_nonneg_right hq_qt.le
            (abs_nonneg theta)).trans_lt hthetaq
      refine ⟨q, hq, ?_⟩
      have hgenerator :=
        generatorMemSucc
          i N (q • left) (q * theta) (q • right)
          hleftq' hrightq' hthetaq'
      simpa [argumentGeneratorPoint_smul_ranked] using hgenerator
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      obtain ⟨q, hq, hdiagq⟩ := ih
      refine ⟨q, hq, ?_⟩
      apply mixedOfDiagonal n hn N (q • x)
      · simp [Pi.smul_apply, hx0]
      · simpa [argumentDiagonal_smul_ranked] using hdiagq
  | mixedTailMemScalar k N x hx ih =>
      obtain ⟨q, hq, hxq⟩ := ih
      refine ⟨q, hq, ?_⟩
      have htail :=
        mixedTailMemScalar k N (q • x) hxq
      exact htail

/-- Equivalently, every ranked point is a strict radial contraction of
another point in the same rank stratum. -/
theorem exists_radial_expansion
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    ∃ r : Real, 0 < r ∧ r < 1 ∧
      ∃ y : Fin n -> Real,
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank kind n N y ∧
        x = r • y := by
  obtain ⟨q, hq, hqx⟩ := hx.exists_one_lt_smul
  have hq_pos : 0 < q := lt_trans (by norm_num) hq
  refine
    ⟨q⁻¹, inv_pos.mpr hq_pos,
      inv_lt_one_of_one_lt₀ hq,
      q • x, hqx, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hq_pos.ne', one_smul]

/-- The zero mixed argument is present at every positive arity, depth, and
analytic rank. -/
theorem mixed_zero_mem
    (rank n N : Nat)
    (hn : 1 <= n) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed n N (0 : Fin n -> Real) := by
  apply mixedOfDiagonal n hn N (0 : Fin n -> Real)
  · rfl
  · have hdiag :
        osiiArgumentDiagonal hn (0 : Fin n -> Real) =
          (0 : Fin (2 * n - 1) -> Real) := by
      funext j
      simp [osiiArgumentDiagonal]
    rw [hdiag]
    exact scalar_zero_mem rank (2 * n - 1) N

end OSIIStrictGeneratedLogarithmicArgumentAtRank

/-- The non-convex scalar input for the passage from rank `rank` to rank
`rank + 1`. -/
inductive OSIIStrictGeneratedScalarRankSuccessorSeed
    (rank : Nat) :
    (k N : Nat) -> (Fin k -> Real) -> Prop where
  | old
      {k N : Nat} {x : Fin k -> Real}
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .scalar k N x) :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N x
  | generatorMemSucc
      {k : Nat} (i : GeneratorIndex k) (N : Nat)
      (left : Fin i.n -> Real) (theta : Real)
      (right : Fin i.m -> Real)
      (hleft :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed i.n N left)
      (hright :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed i.m N right)
      (htheta : |theta| < Real.pi / 2) :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k (N + 1)
        (osiiArgumentGeneratorPoint i left theta right)
  | mixedTailMemScalar
      (k N : Nat) (x : Fin (k + 1) -> Real)
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed (k + 1) N x) :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N (Fin.tail x)

/-- The rank-successor scalar seed base at one arity and depth. -/
def osiiStrictGeneratedScalarRankSuccessorSeedBase
    (k N rank : Nat) :
    Set (Fin k -> Real) :=
  {x |
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank k N x}

namespace OSIIStrictGeneratedScalarRankSuccessorSeed

/-- Every successor seed belongs to the next scalar analytic-rank
stratum. -/
theorem toRankSucc
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      (rank + 1) .scalar k N x := by
  cases hx with
  | old hx =>
      exact
        OSIIStrictGeneratedLogarithmicArgumentAtRank.weaken hx
  | generatorMemSucc i N left theta right
      hleft hright htheta =>
      exact
        OSIIStrictGeneratedLogarithmicArgumentAtRank.generatorMemSucc
          i N left theta right hleft hright htheta
  | mixedTailMemScalar N x hx =>
      exact
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedTailMemScalar
          k N x hx

/-- Coordinatewise shrinking preserves the rank-successor seed family. -/
theorem coordinatewiseShrink
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N x)
    (y : Fin k -> Real)
    (hy : forall i, |y i| <= |x i|) :
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank k N y := by
  cases hx with
  | old hx =>
      exact
        old
          (OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
            hx y hy)
  | generatorMemSucc i N left theta right
      hleft hright htheta =>
      let left' : Fin i.n -> Real :=
        osiiMixedArgumentOfTail i.hn
          (fun a => -y (i.leftGlobalIndex a))
      let right' : Fin i.m -> Real :=
        osiiMixedArgumentOfTail i.hm
          (fun b => y (i.rightGlobalIndex b))
      have hleft' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.n N left' := by
        apply
          OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
            hleft left'
        apply abs_osiiMixedArgumentOfTail_le i.hn
          (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
            i.hn hleft)
        intro a
        simpa [left'] using hy (i.leftGlobalIndex a)
      have hright' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.m N right' := by
        apply
          OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
            hright right'
        apply abs_osiiMixedArgumentOfTail_le i.hm
          (OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
            i.hm hright)
        intro b
        simpa [right'] using hy (i.rightGlobalIndex b)
      have htheta' : |y i.bridgeGlobalIndex| < Real.pi / 2 := by
        have hbridge :
            |y i.bridgeGlobalIndex| <= |theta| := by
          simpa using hy i.bridgeGlobalIndex
        exact hbridge.trans_lt htheta
      have hseed :=
        generatorMemSucc
          i N left' (y i.bridgeGlobalIndex) right'
          hleft' hright' htheta'
      simpa [left', right',
        osiiArgumentGeneratorPoint_reconstruct] using hseed
  | mixedTailMemScalar N x hx =>
      let x' : Fin (k + 1) -> Real := Fin.cons 0 y
      have hx' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed (k + 1) N x' := by
        apply
          OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
            hx x'
        intro j
        refine Fin.cases ?_ (fun a => ?_) j
        · have hk1 : 1 <= k + 1 := by omega
          have hx0 :=
            OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
              hk1 hx
          simpa [x'] using congrArg abs hx0.symm
        · exact hy a
      have hseed :=
        mixedTailMemScalar k N x' hx'
      simpa [x'] using hseed

end OSIIStrictGeneratedScalarRankSuccessorSeed

private theorem
    rankedScalar_mem_convexHull_successorSeed_aux
    {currentRank : Nat}
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        currentRank kind n N x) :
    match kind with
    | .scalar =>
        forall rank,
          currentRank = rank + 1 ->
          x ∈
            convexHull Real
              (osiiStrictGeneratedScalarRankSuccessorSeedBase
                n N rank)
    | .mixed => True := by
  induction hx with
  | scalarZero n N =>
      intro rank hrank
      omega
  | initialMixedZero n =>
      trivial
  | @weaken currentRank kind n N x hx ih =>
      cases kind with
      | scalar =>
          intro rank hrank
          have hcurrent : currentRank = rank := by omega
          subst currentRank
          apply subset_convexHull Real
          exact
            OSIIStrictGeneratedScalarRankSuccessorSeed.old hx
      | mixed =>
          trivial
  | @scalarConvex currentRank k N x y hx hy
      a b ha hb hab ihx ihy =>
      intro rank hrank
      exact
        (convex_convexHull Real
          (osiiStrictGeneratedScalarRankSuccessorSeedBase
            k N rank))
          (ihx rank hrank) (ihy rank hrank)
          ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      trivial
  | @generatorMemSucc currentRank k i N left theta right
      hleft hright htheta ihleft ihright =>
      intro rank hrank
      have hcurrent : currentRank = rank := by omega
      subst currentRank
      apply subset_convexHull Real
      exact
        OSIIStrictGeneratedScalarRankSuccessorSeed.generatorMemSucc
          i N left theta right hleft hright htheta
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      trivial
  | @mixedTailMemScalar currentRank k N x hx ih =>
      intro rank hrank
      have hcurrent : currentRank = rank := by omega
      subst currentRank
      apply subset_convexHull Real
      exact
        OSIIStrictGeneratedScalarRankSuccessorSeed.mixedTailMemScalar
          k N x hx

/-- Every scalar point of rank `rank + 1` belongs to the convex hull of the
old rank stratum and the new generator/tail outputs. -/
theorem strictGeneratedAtRankSucc_mem_convexHull_successorSeed
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k N x) :
    x ∈
      convexHull Real
        (osiiStrictGeneratedScalarRankSuccessorSeedBase
          k N rank) :=
  rankedScalar_mem_convexHull_successorSeed_aux hx rank rfl

/-- Every scalar analytic-rank stratum is convex. -/
theorem convex_osiiStrictGeneratedLogarithmicBaseAtRank
    (k N rank : Nat) :
    Convex Real
      (osiiStrictGeneratedLogarithmicBaseAtRank
        k N rank) := by
  intro x hx y hy a b ha hb hab
  exact
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalarConvex
      hx hy a b ha hb hab

/-- Every scalar rank-`rank + 1` target is a positive finite combination of
rank-successor seeds whose coefficient sum is strictly below one. -/
theorem
    exists_rankSuccessorSeedCombination_sum_lt_one_card_le
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k N x) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι)
      (w : ι -> Real) (z : ι -> Fin k -> Real),
      Fintype.card ι <= k + 1 ∧
      (forall i, 0 <= w i) ∧
      (∑ i, w i) < 1 ∧
      (forall i,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank k N (z i)) ∧
      (∑ i, w i • z i) = x := by
  obtain ⟨r, hr_pos, hr_lt, y, hy, hxy⟩ :=
    hx.exists_radial_expansion
  have hy_hull :
      y ∈
        convexHull Real
          (osiiStrictGeneratedScalarRankSuccessorSeedBase
            k N rank) :=
    strictGeneratedAtRankSucc_mem_convexHull_successorSeed hy
  obtain ⟨ι, hι, z, v, hz, hz_affine, hv_pos, hv_sum, hvz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy_hull
  letI : Fintype ι := hι
  have hι_nonempty : Nonempty ι := by
    by_contra hι_empty
    letI : IsEmpty ι := ⟨fun i => hι_empty ⟨i⟩⟩
    have hzero_one : (0 : Real) = 1 := by
      simpa using hv_sum
    norm_num at hzero_one
  letI : Nonempty ι := hι_nonempty
  have hcard : Fintype.card ι <= k + 1 := by
    calc
      Fintype.card ι <=
          Module.finrank Real
              (vectorSpan Real (Set.range z)) + 1 :=
        hz_affine.card_le_finrank_succ
      _ <= Module.finrank Real (Fin k -> Real) + 1 :=
        Nat.add_le_add_right
          (Submodule.finrank_le
            (vectorSpan Real (Set.range z))) 1
      _ = k + 1 := by simp
  let w : ι -> Real := fun i => r * v i
  refine
    ⟨ι, inferInstance, inferInstance, w, z,
      hcard, ?_, ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg hr_pos.le (hv_pos i).le
  · calc
      (∑ i, w i) = r * ∑ i, v i := by
        simp [w, Finset.mul_sum]
      _ = r := by rw [hv_sum, mul_one]
      _ < 1 := hr_lt
  · intro i
    exact hz ⟨i, rfl⟩
  · calc
      (∑ i, w i • z i) =
          r • ∑ i, v i • z i := by
            simp [w, Finset.smul_sum, smul_smul]
      _ = r • y := by rw [hvz]
      _ = x := hxy.symm

/-- Canonical finite-coordinate form of the rank-successor seed
decomposition. -/
theorem exists_rankSuccessorSeedCombination_fin
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k N x) :
    ∃ n : Nat, 0 < n ∧ n <= k + 1 ∧
      ∃ (w : Fin n -> Real) (z : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) < 1 ∧
        (forall i,
          OSIIStrictGeneratedScalarRankSuccessorSeed
            rank k N (z i)) ∧
        (∑ i, w i • z i) = x := by
  obtain ⟨ι, hι, hι_nonempty, w, z, hcard,
      hw_nonneg, hw_sum, hz, hwz⟩ :=
    exists_rankSuccessorSeedCombination_sum_lt_one_card_le hx
  letI : Fintype ι := hι
  letI : Nonempty ι := hι_nonempty
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let wFin : Fin n -> Real := fun j => w (e.symm j)
  let zFin : Fin n -> Fin k -> Real := fun j => z (e.symm j)
  have hn_pos : 0 < n :=
    Fintype.card_pos_iff.mpr hι_nonempty
  have hwFin_sum :
      (∑ j, wFin j) = ∑ i, w i := by
    simpa [wFin] using e.symm.sum_comp w
  have hwzFin :
      (∑ j, wFin j • zFin j) =
        ∑ i, w i • z i := by
    simpa [wFin, zFin] using
      e.symm.sum_comp (fun i => w i • z i)
  refine
    ⟨n, hn_pos, hcard, wFin, zFin,
      ?_, ?_, ?_, ?_⟩
  · intro j
    exact hw_nonneg (e.symm j)
  · rw [hwFin_sum]
    exact hw_sum
  · intro j
    exact hz (e.symm j)
  · rw [hwzFin]
    exact hwz

end OSIIChapterV
end OSReconstruction
