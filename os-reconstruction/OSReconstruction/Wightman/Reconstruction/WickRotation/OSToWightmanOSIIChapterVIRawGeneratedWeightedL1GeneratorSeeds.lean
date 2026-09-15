import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedWeightedL1CenteredProvenance

/-!
# Raw weighted-L1 generator seeds

The raw outer-depth recurrence is smaller than the full analytic-rank
successor atlas: at depth N + 1 its genuinely new scalar points are convex
combinations of non-vacuum generator insertions whose two lower mixed blocks
already lie at raw depth N.  This module records that source-faithful seed
carrier and lifts finite raw decompositions to one common analytic rank
without forgetting raw lower-block provenance.
-/

noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One unranked raw generator seed at a fixed predecessor depth. -/
structure RawGeneratorSeedData
    (k depth : Nat)
    (x : Fin k -> Real) where
  generator : GeneratorIndex k
  left : Fin generator.n -> Real
  left_raw : OSIIRawStrictGeneratedLogarithmicArgument
    .mixed generator.n depth left
  theta : Real
  theta_bound : |theta| < Real.pi / 2
  right : Fin generator.m -> Real
  right_raw : OSIIRawStrictGeneratedLogarithmicArgument
    .mixed generator.m depth right
  point_eq : osiiArgumentGeneratorPoint generator left theta right = x

namespace RawGeneratorSeedData

/-- A raw generator seed admits one common finite analytic rank for its two
lower blocks. -/
theorem exists_ranked
    {k depth : Nat} {x : Fin k -> Real}
    (H : RawGeneratorSeedData k depth x) :
    ∃ rank,
      Nonempty (RawGeneratorRankSuccessorSeedData rank k depth x) := by
  obtain ⟨leftRank, hleftRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank
      H.left_raw.toStrictGenerated
  obtain ⟨rightRank, hrightRank⟩ :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank
      H.right_raw.toStrictGenerated
  let rank := max leftRank rightRank
  refine ⟨rank, ⟨{
    generator := H.generator
    left := H.left
    left_rank := hleftRank.mono (Nat.le_max_left _ _)
    left_raw := H.left_raw
    theta := H.theta
    theta_bound := H.theta_bound
    right := H.right
    right_rank := hrightRank.mono (Nat.le_max_right _ _)
    right_raw := H.right_raw
    point_eq := H.point_eq }⟩⟩

/-- Zero is itself a raw generator seed at every positive arity. -/
def zero
    (k depth : Nat)
    (hk : 1 <= k) :
    RawGeneratorSeedData k depth (0 : Fin k -> Real) := by
  let i : GeneratorIndex k := ⟨1, k, by omega, hk, by omega⟩
  exact {
    generator := i
    left := 0
    left_raw :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        1 depth (by omega)
    theta := 0
    theta_bound := by
      simpa using
        (div_pos Real.pi_pos (by norm_num : (0 : Real) < 2))
    right := 0
    right_raw :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        k depth hk
    point_eq := by
      funext j
      simp [i, osiiArgumentGeneratorPoint] }

/-- The canonical bridge-coordinate basis vector is a raw generator seed at
every predecessor depth. -/
def bridgeCoordinate
    (k depth : Nat)
    (a : Fin k) :
    RawGeneratorSeedData k depth (Pi.single a 1) := by
  let i : GeneratorIndex k := GeneratorIndex.ofGap a
  exact {
    generator := i
    left := 0
    left_raw :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        i.n depth i.hn
    theta := 1
    theta_bound := by
      have hpi : (3 : Real) < Real.pi := Real.pi_gt_three
      norm_num
      linarith
    right := 0
    right_raw :=
      OSIIRawStrictGeneratedLogarithmicArgument.mixed_zero
        i.m depth i.hm
    point_eq := by
      funext j
      simp only [osiiArgumentGeneratorPoint]
      split_ifs with hleft hbridge
      · simp [Pi.single_apply]
        intro hja
        have hjlt : j.val < a.val := by
          simpa only [i, GeneratorIndex.ofGap, Nat.add_sub_cancel] using hleft
        omega
      · have hja : j = a := by
          apply Fin.ext
          simpa only [i, GeneratorIndex.ofGap, Nat.add_sub_cancel] using hbridge
        subst j
        simp
      · have hja : j ≠ a := by
          intro h
          subst j
          apply hbridge
          simp [i]
        simp [hja] }

end RawGeneratorSeedData

/-- The raw bridge-coordinate seed family spans the complete coefficient
space. -/
theorem rawBridgeGeneratorCoefficientMap_surjective
    (k : Nat) :
    Function.Surjective
      (osiiStrictScalarSeedCoefficientMap
        (fun a : Fin k => Pi.single a 1)) := by
  intro r
  refine ⟨r, ?_⟩
  funext j
  simp only [osiiStrictScalarSeedCoefficientMap, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    simp [Ne.symm hbj]
  · simp

namespace RawGeneratorRankSuccessorSeedData

/-- Increasing the retained analytic rank preserves a dual-provenance raw
generator seed. -/
def mono
    {rank rank' k depth : Nat}
    {x : Fin k -> Real}
    (H : RawGeneratorRankSuccessorSeedData rank k depth x)
    (hrank : rank <= rank') :
    RawGeneratorRankSuccessorSeedData rank' k depth x where
  generator := H.generator
  left := H.left
  left_rank := H.left_rank.mono hrank
  left_raw := H.left_raw
  theta := H.theta
  theta_bound := H.theta_bound
  right := H.right
  right_rank := H.right_rank.mono hrank
  right_raw := H.right_raw
  point_eq := H.point_eq

end RawGeneratorRankSuccessorSeedData

/-- The raw generator seed carrier at one predecessor depth. -/
def osiiRawGeneratorSeedBase
    (k depth : Nat) :
    Set (Fin k -> Real) :=
  {x | Nonempty (RawGeneratorSeedData k depth x)}

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

namespace OSIIRawStrictGeneratedLogarithmicArgument

/-- Multiplication by a scalar in the closed unit interval preserves either
raw argument kind. -/
theorem smul_of_nonneg_le_one
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x)
    (r : Real) (hr0 : 0 <= r) (hr1 : r <= 1) :
    OSIIRawStrictGeneratedLogarithmicArgument kind n N (r • x) := by
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
      apply mixedHyperrectangle hx (r • x)
      intro i
      change |r * x i| <= |x i|
      rw [abs_mul, abs_of_nonneg hr0]
      exact
        (mul_le_mul_of_nonneg_right hr1 (abs_nonneg (x i))
          ).trans_eq (one_mul _)

private theorem rescale_expansion
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    {q Q : Real}
    (hQ : OSIIRawStrictGeneratedLogarithmicArgument kind n N (Q • x))
    (hQ_pos : 0 < Q)
    (hq_nonneg : 0 <= q)
    (hqQ : q < Q) :
    OSIIRawStrictGeneratedLogarithmicArgument kind n N (q • x) := by
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

private theorem exists_one_lt_mul_lt
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

/-- Every raw argument has a nontrivial radial enlargement in the same
outer-depth grammar. -/
theorem exists_one_lt_smul
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    ∃ q : Real, 1 < q ∧
      OSIIRawStrictGeneratedLogarithmicArgument kind n N (q • x) := by
  induction hx with
  | scalarZero n N =>
      refine ⟨2, by norm_num, ?_⟩
      simpa using
        OSIIRawStrictGeneratedLogarithmicArgument.scalarZero n N
  | initialMixedZero n =>
      refine ⟨2, by norm_num, ?_⟩
      simpa using
        OSIIRawStrictGeneratedLogarithmicArgument.initialMixedZero n
  | @scalarConvex k N x y hx hy a b ha hb hab ihx ihy =>
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
          OSIIRawStrictGeneratedLogarithmicArgument
            .scalar k N (q • x) :=
        rescale_expansion hxq
          (lt_trans (by norm_num) hqx)
          hq_nonneg
          (hqQ.trans_le (min_le_left qx qy))
      have hyq' :
          OSIIRawStrictGeneratedLogarithmicArgument
            .scalar k N (q • y) :=
        rescale_expansion hyq
          (lt_trans (by norm_num) hqy)
          hq_nonneg
          (hqQ.trans_le (min_le_right qx qy))
      refine ⟨q, hq, ?_⟩
      have hconv :=
        scalarConvex hxq' hyq' a b ha hb hab
      simpa [smul_add, smul_smul, mul_comm, mul_left_comm,
        mul_assoc] using hconv
  | @mixedHyperrectangle n N x hx y hy ih =>
      obtain ⟨q, hq, hxq⟩ := ih
      refine ⟨q, hq, ?_⟩
      apply mixedHyperrectangle hxq (q • y)
      intro i
      change |q * y i| <= |q * x i|
      have hq_nonneg : 0 <= q :=
        (by norm_num : (0 : Real) <= 1).trans hq.le
      rw [abs_mul, abs_mul, abs_of_nonneg hq_nonneg]
      exact mul_le_mul_of_nonneg_left (hy i) hq_nonneg
  | @generatorMemSucc k i N left theta right
      hleft hright htheta ihleft ihright =>
      obtain ⟨ql, hql, hleftq⟩ := ihleft
      obtain ⟨qr, hqr, hrightq⟩ := ihright
      obtain ⟨qt, hqt, hthetaq⟩ :=
        exists_one_lt_mul_lt (abs_nonneg theta) htheta
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
          OSIIRawStrictGeneratedLogarithmicArgument
            .mixed i.n N (q • left) :=
        rescale_expansion hleftq
          (lt_trans (by norm_num) hql) hq_nonneg
          (hqQ.trans_le (min_le_left ql (min qr qt)))
      have hrightq' :
          OSIIRawStrictGeneratedLogarithmicArgument
            .mixed i.m N (q • right) :=
        rescale_expansion hrightq
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
      simpa [raw_argumentGeneratorPoint_smul] using hgenerator
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      obtain ⟨q, hq, hdiagq⟩ := ih
      refine ⟨q, hq, ?_⟩
      apply mixedOfDiagonal n hn N (q • x)
      · simp [Pi.smul_apply, hx0]
      · simpa [raw_argumentDiagonal_smul] using hdiagq

/-- Equivalently, every raw argument is a strict radial contraction of
another point in the same outer-depth grammar. -/
theorem exists_radial_expansion
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    ∃ r : Real, 0 < r ∧ r < 1 ∧
      ∃ y : Fin n -> Real,
        OSIIRawStrictGeneratedLogarithmicArgument kind n N y ∧
        x = r • y := by
  obtain ⟨q, hq, hqx⟩ := hx.exists_one_lt_smul
  have hq_pos : 0 < q := lt_trans (by norm_num) hq
  refine
    ⟨q⁻¹, inv_pos.mpr hq_pos,
      inv_lt_one_of_one_lt₀ hq,
      q • x, hqx, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hq_pos.ne', one_smul]

end OSIIRawStrictGeneratedLogarithmicArgument

private theorem rawScalar_mem_convexHull_generatorSeed_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar =>
        ∀ depth, N = depth + 1 -> 1 <= n ->
          x ∈ convexHull Real (osiiRawGeneratorSeedBase n depth)
    | .mixed => True := by
  induction hx with
  | scalarZero k N =>
      intro depth _hN hk
      apply subset_convexHull Real
      exact ⟨RawGeneratorSeedData.zero k depth hk⟩
  | initialMixedZero n =>
      trivial
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      intro depth hN hn
      exact
        (convex_convexHull Real (osiiRawGeneratorSeedBase _ _))
          (ihx depth hN hn) (ihy depth hN hn) ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      trivial
  | generatorMemSucc i N left theta right hleft hright htheta
      ihleft ihright =>
      intro depth hN _hk
      have hdepth : N = depth := by omega
      subst depth
      apply subset_convexHull Real
      exact ⟨{
        generator := i
        left := left
        left_raw := hleft
        theta := theta
        theta_bound := htheta
        right := right
        right_raw := hright
        point_eq := rfl }⟩
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      trivial

/-- Every positive-arity raw scalar point at the next outer depth lies in
the convex hull of raw generator seeds from the predecessor depth. -/
theorem rawScalar_succ_mem_convexHull_generatorSeedBase
    {k depth : Nat} {x : Fin k -> Real}
    (hk : 1 <= k)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar k (depth + 1) x) :
    x ∈ convexHull Real (osiiRawGeneratorSeedBase k depth) :=
  rawScalar_mem_convexHull_generatorSeed_aux hx depth rfl hk

/-- A raw next-depth scalar point has a finite convex decomposition through
raw predecessor-depth generator seeds. -/
theorem exists_rawGeneratorSeedCombination_fin
    {k depth : Nat} {x : Fin k -> Real}
    (hk : 1 <= k)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar k (depth + 1) x) :
    ∃ n : Nat, 0 < n ∧ n <= k + 1 ∧
      ∃ (w : Fin n -> Real) (seed : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) = 1 ∧
        (forall i,
          Nonempty (RawGeneratorSeedData k depth (seed i))) ∧
        (∑ i, w i • seed i) = x := by
  have hx_hull :=
    rawScalar_succ_mem_convexHull_generatorSeedBase hk hx
  obtain ⟨ι, hι, z, v, hz, hz_affine, hv_pos, hv_sum, hvz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_hull
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
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let wFin : Fin n -> Real := fun j => v (e.symm j)
  let seedFin : Fin n -> Fin k -> Real := fun j => z (e.symm j)
  have hn_pos : 0 < n :=
    Fintype.card_pos_iff.mpr hι_nonempty
  have hwFin_sum :
      (∑ j, wFin j) = ∑ i, v i := by
    simpa [wFin] using e.symm.sum_comp v
  have hwzFin :
      (∑ j, wFin j • seedFin j) =
        ∑ i, v i • z i := by
    simpa [wFin, seedFin] using
      e.symm.sum_comp (fun i => v i • z i)
  refine
    ⟨n, hn_pos, hcard, wFin, seedFin,
      ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hv_pos (e.symm j)).le
  · rw [hwFin_sum]
    exact hv_sum
  · intro j
    exact hz ⟨e.symm j, rfl⟩
  · rw [hwzFin]
    exact hvz

/-- The finite raw generator decomposition can be chosen with strict radial
slack in the coefficient sum. -/
theorem exists_rawGeneratorSeedCombination_sum_lt_one_fin
    {k depth : Nat} {x : Fin k -> Real}
    (hk : 1 <= k)
    (hx : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar k (depth + 1) x) :
    ∃ n : Nat, 0 < n ∧ n <= k + 1 ∧
      ∃ (w : Fin n -> Real) (seed : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) < 1 ∧
        (forall i,
          Nonempty (RawGeneratorSeedData k depth (seed i))) ∧
        (∑ i, w i • seed i) = x := by
  obtain ⟨r, hr_pos, hr_lt, y, hy, hxy⟩ :=
    hx.exists_radial_expansion
  obtain ⟨n, hn, hcard, v, seed, hv_nonneg, hv_sum, hseed, hvz⟩ :=
    exists_rawGeneratorSeedCombination_fin hk hy
  let w : Fin n -> Real := fun i => r * v i
  refine ⟨n, hn, hcard, w, seed, ?_, ?_, hseed, ?_⟩
  · intro i
    exact mul_nonneg hr_pos.le (hv_nonneg i)
  · calc
      (∑ i, w i) = r * ∑ i, v i := by
        simp [w, Finset.mul_sum]
      _ = r := by rw [hv_sum, mul_one]
      _ < 1 := hr_lt
  · calc
      (∑ i, w i • seed i) =
          r • ∑ i, v i • seed i := by
        simp [w, Finset.smul_sum, smul_smul]
      _ = r • y := by rw [hvz]
      _ = x := hxy.symm

/-- A raw generator decomposition can be padded by zero-weight bridge
coordinates to make its coefficient map surjective and section-regular. -/
theorem exists_sectionRegular_rawGeneratorSeedCombination_fin
    {k depth : Nat} [NeZero k]
    {x : Fin k -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar k (depth + 1) x) :
    ∃ n : Nat, 0 < n ∧
      ∃ (w : Fin n -> Real) (seed : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) < 1 ∧
        (forall i,
          Nonempty (RawGeneratorSeedData k depth (seed i))) ∧
        (∑ i, w i • seed i) = x ∧
        Function.Surjective
          (osiiStrictScalarSeedCoefficientMap seed) ∧
        (osiiStrictScalarSeedCoefficientTarget w = 0 ∨
          osiiStrictScalarSeedCoefficientMap seed
              (osiiStrictScalarSeedCoefficientTarget w) ≠ 0) := by
  obtain ⟨n, hn, _hcard, w0, seed0, hw0, hsum0, hseed0,
      hcombination0⟩ :=
    exists_rawGeneratorSeedCombination_sum_lt_one_fin
      (by
        have hkpos := NeZero.pos k
        omega) hx
  let bridge : Fin k -> Fin k -> Real := fun a => Pi.single a 1
  let seed : Fin (n + k) -> Fin k -> Real :=
    Fin.append seed0 bridge
  have hseed : forall i,
      Nonempty (RawGeneratorSeedData k depth (seed i)) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
        simpa [seed] using hseed0 i
    | right i =>
        simpa [seed, bridge] using
          ⟨RawGeneratorSeedData.bridgeCoordinate k depth i⟩
  have hsurjective : Function.Surjective
      (osiiStrictScalarSeedCoefficientMap seed) := by
    exact osiiStrictScalarSeedCoefficientMap_append_surjective
      seed0 bridge (rawBridgeGeneratorCoefficientMap_surjective k)
  by_cases hx0 : x = 0
  · let w : Fin (n + k) -> Real := 0
    refine ⟨n + k, by omega, w, seed, ?_, ?_, hseed, ?_,
      hsurjective, Or.inl ?_⟩
    · intro i
      simp [w]
    · simp [w]
    · simpa [w, hx0]
    · ext i
      simp [w, osiiStrictScalarSeedCoefficientTarget]
  · let w : Fin (n + k) -> Real :=
      Fin.append w0 (fun _ : Fin k => 0)
    have hw : forall i, 0 <= w i := by
      intro i
      induction i using Fin.addCases with
      | left i => simpa [w] using hw0 i
      | right i => simp [w]
    have hsum : (∑ i, w i) = ∑ i, w0 i := by
      simp [w, Fin.sum_univ_add]
    have hcombination :
        (∑ i, w i • seed i) = x := by
      rw [Fin.sum_univ_add]
      simpa [w, seed, bridge] using hcombination0
    refine ⟨n + k, by omega, w, seed, hw, ?_, hseed,
      hcombination, hsurjective, Or.inr ?_⟩
    · rw [hsum]
      exact hsum0
    · have hmap :
          osiiStrictScalarSeedCoefficientMap seed
              (osiiStrictScalarSeedCoefficientTarget w) =
            fun j => (x j : Complex) * I :=
        osiiStrictScalarSeedCoefficientMap_target
          w seed x hcombination
      intro hzero
      apply hx0
      funext j
      have hj :=
        congrArg Complex.im
          (congrFun (hmap.symm.trans hzero) j)
      simpa using hj

/-- A finite raw generator family admits one common analytic rank while
retaining every raw lower-block witness. -/
theorem exists_common_ranked_rawGeneratorSeedFamily
    {k depth n : Nat} [NeZero n]
    (seed : Fin n -> Fin k -> Real)
    (hseed : forall i,
      Nonempty (RawGeneratorSeedData k depth (seed i))) :
    ∃ rank, forall i,
      Nonempty (RawGeneratorRankSuccessorSeedData rank k depth (seed i)) := by
  choose localRank ranked using
    fun i => (Classical.choice (hseed i)).exists_ranked
  let rank : Nat := Finset.univ.sup localRank
  refine ⟨rank, ?_⟩
  intro i
  obtain ⟨H⟩ := ranked i
  exact ⟨H.mono
    (Finset.le_sup (s := Finset.univ) (f := localRank)
      (Finset.mem_univ i))⟩

/-- An MZ-ready raw generator presentation at one common analytic rank. -/
structure RawRankedGeneratorSectionPresentationData
    (rank k depth : Nat)
    (x : Fin k -> Real) where
  seedCount : Nat
  seedCount_pos : 0 < seedCount
  weight : Fin seedCount -> Real
  seed : Fin seedCount -> Fin k -> Real
  weight_nonneg : forall i, 0 <= weight i
  weight_sum_lt_one : (∑ i, weight i) < 1
  seed_raw : forall i,
    Nonempty (RawGeneratorRankSuccessorSeedData
      rank k depth (seed i))
  combination_eq : (∑ i, weight i • seed i) = x
  coefficient_surjective :
    Function.Surjective (osiiStrictScalarSeedCoefficientMap seed)
  target_regular :
    osiiStrictScalarSeedCoefficientTarget weight = 0 ∨
      osiiStrictScalarSeedCoefficientMap seed
          (osiiStrictScalarSeedCoefficientTarget weight) ≠ 0

/-- Every positive-arity raw next-depth scalar point has an MZ-ready raw
generator presentation at one finite analytic rank. -/
theorem exists_rankedSectionPresentation
    {k depth : Nat} [NeZero k]
    {x : Fin k -> Real}
    (hx : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar k (depth + 1) x) :
    ∃ rank,
      Nonempty
        (RawRankedGeneratorSectionPresentationData
          rank k depth x) := by
  obtain ⟨n, hn, w, seed, hw, hsum, hseed, hcombination,
      hsurjective, hregular⟩ :=
    exists_sectionRegular_rawGeneratorSeedCombination_fin hx
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨rank, hseedRank⟩ :=
    exists_common_ranked_rawGeneratorSeedFamily seed hseed
  exact ⟨rank, ⟨{
    seedCount := n
    seedCount_pos := hn
    weight := w
    seed := seed
    weight_nonneg := hw
    weight_sum_lt_one := hsum
    seed_raw := hseedRank
    combination_eq := hcombination
    coefficient_surjective := hsurjective
    target_regular := hregular }⟩⟩

namespace RawRankedGeneratorSectionPresentationData

/-- The represented raw target lies in the next analytic-rank scalar
stratum.  The unused convex mass is placed at the rank-polymorphic zero
point. -/
theorem toRankSucc
    {rank k depth : Nat}
    {x : Fin k -> Real}
    (S : RawRankedGeneratorSectionPresentationData
      rank k depth x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      (rank + 1) .scalar k (depth + 1) x := by
  let total : Real := ∑ i, S.weight i
  let weight : Fin (S.seedCount + 1) -> Real :=
    Fin.append S.weight (fun _ : Fin 1 => 1 - total)
  let seed : Fin (S.seedCount + 1) -> Fin k -> Real :=
    Fin.append S.seed (fun _ : Fin 1 => 0)
  have hweight_nonneg : forall i, 0 <= weight i := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [weight] using S.weight_nonneg i
    | right i =>
        have htotal : total <= 1 := S.weight_sum_lt_one.le
        simp [weight, htotal]
  have hweight_sum : (∑ i, weight i) = 1 := by
    simp [weight, Fin.sum_univ_add, total]
  have hseed : forall i,
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (depth + 1) (seed i) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
        simpa [seed] using
          (Classical.choice (S.seed_raw i)).toIsGeneratorRankSuccessorSeed
            |>.toRankSuccessorSeed.toRankSucc
    | right i =>
        simpa [seed] using
          (OSIIStrictGeneratedLogarithmicArgumentAtRank.scalarZero
            k (depth + 1)).mono (by omega)
  have hconv :=
    (convex_osiiStrictGeneratedLogarithmicBaseAtRank
      k (depth + 1) (rank + 1)).sum_mem
      (fun i _ => hweight_nonneg i) hweight_sum
      (fun i _ => hseed i)
  have hcombination : (∑ i, weight i • seed i) = x := by
    rw [Fin.sum_univ_add]
    simpa [weight, seed, total] using S.combination_eq
  rw [← hcombination]
  exact hconv

end RawRankedGeneratorSectionPresentationData

end OSIIChapterV
end OSReconstruction
