/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedLogarithmicDomains






















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The strict generated logarithmic grammar stratified by analytic rank.

The first index records the number of generator/tail continuation steps.
The `weaken` constructor makes the strata increasing. -/
inductive OSIIStrictGeneratedLogarithmicArgumentAtRank :
    Nat -> OSIILogarithmicArgumentKind ->
      (n N : Nat) -> (Fin n -> Real) -> Prop where
  | scalarZero (n N : Nat) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        0 .scalar n N (0 : Fin n -> Real)
  | initialMixedZero (n : Nat) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        0 .mixed n 0 (0 : Fin n -> Real)
  | weaken
      {rank : Nat} {kind : OSIILogarithmicArgumentKind}
      {n N : Nat} {x : Fin n -> Real}
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank kind n N x) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) kind n N x
  | scalarConvex
      {rank k N : Nat} {x y : Fin k -> Real}
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .scalar k N x)
      (hy :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .scalar k N y)
      (a b : Real) (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar k N (a • x + b • y)
  | mixedHyperrectangle
      {rank n N : Nat} {x : Fin n -> Real}
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed n N x)
      (y : Fin n -> Real)
      (hy : forall i, |y i| <= |x i|) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n N y
  | generatorMemSucc
      {rank k : Nat} (i : GeneratorIndex k) (N : Nat)
      (left : Fin i.n -> Real) (theta : Real) (right : Fin i.m -> Real)
      (hleft :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed i.n N left)
      (hright :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed i.m N right)
      (htheta : |theta| < Real.pi / 2) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (N + 1)
        (osiiArgumentGeneratorPoint i left theta right)
  | mixedOfDiagonal
      {rank : Nat}
      (n : Nat) (hn : 1 <= n) (N : Nat) (x : Fin n -> Real)
      (hx0 : x ⟨0, hn⟩ = 0)
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .scalar (2 * n - 1) N (osiiArgumentDiagonal hn x)) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n N x
  | mixedTailMemScalar
      {rank : Nat}
      (k N : Nat) (x : Fin (k + 1) -> Real)
      (hx :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed (k + 1) N x) :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k N (Fin.tail x)

/-- The strict scalar base available after at most `rank` analytic steps. -/
def osiiStrictGeneratedLogarithmicBaseAtRank
    (k N rank : Nat) : Set (Fin k -> Real) :=
  {x |
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar k N x}

/-- The strict mixed base available after at most `rank` analytic steps. -/
def osiiStrictGeneratedMixedLogarithmicBaseAtRank
    (n N rank : Nat) : Set (Fin n -> Real) :=
  {x |
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed n N x}

namespace OSIIStrictGeneratedLogarithmicArgumentAtRank

/-- Erasing the analytic rank gives an ordinary strict generated
derivation. -/
theorem toStrictGenerated
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    OSIIStrictGeneratedLogarithmicArgument kind n N x := by
  induction hx with
  | scalarZero n N =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.scalar_zero_mem n N
  | initialMixedZero n =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.initialMixedZero n
  | weaken hx ih =>
      exact ih
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.scalarConvex
          ihx ihy a b ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.mixedHyperrectangle
          ih y hy
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.generatorMemSucc
          i N left theta right ihleft ihright htheta
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.mixedOfDiagonal
          n hn N x hx0 ih
  | mixedTailMemScalar k N x hx ih =>
      exact
        OSIIStrictGeneratedLogarithmicArgument.mixedTailMemScalar
          k N x ih

/-- Ranked derivations are monotone in the analytic rank. -/
theorem mono
    {rank rank' : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hRank : rank <= rank')
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank' kind n N x := by
  refine Nat.le_induction hx ?_ rank' hRank
  intro current _ hcurrent
  exact
    OSIIStrictGeneratedLogarithmicArgumentAtRank.weaken hcurrent

/-- Increasing the outer depth preserves a ranked derivation.

The mixed grammar has a genuine arity-zero exception: its only primitive
zero witness lives at depth zero.  All physical mixed tails have positive
arity, so the usable statement records that hypothesis explicitly. -/
theorem depth_succ_of_scalar_or_mixed_pos
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    (kind = .mixed -> 1 <= n) ->
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n (N + 1) x := by
  induction hx with
  | scalarZero n N =>
      intro _hkind
      exact scalarZero n (N + 1)
  | initialMixedZero n =>
      intro hkind
      have hn : 1 <= n := hkind rfl
      have hdiagonal :
          osiiArgumentDiagonal hn (0 : Fin n -> Real) =
            (0 : Fin (2 * n - 1) -> Real) := by
        funext i
        simp [osiiArgumentDiagonal]
      exact
        mixedOfDiagonal n hn 1 (0 : Fin n -> Real) (by simp)
          (by
            rw [hdiagonal]
            exact
              (scalarZero (2 * n - 1) 1))
  | weaken hx ih =>
      intro hkind
      exact weaken (ih hkind)
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      intro _hkind
      exact
        scalarConvex
          (ihx (by intro h; cases h))
          (ihy (by intro h; cases h))
          a b ha hb hab
  | mixedHyperrectangle hx y hy ih =>
      intro hkind
      exact mixedHyperrectangle (ih hkind) y hy
  | generatorMemSucc i N left theta right hleft hright htheta
      ihleft ihright =>
      intro _hkind
      exact
        generatorMemSucc i (N + 1) left theta right
          (ihleft (fun _ => i.hn))
          (ihright (fun _ => i.hm))
          htheta
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro _hkind
      exact
        mixedOfDiagonal n hn (N + 1) x hx0
          (ih (by intro h; cases h))
  | mixedTailMemScalar k N x hx ih =>
      intro _hkind
      exact
        mixedTailMemScalar k (N + 1) x
          (ih (fun _ => by omega))

/-- Positive-arity mixed ranked arguments persist at the next outer depth. -/
theorem mixed_depth_succ
    {rank n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n N x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed n (N + 1) x :=
  hx.depth_succ_of_scalar_or_mixed_pos (fun _ => hn)

/-- Every ordinary strict generated derivation has finite analytic rank. -/
theorem exists_rank
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIStrictGeneratedLogarithmicArgument kind n N x) :
    exists rank,
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x := by
  induction hx with
  | initialMixedZero n =>
      exact ⟨0, initialMixedZero n⟩
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      obtain ⟨rankX, hrankX⟩ := ihx
      obtain ⟨rankY, hrankY⟩ := ihy
      let rank := max rankX rankY
      refine ⟨rank, scalarConvex ?_ ?_ a b ha hb hab⟩
      · exact hrankX.mono (Nat.le_max_left _ _)
      · exact hrankY.mono (Nat.le_max_right _ _)
  | mixedHyperrectangle hx y hy ih =>
      obtain ⟨rank, hrank⟩ := ih
      exact ⟨rank, mixedHyperrectangle hrank y hy⟩
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      obtain ⟨rankL, hrankL⟩ := ihleft
      obtain ⟨rankR, hrankR⟩ := ihright
      let rank := max rankL rankR
      refine
        ⟨rank + 1,
          generatorMemSucc i N left theta right ?_ ?_ htheta⟩
      · exact hrankL.mono (Nat.le_max_left _ _)
      · exact hrankR.mono (Nat.le_max_right _ _)
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      obtain ⟨rank, hrank⟩ := ih
      exact ⟨rank, mixedOfDiagonal n hn N x hx0 hrank⟩
  | mixedTailMemScalar k N x hx ih =>
      obtain ⟨rank, hrank⟩ := ih
      exact ⟨rank + 1, mixedTailMemScalar k N x hrank⟩

/-- A closed generated derivation admits one analytic rank which works for
every strict radial contraction.  The rank depends only on the derivation,
not on the contraction factor. -/
theorem exists_rank_smul_toStrict
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx : OSIIGeneratedLogarithmicArgument kind n N x) :
    ∃ rank, forall (r : Real), 0 <= r -> r < 1 ->
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N (r • x) := by
  induction hx with
  | initialMixedZero n =>
      refine ⟨0, ?_⟩
      intro r _hr0 _hr1
      simpa using
        OSIIStrictGeneratedLogarithmicArgumentAtRank.initialMixedZero n
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      obtain ⟨rankX, hrankX⟩ := ihx
      obtain ⟨rankY, hrankY⟩ := ihy
      let rank := max rankX rankY
      refine ⟨rank, ?_⟩
      intro r hr0 hr1
      have hx' := (hrankX r hr0 hr1).mono
        (Nat.le_max_left rankX rankY)
      have hy' := (hrankY r hr0 hr1).mono
        (Nat.le_max_right rankX rankY)
      have hconvex :=
        OSIIStrictGeneratedLogarithmicArgumentAtRank.scalarConvex
          hx' hy' a b ha hb hab
      simpa [rank, smul_add, smul_smul, mul_comm] using hconvex
  | @mixedHyperrectangle n N x hx y hy ih =>
      obtain ⟨rank, hrank⟩ := ih
      refine ⟨rank, ?_⟩
      intro r hr0 hr1
      apply
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
          (hrank r hr0 hr1) (r • y)
      intro i
      change |r * y i| <= |r * x i|
      rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left (hy i) hr0
  | generatorMemSucc i N left theta right hleft hright htheta ihleft ihright =>
      obtain ⟨rankL, hrankL⟩ := ihleft
      obtain ⟨rankR, hrankR⟩ := ihright
      let rank := max rankL rankR
      refine ⟨rank + 1, ?_⟩
      intro r hr0 hr1
      have hleft' := (hrankL r hr0 hr1).mono
        (Nat.le_max_left rankL rankR)
      have hright' := (hrankR r hr0 hr1).mono
        (Nat.le_max_right rankL rankR)
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
        OSIIStrictGeneratedLogarithmicArgumentAtRank.generatorMemSucc
          i N (r • left) (r * theta) (r • right)
          hleft' hright' htheta'
      convert hgenerator using 1
      funext j
      simp only [osiiArgumentGeneratorPoint, Pi.smul_apply]
      split_ifs <;> simp
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      obtain ⟨rank, hrank⟩ := ih
      refine ⟨rank, ?_⟩
      intro r hr0 hr1
      apply
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedOfDiagonal
          n hn N (r • x)
      · simp [Pi.smul_apply, hx0]
      · have hdiag := hrank r hr0 hr1
        convert hdiag using 1
        funext j
        simp only [osiiArgumentDiagonal, Pi.smul_apply]
        split_ifs <;> simp
  | mixedTailMemScalar k N x hx ih =>
      obtain ⟨rank, hrank⟩ := ih
      refine ⟨rank + 1, ?_⟩
      intro r hr0 hr1
      have htail :=
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedTailMemScalar
          k N (r • x) (hrank r hr0 hr1)
      simpa [Fin.tail, Pi.smul_apply] using htail

/-- The unranked strict grammar is the union of its finite analytic-rank
strata. -/
theorem iff_exists_rank
    {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real} :
    OSIIStrictGeneratedLogarithmicArgument kind n N x ↔
      exists rank,
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank kind n N x := by
  constructor
  · exact exists_rank
  · rintro ⟨rank, hrank⟩
    exact hrank.toStrictGenerated

/-- Every ranked mixed argument retains the distinguished zero head. -/
theorem mixed_head_eq_zero
    {rank n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n N x) :
    x ⟨0, hn⟩ = 0 :=
  OSIIGeneratedLogarithmicArgument.mixed_head_eq_zero
    hn hx.toStrictGenerated.toGenerated

/-- Every scalar analytic-rank stratum contains the origin. -/
theorem scalar_zero_mem
    (rank n N : Nat) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar n N (0 : Fin n -> Real) :=
  (scalarZero n N).mono (Nat.zero_le rank)

private theorem rank_zero_shape_aux
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    rank = 0 ->
    match kind with
    | .scalar => x = 0
    | .mixed => x = 0 := by
  induction hx with
  | scalarZero =>
      intro _hrank
      rfl
  | initialMixedZero =>
      intro _hrank
      rfl
  | weaken hx ih =>
      intro hrank
      omega
  | @scalarConvex rank k N x y hx hy a b ha hb hab ihx ihy =>
      intro hrank
      have hx0 : x = 0 := ihx hrank
      have hy0 : y = 0 := ihy hrank
      subst x
      subst y
      ext i
      simp
  | @mixedHyperrectangle rank n N x hx y hy ih =>
      intro hrank
      have hx0 : x = 0 := ih hrank
      subst x
      funext i
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa using hy i
      · exact abs_nonneg _
  | generatorMemSucc =>
      intro hrank
      omega
  | @mixedOfDiagonal rank n hn N x hx0 hx ih =>
      intro hrank
      have hdiag : osiiArgumentDiagonal hn x = 0 := ih hrank
      funext i
      have h := congrFun hdiag
        (⟨n - 1 + i.val, by omega⟩ : Fin (2 * n - 1))
      simpa [osiiArgumentDiagonal] using h
  | mixedTailMemScalar =>
      intro hrank
      omega

/-- Rank zero contains no analytic generator or tail step, so every scalar
argument in that stratum is the origin. -/
theorem scalar_eq_zero_of_rank_zero
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        0 .scalar n N x) :
    x = 0 :=
  rank_zero_shape_aux hx rfl

private theorem coordinatewise_closed_aux
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    match kind with
    | .scalar =>
        forall y : Fin n -> Real,
          (forall i, |y i| <= |x i|) ->
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar n N y
    | .mixed => True := by
  induction hx with
  | scalarZero n N =>
      intro y hy
      have hy0 : y = 0 := by
        funext i
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa using hy i
        · exact abs_nonneg _
      subst y
      exact scalarZero n N
  | initialMixedZero n =>
      trivial
  | @weaken rank kind n N x hx ih =>
      cases kind with
      | scalar =>
          intro y hy
          exact weaken (ih y hy)
      | mixed =>
          trivial
  | @scalarConvex rank k N x y hx hy a b ha hb hab ihx ihy =>
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
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar k N (fun i => ratio i * x i) := by
        apply ihx
        intro i
        rw [abs_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hratio i) (abs_nonneg (x i))).trans_eq (one_mul _)
      have hy' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar k N (fun i => ratio i * y i) := by
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
        scalarConvex hx' hy' a b ha hb hab
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
  | @generatorMemSucc rank k i N left theta right
      hleft hright htheta ihleft ihright =>
      intro y hy
      let left' : Fin i.n -> Real :=
        osiiMixedArgumentOfTail i.hn
          (fun a => -y (i.leftGlobalIndex a))
      let right' : Fin i.m -> Real :=
        osiiMixedArgumentOfTail i.hm
          (fun b => y (i.rightGlobalIndex b))
      have hleft' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.n N left' := by
        apply mixedHyperrectangle hleft left'
        apply abs_osiiMixedArgumentOfTail_le i.hn
          (mixed_head_eq_zero i.hn hleft)
        intro a
        simpa [left'] using hy (i.leftGlobalIndex a)
      have hright' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed i.m N right' := by
        apply mixedHyperrectangle hright right'
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
        generatorMemSucc
          i N left' (y i.bridgeGlobalIndex) right'
          hleft' hright' htheta'
      simpa [left', right',
        osiiArgumentGeneratorPoint_reconstruct] using hgen
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      trivial
  | @mixedTailMemScalar rank k N x hx ih =>
      intro y hy
      let x' : Fin (k + 1) -> Real := Fin.cons 0 y
      have hx' :
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed (k + 1) N x' := by
        apply mixedHyperrectangle hx x'
        intro j
        refine Fin.cases ?_ (fun a => ?_) j
        · have hk1 : 1 <= k + 1 := by omega
          have hx0 := mixed_head_eq_zero hk1 hx
          simpa [x'] using congrArg abs hx0.symm
        · simpa [x'] using hy a
      have htail :=
        mixedTailMemScalar k N x' hx'
      simpa [x'] using htail

/-- Coordinatewise shrinking preserves a strict scalar analytic-rank
stratum. -/
theorem scalar_hyperrectangle
    {rank n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar n N x)
    (y : Fin n -> Real)
    (hy : forall i, |y i| <= |x i|) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar n N y :=
  coordinatewise_closed_aux hx y hy

private theorem mixed_diagonal_mem_scalar_aux
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n N : Nat} {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    match kind with
    | .scalar => True
    | .mixed =>
        forall hn : 1 <= n,
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .scalar (2 * n - 1) N
            (osiiArgumentDiagonal hn x) := by
  induction hx with
  | scalarZero n N =>
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
  | @weaken rank kind n N x hx ih =>
      cases kind with
      | scalar =>
          trivial
      | mixed =>
          intro hn
          exact weaken (ih hn)
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      trivial
  | @mixedHyperrectangle rank n N x hx y hy ih =>
      intro hn
      apply scalar_hyperrectangle (ih hn) (osiiArgumentDiagonal hn y)
      intro j
      by_cases hj : j.val < n - 1
      · simpa [osiiArgumentDiagonal, hj] using
          hy ⟨n - 1 - j.val, by omega⟩
      · simpa [osiiArgumentDiagonal, hj] using
          hy ⟨j.val - (n - 1), by omega⟩
  | generatorMemSucc i N left theta right
      hleft hright htheta ihleft ihright =>
      trivial
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro hn'
      simpa using hx
  | mixedTailMemScalar k N x hx ih =>
      trivial

/-- The scalar diagonal of a ranked strict mixed point is available at the
same analytic rank. -/
theorem mixed_diagonal_mem_scalar
    {rank n N : Nat} {x : Fin n -> Real}
    (hn : 1 <= n)
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n N x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar (2 * n - 1) N
      (osiiArgumentDiagonal hn x) :=
  mixed_diagonal_mem_scalar_aux hx hn

/-- Equal-arity reindexing preserves analytic rank. -/
theorem reindex
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n n' N : Nat}
    (h : n = n')
    {x : Fin n -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank kind n N x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank kind n' N (fun j => x ((finCongr h).symm j)) := by
  subst n'
  simpa using hx

/-- At fixed recursive depth, one finite analytic rank contains every mixed
argument whose distinguished head is zero and whose tail lies strictly inside
the recursive-angle box.  The rank is uniform over the complete tail box. -/
theorem exists_rank_strict_recursiveAngle_mixedTail_box_subset
    (k N : Nat) (hk : 0 < k) :
    exists rank,
      forall (tail : Fin k -> Real),
        (forall i, |tail i| < osiiRecursiveAngleAperture k N i) ->
          OSIIStrictGeneratedLogarithmicArgumentAtRank
            rank .mixed (k + 1) N
              (osiiMixedArgumentOfTail (by omega) tail) := by
  have hcornerRaw :=
    osiiGeneratedLogarithmicArgumentDomainSystem.mixedAnglePoint_mem
      N k 0
  obtain ⟨rank, hcornerRank⟩ :=
    exists_rank_smul_toStrict hcornerRaw
  refine ⟨rank, ?_⟩
  intro tail htail
  have hfin : (Finset.univ : Finset (Fin k)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hk
  let ratio : Fin k -> Real :=
    fun i => |tail i| / osiiRecursiveAngleAperture k N i
  let M : Real := Finset.univ.sup' hfin ratio
  have haperture :
      forall i, 0 < osiiRecursiveAngleAperture k N i :=
    fun i => (abs_nonneg (tail i)).trans_lt (htail i)
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
    exact (div_lt_one (haperture i)).2 (htail i)
  let r : Real := (M + 1) / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hr_lt_one : r < 1 := by
    dsimp [r]
    linarith
  have htail_le : forall i,
      |tail i| <= r * osiiRecursiveAngleAperture k N i := by
    intro i
    have hratio_le : ratio i <= M :=
      Finset.le_sup' ratio (Finset.mem_univ i)
    have hMr : M <= r := by
      dsimp [r]
      linarith
    have hdiv :
        |tail i| / osiiRecursiveAngleAperture k N i <= r :=
      hratio_le.trans hMr
    exact (div_le_iff₀ (haperture i)).mp hdiv
  have hscaledRaw := hcornerRank r hr_pos.le hr_lt_one
  have hcard : 1 + k = k + 1 := by omega
  let corner : Fin (k + 1) -> Real :=
    fun j => osiiMixedAnglePoint N k 1 ((finCongr hcard).symm j)
  have hscaledCorner :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed (k + 1) N (r • corner) := by
    have hreindexed := hscaledRaw.reindex hcard
    simpa [corner, Pi.smul_apply] using hreindexed
  apply mixedHyperrectangle hscaledCorner
    (osiiMixedArgumentOfTail (by omega) tail)
  apply abs_osiiMixedArgumentOfTail_le (by omega)
    (mixed_head_eq_zero (by omega) hscaledCorner)
  intro i
  change |tail i| <= |r * corner i.succ|
  rw [abs_mul, abs_of_pos hr_pos]
  simpa [corner, osiiMixedAnglePoint, osiiRecursiveAngleAperture,
    abs_of_nonneg (recursiveAngle_nonneg (i.val + 1) N)] using
      htail_le i

end OSIIStrictGeneratedLogarithmicArgumentAtRank

/-- The ordinary strict scalar base is exhausted by finite analytic-rank
strata. -/
theorem mem_strictGeneratedScalarBase_iff_exists_rank
    {k N : Nat} {x : Fin k -> Real} :
    x ∈ osiiStrictGeneratedLogarithmicBase k N ↔
      exists rank,
        x ∈ osiiStrictGeneratedLogarithmicBaseAtRank k N rank :=
  OSIIStrictGeneratedLogarithmicArgumentAtRank.iff_exists_rank

end OSIIChapterV
end OSReconstruction
