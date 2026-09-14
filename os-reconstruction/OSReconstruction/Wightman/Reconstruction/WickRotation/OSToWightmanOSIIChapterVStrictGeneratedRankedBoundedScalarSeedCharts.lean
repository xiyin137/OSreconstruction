/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientBoundedBranchAtlas












noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A rank-successor seed produced by the generator constructor. -/
def IsGeneratorRankSuccessorSeed
    (rank k targetDepth : Nat)
    (x : Fin k -> Real) : Prop :=
  ∃ (i : GeneratorIndex k) (sourceDepth : Nat)
      (left : Fin i.n -> Real) (theta : Real)
      (right : Fin i.m -> Real),
    sourceDepth + 1 = targetDepth ∧
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.n sourceDepth left ∧
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed i.m sourceDepth right ∧
    |theta| < Real.pi / 2 ∧
    osiiArgumentGeneratorPoint i left theta right = x

/-- A rank-successor seed produced by vacuum-tail projection. -/
def IsMixedTailRankSuccessorSeed
    (rank k targetDepth : Nat)
    (x : Fin k -> Real) : Prop :=
  ∃ y : Fin (k + 1) -> Real,
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed (k + 1) targetDepth y ∧
    Fin.tail y = x

/-- Signed contractions preserve every strict generated analytic-rank
stratum.  Coordinatewise solidity, rather than positivity of the scalar,
handles the negative active-coefficient branch. -/
theorem strictGeneratedAtRank_smul_of_abs_le_one
    {rank : Nat} {kind : OSIILogarithmicArgumentKind}
    {n targetDepth : Nat} {x : Fin n -> Real}
    (hx : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank kind n targetDepth x)
    (t : Real) (ht : |t| <= 1) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank kind n targetDepth (t • x) := by
  cases kind with
  | scalar =>
      apply hx.scalar_hyperrectangle
      intro i
      change |t * x i| <= |x i|
      rw [abs_mul]
      calc
        |t| * |x i| <= 1 * |x i| :=
          mul_le_mul_of_nonneg_right ht (abs_nonneg (x i))
        _ = |x i| := one_mul _
  | mixed =>
      apply hx.mixedHyperrectangle
      intro i
      change |t * x i| <= |x i|
      rw [abs_mul]
      calc
        |t| * |x i| <= 1 * |x i| :=
          mul_le_mul_of_nonneg_right ht (abs_nonneg (x i))
        _ = |x i| := one_mul _

/-- Signed contractions preserve the generator constructor itself. -/
theorem IsGeneratorRankSuccessorSeed.smul_of_abs_le_one
    {rank k targetDepth : Nat}
    {x : Fin k -> Real}
    (hx : IsGeneratorRankSuccessorSeed rank k targetDepth x)
    (t : Real) (ht : |t| <= 1) :
    IsGeneratorRankSuccessorSeed
      rank k targetDepth (t • x) := by
  obtain ⟨i, sourceDepth, left, theta, right,
    hdepth, hleft, hright, htheta, rfl⟩ := hx
  refine
    ⟨i, sourceDepth, t • left, t * theta, t • right,
      hdepth, ?_, ?_, ?_, ?_⟩
  · exact strictGeneratedAtRank_smul_of_abs_le_one hleft t ht
  · exact strictGeneratedAtRank_smul_of_abs_le_one hright t ht
  · rw [abs_mul]
    exact
      (mul_le_mul_of_nonneg_right ht (abs_nonneg theta)).trans_lt
        (by simpa using htheta)
  · funext j
    simp only [osiiArgumentGeneratorPoint, Pi.smul_apply]
    split_ifs <;> simp

/-- Forget the named generator presentation and recover the corresponding
constructor of the canonical rank-successor seed predicate. -/
theorem IsGeneratorRankSuccessorSeed.toRankSuccessorSeed
    {rank k targetDepth : Nat}
    {x : Fin k -> Real}
    (hx : IsGeneratorRankSuccessorSeed rank k targetDepth x) :
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank k targetDepth x := by
  obtain ⟨i, sourceDepth, left, theta, right,
    hdepth, hleft, hright, htheta, hpoint⟩ := hx
  rw [← hpoint, ← hdepth]
  exact
    OSIIStrictGeneratedScalarRankSuccessorSeed.generatorMemSucc
      i sourceDepth left theta right hleft hright htheta

/-- Signed contractions preserve the mixed-tail constructor itself. -/
theorem IsMixedTailRankSuccessorSeed.smul_of_abs_le_one
    {rank k targetDepth : Nat}
    {x : Fin k -> Real}
    (hx : IsMixedTailRankSuccessorSeed rank k targetDepth x)
    (t : Real) (ht : |t| <= 1) :
    IsMixedTailRankSuccessorSeed
      rank k targetDepth (t • x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine
    ⟨t • y,
      strictGeneratedAtRank_smul_of_abs_le_one hy t ht, ?_⟩
  funext j
  simp [Fin.tail, Pi.smul_apply]

/-- Coordinatewise shrinking preserves the mixed-tail constructor itself.
This is the tail analogue of
`IsGeneratorRankSuccessorSeed.coordinatewiseShrink`; it keeps constructor
provenance after a positive real VI.2 shift shrinks principal arguments. -/
theorem IsMixedTailRankSuccessorSeed.coordinatewiseShrink
    {rank k targetDepth : Nat}
    {x : Fin k -> Real}
    (hx : IsMixedTailRankSuccessorSeed rank k targetDepth x)
    (z : Fin k -> Real)
    (hz : forall i, |z i| <= |x i|) :
    IsMixedTailRankSuccessorSeed rank k targetDepth z := by
  obtain ⟨y, hy, htail⟩ := hx
  let y' : Fin (k + 1) -> Real := Fin.cons 0 z
  have hy' : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .mixed (k + 1) targetDepth y' := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.mixedHyperrectangle
      hy y'
    intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · have hy0 :=
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
          (by omega : 1 <= k + 1) hy
      simpa [y'] using congrArg abs hy0.symm
    · have htailAt := congrFun htail a
      have hya : y a.succ = x a := by
        simpa [Fin.tail] using htailAt
      simpa [y', hya] using hz a
  refine ⟨y', hy', ?_⟩
  funext a
  simp [y', Fin.tail]

/-- The inductive successor seed predicate is exactly the union of its old,
generator, and vacuum-tail constructors. -/
theorem strictGeneratedScalarRankSuccessorSeed_cases
    {rank k targetDepth : Nat}
    {x : Fin k -> Real}
    (hx : OSIIStrictGeneratedScalarRankSuccessorSeed
      rank k targetDepth x) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar k targetDepth x ∨
      IsGeneratorRankSuccessorSeed rank k targetDepth x ∨
      IsMixedTailRankSuccessorSeed rank k targetDepth x := by
  cases hx with
  | old hx =>
      exact Or.inl hx
  | generatorMemSucc i sourceDepth left theta right
      hleft hright htheta =>
      exact Or.inr (Or.inl
        ⟨i, sourceDepth, left, theta, right, rfl,
          hleft, hright, htheta, rfl⟩)
  | mixedTailMemScalar targetDepth y hy =>
      exact Or.inr (Or.inr ⟨y, hy, rfl⟩)

/-- The radial exhaustion may be chosen with the canonical first-bridge
generator, and with its complete predecessor mixed tail retained explicitly.

The older radial-contraction theorem records only an existential generator
seed.  Equation `(6.29)` needs more provenance: the nontrivial reflected
source is the mixed tail at the preceding outer depth.  This statement keeps
that witness without strengthening the recursive-angle hypothesis. -/
theorem exists_rank_recursiveAngle_firstBridge_radialExpansion
    (q N : Nat)
    (hdepth : q <= N) :
    ∃ rank : Nat, ∃ r : Real,
      r = 1 - 1 / (2 : Real) ^ (N + 1) ∧
        0 < r ∧ r < 1 ∧
        ∀ x : Fin (q + 1) -> Real,
          (∀ i,
            |x i| < osiiRecursiveAngleAperture (q + 1) (N + 1) i) ->
          ∃ theta : Real, ∃ right : Fin (q + 1) -> Real,
            OSIIStrictGeneratedLogarithmicArgumentAtRank
                rank .mixed (q + 1) N right ∧
              (∀ j : Fin q,
                |osiiMixedArgumentTail right j| <
                  osiiRecursiveAngleAperture q N j) ∧
              |theta| < Real.pi / 2 ∧
              x = r • osiiArgumentGeneratorPoint
                (firstBridgeGeneratorIndex q)
                (0 : Fin 1 -> Real) theta right := by
  let r : Real := 1 - 1 / (2 : Real) ^ (N + 1)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact recursiveAngle_explicitContraction_pos N
  have hr_lt : r < 1 := by
    dsimp [r]
    exact recursiveAngle_explicitContraction_lt_one N
  have hrtheta_bound :
      recursiveAngle 1 (N + 1) <= r * (Real.pi / 2) := by
    simpa [r] using
      (recursiveAngle_one_succ_eq_explicitContraction N).le
  by_cases hq : q = 0
  · subst q
    refine ⟨0, r, rfl, hr_pos, hr_lt, ?_⟩
    intro x hx
    let y : Fin (0 + 1) -> Real := fun j => x j / r
    refine ⟨y 0, (0 : Fin 1 -> Real), ?_, ?_, ?_, ?_⟩
    · exact
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_zero_mem
          0 1 N (by omega)
    · intro j
      exact Fin.elim0 j
    · have hx0_bound : |x 0| < r * (Real.pi / 2) := by
        calc
          |x 0| < osiiRecursiveAngleAperture 1 (N + 1) 0 := hx 0
          _ = recursiveAngle 1 (N + 1) := by rfl
          _ <= r * (Real.pi / 2) := hrtheta_bound
      change |x 0 / r| < Real.pi / 2
      rw [abs_div, abs_of_pos hr_pos]
      exact (div_lt_iff₀ hr_pos).2 (by simpa [mul_comm] using hx0_bound)
    · have hy :
          osiiArgumentGeneratorPoint (firstBridgeGeneratorIndex 0)
              (0 : Fin 1 -> Real) (y 0) (0 : Fin 1 -> Real) = y := by
        rw [osiiArgumentGeneratorPoint_firstBridge]
        have htail :
            Fin.tail (0 : Fin 1 -> Real) = Fin.tail y :=
          Subsingleton.elim _ _
        rw [htail]
        exact Fin.cons_self_tail y
      rw [hy]
      ext j
      change x j = r * (x j / r)
      field_simp [hr_pos.ne']
  · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
    obtain ⟨rank, hrank⟩ :=
      OSIIStrictGeneratedLogarithmicArgumentAtRank.exists_rank_strict_recursiveAngle_mixedTail_box_subset
        q N hq_pos
    refine ⟨rank, r, rfl, hr_pos, hr_lt, ?_⟩
    intro x hx
    let y : Fin (q + 1) -> Real := fun j => x j / r
    let tail : Fin q -> Real := Fin.tail y
    have htail :
        ∀ j, |tail j| < osiiRecursiveAngleAperture q N j := by
      intro j
      have hnext := hx j.succ
      have hbound :
          |x j.succ| < r * osiiRecursiveAngleAperture q N j := by
        calc
          |x j.succ| <
              osiiRecursiveAngleAperture (q + 1) (N + 1) j.succ :=
            hnext
          _ <= r * osiiRecursiveAngleAperture q N j := by
            dsimp [r]
            exact
              osiiRecursiveAngleAperture_succ_tail_le_explicitContraction
                q N hdepth j
      change |x j.succ / r| < osiiRecursiveAngleAperture q N j
      rw [abs_div, abs_of_pos hr_pos]
      exact (div_lt_iff₀ hr_pos).2 (by simpa [mul_comm] using hbound)
    let right : Fin (q + 1) -> Real :=
      osiiMixedArgumentOfTail (by omega) tail
    have hright :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          rank .mixed (q + 1) N right :=
      hrank tail htail
    have hright_tail : Fin.tail right = Fin.tail y := by
      change osiiMixedArgumentTail right = tail
      simpa [right] using
        (osiiMixedArgumentTail_ofTail
          (n := q + 1) (by omega) tail)
    refine ⟨y 0, right, hright, ?_, ?_, ?_⟩
    · intro j
      change |Fin.tail right j| < osiiRecursiveAngleAperture q N j
      rw [hright_tail]
      exact htail j
    · have hx0_bound : |x 0| < r * (Real.pi / 2) := by
        calc
          |x 0| <
              osiiRecursiveAngleAperture (q + 1) (N + 1) 0 := hx 0
          _ = recursiveAngle 1 (N + 1) := by rfl
          _ <= r * (Real.pi / 2) := hrtheta_bound
      change |x 0 / r| < Real.pi / 2
      rw [abs_div, abs_of_pos hr_pos]
      exact (div_lt_iff₀ hr_pos).2 (by simpa [mul_comm] using hx0_bound)
    · have hy :
          osiiArgumentGeneratorPoint (firstBridgeGeneratorIndex q)
              (0 : Fin 1 -> Real) (y 0) right = y := by
        rw [osiiArgumentGeneratorPoint_firstBridge]
        rw [hright_tail]
        exact Fin.cons_self_tail y
      rw [hy]
      ext j
      change x j = r * (x j / r)
      field_simp [hr_pos.ne']

/-- If `active` is the only coefficient with nonzero imaginary part, the
imaginary logarithmic argument is exactly its scalar multiple of the active
seed. -/
theorem osiiStrictScalarSeedCoefficientMap_im_eq_active
    {m n : Nat}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hzero : forall j, j ≠ active -> (r j).im = 0) :
    (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) =
      (r active).im • seed active := by
  rw [osiiStrictScalarSeedCoefficientMap_im]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_single active ?_ ?_
  · intro i _hi hia
    rw [hzero i hia]
    simp
  · intro hactive
    simp at hactive

/-- In the old-seed case, the actual imaginary argument of a flat point
stays in the same analytic-rank stratum. -/
theorem osiiStrictScalarSeedCoefficientMap_im_oldAtRank
    {m n rank targetDepth : Nat}
    {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hold : OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar m targetDepth (seed active)) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar m targetDepth
        (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) := by
  rw [osiiStrictScalarSeedCoefficientMap_im_eq_active
    seed r active hactive.2]
  exact strictGeneratedAtRank_smul_of_abs_le_one
    hold (r active).im (hactive.1.trans hrho_lt_one.le)

/-- In the generator case, the actual imaginary argument of a flat point is
again a generator seed, with all source arguments and the bridge angle
contracted by the active coefficient. -/
theorem osiiStrictScalarSeedCoefficientMap_im_isGeneratorRankSuccessorSeed
    {m n rank targetDepth : Nat}
    {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hgenerator : IsGeneratorRankSuccessorSeed
      rank m targetDepth (seed active)) :
    IsGeneratorRankSuccessorSeed rank m targetDepth
      (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) := by
  rw [osiiStrictScalarSeedCoefficientMap_im_eq_active
    seed r active hactive.2]
  exact hgenerator.smul_of_abs_le_one
    (r active).im (hactive.1.trans hrho_lt_one.le)

/-- In the vacuum-tail case, the actual imaginary argument of a flat point
is again the tail of a mixed argument at the same source rank. -/
theorem osiiStrictScalarSeedCoefficientMap_im_isMixedTailRankSuccessorSeed
    {m n rank targetDepth : Nat}
    {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (htail : IsMixedTailRankSuccessorSeed
      rank m targetDepth (seed active)) :
    IsMixedTailRankSuccessorSeed rank m targetDepth
      (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) := by
  rw [osiiStrictScalarSeedCoefficientMap_im_eq_active
    seed r active hactive.2]
  exact htail.smul_of_abs_le_one
    (r active).im (hactive.1.trans hrho_lt_one.le)

/-- The three genuine analytic chart obligations for one finite family of
rank-successor seeds.  At a flat-window point, `active` is the unique
possibly non-real coefficient. -/
structure BoundedRankSuccessorSeedFlatChartProducerData
    {m n : Nat}
    {B S rho : Real}
    (A : BoundedScalarContinuationData m B)
    (P : SCV.StripCompactificationParameters S rho)
    (rank targetDepth : Nat)
    (seed : Fin n -> Fin m -> Real) where
  seed_rank : forall a,
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank m targetDepth (seed a)
  oldChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar m targetDepth (seed active) ->
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientMap seed r)
  generatorChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    IsGeneratorRankSuccessorSeed
      rank m targetDepth (seed active) ->
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientMap seed r)
  mixedTailChart : forall
    (active : Fin n)
    (r : Fin n -> Complex),
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho ->
    (|(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0) ->
    IsMixedTailRankSuccessorSeed
      rank m targetDepth (seed active) ->
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientMap seed r)

namespace BoundedRankSuccessorSeedFlatChartProducerData

variable {m n : Nat}
variable {B S rho : Real}
variable {A : BoundedScalarContinuationData m B}
variable {P : SCV.StripCompactificationParameters S rho}
variable {rank targetDepth : Nat}
variable {seed : Fin n -> Fin m -> Real}

/-- Every flat-window point has a bounded chart by selecting its active
coefficient and eliminating the active seed into the three constructors. -/
theorem nonempty_targetChart
    (D : BoundedRankSuccessorSeedFlatChartProducerData
      A P rank targetDepth seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho) :
    Nonempty (BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientMap seed r)) := by
  have himag :
      (fun j => (r j).im) ∈
        osiiCoefficientClosedFlatImaginaryUnion (Fin n) rho :=
    hr.2
  obtain ⟨active, hactive, hzero⟩ := himag
  rcases strictGeneratedScalarRankSuccessorSeed_cases
      (D.seed_rank active) with hold | hgenerator | htail
  · exact ⟨D.oldChart active r hr ⟨hactive, hzero⟩ hold⟩
  · exact ⟨D.generatorChart active r hr
      ⟨hactive, hzero⟩ hgenerator⟩
  · exact ⟨D.mixedTailChart active r hr
      ⟨hactive, hzero⟩ htail⟩

/-- Select the target-adapted chart at one flat-window point. -/
noncomputable def targetChart
    (D : BoundedRankSuccessorSeedFlatChartProducerData
      A P rank targetDepth seed)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin n) (P.radius + rho) rho) :
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientMap seed r) :=
  Classical.choice (D.nonempty_targetChart r hr)

end BoundedRankSuccessorSeedFlatChartProducerData

namespace BoundedStrictGeneratedScalarRankSuccessorData

variable {m : Nat} {B : Real}

end BoundedStrictGeneratedScalarRankSuccessorData

namespace BoundedRetainedStrictGeneratedScalarRankSuccessorData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {rank depth : Nat} {target : Fin m -> Real}

end BoundedRetainedStrictGeneratedScalarRankSuccessorData
end OSIIChapterV
end OSReconstruction
