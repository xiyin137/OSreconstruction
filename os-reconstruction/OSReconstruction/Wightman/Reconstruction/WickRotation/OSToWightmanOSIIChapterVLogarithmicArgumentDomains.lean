/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAngleExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates






















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The coordinatewise principal argument of a time-gap point. -/
def osiiTimeArgumentVector {k : ℕ}
    (ζ : OSIITimeGapSpace k) : Fin k → ℝ :=
  fun i => Complex.arg (ζ i)

/-- The part of the product right half-plane whose principal argument vector
belongs to a prescribed logarithmic base. -/
def osiiTimeArgumentCarrier {k : ℕ}
    (base : Set (Fin k → ℝ)) :
    Set (OSIITimeGapSpace k) :=
  {ζ | ζ ∈ osiiTimeRightHalfPlane k ∧
    osiiTimeArgumentVector ζ ∈ base}

/-- A right-half-plane point with vanishing principal arguments is exactly
the positive-real embedding of its coordinatewise real part. -/
theorem eq_positiveRealTimeEmbed_re_of_argumentVector_eq_zero
    {k : ℕ} {ζ : OSIITimeGapSpace k}
    (harg : osiiTimeArgumentVector ζ = 0) :
    ζ = osiiPositiveRealTimeEmbed (fun i => (ζ i).re) := by
  funext i
  have him : (ζ i).im = 0 :=
    (Complex.arg_eq_zero_iff.mp (congrFun harg i)).2
  apply Complex.ext
  · rfl
  · simpa [osiiPositiveRealTimeEmbed] using him

/-- The real part selected by
`eq_positiveRealTimeEmbed_re_of_argumentVector_eq_zero` is strictly
positive coordinatewise. -/
theorem re_mem_strictPositive_of_mem_rightHalfPlane
    {k : ℕ} {ζ : OSIITimeGapSpace k}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    (fun i => (ζ i).re) ∈ section43TimeStrictPositiveRegion k :=
  hζ

/-- The analytic tail domain associated with a logarithmic mixed base.

The omitted head coordinate has argument zero, while the tail lies in the
product right half-plane with argument vector prescribed by the mixed base. -/
def osiiMixedTailArgumentCarrier {k : ℕ}
    (base : Set (Fin (k + 1) → ℝ)) :
    Set (OSIITimeGapSpace k) :=
  {ζ | ζ ∈ osiiTimeRightHalfPlane k ∧
    Fin.cons 0 (osiiTimeArgumentVector ζ) ∈ base}

@[simp]
theorem mem_osiiMixedTailArgumentCarrier_iff
    {k : ℕ} {base : Set (Fin (k + 1) → ℝ)}
    {ζ : OSIITimeGapSpace k} :
    ζ ∈ osiiMixedTailArgumentCarrier base ↔
      ζ ∈ osiiTimeRightHalfPlane k ∧
        Fin.cons 0 (osiiTimeArgumentVector ζ) ∈ base :=
  Iff.rfl

/-- Positive real radial rescaling preserves every mixed principal-argument
fiber. -/
theorem real_smul_mem_osiiMixedTailArgumentCarrier_of_pos
    {k : ℕ}
    {base : Set (Fin (k + 1) → ℝ)}
    {ζ : OSIITimeGapSpace k}
    (hζ : ζ ∈ osiiMixedTailArgumentCarrier base)
    {t : ℝ}
    (ht : 0 < t) :
    t • ζ ∈ osiiMixedTailArgumentCarrier base := by
  refine ⟨?_, ?_⟩
  · intro j
    change 0 < ((t : ℂ) * ζ j).re
    simpa using mul_pos ht (hζ.1 j)
  · have harg :
        osiiTimeArgumentVector (t • ζ) =
          osiiTimeArgumentVector ζ := by
      funext j
      change Complex.arg ((t : ℂ) * ζ j) =
        Complex.arg (ζ j)
      exact Complex.arg_real_mul (ζ j) ht
    simpa [harg] using hζ.2

/-- The closed coordinate box with aperture vector `a`. -/
def osiiClosedArgumentBox {k : ℕ}
    (a : Fin k → ℝ) :
    Set (Fin k → ℝ) :=
  {x | ∀ i, |x i| ≤ a i}

/-- The aperture vector supplied by the exact recursive angles at one arity
and one induction depth. -/
def osiiRecursiveAngleAperture (k N : ℕ) :
    Fin k → ℝ :=
  fun i => recursiveAngle (i.val + 1) N

/-- Every successor tail coordinate is bounded by the same explicit dyadic
contraction of its predecessor coordinate. -/
theorem osiiRecursiveAngleAperture_succ_tail_le_explicitContraction
    (q N : ℕ)
    (hdepth : q ≤ N)
    (j : Fin q) :
    osiiRecursiveAngleAperture (q + 1) (N + 1) j.succ ≤
      (1 - 1 / (2 : ℝ) ^ (N + 1)) *
        osiiRecursiveAngleAperture q N j := by
  change
    recursiveAngle (j.val + 2) (N + 1) ≤
      (1 - 1 / (2 : ℝ) ^ (N + 1)) *
        recursiveAngle (j.val + 1) N
  apply recursiveAngle_succ_succ_le_prev_explicitContraction_of_succ_le
  exact (Nat.succ_le_iff.mpr j.isLt).trans hdepth

/-- An inhabited recursive-angle sector has reached every one of its
coordinates.  This is the converse bookkeeping needed when sector membership
is the only available depth hypothesis. -/
theorem arity_le_depth_of_mem_recursiveAngleTimeArgumentSector
    {k N : ℕ}
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiTimeArgumentSector
      (osiiRecursiveAngleAperture k N)) :
    k ≤ N := by
  by_contra hdepth
  have hNk : N < k := Nat.lt_of_not_ge hdepth
  let i : Fin k := ⟨N, hNk⟩
  have hzero :
      osiiRecursiveAngleAperture k N i = 0 := by
    change recursiveAngle (N + 1) N = 0
    exact recursiveAngle_succ_eq_zero_of_stage_lt N N (by omega)
  have hi := hz.2 i
  rw [hzero] at hi
  exact (not_lt_of_ge (abs_nonneg (Complex.arg (z i)))) hi

/-- The point `w^N(s,t)` from `(5.26)`: `t` zero coordinates followed by
the first `s` recursive angles. -/
def osiiMixedAnglePoint (N s t : ℕ) :
    Fin (t + s) → ℝ :=
  fun j =>
    if j.val < t then 0
    else recursiveAngle (j.val - t + 1) N

/-- The actual `n - 1` analytic coordinates of a mixed Chapter V argument.
The omitted first coordinate is the distinguished zero retained in the
paper's `d_n^(N)` bookkeeping. -/
def osiiMixedArgumentTail {n : ℕ}
    (x : Fin n → ℝ) :
    Fin (n - 1) → ℝ :=
  fun i => x ⟨i.val + 1, by omega⟩

/-- Reconstruct a mixed argument from its analytic tail by restoring the
distinguished leading zero coordinate. -/
def osiiMixedArgumentOfTail
    {n : ℕ} (hn : 1 ≤ n) (tail : Fin (n - 1) → ℝ) :
    Fin n → ℝ :=
  fun j =>
    if hj : j.val = 0 then
      0
    else
      tail ⟨j.val - 1, by omega⟩

@[simp]
theorem osiiMixedArgumentTail_zero (n : ℕ) :
    osiiMixedArgumentTail (0 : Fin n → ℝ) =
      (0 : Fin (n - 1) → ℝ) :=
  rfl

@[simp]
theorem osiiMixedArgumentTail_succ
    {k : ℕ} (x : Fin (k + 1) → ℝ) :
    osiiMixedArgumentTail x = Fin.tail x := by
  rfl

@[simp]
theorem osiiMixedArgumentOfTail_head
    {n : ℕ} (hn : 1 ≤ n) (tail : Fin (n - 1) → ℝ) :
    osiiMixedArgumentOfTail hn tail ⟨0, hn⟩ = 0 := by
  simp [osiiMixedArgumentOfTail]

@[simp]
theorem osiiMixedArgumentTail_ofTail
    {n : ℕ} (hn : 1 ≤ n) (tail : Fin (n - 1) → ℝ) :
    osiiMixedArgumentTail (osiiMixedArgumentOfTail hn tail) = tail := by
  funext a
  simp [osiiMixedArgumentTail, osiiMixedArgumentOfTail]

/-- Coordinate bounds on a mixed tail extend to its reconstruction whenever
the original mixed argument has the required leading zero. -/
theorem abs_osiiMixedArgumentOfTail_le
    {n : ℕ} (hn : 1 ≤ n)
    {x : Fin n → ℝ} {tail : Fin (n - 1) → ℝ}
    (hx0 : x ⟨0, hn⟩ = 0)
    (htail :
      ∀ a, |tail a| ≤ |osiiMixedArgumentTail x a|) :
    ∀ j, |osiiMixedArgumentOfTail hn tail j| ≤ |x j| := by
  intro j
  by_cases hj : j.val = 0
  · have hj' : j = ⟨0, hn⟩ := Fin.ext hj
    subst j
    simp [hx0]
  · have hjpos : 1 ≤ j.val := by omega
    let a : Fin (n - 1) := ⟨j.val - 1, by omega⟩
    have haj : (⟨a.val + 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      dsimp [a]
      omega
    simpa [osiiMixedArgumentOfTail, hj, osiiMixedArgumentTail, a, haj] using
      htail a

/-- The argument vector `(-reverse v', θ, v'')` occurring in `(5.23)`.

The inputs `left` and `right` include their distinguished leading zero
coordinates, so the generator uses only their tails. -/
def osiiArgumentGeneratorPoint {k : ℕ}
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ) :
    Fin k → ℝ :=
  fun j =>
    if hleft : j.val < i.n - 1 then
      -left ⟨i.n - 1 - j.val, by
        have hn := i.hn
        omega⟩
    else if hbridge : j.val = i.n - 1 then
      θ
    else
      right ⟨j.val - (i.n - 1), by
        have hn := i.hn
        have hm := i.hm
        have hnm := i.hnm
        omega⟩

/-- The reflected-left coordinates of a logarithmic generator are the
negated mixed tail in reverse chronological order. -/
@[simp]
theorem osiiArgumentGeneratorPoint_left
    {k : ℕ}
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ)
    (a : Fin (i.n - 1)) :
    osiiArgumentGeneratorPoint i left θ right
        (i.leftGlobalIndex a) =
      -osiiMixedArgumentTail left a := by
  simp only [osiiArgumentGeneratorPoint]
  rw [dif_pos]
  · congr 2
    apply Fin.ext
    have hn := i.n_eq_toGap_add_one
    simp [GeneratorIndex.leftGlobalIndex]
    omega
  · change (Fin.rev a).val < i.n - 1
    exact (Fin.rev a).isLt

/-- The distinguished generator coordinate is exactly the bridge angle. -/
@[simp]
theorem osiiArgumentGeneratorPoint_bridge
    {k : ℕ}
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ) :
    osiiArgumentGeneratorPoint i left θ right
        i.bridgeGlobalIndex = θ := by
  simp [osiiArgumentGeneratorPoint,
    GeneratorIndex.bridgeGlobalIndex]

/-- The right coordinates of a logarithmic generator are the mixed right
tail in chronological order. -/
@[simp]
theorem osiiArgumentGeneratorPoint_right
    {k : ℕ}
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ)
    (b : Fin (i.m - 1)) :
    osiiArgumentGeneratorPoint i left θ right
        (i.rightGlobalIndex b) =
      osiiMixedArgumentTail right b := by
  simp only [osiiArgumentGeneratorPoint]
  rw [dif_neg, dif_neg]
  · congr 1
    apply Fin.ext
    simp [GeneratorIndex.rightGlobalIndex]
    omega
  · simp [GeneratorIndex.rightGlobalIndex]
    omega
  · simp [GeneratorIndex.rightGlobalIndex]
    omega

/-- Reconstruct an arbitrary generator-shaped vector from its left, bridge,
and right coordinate blocks. -/
theorem osiiArgumentGeneratorPoint_reconstruct
    {k : ℕ} (i : GeneratorIndex k) (y : Fin k → ℝ) :
    osiiArgumentGeneratorPoint i
        (osiiMixedArgumentOfTail i.hn
          (fun a => -y (i.leftGlobalIndex a)))
        (y i.bridgeGlobalIndex)
        (osiiMixedArgumentOfTail i.hm
          (fun b => y (i.rightGlobalIndex b))) =
      y := by
  funext j
  by_cases hjleft : j.val < i.n - 1
  · let a : Fin (i.n - 1) := ⟨j.val, hjleft⟩
    have hj :
        i.leftGlobalIndex (Fin.rev a) = j := by
      apply Fin.ext
      simpa [a] using i.leftGlobalIndex_rev_val a
    rw [← hj, osiiArgumentGeneratorPoint_left]
    simp
  · by_cases hjbridge : j = i.bridgeGlobalIndex
    · subst j
      simp
    · have hjright : i.n ≤ j.val := by
        have hbridgeVal :
            i.bridgeGlobalIndex.val = i.n - 1 := rfl
        omega
      let b : Fin (i.m - 1) :=
        ⟨j.val - i.n, by
          have hnm := i.hnm
          omega⟩
      have hj :
          i.rightGlobalIndex b = j := by
        apply Fin.ext
        change i.n + (j.val - i.n) = j.val
        omega
      rw [← hj, osiiArgumentGeneratorPoint_right]
      simp

/-- The argument vector `(-reverse v, 0, v)` occurring in `(5.24)`.

The leading coordinate of `x` is the distinguished zero. -/
def osiiArgumentDiagonal {n : ℕ}
    (hn : 1 ≤ n)
    (x : Fin n → ℝ) :
    Fin (2 * n - 1) → ℝ :=
  fun j =>
    if hleft : j.val < n - 1 then
      -x ⟨n - 1 - j.val, by omega⟩
    else
      x ⟨j.val - (n - 1), by omega⟩

/-- The split producing the first generator point on page 296. -/
def osiiFirstRecursiveAngleSplit (s t : ℕ) :
    GeneratorIndex (2 * ((t + 1) + (s + 1)) - 1) where
  n := 2 * (t + 1) + (s + 1)
  m := 1 + s
  hn := by omega
  hm := by omega
  hnm := by omega

/-- The split producing the second generator point on page 296. -/
def osiiSecondRecursiveAngleSplit (s t : ℕ) :
    GeneratorIndex (2 * ((t + 1) + (s + 1)) - 1) where
  n := 1 + s
  m := 2 * (t + 1) + (s + 1)
  hn := by omega
  hm := by omega
  hnm := by omega

/-- The first of the two offset generator points used to prove `(5.27)`. -/
def osiiFirstRecursiveAngleGeneratorPoint (N s t : ℕ) :
    Fin (2 * ((t + 1) + (s + 1)) - 1) → ℝ :=
  osiiArgumentGeneratorPoint
    (osiiFirstRecursiveAngleSplit s t)
    (osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))
    (Real.pi / 2)
    (osiiMixedAnglePoint N s 1)

/-- The second of the two offset generator points used to prove `(5.27)`. -/
def osiiSecondRecursiveAngleGeneratorPoint (N s t : ℕ) :
    Fin (2 * ((t + 1) + (s + 1)) - 1) → ℝ :=
  osiiArgumentGeneratorPoint
    (osiiSecondRecursiveAngleSplit s t)
    (osiiMixedAnglePoint N s 1)
    (-(Real.pi / 2))
    (osiiMixedAnglePoint N (s + 1) (2 * (t + 1)))

private theorem recursiveAngle_succ_eq_average_of_two_le
    (N i : ℕ) (hi : 2 ≤ i) :
    recursiveAngle i (N + 1) =
      (recursiveAngle i N + recursiveAngle (i - 1) N) / 2 := by
  calc
    recursiveAngle i (N + 1) =
        recursiveAngle ((i - 2) + 2) (N + 1) := by
          congr 1
          omega
    _ =
        (recursiveAngle ((i - 2) + 2) N +
          recursiveAngle ((i - 2) + 1) N) / 2 :=
      recursiveAngle_succ_succ (i - 2) N
    _ =
        (recursiveAngle i N + recursiveAngle (i - 1) N) / 2 := by
      have hi0 : (i - 2) + 2 = i := by omega
      have hi1 : (i - 2) + 1 = i - 1 := by omega
      rw [hi0, hi1]

/-- Coordinatewise, the midpoint of the two page-296 generator points is the
diagonal vector for `w^(N+1)(s+1,t+1)`. This is the exact finite-coordinate
content of `(5.27)`. -/
theorem osiiRecursiveAngleGenerator_midpoint_eq_diagonal
    (N s t : ℕ) :
    (fun j =>
      (osiiFirstRecursiveAngleGeneratorPoint N s t j +
        osiiSecondRecursiveAngleGeneratorPoint N s t j) / 2) =
      osiiArgumentDiagonal (by omega)
        (osiiMixedAnglePoint (N + 1) (s + 1) (t + 1)) := by
  funext j
  simp only [
    osiiFirstRecursiveAngleGeneratorPoint,
    osiiSecondRecursiveAngleGeneratorPoint,
    osiiArgumentGeneratorPoint,
    osiiArgumentDiagonal,
    osiiMixedAnglePoint
  ]
  dsimp only [osiiFirstRecursiveAngleSplit, osiiSecondRecursiveAngleSplit]
  simp! +arith
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ <;> try omega
  all_goals try norm_num
  next =>
    let r := s - j.val
    have hr : 1 ≤ r := by
      dsimp [r]
      omega
    have hA :
        s + 2 * t + 2 - j.val - (2 * t + 2) + 1 =
          r + 1 := by
      dsimp [r]
      omega
    have hB : s - j.val - 1 + 1 = r := by
      dsimp [r]
      omega
    have hC :
        s + t + 1 - j.val - (t + 1) + 1 = r + 1 := by
      dsimp [r]
      omega
    rw [hA, hB, hC,
      recursiveAngle_succ_eq_average_of_two_le N (r + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    ring
  next =>
    have hA :
        s + 2 * t + 2 - j.val - (2 * t + 2) + 1 = 1 := by
      omega
    have hC :
        s + t + 1 - j.val - (t + 1) + 1 = 1 := by
      omega
    rw [hA, hC, recursiveAngle_one_succ]
    ring
  next =>
    have hB :
        j.val - s - (2 * t + 2) + 1 = 1 := by
      omega
    have hC :
        j.val - (s + t + 1) - (t + 1) + 1 = 1 := by
      omega
    rw [hB, hC, recursiveAngle_one_succ]
    ring
  next =>
    let r := j.val - (s + 2 * t + 2)
    have hr : 1 ≤ r := by
      dsimp [r]
      omega
    have hA :
        j.val - (s + 2 * t + 2) - 1 + 1 = r := by
      dsimp [r]
      omega
    have hB :
        j.val - s - (2 * t + 2) + 1 = r + 1 := by
      dsimp [r]
      omega
    have hC :
        j.val - (s + t + 1) - (t + 1) + 1 = r + 1 := by
      dsimp [r]
      omega
    rw [hA, hB, hC,
      recursiveAngle_succ_eq_average_of_two_le N (r + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

/-- The exact geometric data from `(5.23)` and `(5.24)` needed for OS II
Lemma 5.2.

`base` is the scalar family `c_k^(N)` and `mixedBase` is the mixed family
`d_n^(N)`. The last field is the separate vacuum-pairing relation
`S_k = (Ω, Ψ_{k+1})` used by the paper to pass from part (a) to part (b). -/
structure OSIILogarithmicArgumentDomainSystem where
  base : (k N : ℕ) → Set (Fin k → ℝ)
  mixedBase : (n N : ℕ) → Set (Fin n → ℝ)
  initial_mixed_zero :
    ∀ n, (0 : Fin n → ℝ) ∈ mixedBase n 0
  base_convex :
    ∀ k N, Convex ℝ (base k N)
  mixed_hyperrectangle :
    ∀ n N {x : Fin n → ℝ},
      x ∈ mixedBase n N →
      ∀ y : Fin n → ℝ,
        (∀ i, |y i| ≤ |x i|) →
        y ∈ mixedBase n N
  generator_mem_succ :
    ∀ {k} (i : GeneratorIndex k) N
      (left : Fin i.n → ℝ) (θ : ℝ) (right : Fin i.m → ℝ),
      left ∈ mixedBase i.n N →
      right ∈ mixedBase i.m N →
      |θ| ≤ Real.pi / 2 →
      osiiArgumentGeneratorPoint i left θ right ∈ base k (N + 1)
  mixed_of_diagonal :
    ∀ n (hn : 1 ≤ n) N (x : Fin n → ℝ),
      x ⟨0, hn⟩ = 0 →
      osiiArgumentDiagonal hn x ∈ base (2 * n - 1) N →
      x ∈ mixedBase n N
  mixed_tail_mem_base :
    ∀ k N (x : Fin (k + 1) → ℝ),
      x ∈ mixedBase (k + 1) N →
      Fin.tail x ∈ base k N

namespace OSIILogarithmicArgumentDomainSystem

private theorem mixedBase_reindex
    (D : OSIILogarithmicArgumentDomainSystem)
    {n m N : ℕ} (h : n = m) {x : Fin n → ℝ}
    (hx : x ∈ D.mixedBase n N) :
    (fun j : Fin m => x ((finCongr h).symm j)) ∈
      D.mixedBase m N := by
  subst m
  simpa

private def diagonalSplit (n : ℕ) (hn : 1 ≤ n) :
    GeneratorIndex (2 * n - 1) where
  n := n
  m := n
  hn := hn
  hm := hn
  hnm := by omega

private theorem argumentGeneratorPoint_zero
    {k : ℕ} (i : GeneratorIndex k) :
    osiiArgumentGeneratorPoint i
        (0 : Fin i.n → ℝ) 0 (0 : Fin i.m → ℝ) =
      (0 : Fin k → ℝ) := by
  funext j
  simp [osiiArgumentGeneratorPoint]

private theorem argumentDiagonal_zero
    (n : ℕ) (hn : 1 ≤ n) :
    osiiArgumentDiagonal hn (0 : Fin n → ℝ) =
      (0 : Fin (2 * n - 1) → ℝ) := by
  funext j
  simp [osiiArgumentDiagonal]

/-- Every mixed logarithmic base contains its origin. This is derived from
the stage-zero condition and the zero-angle generator with the symmetric
split, rather than assumed at every stage. -/
theorem mixed_zero_mem
    (D : OSIILogarithmicArgumentDomainSystem) :
    ∀ N n, 1 ≤ n → (0 : Fin n → ℝ) ∈ D.mixedBase n N := by
  intro N
  induction N with
  | zero =>
      intro n hn
      exact D.initial_mixed_zero n
  | succ N ih =>
      intro n hn
      apply D.mixed_of_diagonal n hn (N + 1)
      · rfl
      rw [argumentDiagonal_zero n hn]
      rw [← argumentGeneratorPoint_zero (diagonalSplit n hn)]
      apply D.generator_mem_succ (diagonalSplit n hn) N
      · exact ih n hn
      · exact ih n hn
      · simp
        positivity

/-- The distinguished positive point `w^N(s,t)` belongs to `d_(s+t)^N`
for every `t ≥ 1`. The successor proof is exactly the two-generator
midpoint argument on page 296. -/
theorem mixedAnglePoint_mem
    (D : OSIILogarithmicArgumentDomainSystem) :
    ∀ N s t,
      osiiMixedAnglePoint N s (t + 1) ∈
        D.mixedBase ((t + 1) + s) N := by
  intro N
  induction N with
  | zero =>
      intro s t
      have hzero :
          osiiMixedAnglePoint 0 s (t + 1) =
            (0 : Fin ((t + 1) + s) → ℝ) := by
        funext j
        simp [osiiMixedAnglePoint]
      rw [hzero]
      exact D.initial_mixed_zero _
  | succ N ih =>
      intro s t
      cases s with
      | zero =>
          have hzero :
              osiiMixedAnglePoint (N + 1) 0 (t + 1) =
                (0 : Fin ((t + 1) + 0) → ℝ) := by
            funext j
            simp [osiiMixedAnglePoint]
            omega
          rw [hzero]
          exact D.mixed_zero_mem (N + 1) (t + 1) (by omega)
      | succ s =>
          have hleftLarge :
              osiiMixedAnglePoint N (s + 1) (2 * (t + 1)) ∈
                D.mixedBase (2 * (t + 1) + (s + 1)) N := by
            rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]
            exact ih (s + 1) (2 * t + 1)
          have hsmall :
              osiiMixedAnglePoint N s 1 ∈
                D.mixedBase (1 + s) N :=
            ih s 0
          have hfirst :
              osiiFirstRecursiveAngleGeneratorPoint N s t ∈
                D.base (2 * ((t + 1) + (s + 1)) - 1) (N + 1) := by
            apply D.generator_mem_succ
                (osiiFirstRecursiveAngleSplit s t) N
            · exact hleftLarge
            · exact hsmall
            · rw [abs_of_nonneg (by positivity)]
          have hsecond :
              osiiSecondRecursiveAngleGeneratorPoint N s t ∈
                D.base (2 * ((t + 1) + (s + 1)) - 1) (N + 1) := by
            apply D.generator_mem_succ
                (osiiSecondRecursiveAngleSplit s t) N
            · exact hsmall
            · exact hleftLarge
            · rw [abs_neg, abs_of_nonneg (by positivity)]
          have hmid :=
            (D.base_convex
              (2 * ((t + 1) + (s + 1)) - 1) (N + 1)
              ).midpoint_mem hfirst hsecond
          apply D.mixed_of_diagonal
              ((t + 1) + (s + 1)) (by omega) (N + 1)
          · simp [osiiMixedAnglePoint]
          rw [← osiiRecursiveAngleGenerator_midpoint_eq_diagonal N s t]
          have hpointwise :
              midpoint ℝ
                  (osiiFirstRecursiveAngleGeneratorPoint N s t)
                  (osiiSecondRecursiveAngleGeneratorPoint N s t) =
                fun j =>
                  (osiiFirstRecursiveAngleGeneratorPoint N s t j +
                    osiiSecondRecursiveAngleGeneratorPoint N s t j) / 2 := by
            rw [midpoint_eq_smul_add]
            ext j
            simp only [
              Pi.smul_apply, Pi.add_apply, invOf_eq_inv, smul_eq_mul
            ]
            ring
          rwa [hpointwise] at hmid

/-- The exact recursive-angle closed box lies in the scalar logarithmic base
`c_k^(N)`. Unlike the former prepend-only abstraction, this theorem is
derived from the mixed domains and the genuine `(5.23)`/`(5.24)` geometry. -/
theorem recursiveAngle_box_subset
    (D : OSIILogarithmicArgumentDomainSystem)
    (N k : ℕ) :
    osiiClosedArgumentBox (osiiRecursiveAngleAperture k N) ⊆
      D.base k N := by
  intro x hx
  let y : Fin (k + 1) → ℝ := Fin.cons 0 x
  have hcornerRaw := D.mixedAnglePoint_mem N k 0
  have hcard : 1 + k = k + 1 := by omega
  let corner : Fin (k + 1) → ℝ :=
    fun j =>
      osiiMixedAnglePoint N k 1 ((finCongr hcard).symm j)
  have hcorner :
      corner ∈ D.mixedBase (k + 1) N := by
    exact D.mixedBase_reindex hcard hcornerRaw
  have hy : y ∈ D.mixedBase (k + 1) N := by
    apply D.mixed_hyperrectangle (k + 1) N hcorner y
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [y, corner, osiiMixedAnglePoint]
    · simpa [y, corner, osiiMixedAnglePoint,
        osiiRecursiveAngleAperture,
        abs_of_nonneg (recursiveAngle_nonneg (j.val + 1) N)] using
        hx j
  have htail := D.mixed_tail_mem_base k N y hy
  simpa [y] using htail

end OSIILogarithmicArgumentDomainSystem

end OSIIChapterV
end OSReconstruction
