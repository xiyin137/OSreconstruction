/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicArgumentDomains























noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Whether a generated logarithmic argument belongs to a scalar continuation
base or to a mixed Hilbert-vector base. -/
inductive OSIILogarithmicArgumentKind where
  | scalar
  | mixed
  deriving DecidableEq

/-- The least simultaneous scalar/mixed logarithmic-domain closure generated
by the operations in OS II equations `(5.23)` and `(5.24)`. -/
inductive OSIIGeneratedLogarithmicArgument :
    OSIILogarithmicArgumentKind →
      (n N : ℕ) → (Fin n → ℝ) → Prop where
  | initialMixedZero (n : ℕ) :
      OSIIGeneratedLogarithmicArgument
        .mixed n 0 (0 : Fin n → ℝ)
  | scalarConvex
      {k N : ℕ} {x y : Fin k → ℝ}
      (hx : OSIIGeneratedLogarithmicArgument .scalar k N x)
      (hy : OSIIGeneratedLogarithmicArgument .scalar k N y)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      OSIIGeneratedLogarithmicArgument
        .scalar k N (a • x + b • y)
  | mixedHyperrectangle
      {n N : ℕ} {x : Fin n → ℝ}
      (hx : OSIIGeneratedLogarithmicArgument .mixed n N x)
      (y : Fin n → ℝ)
      (hy : ∀ i, |y i| ≤ |x i|) :
      OSIIGeneratedLogarithmicArgument .mixed n N y
  | generatorMemSucc
      {k : ℕ} (i : GeneratorIndex k) (N : ℕ)
      (left : Fin i.n → ℝ) (θ : ℝ) (right : Fin i.m → ℝ)
      (hleft :
        OSIIGeneratedLogarithmicArgument .mixed i.n N left)
      (hright :
        OSIIGeneratedLogarithmicArgument .mixed i.m N right)
      (hθ : |θ| ≤ Real.pi / 2) :
      OSIIGeneratedLogarithmicArgument .scalar k (N + 1)
        (osiiArgumentGeneratorPoint i left θ right)
  | mixedOfDiagonal
      (n : ℕ) (hn : 1 ≤ n) (N : ℕ) (x : Fin n → ℝ)
      (hx0 : x ⟨0, hn⟩ = 0)
      (hx :
        OSIIGeneratedLogarithmicArgument .scalar (2 * n - 1) N
          (osiiArgumentDiagonal hn x)) :
      OSIIGeneratedLogarithmicArgument .mixed n N x
  | mixedTailMemScalar
      (k N : ℕ) (x : Fin (k + 1) → ℝ)
      (hx :
        OSIIGeneratedLogarithmicArgument .mixed (k + 1) N x) :
      OSIIGeneratedLogarithmicArgument .scalar k N (Fin.tail x)

/-- The canonical scalar base `c_k^(N)`. -/
def osiiGeneratedLogarithmicBase (k N : ℕ) :
    Set (Fin k → ℝ) :=
  {x | OSIIGeneratedLogarithmicArgument .scalar k N x}

/-- The canonical mixed base `d_n^(N)`. -/
def osiiGeneratedMixedLogarithmicBase (n N : ℕ) :
    Set (Fin n → ℝ) :=
  {x | OSIIGeneratedLogarithmicArgument .mixed n N x}

/-- The least generated closure is an
`OSIILogarithmicArgumentDomainSystem`. -/
def osiiGeneratedLogarithmicArgumentDomainSystem :
    OSIILogarithmicArgumentDomainSystem where
  base := osiiGeneratedLogarithmicBase
  mixedBase := osiiGeneratedMixedLogarithmicBase
  initial_mixed_zero := fun n =>
    OSIIGeneratedLogarithmicArgument.initialMixedZero n
  base_convex := by
    intro k N x hx y hy a b ha hb hab
    exact
      OSIIGeneratedLogarithmicArgument.scalarConvex
        hx hy a b ha hb hab
  mixed_hyperrectangle := by
    intro n N x hx y hy
    exact
      OSIIGeneratedLogarithmicArgument.mixedHyperrectangle hx y hy
  generator_mem_succ := by
    intro k i N left θ right hleft hright hθ
    exact
      OSIIGeneratedLogarithmicArgument.generatorMemSucc
        i N left θ right hleft hright hθ
  mixed_of_diagonal := by
    intro n hn N x hx0 hx
    exact
      OSIIGeneratedLogarithmicArgument.mixedOfDiagonal
        n hn N x hx0 hx
  mixed_tail_mem_base := by
    intro k N x hx
    exact
      OSIIGeneratedLogarithmicArgument.mixedTailMemScalar
        k N x hx

namespace OSIIGeneratedLogarithmicArgument

/-- At induction depth zero, every generated scalar or mixed argument is the
origin.  The generator constructor cannot occur because it always raises the
depth. -/
theorem eq_zero_of_stage_zero
    {kind : OSIILogarithmicArgumentKind}
    {n : ℕ} {x : Fin n → ℝ}
    (hx : OSIIGeneratedLogarithmicArgument kind n 0 x) :
    x = 0 := by
  generalize hN : (0 : ℕ) = N at hx
  induction hx with
  | initialMixedZero n =>
      rfl
  | scalarConvex hx hy a b ha hb hab ihx ihy =>
      rw [ihx hN, ihy hN, smul_zero, smul_zero, add_zero]
  | mixedHyperrectangle hx y hy ih =>
      funext i
      have hbound : |y i| ≤ 0 := by
        simpa [ih hN] using hy i
      exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  | generatorMemSucc i N left θ right hleft hright hθ ihleft ihright =>
      omega
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      funext i
      let j : Fin (2 * n - 1) :=
        ⟨n - 1 + i.val, by omega⟩
      have hj := congrFun (ih hN) j
      simpa [j, osiiArgumentDiagonal] using hj
  | mixedTailMemScalar k N x hx ih =>
      rw [ih hN]
      rfl

private theorem mixed_head_eq_zero_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : ℕ} {x : Fin n → ℝ}
    (hx : OSIIGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar => True
    | .mixed => ∀ hn : 1 ≤ n, x ⟨0, hn⟩ = 0 := by
  induction hx with
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
  | generatorMemSucc i N left θ right hleft hright hθ ihleft ihright =>
      trivial
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro _
      exact hx0
  | mixedTailMemScalar k N x hx ih =>
      trivial

/-- Every generated mixed argument has the distinguished leading zero used by
the Chapter V Hilbert-vector domains.  The actual analytic variables are its
`n - 1` tail coordinates. -/
theorem mixed_head_eq_zero
    {n N : ℕ} {x : Fin n → ℝ}
    (hn : 1 ≤ n)
    (hx : OSIIGeneratedLogarithmicArgument .mixed n N x) :
    x ⟨0, hn⟩ = 0 :=
  mixed_head_eq_zero_aux hx hn

private theorem coordinatewise_closed_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : ℕ} {x : Fin n → ℝ}
    (hx : OSIIGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar =>
        ∀ y : Fin n → ℝ,
          (∀ i, |y i| ≤ |x i|) →
          OSIIGeneratedLogarithmicArgument .scalar n N y
    | .mixed => True := by
  induction hx with
  | initialMixedZero n =>
      trivial
  | @scalarConvex k N x y hx hy a b ha hb hab ihx ihy =>
      intro z hz
      let c : Fin k → ℝ := fun i => a * x i + b * y i
      let ratio : Fin k → ℝ :=
        fun i => if c i = 0 then 0 else z i / c i
      have hz_c : ∀ i, |z i| ≤ |c i| := by
        intro i
        simpa [c] using hz i
      have hratio : ∀ i, |ratio i| ≤ 1 := by
        intro i
        by_cases hci : c i = 0
        · simp [ratio, hci]
        · have hcpos : 0 < |c i| := abs_pos.mpr hci
          simp only [ratio, hci, ↓reduceIte, abs_div]
          exact (div_le_one hcpos).2 (hz_c i)
      have hx' :
          OSIIGeneratedLogarithmicArgument .scalar k N
            (fun i => ratio i * x i) := by
        apply ihx
        intro i
        rw [abs_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hratio i) (abs_nonneg (x i))).trans_eq (one_mul _)
      have hy' :
          OSIIGeneratedLogarithmicArgument .scalar k N
            (fun i => ratio i * y i) := by
        apply ihy
        intro i
        rw [abs_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hratio i) (abs_nonneg (y i))).trans_eq (one_mul _)
      have hratio_c : ∀ i, ratio i * c i = z i := by
        intro i
        by_cases hci : c i = 0
        · have hzi_abs : |z i| = 0 :=
            le_antisymm (by simpa [hci] using hz_c i) (abs_nonneg _)
          have hzi : z i = 0 := abs_eq_zero.mp hzi_abs
          simp [ratio, hci, hzi]
        · simp [ratio, hci]
      have hcomb :=
        OSIIGeneratedLogarithmicArgument.scalarConvex
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
  | generatorMemSucc i N left θ right hleft hright hθ ihleft ihright =>
      intro y hy
      let left' : Fin i.n → ℝ :=
        osiiMixedArgumentOfTail i.hn
          (fun a => -y (i.leftGlobalIndex a))
      let right' : Fin i.m → ℝ :=
        osiiMixedArgumentOfTail i.hm
          (fun b => y (i.rightGlobalIndex b))
      have hleft' :
          OSIIGeneratedLogarithmicArgument .mixed i.n N left' := by
        apply OSIIGeneratedLogarithmicArgument.mixedHyperrectangle
          hleft left'
        apply abs_osiiMixedArgumentOfTail_le i.hn
          (mixed_head_eq_zero i.hn hleft)
        intro a
        simpa [left'] using hy (i.leftGlobalIndex a)
      have hright' :
          OSIIGeneratedLogarithmicArgument .mixed i.m N right' := by
        apply OSIIGeneratedLogarithmicArgument.mixedHyperrectangle
          hright right'
        apply abs_osiiMixedArgumentOfTail_le i.hm
          (mixed_head_eq_zero i.hm hright)
        intro b
        simpa [right'] using hy (i.rightGlobalIndex b)
      have hθ' : |y i.bridgeGlobalIndex| ≤ Real.pi / 2 := by
        have hbridge :
            |y i.bridgeGlobalIndex| ≤ |θ| := by
          simpa using hy i.bridgeGlobalIndex
        exact hbridge.trans hθ
      have hgen :=
        OSIIGeneratedLogarithmicArgument.generatorMemSucc
          i N left' (y i.bridgeGlobalIndex) right'
          hleft' hright' hθ'
      simpa [left', right', osiiArgumentGeneratorPoint_reconstruct] using hgen
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      trivial
  | mixedTailMemScalar k N x hx ih =>
      intro y hy
      let x' : Fin (k + 1) → ℝ := Fin.cons 0 y
      have hx' :
          OSIIGeneratedLogarithmicArgument .mixed (k + 1) N x' := by
        apply OSIIGeneratedLogarithmicArgument.mixedHyperrectangle hx x'
        intro j
        refine Fin.cases ?_ (fun a => ?_) j
        · have hk1 : 1 ≤ k + 1 := by omega
          have hx0 := mixed_head_eq_zero hk1 hx
          simpa [x'] using congrArg abs hx0.symm
        · simpa [x', Fin.tail_def] using hy a
      have htail :=
        OSIIGeneratedLogarithmicArgument.mixedTailMemScalar
          k N x' hx'
      simpa [x'] using htail

/-- The canonical generated scalar base is closed under coordinatewise
shrinking of absolute values. -/
theorem scalar_hyperrectangle
    {n N : ℕ} {x : Fin n → ℝ}
    (hx :
      OSIIGeneratedLogarithmicArgument .scalar n N x)
    (y : Fin n → ℝ)
    (hy : ∀ i, |y i| ≤ |x i|) :
    OSIIGeneratedLogarithmicArgument .scalar n N y :=
  coordinatewise_closed_aux hx y hy

private theorem mixed_diagonal_mem_scalar_aux
    {kind : OSIILogarithmicArgumentKind}
    {n N : ℕ} {x : Fin n → ℝ}
    (hx : OSIIGeneratedLogarithmicArgument kind n N x) :
    match kind with
    | .scalar => True
    | .mixed =>
        ∀ hn : 1 ≤ n,
          OSIIGeneratedLogarithmicArgument .scalar (2 * n - 1) N
            (osiiArgumentDiagonal hn x) := by
  induction hx with
  | initialMixedZero n =>
      intro hn
      have hzero :
          OSIIGeneratedLogarithmicArgument .scalar (2 * n - 1) 0
            (0 : Fin (2 * n - 1) → ℝ) := by
        exact
          OSIIGeneratedLogarithmicArgument.mixedTailMemScalar
            (2 * n - 1) 0
            (0 : Fin ((2 * n - 1) + 1) → ℝ)
            (OSIIGeneratedLogarithmicArgument.initialMixedZero
              ((2 * n - 1) + 1))
      have hdiag :
          osiiArgumentDiagonal hn (0 : Fin n → ℝ) =
            (0 : Fin (2 * n - 1) → ℝ) := by
        funext j
        simp [osiiArgumentDiagonal]
      rw [hdiag]
      exact hzero
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
  | generatorMemSucc i N left θ right hleft hright hθ ihleft ihright =>
      trivial
  | mixedOfDiagonal n hn N x hx0 hx ih =>
      intro hn'
      simpa using hx
  | mixedTailMemScalar k N x hx ih =>
      trivial

/-- The reflected diagonal of every canonical generated mixed argument lies
in the scalar generated base at the same depth. -/
theorem mixed_diagonal_mem_scalar
    {n N : ℕ} {x : Fin n → ℝ}
    (hn : 1 ≤ n)
    (hx :
      OSIIGeneratedLogarithmicArgument .mixed n N x) :
    OSIIGeneratedLogarithmicArgument .scalar (2 * n - 1) N
      (osiiArgumentDiagonal hn x) :=
  mixed_diagonal_mem_scalar_aux hx hn

/-- Every canonical generated scalar base contains its origin at every
depth. -/
theorem scalar_zero_mem
    (n N : ℕ) :
    OSIIGeneratedLogarithmicArgument .scalar n N
      (0 : Fin n → ℝ) := by
  have hmixed :
      OSIIGeneratedLogarithmicArgument .mixed (n + 1) N
        (0 : Fin (n + 1) → ℝ) := by
    exact
      osiiGeneratedLogarithmicArgumentDomainSystem.mixed_zero_mem
        N (n + 1) (by omega)
  have htail :=
    OSIIGeneratedLogarithmicArgument.mixedTailMemScalar
      n N (0 : Fin (n + 1) → ℝ) hmixed
  convert htail using 1
  funext i
  simp [Fin.tail_def]

end OSIIGeneratedLogarithmicArgument

/-- The canonical scalar base at depth zero is exactly the origin. -/
theorem osiiGeneratedLogarithmicBase_zero (k : ℕ) :
    osiiGeneratedLogarithmicBase k 0 =
      ({0} : Set (Fin k → ℝ)) := by
  ext x
  constructor
  · intro hx
    exact Set.mem_singleton_iff.mpr hx.eq_zero_of_stage_zero
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact
      OSIIGeneratedLogarithmicArgument.mixedTailMemScalar
        k 0 (0 : Fin (k + 1) → ℝ)
        (OSIIGeneratedLogarithmicArgument.initialMixedZero (k + 1))

end OSIIChapterV
end OSReconstruction
