import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import Mathlib.Analysis.LocallyConvex.WithSeminorms

set_option backward.isDefEq.respectTransparency false

/-!
# Finite-seminorm bounds from ordinary Euclidean continuity

At each fixed arity, E0 continuity bounds the Schwinger functional by a finite
family of ambient Schwartz seminorms restricted to its actual zero-diagonal
domain. No extension to the full Schwartz space or uniform-in-arity growth
hypothesis is required.
-/

noncomputable section

open scoped Classical

namespace OSReconstruction

/-- Ordinary E0 continuity gives a finite Schwartz-seminorm bound directly on
the zero-diagonal test space. -/
theorem exists_zeroDiagonalSchwinger_finsetSeminormBound
    {d : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (n : Nat) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 ≤ C ∧
      ∀ f : ZeroDiagonalSchwartz d n,
        ‖OS.S n f‖ ≤
          C * s.sup
            (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 := by
  let L : ZeroDiagonalSchwartz d n →L[Complex] Complex :=
    OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n
  let p : SeminormFamily Complex
      ↥(zeroDiagonalSubmodule d n) (Nat × Nat) :=
    (schwartzSeminormFamily Complex (NPointDomain d n) Complex).comp
      (zeroDiagonalSubmodule d n).subtype
  let q : Seminorm Complex ↥(zeroDiagonalSubmodule d n) :=
    (normSeminorm Complex Complex).comp L.toLinearMap
  have hp : WithSeminorms p :=
    Topology.IsInducing.withSeminorms
      (schwartz_withSeminorms
        (𝕜 := Complex) (E := NPointDomain d n) (F := Complex))
      Topology.IsInducing.subtypeVal
  have hq : Continuous q := by
    change Continuous fun f : ↥(zeroDiagonalSubmodule d n) => ‖L f‖
    exact continuous_norm.comp L.continuous
  obtain ⟨s, C, _hC_ne, hbound⟩ :=
    Seminorm.bound_of_continuous hp q hq
  refine ⟨s, (C : Real), C.2, fun f => ?_⟩
  calc
    ‖OS.S n f‖ = q f := rfl
    _ ≤ (C • s.sup p) f := hbound f
    _ = (C : Real) *
        s.sup
          (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 := by
      change (C : Real) * (s.sup p) f = _
      congr 1
      change
        (s.sup
          ((schwartzSeminormFamily Complex (NPointDomain d n) Complex).comp
            (zeroDiagonalSubmodule d n).subtype)) f = _
      rw [← SeminormFamily.finset_sup_comp]
      rfl

/-- Ordinary E0 controls every point arity in one prescribed finite range by
the same finite Schwartz-seminorm indices and numerical coefficient. -/
theorem exists_zeroDiagonalSchwinger_boundedArity_finsetSeminormBound
    {d : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (N : Nat) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 ≤ C ∧
      ∀ (n : Nat), n ≤ N → ∀ f : ZeroDiagonalSchwartz d n,
        ‖OS.S n f‖ ≤
          C * s.sup
            (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 := by
  choose sourceIndices sourceConstant sourceConstant_nonneg sourceBound using
    fun n : Nat => exists_zeroDiagonalSchwinger_finsetSeminormBound OS n
  let arities : Finset Nat := Finset.range (N + 1)
  let indices : Finset (Nat × Nat) := arities.biUnion sourceIndices
  let C : Real := arities.sum sourceConstant
  have hC : 0 ≤ C := by
    exact Finset.sum_nonneg fun n _ => sourceConstant_nonneg n
  refine ⟨indices, C, hC, ?_⟩
  intro n hn f
  have hn_mem : n ∈ arities := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
  have hcoefficient : sourceConstant n ≤ C := by
    exact Finset.single_le_sum
      (fun m _ => sourceConstant_nonneg m) hn_mem
  have hseminorm :
      (sourceIndices n).sup
          (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 ≤
        indices.sup
          (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 := by
    apply Seminorm.finset_sup_apply_le
    · exact apply_nonneg _ _
    intro i hi
    apply Seminorm.le_finset_sup_apply
    exact Finset.mem_biUnion.mpr ⟨n, hn_mem, hi⟩
  calc
    ‖OS.S n f‖ ≤
        sourceConstant n * (sourceIndices n).sup
          (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 :=
      sourceBound n f
    _ ≤ C * indices.sup
          (schwartzSeminormFamily Complex (NPointDomain d n) Complex) f.1 :=
      mul_le_mul hcoefficient hseminorm (apply_nonneg _ _) hC

/-- At fixed positive gap arity, one ordinary-E0 bound controls all genuine
reflected norm-square point arities `2*r`, without an arity-growth hypothesis. -/
theorem exists_zeroDiagonalSchwinger_evenArity_finsetSeminormBound
    {d : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (k : Nat) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 ≤ C ∧
      ∀ (r : Nat), r ≤ k → ∀ f : ZeroDiagonalSchwartz d (2 * r),
        ‖OS.S (2 * r) f‖ ≤
          C * s.sup
            (schwartzSeminormFamily Complex
              (NPointDomain d (2 * r)) Complex) f.1 := by
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_zeroDiagonalSchwinger_boundedArity_finsetSeminormBound OS (2 * k)
  refine ⟨s, C, hC, ?_⟩
  intro r hr f
  exact hbound (2 * r) (Nat.mul_le_mul_left 2 hr) f

end OSReconstruction
