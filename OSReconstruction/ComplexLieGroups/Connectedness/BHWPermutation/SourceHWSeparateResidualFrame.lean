import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWLowRankNormalForm
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFinal

/-!
# Separate residual-frame singular contraction

The common-frame low-rank normal form is convenient when a determinant-one
residual correction has already put both residual families in the same
maximal isotropic frame.  The singular-limit API itself only needs two orbit
curves converging to the same selected base, so this file provides the
critical-path separate-frame variant.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Separate left and right maximal isotropic residual frames after the
selected-span alignment.

This data is enough to build two determinant-one null-boost contractions to
the same selected base `A.ξ`; no determinant-one map between the two residual
maximal isotropic frames is required. -/
structure HWLowRankSeparateResidualFrameData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) where
  sLeft : ℕ
  qLeft : Fin sLeft → Fin (d + 1) → ℂ
  sRight : ℕ
  qRight : Fin sRight → Fin (d + 1) → ℂ
  left_span :
    ∀ i, A.leftResidual i ∈ Submodule.span ℂ (Set.range qLeft)
  right_span :
    ∀ i, A.rightResidual i ∈ Submodule.span ℂ (Set.range qRight)
  qLeft_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (qLeft c) (qLeft c') = 0
  qRight_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (qRight c) (qRight c') = 0
  qLeft_orth_M :
    ∀ c (m : A.M),
      sourceComplexMinkowskiInner d (qLeft c)
        (m : Fin (d + 1) → ℂ) = 0
  qRight_orth_M :
    ∀ c (m : A.M),
      sourceComplexMinkowskiInner d (qRight c)
        (m : Fin (d + 1) → ℂ) = 0
  qLeft_independent : LinearIndependent ℂ qLeft
  qRight_independent : LinearIndependent ℂ qRight

/-- The checked maximal-isotropic extension theorem supplies separate maximal
frames containing the left and right residual spans. -/
noncomputable def hw_lowRank_separateResidualFrameData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    HWLowRankSeparateResidualFrameData A := by
  classical
  let hSubspaces :=
    hw_lowRank_residualSubspaces_orthogonalComplement_after_selectedAlignment
      (d := d) (n := n) (r := r) (z := z) (w := w)
      (I := I) (S := S) A
  let Rleft : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Classical.choose hSubspaces
  let hSubspacesRight := Classical.choose_spec hSubspaces
  let Rright : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Classical.choose hSubspacesRight
  have hSpec := Classical.choose_spec hSubspacesRight
  have hRleft_eq :
      Rleft = Submodule.span ℂ (Set.range A.leftResidual) := hSpec.1
  have hRright_eq :
      Rright = Submodule.span ℂ (Set.range A.rightResidual) := hSpec.2.1
  have hRleft_le :
      Rleft ≤ complexMinkowskiOrthogonalSubmodule d A.M := hSpec.2.2.1
  have hRright_le :
      Rright ≤ complexMinkowskiOrthogonalSubmodule d A.M := hSpec.2.2.2.1
  have hRleft_iso : ComplexMinkowskiTotallyIsotropicSubspace d Rleft :=
    hSpec.2.2.2.2.2.2.1
  have hRright_iso : ComplexMinkowskiTotallyIsotropicSubspace d Rright :=
    hSpec.2.2.2.2.2.2.2
  let N : Submodule ℂ (Fin (d + 1) → ℂ) :=
    complexMinkowskiOrthogonalSubmodule d A.M
  let hFleftExists :=
    complexMinkowski_maximalIsotropicFrameIn_extending
      (d := d) (N := N) (R := Rleft) hRleft_le hRleft_iso
  let Fleft : ComplexMinkowskiMaximalIsotropicFrameIn d N :=
    Classical.choose hFleftExists
  have hRleft_span : Rleft ≤ Submodule.span ℂ (Set.range Fleft.q) :=
    Classical.choose_spec hFleftExists
  let hFrightExists :=
    complexMinkowski_maximalIsotropicFrameIn_extending
      (d := d) (N := N) (R := Rright) hRright_le hRright_iso
  let Fright : ComplexMinkowskiMaximalIsotropicFrameIn d N :=
    Classical.choose hFrightExists
  have hRright_span : Rright ≤ Submodule.span ℂ (Set.range Fright.q) :=
    Classical.choose_spec hFrightExists
  refine
    { sLeft := Fleft.s
      qLeft := Fleft.q
      sRight := Fright.s
      qRight := Fright.q
      left_span := ?_
      right_span := ?_
      qLeft_pair_zero := Fleft.q_pair_zero
      qRight_pair_zero := Fright.q_pair_zero
      qLeft_orth_M := ?_
      qRight_orth_M := ?_
      qLeft_independent := Fleft.q_independent
      qRight_independent := Fright.q_independent }
  · intro i
    have hi : A.leftResidual i ∈ Rleft := by
      simpa [hRleft_eq] using
        (Submodule.subset_span (R := ℂ) ⟨i, rfl⟩ :
          A.leftResidual i ∈
            Submodule.span ℂ (Set.range A.leftResidual))
    exact hRleft_span hi
  · intro i
    have hi : A.rightResidual i ∈ Rright := by
      simpa [hRright_eq] using
        (Submodule.subset_span (R := ℂ) ⟨i, rfl⟩ :
          A.rightResidual i ∈
            Submodule.span ℂ (Set.range A.rightResidual))
    exact hRright_span hi
  · intro c m
    exact
      (mem_complexMinkowskiOrthogonalSubmodule_iff d A.M (Fleft.q c)).1
        (by simpa [N] using Fleft.q_mem c) m
  · intro c m
    exact
      (mem_complexMinkowskiOrthogonalSubmodule_iff d A.M (Fright.q c)).1
        (by simpa [N] using Fright.q_mem c) m

/-- Separate residual frames produce the two orbit curves required by the
singular-contraction API. -/
noncomputable def hw_sameSourceGram_singular_contractionData_of_separateFrameData
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S)
    (D : HWLowRankSeparateResidualFrameData A) :
    HWSameSourceGramSingularContractionData d n z w := by
  classical
  let hLeftCoeff :=
    coefficients_of_family_mem_span_finite_frame
      (d := d) (n := n) (s := D.sLeft) (q := D.qLeft)
      (v := A.leftResidual) D.left_span
  let aLeft : Fin n → Fin D.sLeft → ℂ := Classical.choose hLeftCoeff
  have h_aLeft :
      ∀ i, A.leftResidual i =
        ∑ c : Fin D.sLeft, aLeft i c • D.qLeft c :=
    Classical.choose_spec hLeftCoeff
  let hRightCoeff :=
    coefficients_of_family_mem_span_finite_frame
      (d := d) (n := n) (s := D.sRight) (q := D.qRight)
      (v := A.rightResidual) D.right_span
  let aRight : Fin n → Fin D.sRight → ℂ := Classical.choose hRightCoeff
  have h_aRight :
      ∀ i, A.rightResidual i =
        ∑ c : Fin D.sRight, aRight i c • D.qRight c :=
    Classical.choose_spec hRightCoeff
  let hLeftDualExists :=
    complexMinkowski_isotropicDualFrame_of_residualFrame
      (d := d) (n := n) (s := D.sLeft) (ξ := A.ξ)
      (q := D.qLeft) (M := A.M)
      A.M_nondeg A.ξ_mem D.qLeft_orth_M D.qLeft_pair_zero
      D.qLeft_independent
  let qLeftDual : Fin D.sLeft → Fin (d + 1) → ℂ :=
    Classical.choose hLeftDualExists
  have hLeftDualSpec := Classical.choose_spec hLeftDualExists
  have hqLeftDual_pair_zero :
      ∀ c c',
        sourceComplexMinkowskiInner d (qLeftDual c) (qLeftDual c') = 0 :=
    hLeftDualSpec.1
  have hqLeft_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (D.qLeft c) (qLeftDual c') =
          if c = c' then (1 : ℂ) else 0 :=
    hLeftDualSpec.2.1
  have hqLeftDual_orth_M :
      ∀ c (m : A.M),
        sourceComplexMinkowskiInner d (qLeftDual c)
          (m : Fin (d + 1) → ℂ) = 0 :=
    hLeftDualSpec.2.2.1
  have hqLeftDual_orth_ξ :
      ∀ c i, sourceComplexMinkowskiInner d (qLeftDual c) (A.ξ i) = 0 :=
    hLeftDualSpec.2.2.2
  let hRightDualExists :=
    complexMinkowski_isotropicDualFrame_of_residualFrame
      (d := d) (n := n) (s := D.sRight) (ξ := A.ξ)
      (q := D.qRight) (M := A.M)
      A.M_nondeg A.ξ_mem D.qRight_orth_M D.qRight_pair_zero
      D.qRight_independent
  let qRightDual : Fin D.sRight → Fin (d + 1) → ℂ :=
    Classical.choose hRightDualExists
  have hRightDualSpec := Classical.choose_spec hRightDualExists
  have hqRightDual_pair_zero :
      ∀ c c',
        sourceComplexMinkowskiInner d (qRightDual c) (qRightDual c') = 0 :=
    hRightDualSpec.1
  have hqRight_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (D.qRight c) (qRightDual c') =
          if c = c' then (1 : ℂ) else 0 :=
    hRightDualSpec.2.1
  have hqRightDual_orth_M :
      ∀ c (m : A.M),
        sourceComplexMinkowskiInner d (qRightDual c)
          (m : Fin (d + 1) → ℂ) = 0 :=
    hRightDualSpec.2.2.1
  have hqRightDual_orth_ξ :
      ∀ c i, sourceComplexMinkowskiInner d (qRightDual c) (A.ξ i) = 0 :=
    hRightDualSpec.2.2.2
  let contractLeft : ℝ → ComplexLorentzGroup d := fun t =>
    complexMinkowski_selectedHyperbolicContractionFamily
      (d := d) (s := D.sLeft) (M := A.M)
      (q := D.qLeft) (qDual := qLeftDual)
      A.M_nondeg D.qLeft_orth_M hqLeftDual_orth_M
      D.qLeft_pair_zero hqLeftDual_pair_zero hqLeft_dual t
  let contractRight : ℝ → ComplexLorentzGroup d := fun t =>
    complexMinkowski_selectedHyperbolicContractionFamily
      (d := d) (s := D.sRight) (M := A.M)
      (q := D.qRight) (qDual := qRightDual)
      A.M_nondeg D.qRight_orth_M hqRightDual_orth_M
      D.qRight_pair_zero hqRightDual_pair_zero hqRight_dual t
  have hcontractLeft_fix_ξ :
      ∀ t i, complexLorentzVectorAction (contractLeft t) (A.ξ i) = A.ξ i := by
    intro t i
    simpa [contractLeft] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_M
        (d := d) (s := D.sLeft) (M := A.M)
        (q := D.qLeft) (qDual := qLeftDual)
        A.M_nondeg D.qLeft_orth_M hqLeftDual_orth_M
        D.qLeft_pair_zero hqLeftDual_pair_zero hqLeft_dual
        t ⟨A.ξ i, A.ξ_mem i⟩
  have hcontractRight_fix_ξ :
      ∀ t i, complexLorentzVectorAction (contractRight t) (A.ξ i) = A.ξ i := by
    intro t i
    simpa [contractRight] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_M
        (d := d) (s := D.sRight) (M := A.M)
        (q := D.qRight) (qDual := qRightDual)
        A.M_nondeg D.qRight_orth_M hqRightDual_orth_M
        D.qRight_pair_zero hqRightDual_pair_zero hqRight_dual
        t ⟨A.ξ i, A.ξ_mem i⟩
  have hcontractLeft_scale_q :
      ∀ t c,
        complexLorentzVectorAction (contractLeft t) (D.qLeft c) =
          ((Real.exp (-t) : ℝ) : ℂ) • D.qLeft c := by
    intro t c
    simpa [contractLeft] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_q
        (d := d) (s := D.sLeft) (M := A.M)
        (q := D.qLeft) (qDual := qLeftDual)
        A.M_nondeg D.qLeft_orth_M hqLeftDual_orth_M
        D.qLeft_pair_zero hqLeftDual_pair_zero hqLeft_dual t c
  have hcontractRight_scale_q :
      ∀ t c,
        complexLorentzVectorAction (contractRight t) (D.qRight c) =
          ((Real.exp (-t) : ℝ) : ℂ) • D.qRight c := by
    intro t c
    simpa [contractRight] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_q
        (d := d) (s := D.sRight) (M := A.M)
        (q := D.qRight) (qDual := qRightDual)
        A.M_nondeg D.qRight_orth_M hqRightDual_orth_M
        D.qRight_pair_zero hqRightDual_pair_zero hqRight_dual t c
  have hqLeft_orth_ξ :
      ∀ c i, sourceComplexMinkowskiInner d (D.qLeft c) (A.ξ i) = 0 := by
    intro c i
    exact D.qLeft_orth_M c ⟨A.ξ i, A.ξ_mem i⟩
  have hqRight_orth_ξ :
      ∀ c i, sourceComplexMinkowskiInner d (D.qRight c) (A.ξ i) = 0 := by
    intro c i
    exact D.qRight_orth_M c ⟨A.ξ i, A.ξ_mem i⟩
  have hleft_expansion :
      complexLorentzAction A.Λsel z =
        fun i => A.ξ i + ∑ c : Fin D.sLeft, aLeft i c • D.qLeft c := by
    ext i μ
    calc
      complexLorentzAction A.Λsel z i μ =
          complexLorentzVectorAction A.Λsel (z i) μ := by
          rfl
      _ = (A.ξ i + A.leftResidual i) μ := by
          exact congrFun (A.left_decomp i) μ
      _ = (A.ξ i + ∑ c : Fin D.sLeft, aLeft i c • D.qLeft c) μ := by
          rw [h_aLeft i]
  have hright_expansion :
      w =
        fun i => A.ξ i + ∑ c : Fin D.sRight, aRight i c • D.qRight c := by
    ext i μ
    calc
      w i μ = (A.ξ i + A.rightResidual i) μ := by
          rw [A.right_decomp i]
      _ = (A.ξ i + ∑ c : Fin D.sRight, aRight i c • D.qRight c) μ := by
          rw [h_aRight i]
  have hleft_endpoint :
      (fun i => A.ξ i + ∑ c : Fin D.sLeft, aLeft i c • D.qLeft c) ∈
        ExtendedTube d n := by
    rw [← hleft_expansion]
    exact complexLorentzAction_mem_extendedTube n A.Λsel hz
  have hright_endpoint :
      (fun i => A.ξ i + ∑ c : Fin D.sRight, aRight i c • D.qRight c) ∈
        ExtendedTube d n := by
    rw [← hright_expansion]
    exact hw
  have hleft_all :=
    hw_isotropicFrame_allCoefficients_mem_extendedTube
      (d := d) hd (m := D.sLeft) (ξ := A.ξ) (a := aLeft)
      (q := D.qLeft) hleft_endpoint D.qLeft_pair_zero hqLeft_orth_ξ
  have hright_all :=
    hw_isotropicFrame_allCoefficients_mem_extendedTube
      (d := d) hd (m := D.sRight) (ξ := A.ξ) (a := aRight)
      (q := D.qRight) hright_endpoint D.qRight_pair_zero hqRight_orth_ξ
  have hleft_curve_eq :
      ∀ t,
        complexLorentzAction (contractLeft t * A.Λsel) z =
          fun i => A.ξ i +
            ∑ c : Fin D.sLeft,
              (((Real.exp (-t) : ℝ) : ℂ) * aLeft i c) • D.qLeft c := by
    intro t
    calc
      complexLorentzAction (contractLeft t * A.Λsel) z =
          complexLorentzAction (contractLeft t)
            (complexLorentzAction A.Λsel z) := by
            exact complexLorentzAction_mul (contractLeft t) A.Λsel z
      _ =
          complexLorentzAction (contractLeft t)
            (fun i => A.ξ i +
              ∑ c : Fin D.sLeft, aLeft i c • D.qLeft c) := by
            exact congrArg (complexLorentzAction (contractLeft t)) hleft_expansion
      _ =
          fun i => A.ξ i +
            ∑ c : Fin D.sLeft,
              (((Real.exp (-t) : ℝ) : ℂ) * aLeft i c) • D.qLeft c := by
            exact
              complexLorentzAction_residualExpansion
                (contractLeft t) A.ξ aLeft D.qLeft
                (((Real.exp (-t) : ℝ) : ℂ))
                (hcontractLeft_fix_ξ t) (hcontractLeft_scale_q t)
  have hright_curve_eq :
      ∀ t,
        complexLorentzAction (contractRight t) w =
          fun i => A.ξ i +
            ∑ c : Fin D.sRight,
              (((Real.exp (-t) : ℝ) : ℂ) * aRight i c) • D.qRight c := by
    intro t
    calc
      complexLorentzAction (contractRight t) w =
          complexLorentzAction (contractRight t)
            (fun i => A.ξ i +
              ∑ c : Fin D.sRight, aRight i c • D.qRight c) := by
            exact congrArg (complexLorentzAction (contractRight t)) hright_expansion
      _ =
          fun i => A.ξ i +
            ∑ c : Fin D.sRight,
              (((Real.exp (-t) : ℝ) : ℂ) * aRight i c) • D.qRight c := by
            exact
              complexLorentzAction_residualExpansion
                (contractRight t) A.ξ aRight D.qRight
                (((Real.exp (-t) : ℝ) : ℂ))
                (hcontractRight_fix_ξ t) (hcontractRight_scale_q t)
  refine
    { base := A.ξ
      curve_left := fun t => complexLorentzAction (contractLeft t * A.Λsel) z
      curve_right := fun t => complexLorentzAction (contractRight t) w
      base_mem := hleft_all.1
      curve_left_mem := ?_
      curve_right_mem := ?_
      curve_left_tendsto_base := ?_
      curve_right_tendsto_base := ?_
      curve_left_orbit := ?_
      curve_right_orbit := ?_ }
  · intro t
    rw [hleft_curve_eq t]
    exact hleft_all.2
      (fun i c => (((Real.exp (-t) : ℝ) : ℂ) * aLeft i c))
  · intro t
    rw [hright_curve_eq t]
    exact hright_all.2
      (fun i c => (((Real.exp (-t) : ℝ) : ℂ) * aRight i c))
  · refine
      Filter.Tendsto.congr'
        (Eventually.of_forall fun t => ?_)
        (tendsto_isotropicResidual_exp_neg_base
          (d := d) (n := n) (s := D.sLeft) A.ξ aLeft D.qLeft)
    ext i μ
    calc
      A.ξ i μ +
          ∑ c : Fin D.sLeft,
            (((Real.exp (-t) : ℝ) : ℂ) * aLeft i c * D.qLeft c μ) =
        (A.ξ i +
          ∑ c : Fin D.sLeft,
            (((Real.exp (-t) : ℝ) : ℂ) * aLeft i c) • D.qLeft c) μ := by
          simp [Pi.smul_apply, mul_assoc]
      _ = complexLorentzAction (contractLeft t * A.Λsel) z i μ :=
          congrFun (congrFun (hleft_curve_eq t).symm i) μ
  · refine
      Filter.Tendsto.congr'
        (Eventually.of_forall fun t => ?_)
        (tendsto_isotropicResidual_exp_neg_base
          (d := d) (n := n) (s := D.sRight) A.ξ aRight D.qRight)
    ext i μ
    calc
      A.ξ i μ +
          ∑ c : Fin D.sRight,
            (((Real.exp (-t) : ℝ) : ℂ) * aRight i c * D.qRight c μ) =
        (A.ξ i +
          ∑ c : Fin D.sRight,
            (((Real.exp (-t) : ℝ) : ℂ) * aRight i c) • D.qRight c) μ := by
          simp [Pi.smul_apply, mul_assoc]
      _ = complexLorentzAction (contractRight t) w i μ :=
          congrFun (congrFun (hright_curve_eq t).symm i) μ
  · intro t
    exact ⟨contractLeft t * A.Λsel, rfl⟩
  · intro t
    exact ⟨contractRight t, rfl⟩

/-- Fully constructive separate-frame low-rank singular contraction data after
the selected-span alignment. -/
noncomputable def hw_sameSourceGram_singular_contractionData_of_selectedAlignment
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    HWSameSourceGramSingularContractionData d n z w :=
  hw_sameSourceGram_singular_contractionData_of_separateFrameData
    (d := d) hd hz hw A (hw_lowRank_separateResidualFrameData A)

end BHW
