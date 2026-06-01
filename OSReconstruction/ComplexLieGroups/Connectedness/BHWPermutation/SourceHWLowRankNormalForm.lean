import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWCommonResidualFrame

/-!
# Hall-Wightman low-rank normal-form assembly

This file consumes the honest finite-dimensional common isotropic-frame data
after selected-span alignment and assembles the checked
`HWLowRankIsotropicNormalForm`.  It deliberately leaves the remaining
maximal/common isotropic-frame producer as a separate theorem: the consumer
below only adds the already checked dual-frame, determinant-one null boost,
extended-tube coefficient freedom, and convergence fields.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Lorentz actions distribute over a base plus finite isotropic-frame
residual expansion when the action fixes the base and scales the frame. -/
theorem complexLorentzAction_residualExpansion
    {d n s : ℕ}
    (Λ : ComplexLorentzGroup d)
    (ξ : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → Fin s → ℂ)
    (q : Fin s → Fin (d + 1) → ℂ)
    (α : ℂ)
    (hfix : ∀ i, complexLorentzVectorAction Λ (ξ i) = ξ i)
    (hscale : ∀ c, complexLorentzVectorAction Λ (q c) = α • q c) :
    complexLorentzAction Λ (fun i => ξ i + ∑ c, a i c • q c) =
      fun i => ξ i + ∑ c, (α * a i c) • q c := by
  ext i μ
  simp only [complexLorentzAction]
  have hsum_action :
      complexLorentzVectorAction Λ (∑ c : Fin s, a i c • q c) =
        fun μ => ∑ c : Fin s,
          complexLorentzVectorAction Λ (a i c • q c) μ := by
    rw [show (∑ c : Fin s, a i c • q c) =
        (fun μ => ∑ c : Fin s, (a i c • q c) μ) by
      exact Finset.sum_fn Finset.univ (fun c : Fin s => a i c • q c)]
    exact complexLorentzVectorAction_sum Λ (fun c : Fin s => a i c • q c)
  calc
    complexLorentzVectorAction Λ (ξ i + ∑ c : Fin s, a i c • q c) μ
        =
      (complexLorentzVectorAction Λ (ξ i) +
        complexLorentzVectorAction Λ (∑ c : Fin s, a i c • q c)) μ := by
          simpa only [Pi.add_apply] using
            congrFun
              (complexLorentzVectorAction_add Λ (ξ i)
                (∑ c : Fin s, a i c • q c)) μ
    _ = ξ i μ +
          (∑ c : Fin s, complexLorentzVectorAction Λ (a i c • q c) μ) := by
          rw [hfix i, hsum_action]
          rfl
    _ = ξ i μ + (∑ c : Fin s, ((α * a i c) • q c) μ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          calc
            complexLorentzVectorAction Λ (a i c • q c) μ =
                a i c * complexLorentzVectorAction Λ (q c) μ := by
                  simpa [Pi.smul_apply] using
                    congrFun
                      (complexLorentzVectorAction_smul Λ (a i c) (q c)) μ
            _ = ((α * a i c) • q c) μ := by
                  rw [hscale c]
                  simp [Pi.smul_apply, mul_comm, mul_left_comm]
    _ = ξ i μ + (∑ c : Fin s, (α * a i c) • q c) μ := by
          simp [Finset.sum_apply]

/-- The remaining finite-dimensional geometric input for the low-rank
Hall-Wightman normal form, after the selected spans have already been aligned.

The data say that a determinant-one Lorentz transformation fixing the selected
span has put the left residual family into the span of the same totally
isotropic frame that contains the right residual family.  This is the exact
place where the future maximal/common isotropic-frame producer must land; the
fields here do not include the dual frame, the contraction family, or any
extended-tube/convergence output. -/
structure HWLowRankCommonIsotropicFrameData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) where
  Λfix : ComplexLorentzGroup d
  s : ℕ
  aLeft : Fin n → Fin s → ℂ
  aRight : Fin n → Fin s → ℂ
  q : Fin s → Fin (d + 1) → ℂ
  left_eq :
    complexLorentzAction (Λfix * A.Λsel) z =
      fun i => A.ξ i + ∑ c : Fin s, aLeft i c • q c
  right_eq :
    w = fun i => A.ξ i + ∑ c : Fin s, aRight i c • q c
  q_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0
  q_orth_M :
    ∀ c (m : A.M),
      sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0
  q_independent : LinearIndependent ℂ q

/-- The geometric residual-alignment packet just before coefficient
extraction.  A future finite-dimensional Witt-basis theorem should produce
this data from `HWLowRankSelectedSpanAlignment`: a determinant-one Lorentz
correction fixing the selected span, a common totally isotropic frame, and
span membership of both residual families after the correction. -/
structure HWLowRankResidualAlignmentData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) where
  Λfix : ComplexLorentzGroup d
  s : ℕ
  q : Fin s → Fin (d + 1) → ℂ
  Λfix_M :
    ∀ m : A.M,
      complexLorentzVectorAction Λfix
        (m : Fin (d + 1) → ℂ) =
      (m : Fin (d + 1) → ℂ)
  left_span :
    ∀ i,
      complexLorentzVectorAction Λfix (A.leftResidual i) ∈
        Submodule.span ℂ (Set.range q)
  right_span :
    ∀ i, A.rightResidual i ∈ Submodule.span ℂ (Set.range q)
  q_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0
  q_orth_M :
    ∀ c (m : A.M),
      sourceComplexMinkowskiInner d (q c)
        (m : Fin (d + 1) → ℂ) = 0
  q_independent : LinearIndependent ℂ q

/-- Coefficient extraction and endpoint-expansion assembly from the geometric
residual-alignment packet.  This removes purely mechanical coefficient
bookkeeping from the remaining finite-dimensional common-frame producer. -/
noncomputable def hw_lowRank_commonIsotropicFrameData_of_residualAlignmentData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S)
    (D : HWLowRankResidualAlignmentData A) :
    HWLowRankCommonIsotropicFrameData A := by
  classical
  let leftVectors : Fin n → Fin (d + 1) → ℂ :=
    fun i => complexLorentzVectorAction D.Λfix (A.leftResidual i)
  let hLeftExists :=
    coefficients_of_family_mem_span_finite_frame
      (d := d) (n := n) (s := D.s) (q := D.q)
      (v := leftVectors) (by
        intro i
        exact D.left_span i)
  let aLeft : Fin n → Fin D.s → ℂ := Classical.choose hLeftExists
  have h_aLeft :
      ∀ i, leftVectors i = ∑ c : Fin D.s, aLeft i c • D.q c :=
    Classical.choose_spec hLeftExists
  let hRightExists :=
    coefficients_of_family_mem_span_finite_frame
      (d := d) (n := n) (s := D.s) (q := D.q)
      (v := A.rightResidual) D.right_span
  let aRight : Fin n → Fin D.s → ℂ := Classical.choose hRightExists
  have h_aRight :
      ∀ i, A.rightResidual i = ∑ c : Fin D.s, aRight i c • D.q c :=
    Classical.choose_spec hRightExists
  refine
    { Λfix := D.Λfix
      s := D.s
      aLeft := aLeft
      aRight := aRight
      q := D.q
      left_eq := ?_
      right_eq := ?_
      q_pair_zero := D.q_pair_zero
      q_orth_M := D.q_orth_M
      q_independent := D.q_independent }
  · ext i μ
    calc
      complexLorentzAction (D.Λfix * A.Λsel) z i μ =
          complexLorentzVectorAction D.Λfix
            (complexLorentzVectorAction A.Λsel (z i)) μ := by
            simpa [complexLorentzAction] using
              congrFun (congrFun
                (complexLorentzAction_mul D.Λfix A.Λsel z) i) μ
      _ =
          complexLorentzVectorAction D.Λfix
            (A.ξ i + A.leftResidual i) μ := by
            rw [A.left_decomp i]
      _ =
          (complexLorentzVectorAction D.Λfix (A.ξ i) +
            complexLorentzVectorAction D.Λfix (A.leftResidual i)) μ := by
            simpa only [Pi.add_apply] using
              congrFun
                (complexLorentzVectorAction_add D.Λfix (A.ξ i)
                  (A.leftResidual i)) μ
      _ = (A.ξ i + ∑ c : Fin D.s, aLeft i c • D.q c) μ := by
            rw [D.Λfix_M ⟨A.ξ i, A.ξ_mem i⟩]
            rw [show
                complexLorentzVectorAction D.Λfix (A.leftResidual i) =
                  ∑ c : Fin D.s, aLeft i c • D.q c from
                by simpa [leftVectors] using h_aLeft i]
  · ext i μ
    calc
      w i μ = (A.ξ i + A.rightResidual i) μ := by
          rw [A.right_decomp i]
      _ = (A.ξ i + ∑ c : Fin D.s, aRight i c • D.q c) μ := by
          rw [show A.rightResidual i =
              ∑ c : Fin D.s, aRight i c • D.q c from h_aRight i]

/-- Once the common isotropic-frame data are available, the full low-rank
normal form is mechanical: build the dual frame in `Mᗮ`, package the
determinant-one null boost, use coefficient freedom for extended-tube
membership, and use the explicit exponential residual limit for convergence. -/
noncomputable def hw_lowRank_isotropicNormalForm_of_commonFrameData
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S)
    (C : HWLowRankCommonIsotropicFrameData A) :
    HWLowRankIsotropicNormalForm d n z w := by
  classical
  let Λ0 : ComplexLorentzGroup d := C.Λfix * A.Λsel
  have hq_orth_ξ :
      ∀ c i, sourceComplexMinkowskiInner d (C.q c) (A.ξ i) = 0 := by
    intro c i
    exact C.q_orth_M c ⟨A.ξ i, A.ξ_mem i⟩
  let hdualExists :=
    complexMinkowski_isotropicDualFrame_of_residualFrame
      (d := d) (n := n) (s := C.s) (ξ := A.ξ) (q := C.q) (M := A.M)
      A.M_nondeg A.ξ_mem C.q_orth_M C.q_pair_zero C.q_independent
  let qDual : Fin C.s → Fin (d + 1) → ℂ := Classical.choose hdualExists
  have hdualSpec := Classical.choose_spec hdualExists
  have hqDual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0 :=
    hdualSpec.1
  have hq_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (C.q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0 :=
    hdualSpec.2.1
  have hqDual_orth_M :
      ∀ c (m : A.M),
        sourceComplexMinkowskiInner d (qDual c)
          (m : Fin (d + 1) → ℂ) = 0 :=
    hdualSpec.2.2.1
  have hqDual_orth :
      ∀ c i, sourceComplexMinkowskiInner d (qDual c) (A.ξ i) = 0 :=
    hdualSpec.2.2.2
  let contract : ℝ → ComplexLorentzGroup d := fun t =>
    complexMinkowski_selectedHyperbolicContractionFamily
      (d := d) (s := C.s) (M := A.M) (q := C.q) (qDual := qDual)
      A.M_nondeg C.q_orth_M hqDual_orth_M C.q_pair_zero
      hqDual_pair_zero hq_dual t
  have hcontract_fix_ξ :
      ∀ t i, complexLorentzVectorAction (contract t) (A.ξ i) = A.ξ i := by
    intro t i
    simpa [contract] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_M
        (d := d) (s := C.s) (M := A.M) (q := C.q) (qDual := qDual)
        A.M_nondeg C.q_orth_M hqDual_orth_M C.q_pair_zero
        hqDual_pair_zero hq_dual t ⟨A.ξ i, A.ξ_mem i⟩
  have hcontract_scale_q :
      ∀ t c,
        complexLorentzVectorAction (contract t) (C.q c) =
          ((Real.exp (-t) : ℝ) : ℂ) • C.q c := by
    intro t c
    simpa [contract] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_q
        (d := d) (s := C.s) (M := A.M) (q := C.q) (qDual := qDual)
        A.M_nondeg C.q_orth_M hqDual_orth_M C.q_pair_zero
        hqDual_pair_zero hq_dual t c
  have hcontract_scale_qDual :
      ∀ t c,
        complexLorentzVectorAction (contract t) (qDual c) =
          ((Real.exp t : ℝ) : ℂ) • qDual c := by
    intro t c
    simpa [contract] using
      complexMinkowski_selectedHyperbolicContractionFamily_maps_qDual
        (d := d) (s := C.s) (M := A.M) (q := C.q) (qDual := qDual)
        A.M_nondeg C.q_orth_M hqDual_orth_M C.q_pair_zero
        hqDual_pair_zero hq_dual t c
  have hleft_endpoint :
      (fun i => A.ξ i + ∑ c : Fin C.s, C.aLeft i c • C.q c) ∈
        ExtendedTube d n := by
    rw [← C.left_eq]
    exact complexLorentzAction_mem_extendedTube n Λ0 hz
  have hright_endpoint :
      (fun i => A.ξ i + ∑ c : Fin C.s, C.aRight i c • C.q c) ∈
        ExtendedTube d n := by
    rw [← C.right_eq]
    exact hw
  have hleft_all :=
    hw_isotropicFrame_allCoefficients_mem_extendedTube
      (d := d) hd (m := C.s) (ξ := A.ξ) (a := C.aLeft) (q := C.q)
      hleft_endpoint C.q_pair_zero hq_orth_ξ
  have hright_all :=
    hw_isotropicFrame_allCoefficients_mem_extendedTube
      (d := d) hd (m := C.s) (ξ := A.ξ) (a := C.aRight) (q := C.q)
      hright_endpoint C.q_pair_zero hq_orth_ξ
  have hleft_curve_eq :
      ∀ t,
        complexLorentzAction (contract t * Λ0) z =
          fun i => A.ξ i +
            ∑ c : Fin C.s,
              (((Real.exp (-t) : ℝ) : ℂ) * C.aLeft i c) • C.q c := by
    intro t
    calc
      complexLorentzAction (contract t * Λ0) z =
          complexLorentzAction (contract t) (complexLorentzAction Λ0 z) := by
            exact complexLorentzAction_mul (contract t) Λ0 z
      _ =
          complexLorentzAction (contract t)
            (fun i => A.ξ i + ∑ c : Fin C.s, C.aLeft i c • C.q c) := by
            exact congrArg (complexLorentzAction (contract t)) C.left_eq
      _ =
          fun i => A.ξ i +
            ∑ c : Fin C.s,
              (((Real.exp (-t) : ℝ) : ℂ) * C.aLeft i c) • C.q c := by
            exact
              complexLorentzAction_residualExpansion
                (contract t) A.ξ C.aLeft C.q (((Real.exp (-t) : ℝ) : ℂ))
                (hcontract_fix_ξ t) (hcontract_scale_q t)
  have hright_curve_eq :
      ∀ t,
        complexLorentzAction (contract t) w =
          fun i => A.ξ i +
            ∑ c : Fin C.s,
              (((Real.exp (-t) : ℝ) : ℂ) * C.aRight i c) • C.q c := by
    intro t
    calc
      complexLorentzAction (contract t) w =
          complexLorentzAction (contract t)
            (fun i => A.ξ i + ∑ c : Fin C.s, C.aRight i c • C.q c) := by
            exact congrArg (complexLorentzAction (contract t)) C.right_eq
      _ =
          fun i => A.ξ i +
            ∑ c : Fin C.s,
              (((Real.exp (-t) : ℝ) : ℂ) * C.aRight i c) • C.q c := by
            exact
              complexLorentzAction_residualExpansion
                (contract t) A.ξ C.aRight C.q (((Real.exp (-t) : ℝ) : ℂ))
                (hcontract_fix_ξ t) (hcontract_scale_q t)
  refine
    { Λ0 := Λ0
      ξ := A.ξ
      s := C.s
      aLeft := C.aLeft
      aRight := C.aRight
      q := C.q
      qDual := qDual
      left_eq := by
        simpa [Λ0] using C.left_eq
      right_eq := C.right_eq
      base_mem := hleft_all.1
      q_pair_zero := C.q_pair_zero
      qDual_pair_zero := hqDual_pair_zero
      q_dual := hq_dual
      q_orth := hq_orth_ξ
      qDual_orth := hqDual_orth
      contract := contract
      contract_fix_ξ := hcontract_fix_ξ
      contract_scale_q := hcontract_scale_q
      contract_scale_qDual := hcontract_scale_qDual
      contracted_left_mem := ?_
      contracted_right_mem := ?_
      contracted_left_tendsto := ?_
      contracted_right_tendsto := ?_ }
  · intro t
    rw [hleft_curve_eq t]
    exact hleft_all.2 (fun i c => (((Real.exp (-t) : ℝ) : ℂ) * C.aLeft i c))
  · intro t
    rw [hright_curve_eq t]
    exact hright_all.2 (fun i c => (((Real.exp (-t) : ℝ) : ℂ) * C.aRight i c))
  · refine
      Filter.Tendsto.congr'
        (Eventually.of_forall fun t => ?_)
        (tendsto_isotropicResidual_exp_neg_base
          (d := d) (n := n) (s := C.s) A.ξ C.aLeft C.q)
    ext i μ
    calc
      A.ξ i μ +
          ∑ c : Fin C.s,
            (((Real.exp (-t) : ℝ) : ℂ) * C.aLeft i c * C.q c μ) =
        (A.ξ i +
          ∑ c : Fin C.s,
            (((Real.exp (-t) : ℝ) : ℂ) * C.aLeft i c) • C.q c) μ := by
          simp [Pi.smul_apply, mul_assoc]
      _ = complexLorentzAction (contract t * Λ0) z i μ :=
          congrFun (congrFun (hleft_curve_eq t).symm i) μ
  · refine
      Filter.Tendsto.congr'
        (Eventually.of_forall fun t => ?_)
        (tendsto_isotropicResidual_exp_neg_base
          (d := d) (n := n) (s := C.s) A.ξ C.aRight C.q)
    ext i μ
    calc
      A.ξ i μ +
          ∑ c : Fin C.s,
            (((Real.exp (-t) : ℝ) : ℂ) * C.aRight i c * C.q c μ) =
        (A.ξ i +
          ∑ c : Fin C.s,
            (((Real.exp (-t) : ℝ) : ℂ) * C.aRight i c) • C.q c) μ := by
          simp [Pi.smul_apply, mul_assoc]
      _ = complexLorentzAction (contract t) w i μ :=
          congrFun (congrFun (hright_curve_eq t).symm i) μ

/-- The corresponding singular contraction-data wrapper from common
isotropic-frame data. -/
noncomputable def hw_sameSourceGram_singular_contractionData_of_commonFrameData
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S)
    (C : HWLowRankCommonIsotropicFrameData A) :
    HWSameSourceGramSingularContractionData d n z w :=
  hw_lowRank_isotropicNormalForm_to_contractionData
    (hw_lowRank_isotropicNormalForm_of_commonFrameData
      (d := d) hd hz hw A C)

end BHW
