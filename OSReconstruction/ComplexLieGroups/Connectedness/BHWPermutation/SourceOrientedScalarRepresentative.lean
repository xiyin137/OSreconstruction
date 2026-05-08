import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTubeResidualPolydisc

/-!
# Oriented scalar representatives

This file contains the first mechanical scalar-representative layer for the
proper-complex oriented Hall-Wightman route: the branch-defined quotient value
on the oriented extended-tube image, its well-definedness under the oriented
branch law, and the data package consumed by later OS II locality steps.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Source-oriented Hall-Wightman scalar representative data for the ordinary
extended-tube branch.  The representative lives on the source-oriented image of
the extended tube, a relatively open connected subset of the source-oriented
variety. -/
structure SourceOrientedScalarRepresentativeData
    {d : ℕ}
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  U : Set (SourceOrientedGramData d n)
  U_eq : U = sourceOrientedExtendedTubeDomain d n
  U_relOpen : IsRelOpenInSourceOrientedGramVariety d n U
  U_connected : IsConnected U
  Phi : SourceOrientedGramData d n → ℂ
  Phi_holomorphic : SourceOrientedVarietyGermHolomorphicOn d n Phi U
  branch_eq :
    ∀ w, w ∈ ExtendedTube d n →
      Phi (sourceOrientedMinkowskiInvariant d n w) = extendF F w

/-- A source-oriented scalar representative gives the normalized initial
oriented continuation chart on the ordinary extended tube, for any OS45
continuation ambient `U` containing that extended tube.

The hard input is still the scalar representative itself; this constructor
only packages its oriented pullback law into the local chart API used by the
strict BHW/Jost continuation chain. -/
noncomputable def SourceOrientedScalarRepresentativeData.toExtendedTubeInitialChart
    {d : ℕ}
    [NeZero d]
    {hd : 2 ≤ d}
    {n : ℕ}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (S : SourceOrientedScalarRepresentativeData (d := d) n F)
    (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (hET_sub_U : ExtendedTube d n ⊆ U)
    (hF_ext_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n)) :
    BHWJostLocalOrientedContinuationChart hd n τ U where
  carrier := ExtendedTube d n
  carrier_open := isOpen_extendedTube
  carrier_preconnected := (isConnected_extendedTube (d := d) (n := n)).2
  carrier_sub_U := hET_sub_U
  carrier_is_lorentz_step := by
    refine ⟨ExtendedTube d n, isOpen_extendedTube, ?_, 1, ?_⟩
    · intro z hz
      exact Or.inl hz
    · ext z
      constructor
      · intro hz
        exact ⟨z, hz, by simp [complexLorentzAction_one]⟩
      · rintro ⟨u, hu, rfl⟩
        simpa [complexLorentzAction_one] using hu
  orientedDomain := S.U
  oriented_relOpen := S.U_relOpen
  oriented_preconnected := S.U_connected.2
  oriented_sub_variety := by
    rw [S.U_eq]
    exact sourceOrientedExtendedTubeDomain_subset_variety d n
  oriented_mem := by
    intro z hz
    rw [S.U_eq]
    exact ⟨z, hz, rfl⟩
  oriented_realizes := by
    intro G hG
    rw [S.U_eq] at hG
    rcases hG with ⟨z, hz, hG⟩
    exact ⟨z, hz, hG⟩
  Psi := S.Phi
  Psi_holo := S.Phi_holomorphic
  branch := extendF F
  branch_eq_orientedPullback := by
    intro z hz
    exact (S.branch_eq z hz).symm
  branch_holo := hF_ext_holo
  branch_same_sourceOrientedInvariant := by
    intro z w hz hw hzw
    calc
      extendF F z = S.Phi (sourceOrientedMinkowskiInvariant d n z) :=
        (S.branch_eq z hz).symm
      _ = S.Phi (sourceOrientedMinkowskiInvariant d n w) := by rw [hzw]
      _ = extendF F w := S.branch_eq w hw
  branch_complexLorentzInvariant := by
    intro Λ z hz hΛz
    calc
      extendF F (complexLorentzAction Λ z) =
          S.Phi
            (sourceOrientedMinkowskiInvariant d n
              (complexLorentzAction Λ z)) :=
        (S.branch_eq (complexLorentzAction Λ z) hΛz).symm
      _ = S.Phi (sourceOrientedMinkowskiInvariant d n z) := by
        rw [sourceOrientedMinkowskiInvariant_complexLorentzAction]
      _ = extendF F z := S.branch_eq z hz

/-- A source-oriented scalar representative also gives the normalized initial
oriented continuation chart on a permuted extended-tube preimage.

The oriented germ is the ordinary representative precomposed with the source
permutation on oriented invariants.  This is the chart needed for the adjacent
initial branch `z ↦ extendF F (permAct τ z)` in the OS45 strict route. -/
noncomputable def SourceOrientedScalarRepresentativeData.toPermutedExtendedTubeInitialChart
    {d : ℕ}
    [NeZero d]
    {hd : 2 ≤ d}
    {n : ℕ}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (S : SourceOrientedScalarRepresentativeData (d := d) n F)
    (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (hPermET_sub_U :
      {z : Fin n → Fin (d + 1) → ℂ |
        permAct (d := d) τ z ∈ ExtendedTube d n} ⊆ U)
    (hF_perm_holo :
      DifferentiableOn ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          extendF F (permAct (d := d) τ z))
        {z | permAct (d := d) τ z ∈ ExtendedTube d n}) :
    BHWJostLocalOrientedContinuationChart hd n τ U where
  carrier := {z | permAct (d := d) τ z ∈ ExtendedTube d n}
  carrier_open :=
    isOpen_extendedTube.preimage (continuous_permAct (d := d) (n := n) τ)
  carrier_preconnected := by
    have hcarrier_eq :
        {z : Fin n → Fin (d + 1) → ℂ |
          permAct (d := d) τ z ∈ ExtendedTube d n} =
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            permAct (d := d) τ⁻¹ z) '' ExtendedTube d n := by
      ext z
      constructor
      · intro hz
        refine ⟨permAct (d := d) τ z, hz, ?_⟩
        ext k μ
        simp [permAct]
      · rintro ⟨w, hw, rfl⟩
        have hcancel :
            permAct (d := d) τ (permAct (d := d) τ⁻¹ w) = w := by
          ext k μ
          simp [permAct]
        simpa [hcancel] using hw
    have hpre :
        IsPreconnected
          ((fun z : Fin n → Fin (d + 1) → ℂ =>
            permAct (d := d) τ⁻¹ z) '' ExtendedTube d n) :=
      (isConnected_extendedTube (d := d) (n := n)).2.image _
        (continuous_permAct (d := d) (n := n) τ⁻¹).continuousOn
    simpa [hcarrier_eq] using hpre
  carrier_sub_U := hPermET_sub_U
  carrier_is_lorentz_step := by
    refine
      ⟨{z : Fin n → Fin (d + 1) → ℂ |
          permAct (d := d) τ z ∈ ExtendedTube d n},
        isOpen_extendedTube.preimage
          (continuous_permAct (d := d) (n := n) τ),
        ?_, 1, ?_⟩
    · intro z hz
      exact Or.inr hz
    · ext z
      constructor
      · intro hz
        exact ⟨z, hz, by simp [complexLorentzAction_one]⟩
      · rintro ⟨u, hu, rfl⟩
        simpa [complexLorentzAction_one] using hu
  orientedDomain :=
    {G : SourceOrientedGramData d n |
      sourcePermuteOrientedGram d n τ G ∈ S.U}
  oriented_relOpen :=
    S.U_relOpen.preimage_sourcePermuteOrientedGram (d := d) (n := n) τ
  oriented_preconnected := by
    have hdomain_eq :
        {G : SourceOrientedGramData d n |
          sourcePermuteOrientedGram d n τ G ∈ S.U} =
          (fun G : SourceOrientedGramData d n =>
            sourcePermuteOrientedGram d n τ⁻¹ G) '' S.U := by
      ext G
      constructor
      · intro hG
        refine ⟨sourcePermuteOrientedGram d n τ G, hG, ?_⟩
        exact sourcePermuteOrientedGram_inv_mul (d := d) (n := n) τ G
      · rintro ⟨H, hH, rfl⟩
        have hcancel :
            sourcePermuteOrientedGram d n τ
                (sourcePermuteOrientedGram d n τ⁻¹ H) = H := by
          simpa using
            sourcePermuteOrientedGram_inv_mul
              (d := d) (n := n) τ⁻¹ H
        change
          sourcePermuteOrientedGram d n τ
              (sourcePermuteOrientedGram d n τ⁻¹ H) ∈ S.U
        rw [hcancel]
        exact hH
    have hpre :
        IsPreconnected
          ((fun G : SourceOrientedGramData d n =>
            sourcePermuteOrientedGram d n τ⁻¹ G) '' S.U) :=
      S.U_connected.2.image _
        (continuous_sourcePermuteOrientedGram
          (d := d) (n := n) τ⁻¹).continuousOn
    simpa [hdomain_eq] using hpre
  oriented_sub_variety := by
    intro G hG
    have hperm_var :
        sourcePermuteOrientedGram d n τ G ∈
          sourceOrientedGramVariety d n := by
      rw [S.U_eq] at hG
      exact sourceOrientedExtendedTubeDomain_subset_variety d n hG
    exact
      (sourcePermuteOrientedGram_mem_variety_iff
        (d := d) (n := n) τ G).1 hperm_var
  oriented_mem := by
    intro z hz
    rw [S.U_eq]
    change
      sourcePermuteOrientedGram d n τ
          (sourceOrientedMinkowskiInvariant d n z) ∈
        sourceOrientedExtendedTubeDomain d n
    rw [← sourceOrientedMinkowskiInvariant_permAct
      (d := d) (n := n) τ z]
    exact ⟨permAct (d := d) τ z, hz, rfl⟩
  oriented_realizes := by
    intro G hG
    rw [S.U_eq] at hG
    rcases hG with ⟨w, hw, hwG⟩
    refine ⟨permAct (d := d) τ⁻¹ w, ?_, ?_⟩
    · have hcancel :
          permAct (d := d) τ (permAct (d := d) τ⁻¹ w) = w := by
        ext k μ
        simp [permAct]
      simpa [hcancel] using hw
    · calc
        sourceOrientedMinkowskiInvariant d n
            (permAct (d := d) τ⁻¹ w) =
            sourcePermuteOrientedGram d n τ⁻¹
              (sourceOrientedMinkowskiInvariant d n w) :=
          sourceOrientedMinkowskiInvariant_permAct
            (d := d) (n := n) τ⁻¹ w
        _ = sourcePermuteOrientedGram d n τ⁻¹
              (sourcePermuteOrientedGram d n τ G) := by rw [hwG]
        _ = G := sourcePermuteOrientedGram_inv_mul
          (d := d) (n := n) τ G
  Psi := fun G => S.Phi (sourcePermuteOrientedGram d n τ G)
  Psi_holo :=
    S.Phi_holomorphic.precomp_sourcePermuteOrientedGram
      (d := d) (n := n) τ
  branch := fun z => extendF F (permAct (d := d) τ z)
  branch_eq_orientedPullback := by
    intro z hz
    calc
      extendF F (permAct (d := d) τ z) =
          S.Phi
            (sourceOrientedMinkowskiInvariant d n
              (permAct (d := d) τ z)) :=
        (S.branch_eq (permAct (d := d) τ z) hz).symm
      _ = S.Phi
            (sourcePermuteOrientedGram d n τ
              (sourceOrientedMinkowskiInvariant d n z)) := by
        rw [sourceOrientedMinkowskiInvariant_permAct]
  branch_holo := hF_perm_holo
  branch_same_sourceOrientedInvariant := by
    intro z w hz hw hzw
    calc
      extendF F (permAct (d := d) τ z) =
          S.Phi
            (sourcePermuteOrientedGram d n τ
              (sourceOrientedMinkowskiInvariant d n z)) := by
        rw [← sourceOrientedMinkowskiInvariant_permAct
          (d := d) (n := n) τ z]
        exact (S.branch_eq (permAct (d := d) τ z) hz).symm
      _ = S.Phi
            (sourcePermuteOrientedGram d n τ
              (sourceOrientedMinkowskiInvariant d n w)) := by rw [hzw]
      _ = extendF F (permAct (d := d) τ w) := by
        rw [← sourceOrientedMinkowskiInvariant_permAct
          (d := d) (n := n) τ w]
        exact S.branch_eq (permAct (d := d) τ w) hw
  branch_complexLorentzInvariant := by
    intro Λ z hz hΛz
    calc
      extendF F (permAct (d := d) τ (complexLorentzAction Λ z)) =
          S.Phi
            (sourcePermuteOrientedGram d n τ
              (sourceOrientedMinkowskiInvariant d n
                (complexLorentzAction Λ z))) := by
        rw [← sourceOrientedMinkowskiInvariant_permAct
          (d := d) (n := n) τ (complexLorentzAction Λ z)]
        exact
          (S.branch_eq
            (permAct (d := d) τ (complexLorentzAction Λ z)) hΛz).symm
      _ = S.Phi
            (sourcePermuteOrientedGram d n τ
              (sourceOrientedMinkowskiInvariant d n z)) := by
        rw [sourceOrientedMinkowskiInvariant_complexLorentzAction]
      _ = extendF F (permAct (d := d) τ z) := by
        rw [← sourceOrientedMinkowskiInvariant_permAct
          (d := d) (n := n) τ z]
        exact S.branch_eq (permAct (d := d) τ z) hz

/-- The branch-defined quotient value on the source-oriented extended-tube
image, extended by zero away from that image. -/
noncomputable def sourceOrientedQuotientValue
    {d : ℕ}
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (G : SourceOrientedGramData d n) : ℂ :=
  if hG : G ∈ sourceOrientedExtendedTubeDomain d n then
    extendF F (Classical.choose hG)
  else
    0

/-- The quotient value is independent of the chosen extended-tube source
representative, provided the oriented branch law holds. -/
theorem sourceOrientedQuotientValue_wellDefined
    {d n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {G : SourceOrientedGramData d n}
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hGz : sourceOrientedMinkowskiInvariant d n z = G) :
    sourceOrientedQuotientValue (d := d) n F G = extendF F z := by
  classical
  have hGmem : G ∈ sourceOrientedExtendedTubeDomain d n := ⟨z, hz, hGz⟩
  unfold sourceOrientedQuotientValue
  rw [dif_pos hGmem]
  let zpick : Fin n → Fin (d + 1) → ℂ := Classical.choose hGmem
  have hzpick : zpick ∈ ExtendedTube d n :=
    (Classical.choose_spec hGmem).1
  have hpickG : sourceOrientedMinkowskiInvariant d n zpick = G :=
    (Classical.choose_spec hGmem).2
  exact hBranch hzpick hz (hpickG.trans hGz.symm)

/-- Local boundedness on a subset, packaged in the elementary form needed by
the quotient-value descent argument. -/
def LocallyBoundedOn
    {E : Type*}
    [TopologicalSpace E]
    (φ : E → ℂ)
    (U : Set E) : Prop :=
  ∀ x, x ∈ U →
    ∃ Ω0 : Set E,
      IsOpen Ω0 ∧ x ∈ Ω0 ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y, y ∈ Ω0 ∩ U → ‖φ y‖ ≤ C

/-- Compactness of the residual parameter set bounds the pulled-back quotient
values `extendF F (C.toVec c)`. -/
theorem sourceOrientedResidualChart_compactBound
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (C : SourceOrientedRankDeficientResidualChartData d n z0)
    (hF_ext_cont : ContinuousOn (extendF F) (ExtendedTube d n)) :
    ∃ Cbound : ℝ,
      0 ≤ Cbound ∧
        ∀ c, c ∈ C.K → ‖extendF F (C.toVec c)‖ ≤ Cbound := by
  have hvalue_cont :
      ContinuousOn (fun c : Fin C.m → ℂ => extendF F (C.toVec c)) C.K :=
    hF_ext_cont.comp C.toVec_continuousOn C.toVec_mem
  rcases C.K_compact.exists_bound_of_continuousOn hvalue_cont with
    ⟨Craw, hCraw⟩
  exact ⟨max Craw 0, le_max_right _ _, fun c hc =>
    (hCraw c hc).trans (le_max_left _ _)⟩

/-- On a residual-chart parameter, the branch-defined quotient agrees with the
corresponding `extendF` value. -/
theorem sourceOrientedResidualChart_quotient_eq_parameter
    {d n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (C : SourceOrientedRankDeficientResidualChartData d n z0)
    {G : SourceOrientedGramData d n}
    {c : Fin C.m → ℂ}
    (hcP : c ∈ C.P)
    (hcG : sourceOrientedMinkowskiInvariant d n (C.toVec c) = G) :
    sourceOrientedQuotientValue (d := d) n F G = extendF F (C.toVec c) :=
  sourceOrientedQuotientValue_wellDefined
    (d := d) F hBranch (C.toVec_mem c (C.P_subset_K hcP)) hcG

/-- The compact residual chart gives a local bound for the branch-defined
quotient value at a rank-deficient center. -/
theorem sourceOrientedQuotientValue_locallyBounded_of_residualChart
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_ext_cont : ContinuousOn (extendF F) (ExtendedTube d n))
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hlow :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    ∃ Ω : Set (SourceOrientedGramData d n),
      IsOpen Ω ∧
        sourceOrientedMinkowskiInvariant d n z0 ∈ Ω ∧
          ∃ Cbound : ℝ, 0 ≤ Cbound ∧
            ∀ G,
              G ∈ Ω ∩ sourceOrientedExtendedTubeDomain d n →
                ‖sourceOrientedQuotientValue (d := d) n F G‖ ≤ Cbound := by
  classical
  let R :=
    sourceOriented_rankDeficient_residualChart (d := d) hd n hz0 hlow
  rcases
    sourceOrientedResidualChart_compactBound (d := d) F R hF_ext_cont with
    ⟨Cbound, hCbound_nonneg, hCbound⟩
  refine ⟨R.Ω, R.Ω_open, R.center_mem, Cbound, hCbound_nonneg, ?_⟩
  intro G hG
  have hGvar :
      G ∈ R.Ω ∩ sourceOrientedGramVariety d n :=
    ⟨hG.1,
      sourceOrientedExtendedTubeDomain_subset_variety (d := d) (n := n) hG.2⟩
  rcases R.image_surj hGvar with ⟨c, hcP, hcG⟩
  have hquot :
      sourceOrientedQuotientValue (d := d) n F G =
        extendF F (R.toVec c) :=
    sourceOrientedResidualChart_quotient_eq_parameter
      (d := d) F hBranch R hcP hcG
  calc
    ‖sourceOrientedQuotientValue (d := d) n F G‖ =
        ‖extendF F (R.toVec c)‖ := by rw [hquot]
    _ ≤ Cbound := hCbound c (R.P_subset_K hcP)

/-- If a residual-chart parameter has the center invariant, the branch law
identifies its `extendF` value with the original center value. -/
theorem sourceOrientedResidualChart_clusterValue
    {d n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (C : SourceOrientedRankDeficientResidualChartData d n z0)
    {c : Fin C.m → ℂ}
    (hcK : c ∈ C.K)
    (hc0 :
      sourceOrientedMinkowskiInvariant d n (C.toVec c) =
        sourceOrientedMinkowskiInvariant d n z0) :
    extendF F (C.toVec c) = extendF F z0 :=
  hBranch (C.toVec_mem c hcK) C.center_mem_ET hc0

end BHW

namespace SCV

/-- If a function agrees locally on a relative neighborhood with a continuous
ambient representative, then it is continuous within the smaller domain. -/
theorem continuousWithinAt_of_local_eqOn_relNeighborhood
    {E : Type*}
    [TopologicalSpace E]
    {U V Ω : Set E}
    {x : E}
    {φ Ψ : E → ℂ}
    (hU_sub : U ⊆ V)
    (hxU : x ∈ U)
    (hΩ_open : IsOpen Ω)
    (hxΩ : x ∈ Ω)
    (hΨ_cont : ContinuousOn Ψ Ω)
    (hEq : Set.EqOn φ Ψ (Ω ∩ V)) :
    ContinuousWithinAt φ U x := by
  have hΨ_at : ContinuousAt Ψ x :=
    hΨ_cont.continuousAt (hΩ_open.mem_nhds hxΩ)
  have hΨ_tendsto :
      Tendsto Ψ (𝓝[U] x) (𝓝 (Ψ x)) :=
    hΨ_at.tendsto.mono_left nhdsWithin_le_nhds
  have hΩ_ev : ∀ᶠ y in 𝓝[U] x, y ∈ Ω :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hΩ_open.mem_nhds hxΩ)
  have hV_ev : ∀ᶠ y in 𝓝[U] x, y ∈ V :=
    eventually_mem_nhdsWithin.mono fun y hy => hU_sub hy
  have hEq_ev : ∀ᶠ y in 𝓝[U] x, Ψ y = φ y :=
    (hΩ_ev.and hV_ev).mono fun y hy => (hEq ⟨hy.1, hy.2⟩).symm
  have hxEq : Ψ x = φ x := (hEq ⟨hxΩ, hU_sub hxU⟩).symm
  simpa [hxEq] using hΨ_tendsto.congr' hEq_ev

/-- If a function agrees locally on a relative neighborhood with a continuous
ambient representative, then it is locally bounded on the smaller domain. -/
theorem locallyBoundedAt_of_local_eqOn_relNeighborhood
    {E : Type*}
    [TopologicalSpace E]
    {U V Ω : Set E}
    {x : E}
    {φ Ψ : E → ℂ}
    (hU_sub : U ⊆ V)
    (hΩ_open : IsOpen Ω)
    (hxΩ : x ∈ Ω)
    (hΨ_cont : ContinuousOn Ψ Ω)
    (hEq : Set.EqOn φ Ψ (Ω ∩ V)) :
    ∃ Ω0 : Set E,
      IsOpen Ω0 ∧ x ∈ Ω0 ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y, y ∈ Ω0 ∩ U → ‖φ y‖ ≤ C := by
  have hΨ_at : ContinuousAt Ψ x :=
    hΨ_cont.continuousAt (hΩ_open.mem_nhds hxΩ)
  have hpre : Ψ ⁻¹' Metric.ball (Ψ x) 1 ∈ 𝓝 x :=
    hΨ_at (Metric.ball_mem_nhds (Ψ x) zero_lt_one)
  rcases mem_nhds_iff.mp hpre with ⟨S, hS_sub, hS_open, hxS⟩
  let Ω0 : Set E := S ∩ Ω
  refine
    ⟨Ω0, hS_open.inter hΩ_open, ⟨hxS, hxΩ⟩,
      ‖Ψ x‖ + 1, by positivity, ?_⟩
  intro y hy
  have hyS : y ∈ S := hy.1.1
  have hyΩ : y ∈ Ω := hy.1.2
  have hyU : y ∈ U := hy.2
  have hball : Ψ y ∈ Metric.ball (Ψ x) 1 := hS_sub hyS
  have hdist : dist (Ψ y) (Ψ x) < 1 := by
    simpa [Metric.mem_ball] using hball
  have hnorm : ‖Ψ y‖ ≤ ‖Ψ x‖ + 1 := by
    calc
      ‖Ψ y‖ ≤ ‖Ψ x‖ + dist (Ψ y) (Ψ x) := by
        simpa [dist_eq_norm, norm_sub_rev, add_comm] using
          norm_add_le (Ψ x) (Ψ y - Ψ x)
      _ ≤ ‖Ψ x‖ + 1 := by linarith
  have hφ : φ y = Ψ y := hEq ⟨hyΩ, hU_sub hyU⟩
  simpa [hφ] using hnorm

/-- Compact-parameter continuity criterion.  A compact parameter family
surjects onto a local piece of the target, the scalar value agrees with the
parameter value there, and every compact-parameter point over the base has the
same scalar value; then the descended scalar is continuous within the target
domain at the base. -/
theorem continuousWithinAt_of_compact_parameter_surjection
    {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    [T2Space X]
    [T2Space Y]
    {K P : Set X}
    {Ω U : Set Y}
    {y0 : Y}
    {param : X → Y}
    {value : X → ℂ}
    {φ : Y → ℂ}
    (hK_compact : IsCompact K)
    (hP_subset_K : P ⊆ K)
    (hparam_cont : ContinuousOn param K)
    (hvalue_cont : ContinuousOn value K)
    (_hy0U : y0 ∈ U)
    (hΩ_open : IsOpen Ω)
    (hy0Ω : y0 ∈ Ω)
    (hsurj : ∀ y, y ∈ Ω ∩ U → ∃ c, c ∈ P ∧ param c = y)
    (hvalue_eq :
      ∀ y, y ∈ Ω ∩ U → ∀ c, c ∈ P → param c = y → φ y = value c)
    (hcluster_base :
      ∀ c, c ∈ K → param c = y0 → value c = φ y0) :
    ContinuousWithinAt φ U y0 := by
  rw [ContinuousWithinAt, tendsto_def]
  intro S hS
  rcases mem_nhds_iff.mp hS with ⟨V, hV_sub, hV_open, hφV⟩
  let Bad : Set X := K ∩ value ⁻¹' Vᶜ
  have hBad_closed : IsClosed Bad := by
    simpa [Bad] using
      hvalue_cont.preimage_isClosed_of_isClosed hK_compact.isClosed
        hV_open.isClosed_compl
  have hBad_compact : IsCompact Bad :=
    hK_compact.of_isClosed_subset hBad_closed (by
      intro c hc
      exact hc.1)
  have hparam_bad_cont : ContinuousOn param Bad :=
    hparam_cont.mono (by
      intro c hc
      exact hc.1)
  have hBad_image_closed : IsClosed (param '' Bad) :=
    (hBad_compact.image_of_continuousOn hparam_bad_cont).isClosed
  have hy0_not_bad : y0 ∉ param '' Bad := by
    rintro ⟨c, hcBad, hcy0⟩
    have hcK : c ∈ K := hcBad.1
    have hval : value c = φ y0 := hcluster_base c hcK hcy0
    exact hcBad.2 (by simpa [hval] using hφV)
  let N : Set Y := (param '' Bad)ᶜ ∩ Ω
  have hN_open : IsOpen N :=
    hBad_image_closed.isOpen_compl.inter hΩ_open
  have hy0N : y0 ∈ N := ⟨hy0_not_bad, hy0Ω⟩
  refine mem_nhdsWithin.mpr ⟨N, hN_open, hy0N, ?_⟩
  intro y hy
  have hyN : y ∈ N := hy.1
  have hyU : y ∈ U := hy.2
  rcases hsurj y ⟨hyN.2, hyU⟩ with ⟨c, hcP, hcy⟩
  have hcK : c ∈ K := hP_subset_K hcP
  have hc_not_bad : c ∉ Bad := by
    intro hcBad
    exact hyN.1 ⟨c, hcBad, hcy⟩
  have hvalueV : value c ∈ V := by
    by_contra hnotV
    exact hc_not_bad ⟨hcK, hnotV⟩
  have hφ_eq : φ y = value c :=
    hvalue_eq y ⟨hyN.2, hyU⟩ c hcP hcy
  exact hV_sub (by simpa [hφ_eq] using hvalueV)

end SCV

namespace BHW

/-- The compact residual chart gives continuity of the branch-defined quotient
value at a rank-deficient center. -/
theorem sourceOrientedQuotientValue_continuous_of_residualChart
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_ext_cont : ContinuousOn (extendF F) (ExtendedTube d n))
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hlow :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    ContinuousWithinAt
      (sourceOrientedQuotientValue (d := d) n F)
      (sourceOrientedExtendedTubeDomain d n)
      (sourceOrientedMinkowskiInvariant d n z0) := by
  classical
  let R :=
    sourceOriented_rankDeficient_residualChart (d := d) hd n hz0 hlow
  have hvalue_cont :
      ContinuousOn (fun c : Fin R.m → ℂ => extendF F (R.toVec c)) R.K :=
    hF_ext_cont.comp R.toVec_continuousOn R.toVec_mem
  have hparam_cont :
      ContinuousOn
        (fun c : Fin R.m → ℂ =>
          sourceOrientedMinkowskiInvariant d n (R.toVec c))
        R.K := by
    have hinv_cont :
        ContinuousOn (sourceOrientedMinkowskiInvariant d n) Set.univ :=
      (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).continuousOn
    exact
      hinv_cont.comp R.toVec_continuousOn (by intro c hc; exact Set.mem_univ _)
  have hy0U :
      sourceOrientedMinkowskiInvariant d n z0 ∈
        sourceOrientedExtendedTubeDomain d n :=
    ⟨z0, hz0, rfl⟩
  refine
    SCV.continuousWithinAt_of_compact_parameter_surjection
      (K := R.K) (P := R.P) (Ω := R.Ω)
      (U := sourceOrientedExtendedTubeDomain d n)
      (y0 := sourceOrientedMinkowskiInvariant d n z0)
      (param := fun c : Fin R.m → ℂ =>
        sourceOrientedMinkowskiInvariant d n (R.toVec c))
      (value := fun c : Fin R.m → ℂ => extendF F (R.toVec c))
      (φ := sourceOrientedQuotientValue (d := d) n F)
      R.K_compact R.P_subset_K hparam_cont hvalue_cont hy0U
      R.Ω_open R.center_mem ?_ ?_ ?_
  · intro G hG
    have hGvar :
        G ∈ R.Ω ∩ sourceOrientedGramVariety d n :=
      ⟨hG.1,
        sourceOrientedExtendedTubeDomain_subset_variety (d := d) (n := n) hG.2⟩
    exact R.image_surj hGvar
  · intro G hG c hcP hcG
    exact
      sourceOrientedResidualChart_quotient_eq_parameter
        (d := d) F hBranch R hcP hcG
  · intro c hcK hc0
    have hcenter :
        sourceOrientedQuotientValue (d := d) n F
            (sourceOrientedMinkowskiInvariant d n z0) =
          extendF F z0 :=
      sourceOrientedQuotientValue_wellDefined (d := d) F hBranch hz0 rfl
    exact
      (sourceOrientedResidualChart_clusterValue
        (d := d) F hBranch R hcK hc0).trans hcenter.symm

/-- Once max-rank points have local ambient holomorphic representatives for the
quotient value, the checked residual chart supplies the rank-deficient branch
and hence global continuity and local boundedness on the oriented
extended-tube image. -/
theorem sourceOrientedQuotientValue_continuous_locallyBounded_of_maxRankLocal
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_ext_cont : ContinuousOn (extendF F) (ExtendedTube d n))
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    (hMaxLocal :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedExtendedTubeDomain d n →
          SourceOrientedMaxRankAt d n G0 →
            ∃ Ω Ψ,
              IsOpen Ω ∧ G0 ∈ Ω ∧
                DifferentiableOn ℂ Ψ Ω ∧
                  Ω ∩ sourceOrientedGramVariety d n ⊆
                    sourceOrientedExtendedTubeDomain d n ∧
                  Set.EqOn (sourceOrientedQuotientValue (d := d) n F) Ψ
                    (Ω ∩ sourceOrientedGramVariety d n)) :
    ContinuousOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) ∧
      LocallyBoundedOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) := by
  classical
  have hU_sub :
      sourceOrientedExtendedTubeDomain d n ⊆
        sourceOrientedGramVariety d n :=
    sourceOrientedExtendedTubeDomain_subset_variety d n
  constructor
  · intro G0 hG0
    rcases hG0 with ⟨z0, hz0, rfl⟩
    by_cases hmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)
    · rcases hMaxLocal ⟨z0, hz0, rfl⟩ hmax with
        ⟨Ω, Ψ, hΩ_open, hG0Ω, hΨ, _hΩ_sub, hEq⟩
      exact
        SCV.continuousWithinAt_of_local_eqOn_relNeighborhood
          (U := sourceOrientedExtendedTubeDomain d n)
          (V := sourceOrientedGramVariety d n)
          (Ω := Ω)
          hU_sub ⟨z0, hz0, rfl⟩ hΩ_open hG0Ω
          hΨ.continuousOn hEq
    · exact
        sourceOrientedQuotientValue_continuous_of_residualChart
          (d := d) hd n F hF_ext_cont hBranch hz0 hmax
  · intro G0 hG0
    rcases hG0 with ⟨z0, hz0, rfl⟩
    by_cases hmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)
    · rcases hMaxLocal ⟨z0, hz0, rfl⟩ hmax with
        ⟨Ω, Ψ, hΩ_open, hG0Ω, hΨ, _hΩ_sub, hEq⟩
      exact
        SCV.locallyBoundedAt_of_local_eqOn_relNeighborhood
          (U := sourceOrientedExtendedTubeDomain d n)
          (V := sourceOrientedGramVariety d n)
          (Ω := Ω)
          hU_sub hΩ_open hG0Ω hΨ.continuousOn hEq
    · exact
        sourceOrientedQuotientValue_locallyBounded_of_residualChart
          (d := d) hd n F hF_ext_cont hBranch hz0 hmax

/-- Assemble source-oriented scalar representative data from the oriented
domain geometry and a descended germ-holomorphic quotient branch. -/
noncomputable def sourceOrientedScalarRepresentativeData_of_branchLaw
    {d : ℕ}
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hGeom :
      IsRelOpenInSourceOrientedGramVariety d n
          (sourceOrientedExtendedTubeDomain d n) ∧
        IsConnected (sourceOrientedExtendedTubeDomain d n))
    (hDesc :
      ∃ Phi : SourceOrientedGramData d n → ℂ,
        SourceOrientedVarietyGermHolomorphicOn d n Phi
          (sourceOrientedExtendedTubeDomain d n) ∧
        ∀ w, w ∈ ExtendedTube d n →
          Phi (sourceOrientedMinkowskiInvariant d n w) = extendF F w) :
    SourceOrientedScalarRepresentativeData (d := d) n F := by
  classical
  refine
    { U := sourceOrientedExtendedTubeDomain d n
      U_eq := rfl
      U_relOpen := hGeom.1
      U_connected := hGeom.2
      Phi := Classical.choose hDesc
      Phi_holomorphic := (Classical.choose_spec hDesc).1
      branch_eq := ?_ }
  exact (Classical.choose_spec hDesc).2

end BHW
