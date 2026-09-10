import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedCauchyContinuation

/-!
# Anchored coherence for source-indexed reflected Gram fields

Pairwise reflected Gram kernels determine a Hilbert-vector family only up to
a common unitary transformation.  Consequently, local continuation and
adjacent-overlap agreement do not by themselves identify charts reached by
unrelated continuation chains.

This file fixes that gauge ambiguity with one source anchor.  Every chart is
required to remain in the closed span of its anchored source vectors and to
realize the prescribed scalar continuation against those vectors.  These two
facts force arbitrary anchored charts to agree on overlaps.  Both conditions
are preserved by the complex-centered Cauchy successor, so the construction
provides the path coherence needed for the stage-wide `(P_N)` field without a
monodromy axiom.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} {m : ℕ}

def sourceAnchorSpan (anchorField : ι → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range anchorField)).topologicalClosure

theorem eq_of_mem_sourceAnchorSpan_of_inner_eq
    (anchorField : ι → H)
    {x y : H}
    (hx : x ∈ sourceAnchorSpan anchorField)
    (hy : y ∈ sourceAnchorSpan anchorField)
    (hinner :
      ∀ a, @inner ℂ H _ (anchorField a) x =
        @inner ℂ H _ (anchorField a) y) :
    x = y := by
  let K : Submodule ℂ H := sourceAnchorSpan anchorField
  have hxyK : x - y ∈ K :=
    K.sub_mem hx hy
  have hxyOrthSpan :
      x - y ∈ (Submodule.span ℂ (Set.range anchorField))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        rw [inner_sub_right, hinner a, sub_self]
    | zero =>
        exact inner_zero_left _
    | add u v _ _ hu hv =>
        rw [inner_add_left, hu, hv, add_zero]
    | smul c v _ hv =>
        simp only [inner_smul_left, hv, mul_zero]
  have hxyOrth : x - y ∈ Kᗮ := by
    simpa only [K, sourceAnchorSpan,
      Submodule.orthogonal_closure] using hxyOrthSpan
  have hxyBot : x - y ∈ (⊥ : Submodule ℂ H) := by
    rw [← K.inf_orthogonal_eq_bot]
    exact ⟨hxyK, hxyOrth⟩
  exact sub_eq_zero.mp (by simpa using hxyBot)

theorem mem_closedSubmodule_of_eventually_mem_of_holomorphic
    [CompleteSpace H]
    (K : Submodule ℂ H)
    (hK_closed : IsClosed (K : Set H))
    {U : Set (Fin m → ℂ)}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    {center : Fin m → ℂ}
    (hcenter : center ∈ U)
    {field : (Fin m → ℂ) → H}
    (hfield : DifferentiableOn ℂ field U)
    (hfield_local : ∀ᶠ z in 𝓝 center, field z ∈ K)
    {z : Fin m → ℂ}
    (hz : z ∈ U) :
    field z ∈ K := by
  have hperpperp : field z ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    let pairing : (Fin m → ℂ) → ℂ :=
      fun w => @inner ℂ H _ v (field w)
    have hpairing :
        DifferentiableOn ℂ pairing U := by
      exact
        (differentiableOn_const (c := innerSL ℂ v)).clm_apply hfield
    have hpairing_local : pairing =ᶠ[𝓝 center] 0 := by
      filter_upwards [hfield_local] with w hw
      exact Submodule.inner_left_of_mem_orthogonal hw hv
    exact
      (hpairing.analyticOnNhd_of_finiteDimensional hU_open)
        |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          hU_preconnected hcenter hpairing_local hz
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hperpperp
  rwa [hK_closed.submodule_topologicalClosure_eq] at hperpperp

/-- The doubled scalar point pairing a fixed left anchor with a variable
right Hilbert-field point. -/
def reflectedAnchorPair
    (anchorPoint z : Fin m → ℂ) :
    Fin (m + m) → ℂ :=
  Fin.append (star anchorPoint) z

@[simp] theorem reflectedAnchorPair_left
    (anchorPoint z : Fin m → ℂ) :
    star (fun i =>
      reflectedAnchorPair anchorPoint z (Fin.castAdd m i)) =
      anchorPoint := by
  funext i
  simp [reflectedAnchorPair]

@[simp] theorem reflectedAnchorPair_right
    (anchorPoint z : Fin m → ℂ) :
    (fun i =>
      reflectedAnchorPair anchorPoint z (Fin.natAdd m i)) =
      z := by
  funext i
  exact Fin.append_right _ _ _

theorem reflectedAnchorPair_mem_pairKernelDomain
    {U V : Set (Fin m → ℂ)}
    {anchorPoint z : Fin m → ℂ}
    (hanchorPoint : anchorPoint ∈ U)
    (hz : z ∈ V) :
    reflectedAnchorPair anchorPoint z ∈
      reflectedHilbertPairKernelDomain U V := by
  constructor
  · rw [reflectedAnchorPair_left]
    exact hanchorPoint
  · rw [reflectedAnchorPair_right]
    exact hz

/-- A reflected-Gram chart with one fixed source anchor that removes the
unitary gauge ambiguity between unrelated continuation chains. -/
structure SourceIndexedAnchoredReflectedGramHilbertFieldData
    (scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ)
    (anchorPoint : Fin m → ℂ)
    (anchorField : ι → H)
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι m scalar) where
  anchorPair_subset_scalarDomain :
    ∀ z ∈ P.domain,
      reflectedAnchorPair anchorPoint z ∈ P.scalarDomain
  scalar_eq_inner_anchor :
    ∀ a b z, z ∈ P.domain →
      scalar a b (reflectedAnchorPair anchorPoint z) =
        @inner ℂ H _ (anchorField a) (P.field b z)
  field_mem_sourceAnchorSpan :
    ∀ b z, z ∈ P.domain →
      P.field b z ∈ sourceAnchorSpan anchorField

namespace SourceIndexedAnchoredReflectedGramHilbertFieldData

variable
  {scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ}
  {anchorPoint : Fin m → ℂ}
  {anchorField : ι → H}
  {P Q : SourceIndexedReflectedGramHilbertFieldData
    H ι m scalar}

/-- A reflected-Gram chart becomes anchored at any one of its points once
its complete field range is known to lie in the closed span of the source
vectors at that point. -/
noncomputable def ofAnchor
    [Nonempty ι]
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι m scalar)
    (anchorPoint : Fin m → ℂ)
    (hanchorPoint : anchorPoint ∈ P.domain)
    (hfield_mem :
      ∀ b z, z ∈ P.domain →
        P.field b z ∈
          sourceAnchorSpan (fun a => P.field a anchorPoint)) :
    SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint (fun a => P.field a anchorPoint) P where
  anchorPair_subset_scalarDomain := by
    intro z hz
    let a₀ : ι := Classical.choice inferInstance
    exact
      P.kernelDomain_subset_scalarDomain a₀ a₀
        (reflectedAnchorPair_mem_pairKernelDomain
          hanchorPoint hz)
  scalar_eq_inner_anchor := by
    intro a b z hz
    have h :=
      P.scalar_eq_kernel a b
        (reflectedAnchorPair_mem_pairKernelDomain
          hanchorPoint hz)
    rw [reflectedHilbertPairKernel,
      reflectedAnchorPair_left,
      reflectedAnchorPair_right] at h
    exact h
  field_mem_sourceAnchorSpan := hfield_mem

/-- Anchored pairings and closed anchor-span membership force two charts to
agree on every overlap, independently of how the charts were reached. -/
theorem compatible
    (A : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField P)
    (B : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField Q)
    (b : ι) :
    Set.EqOn (P.field b) (Q.field b)
      (P.domain ∩ Q.domain) := by
  intro z hz
  apply
    eq_of_mem_sourceAnchorSpan_of_inner_eq
      anchorField
      (A.field_mem_sourceAnchorSpan b z hz.1)
      (B.field_mem_sourceAnchorSpan b z hz.2)
  intro a
  rw [← A.scalar_eq_inner_anchor a b z hz.1,
    ← B.scalar_eq_inner_anchor a b z hz.2]

variable {k : ℕ}
variable [CompleteSpace H]
variable
  {scalar' :
    ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
  {anchorPoint' : Fin (k + 1) → ℂ}
  {anchorField' : ι → H}
  {P' : SourceIndexedReflectedGramHilbertFieldData
    H ι (k + 1) scalar'}

/-- The fixed-anchor scalar identity propagates through one complex-centered
Cauchy successor by holomorphic uniqueness. -/
theorem successor_scalar_eq_inner_anchor
    (A : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar' anchorPoint' anchorField' P')
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar' P')
    (hanchorPair :
      ∀ z ∈ D.successorDomain,
        reflectedAnchorPair anchorPoint' z ∈ P'.scalarDomain)
    (a b : ι)
    (z : Fin (k + 1) → ℂ)
    (hz : z ∈ D.successorDomain) :
    scalar' a b (reflectedAnchorPair anchorPoint' z) =
      @inner ℂ H _ (anchorField' a) (D.successorField b z) := by
  let left : (Fin (k + 1) → ℂ) → ℂ :=
    fun w => scalar' a b (reflectedAnchorPair anchorPoint' w)
  let right : (Fin (k + 1) → ℂ) → ℂ :=
    fun w => @inner ℂ H _ (anchorField' a) (D.successorField b w)
  have hleft :
      DifferentiableOn ℂ left D.successorDomain := by
    exact
      (P'.scalar_holomorphic a b).comp
        (by
          change DifferentiableOn ℂ
            (fun w => Fin.append (star anchorPoint') w)
            D.successorDomain
          rw [differentiableOn_pi]
          intro j
          refine Fin.addCases ?_ ?_ j
          · intro i
            simp only [Fin.append_left]
            exact
              (differentiableOn_const
                (c := (star anchorPoint') i) :
                DifferentiableOn ℂ
                  (fun _ : Fin (k + 1) → ℂ =>
                    (star anchorPoint') i)
                  D.successorDomain)
          · intro i
            simp only [Fin.append_right]
            exact differentiableOn_apply i _)
        hanchorPair
  have hright :
      DifferentiableOn ℂ right D.successorDomain := by
    exact
      (differentiableOn_const
        (c := innerSL ℂ (anchorField' a))).clm_apply
          (D.successorField_holomorphic b)
  have hlocal : left =ᶠ[𝓝 D.center] right := by
    filter_upwards [
      D.successorField_eventuallyEq b,
      P'.domain_open.mem_nhds D.center_mem] with w hw hPw
    exact A.scalar_eq_inner_anchor a b w hPw |>.trans
      (congrArg (fun v => @inner ℂ H _ (anchorField' a) v) hw).symm
  exact
    (hleft.analyticOnNhd_of_finiteDimensional D.successorDomain_open)
      |>.eqOn_of_preconnected_of_eventuallyEq
        (hright.analyticOnNhd_of_finiteDimensional
          D.successorDomain_open)
        D.successorDomain_convex.isPreconnected
        D.center_mem_successorDomain hlocal hz

/-- A Cauchy successor remains in the closed anchor span because it agrees
locally with its predecessor there and the quotient scalar components vanish
by analytic continuation. -/
theorem successorField_mem_sourceAnchorSpan
    (A : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar' anchorPoint' anchorField' P')
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar' P')
    (b : ι)
    (z : Fin (k + 1) → ℂ)
    (hz : z ∈ D.successorDomain) :
    D.successorField b z ∈ sourceAnchorSpan anchorField' := by
  apply
    mem_closedSubmodule_of_eventually_mem_of_holomorphic
      (sourceAnchorSpan anchorField')
      (Submodule.isClosed_topologicalClosure
        (Submodule.span ℂ (Set.range anchorField')))
      D.successorDomain_open
      D.successorDomain_convex.isPreconnected
      D.center_mem_successorDomain
      (D.successorField_holomorphic b)
      ?_ hz
  filter_upwards [
    D.successorField_eventuallyEq b,
    P'.domain_open.mem_nhds D.center_mem] with w hw hPw
  rw [hw]
  exact A.field_mem_sourceAnchorSpan b w hPw

/-- One Cauchy continuation step preserves the anchored coherence contract. -/
noncomputable def toSuccessor
    (A : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar' anchorPoint' anchorField' P')
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar' P')
    (hanchorPair :
      ∀ z ∈ D.successorDomain,
        reflectedAnchorPair anchorPoint' z ∈ P'.scalarDomain) :
    SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar' anchorPoint' anchorField' D.toSuccessor where
  anchorPair_subset_scalarDomain := hanchorPair
  scalar_eq_inner_anchor := by
    intro a b z hz
    exact A.successor_scalar_eq_inner_anchor D hanchorPair a b z hz
  field_mem_sourceAnchorSpan := by
    intro b z hz
    exact A.successorField_mem_sourceAnchorSpan D b z hz

end SourceIndexedAnchoredReflectedGramHilbertFieldData

end OSIIChapterV
end OSReconstruction
