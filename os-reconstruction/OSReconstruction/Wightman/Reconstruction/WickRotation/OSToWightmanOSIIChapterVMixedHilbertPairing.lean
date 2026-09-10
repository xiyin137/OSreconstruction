import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.LinearMap
import OSReconstruction.SCV.Osgood

/-!
# OS-II Chapter V mixed Hilbert pairings

The Chapter V generator candidates pair two holomorphic Hilbert-valued
fields. Since the complex inner product is conjugate-linear in its left slot,
the left field must first be evaluated at conjugated coordinates.

This file isolates that functional-analytic fact. The two conjugations, one
on the source and one in `innerSL`, compose to a holomorphic dual-valued
field. Bilinear evaluation against the right holomorphic field then gives a
holomorphic scalar pairing on the mixed product domain.
-/

noncomputable section

open Complex Set

namespace OSReconstruction
namespace OSIIChapterV

/-- The domain on which a left field can be evaluated at conjugated
coordinates. -/
def conjugateFieldDomain
    {E : Type*} [Star E] (U : Set E) : Set E :=
  (star : E → E) ⁻¹' U

/-- A Hilbert-valued field, evaluated at conjugated coordinates and embedded
in the continuous dual through the conjugate-linear left inner-product slot. -/
def conjugateDualField
    {E H : Type*}
    [Star E]
    [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (left : E → H) :
    E → (H →L[ℂ] ℂ) :=
  fun z => innerSL ℂ (left (star z))

/-- The scalar pairing used on a mixed Chapter V generator domain. -/
def mixedHilbertPairing
    {E₁ E₂ H : Type*}
    [Star E₁]
    [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (left : E₁ → H) (right : E₂ → H) :
    E₁ × E₂ → ℂ :=
  fun z => @inner ℂ H _ (left (star z.1)) (right z.2)

/-- The natural mixed domain for `mixedHilbertPairing`. -/
def mixedHilbertPairingDomain
    {E₁ E₂ : Type*} [Star E₁]
    (U : Set E₁) (V : Set E₂) :
    Set (E₁ × E₂) :=
  conjugateFieldDomain U ×ˢ V

@[simp]
theorem mixedHilbertPairing_apply
    {E₁ E₂ H : Type*}
    [Star E₁]
    [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (left : E₁ → H) (right : E₂ → H)
    (z : E₁ × E₂) :
    mixedHilbertPairing left right z =
      @inner ℂ H _ (left (star z.1)) (right z.2) :=
  rfl

theorem isOpen_conjugateFieldDomain
    {E : Type*} [TopologicalSpace E] [Star E] [ContinuousStar E]
    {U : Set E} (hU : IsOpen U) :
    IsOpen (conjugateFieldDomain U) :=
  hU.preimage continuous_star

theorem isOpen_mixedHilbertPairingDomain
    {E₁ E₂ : Type*}
    [TopologicalSpace E₁] [Star E₁] [ContinuousStar E₁]
    [TopologicalSpace E₂]
    {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (mixedHilbertPairingDomain U V) :=
  (isOpen_conjugateFieldDomain hU).prod hV

/-- The conjugated-coordinate left field is holomorphic after embedding it
in the continuous dual. -/
theorem differentiableAt_conjugateDualField
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E]
    [StarModule ℂ E] [ContinuousStar E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (left : E → H) (z : E)
    (hleft : DifferentiableAt ℂ left (star z)) :
    DifferentiableAt ℂ (conjugateDualField left) z := by
  let L : H →L⋆[ℂ] (H →L[ℂ] ℂ) :=
    innerSL (E := H) ℂ
  let R : E →L⋆[ℂ] E :=
    (starL (A := E) ℂ).toContinuousLinearMap
  have hleft' : DifferentiableAt ℂ left (R z) := by
    simpa [R] using hleft
  have h :=
    @DifferentiableAt.comp_semilinear₂
      ℂ E E H (H →L[ℂ] ℂ) _
      (starRingEnd ℂ) (starRingEnd ℂ)
      _ _ _ _ _ _ _ _ _ _
      L R left z hleft'
  simpa only [conjugateDualField, L, R, Function.comp_apply] using h

/-- Pairing two holomorphic Hilbert fields is holomorphic when the coordinates
of the conjugate-linear left slot are conjugated. -/
theorem differentiableOn_mixedHilbertPairing
    {E₁ E₂ H : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [StarAddMonoid E₁]
    [StarModule ℂ E₁] [ContinuousStar E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V)
    {left : E₁ → H} {right : E₂ → H}
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (mixedHilbertPairing left right)
      (mixedHilbertPairingDomain U V) := by
  intro z hz
  have hleftAt : DifferentiableAt ℂ left (star z.1) :=
    (hleft (star z.1) hz.1).differentiableAt
      (hU.mem_nhds hz.1)
  have hdualAt :
      DifferentiableAt ℂ (conjugateDualField left) z.1 :=
    differentiableAt_conjugateDualField left z.1 hleftAt
  have hdualProd :
      DifferentiableAt ℂ
        (fun w : E₁ × E₂ => conjugateDualField left w.1) z :=
    hdualAt.comp z (ContinuousLinearMap.fst ℂ E₁ E₂).differentiableAt
  have hrightAt : DifferentiableAt ℂ right z.2 :=
    (hright z.2 hz.2).differentiableAt
      (hV.mem_nhds hz.2)
  have hrightProd :
      DifferentiableAt ℂ (fun w : E₁ × E₂ => right w.2) z :=
    hrightAt.comp z (ContinuousLinearMap.snd ℂ E₁ E₂).differentiableAt
  simpa only [
    mixedHilbertPairing,
    conjugateDualField,
    innerSL_apply_apply
  ] using (hdualProd.clm_apply hrightProd).differentiableWithinAt

/-- The three-block Chapter V pairing: a conjugated left field, one complex
bridge parameter acting through an operator family, and a right field. -/
def bridgedMixedHilbertPairing
    {E₁ E₂ H : Type*}
    [Star E₁]
    [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : ℂ → H →L[ℂ] H)
    (left : E₁ → H) (right : E₂ → H) :
    ℂ × (E₁ × E₂) → ℂ :=
  fun p =>
    @inner ℂ H _
      (left (star p.2.1))
      (T p.1 (right p.2.2))

/-- The natural product domain of the three-block Chapter V pairing. -/
def bridgedMixedHilbertPairingDomain
    {E₁ E₂ : Type*} [Star E₁]
    (B : Set ℂ) (U : Set E₁) (V : Set E₂) :
    Set (ℂ × (E₁ × E₂)) :=
  B ×ˢ mixedHilbertPairingDomain U V

theorem isOpen_bridgedMixedHilbertPairingDomain
    {E₁ E₂ : Type*}
    [TopologicalSpace E₁] [Star E₁] [ContinuousStar E₁]
    [TopologicalSpace E₂]
    {B : Set ℂ} {U : Set E₁} {V : Set E₂}
    (hB : IsOpen B) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (bridgedMixedHilbertPairingDomain B U V) :=
  hB.prod (isOpen_mixedHilbertPairingDomain hU hV)

/-- A weakly holomorphic operator family in the bridge variable produces a
jointly holomorphic three-block pairing with holomorphic Hilbert fields.

Only scalar matrix-element holomorphy of `T` is required. Joint continuity,
together with Osgood's lemma, upgrades the separate bridge and vector-block
holomorphy to joint holomorphy. -/
theorem differentiableOn_bridgedMixedHilbertPairing
    {E₁ E₂ H : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [StarAddMonoid E₁]
    [StarModule ℂ E₁] [ContinuousStar E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {B : Set ℂ} {U : Set E₁} {V : Set E₂}
    (hB : IsOpen B) (hU : IsOpen U) (hV : IsOpen V)
    (T : ℂ → H →L[ℂ] H)
    (hT_cont :
      ContinuousOn
        (fun p : ℂ × H => T p.1 p.2)
        (B ×ˢ (Set.univ : Set H)))
    (hT_pair :
      ∀ x y : H,
        DifferentiableOn ℂ
          (fun z => @inner ℂ H _ x (T z y)) B)
    {left : E₁ → H} {right : E₂ → H}
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (bridgedMixedHilbertPairing T left right)
      (bridgedMixedHilbertPairingDomain B U V) := by
  let D : Set (ℂ × (E₁ × E₂)) :=
    bridgedMixedHilbertPairingDomain B U V
  have hleft_cont :
      ContinuousOn
        (fun p : ℂ × (E₁ × E₂) => left (star p.2.1)) D := by
    apply hleft.continuousOn.comp
      ((continuous_star.comp continuous_snd.fst).continuousOn)
    intro p hp
    exact hp.2.1
  have hright_cont :
      ContinuousOn
        (fun p : ℂ × (E₁ × E₂) => right p.2.2) D := by
    apply hright.continuousOn.comp continuous_snd.snd.continuousOn
    intro p hp
    exact hp.2.2
  have hshift_cont :
      ContinuousOn
        (fun p : ℂ × (E₁ × E₂) => T p.1 (right p.2.2)) D := by
    apply hT_cont.comp
      (continuous_fst.continuousOn.prodMk hright_cont)
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  apply SCV.osgood_lemma_prod hB
    (isOpen_mixedHilbertPairingDomain hU hV)
  · exact hleft_cont.inner hshift_cont
  · intro p hp
    exact hT_pair (left (star p.1)) (right p.2)
  · intro z hz
    have hright_shift :
        DifferentiableOn ℂ
          (fun w : E₂ => T z (right w)) V := by
      intro w hw
      exact
        ((T z).differentiableAt.comp w
          ((hright w hw).differentiableAt
            (hV.mem_nhds hw))).differentiableWithinAt
    simpa only [
      bridgedMixedHilbertPairing,
      mixedHilbertPairing
    ] using
      differentiableOn_mixedHilbertPairing
        hU hV hleft hright_shift

end OSIIChapterV
end OSReconstruction
