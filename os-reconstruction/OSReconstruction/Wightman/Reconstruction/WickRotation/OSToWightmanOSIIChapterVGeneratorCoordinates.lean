/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSemigroupMixedPairing



















noncomputable section

open Complex Filter Set Topology

namespace OSReconstruction
namespace OSIIChapterV

namespace GeneratorIndex

variable {k : ℕ} (i : GeneratorIndex k)

/-- Global coordinate occupied by a left internal gap.

The left Hilbert source is reflected in the OS inner product. Restoring
chronological order therefore reverses its internal gaps. -/
def leftGlobalIndex (a : Fin (i.n - 1)) : Fin k :=
  ⟨(Fin.rev a).1, by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega⟩

@[simp]
theorem leftGlobalIndex_rev_val (a : Fin (i.n - 1)) :
    (i.leftGlobalIndex (Fin.rev a)).val = a.val := by
  simp [leftGlobalIndex]

/-- Global coordinate occupied by the semigroup bridge. -/
def bridgeGlobalIndex : Fin k :=
  ⟨i.n - 1, by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega⟩

/-- Global coordinate occupied by a right internal gap. -/
def rightGlobalIndex (b : Fin (i.m - 1)) : Fin k :=
  ⟨i.n + b.1, by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega⟩

/-- Extract, reverse, and negate the left block before conjugation in the
Hilbert pairing. -/
def leftCoordinatesCLM :
    OSIITimeGapSpace k →L[ℂ] (Fin (i.n - 1) → ℂ) :=
  ContinuousLinearMap.pi fun a =>
    -(ContinuousLinearMap.proj
      (R := ℂ) (ι := Fin k) (φ := fun _ => ℂ)
      (i.leftGlobalIndex a))

/-- Extract the distinguished bridge coordinate. -/
def bridgeCoordinateCLM :
    OSIITimeGapSpace k →L[ℂ] ℂ :=
  ContinuousLinearMap.proj
    (R := ℂ) (ι := Fin k) (φ := fun _ => ℂ)
    i.bridgeGlobalIndex

/-- Extract the right block in its original order. -/
def rightCoordinatesCLM :
    OSIITimeGapSpace k →L[ℂ] (Fin (i.m - 1) → ℂ) :=
  ContinuousLinearMap.pi fun b =>
    ContinuousLinearMap.proj
      (R := ℂ) (ι := Fin k) (φ := fun _ => ℂ)
      (i.rightGlobalIndex b)

/-- Split all global generator coordinates into bridge, left, and right
blocks in the input order of `osiiSemigroupMixedHilbertPairing`. -/
def splitCoordinatesCLM :
    OSIITimeGapSpace k →L[ℂ]
      ℂ × ((Fin (i.n - 1) → ℂ) × (Fin (i.m - 1) → ℂ)) :=
  i.bridgeCoordinateCLM.prod
    (i.leftCoordinatesCLM.prod i.rightCoordinatesCLM)

@[simp]
theorem leftCoordinatesCLM_apply
    (w : OSIITimeGapSpace k) (a : Fin (i.n - 1)) :
    i.leftCoordinatesCLM w a = -w (i.leftGlobalIndex a) := by
  rfl

@[simp]
theorem splitCoordinatesCLM_fst
    (w : OSIITimeGapSpace k) :
    (i.splitCoordinatesCLM w).1 = w i.bridgeGlobalIndex := by
  rfl

@[simp]
theorem splitCoordinatesCLM_left
    (w : OSIITimeGapSpace k) (a : Fin (i.n - 1)) :
    (i.splitCoordinatesCLM w).2.1 a =
      -w (i.leftGlobalIndex a) := by
  rfl

@[simp]
theorem splitCoordinatesCLM_right
    (w : OSIITimeGapSpace k) (b : Fin (i.m - 1)) :
    (i.splitCoordinatesCLM w).2.2 b =
      w (i.rightGlobalIndex b) := by
  rfl

end GeneratorIndex

variable {d k : ℕ} [NeZero d]

/-- The Chapter V scalar candidate attached to one admissible split. -/
def generatorSemigroupCandidate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right : (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (w : OSIITimeGapSpace k) : ℂ :=
  osiiSemigroupMixedHilbertPairing OS left right
    (i.splitCoordinatesCLM w)

/-- The natural global-coordinate domain of one Chapter V generator
candidate. -/
def generatorSemigroupDomain
    (i : GeneratorIndex k)
    (U : Set (Fin (i.n - 1) → ℂ))
    (V : Set (Fin (i.m - 1) → ℂ)) :
    Set (OSIITimeGapSpace k) :=
  i.splitCoordinatesCLM ⁻¹'
    bridgedMixedHilbertPairingDomain
      {z : ℂ | 0 < z.re} U V

theorem isOpen_generatorSemigroupDomain
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (generatorSemigroupDomain i U V) := by
  exact
    (isOpen_bridgedMixedHilbertPairingDomain
      (isOpen_lt continuous_const Complex.continuous_re)
      hU hV).preimage
      i.splitCoordinatesCLM.continuous

/-- Convex left and right field domains give a convex Chapter V generator
domain in the original global time-gap coordinates. -/
theorem convex_generatorSemigroupDomain
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : Convex ℝ (conjugateFieldDomain U))
    (hV : Convex ℝ V) :
    Convex ℝ (generatorSemigroupDomain i U V) := by
  change Convex ℝ
    ((i.splitCoordinatesCLM.restrictScalars ℝ).toLinearMap ⁻¹'
      ({z : ℂ | 0 < z.re} ×ˢ conjugateFieldDomain U ×ˢ V))
  exact
    ((convex_halfSpace_re_gt (r := (0 : ℝ))).prod (hU.prod hV)
      ).linear_preimage
        (i.splitCoordinatesCLM.restrictScalars ℝ).toLinearMap

/-- The genuine split-coordinate generator is holomorphic under the original
OS axioms, without an arity-growth hypothesis. -/
theorem differentiableOn_generatorSemigroupPairing
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V)
    {left : (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS}
    {right : (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS}
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (fun w =>
        osiiSemigroupMixedHilbertPairing OS left right
          (i.splitCoordinatesCLM w))
      (generatorSemigroupDomain i U V) := by
  apply DifferentiableOn.comp
    (differentiableOn_osiiSemigroupMixedHilbertPairing
      OS hU hV hleft hright)
  · exact i.splitCoordinatesCLM.differentiable.differentiableOn
  · intro w hw
    exact hw

/-- Holomorphy of the legacy generator wrapper follows from the growth-free
split-coordinate generator theorem. -/
theorem differentiableOn_generatorSemigroupCandidate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V)
    {left : (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS}
    {right : (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS}
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (generatorSemigroupCandidate OS lgc i left right)
      (generatorSemigroupDomain i U V) := by
  change DifferentiableOn ℂ
    (fun w =>
      osiiSemigroupMixedHilbertPairing OS left right
        (i.splitCoordinatesCLM w))
    (generatorSemigroupDomain i U V)
  exact differentiableOn_generatorSemigroupPairing OS i hU hV hleft hright

@[simp]
theorem generatorSemigroupCandidate_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right : (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (w : OSIITimeGapSpace k) :
    generatorSemigroupCandidate OS lgc i left right w =
      @inner ℂ (OSHilbertSpace OS) _
        (left (fun a => -star (w (i.leftGlobalIndex a))))
        (osTimeShiftHilbertComplex OS lgc
          (w i.bridgeGlobalIndex)
          (right (fun b => w (i.rightGlobalIndex b)))) := by
  rfl

end OSIIChapterV
end OSReconstruction
