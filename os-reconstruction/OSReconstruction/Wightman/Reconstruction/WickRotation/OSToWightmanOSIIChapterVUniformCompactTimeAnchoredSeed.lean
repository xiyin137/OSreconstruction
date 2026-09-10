import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedAnchoredCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedHilbertGram

/-!
# Uniform compact-time anchored reflected-Gram seeds

The source-indexed Cauchy continuation has a genuine unitary gauge ambiguity
unless the initial source family is rich enough to anchor every Taylor
coefficient.  An arbitrary list of sources is not rich enough.

This file uses the natural source universe: all positive-time sources whose
difference-time support is carried by one fixed compact positive set.  That
space is a complex submodule and is closed under every normalized
chronological derivative used in the Taylor construction.  Consequently all
finite Taylor polynomials, and hence their locally uniform limits, lie in the
closed span of the zero-anchor source vectors.  The concrete mixed-Gram seed
therefore instantiates the anchored coherence contract without an additional
hypothesis.
-/

noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Positive-time sources whose difference-time support is carried by one
fixed set. -/
def uniformCompactTimeSourceSubmodule
    (d n : ℕ) [NeZero d]
    (K : Set (Fin n → ℝ)) :
    Submodule ℂ (euclideanPositiveTimeSubmodule (d := d) n) where
  carrier := {f |
    ∀ x ∈ tsupport (f.1 : NPointDomain d n → ℂ),
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n x) ∈ K}
  zero_mem' := by
    intro x hx
    simp at hx
  add_mem' := by
    intro f g hf hg x hx
    have hx' :=
      tsupport_add
        ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        ((g.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        hx
    exact hx'.elim (hf x) (hg x)
  smul_mem' := by
    intro c f hf x hx
    apply hf x
    exact
      tsupport_smul_subset_right
        (fun _ : NPointDomain d n => c)
        ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        hx

/-- The source index used for an anchored compact-time Taylor family. -/
abbrev UniformCompactTimeSource
    (d n : ℕ) [NeZero d]
    (K : Set (Fin n → ℝ)) :=
  uniformCompactTimeSourceSubmodule d n K

namespace UniformCompactTimeSource

variable {d n : ℕ} [NeZero d]
variable {K : Set (Fin n → ℝ)}

/-- Forget the fixed-carrier proof and retain the positive-time source. -/
def source
    (a : UniformCompactTimeSource d n K) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  a.1

/-- The universal fixed-carrier source family has uniform compact
strict-positive difference-time support. -/
theorem hasUniformCompactStrictPositiveDifferenceTimeSupport
    (hK_compact : IsCompact K)
    (hK_positive : K ⊆ section43TimeStrictPositiveRegion n) :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun a : UniformCompactTimeSource d n K =>
        (UniformCompactTimeSource.source a).1) := by
  exact
    ⟨K, hK_compact, hK_positive,
      fun a x hx => a.2 x hx⟩

/-- Normalized source Taylor derivatives remain in the same fixed carrier. -/
def normalizedDerivative
    {k : ℕ}
    (directions : Fin k → NPointDomain d n)
    (α : Fin k → ℕ)
    (a : UniformCompactTimeSource d n K) :
    UniformCompactTimeSource d n K := by
  refine
    ⟨(PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
        (UniformCompactTimeSource.source a) directions).coefficient α, ?_⟩
  intro x hx
  apply a.2 x
  exact
    (tsupport_normalizedSourceMultiDerivative_subset
      directions α (UniformCompactTimeSource.source a).1) (by
        simpa [PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives,
          source] using hx)

@[simp] theorem normalizedDerivative_source
    {k : ℕ}
    (directions : Fin k → NPointDomain d n)
    (α : Fin k → ℕ)
    (a : UniformCompactTimeSource d n K) :
    UniformCompactTimeSource.source
        (normalizedDerivative directions α a) =
      (PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
        (UniformCompactTimeSource.source a) directions).coefficient α :=
  rfl

end UniformCompactTimeSource

namespace UniformCompactTimeSourceHilbertFieldFamilyData

variable {d q : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Every compact-time Hilbert Taylor field is anchored at zero by its
underlying positive-time OS vector. -/
theorem field_zero_eq_source
    {ι : Type*}
    (f : ι →
      euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS f)
    (a : ι) :
    H.field a 0 =
      osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1) (f a) := by
  let T :=
    PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
      (f a)
      (fun r : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) r)
  have hzero :
      (0 : Fin (q + 1) → ℂ) ∈
        SCV.Polydisc
          (0 : Fin (q + 1) → ℂ)
          (fun _ => H.radius) :=
    SCV.center_mem_polydisc (fun _ => H.radius_pos)
  have h :=
    T.limit_zero_eq_source OS (H.field a)
      (SCV.Polydisc
        (0 : Fin (q + 1) → ℂ)
        (fun _ => H.radius))
      hzero (by simpa [T] using H.taylor a)
  simpa [T, PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives] using h

variable
  {K : Set (Fin ((q + 1) + 1) → ℝ)}

/-- Every finite Taylor polynomial for the universal fixed-carrier family is
in the algebraic span of the zero-anchor source vectors. -/
theorem partialSum_mem_sourceAnchorSpan
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS
      (fun a : UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a))
    (a : UniformCompactTimeSource d ((q + 1) + 1) K)
    (N : ℕ)
    (z : Fin (q + 1) → ℂ) :
    (PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
        (UniformCompactTimeSource.source a)
        (fun r : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) r)).partialSum
      OS N z ∈
        sourceAnchorSpan (fun b => H.field b 0) := by
  rw [PositiveTimeSourceTaylorFamily.partialSum]
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  let b : UniformCompactTimeSource d ((q + 1) + 1) K :=
    UniformCompactTimeSource.normalizedDerivative
      (fun r : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) r)
      α a
  refine ⟨b, ?_⟩
  simpa [b] using
    field_zero_eq_source
      (OS := OS)
      (fun c : UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source c)
      H b

/-- The locally uniform Taylor limit for every fixed-carrier source remains
in the closed span of the zero-anchor source vectors. -/
theorem field_mem_sourceAnchorSpan
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS
      (fun a : UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a))
    (a : UniformCompactTimeSource d ((q + 1) + 1) K)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ)
        (fun _ => H.radius)) :
    H.field a z ∈ sourceAnchorSpan (fun b => H.field b 0) := by
  apply
    (Submodule.isClosed_topologicalClosure
      (Submodule.span ℂ
        (Set.range fun b => H.field b 0))).mem_of_tendsto
      ((H.taylor a).tendsto_at hz)
  exact
    Filter.Eventually.of_forall fun N =>
      partialSum_mem_sourceAnchorSpan H a N z

end UniformCompactTimeSourceHilbertFieldFamilyData

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) → ℝ)}

/-- The concrete compact-time reflected-Gram seed over the universal
fixed-carrier source family carries the anchored coherence contract at the
zero Taylor basepoint. -/
noncomputable def toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a)
      stage germ) :
    SourceIndexedAnchoredReflectedGramHilbertFieldData
      (fun a b => (G.cauchy a b).scalar)
      (0 : Fin (q + 1) → ℂ)
      (fun a => G.hilbert.field a 0)
      (G.toInitialSourceIndexedReflectedGramHilbertFieldData
        OS
        (fun a : UniformCompactTimeSource d ((q + 1) + 1) K =>
          UniformCompactTimeSource.source a)
        stage germ) := by
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K →
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  let P :=
    G.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS f stage germ
  apply
    SourceIndexedAnchoredReflectedGramHilbertFieldData.ofAnchor
      P (0 : Fin (q + 1) → ℂ)
  · change
      (0 : Fin (q + 1) → ℂ) ∈
        SCV.Polydisc
          (0 : Fin (q + 1) → ℂ)
          (fun _ => G.gramRadius)
    exact SCV.center_mem_polydisc (fun _ => G.gramRadius_pos)
  · intro b z hz
    apply
      UniformCompactTimeSourceHilbertFieldFamilyData.field_mem_sourceAnchorSpan
        G.hilbert b z
    exact
      SCV.polydisc_mono
        (fun _ => le_of_lt G.gramRadius_lt_hilbert)
        hz

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
