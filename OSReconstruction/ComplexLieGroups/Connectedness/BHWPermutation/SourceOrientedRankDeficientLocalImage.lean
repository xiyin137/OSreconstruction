import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTransport

/-!
# Rank-deficient oriented local-image packets

This file records the topology interface expected from the rank-deficient
Schur/residual normal-form construction.  The hard algebraic construction must
produce one of these packets; the lemma here extracts the connected relatively
open patch needed by the oriented local-basis dispatcher.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Local-image data for a rank-deficient point of the oriented source
variety.  The parameter space is intentionally abstract: the planned producer
will instantiate it with the finite Schur head/mixed/tail parameter box. -/
structure SourceOrientedRankDeficientVarietyLocalImageData
    {P : Type*} [TopologicalSpace P]
    (G0 : SourceOrientedGramData d n)
    (N0 : Set (SourceOrientedGramData d n)) where
  parameterBox : Set P
  parameterBox_open : IsOpen parameterBox
  parameterBox_connected : IsConnected parameterBox
  p0 : P
  p0_mem : p0 ∈ parameterBox
  image : P → SourceOrientedGramData d n
  image_continuousOn : ContinuousOn image parameterBox
  center_eq : image p0 = G0
  image_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n (image '' parameterBox)
  image_sub :
    image '' parameterBox ⊆ N0 ∩ sourceOrientedGramVariety d n

/-- Strengthened rank-deficient local-image data for the max-rank
connectedness assembly.  The old packet produces a connected relatively open
rank-deficient neighborhood; this one additionally records that the same
image has connected intersection with the maximal-rank stratum. -/
structure SourceOrientedRankDeficientMaxRankLocalImageData
    {P : Type*} [TopologicalSpace P]
    (G0 : SourceOrientedGramData d n)
    (N0 : Set (SourceOrientedGramData d n)) where
  parameterBox : Set P
  parameterBox_open : IsOpen parameterBox
  parameterBox_connected : IsConnected parameterBox
  p0 : P
  p0_mem : p0 ∈ parameterBox
  image : P → SourceOrientedGramData d n
  image_continuousOn : ContinuousOn image parameterBox
  center_eq : image p0 = G0
  image_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n (image '' parameterBox)
  image_sub :
    image '' parameterBox ⊆ N0 ∩ sourceOrientedGramVariety d n
  image_maxRank_connected :
    IsConnected ((image '' parameterBox) ∩
      {G | SourceOrientedMaxRankAt d n G})

/-- Transport connectedness from a parameter-space max-rank slice to the
max-rank part of a source-oriented local image.  The concrete Schur/residual
producer is expected to prove the displayed image equality from its rank
formula. -/
theorem isConnected_image_inter_sourceOrientedMaxRank_of_parameter_slice
    {P : Type*} [TopologicalSpace P]
    {parameterBox parameterMaxRank : Set P}
    {image : P → SourceOrientedGramData d n}
    (hparameter_sub : parameterMaxRank ⊆ parameterBox)
    (hparameter_conn : IsConnected parameterMaxRank)
    (himage_eq :
      image '' parameterMaxRank =
        (image '' parameterBox) ∩ {G | SourceOrientedMaxRankAt d n G})
    (himage_cont : ContinuousOn image parameterBox) :
    IsConnected
      ((image '' parameterBox) ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  rw [← himage_eq]
  exact hparameter_conn.image image (himage_cont.mono hparameter_sub)

/-- The max-rank part of a parameterized source-oriented image is the image of
the parameter subset on which the image point is max-rank. -/
theorem image_inter_preimage_sourceOrientedMaxRank_eq
    {P : Type*}
    {parameterBox : Set P}
    {image : P → SourceOrientedGramData d n} :
    image '' (parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (image p)}) =
      (image '' parameterBox) ∩
        {G | SourceOrientedMaxRankAt d n G} := by
  ext G
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨⟨p, hp, rfl⟩, hpmax⟩
    exact ⟨p, ⟨hp, hpmax⟩, rfl⟩

/-- Transport connectedness from the concrete preimage of the max-rank stratum
inside a parameter box to the max-rank part of the image. -/
theorem isConnected_image_inter_sourceOrientedMaxRank_of_connected_preimage
    {P : Type*} [TopologicalSpace P]
    {parameterBox : Set P}
    {image : P → SourceOrientedGramData d n}
    (hparameter_conn :
      IsConnected (parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (image p)}))
    (himage_cont : ContinuousOn image parameterBox) :
    IsConnected
      ((image '' parameterBox) ∩ {G | SourceOrientedMaxRankAt d n G}) :=
  isConnected_image_inter_sourceOrientedMaxRank_of_parameter_slice
    (d := d) (n := n)
    (by intro p hp; exact hp.1)
    hparameter_conn
    (image_inter_preimage_sourceOrientedMaxRank_eq (d := d) (n := n))
    himage_cont

namespace SourceOrientedRankDeficientVarietyLocalImageData

/-- Build the ambient local-image packet from a subtype-valued local image on
the oriented source variety.  This is the preferred adapter for source-change
normal forms, whose inverse transport is only available on
`SourceOrientedVariety d n`. -/
def ofSubtype
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox : Set P}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    {p0 : P}
    (p0_mem : p0 ∈ parameterBox)
    {imageV : P → SourceOrientedVariety d n}
    (imageV_continuousOn : ContinuousOn imageV parameterBox)
    (center_eq : (imageV p0).1 = G0)
    (imageV_open : IsOpen (imageV '' parameterBox))
    (imageV_sub :
      sourceOrientedVarietyUnderlyingSet d n (imageV '' parameterBox) ⊆
        N0 ∩ sourceOrientedGramVariety d n) :
    SourceOrientedRankDeficientVarietyLocalImageData
      (d := d) (n := n) (P := P) G0 N0 where
  parameterBox := parameterBox
  parameterBox_open := parameterBox_open
  parameterBox_connected := parameterBox_connected
  p0 := p0
  p0_mem := p0_mem
  image := fun p => (imageV p).1
  image_continuousOn := continuous_subtype_val.comp_continuousOn imageV_continuousOn
  center_eq := center_eq
  image_relOpen := by
    rw [← sourceOrientedVarietyUnderlyingSet_image (d := d) (n := n)
      imageV parameterBox]
    exact sourceOrientedVarietyUnderlyingSet_relOpen_of_isOpen imageV_open
  image_sub := by
    rw [← sourceOrientedVarietyUnderlyingSet_image (d := d) (n := n)
      imageV parameterBox]
    exact imageV_sub

/-- A rank-deficient local-image packet yields the connected relatively open
patch required by the oriented local-basis theorem. -/
theorem to_connectedRelOpenPatch
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    (R :
      SourceOrientedRankDeficientVarietyLocalImageData
        (d := d) (n := n) (P := P) G0 N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  refine ⟨R.image '' R.parameterBox, ?_, R.image_relOpen, ?_, R.image_sub⟩
  · exact ⟨R.p0, R.p0_mem, R.center_eq⟩
  · exact R.parameterBox_connected.image R.image R.image_continuousOn

/-- A connected rank-deficient local-image packet upgrades to the strengthened
max-rank packet once the concrete producer proves connectedness of the
max-rank preimage in parameter space. -/
def to_maxRankLocalImageData_of_connected_preimage
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    (R :
      SourceOrientedRankDeficientVarietyLocalImageData
        (d := d) (n := n) (P := P) G0 N0)
    (hpreimage_connected :
      IsConnected (R.parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (R.image p)})) :
    SourceOrientedRankDeficientMaxRankLocalImageData
      (d := d) (n := n) (P := P) G0 N0 where
  parameterBox := R.parameterBox
  parameterBox_open := R.parameterBox_open
  parameterBox_connected := R.parameterBox_connected
  p0 := R.p0
  p0_mem := R.p0_mem
  image := R.image
  image_continuousOn := R.image_continuousOn
  center_eq := R.center_eq
  image_relOpen := R.image_relOpen
  image_sub := R.image_sub
  image_maxRank_connected :=
    isConnected_image_inter_sourceOrientedMaxRank_of_connected_preimage
      (d := d) (n := n) hpreimage_connected R.image_continuousOn

end SourceOrientedRankDeficientVarietyLocalImageData

namespace SourceOrientedRankDeficientMaxRankLocalImageData

/-- Build the strengthened max-rank local-image packet from a subtype-valued
local image, once the concrete producer proves connectedness of the max-rank
preimage in parameter space. -/
def ofSubtype
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox : Set P}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    {p0 : P}
    (p0_mem : p0 ∈ parameterBox)
    {imageV : P → SourceOrientedVariety d n}
    (imageV_continuousOn : ContinuousOn imageV parameterBox)
    (center_eq : (imageV p0).1 = G0)
    (imageV_open : IsOpen (imageV '' parameterBox))
    (imageV_sub :
      sourceOrientedVarietyUnderlyingSet d n (imageV '' parameterBox) ⊆
        N0 ∩ sourceOrientedGramVariety d n)
    (hpreimage_connected :
      IsConnected (parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (imageV p).1})) :
    SourceOrientedRankDeficientMaxRankLocalImageData
      (d := d) (n := n) (P := P) G0 N0 :=
  (SourceOrientedRankDeficientVarietyLocalImageData.ofSubtype
      (d := d) (n := n) parameterBox_open parameterBox_connected p0_mem
      imageV_continuousOn center_eq imageV_open imageV_sub)
    |>.to_maxRankLocalImageData_of_connected_preimage hpreimage_connected

/-- A strengthened rank-deficient local-image packet yields the exact
exceptional local basis patch consumed by max-rank connectedness assembly. -/
theorem to_connectedMaxRankPatch
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    (R :
      SourceOrientedRankDeficientMaxRankLocalImageData
        (d := d) (n := n) (P := P) G0 N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n ∧
      IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  refine
    ⟨R.image '' R.parameterBox, ?_, R.image_relOpen, R.image_sub,
      R.image_maxRank_connected⟩
  exact ⟨R.p0, R.p0_mem, R.center_eq⟩

end SourceOrientedRankDeficientMaxRankLocalImageData

/-- A producer of rank-deficient local-image packets is exactly the
rank-deficient patch producer expected by the local-basis dispatcher. -/
theorem sourceOrientedRankDeficientPatchAt_of_localImageProducer
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hex : SourceOrientedExceptionalRank d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  rcases rankDeficientLocalImageAt hG0 hex hN0_open hG0N0 with
    ⟨P, instP, R⟩
  letI : TopologicalSpace P := instP
  exact R.to_connectedRelOpenPatch

/-- A producer of strengthened rank-deficient local-image packets supplies the
exceptional local basis input for the max-rank connectedness assembly.  The
relative-open target `U` is handled by first replacing the requested ambient
neighborhood with a smaller ambient open set whose variety slice lies in
`U`. -/
theorem sourceOrientedRankDeficientConnectedMaxRankPatchAt_of_localImageProducer
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientMaxRankLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {U : Set (SourceOrientedGramData d n)}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    {G0 : SourceOrientedGramData d n}
    (hG0U : G0 ∈ U)
    (hex : SourceOrientedExceptionalRank d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      V ⊆ U ∩ N0 ∧
      IsConnected (V ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  have hG0U0 : G0 ∈ U0 := by
    have h := hG0U
    rw [hU_eq] at h
    exact h.1
  have hG0var : G0 ∈ sourceOrientedGramVariety d n := by
    have h := hG0U
    rw [hU_eq] at h
    exact h.2
  let Nsmall : Set (SourceOrientedGramData d n) := U0 ∩ N0
  have hNsmall_open : IsOpen Nsmall := hU0_open.inter hN0_open
  have hG0Nsmall : G0 ∈ Nsmall := ⟨hG0U0, hG0N0⟩
  rcases rankDeficientLocalImageAt
      (G0 := G0) hG0var hex
      (N0 := Nsmall) hNsmall_open hG0Nsmall with
    ⟨P, instP, R⟩
  letI : TopologicalSpace P := instP
  rcases R.to_connectedMaxRankPatch with
    ⟨V, hG0V, hV_rel, hV_sub, hVmax_conn⟩
  refine ⟨V, hG0V, hV_rel, ?_, hVmax_conn⟩
  intro G hGV
  rcases hV_sub hGV with ⟨hGNsmall, hGvar⟩
  exact ⟨by simpa [hU_eq] using ⟨hGNsmall.1, hGvar⟩, hGNsmall.2⟩

end BHW
