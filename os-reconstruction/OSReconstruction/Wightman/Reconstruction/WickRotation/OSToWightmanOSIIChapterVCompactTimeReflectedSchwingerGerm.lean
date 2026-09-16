/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedSchwingerGerm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger











open Complex Topology MeasureTheory Set
open scoped Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Consecutive gaps of the reflected chronological product, expressed in
the two original positive-time difference-coordinate blocks. -/
def reflectedChronologicalGapMap
    (k : ℕ)
    (τ : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ)) :
    Fin (k + (k + 1)) → ℝ :=
  fun i =>
    if hleft : i.val < k then
      τ.1 ⟨k - i.val, by omega⟩
    else if hbridge : i.val = k then
      τ.1 0 + τ.2 0
    else
      τ.2 ⟨i.val - k, by omega⟩

theorem continuous_reflectedChronologicalGapMap
    (k : ℕ) :
    Continuous (reflectedChronologicalGapMap k) := by
  apply continuous_pi
  intro i
  by_cases hleft : i.val < k
  · simp only [reflectedChronologicalGapMap, hleft, ↓reduceDIte]
    fun_prop
  · by_cases hbridge : i.val = k
    · simp only [reflectedChronologicalGapMap, hbridge, Nat.lt_irrefl,
        ↓reduceDIte]
      fun_prop
    · simp only [reflectedChronologicalGapMap, hleft, hbridge, ↓reduceDIte]
      fun_prop

/-- Undo the chronological reindexing while retaining the arity-normalized
configuration type at the public boundary. -/
def reflectedChronologicalRawConfig
    (x : NPointDomain d ((k + (k + 1)) + 1)) :
    NPointDomain d ((k + 1) + (k + 1)) :=
  fun i =>
    x (((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega))) i)

omit [NeZero d] in
@[simp] theorem reflectedChronologicalRawConfig_apply
    (x : NPointDomain d ((k + (k + 1)) + 1))
    (i : Fin ((k + 1) + (k + 1))) :
    reflectedChronologicalRawConfig x i =
      x (((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
        (finCongr (by omega))) i) := rfl

/-- The reduced time projection of a chronologically reordered reflected
configuration is exactly `reflectedChronologicalGapMap` applied to the two
positive-time difference-coordinate blocks of the raw configuration. -/
theorem reducedTimeProjection_reflectedChronological_eq_gapMap
    (x : NPointDomain d ((k + (k + 1)) + 1)) :
    reducedTimeProjectionCLM d (k + (k + 1)) x =
      reflectedChronologicalGapMap k
        (section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (timeReflectionN d
                (splitFirst (k + 1) (k + 1)
                  (reflectedChronologicalRawConfig x)))),
          section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (splitLast (k + 1) (k + 1)
                (reflectedChronologicalRawConfig x)))) := by
  ext i
  change x i.succ 0 - x i.castSucc 0 = _
  by_cases hleft : i.val < k
  · let a : Fin (k + 1) := ⟨k - i.val, by omega⟩
    let b : Fin (k + 1) := ⟨k - i.val - 1, by omega⟩
    have ha :
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega)))
            (Fin.castAdd (k + 1) a) = i.castSucc := by
      rw [Equiv.trans_apply,
        osiiAxisPairLeftBlockReversePerm_castAdd]
      ext
      simp [a]
      omega
    have hb :
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega)))
            (Fin.castAdd (k + 1) b) = i.succ := by
      rw [Equiv.trans_apply,
        osiiAxisPairLeftBlockReversePerm_castAdd]
      ext
      simp [b]
      omega
    rw [show i.castSucc =
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega))) (Fin.castAdd (k + 1) a) by
      exact ha.symm]
    rw [show i.succ =
        ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
          (finCongr (by omega))) (Fin.castAdd (k + 1) b) by
      exact hb.symm]
    simp [reflectedChronologicalGapMap, hleft, a, b,
      section43QTime, nPointTimeSpatialCLE,
      timeReflectionN, timeReflection, splitFirst,
      reflectedChronologicalRawConfig]
    have hsub : k - i.val ≠ 0 := by omega
    rw [if_neg hsub]
    ring_nf
    congr 2
    apply Fin.ext
    change
      (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
          (Fin.castAdd (k + 1) a)).val =
        (Fin.castAdd (k + 1) (Fin.rev a)).val
    rw [osiiAxisPairLeftBlockReversePerm_castAdd]
  · by_cases hbridge : i.val = k
    · have hleftIndex :
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.castAdd (k + 1) (0 : Fin (k + 1))) =
            i.castSucc := by
        rw [Equiv.trans_apply,
          osiiAxisPairLeftBlockReversePerm_castAdd]
        ext
        simp [hbridge]
      have hrightIndex :
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.natAdd (k + 1) (0 : Fin (k + 1))) =
            i.succ := by
        rw [Equiv.trans_apply,
          osiiAxisPairLeftBlockReversePerm_natAdd]
        ext
        simp [hbridge]
      rw [show i.castSucc =
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.castAdd (k + 1) (0 : Fin (k + 1))) by
        exact hleftIndex.symm]
      rw [show i.succ =
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.natAdd (k + 1) (0 : Fin (k + 1))) by
        exact hrightIndex.symm]
      simp [reflectedChronologicalGapMap, hbridge,
        section43QTime, nPointTimeSpatialCLE,
        timeReflectionN, timeReflection, splitFirst, splitLast,
        reflectedChronologicalRawConfig]
      ring
    · let a : Fin (k + 1) := ⟨i.val - (k + 1), by omega⟩
      let b : Fin (k + 1) := ⟨i.val - k, by omega⟩
      have ha :
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.natAdd (k + 1) a) = i.castSucc := by
        rw [Equiv.trans_apply,
          osiiAxisPairLeftBlockReversePerm_natAdd]
        ext
        simp [a]
        omega
      have hb :
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega)))
              (Fin.natAdd (k + 1) b) = i.succ := by
        rw [Equiv.trans_apply,
          osiiAxisPairLeftBlockReversePerm_natAdd]
        ext
        simp [b]
        omega
      rw [show i.castSucc =
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega))) (Fin.natAdd (k + 1) a) by
        exact ha.symm]
      rw [show i.succ =
          ((osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
            (finCongr (by omega))) (Fin.natAdd (k + 1) b) by
        exact hb.symm]
      simp [reflectedChronologicalGapMap, hleft, hbridge, a, b,
        section43QTime, nPointTimeSpatialCLE, splitLast,
        reflectedChronologicalRawConfig]
      have hik : k < i.val := by omega
      have hsub : i.val - k ≠ 0 := by omega
      rw [if_neg hsub]
      congr 1

/-- Undoing the chronological reindexing of a mixed reflected source sends
support back into the raw mixed tensor-product support. -/
theorem mixedReflectedChronologicalRawConfig_mem_tsupport
    (f g : SchwartzNPoint d (k + 1))
    {x : NPointDomain d ((k + (k + 1)) + 1)}
    (hx :
      x ∈ tsupport
        ((mixedReflectedChronologicalSource f g :
          SchwartzNPoint d ((k + (k + 1)) + 1)) :
            NPointDomain d ((k + (k + 1)) + 1) → ℂ)) :
    reflectedChronologicalRawConfig x ∈
      tsupport
        (((f.osConjTensorProduct g :
          SchwartzNPoint d ((k + 1) + (k + 1))) :
            NPointDomain d ((k + 1) + (k + 1)) → ℂ)) := by
  let σ : Fin ((k + 1) + (k + 1)) ≃
      Fin ((k + (k + 1)) + 1) :=
    (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega))
  let e :=
    (LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ
      ).toContinuousLinearEquiv
  have hts :=
    tsupport_comp_eq_preimage
      (g := (((f.osConjTensorProduct g :
        SchwartzNPoint d ((k + 1) + (k + 1))) :
        NPointDomain d ((k + 1) + (k + 1)) → ℂ)))
      e.toHomeomorph
  have hx' :
      x ∈ e.toHomeomorph ⁻¹'
        tsupport
          (((f.osConjTensorProduct g :
            SchwartzNPoint d ((k + 1) + (k + 1))) :
            NPointDomain d ((k + 1) + (k + 1)) → ℂ)) := by
    rw [← hts]
    simpa [mixedReflectedChronologicalSource, reindexSchwartz, σ, e,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hx
  have heq : reflectedChronologicalRawConfig x = e x := by
    ext i
    rfl
  rwa [heq]

/-- The compact reduced-time carrier canonically induced by reflecting and
chronologically ordering two source-time carriers. -/
def reflectedChronologicalGapCarrier
    (k : ℕ)
    (K : Set (Fin (k + 1) → ℝ)) :
    Set (Fin (k + (k + 1)) → ℝ) :=
  reflectedChronologicalGapMap k '' (K ×ˢ K)

theorem isCompact_reflectedChronologicalGapCarrier
    {K : Set (Fin (k + 1) → ℝ)}
    (hK_comp : IsCompact K) :
    IsCompact (reflectedChronologicalGapCarrier k K) := by
  exact (hK_comp.prod hK_comp).image
    (continuous_reflectedChronologicalGapMap k)

theorem reflectedChronologicalGapCarrier_positive
    {K : Set (Fin (k + 1) → ℝ)}
    (hK_pos :
      K ⊆ section43TimeStrictPositiveRegion (k + 1)) :
    reflectedChronologicalGapCarrier k K ⊆
      section43TimeStrictPositiveRegion (k + (k + 1)) := by
  rintro _ ⟨τ, hτ, rfl⟩
  intro i
  by_cases hleft : i.val < k
  · simpa [reflectedChronologicalGapMap, hleft] using
      hK_pos hτ.1 (⟨k - i.val, by omega⟩ : Fin (k + 1))
  · by_cases hbridge : i.val = k
    · have hleft_pos := hK_pos hτ.1 (0 : Fin (k + 1))
      have hright_pos := hK_pos hτ.2 (0 : Fin (k + 1))
      simpa [reflectedChronologicalGapMap, hleft, hbridge] using
        add_pos hleft_pos hright_pos
    · simpa [reflectedChronologicalGapMap, hleft, hbridge] using
        hK_pos hτ.2 (⟨i.val - k, by omega⟩ : Fin (k + 1))

/-- Exact carrier control for every mixed reflected chronological source.
Keeping the carrier explicit is what permits later cutoff selection inside a
smaller target-adapted open region. -/
theorem
    mixedReflectedChronologicalSource_reducedTimeProjection_mem_reflectedChronologicalGapCarrier
    {ι : Type*}
    (f : ι → SchwartzNPoint d (k + 1))
    {K : Set (Fin (k + 1) → ℝ)}
    (hfK :
      ∀ a x, x ∈ tsupport
          (f a : NPointDomain d (k + 1) → ℂ) →
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) ∈ K) :
    ∀ (ab : ι × ι) x, x ∈ tsupport
        (mixedReflectedChronologicalSource
          (f ab.1) (f ab.2) :
          NPointDomain d ((k + (k + 1)) + 1) → ℂ) →
      reducedTimeProjectionCLM d (k + (k + 1)) x ∈
        reflectedChronologicalGapCarrier k K := by
  intro ab x hx
  let raw := reflectedChronologicalRawConfig x
  have hxraw :
      raw ∈ tsupport
        (((f ab.1).osConjTensorProduct (f ab.2) :
          SchwartzNPoint d ((k + 1) + (k + 1))) :
            NPointDomain d ((k + 1) + (k + 1)) → ℂ) := by
    exact
      mixedReflectedChronologicalRawConfig_mem_tsupport
        (f ab.1) (f ab.2) hx
  let τleft : Fin (k + 1) → ℝ :=
    section43QTime (d := d) (n := k + 1)
      (section43DiffCoordRealCLE d (k + 1)
        (timeReflectionN d (splitFirst (k + 1) (k + 1) raw)))
  let τright : Fin (k + 1) → ℝ :=
    section43QTime (d := d) (n := k + 1)
      (section43DiffCoordRealCLE d (k + 1)
        (splitLast (k + 1) (k + 1) raw))
  have hτleft : τleft ∈ K := by
    exact hfK ab.1
      (timeReflectionN d (splitFirst (k + 1) (k + 1) raw))
      (osConjTensorProduct_tsupport_reflectedLeft_mem
        (f ab.1) (f ab.2) hxraw)
  have hτright : τright ∈ K := by
    exact hfK ab.2
      (splitLast (k + 1) (k + 1) raw)
      (osConjTensorProduct_tsupport_right_mem
        (f ab.1) (f ab.2) hxraw)
  rw [reducedTimeProjection_reflectedChronological_eq_gapMap]
  exact ⟨(τleft, τright), ⟨hτleft, hτright⟩, rfl⟩

omit [NeZero d] in
/-- The normalized reflected absolute displacement depends continuously on
the Chapter V source parameters. -/
theorem continuous_reflectedReducedAbsoluteDisplacement :
    Continuous
      (reflectedReducedAbsoluteDisplacement (d := d) :
        (Fin (k + k) → ℝ) →
          NPointDomain d ((k + (k + 1)) + 1)) := by
  let Labs :=
    reflectedSourceParameterDisplacementCLM
      (fun r : Fin k =>
        chronologicalTimeSourceDirection (d := d) r)
  apply continuous_pi
  intro j
  exact
    (continuous_apply
      (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
        ((finCongr (by omega)).symm j))).comp Labs.continuous

omit [NeZero d] in
@[simp] theorem reflectedReducedAbsoluteDisplacement_zero :
    reflectedReducedAbsoluteDisplacement (d := d)
        (0 : Fin (k + k) → ℝ) =
      0 := by
  ext j μ
  change
    reflectedSourceParameterDisplacementCLM
        (fun r : Fin k =>
          chronologicalTimeSourceDirection (d := d) r) 0
        (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
          ((finCongr (by omega)).symm j)) μ =
      0
  rw [map_zero]
  rfl

/-- Common reduced-Schwinger data for every mixed pair in a uniformly
compact positive-time source family. This is the scalar real-edge package
needed by pairwise Hilbert Gram kernels. -/
structure UniformCompactTimeMixedReflectedSourceFamilyData
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (k + 1)) where
  η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ
  η_support :
    tsupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion (k + (k + 1))
  η_compact :
    HasCompactSupport (η : (Fin (k + (k + 1)) → ℝ) → ℂ)
  /-- The common cutoff is chosen from a unit-interval-valued smooth bump.
  This chart-independent normalization is the quantitative invariant used by
  the VI.2 weighted-source envelope. -/
  η_seminorm_zero_le_one : SchwartzMap.seminorm ℂ 0 0 η ≤ 1
  W : SchwartzNPoint d (k + (k + 1)) →L[ℂ] ℂ
  W_eq_canonical :
    W =
      canonicalReducedTimeCutoffSchwingerCLM OS η η_support
  cutoff :
    ∀ a b,
      SchwartzMap.smulLeftCLM ℂ
          (section43NPointTimeCutoffWeight d (k + (k + 1)) η)
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource (f a).1 (f b).1)) =
        diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource (f a).1 (f b).1)
  cutoff_one_on :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ ab : ι × ι,
        ∀ x ∈ tsupport
            (translateSchwartzConfiguration
              (reflectedReducedAbsoluteDisplacement (d := d) u)
              (mixedReflectedChronologicalSource
                (f ab.1).1 (f ab.2).1) :
              NPointDomain d ((k + (k + 1)) + 1) → ℂ),
          reducedTimeCutoffWeight (d := d) η x = 1
  realEdgeUniform :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ a b,
        W (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d)
            (reflectedReducedTimeDisplacement u))
          (diffVarReduction d (k + (k + 1))
            (mixedReflectedChronologicalSource (f a).1 (f b).1))) =
          OS.S ((k + 1) + (k + 1))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin k =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f a).1.osConjTensorProduct (f b).1)))

/-- Uniform compact strict-positive support keeps all sufficiently small
translated mixed reflected products away from the coincidence locus. -/
theorem
    eventually_mixedReflectedRawTranslation_vanishes_of_uniformCompactTimeSupport
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (k + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1)) :
    ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
      ∀ ab : ι × ι,
        VanishesToInfiniteOrderOnCoincidence
          (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM
              (fun r : Fin k =>
                chronologicalTimeSourceDirection (d := d) r) u)
            ((f ab.1).1.osConjTensorProduct (f ab.2).1)) := by
  obtain ⟨ε, _hε, _hχ_growth, hχ_disj, _hχ_base, hχ_local⟩ :=
    exists_twoBlockTimeMarginCutoff_one_on_mixedReflectedTranslation_family_germ
      (fun a => (f a).1) hf
  filter_upwards [hχ_local] with u hu
  intro ab
  let rawDisplacement :=
    reflectedSourceParameterDisplacementCLM
      (fun r : Fin k =>
        chronologicalTimeSourceDirection (d := d) r)
  let raw : SchwartzNPoint d ((k + 1) + (k + 1)) :=
    translateSchwartzConfiguration
      (rawDisplacement u)
      ((f ab.1).1.osConjTensorProduct (f ab.2).1)
  have hraw_disj :
      Disjoint
        (tsupport
          (raw : NPointDomain d ((k + 1) + (k + 1)) → ℂ))
        (CoincidenceLocus d ((k + 1) + (k + 1))) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hχx :
        osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1 :=
      hu ab.1 ab.2 x (by simpa [raw, rawDisplacement] using hx)
    have hx_support :
        x ∈ tsupport
          (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε) := by
      apply subset_closure
      simp only [Function.mem_support]
      rw [hχx]
      exact one_ne_zero
    exact Set.disjoint_left.mp hχ_disj hx_support hcoin
  exact
    (VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      (f := raw) hraw_disj : _)

/-- Construct the ordinary mixed reflected germ while retaining support in a
prescribed open region containing the exact reflected source carrier. -/
theorem
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (k + 1))
    (K : Set (Fin (k + 1) → ℝ))
    (hK_comp : IsCompact K)
    (hK_pos :
      K ⊆ section43TimeStrictPositiveRegion (k + 1))
    (hfK :
      ∀ a x, x ∈ tsupport
          ((f a).1 : NPointDomain d (k + 1) → ℂ) →
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) ∈ K)
    (O : Set (Fin (k + (k + 1)) → ℝ))
    (hO_open : IsOpen O)
    (hO_positive :
      O ⊆ section43TimeStrictPositiveRegion (k + (k + 1)))
    (hcarrierO :
      reflectedChronologicalGapCarrier k K ⊆ O) :
    ∃ G : UniformCompactTimeMixedReflectedSourceFamilyData OS f,
      tsupport
          (G.η : (Fin (k + (k + 1)) → ℝ) → ℂ) ⊆ O := by
  let hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1) :=
    ⟨K, hK_comp, hK_pos, hfK⟩
  let reflected :
      ι × ι → SchwartzNPoint d ((k + (k + 1)) + 1) :=
    fun ab =>
      mixedReflectedChronologicalSource (f ab.1).1 (f ab.2).1
  obtain ⟨η, hη, hηO, hη_comp, hη_bound, V, hV, hrecover⟩ :=
    exists_unitBoundedCanonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ_of_compactCarrier_subset_open
      OS reflected
      (reflectedChronologicalGapCarrier k K)
      (isCompact_reflectedChronologicalGapCarrier hK_comp)
      (mixedReflectedChronologicalSource_reducedTimeProjection_mem_reflectedChronologicalGapCarrier
        (fun a => (f a).1) hfK)
      O hO_open hO_positive hcarrierO
      (reflectedReducedAbsoluteDisplacement (d := d))
      continuous_reflectedReducedAbsoluteDisplacement
      reflectedReducedAbsoluteDisplacement_zero
  obtain ⟨ε, hε, _hχ_growth, hχ_disj, _hχ_base, hχ_local⟩ :=
    exists_twoBlockTimeMarginCutoff_one_on_mixedReflectedTranslation_family_germ
      (fun a => (f a).1) hf
  have hzeroV : (0 : Fin (k + k) → ℝ) ∈ V :=
    mem_of_mem_nhds hV
  refine ⟨{
    η := η
    η_support := hη
    η_compact := hη_comp
    η_seminorm_zero_le_one := hη_bound
    W := canonicalReducedTimeCutoffSchwingerCLM OS η hη
    W_eq_canonical := rfl
    cutoff := ?_
    cutoff_one_on := ?_
    realEdgeUniform := ?_ }, hηO⟩
  · intro a b
    have hcutoff := (hrecover (a, b) 0 hzeroV).1
    have htranslate_zero :
        translateSchwartzConfiguration
            (reflectedReducedAbsoluteDisplacement (d := d)
              (0 : Fin (k + k) → ℝ))
            (reflected (a, b)) =
          reflected (a, b) := by
      rw [reflectedReducedAbsoluteDisplacement_zero]
      ext x
      simp
    rw [htranslate_zero] at hcutoff
    simpa [reflected] using hcutoff
  · filter_upwards [hV] with u hu
    intro ab x hx
    exact (hrecover ab u hu).2.2 x (by simpa [reflected] using hx)
  · filter_upwards [hV, hχ_local] with u huV huRaw
    intro a b
    let rawDisplacement :=
      reflectedSourceParameterDisplacementCLM
        (fun r : Fin k =>
          chronologicalTimeSourceDirection (d := d) r)
    let raw : SchwartzNPoint d ((k + 1) + (k + 1)) :=
      translateSchwartzConfiguration
        (rawDisplacement u)
        ((f a).1.osConjTensorProduct (f b).1)
    have hraw_disj :
        Disjoint
          (tsupport
            (raw : NPointDomain d ((k + 1) + (k + 1)) → ℂ))
          (CoincidenceLocus d ((k + 1) + (k + 1))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hcoin
      have hχx :
          osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1 :=
        huRaw a b x (by simpa [raw, rawDisplacement] using hx)
      have hx_support :
          x ∈ tsupport
            (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε) := by
        apply subset_closure
        simp only [Function.mem_support]
        rw [hχx]
        exact one_ne_zero
      exact Set.disjoint_left.mp hχ_disj hx_support hcoin
    have hraw_zero : VanishesToInfiniteOrderOnCoincidence raw :=
      VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
        (f := raw) hraw_disj
    have hnormalized := (hrecover (a, b) u huV).2.1
    rw [translate_diffVarReduction_reflectedReducedTimeDisplacement]
    exact hnormalized.trans
      (mixedReflectedChronologicalSource_schwinger_eq_raw
        OS u (f a).1 (f b).1
        (by simpa [raw, rawDisplacement] using hraw_zero))

/-- Uniform compact strict-positive support constructs one common reflected
reduced cutoff, reduced Schwinger functional, and scalar real-edge
neighborhood for all mixed source pairs. -/
theorem exists_uniformCompactTimeMixedReflectedSourceFamilyData
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (k + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1)) :
    Nonempty (UniformCompactTimeMixedReflectedSourceFamilyData OS f) := by
  obtain ⟨K, hK_comp, hK_pos, hfK⟩ := hf
  obtain ⟨G, _hG_support⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData_of_sourceCarrier_subset_open
      OS f K hK_comp hK_pos hfK
      (section43TimeStrictPositiveRegion (k + (k + 1)))
      (isOpen_section43TimeStrictPositiveRegion (k + (k + 1)))
      Set.Subset.rfl
      (reflectedChronologicalGapCarrier_positive hK_pos)
  exact ⟨G⟩

end OSIIChapterV
end OSReconstruction
