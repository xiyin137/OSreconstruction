/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedSources
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReflectedA0Factorization










noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace Section43ProductTimeApproximateIdentity

/-- A normalized product approximate-identity test is nonzero at some point
at every scale. -/
theorem exists_test_ne_zero
    {n : Nat}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : Nat) :
    ∃ x, I.test N x ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : I.test N = 0 := by
    ext x
    exact h x
  have hone := I.integral_one N
  change (∫ x : Fin n → Real, I.test N x) = 1 at hone
  rw [hzero] at hone
  simp at hone

/-- Every nonzero spatial factor produces a nonzero translated full source
point whose difference-time coordinate lies within the packet radius of the
anchor. -/
theorem exists_translatedPositiveTimeSpatialSource_ne_zero
    {d n : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity n)
    (tau : Fin n → Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion n)
    (chi : SchwartzMap (Section43SpatialSpace d n) Complex)
    (hchi : chi ≠ 0)
    (N : Nat) :
    ∃ y : NPointDomain d n,
      (I.translatedPositiveTimeSpatialSource tau htau chi N).1 y ≠ 0 ∧
        dist
          (section43QTime d n (section43DiffCoordRealCLE d n y)) tau <
            I.radius N := by
  obtain ⟨x, hx⟩ := I.exists_test_ne_zero N
  obtain ⟨q, hq⟩ : ∃ q, chi q ≠ 0 := by
    by_contra h
    push Not at h
    apply hchi
    ext q
    exact h q
  let xi : NPointDomain d n :=
    (nPointTimeSpatialCLE (d := d) n).symm (tau + x, q)
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm xi
  refine ⟨y, ?_, ?_⟩
  · simp only [translatedPositiveTimeSpatialSource_coe,
      section43OrderedPullbackTimeSpatialTensorCLM_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      section43NPointTimeSpatialTensor_apply]
    rw [show section43DiffCoordRealCLE d n y = xi by
      exact (section43DiffCoordRealCLE d n).apply_symm_apply xi]
    have hsplit :
        (nPointTimeSpatialCLE (d := d) n) xi = (tau + x, q) :=
      (nPointTimeSpatialCLE (d := d) n).apply_symm_apply (tau + x, q)
    have htime : section43QTime d n xi = tau + x := by
      exact congrArg Prod.fst hsplit
    have hspatial : section43QSpatial d n xi = q := by
      exact congrArg Prod.snd hsplit
    rw [htime, hspatial, SCV.translateSchwartz_apply]
    have hadd : tau + x + -tau = x := by abel
    rw [hadd]
    exact mul_ne_zero hx hq
  · rw [show section43DiffCoordRealCLE d n y = xi by
      exact (section43DiffCoordRealCLE d n).apply_symm_apply xi]
    have hsplit :
        (nPointTimeSpatialCLE (d := d) n) xi = (tau + x, q) :=
      (nPointTimeSpatialCLE (d := d) n).apply_symm_apply (tau + x, q)
    have htime : section43QTime d n xi = tau + x := by
      exact congrArg Prod.fst hsplit
    rw [htime, dist_eq_norm]
    have hsupp :
        x ∈ Function.support (I.test N : (Fin n → Real) → Complex) := by
      simpa [Function.mem_support] using hx
    have hradius := I.support N hsupp
    rw [Metric.mem_ball, dist_zero_right] at hradius
    simpa using hradius

end Section43ProductTimeApproximateIdentity

/-- A fixed nonzero spatial Schwartz test at every particle arity. -/
noncomputable def equation621NonzeroSpatialTest
    (d n : Nat) [NeZero d] :
    SchwartzMap (Section43SpatialSpace d n) Complex :=
  (section43SpatialSchwartzParticleCLE d n).symm
    (SchwartzMap.productTensor fun _ : Fin n =>
      (normalizedSpatialBasepointCutoff d).toSchwartz)

theorem equation621NonzeroSpatialTest_ne_zero
    (d n : Nat) [NeZero d] :
    equation621NonzeroSpatialTest d n ≠ 0 := by
  let rho := (normalizedSpatialBasepointCutoff d).toSchwartz
  obtain ⟨x, hx⟩ : ∃ x, rho x ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : rho = 0 := by
      ext x
      exact h x
    have hone := (normalizedSpatialBasepointCutoff d).integral_eq_one
    rw [show (normalizedSpatialBasepointCutoff d).toSchwartz = rho by rfl,
      hzero] at hone
    simp at hone
  intro hzero
  have hforward := congrArg
    (fun chi => section43SpatialSchwartzParticleCLE d n chi) hzero
  have hproduct :
      SchwartzMap.productTensor (fun _ : Fin n => rho) = 0 := by
    simpa [equation621NonzeroSpatialTest, rho] using hforward
  have hvalue := congrArg
    (fun chi : SchwartzMap (Fin n → Fin d → Real) Complex =>
      chi (fun _ => x)) hproduct
  simp only [SchwartzMap.productTensor_apply, SchwartzMap.zero_apply] at hvalue
  exact (Finset.prod_ne_zero_iff.mpr fun _i _hi => hx) hvalue

/-- Chronologically reorder the raw reflected pair of two absolute source
configurations. -/
def equation621MixedChronologicalConfigOfPair
    (d k : Nat)
    (p : NPointDomain d (k + 1) × NPointDomain d (k + 1)) :
    NPointDomain d ((k + (k + 1)) + 1) :=
  let sigma : Fin ((k + 1) + (k + 1)) ≃
      Fin ((k + (k + 1)) + 1) :=
    (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)).trans
      (finCongr (by omega))
  fun j => Fin.append (timeReflectionN d p.1) p.2 (sigma.symm j)

theorem reflectedChronologicalRawConfig_equation621MixedConfig
    {d k : Nat}
    (yLeft yRight : NPointDomain d (k + 1)) :
    reflectedChronologicalRawConfig
        (equation621MixedChronologicalConfigOfPair d k (yLeft, yRight)) =
      Fin.append (timeReflectionN d yLeft) yRight := by
  funext i
  simp [reflectedChronologicalRawConfig,
    equation621MixedChronologicalConfigOfPair]

theorem mixedReflectedChronologicalSource_equation621MixedConfig_apply
    {d k : Nat} [NeZero d]
    (f g : SchwartzNPoint d (k + 1))
    (yLeft yRight : NPointDomain d (k + 1)) :
    mixedReflectedChronologicalSource f g
        (equation621MixedChronologicalConfigOfPair d k (yLeft, yRight)) =
      starRingEnd Complex (f yLeft) * g yRight := by
  change (f.osConjTensorProduct g)
      (reflectedChronologicalRawConfig
        (equation621MixedChronologicalConfigOfPair
          d k (yLeft, yRight))) = _
  rw [reflectedChronologicalRawConfig_equation621MixedConfig]
  simp only [SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, splitFirst_append, splitLast_append,
    SchwartzNPoint.osConj_apply]
  have hreflect : timeReflectionN d (timeReflectionN d yLeft) = yLeft := by
    ext i mu
    exact congrFun (timeReflection_timeReflection d (yLeft i)) mu
  rw [hreflect]

theorem reducedTimeProjection_equation621MixedConfig
    {d k : Nat} [NeZero d]
    (yLeft yRight : NPointDomain d (k + 1)) :
    reducedTimeProjectionCLM d (k + (k + 1))
        (equation621MixedChronologicalConfigOfPair d k (yLeft, yRight)) =
      reflectedChronologicalGapMap k
        (section43QTime d (k + 1)
            (section43DiffCoordRealCLE d (k + 1) yLeft),
          section43QTime d (k + 1)
            (section43DiffCoordRealCLE d (k + 1) yRight)) := by
  rw [reducedTimeProjection_reflectedChronological_eq_gapMap]
  rw [reflectedChronologicalRawConfig_equation621MixedConfig,
    splitFirst_append, splitLast_append]
  have hreflect : timeReflectionN d (timeReflectionN d yLeft) = yLeft := by
    ext i mu
    exact congrFun (timeReflection_timeReflection d (yLeft i)) mu
  rw [hreflect]

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

/-- A mixed reflected-source cutoff is one at the limiting packet anchor.

The source family may use any index type and may start at a finite packet
tail.  This is the common argument behind both the nontrivial reflected-Gram
rows and the one-particle endpoint row. -/
theorem UniformCompactTimeMixedReflectedSourceFamilyData.cutoff_eq_one_at_translatedSourceAnchor
    {r : Nat}
    {ι : Type*}
    {f : ι -> euclideanPositiveTimeSubmodule (d := d) (r + 1)}
    (G : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (I : Section43ProductTimeApproximateIdentity (r + 1))
    (tau : Fin (r + 1) -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion (r + 1))
    (sourceIndex : Nat ->
      SchwartzMap (Section43SpatialSpace d (r + 1)) Complex -> ι)
    (tailStart : Nat)
    (hsource : forall scale chi,
      f (sourceIndex scale chi) =
        I.translatedPositiveTimeSpatialSource tau htau chi
          (scale + tailStart)) :
    G.η
        (osiiMixedBlockGlobalReducedTime r
          (Fin.append tau tau)) = 1 := by
  let chi := equation621NonzeroSpatialTest d (r + 1)
  have hchi : chi ≠ 0 :=
    equation621NonzeroSpatialTest_ne_zero d (r + 1)
  choose y hy hdist using fun N =>
    I.exists_translatedPositiveTimeSpatialSource_ne_zero
      tau htau chi hchi (N + tailStart)
  let packetTime : Nat -> Fin (r + 1) -> Real := fun N =>
    section43QTime d (r + 1)
      (section43DiffCoordRealCLE d (r + 1) (y N))
  have hpacketTime : Tendsto packetTime atTop (nhds tau) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro epsilon hepsilon
    obtain ⟨N0, hN0⟩ :=
      (Metric.tendsto_atTop.mp
        (I.radius_tendsto.comp (tendsto_add_atTop_nat tailStart)))
        epsilon hepsilon
    refine ⟨N0, ?_⟩
    intro N hN
    have hradius := hN0 N hN
    simp only [Function.comp_apply] at hradius
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (I.radius_pos (N + tailStart))] at hradius
    exact (hdist N).trans hradius
  let source : Nat -> ι := fun N => sourceIndex N chi
  let mixedPoint : Nat ->
      NPointDomain d ((r + (r + 1)) + 1) :=
    fun N => equation621MixedChronologicalConfigOfPair
      d r (y N, y N)
  have hmixed_ne : forall N,
      mixedReflectedChronologicalSource
          (f (source N)).1 (f (source N)).1 (mixedPoint N) ≠ 0 := by
    intro N
    have hsource_ne : (f (source N)).1 (y N) ≠ 0 := by
      rw [show f (source N) =
          I.translatedPositiveTimeSpatialSource tau htau chi
            (N + tailStart) by
        simpa [source] using hsource N chi]
      exact hy N
    rw [mixedReflectedChronologicalSource_equation621MixedConfig_apply]
    exact mul_ne_zero (by simpa using hsource_ne) hsource_ne
  have hcutoff_zero := mem_of_mem_nhds G.cutoff_one_on
  have hone : forall N,
      G.η
          (reducedTimeProjectionCLM d (r + (r + 1))
            (mixedPoint N)) = 1 := by
    intro N
    have hmixed_support : mixedPoint N ∈ tsupport
        (mixedReflectedChronologicalSource
          (f (source N)).1 (f (source N)).1 :
            NPointDomain d ((r + (r + 1)) + 1) -> Complex) :=
      subset_tsupport _ (hmixed_ne N)
    have hzero_support : mixedPoint N ∈ tsupport
        (translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d)
            (0 : Fin (r + r) -> Real))
          (mixedReflectedChronologicalSource
            (f (source N)).1 (f (source N)).1) :
            NPointDomain d ((r + (r + 1)) + 1) -> Complex) := by
      simpa [reflectedReducedAbsoluteDisplacement_zero] using hmixed_support
    have h := hcutoff_zero (source N, source N) (mixedPoint N) hzero_support
    simpa [reducedTimeCutoffWeight] using h
  have hpair : Tendsto (fun N => (packetTime N, packetTime N)) atTop
      (nhds (tau, tau)) :=
    Filter.Tendsto.prodMk_nhds hpacketTime hpacketTime
  have hgap :=
    (continuous_reflectedChronologicalGapMap r).continuousAt.tendsto.comp
      hpair
  have hreduced : Tendsto
      (fun N => reducedTimeProjectionCLM d (r + (r + 1))
        (mixedPoint N)) atTop
      (nhds (osiiMixedBlockGlobalReducedTime r
        (Fin.append tau tau))) := by
    rw [osiiMixedBlockGlobalReducedTime_append_eq_reflectedChronologicalGapMap]
    apply hgap.congr'
    filter_upwards with N
    exact (reducedTimeProjection_equation621MixedConfig
      (y N) (y N)).symm
  have heta := G.η.continuous.continuousAt.tendsto.comp hreduced
  have hone_limit : Tendsto
      (fun N => G.η
        (reducedTimeProjectionCLM d (r + (r + 1))
          (mixedPoint N))) atTop (nhds 1) := by
    simpa only [hone] using
      (tendsto_const_nhds :
        Tendsto (fun _ : Nat => (1 : Complex)) atTop (nhds 1))
  exact tendsto_nhds_unique heta hone_limit

/-- The cutoff of a source-realized reflected Gram atlas is one at the
reflected pair of the translated packet anchor. -/
theorem ReflectedGramSpatialSourceData.cutoff_eq_one_at_translatedSourceAnchor
    {q : Nat}
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (tau : Fin ((q + 1) + 1) → Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hsource : ∀ scale chi,
      UniformCompactTimeSource.source (D.sourceCLM scale chi) =
        I.translatedPositiveTimeSpatialSource tau htau chi scale) :
    D.reflectedGram.atlas.sourceStage.germ.η
        (osiiMixedBlockGlobalReducedTime (q + 1)
          (Fin.append tau tau)) = 1 := by
  apply
    D.reflectedGram.atlas.sourceStage.germ.cutoff_eq_one_at_translatedSourceAnchor
      (r := q + 1) I tau htau (fun scale chi => D.sourceCLM scale chi) 0
  intro scale chi
  simpa using hsource scale chi

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {k depth : Nat} [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → Real}

/-- The canonical rooted left reflected-Gram germ is one at its fixed
reflected packet anchor. -/
theorem rootedLeftNontrivialReflectedGram_cutoff_eq_one
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (q m : Nat)
    (hn : 1 ≤ q + 2)
    (hm : 1 ≤ m)
    (hnm : k = (q + 2) + m - 1) :
    let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let D := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    D.reflectedGram.atlas.sourceStage.germ.η
      (osiiMixedBlockGlobalReducedTime (q + 1)
        (Fin.append (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor i))) = 1 := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  apply D.cutoff_eq_one_at_translatedSourceAnchor
    (A.rootedLeftBlockApproximateIdentity R i)
    (A.rootedLeftBlockAnchor i)
    (A.rootedLeftBlockAnchor_positive i)
  intro scale chi
  change A.rootedLeftBlockSpatialSource R i scale chi = _
  exact A.rootedLeftBlockAnchoredSourceCLM_source_translated R i scale chi

/-- The canonical rooted right reflected-Gram germ is one at its fixed
reflected packet anchor. -/
theorem rootedRightNontrivialReflectedGram_cutoff_eq_one
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (n q : Nat)
    (hn : 1 ≤ n)
    (hm : 1 ≤ q + 2)
    (hnm : k = n + (q + 2) - 1) :
    let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    let D := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    D.reflectedGram.atlas.sourceStage.germ.η
      (osiiMixedBlockGlobalReducedTime (q + 1)
        (Fin.append (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor i))) = 1 := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  apply D.cutoff_eq_one_at_translatedSourceAnchor
    (A.rootedRightBlockApproximateIdentity R i)
    (A.rootedRightBlockAnchor i)
    (A.rootedRightBlockAnchor_positive i)
  intro scale chi
  change A.rootedRightBlockSpatialSource R i scale chi = _
  exact A.rootedRightBlockAnchoredSourceCLM_source_translated R i scale chi

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
