/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeHilbertField










open Complex Topology Filter
open scoped BigOperators Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- Put independent left and right increments into the reflected scalar
variables, conjugating only the left block. -/
def mixedReflectedCauchyIncrement
    {k : ℕ} (zL zR : Fin k → ℂ) :
    Fin (k + k) → ℂ :=
  Fin.addCases (fun i => starRingEnd ℂ (zL i)) zR

@[simp] theorem mixedReflectedCauchyIncrement_left
    {k : ℕ} (zL zR : Fin k → ℂ) (i : Fin k) :
    mixedReflectedCauchyIncrement zL zR (Fin.castAdd k i) =
      starRingEnd ℂ (zL i) := by
  simp [mixedReflectedCauchyIncrement]

@[simp] theorem mixedReflectedCauchyIncrement_right
    {k : ℕ} (zL zR : Fin k → ℂ) (i : Fin k) :
    mixedReflectedCauchyIncrement zL zR (Fin.natAdd k i) =
      zR i := by
  change
    Fin.addCases (fun j => starRingEnd ℂ (zL j)) zR
        (Fin.natAdd k i) =
      zR i
  rw [Fin.addCases_right]

@[simp] theorem mixedReflectedCauchyIncrement_self
    {k : ℕ} (z : Fin k → ℂ) :
    mixedReflectedCauchyIncrement z z =
      reflectedCauchyIncrement z := rfl

namespace PositiveTimeSourceCoefficientData

/-- The unweighted reflected Schwinger coefficient for two different
positive-time source Taylor families. -/
def mixedScalarGram
    {n k : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceCoefficientData d n k)
    (α β : Fin k → ℕ) : ℂ :=
  OS.S (n + n)
    (ZeroDiagonalSchwartz.ofClassical
      ((L.coefficient α).1.osConjTensorProduct (R.coefficient β).1))

end PositiveTimeSourceCoefficientData

/-- Termwise compatibility between a doubled scalar Cauchy expansion and two
independently chosen positive-time source Taylor families. -/
structure MixedReflectedSourceCauchyCompatibility
    {n k : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k) : Prop where
  left_increment :
    ∀ i, D.increment (Fin.castAdd k i) =
      starRingEnd ℂ (L.increment i)
  right_increment :
    ∀ i, D.increment (Fin.natAdd k i) = R.increment i
  cauchyCoeff_eq_mixedScalarGram :
    ∀ α β,
      SCV.cauchyCoeffPolydisc D.scalar D.center
          (fun _ => D.radius) (Fin.append α β) =
        L.mixedScalarGram OS R α β

namespace PositiveTimeSourceCoefficientData

/-- A weighted mixed Cauchy multi-index term is the corresponding weighted
reflected Schwinger coefficient. -/
theorem mixedReflectedCauchy_multiIndexTerm_append_eq
    {n k : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k)
    (C : MixedReflectedSourceCauchyCompatibility OS L R D)
    (α β : Fin k → ℕ) :
    D.multiIndexTerm (Fin.append α β) =
      starRingEnd ℂ (L.monomial α) * R.monomial β *
        L.mixedScalarGram OS R α β := by
  simp only [ReflectedCauchyCoefficientData.multiIndexTerm,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    C.left_increment, C.right_increment,
    C.cauchyCoeff_eq_mixedScalarGram,
    monomial, map_prod, map_pow]

/-- The reflected Schwinger pairing of two homogeneous source polynomials is
the bidegree term of the compatible doubled scalar Cauchy expansion. -/
theorem mixedScalarGram_homogeneousSource_eq_cauchyScalarGram
    {n k : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k)
    (C : MixedReflectedSourceCauchyCompatibility OS L R D)
    (p q : ℕ) :
    OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical
          ((L.homogeneousSource p).1.osConjTensorProduct
            (R.homogeneousSource q).1)) =
      D.scalarGram p q := by
  rw [← osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  simp only [homogeneousSource, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [D.scalarGram_eq_sum_antidiagonalTuple p q]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  rw [L.mixedReflectedCauchy_multiIndexTerm_append_eq OS R D C α β]
  change
    R.monomial β *
        (starRingEnd ℂ (L.monomial α) * L.mixedScalarGram OS R α β) =
      starRingEnd ℂ (L.monomial α) * R.monomial β *
        L.mixedScalarGram OS R α β
  ring

end PositiveTimeSourceCoefficientData

namespace PositiveTimeSourceTaylorFamily

/-- Finite Taylor approximants from two source families have the exact square
partial sum of the compatible mixed scalar Gram matrix. -/
theorem inner_partialSum_eq_mixedCauchy_squareSum
    {n q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceTaylorFamily d n (q + 1))
    (zL zR : Fin (q + 1) → ℂ)
    (D : ReflectedCauchyCoefficientData (q + 1))
    (C :
      MixedReflectedSourceCauchyCompatibility OS
        (L.coefficientData zL) (R.coefficientData zR) D)
    (N : ℕ) :
    @inner ℂ (OSHilbertSpace OS) _
        (L.partialSum OS N zL) (R.partialSum OS N zR) =
      ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
        D.scalarGram pq.1 pq.2 := by
  rw [L.partialSum_eq_source, R.partialSum_eq_source]
  calc
    @inner ℂ (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS n
          (∑ p ∈ Finset.range N, L.homogeneousSource zL p))
        (osiiPositiveTimeSingleVectorCLM OS n
          (∑ q ∈ Finset.range N, R.homogeneousSource zR q)) =
        ∑ p ∈ Finset.range N,
          ∑ q ∈ Finset.range N, D.scalarGram q p := by
      simp only [map_sum, sum_inner, inner_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
      exact
        (L.coefficientData zL).mixedScalarGram_homogeneousSource_eq_cauchyScalarGram
          OS (R.coefficientData zR) D C q p
    _ = ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
          D.scalarGram pq.1 pq.2 := by
      rw [Finset.sum_product, Finset.sum_comm]

/-- If two Hilbert Taylor sequences converge and their mixed coefficients are
one doubled scalar Cauchy expansion, the inner product of the limits is the
value of that scalar expansion. -/
theorem inner_limit_eq_of_mixedReflectedCauchyCompatibility
    {n q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (L R : PositiveTimeSourceTaylorFamily d n (q + 1))
    (zL zR : Fin (q + 1) → ℂ)
    (D : ReflectedCauchyCoefficientData (q + 1))
    (C :
      MixedReflectedSourceCauchyCompatibility OS
        (L.coefficientData zL) (R.coefficientData zR) D)
    (ΨL ΨR : OSHilbertSpace OS)
    (hL :
      Tendsto (fun N => L.partialSum OS N zL) atTop (𝓝 ΨL))
    (hR :
      Tendsto (fun N => R.partialSum OS N zR) atTop (𝓝 ΨR))
    (value : ℂ)
    (hseries :
      HasSum
        (fun p =>
          SCV.cauchyPowerSeriesPolydisc D.scalar D.center
            (fun _ => D.radius) p (fun _ => D.increment))
        value) :
    @inner ℂ (OSHilbertSpace OS) _ ΨL ΨR = value := by
  have hinner :
      Tendsto
        (fun N =>
          @inner ℂ (OSHilbertSpace OS) _
            (L.partialSum OS N zL) (R.partialSum OS N zR))
        atTop
        (𝓝 (@inner ℂ (OSHilbertSpace OS) _ ΨL ΨR)) :=
    hL.inner hR
  have hmulti := D.hasSum_multiIndexTerm_of_cauchyPowerSeries hseries
  have hgram := D.hasSum_scalarGram hmulti
  have hsquare := D.tendsto_square_sum_scalarGram hgram
  have hscalar :
      Tendsto
        (fun N =>
          @inner ℂ (OSHilbertSpace OS) _
            (L.partialSum OS N zL) (R.partialSum OS N zR))
        atTop (𝓝 value) :=
    hsquare.congr'
      (Filter.Eventually.of_forall fun N =>
        (L.inner_partialSum_eq_mixedCauchy_squareSum
          OS R zL zR D C N).symm)
  exact tendsto_nhds_unique hinner hscalar

end PositiveTimeSourceTaylorFamily

/-- A genuine mixed reflected scalar real edge supplies the termwise Cauchy
compatibility for every pair in a uniformly compact source family. -/
theorem mixedReflectedSourceCauchyCompatibility_of_realEdge_compactTime_family
    {q : ℕ} {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (a b : ι)
    (zL zR : Fin (q + 1) → ℂ)
    (D : ReflectedCauchyCoefficientData (q + 1))
    (hleft :
      ∀ i, D.increment (Fin.castAdd (q + 1) i) =
        starRingEnd ℂ (zL i))
    (hright :
      ∀ i, D.increment (Fin.natAdd (q + 1) i) = zR i)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc D.center (fun _ => D.radius) ⊆ U)
    (hscalar : DifferentiableOn ℂ D.scalar U)
    (hreal :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) i) x)
                ((f a).1.osConjTensorProduct (f b).1))))) :
    MixedReflectedSourceCauchyCompatibility OS
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        (f a)
        (fun i : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) i)
        zL)
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        (f b)
        (fun i : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) i)
        zR)
      D := by
  let directions : Fin (q + 1) → NPointDomain d (q + 2) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  let φ : SchwartzNPoint d ((q + 2) + (q + 2)) :=
    (f a).1.osConjTensorProduct (f b).1
  obtain ⟨ε, hε, hχ_growth, hχ_disj, hχ_base, hχ_local⟩ :=
    exists_twoBlockTimeMarginCutoff_one_on_mixedReflectedTranslation_family_germ
      (fun c => (f c).1) hf
  let χ : NPointDomain d ((q + 2) + (q + 2)) → ℂ :=
    osiiA0TwoBlockTimeMarginCutoff d (q + 2) ε
  let T : SchwartzNPoint d ((q + 2) + (q + 2)) →L[ℂ] ℂ :=
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
  have hφ_disj :
      Disjoint
        (tsupport
          ((φ : SchwartzNPoint d ((q + 2) + (q + 2))) :
            NPointDomain d ((q + 2) + (q + 2)) → ℂ))
        (CoincidenceLocus d ((q + 2) + (q + 2))) := by
    simpa [φ] using
      osiiA0_osConjTensorProduct_tsupport_disjoint_coincidence_of_ordered
        (f a).1 (f b).1 (f a).2 (f b).2
  have hlocalT :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        T (translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM directions x) φ)) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM directions x)
                φ))) := by
    filter_upwards [hχ_local] with u hu
    let ψ : SchwartzNPoint d ((q + 2) + (q + 2)) :=
      translateSchwartzConfiguration
        (reflectedSourceParameterDisplacementCLM directions u) φ
    have hψ_disj :
        Disjoint
          (tsupport
            ((ψ : SchwartzNPoint d ((q + 2) + (q + 2))) :
              NPointDomain d ((q + 2) + (q + 2)) → ℂ))
          (CoincidenceLocus d ((q + 2) + (q + 2))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hcoin
      have hχx : χ x = 1 :=
        hu a b x (by simpa [ψ, φ, directions, χ] using hx)
      have hx_support : x ∈ Function.support χ := by
        intro hxzero
        rw [hxzero] at hχx
        norm_num at hχx
      exact Set.disjoint_left.mp hχ_disj (subset_closure hx_support) hcoin
    have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
      VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
        (f := ψ) hψ_disj
    simpa [T, ψ] using
      osiiA0TemperateCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        OS χ hχ_growth hχ_disj ψ hψ_zero
        (fun x hx =>
          hu a b x (by simpa [ψ, φ, directions, χ] using hx))
  have hrealT :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions x) φ)) := by
    simpa [directions, φ] using hreal.trans hlocalT.symm
  refine
    { left_increment := hleft
      right_increment := hright
      cauchyCoeff_eq_mixedScalarGram := ?_ }
  intro α β
  calc
    SCV.cauchyCoeffPolydisc D.scalar D.center
        (fun _ => D.radius) (@Fin.append (q + 1) (q + 1) ℕ α β) =
      T (SchwartzNPoint.osConjTensorProduct
        (normalizedSourceMultiDerivative directions α (f a).1 :
          SchwartzNPoint d (q + 2))
        (normalizedSourceMultiDerivative directions β (f b).1 :
          SchwartzNPoint d (q + 2))) := by
      exact
        cauchyCoeffPolydisc_eq_localReflectedProduct_normalized
          hTowerC hTowerPi T directions (f a).1 (f b).1 D.radius_pos
          hU hRU hscalar (by simpa [φ] using hrealT) α β
    _ =
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        (f a) directions zL).mixedScalarGram OS
          (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
            (f b) directions zR) α β := by
      simpa [PositiveTimeSourceCoefficientData.mixedScalarGram, T, χ] using
        osiiA0TemperateCutoffSchwingerCLM_normalized_reflectedProduct_eq
          OS directions α β (f a).1 (f b).1 χ
          hχ_growth hχ_disj (hχ_base a b) hφ_disj

/-- One represented continuation stage shared by every mixed pair in a
uniformly compact positive-time source family. -/
structure UniformCompactTimeMixedReflectedSourceStageData
    {q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2)) where
  germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f
  stage : OSIITimeContinuationStage d
    ((q + 1) + ((q + 1) + 1))
  realRegion : Set (Fin ((q + 1) + ((q + 1) + 1)) → ℝ)
  realRegion_open : IsOpen realRegion
  cutoff_support :
    tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      realRegion
  edge :
    stage.PositiveRealEdgeData
      (orderedTransportDistribution germ.W) realRegion

/-- The minimal represented-stage contract for the mixed scalar continuation.
The stage distribution need not coincide with the auxiliary germ functional
away from the concrete translated cutoff currents used by this source family. -/
structure UniformCompactTimeMixedOrderedSourceStageData
    {q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2)) where
  germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f
  stage : OSIITimeContinuationStage d
    ((q + 1) + ((q + 1) + 1))
  representedDistribution :
    SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) →L[ℂ] ℂ
  realRegion : Set (Fin ((q + 1) + ((q + 1) + 1)) → ℝ)
  realRegion_open : IsOpen realRegion
  cutoff_support :
    tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      realRegion
  edge :
    stage.PositiveRealEdgeData representedDistribution realRegion
  orderedSourceEdge :
    ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
      ∀ ab : ι × ι,
        representedDistribution
            (section43OrderedPullbackFullCutoffCLM d
              ((q + 1) + ((q + 1) + 1))
              (SCV.translateSchwartz
                (reflectedReducedTimeDisplacement u) germ.η)
              (translateSchwartzConfiguration
                (osiiDifferenceTimeTranslation (d := d)
                  (reflectedReducedTimeDisplacement u))
                (diffVarReduction d
                  ((q + 1) + ((q + 1) + 1))
                  (mixedReflectedChronologicalSource
                    (f ab.1).1 (f ab.2).1)))) =
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f ab.1).1.osConjTensorProduct (f ab.2).1)))

/-- The non-circular mixed scalar predecessor contract.  It retains only the
part of the stage geometry needed to obtain a common moving-slice polydisc and
the equality of the stage's translated positive-real orbit integral with the
intended Schwinger source values. -/
structure UniformCompactTimeMixedStageOrbitSourceData
    {q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2)) where
  germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f
  stage : OSIITimeContinuationStage d
    ((q + 1) + ((q + 1) + 1))
  cutoffCarrier :
    ∀ τ ∈ tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ),
      osiiPositiveRealTimeEmbed τ ∈ stage.carrier
  stageOrbitSourceEdge :
    ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
      ∀ ab : ι × ι,
        osiiMovingSpatialSliceIntegral
            (SCV.translateSchwartz
              (reflectedReducedTimeDisplacement u) germ.η)
            (fun τ =>
              stage.distribution (osiiPositiveRealTimeEmbed τ))
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d)
                (reflectedReducedTimeDisplacement u))
              (diffVarReduction d
                ((q + 1) + ((q + 1) + 1))
                (mixedReflectedChronologicalSource
                  (f ab.1).1 (f ab.2).1))) =
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f ab.1).1.osConjTensorProduct (f ab.2).1)))

namespace UniformCompactTimeMixedReflectedSourceStageData

end UniformCompactTimeMixedReflectedSourceStageData

namespace UniformCompactTimeMixedOrderedSourceStageData

/-- A source-specific ordered-current edge already determines the direct
stage-orbit integral edge.  Compact support keeps every sufficiently small
translated cutoff inside the represented real region, where the stage
distribution represents the declared current. -/
noncomputable def toStageOrbitSourceData
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (S : UniformCompactTimeMixedOrderedSourceStageData OS f) :
    UniformCompactTimeMixedStageOrbitSourceData OS f where
  germ := S.germ
  stage := S.stage
  cutoffCarrier := by
    intro τ hτ
    exact (S.edge.stageEdge τ (S.cutoff_support hτ)).1
  stageOrbitSourceEdge := by
    obtain ⟨V, hV, htranslate⟩ :=
      exists_mem_nhds_tsupport_translateSchwartz_subset
        S.germ.η S.germ.η_compact S.realRegion S.realRegion_open
          S.cutoff_support
    have hdisp_zero :
        reflectedReducedTimeDisplacement
            (0 : Fin ((q + 1) + (q + 1)) → ℝ) =
          0 := by
      ext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp
      · intro r
        refine Fin.cases ?_ (fun i => ?_) r <;> simp
    have hpreV :
        reflectedReducedTimeDisplacement ⁻¹' V ∈
          𝓝 (0 : Fin ((q + 1) + (q + 1)) → ℝ) := by
      have hV0 :
          V ∈ 𝓝
            (reflectedReducedTimeDisplacement
              (0 : Fin ((q + 1) + (q + 1)) → ℝ)) := by
        rw [hdisp_zero]
        exact hV
      exact
        continuous_reflectedReducedTimeDisplacement.continuousAt hV0
    filter_upwards [hpreV, S.orderedSourceEdge] with u hu hedge
    intro ab
    let t : Fin ((q + 1) + ((q + 1) + 1)) → ℝ :=
      reflectedReducedTimeDisplacement u
    have hsupport :
        tsupport
            ((SCV.translateSchwartz t S.germ.η :
              SchwartzMap
                (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ) :
              (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
          S.realRegion := by
      exact htranslate t hu
    calc
      osiiMovingSpatialSliceIntegral
          (SCV.translateSchwartz t S.germ.η)
          (fun τ =>
            S.stage.distribution (osiiPositiveRealTimeEmbed τ))
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) t)
            (diffVarReduction d
              ((q + 1) + ((q + 1) + 1))
              (mixedReflectedChronologicalSource
                (f ab.1).1 (f ab.2).1))) =
        S.representedDistribution
          (section43OrderedPullbackFullCutoffCLM d
            ((q + 1) + ((q + 1) + 1))
            (SCV.translateSchwartz t S.germ.η)
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d) t)
              (diffVarReduction d
                ((q + 1) + ((q + 1) + 1))
                (mixedReflectedChronologicalSource
                  (f ab.1).1 (f ab.2).1)))) := by
        exact
          osiiMovingSpatialSliceIntegral_eq_orderedPullbackFullCutoff
            S.representedDistribution
            (SCV.translateSchwartz t S.germ.η)
            (fun τ =>
              S.stage.distribution (osiiPositiveRealTimeEmbed τ))
            S.realRegion
            (hasCompactSupport_translateSchwartz
              S.germ.η S.germ.η_compact t)
            hsupport
            S.edge.stage_continuousOn
            S.edge.stage_pointwiseBounded
            S.edge.stage_represents
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d) t)
              (diffVarReduction d
                ((q + 1) + ((q + 1) + 1))
                (mixedReflectedChronologicalSource
                  (f ab.1).1 (f ab.2).1)))
      _ =
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f ab.1).1.osConjTensorProduct (f ab.2).1))) := by
        simpa [t] using hedge ab

end UniformCompactTimeMixedOrderedSourceStageData

namespace UniformCompactTimeMixedStageOrbitSourceData

/-- The stage-orbit source edge directly constructs the mixed scalar Cauchy
continuation family. -/
theorem exists_mixedReflectedCauchyPolydiscFamilyData_of_radius
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (S : UniformCompactTimeMixedStageOrbitSourceData OS f)
    (R : ℝ)
    (hR : 0 < R)
    (hclosed :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R) ⊆
        reflectedMovingSliceCarrier S.stage S.germ.η) :
    ∃ D : ι × ι → ReflectedCauchyPolydiscData (q + 1),
      (∀ ab,
        (D ab).center = 0 ∧
          (D ab).radius = R ∧
            (SCV.closedPolydisc
                (D ab).center (fun _ => (D ab).radius) ⊆
              reflectedMovingSliceCarrier S.stage S.germ.η) ∧
            DifferentiableOn ℂ (D ab).scalar
              (reflectedMovingSliceCarrier S.stage S.germ.η) ∧
            (D ab).scalar =
              reflectedMovingSliceScalar S.stage S.germ.η
                (diffVarReduction d ((q + 1) + ((q + 1) + 1))
                  (mixedReflectedChronologicalSource
                    (f ab.1).1 (f ab.2).1))) ∧
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ ab,
          realAffineSlice (D ab).scalar (D ab).center u =
            OS.S ((q + 2) + (q + 2))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM
                    (fun r : Fin (q + 1) =>
                      chronologicalTimeSourceDirection (d := d) r) u)
                  ((f ab.1).1.osConjTensorProduct (f ab.2).1))) := by
  let F :
      ι × ι →
        SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
    fun ab =>
      diffVarReduction d ((q + 1) + ((q + 1) + 1))
        (mixedReflectedChronologicalSource
          (f ab.1).1 (f ab.2).1)
  let raw :
      ι × ι → (Fin ((q + 1) + (q + 1)) → ℝ) → ℂ :=
    fun ab u =>
      OS.S ((q + 2) + (q + 2))
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM
              (fun r : Fin (q + 1) =>
                chronologicalTimeSourceDirection (d := d) r) u)
            ((f ab.1).1.osConjTensorProduct (f ab.2).1)))
  have hreal :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ ab,
          realAffineSlice
            (reflectedMovingSliceScalar S.stage S.germ.η (F ab)) 0 u =
              raw ab u :=
    reflectedMovingSliceScalar_family_realEdge_eventually_of_stageOrbitIntegral
      S.stage S.germ.η F raw
      (by simpa [F, raw] using S.stageOrbitSourceEdge)
  obtain ⟨D, hD, hrealD⟩ :=
    exists_reflectedCauchyPolydiscFamilyData_of_realEdge_of_radius
      S.stage S.germ.η S.germ.η_compact
      R hR hclosed F raw hreal
  exact ⟨D, by simpa [F] using hD, by simpa [raw] using hrealD⟩

end UniformCompactTimeMixedStageOrbitSourceData

namespace UniformCompactTimeSourceHilbertFieldFamilyData

/-- Once the mixed scalar Cauchy coefficients are identified, the inner
product of two fields in a common compact-time Hilbert family is the value of
that scalar continuation at the independent reflected increment. -/
theorem inner_eq_mixedScalar_of_compatibility_of_hasSum
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS f)
    (a b : ι)
    (zL zR : Fin (q + 1) → ℂ)
    (hzL :
      zL ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => H.radius))
    (hzR :
      zR ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => H.radius))
    (D : ReflectedCauchyPolydiscData (q + 1))
    (hincrement :
      ∀ i,
        ‖mixedReflectedCauchyIncrement zL zR i‖ < D.radius)
    (C :
      MixedReflectedSourceCauchyCompatibility OS
        (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
          (f a)
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i)
          zL)
        (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
          (f b)
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i)
          zR)
        (D.atIncrement
          (mixedReflectedCauchyIncrement zL zR) hincrement))
    (hseries :
      HasSum
        (fun p =>
          SCV.cauchyPowerSeriesPolydisc D.scalar D.center
            (fun _ => D.radius) p
            (fun _ => mixedReflectedCauchyIncrement zL zR))
        (D.scalar
          (D.center + mixedReflectedCauchyIncrement zL zR))) :
    @inner ℂ (OSHilbertSpace OS) _
        (H.field a zL) (H.field b zR) =
      D.scalar (D.center + mixedReflectedCauchyIncrement zL zR) := by
  let L :=
    PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
      (f a)
      (fun i : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) i)
  let R :=
    PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
      (f b)
      (fun i : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) i)
  let E :=
    D.atIncrement (mixedReflectedCauchyIncrement zL zR) hincrement
  apply
    L.inner_limit_eq_of_mixedReflectedCauchyCompatibility
      OS R zL zR E C (H.field a zL) (H.field b zR)
  · simpa [L] using (H.taylor a).tendsto_at hzL
  · simpa [R] using (H.taylor b).tendsto_at hzR
  · simpa [E, ReflectedCauchyPolydiscData.atIncrement] using hseries

/-- A genuine mixed compact-time real edge and a larger holomorphy polydisc
supply the exact pairwise scalar continuation formula for the common Hilbert
fields. -/
theorem inner_eq_mixedScalar_of_realEdge_compactTime_of_norm_lt
    {q : ℕ} {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS f)
    (a b : ι)
    (zL zR : Fin (q + 1) → ℂ)
    (hzL :
      zL ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => H.radius))
    (hzR :
      zR ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => H.radius))
    (D : ReflectedCauchyPolydiscData (q + 1))
    (hincrement :
      ∀ i,
        ‖mixedReflectedCauchyIncrement zL zR i‖ < D.radius)
    (Rw : ℝ)
    (hRw : D.radius < Rw)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRwU :
      SCV.closedPolydisc D.center (fun _ => Rw) ⊆ U)
    (hscalar : DifferentiableOn ℂ D.scalar U)
    (hreal :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) i) x)
                ((f a).1.osConjTensorProduct (f b).1)))))
    (hnorm :
      ‖mixedReflectedCauchyIncrement zL zR‖ <
        D.radius /
          (2 * ((((q + 1) + (q + 1) - 1 : ℕ) : ℝ) + 2))) :
    @inner ℂ (OSHilbertSpace OS) _
        (H.field a zL) (H.field b zR) =
      D.scalar (D.center + mixedReflectedCauchyIncrement zL zR) := by
  let E :=
    D.atIncrement (mixedReflectedCauchyIncrement zL zR) hincrement
  have C :
      MixedReflectedSourceCauchyCompatibility OS
        (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
          (f a)
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i)
          zL)
        (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
          (f b)
          (fun i : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) i)
          zR)
        E := by
    apply
      mixedReflectedSourceCauchyCompatibility_of_realEdge_compactTime_family
        hTowerC hTowerPi OS f hf a b zL zR E
    · intro i
      exact mixedReflectedCauchyIncrement_left zL zR i
    · intro i
      exact mixedReflectedCauchyIncrement_right zL zR i
    · exact hU
    · intro w hw
      exact hRwU
        (SCV.closedPolydisc_mono (fun _ => le_of_lt hRw) hw)
    · exact hscalar
    · simpa [E, ReflectedCauchyPolydiscData.atIncrement] using hreal
  apply H.inner_eq_mixedScalar_of_compatibility_of_hasSum
    OS f a b zL zR hzL hzR D hincrement C
  simpa using
    SCV.hasSum_cauchyPowerSeriesPolydisc_diag_of_differentiableOn
      D.radius_pos hRw hU hRwU hscalar hnorm

end UniformCompactTimeSourceHilbertFieldFamilyData

end OSIIChapterV
end OSReconstruction
