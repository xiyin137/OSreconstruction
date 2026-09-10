/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorAbsoluteSpatialSource
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.SCV.SchwartzFiniteSeminormBound




















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace GeneratorHermiteHilbertFieldFamilyData

/-- The translated compact left time profile selected by a global real
generator parameter. -/
noncomputable def translatedLeftTimeProfile
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    SchwartzMap (Fin i.n → ℝ) ℂ :=
  SCV.translateSchwartz
    (chronologicalTimeProfileDisplacementOfPositive i.hn
      (i.leftRealCoordinates τ))
    (B.leftTimeProfile i).f

/-- The translated compact right time profile selected by a global real
generator parameter. -/
noncomputable def translatedRightTimeProfile
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    SchwartzMap (Fin i.m → ℝ) ℂ :=
  SCV.translateSchwartz
    (chronologicalTimeProfileDisplacementOfPositive i.hm
      (i.rightRealCoordinates τ))
    (B.rightTimeProfile i).f

/-- The native split-arity source before the axis-pair semigroup applies its
own block-global affine pullback. Keeping this separate from the already
global source avoids multiplying the translated generator time profiles by
the auxiliary cutoffs twice. -/
noncomputable def generatorSplitSeparateTimeSpatialSourceCLM
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzNPoint d (i.n + i.m) :=
  (axisPairSeparateTimeSpatialTensorCLM
    i.n i.m
    (B.translatedLeftTimeProfile i τ)
    (B.translatedRightTimeProfile i τ)).comp
      (generatorSplitSpatialPullbackCLM i)

@[simp] theorem generatorSplitSeparateTimeSpatialSourceCLM_apply
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    B.generatorSplitSeparateTimeSpatialSourceCLM i τ F =
      axisPairSeparateTimeSpatialTensor i.n i.m
        (B.translatedLeftTimeProfile i τ)
        (B.translatedRightTimeProfile i τ)
        (generatorSplitSpatialPullbackCLM i F) := rfl

/-- Translating a compact chronological time profile preserves compact
support for every parameter value. -/
theorem hasCompactSupport_translatedTimeProfile
    {n : ℕ}
    (hn : 0 < n)
    (g : Section43CompactStrictPositiveTimeSource n)
    (u : Fin (n - 1) → ℝ) :
    HasCompactSupport
      ((SCV.translateSchwartz
          (chronologicalTimeProfileDisplacementOfPositive hn u) g.f :
        SchwartzMap (Fin n → ℝ) ℂ) :
        (Fin n → ℝ) → ℂ) :=
  hasCompactSupport_translateSchwartz g.f g.compact
    (chronologicalTimeProfileDisplacementOfPositive hn u)

/-- The concrete translated-source identity, viewed as a subset of global
real generator parameters. This set is a neighborhood of the origin; bridge
positivity and membership in the two Hilbert-field real regions remain
explicit antecedents because they are the genuine generator-domain
conditions. -/
def translatedSourceRealEdgeSet
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS) :
    Set (Fin k → ℝ) :=
  {τ | ∀ i : GeneratorIndex k, ∀ r : ℕ,
    0 < τ i.bridgeGlobalIndex →
    i.leftRealCoordinates τ ∈ B.leftRealRegion i →
    i.rightRealCoordinates τ ∈ B.rightRealRegion i →
      B.mode lgc i r (osiiPositiveRealTimeEmbed τ) =
        OS.S (i.n + i.m)
          (ZeroDiagonalSchwartz.ofClassical
            ((section43OrderedPullbackTimeSpatialTensorCLM
                d i.n (leftSpatialHermiteBlock d i r)
                (B.translatedLeftTimeProfile i τ)).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (τ i.bridgeGlobalIndex)
                (section43OrderedPullbackTimeSpatialTensorCLM
                  d i.m (rightSpatialHermiteBlock d i r)
                  (B.translatedRightTimeProfile i τ)))))}

/-- The global left coordinates of one generator split tend to zero with the
global real parameter. -/
theorem tendsto_leftRealCoordinates_zero
    (i : GeneratorIndex k) :
    Tendsto i.leftRealCoordinates (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous i.leftRealCoordinates := by
    unfold GeneratorIndex.leftRealCoordinates
    fun_prop
  have hzero :
      i.leftRealCoordinates (0 : Fin k → ℝ) = 0 := by
    ext a
    simp [GeneratorIndex.leftRealCoordinates]
  rw [← hzero]
  exact hcontinuous.continuousAt

/-- The global right coordinates of one generator split tend to zero with the
global real parameter. -/
theorem tendsto_rightRealCoordinates_zero
    (i : GeneratorIndex k) :
    Tendsto i.rightRealCoordinates (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous i.rightRealCoordinates := by
    unfold GeneratorIndex.rightRealCoordinates
    fun_prop
  have hzero :
      i.rightRealCoordinates (0 : Fin k → ℝ) = 0 := by
    ext b
    simp [GeneratorIndex.rightRealCoordinates]
  rw [← hzero]
  exact hcontinuous.continuousAt

/-- A fixed auxiliary common translation for the untranslated left compact
time profile.  Choosing this once, before the generator parameter is known,
keeps the later translated shift quantitatively visible. -/
noncomputable def baseLeftCommonShift
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) : ℝ :=
  Classical.choose
    (exists_osiiAxisPairCommonShift_gt_leftTimeSpan
      i.hn (B.leftTimeProfile i).f (B.leftTimeProfile i).compact)

theorem baseLeftCommonShift_span
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k) :
    ∀ δ ∈ tsupport
        ((B.leftTimeProfile i).f :
          (Fin i.n → ℝ) → ℂ),
      (section43ScalarDiffCLE i.n).symm δ
          (Fin.rev ⟨0, i.hn⟩) <
        B.baseLeftCommonShift i :=
  (Classical.choose_spec
    (exists_osiiAxisPairCommonShift_gt_leftTimeSpan
      i.hn (B.leftTimeProfile i).f (B.leftTimeProfile i).compact)).2

/-- A controlled common translation for the moved left profile.  The fixed
base shift handles the original compact support; the norm correction handles
the chronological displacement and is at most linear in the generator
parameter. -/
noncomputable def translatedLeftCommonShift
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) : ℝ :=
  B.baseLeftCommonShift i +
    ‖(section43ScalarDiffCLE i.n).symm
      (chronologicalTimeProfileDisplacementOfPositive i.hn
        (i.leftRealCoordinates τ))‖

/-- The endpoint displacement of the translated left profile is linear in the
global real generator parameter.  Bundling it as a CLM exposes one fixed
operator norm for all later growth estimates. -/
noncomputable def translatedLeftEndpointDisplacementCLM
    (i : GeneratorIndex k) :
    (Fin k → ℝ) →L[ℝ] (Fin i.n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun τ =>
        (section43ScalarDiffCLE i.n).symm
          (chronologicalTimeProfileDisplacementOfPositive i.hn
            (i.leftRealCoordinates τ))
      map_add' := by
        intro τ υ
        rw [← (section43ScalarDiffCLE i.n).symm.map_add]
        congr 1
        ext j
        unfold chronologicalTimeProfileDisplacementOfPositive
        simp only [Pi.add_apply]
        let q : Fin (i.n - 1 + 1) :=
          Fin.cast (Nat.sub_add_cancel i.hn).symm j
        change
          -(Fin.cases (0 : ℝ) (i.leftRealCoordinates (τ + υ)) q : ℝ) =
            -(Fin.cases (0 : ℝ) (i.leftRealCoordinates τ) q : ℝ) +
              -(Fin.cases (0 : ℝ) (i.leftRealCoordinates υ) q : ℝ)
        refine Fin.cases ?_ ?_ q
        · simp
        · intro a
          simp [GeneratorIndex.leftRealCoordinates]
      map_smul' := by
        intro c τ
        rw [← (section43ScalarDiffCLE i.n).symm.map_smul]
        congr 1
        ext j
        unfold chronologicalTimeProfileDisplacementOfPositive
        simp only [Pi.smul_apply]
        let q : Fin (i.n - 1 + 1) :=
          Fin.cast (Nat.sub_add_cancel i.hn).symm j
        change
          -(Fin.cases (0 : ℝ) (i.leftRealCoordinates (c • τ)) q : ℝ) =
            c * -(Fin.cases (0 : ℝ) (i.leftRealCoordinates τ) q : ℝ)
        refine Fin.cases ?_ ?_ q
        · simp
        · intro a
          simp [GeneratorIndex.leftRealCoordinates, smul_eq_mul] }

@[simp] theorem translatedLeftEndpointDisplacementCLM_apply
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    translatedLeftEndpointDisplacementCLM i τ =
      (section43ScalarDiffCLE i.n).symm
        (chronologicalTimeProfileDisplacementOfPositive i.hn
          (i.leftRealCoordinates τ)) :=
  rfl

theorem translatedLeftCommonShift_span
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    ∀ δ ∈ tsupport
        (B.translatedLeftTimeProfile i τ :
          (Fin i.n → ℝ) → ℂ),
      (section43ScalarDiffCLE i.n).symm δ
          (Fin.rev ⟨0, i.hn⟩) <
        B.translatedLeftCommonShift i τ := by
  let h :=
    chronologicalTimeProfileDisplacementOfPositive i.hn
      (i.leftRealCoordinates τ)
  intro δ hδ
  have hδbase :
      δ + h ∈ tsupport
        ((B.leftTimeProfile i).f : (Fin i.n → ℝ) → ℂ) := by
    simpa [translatedLeftTimeProfile, h, tsupport_translateSchwartz_eq_preimage]
      using hδ
  have hbase :=
    B.baseLeftCommonShift_span i (δ + h) hδbase
  have hcoord :
      ‖((section43ScalarDiffCLE i.n).symm h)
          (Fin.rev ⟨0, i.hn⟩)‖ ≤
        ‖(section43ScalarDiffCLE i.n).symm h‖ :=
    norm_le_pi_norm _ _
  have hneg :
      -((section43ScalarDiffCLE i.n).symm h)
          (Fin.rev ⟨0, i.hn⟩) ≤
        ‖(section43ScalarDiffCLE i.n).symm h‖ := by
    calc
      -((section43ScalarDiffCLE i.n).symm h)
          (Fin.rev ⟨0, i.hn⟩) ≤
        |((section43ScalarDiffCLE i.n).symm h)
          (Fin.rev ⟨0, i.hn⟩)| := neg_le_abs _
      _ = ‖((section43ScalarDiffCLE i.n).symm h)
          (Fin.rev ⟨0, i.hn⟩)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖(section43ScalarDiffCLE i.n).symm h‖ := hcoord
  have hsum :
      (section43ScalarDiffCLE i.n).symm (δ + h)
          (Fin.rev ⟨0, i.hn⟩) =
        (section43ScalarDiffCLE i.n).symm δ
            (Fin.rev ⟨0, i.hn⟩) +
          (section43ScalarDiffCLE i.n).symm h
            (Fin.rev ⟨0, i.hn⟩) := by
    rw [(section43ScalarDiffCLE i.n).symm.map_add]
    rfl
  change
    (section43ScalarDiffCLE i.n).symm δ
        (Fin.rev ⟨0, i.hn⟩) <
      B.baseLeftCommonShift i +
        ‖(section43ScalarDiffCLE i.n).symm h‖
  linarith

/-- Every open neighborhood of zero in the finite real parameter space meets
the strict-positive orthant. -/
theorem open_inter_strictPositive_nonempty
    (V : Set (Fin k → ℝ))
    (hVopen : IsOpen V)
    (h0V : (0 : Fin k → ℝ) ∈ V) :
    (V ∩ section43TimeStrictPositiveRegion k).Nonempty := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (hVopen.mem_nhds h0V)
  let τ : Fin k → ℝ := fun _ => ε / 2
  refine ⟨τ, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖τ‖ ≤ ‖ε / 2‖ := by
        simpa [τ] using
          (pi_norm_const_le (ι := Fin k) (ε / 2 : ℝ))
      _ = ε / 2 := by
        rw [Real.norm_of_nonneg]
        linarith
      _ < ε := by linarith
  · intro j
    exact half_pos hε

/-- Reindex the point variables of an honest zero-diagonal source by a finite
equivalence. -/
noncomputable def reindexZeroDiagonalSchwartzCLM
    {n m : ℕ} (σ : Fin n ≃ Fin m) :
    ZeroDiagonalSchwartz d n →L[ℂ]
      ZeroDiagonalSchwartz d m :=
  (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ
        ).toContinuousLinearEquiv)).comp
      (zeroDiagonalSubmodule d n).subtypeL).codRestrict
    (zeroDiagonalSubmodule d m)
    (fun f =>
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        f.2 σ))

@[simp] theorem reindexZeroDiagonalSchwartzCLM_coe
    {n m : ℕ} (σ : Fin n ≃ Fin m)
    (f : ZeroDiagonalSchwartz d n) :
    (reindexZeroDiagonalSchwartzCLM (d := d) σ f).1 =
      reindexSchwartz (d := d) σ f.1 := rfl

/-- Reindexing by the canonical equivalence induced by an equality of
arities does not change the Schwinger value. -/
theorem schwinger_reindex_finCongr
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (h : n = m)
    (f : ZeroDiagonalSchwartz d n) :
    OS.S m
        (reindexZeroDiagonalSchwartzCLM (d := d) (finCongr h) f) =
      OS.S n f := by
  subst m
  have hreindex :
      reindexZeroDiagonalSchwartzCLM
          (d := d) (finCongr rfl) f =
        f := by
    apply Subtype.ext
    ext x
    rfl
  rw [hreindex]

/-- The split-induced zero-diagonal source map, reindexed to the common
`k + 1` absolute-particle arity. -/
noncomputable def generatorSplitAbsoluteSpatialSourceZeroCLM
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hleft :
      tsupport
          (B.translatedLeftTimeProfile i τ :
            (Fin i.n → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.n)
    (hright :
      tsupport
          (B.translatedRightTimeProfile i τ :
            (Fin i.m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.m)
    (ht : 0 ≤ τ i.bridgeGlobalIndex) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (k + 1) :=
  (reindexZeroDiagonalSchwartzCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)).comp
      ((axisPairGlobalAbsoluteSpatialSourceZeroCLM
        i.n i.m i.hn i.hm
        (B.translatedLeftTimeProfile i τ) hleft
        (B.translatedRightTimeProfile i τ) hright
        (B.translatedLeftCommonShift i τ)
        (τ i.bridgeGlobalIndex) ht
        (B.translatedLeftCommonShift_span i τ)).comp
          (generatorSplitSpatialPullbackCLM i))

namespace CommonAbsoluteSpatialSourceGermData

end CommonAbsoluteSpatialSourceGermData

namespace CommonAbsoluteSpatialSourceData

end CommonAbsoluteSpatialSourceData

end GeneratorHermiteHilbertFieldFamilyData

end OSIIChapterV
end OSReconstruction
