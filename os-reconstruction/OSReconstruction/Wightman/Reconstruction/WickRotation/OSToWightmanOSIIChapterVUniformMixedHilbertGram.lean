/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedGram














open Complex Topology Filter
open scoped BigOperators Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- A common holomorphic Hilbert-field family together with pair-indexed
scalar continuations computing every mixed inner product near the origin. -/
structure UniformCompactTimeMixedHilbertGramFamilyData
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f) where
  hilbert : UniformCompactTimeSourceHilbertFieldFamilyData OS f
  cauchyRadius : ℝ
  cauchyRadius_pos : 0 < cauchyRadius
  cauchy : ι → ι → ReflectedCauchyPolydiscData (q + 1)
  cauchy_center :
    ∀ a b, (cauchy a b).center = 0
  cauchy_radius :
    ∀ a b, (cauchy a b).radius = cauchyRadius
  cauchy_holomorphic :
    ∀ a b,
      DifferentiableOn ℂ (cauchy a b).scalar
        (reflectedMovingSliceCarrier stage germ.η)
  cauchy_closed :
    ∀ a b,
      SCV.closedPolydisc
          (cauchy a b).center (fun _ => (cauchy a b).radius) ⊆
        reflectedMovingSliceCarrier stage germ.η
  cauchy_scalar :
    ∀ a b,
      (cauchy a b).scalar =
        reflectedMovingSliceScalar stage germ.η
          (diffVarReduction d ((q + 1) + ((q + 1) + 1))
            (mixedReflectedChronologicalSource
              (f a).1 (f b).1))
  cauchy_realEdge :
    ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
      ∀ a b,
        realAffineSlice
            (cauchy a b).scalar (cauchy a b).center u =
          OS.S (((q + 1) + 1) + ((q + 1) + 1))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f a).1.osConjTensorProduct (f b).1)))
  gramRadius : ℝ
  gramRadius_pos : 0 < gramRadius
  gramRadius_lt_hilbert : gramRadius < hilbert.radius
  gramRadius_lt_cauchy : gramRadius < cauchyRadius
  gram_carrier :
    ∀ z : Fin (q + 1) → ℂ, ‖z‖ < gramRadius →
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier stage germ.η
  mixed_inner :
    ∀ a b (z : Fin (q + 1) → ℂ), ‖z‖ < gramRadius →
      @inner ℂ (OSHilbertSpace OS) _
          (hilbert.field a z) (hilbert.field b z) =
        (cauchy a b).scalar
          ((cauchy a b).center + reflectedCauchyIncrement z)

/-- A diagonal Hilbert-field construction and a mixed stage-orbit source edge
are independent inputs to the mixed Gram step.  This is the non-circular
constructor used when the diagonal norm-square argument is available before
the mixed spacetime distribution has been constructed. -/
theorem
    exists_uniformCompactTimeMixedHilbertGramFamilyData_of_hilbertField_of_stageOrbitSource
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (H : UniformCompactTimeSourceHilbertFieldFamilyData OS f)
    (S : UniformCompactTimeMixedStageOrbitSourceData OS f) :
    Nonempty
      (UniformCompactTimeMixedHilbertGramFamilyData
        OS f S.stage S.germ) := by
  obtain ⟨Rw, hRw, hclosedRw⟩ :=
    exists_reflectedMovingSlice_closedPolydisc
      S.stage S.germ.η S.germ.η_compact
      (tsupport
        (S.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
      (fun _ h => h) S.cutoffCarrier
  let R : ℝ := min (H.radius / 2) (Rw / 2)
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min (half_pos H.radius_pos) (half_pos hRw)
  have hR_hilbert : R < H.radius := by
    exact (min_le_left _ _).trans_lt (half_lt_self H.radius_pos)
  have hR_Rw : R < Rw := by
    exact (min_le_right _ _).trans_lt (half_lt_self hRw)
  have hclosed :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R) ⊆
        reflectedMovingSliceCarrier S.stage S.germ.η := by
    intro w hw
    exact hclosedRw
      (SCV.closedPolydisc_mono (fun _ => le_of_lt hR_Rw) hw)
  obtain ⟨D, hD, hreal⟩ :=
    S.exists_mixedReflectedCauchyPolydiscFamilyData_of_radius
      OS f R hR hclosed
  let cauchy : ι → ι → ReflectedCauchyPolydiscData (q + 1) :=
    fun a b => D (a, b)
  let cauchyDimension : ℕ := (q + 1) + (q + 1) - 1
  let gramRadius : ℝ :=
    R / (2 * ((cauchyDimension : ℝ) + 2))
  have hdenom : 0 < 2 * ((cauchyDimension : ℝ) + 2) := by
    positivity
  have hgramRadius : 0 < gramRadius := div_pos hR hdenom
  have hgramRadius_R : gramRadius < R := by
    dsimp [gramRadius]
    rw [div_lt_iff₀ hdenom]
    have hc : 0 ≤ (cauchyDimension : ℝ) := Nat.cast_nonneg _
    nlinarith
  refine ⟨{
    hilbert := H
    cauchyRadius := R
    cauchyRadius_pos := hR
    cauchy := cauchy
    cauchy_center := fun a b => (hD (a, b)).1
    cauchy_radius := fun a b => (hD (a, b)).2.1
    cauchy_holomorphic := fun a b => (hD (a, b)).2.2.2.1
    cauchy_closed := fun a b => (hD (a, b)).2.2.1
    cauchy_scalar := fun a b => by
      simpa [cauchy] using (hD (a, b)).2.2.2.2
    cauchy_realEdge := by
      simpa [cauchy] using hreal
    gramRadius := gramRadius
    gramRadius_pos := hgramRadius
    gramRadius_lt_hilbert :=
      hgramRadius_R.trans hR_hilbert
    gramRadius_lt_cauchy := hgramRadius_R
    gram_carrier := by
      intro z hz
      apply hclosed
      intro j
      change dist (reflectedCauchyIncrement z j) 0 ≤ R
      rw [dist_zero_right]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [reflectedCauchyIncrement_left]
        simpa using
          ((norm_le_pi_norm z i).trans_lt
            (hz.trans hgramRadius_R)).le
      · rw [reflectedCauchyIncrement_right]
        exact
          ((norm_le_pi_norm z i).trans_lt
            (hz.trans hgramRadius_R)).le
    mixed_inner := ?_ }⟩
  intro a b z hz
  have hzH :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => H.radius) := by
    intro i
    change dist (z i) 0 < H.radius
    rw [dist_zero_right]
    exact (norm_le_pi_norm z i).trans_lt
      (hz.trans (hgramRadius_R.trans hR_hilbert))
  have hincrement :
      ∀ i, ‖reflectedCauchyIncrement z i‖ <
        (cauchy a b).radius := by
    intro j
    rw [(hD (a, b)).2.1]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [reflectedCauchyIncrement_left]
      simpa using
        (norm_le_pi_norm z i).trans_lt (hz.trans hgramRadius_R)
    · rw [reflectedCauchyIncrement_right]
      exact (norm_le_pi_norm z i).trans_lt
        (hz.trans hgramRadius_R)
  have hreal_ab :
      (fun u : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice
          (cauchy a b).scalar (cauchy a b).center u) =ᶠ[𝓝 0]
        (fun u =>
          OS.S (((q + 1) + 1) + ((q + 1) + 1))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun r : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) r) u)
                ((f a).1.osConjTensorProduct (f b).1)))) :=
    hreal.mono (fun _ hu => hu (a, b))
  have hreflected_le :
      ‖reflectedCauchyIncrement z‖ ≤ ‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [reflectedCauchyIncrement_left]
      simpa using norm_le_pi_norm z i
    · rw [reflectedCauchyIncrement_right]
      exact norm_le_pi_norm z i
  have hreflected :
      ‖reflectedCauchyIncrement z‖ <
        R / (2 * ((((q + 1) + (q + 1) - 1 : ℕ) : ℝ) + 2)) := by
    exact hreflected_le.trans_lt
      (by simpa [gramRadius, cauchyDimension] using hz)
  apply H.inner_eq_mixedScalar_of_realEdge_compactTime_of_norm_lt
    (hTowerC := hTowerC)
    (hTowerPi := hTowerPi)
    (OS := OS)
    (f := f)
    (hf := hf)
    (a := a)
    (b := b)
    (zL := z)
    (zR := z)
    (hzL := hzH)
    (hzR := hzH)
    (D := cauchy a b)
    (Rw := Rw)
    (U := reflectedMovingSliceCarrier S.stage S.germ.η)
  · simpa [mixedReflectedCauchyIncrement_self] using hincrement
  · simpa [cauchy, (hD (a, b)).2.1] using hR_Rw
  · exact
      isOpen_reflectedMovingSliceCarrier
        S.stage S.germ.η S.germ.η_compact
  · simpa [cauchy, (hD (a, b)).1] using hclosedRw
  · exact (hD (a, b)).2.2.2.1
  · simpa [cauchy] using hreal_ab
  · simpa [mixedReflectedCauchyIncrement_self, cauchy,
      (hD (a, b)).2.1] using hreflected

/-- A mixed stage-orbit source edge supplies its own diagonal scalar Cauchy
family, so no independently represented diagonal predecessor is needed to
construct the common Hilbert fields. -/
theorem
    exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_stageOrbitSource
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (S : UniformCompactTimeMixedStageOrbitSourceData OS f) :
    Nonempty (UniformCompactTimeSourceHilbertFieldFamilyData OS f) := by
  obtain ⟨Rw, hRw, hclosedRw⟩ :=
    exists_reflectedMovingSlice_closedPolydisc
      S.stage S.germ.η S.germ.η_compact
      (tsupport
        (S.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
      (fun _ h => h) S.cutoffCarrier
  let R : ℝ := Rw / 2
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRRw : R < Rw := by
    dsimp [R]
    linarith
  have hclosed :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => R) ⊆
        reflectedMovingSliceCarrier S.stage S.germ.η := by
    intro w hw
    exact hclosedRw
      (SCV.closedPolydisc_mono (fun _ => le_of_lt hRRw) hw)
  obtain ⟨D, hD, hreal⟩ :=
    S.exists_mixedReflectedCauchyPolydiscFamilyData_of_radius
      OS f R hR hclosed
  let diagonal : ι → ReflectedCauchyPolydiscData (q + 1) :=
    fun a => D (a, a)
  apply
    exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_cauchyFamily
      hTowerC hTowerPi OS f hf S.stage S.germ.η S.germ.η_compact
      R Rw hR hRRw hclosedRw diagonal
  · intro a
    exact (hD (a, a)).1
  · intro a
    exact (hD (a, a)).2.1
  · intro a
    exact (hD (a, a)).2.2.1
  · intro a
    exact (hD (a, a)).2.2.2.1
  · filter_upwards [hreal] with u hu
    intro a
    simpa [diagonal] using hu (a, a)

/-- The direct mixed source edge contains both the diagonal Hilbert-field
input and every off-diagonal scalar continuation needed for the Gram
identity. -/
theorem
    exists_uniformCompactTimeMixedHilbertGramFamilyData_of_stageOrbitSource
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (S : UniformCompactTimeMixedStageOrbitSourceData OS f) :
    Nonempty
      (UniformCompactTimeMixedHilbertGramFamilyData
        OS f S.stage S.germ) := by
  obtain ⟨H⟩ :=
    exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_stageOrbitSource
      hTowerC hTowerPi OS f hf S
  exact
    exists_uniformCompactTimeMixedHilbertGramFamilyData_of_hilbertField_of_stageOrbitSource
      hTowerC hTowerPi OS f hf H S

end OSIIChapterV
end OSReconstruction
