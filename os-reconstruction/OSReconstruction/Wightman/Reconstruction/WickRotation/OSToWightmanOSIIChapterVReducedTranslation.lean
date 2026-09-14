/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTimeChartGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.SpectralEquivalence










noncomputable section

open MeasureTheory

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ}

/-- The consecutive-difference displacement induced by an absolute
configuration displacement. -/
def reducedConfigurationDisplacement
    (a : NPointDomain d (m + 1)) :
    NPointDomain d m :=
  fun i μ =>
    BHW.reducedDiffMapReal (m + 1) d a
      ⟨i.val, by omega⟩ μ

@[simp] theorem reducedConfigurationDisplacement_apply
    (a : NPointDomain d (m + 1))
    (i : Fin m)
    (μ : Fin (d + 1)) :
    reducedConfigurationDisplacement a i μ =
      a i.succ μ - a i.castSucc μ := by
  change
    a ⟨i.val + 1, by omega⟩ μ -
        a ⟨i.val, by omega⟩ μ =
      a i.succ μ - a i.castSucc μ
  rfl

private theorem diffVarSection_add_reducedConfigurationDisplacement
    (ξ : NPointDomain d m)
    (a : NPointDomain d (m + 1))
    (j : Fin (m + 1))
    (μ : Fin (d + 1)) :
    diffVarSection d m
        (ξ + reducedConfigurationDisplacement a) j μ =
      diffVarSection d m ξ j μ + a j μ - a 0 μ := by
  induction j using Fin.induction with
  | zero =>
      simp [diffVarSection_zero]
  | succ j ih =>
      rw [diffVarSection_succ, diffVarSection_succ, ih]
      simp only [Pi.add_apply,
        reducedConfigurationDisplacement_apply]
      ring

/-- Basepoint fiber reduction commutes with arbitrary independent
configuration translation. The absolute displacement descends to its
consecutive-difference displacement. -/
theorem diffVarReduction_translateSchwartzConfiguration
    [NeZero d]
    (a : NPointDomain d (m + 1))
    (f : SchwartzNPoint d (m + 1)) :
    diffVarReduction d m (translateSchwartzConfiguration a f) =
      translateSchwartzConfiguration
        (reducedConfigurationDisplacement a)
        (diffVarReduction d m f) := by
  ext ξ
  change
    (∫ b : SpacetimeDim d,
      f (fun j μ => b μ + diffVarSection d m ξ j μ + a j μ)) =
      (∫ b : SpacetimeDim d,
        f (fun j μ =>
          b μ +
            diffVarSection d m
              (ξ + reducedConfigurationDisplacement a) j μ))
  let G : SpacetimeDim d → ℂ := fun b =>
    f (fun j μ =>
      b μ +
        diffVarSection d m
          (ξ + reducedConfigurationDisplacement a) j μ)
  have htranslate :=
    MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (SpacetimeDim d))) G (a 0)
  rw [← htranslate]
  apply integral_congr_ae
  filter_upwards with b
  congr 1
  funext j μ
  rw [diffVarSection_add_reducedConfigurationDisplacement]
  dsimp [G]
  ring

private theorem blockwiseSpacetimeDiff_symm_time
    {d n m : ℕ}
    (q : NPointDomain d (n + m)) :
    (fun i =>
      (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q i 0) =
      (osiiAxisPairBlockwiseTimeDiffCLE n m).symm
        (fun i => q i 0) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    simp [section43ScalarDiffCLE_symm_apply, splitFirst]
  · intro j
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
    simp [section43ScalarDiffCLE_symm_apply, splitLast]

private theorem reflectReverseLeftSpacetime_time
    {d n m : ℕ}
    (x : NPointDomain d (n + m)) :
    (fun i =>
      osiiAxisPairReflectReverseLeftSpacetimeCLE d n m x i 0) =
      osiiAxisPairReflectReverseLeftTimeCLE n m
        (fun i => x i 0) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [timeReflection]
  · intro j
    simp

private theorem section43DiffCoordRealCLE_time
    {d n : ℕ}
    (x : NPointDomain d n) :
    (fun i => section43DiffCoordRealCLE d n x i 0) =
      section43ScalarDiffCLE n (fun i => x i 0) := by
  funext i
  simp [section43ScalarDiffCLE_apply]

private theorem blockGlobalSpacetime_time
    {d n m : ℕ}
    (q : NPointDomain d (n + m)) :
    (fun i => osiiAxisPairBlockGlobalSpacetimeCLE d n m q i 0) =
      osiiAxisPairBlockGlobalTimeCLE n m (fun i => q i 0) := by
  change
    (fun i =>
      section43DiffCoordRealCLE d (n + m)
        (osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)) i 0) =
      section43ScalarDiffCLE (n + m)
        (osiiAxisPairReflectReverseLeftTimeCLE n m
          ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm
            (fun i => q i 0)))
  rw [section43DiffCoordRealCLE_time]
  congr 1
  rw [reflectReverseLeftSpacetime_time,
    blockwiseSpacetimeDiff_symm_time]

private theorem blockGlobalSpacetime_spatial_eq_zero
    {d n m : ℕ}
    (q : NPointDomain d (n + m))
    (hq : ∀ i (μ : Fin d), q i μ.succ = 0)
    (j : Fin (n + m))
    (μ : Fin d) :
    osiiAxisPairBlockGlobalSpacetimeCLE d n m q j μ.succ = 0 := by
  have habs :
      ∀ i,
        (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q i μ.succ = 0 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro r
      rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left,
        section43DiffCoordRealCLE_symm_apply]
      apply Finset.sum_eq_zero
      intro s hs
      exact hq _ μ
    · intro r
      rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right,
        section43DiffCoordRealCLE_symm_apply]
      apply Finset.sum_eq_zero
      intro s hs
      exact hq _ μ
  have hreflect :
      ∀ i,
        osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)
          i μ.succ = 0 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro r
      rw [osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_left]
      simp [timeReflection, habs]
    · intro r
      rw [osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_right]
      exact habs _
  change
    section43DiffCoordRealCLE d (n + m)
      (osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
        ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q))
      j μ.succ = 0
  rw [section43DiffCoordRealCLE_apply]
  split_ifs <;> simp [hreflect]

private def unreflectedSourceParameterDisplacement
    {d k : ℕ}
    (u : Fin (k + k) → ℝ) :
    NPointDomain d ((k + 1) + (k + 1)) :=
  Fin.append
    (sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (fun i => u (Fin.castAdd k i)))
    (sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (fun i => u (Fin.natAdd k i)))

private theorem reflectedSourceParameterDisplacement_permuted
    {d k : ℕ}
    (u : Fin (k + k) → ℝ) :
    (fun i =>
      reflectedSourceParameterDisplacementCLM
        (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r) u
        (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i)) =
      osiiAxisPairReflectReverseLeftSpacetimeCLE d (k + 1) (k + 1)
        (unreflectedSourceParameterDisplacement u) := by
  change
    (fun i =>
      Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM
              (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r)
              (fun r => u (Fin.castAdd k r))))
          (sourceParameterDisplacementCLM
            (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r)
            (fun r => u (Fin.natAdd k r)))
          (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i)) =
      osiiAxisPairReflectReverseLeftSpacetimeCLE d (k + 1) (k + 1)
        (Fin.append
          (sourceParameterDisplacementCLM
            (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r)
            (fun r => u (Fin.castAdd k r)))
          (sourceParameterDisplacementCLM
            (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r)
            (fun r => u (Fin.natAdd k r))))
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [osiiAxisPairLeftBlockReversePerm_castAdd,
      osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_left]
    rw [Fin.append_left, Fin.append_left]
    rfl
  · intro j
    rw [osiiAxisPairLeftBlockReversePerm_natAdd,
      osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_right]
    rw [Fin.append_right, Fin.append_right]

private theorem blockwiseDiff_unreflectedSource_time
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ) :
    (fun i =>
      osiiAxisPairBlockwiseSpacetimeDiffCLE d (k + 1) (k + 1)
        (unreflectedSourceParameterDisplacement u) i 0) =
      reflectedBlockTimeDisplacement u := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_left]
    simp only [unreflectedSourceParameterDisplacement,
      splitFirst_fin_append]
    change
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.castAdd k i)))) j =
        _
    have h :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) (fun i => u (Fin.castAdd k i))
        (0 : NPointDomain d (k + 1)) j
    have h' :
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.castAdd k i)))) j =
        -Fin.cases 0 (fun i => u (Fin.castAdd k i)) j := by
      simpa [section43QTime, nPointTimeSpatialCLE] using h
    rw [h']
    refine Fin.cases ?_ (fun r => ?_) j
    · simpa using (reflectedBlockTimeDisplacement_left_zero u).symm
    · simpa using (reflectedBlockTimeDisplacement_left_succ u r).symm
  · intro j
    rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_right]
    simp only [unreflectedSourceParameterDisplacement,
      splitLast_fin_append]
    change
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.natAdd k i)))) j =
        _
    have h :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) (fun i => u (Fin.natAdd k i))
        (0 : NPointDomain d (k + 1)) j
    have h' :
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.natAdd k i)))) j =
        -Fin.cases 0 (fun i => u (Fin.natAdd k i)) j := by
      simpa [section43QTime, nPointTimeSpatialCLE] using h
    rw [h']
    refine Fin.cases ?_ (fun r => ?_) j
    · simpa using
        (reflectedBlockTimeDisplacement_right_zero u).symm
    · simpa using
        (reflectedBlockTimeDisplacement_right_succ u r).symm

private theorem blockwiseDiff_unreflectedSource_spatial_eq_zero
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ)
    (i : Fin ((k + 1) + (k + 1)))
    (μ : Fin d) :
    osiiAxisPairBlockwiseSpacetimeDiffCLE d (k + 1) (k + 1)
      (unreflectedSourceParameterDisplacement u) i μ.succ = 0 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_left]
    simp only [unreflectedSourceParameterDisplacement,
      splitFirst_fin_append]
    have h :=
      chronologicalSourceParameterDisplacement_diff_spatial
        (d := d) (fun i => u (Fin.castAdd k i))
        (0 : NPointDomain d (k + 1))
    have hj := congrFun
      (congrArg
        (fun z : EuclideanSpace ℝ (Fin (k + 1) × Fin d) =>
          (EuclideanSpace.equiv (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ) z))
        h) (j, μ)
    have hj' :
        section43DiffCoordRealCLE d (k + 1)
            (0 + sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.castAdd k i))) j μ.succ = 0 := by
      simpa only [section43QSpatial_apply, map_zero,
        Pi.zero_apply] using hj
    simpa only [zero_add] using hj'
  · intro j
    rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_right]
    simp only [unreflectedSourceParameterDisplacement,
      splitLast_fin_append]
    have h :=
      chronologicalSourceParameterDisplacement_diff_spatial
        (d := d) (fun i => u (Fin.natAdd k i))
        (0 : NPointDomain d (k + 1))
    have hj := congrFun
      (congrArg
        (fun z : EuclideanSpace ℝ (Fin (k + 1) × Fin d) =>
          (EuclideanSpace.equiv (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ) z))
        h) (j, μ)
    have hj' :
        section43DiffCoordRealCLE d (k + 1)
            (0 + sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
              (fun i => u (Fin.natAdd k i))) j μ.succ = 0 := by
      simpa only [section43QSpatial_apply, map_zero,
        Pi.zero_apply] using hj
    simpa only [zero_add] using hj'

/-- The doubled Chapter V displacement as a spacetime difference
configuration: the reflected reduced time displacement sits in the time
component and every spatial component is zero. -/
def reflectedReducedSpacetimeDisplacement
    {d k : ℕ}
    (u : Fin (k + k) → ℝ) :
    NPointDomain d (k + (k + 1)) :=
  fun j μ =>
    Fin.cases (reflectedReducedTimeDisplacement u j) (fun _ => 0) μ

@[simp] theorem reflectedReducedSpacetimeDisplacement_time
    {d k : ℕ}
    (u : Fin (k + k) → ℝ)
    (j : Fin (k + (k + 1))) :
    reflectedReducedSpacetimeDisplacement (d := d) u j 0 =
      reflectedReducedTimeDisplacement u j := by
  rfl

@[simp] theorem reflectedReducedSpacetimeDisplacement_spatial
    {d k : ℕ}
    (u : Fin (k + k) → ℝ)
    (j : Fin (k + (k + 1)))
    (μ : Fin d) :
    reflectedReducedSpacetimeDisplacement (d := d) u j μ.succ = 0 := by
  rfl

/-- After restoring chronological order in the reflected left block, the tail
of the global difference chart is exactly the doubled Chapter V spacetime
displacement. -/
theorem section43Diff_permuted_reflectedSourceParameterDisplacement_tail
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ)
    (j : Fin (k + (k + 1)))
    (μ : Fin (d + 1)) :
    section43DiffCoordRealCLE d ((k + 1) + (k + 1))
        (fun i =>
          reflectedSourceParameterDisplacementCLM
            (fun r : Fin k =>
              chronologicalTimeSourceDirection (d := d) r) u
            (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i))
        ⟨j.val + 1, by omega⟩ μ =
      reflectedReducedSpacetimeDisplacement (d := d) u j μ := by
  let pre := unreflectedSourceParameterDisplacement (d := d) u
  let q :=
    osiiAxisPairBlockwiseSpacetimeDiffCLE d (k + 1) (k + 1) pre
  have hsource :
      (fun i =>
        reflectedSourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u
          (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i)) =
        osiiAxisPairReflectReverseLeftSpacetimeCLE d (k + 1) (k + 1) pre := by
    exact reflectedSourceParameterDisplacement_permuted u
  have hglobal :
      section43DiffCoordRealCLE d ((k + 1) + (k + 1))
          (fun i =>
            reflectedSourceParameterDisplacementCLM
              (fun r : Fin k =>
                chronologicalTimeSourceDirection (d := d) r) u
              (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1) i)) =
        osiiAxisPairBlockGlobalSpacetimeCLE d (k + 1) (k + 1) q := by
    rw [hsource]
    change
      section43DiffCoordRealCLE d ((k + 1) + (k + 1))
          (osiiAxisPairReflectReverseLeftSpacetimeCLE d (k + 1) (k + 1) pre) =
        section43DiffCoordRealCLE d ((k + 1) + (k + 1))
          (osiiAxisPairReflectReverseLeftSpacetimeCLE d (k + 1) (k + 1)
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE
              d (k + 1) (k + 1)).symm q))
    rw [show
      (osiiAxisPairBlockwiseSpacetimeDiffCLE
          d (k + 1) (k + 1)).symm q = pre by
      exact (osiiAxisPairBlockwiseSpacetimeDiffCLE
        d (k + 1) (k + 1)).symm_apply_apply pre]
  rw [hglobal]
  refine Fin.cases ?_ (fun ν => ?_) μ
  · rw [congrFun (blockGlobalSpacetime_time q)
      ⟨j.val + 1, by omega⟩]
    rw [show (fun i => q i 0) = reflectedBlockTimeDisplacement u by
      exact blockwiseDiff_unreflectedSource_time u]
    exact
      osiiAxisPairBlockGlobalTimeCLE_reflectedBlockTimeDisplacement_tail u j
  · exact blockGlobalSpacetime_spatial_eq_zero q
      (blockwiseDiff_unreflectedSource_spatial_eq_zero u)
      ⟨j.val + 1, by omega⟩ ν

/-- The arity-normalized absolute displacement obtained by first restoring
chronological order in the reflected-left block. -/
def reflectedReducedAbsoluteDisplacement
    {d k : ℕ}
    (u : Fin (k + k) → ℝ) :
    NPointDomain d ((k + (k + 1)) + 1) :=
  fun j =>
    reflectedSourceParameterDisplacementCLM
      (fun r : Fin k => chronologicalTimeSourceDirection (d := d) r) u
      (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
        ((finCongr (by omega :
          ((k + 1) + (k + 1)) = ((k + (k + 1)) + 1))).symm j))

/-- Consecutive-difference reduction of the reflected, reordered absolute
source displacement is the exact spacetime displacement used by the reduced
Chapter V chart. -/
theorem reducedConfigurationDisplacement_reflectedReducedAbsoluteDisplacement
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ) :
    reducedConfigurationDisplacement
        (reflectedReducedAbsoluteDisplacement (d := d) u) =
      reflectedReducedSpacetimeDisplacement (d := d) u := by
  ext j μ
  rw [reducedConfigurationDisplacement_apply]
  let e : Fin ((k + 1) + (k + 1)) ≃
      Fin ((k + (k + 1)) + 1) :=
    finCongr (by omega)
  have hsucc :
      e.symm j.succ = (⟨j.val + 1, by omega⟩ :
        Fin ((k + 1) + (k + 1))) := by
    ext
    rfl
  have hprev :
      e.symm j.castSucc = (⟨j.val, by omega⟩ :
        Fin ((k + 1) + (k + 1))) := by
    ext
    rfl
  change
    reflectedSourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u
          (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
            (e.symm j.succ)) μ -
        reflectedSourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u
          (osiiAxisPairLeftBlockReversePerm (k + 1) (k + 1)
            (e.symm j.castSucc)) μ =
      reflectedReducedSpacetimeDisplacement (d := d) u j μ
  rw [hsucc, hprev]
  rw [←
    section43Diff_permuted_reflectedSourceParameterDisplacement_tail
      (d := d) u j μ]
  rw [section43DiffCoordRealCLE_apply]
  rw [dif_neg (Nat.succ_ne_zero j.val)]
  congr 1

/-- The full reflected source translation therefore descends through
`diffVarReduction` to the exact reduced Chapter V spacetime translation. -/
theorem diffVarReduction_translate_reflectedReducedAbsoluteDisplacement
    {d k : ℕ} [NeZero d]
    (u : Fin (k + k) → ℝ)
    (f : SchwartzNPoint d ((k + (k + 1)) + 1)) :
    diffVarReduction d (k + (k + 1))
        (translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) u) f) =
      translateSchwartzConfiguration
        (reflectedReducedSpacetimeDisplacement (d := d) u)
        (diffVarReduction d (k + (k + 1)) f) := by
  rw [diffVarReduction_translateSchwartzConfiguration,
    reducedConfigurationDisplacement_reflectedReducedAbsoluteDisplacement]

end OSIIChapterV
end OSReconstruction
