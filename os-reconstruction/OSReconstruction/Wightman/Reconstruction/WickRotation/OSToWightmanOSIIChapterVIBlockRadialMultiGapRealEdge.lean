/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFrozenSource
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZApproximation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockTranslation

noncomputable section

open Matrix Set
open scoped Classical

namespace OSReconstruction

def osiiAxisPairOppositeEquiv (d : Nat) :
    osiiAxisPairIndex d ≃ osiiAxisPairIndex d where
  toFun := osiiAxisPairOpposite
  invFun := osiiAxisPairOpposite
  left_inv := osiiAxisPairOpposite_opposite
  right_inv := osiiAxisPairOpposite_opposite

theorem euclideanParity_mulVec_axisPairDir
    (d : Nat) [NeZero d]
    (T : Real) (a : osiiAxisPairIndex d) :
    (osiiStep4EuclideanParityMatrix d).mulVec
        (osiiAxisPairDir (d := d) T a) =
      osiiAxisPairDir (d := d) T (osiiAxisPairOpposite a) := by
  ext mu
  rcases a with ⟨j, s⟩
  refine Fin.cases ?_ ?_ mu
  · simp [osiiAxisPairDir, osiiAxisPairOpposite]
  · intro l
    by_cases hlj : l = j
    · subst l
      cases s <;> simp [osiiAxisPairDir, osiiAxisPairOpposite]
    · have hjl : j ≠ l := Ne.symm hlj
      cases s <;>
        simp [osiiAxisPairDir, osiiAxisPairOpposite, hjl]

theorem euclideanParity_mulVec_axisPairGapTranslation
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    (osiiStep4EuclideanParityMatrix d).mulVec
        (osiiAxisPairChronologicalGapTranslation T x i) =
      osiiAxisPairChronologicalGapTranslation T
        (fun j a => x j (osiiAxisPairOpposite a)) i := by
  rw [osiiAxisPairChronologicalGapTranslation,
    osiiAxisPairChronologicalGapTranslation,
    Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, euclideanParity_mulVec_axisPairDir]
  let e := osiiAxisPairOppositeEquiv d
  have hsum := e.sum_comp
    (fun a : osiiAxisPairIndex d =>
      osiiAxisPairPositiveCoefficients (x i)
          (osiiAxisPairOpposite a) •
        osiiAxisPairDir (d := d) T a)
  dsimp [e, osiiAxisPairOppositeEquiv] at hsum
  simpa [osiiAxisPairPositiveCoefficients,
    osiiAxisPairOpposite_opposite] using hsum

def osiiStep4MultiGapSpectatorCenter
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (selected : Fin k)
    (center : Fin (k * (d + 1)) -> Real) :
    Fin (k * (d + 1)) -> Real :=
  fun a =>
    let p := finProdFinEquiv.symm a
    center a + if p.1 = selected then 0
      else osiiAxisPairChronologicalGapTranslation T x p.1 p.2

@[simp] theorem osiiStep4MultiGapSpectatorCenter_selected
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (selected : Fin k)
    (center : Fin (k * (d + 1)) -> Real)
    (mu : Fin (d + 1)) :
    osiiStep4MultiGapSpectatorCenter d T x selected center
        (finProdFinEquiv (selected, mu)) =
      center (finProdFinEquiv (selected, mu)) := by
  simp [osiiStep4MultiGapSpectatorCenter]

@[simp] theorem osiiStep4MultiGapSpectatorCenter_other
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (selected j : Fin k) (hj : j ≠ selected)
    (center : Fin (k * (d + 1)) -> Real)
    (mu : Fin (d + 1)) :
    osiiStep4MultiGapSpectatorCenter d T x selected center
        (finProdFinEquiv (j, mu)) =
      center (finProdFinEquiv (j, mu)) +
        osiiAxisPairChronologicalGapTranslation T x j mu := by
  simp [osiiStep4MultiGapSpectatorCenter, hj]

@[simp] theorem osiiStep4MultiGapSplitBlockEquiv_selected
    {k : Nat} (i : Fin k) :
    osiiStep4MultiGapSplitBlockEquiv i
        (osiiStep4SelectedBlockIndex
          i.val (osiiStep4MultiGapAfterCount i)) = i := by
  apply Fin.ext
  simp [osiiStep4MultiGapSplitBlockEquiv]

theorem osiiStep4MultiGapSpectatorCenter_time_lower
    (d k : Nat) [NeZero d]
    {rho : Real}
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (selected : Fin k)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    forall j : Fin k,
      rho / 2 <= osiiStep4MultiGapSpectatorCenter d T x selected center
        (finProdFinEquiv (j, (0 : Fin (d + 1)))) := by
  intro j
  by_cases hj : j = selected
  · subst j
    simpa using hcenter selected
  · rw [osiiStep4MultiGapSpectatorCenter_other d T x selected j hj]
    have hgap : 0 <=
        osiiAxisPairChronologicalGapTranslation T x j 0 := by
      apply axisPairFullTranslation_time_nonneg d T (by linarith)
      intro a
      exact (osiiAxisPairPositiveCoefficients_pos (x j) a).le
    linarith [hcenter j]

theorem axisPairChronologicalGapTranslation_congr
    (d k : Nat) [NeZero d]
    (T : Real)
    {x z : Fin k -> osiiAxisPairIndex d -> Real}
    (i : Fin k)
    (h : forall a, x i a = z i a) :
    osiiAxisPairChronologicalGapTranslation T x i =
      osiiAxisPairChronologicalGapTranslation T z i := by
  unfold osiiAxisPairChronologicalGapTranslation
  apply Finset.sum_congr rfl
  intro a ha
  rw [show osiiAxisPairPositiveCoefficients (x i) a =
      osiiAxisPairPositiveCoefficients (z i) a by
    simp [osiiAxisPairPositiveCoefficients, h a]]

theorem osiiStep4MultiGapSpectatorCenter_congr_of_eq_off_selected
    (d k : Nat) [NeZero d]
    (T : Real)
    {x z : Fin k -> osiiAxisPairIndex d -> Real}
    (q : osiiAxisPairMultiGapIndex d k)
    (h : forall p, p ≠ q -> x p.1 p.2 = z p.1 p.2)
    (center : Fin (k * (d + 1)) -> Real) :
    osiiStep4MultiGapSpectatorCenter d T x q.1 center =
      osiiStep4MultiGapSpectatorCenter d T z q.1 center := by
  funext a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  by_cases hi : i = q.1
  · subst i
    simp
  · rw [osiiStep4MultiGapSpectatorCenter_other d T x q.1 i hi,
      osiiStep4MultiGapSpectatorCenter_other d T z q.1 i hi]
    congr 1
    apply congrFun
    apply axisPairChronologicalGapTranslation_congr d k T i
    intro b
    exact h (i, b) (by
      intro heq
      exact hi (congrArg Prod.fst heq))

theorem parityReversedBefore_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4ParityReversedBeforeRealBlocks
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center)) =
      osiiStep4ParityReversedBeforeRealBlocks
          d i.val (osiiStep4MultiGapAfterCount i)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i center) +
        osiiStep4AxisPairGapTranslationFlat d T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) := by
  ext a
  obtain ⟨⟨j, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [Pi.add_apply,
    osiiStep4ParityReversedBeforeRealBlocks_apply,
    osiiStep4ParityReversedBeforeRealBlocks_apply]
  rw [osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  let b := osiiStep4MultiGapSplitBlockEquiv i
    (osiiStep4ReversedBeforeBlockIndex
      i.val (osiiStep4MultiGapAfterCount i) j)
  change
    (osiiStep4EuclideanParityMatrix d).mulVec
        (fun nu => osiiStep4MultiGapSpectatorCenter d T x i center
          (finProdFinEquiv (b, nu))) mu =
      (osiiStep4EuclideanParityMatrix d).mulVec
          (fun nu => center (finProdFinEquiv (b, nu))) mu +
        osiiAxisPairChronologicalGapTranslation T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j mu
  have hb : b ≠ i := multiGapSplitBlockEquiv_reversedBefore_ne i j
  have hspectator :
      (fun nu => osiiStep4MultiGapSpectatorCenter d T x i center
        (finProdFinEquiv (b, nu))) =
      (fun nu => center (finProdFinEquiv (b, nu))) +
        osiiAxisPairChronologicalGapTranslation T x b := by
    funext nu
    simp [hb]
  rw [hspectator, Matrix.mulVec_add]
  rw [euclideanParity_mulVec_axisPairGapTranslation]
  rfl

theorem afterRealBlocks_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4AfterRealBlocks
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center)) =
      osiiStep4AfterRealBlocks
          i.val (osiiStep4MultiGapAfterCount i) (d + 1)
          (osiiStep4MultiGapSplitCoordinates (d + 1) i center) +
        osiiStep4AxisPairGapTranslationFlat d T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) := by
  ext a
  obtain ⟨⟨j, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [Pi.add_apply, osiiStep4AfterRealBlocks_apply,
    osiiStep4AfterRealBlocks_apply]
  rw [osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  let b := osiiStep4MultiGapSplitBlockEquiv i
    (osiiStep4AfterBlockIndex
      i.val (osiiStep4MultiGapAfterCount i) j)
  change
    osiiStep4MultiGapSpectatorCenter d T x i center
        (finProdFinEquiv (b, mu)) =
      center (finProdFinEquiv (b, mu)) +
        osiiAxisPairChronologicalGapTranslation T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j mu
  have hb : b ≠ i := multiGapSplitBlockEquiv_after_ne i j
  rw [osiiStep4MultiGapSpectatorCenter_other d T x i b hb]
  rfl

theorem selectedRealBlock_split_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4SelectedRealBlock
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center)) =
      osiiStep4SelectedRealBlock
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center) := by
  ext mu
  rw [osiiStep4SelectedRealBlock_apply,
    osiiStep4SelectedRealBlock_apply]
  change
    osiiStep4MultiGapSpectatorCenter d T x i center
        (finProdFinEquiv
          (osiiStep4MultiGapSplitBlockEquiv i
            (osiiStep4SelectedBlockIndex
              i.val (osiiStep4MultiGapAfterCount i)), mu)) =
      center
        (finProdFinEquiv
          (osiiStep4MultiGapSplitBlockEquiv i
            (osiiStep4SelectedBlockIndex
              i.val (osiiStep4MultiGapAfterCount i)), mu))
  rw [osiiStep4MultiGapSplitBlockEquiv_selected]
  exact osiiStep4MultiGapSpectatorCenter_selected d T x i center mu

theorem addSelectedBlock_split_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4AddSelectedRealBlock
        i.val (osiiStep4MultiGapAfterCount i) (d + 1)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center))
        (osiiAxisPairChronologicalGapTranslation T x i) =
      osiiStep4MultiGapSplitCoordinates (d + 1) i
        (center + osiiStep4AxisPairGapTranslationFlat d T x) := by
  ext a
  obtain ⟨⟨j, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  simp only [osiiStep4AddSelectedRealBlock,
    finProdFinEquiv.symm_apply_apply,
    osiiStep4MultiGapSplitCoordinates,
    osiiStep4MultiGapSplitCoordinateEquiv_finProdFinEquiv,
    Pi.add_apply,
    osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  let selected := osiiStep4SelectedBlockIndex
    i.val (osiiStep4MultiGapAfterCount i)
  let b := osiiStep4MultiGapSplitBlockEquiv i j
  have hselected : osiiStep4MultiGapSplitBlockEquiv i selected = i :=
    osiiStep4MultiGapSplitBlockEquiv_selected i
  have hiff : j = selected ↔ b = i := by
    constructor
    · intro hj
      subst j
      exact hselected
    · intro hb
      apply (osiiStep4MultiGapSplitBlockEquiv i).injective
      have hjmap : osiiStep4MultiGapSplitBlockEquiv i j = i := by
        simpa [b] using hb
      rw [hjmap, hselected]
  change
    osiiStep4MultiGapSpectatorCenter d T x i center
          (finProdFinEquiv (b, mu)) +
        (if j = selected then
          osiiAxisPairChronologicalGapTranslation T x i mu else 0) =
      center (finProdFinEquiv (b, mu)) +
        osiiAxisPairChronologicalGapTranslation T x b mu
  by_cases hj : j = selected
  · have hb : b = i := hiff.mp hj
    subst b
    simp [hj, hselected]
  · have hb : b ≠ i := fun hbi => hj (hiff.mpr hbi)
    rw [osiiStep4MultiGapSpectatorCenter_other d T x i b hb]
    simp [hj]

theorem leftEndpointCenter_split_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4SelectedBlockLeftEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center)) =
      osiiStep4SelectedBlockLeftEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center) := by
  unfold osiiStep4SelectedBlockLeftEndpointCenter
    osiiStep4SelectedRealBlockHalf
  rw [selectedRealBlock_split_spectatorCenter]

theorem rightEndpointCenter_split_spectatorCenter
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) :
    osiiStep4SelectedBlockRightEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center)) =
      osiiStep4SelectedBlockRightEndpointCenter
        d i.val (osiiStep4MultiGapAfterCount i)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center) := by
  unfold osiiStep4SelectedBlockRightEndpointCenter
    osiiStep4SelectedRealBlockHalf
  rw [selectedRealBlock_split_spectatorCenter]

theorem osiiStep4MultiGapFrozenLeftPositiveSource_eq_selected_spectator
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    osiiStep4MultiGapFrozenLeftPositiveSource
        d k hrho center y y' hcenter T x i =
      (osiiStep4SelectedBlockLeftPositiveTimeSource
        d i.val (osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center))
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower d k i
          (osiiStep4MultiGapSpectatorCenter d T x i center)
          (osiiStep4MultiGapSpectatorCenter_time_lower
            d k T hT x i center hcenter))).1 := by
  rw [osiiStep4MultiGapFrozenLeftPositiveSource_eq_radialEndpoint]
  simp only [osiiStep4SelectedBlockLeftPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource]
  rw [leftEndpointCenter_split_spectatorCenter]
  rw [parityReversedBefore_spectatorCenter]

theorem osiiStep4MultiGapFrozenRightPositiveSource_eq_selected_spectator
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    osiiStep4MultiGapFrozenRightPositiveSource
        d k hrho center y y' hcenter T x i =
      (osiiStep4SelectedBlockRightPositiveTimeSource
        d i.val (osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d T x i center))
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower d k i
          (osiiStep4MultiGapSpectatorCenter d T x i center)
          (osiiStep4MultiGapSpectatorCenter_time_lower
            d k T hT x i center hcenter))).1 := by
  rw [osiiStep4MultiGapFrozenRightPositiveSource_eq_radialEndpoint]
  simp only [osiiStep4SelectedBlockRightPositiveTimeSource,
    osiiStep4RadialEndpointPositiveTimeSource]
  rw [rightEndpointCenter_split_spectatorCenter]
  rw [afterRealBlocks_spectatorCenter]

/-- The canonical OS-side centered-kernel value, before any comparison with
the reduced BVT.  The positivity witness only certifies that the lifted
kernel is a zero-diagonal Euclidean test. -/
noncomputable def osiiStep4FixedRadiusCenteredSchwinger
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    Complex :=
  OS.S (k + 1)
    (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
      d k hrho center y y' hcenter)

theorem osiiStep4FixedRadiusCenteredSchwinger_congr_center
    (d k : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {rho : Real} (hrho : 0 < rho)
    {center center' y y' : Fin (k * (d + 1)) -> Real}
    (hcenterEq : center = center')
    {hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))}
    {hcenter' : forall i : Fin k,
      rho / 2 <= center' (finProdFinEquiv (i, (0 : Fin (d + 1))))} :
    osiiStep4FixedRadiusCenteredSchwinger
        d OS k hrho center y y' hcenter =
      osiiStep4FixedRadiusCenteredSchwinger
        d OS k hrho center' y y' hcenter' := by
  subst center'
  rfl

theorem osiiStep4FixedRadiusCenteredSchwinger_reindex
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {r k : Nat} (h : r = k)
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    {hcenterR : forall i : Fin r,
      rho / 2 <=
        (fun a => center
          (finCongr (congrArg (fun n => n * (d + 1)) h) a))
            (finProdFinEquiv (i, (0 : Fin (d + 1))))}
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiStep4FixedRadiusCenteredSchwinger d OS r hrho
        (fun a => center
          (finCongr (congrArg (fun n => n * (d + 1)) h) a))
        (fun a => y
          (finCongr (congrArg (fun n => n * (d + 1)) h) a))
        (fun a => y'
          (finCongr (congrArg (fun n => n * (d + 1)) h) a))
        hcenterR =
      osiiStep4FixedRadiusCenteredSchwinger
        d OS k hrho center y y' hcenter := by
  subst k
  rfl

theorem osiiStep4FixedRadiusCenteredSchwinger_splitCoordinates
    (d k : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (i : Fin k) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    osiiStep4FixedRadiusCenteredSchwinger d OS
        (i.val + 1 + osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i center)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower
          d k i center hcenter) =
      osiiStep4FixedRadiusCenteredSchwinger
        d OS k hrho center y y' hcenter := by
  exact osiiStep4FixedRadiusCenteredSchwinger_reindex
    d OS (osiiStep4MultiGap_split_count i) hrho center y y' hcenter

/-- Every positive axis-pair gap translation preserves the lower bound on
the real time centers. -/
theorem osiiStep4MultiGapTranslatedCenter_time_lower
    (d k : Nat) [NeZero d]
    {rho : Real}
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))))
    (T : Real) (hT : 1 < T)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    forall j : Fin k,
      rho / 2 <=
        (center + osiiStep4AxisPairGapTranslationFlat d T x)
          (finProdFinEquiv (j, (0 : Fin (d + 1)))) := by
  intro j
  rw [Pi.add_apply,
    osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  exact le_trans (hcenter j)
    (le_add_of_nonneg_right
      (axisPairFullTranslation_time_nonneg
        d T (le_trans (by norm_num) (le_of_lt hT))
        (osiiAxisPairPositiveCoefficients (x j))
        (fun a => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x j) a))))

structure OSIIStep4MultiGapSelectedCommonSlopeData
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) where
  T : Real
  hT : 1 < T
  left_support : forall i a,
    tsupport
        ((osiiStep4MultiGapSelectedLeftPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (i.val + 1) -> Complex) <=
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := i.val + 1)
        (osiiAxisPairRotationData T a).matrix
  right_support : forall i a,
    tsupport
        ((osiiStep4MultiGapSelectedRightPositiveTimeSource
          d k hrho center y y' hcenter i).1 :
          NPointDomain d (osiiStep4MultiGapAfterCount i + 1) -> Complex) <=
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiStep4MultiGapAfterCount i + 1)
        (osiiAxisPairRotationData T a).matrix

namespace OSIIStep4MultiGapUniformCommonSlopeData

/-- Specialize a carrier-level slope to any pair of radial source
parameters.  The resulting selected-source datum retains exactly the same
slope. -/
def toSelectedCommonSlopeData
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (y y' : Fin (k * (d + 1)) -> Real) :
    OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter where
  T := D.T
  hT := D.hT
  left_support := D.left_source_support y y'
  right_support := D.right_source_support y y'

@[simp] theorem toSelectedCommonSlopeData_T
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (y y' : Fin (k * (d + 1)) -> Real) :
    (D.toSelectedCommonSlopeData y y').T = D.T :=
  rfl

end OSIIStep4MultiGapUniformCommonSlopeData

noncomputable def osiiStep4MultiGapSelectedCommonSlopeData
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter :=
  (osiiStep4MultiGapUniformCommonSlopeData
    d k hrho center hcenter).toSelectedCommonSlopeData y y'

@[simp] theorem osiiStep4MultiGapSelectedCommonSlopeData_T
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))) :
    (osiiStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter).T =
      (osiiStep4MultiGapUniformCommonSlopeData
        d k hrho center hcenter).T :=
  rfl

namespace OSIIStep4MultiGapSelectedCommonSlopeData

noncomputable def spectatorPackage
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    OSIIAxisPairCompactCommonSourcePackage
      (osiiStep4SelectedBlockLeftPositiveTimeSource
        d i.val (osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d D.T x i center))
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower d k i
          (osiiStep4MultiGapSpectatorCenter d D.T x i center)
          (osiiStep4MultiGapSpectatorCenter_time_lower
            d k D.T D.hT x i center hcenter))).1
      (osiiStep4SelectedBlockRightPositiveTimeSource
        d i.val (osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (osiiStep4MultiGapSpectatorCenter d D.T x i center))
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower d k i
          (osiiStep4MultiGapSpectatorCenter d D.T x i center)
          (osiiStep4MultiGapSpectatorCenter_time_lower
            d k D.T D.hT x i center hcenter))).1 := by
  let spectator := osiiStep4MultiGapSpectatorCenter d D.T x i center
  let hspectator := osiiStep4MultiGapSpectatorCenter_time_lower
    d k D.T D.hT x i center hcenter
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i spectator
  let splitY := osiiStep4MultiGapSplitCoordinates (d + 1) i y
  let splitY' := osiiStep4MultiGapSplitCoordinates (d + 1) i y'
  let hsplit := osiiStep4MultiGapSplitCoordinates_time_lower
    d k i spectator hspectator
  let leftPositive :=
    (osiiStep4SelectedBlockLeftPositiveTimeSource
      d i.val (osiiStep4MultiGapAfterCount i) hrho
      splitCenter splitY splitY' hsplit).1
  let rightPositive :=
    (osiiStep4SelectedBlockRightPositiveTimeSource
      d i.val (osiiStep4MultiGapAfterCount i) hrho
      splitCenter splitY splitY' hsplit).1
  apply OSIIAxisPairCompactCommonSourcePackage.ofCommonSlope
    leftPositive rightPositive D.T D.hT
  · exact selectedBlockLeftPositiveTimeSource_hasCompactSupport
      d i.val (osiiStep4MultiGapAfterCount i) hrho
      splitCenter splitY splitY' hsplit
  · exact selectedBlockRightPositiveTimeSource_hasCompactSupport
      d i.val (osiiStep4MultiGapAfterCount i) hrho
      splitCenter splitY splitY' hsplit
  · intro a
    dsimp only [leftPositive, splitCenter, splitY, splitY', spectator, hsplit]
    rw [← osiiStep4MultiGapFrozenLeftPositiveSource_eq_selected_spectator
      d k hrho center y y' hcenter D.T D.hT x i]
    exact osiiStep4MultiGapFrozenLeftPositiveSource_support
      d k hrho center y y' hcenter D.T D.hT D.left_support x i a
  · intro a
    dsimp only [rightPositive, splitCenter, splitY, splitY', spectator, hsplit]
    rw [← osiiStep4MultiGapFrozenRightPositiveSource_eq_selected_spectator
      d k hrho center y y' hcenter D.T D.hT x i]
    exact osiiStep4MultiGapFrozenRightPositiveSource_support
      d k hrho center y y' hcenter D.T D.hT D.right_support x i a

@[simp] theorem spectatorPackage_T
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    (D.spectatorPackage x i).T = D.T :=
  rfl

theorem spectatorPackage_realEdge_eq_centeredSchwinger
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    ((D.spectatorPackage x i).toSemigroupPacketFamily OS lgc).realEdge
        (x i) =
      osiiStep4FixedRadiusCenteredSchwinger d OS k hrho
        (center + osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
        (osiiStep4MultiGapTranslatedCenter_time_lower
          d k center hcenter D.T D.hT x) := by
  let spectator := osiiStep4MultiGapSpectatorCenter d D.T x i center
  let hspectator := osiiStep4MultiGapSpectatorCenter_time_lower
    d k D.T D.hT x i center hcenter
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i spectator
  let splitY := osiiStep4MultiGapSplitCoordinates (d + 1) i y
  let splitY' := osiiStep4MultiGapSplitCoordinates (d + 1) i y'
  let hsplit := osiiStep4MultiGapSplitCoordinates_time_lower
    d k i spectator hspectator
  have hedge :=
    selectedBlockAxisPairPacket_realEdge_eq_positiveLiftedSchwinger
    d i.val (osiiStep4MultiGapAfterCount i) OS lgc hrho
    splitCenter splitY splitY' hsplit (D.spectatorPackage x i) (x i)
  have hedge' :
      ((D.spectatorPackage x i).toSemigroupPacketFamily OS lgc).realEdge
          (x i) =
        osiiStep4FixedRadiusCenteredSchwinger d OS
          (i.val + 1 + osiiStep4MultiGapAfterCount i) hrho
          (osiiStep4AddSelectedRealBlock
            i.val (osiiStep4MultiGapAfterCount i) (d + 1)
            splitCenter (osiiAxisPairChronologicalGapTranslation D.T x i))
          splitY splitY'
          (addSelectedRealBlock_time_lower
            d i.val (osiiStep4MultiGapAfterCount i) splitCenter
            (osiiAxisPairChronologicalGapTranslation D.T x i)
            hsplit
            (axisPairFullTranslation_time_nonneg
              d D.T (le_trans (by norm_num) (le_of_lt D.hT))
              (osiiAxisPairPositiveCoefficients (x i))
              (fun a => le_of_lt
                (osiiAxisPairPositiveCoefficients_pos (x i) a)))) := by
    unfold osiiStep4FixedRadiusCenteredSchwinger
    change ((D.spectatorPackage x i).toSemigroupPacketFamily OS lgc).realEdge
      (x i) = OS.S (i.val + 1 + (osiiStep4MultiGapAfterCount i + 1)) _
    simpa [osiiAxisPairChronologicalGapTranslation,
      spectatorPackage_T] using hedge
  rw [hedge']
  calc
    osiiStep4FixedRadiusCenteredSchwinger d OS
        (i.val + 1 + osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4AddSelectedRealBlock
          i.val (osiiStep4MultiGapAfterCount i) (d + 1)
          splitCenter (osiiAxisPairChronologicalGapTranslation D.T x i))
        splitY splitY' _ =
      osiiStep4FixedRadiusCenteredSchwinger d OS
        (i.val + 1 + osiiStep4MultiGapAfterCount i) hrho
        (osiiStep4MultiGapSplitCoordinates (d + 1) i
          (center + osiiStep4AxisPairGapTranslationFlat d D.T x))
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y)
        (osiiStep4MultiGapSplitCoordinates (d + 1) i y')
        (osiiStep4MultiGapSplitCoordinates_time_lower d k i
          (center + osiiStep4AxisPairGapTranslationFlat d D.T x)
          (osiiStep4MultiGapTranslatedCenter_time_lower
            d k center hcenter D.T D.hT x)) :=
      osiiStep4FixedRadiusCenteredSchwinger_congr_center
        d _ OS hrho
          (addSelectedBlock_split_spectatorCenter d k D.T x center i)
    _ = osiiStep4FixedRadiusCenteredSchwinger d OS k hrho
        (center + osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
        (osiiStep4MultiGapTranslatedCenter_time_lower
          d k center hcenter D.T D.hT x) :=
      osiiStep4FixedRadiusCenteredSchwinger_splitCoordinates
        d k OS i hrho
        (center + osiiStep4AxisPairGapTranslationFlat d D.T x) y y' _

set_option maxHeartbeats 800000 in
noncomputable def packetFamily
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter) :
    OSIIAxisPairMultiGapSemigroupPacketFamily d k D.T OS lgc where
  packet := fun x q =>
    { leftArity := q.1.val + 1
      rightArity := osiiStep4MultiGapAfterCount q.1 + 1
      packet :=
        ((D.spectatorPackage x q.1).toSemigroupPacketFamily OS lgc
          ).packet (x q.1) q.2 }
  realEdge := fun x =>
    osiiStep4FixedRadiusCenteredSchwinger d OS k hrho
      (center + osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
      (osiiStep4MultiGapTranslatedCenter_time_lower
        d k center hcenter D.T D.hT x)
  packet_logBranch_congr_of_eq_off_selected := by
    intro x z q hxz
    let P := D.spectatorPackage x q.1
    let Q := D.spectatorPackage z q.1
    have hcenterXZ :=
      osiiStep4MultiGapSpectatorCenter_congr_of_eq_off_selected
        d k D.T q hxz center
    have hleftPositive :
        (osiiStep4SelectedBlockLeftPositiveTimeSource
          d q.1.val (osiiStep4MultiGapAfterCount q.1) hrho
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center))
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y)
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y')
          (osiiStep4MultiGapSplitCoordinates_time_lower d k q.1
            (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center)
            (osiiStep4MultiGapSpectatorCenter_time_lower
              d k D.T D.hT x q.1 center hcenter))).1 =
        (osiiStep4SelectedBlockLeftPositiveTimeSource
          d q.1.val (osiiStep4MultiGapAfterCount q.1) hrho
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter d D.T z q.1 center))
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y)
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y')
          (osiiStep4MultiGapSplitCoordinates_time_lower d k q.1
            (osiiStep4MultiGapSpectatorCenter d D.T z q.1 center)
            (osiiStep4MultiGapSpectatorCenter_time_lower
              d k D.T D.hT z q.1 center hcenter))).1 := by
      simp only [hcenterXZ]
    have hrightPositive :
        (osiiStep4SelectedBlockRightPositiveTimeSource
          d q.1.val (osiiStep4MultiGapAfterCount q.1) hrho
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center))
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y)
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y')
          (osiiStep4MultiGapSplitCoordinates_time_lower d k q.1
            (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center)
            (osiiStep4MultiGapSpectatorCenter_time_lower
              d k D.T D.hT x q.1 center hcenter))).1 =
        (osiiStep4SelectedBlockRightPositiveTimeSource
          d q.1.val (osiiStep4MultiGapAfterCount q.1) hrho
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter d D.T z q.1 center))
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y)
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1 y')
          (osiiStep4MultiGapSplitCoordinates_time_lower d k q.1
            (osiiStep4MultiGapSpectatorCenter d D.T z q.1 center)
            (osiiStep4MultiGapSpectatorCenter_time_lower
              d k D.T D.hT z q.1 center hcenter))).1 := by
      simp only [hcenterXZ]
    have hleft : P.data.left = Q.data.left := by
      rw [P.left_eq, Q.left_eq, hleftPositive]
    have hright : P.data.right = Q.data.right := by
      rw [P.right_eq, Q.right_eq, hrightPositive]
    have hcoeff : forall b, b ≠ q.2 ->
        osiiAxisPairPositiveCoefficients (x q.1) b =
          osiiAxisPairPositiveCoefficients (z q.1) b := by
      intro b hb
      change Real.exp (x q.1 b) = Real.exp (z q.1 b)
      rw [hxz (q.1, b) (by
        intro heq
        exact hb (congrArg Prod.snd heq))]
    let RX :=
      ((P.toSemigroupPacketFamily OS lgc).packet (x q.1) q.2)
    let RZ :=
      ((Q.toSemigroupPacketFamily OS lgc).packet (z q.1) q.2)
    have hRXleft : RX.left = RZ.left := by
      dsimp [RX, RZ, P, Q,
        OSIIAxisPairCompactCommonSourcePackage.toSemigroupPacketFamily,
        OSIIAxisPairCommonSourceData.toSemigroupPacketFamily,
        OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hleft]
    have hRXright : RX.right = RZ.right := by
      dsimp [RX, RZ, P, Q,
        OSIIAxisPairCompactCommonSourcePackage.toSemigroupPacketFamily,
        OSIIAxisPairCommonSourceData.toSemigroupPacketFamily,
        OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hright,
        osiiAxisPairFrozenTranslation_congr_of_eq_off_selected
          D.T q.2 hcoeff]
    have hbranch := OSIIAxisPairRotatedSourcePacket.branch_eq_of_source_eq
      RX RZ hRXleft hRXright OS lgc
    funext r
    exact congrFun hbranch (Complex.exp (r q.1 q.2))
  packet_real_edge := by
    intro x q
    exact
      (((D.spectatorPackage x q.1).toSemigroupPacketFamily OS lgc
        ).packet_real_edge (x q.1) q.2).trans
      (D.spectatorPackage_realEdge_eq_centeredSchwinger
        OS lgc x q.1)

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
