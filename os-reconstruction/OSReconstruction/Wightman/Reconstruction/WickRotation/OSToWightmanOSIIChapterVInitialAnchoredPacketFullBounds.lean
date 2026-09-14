/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketCenteredMZ
import OSReconstruction.SCV.SchwartzComplete














noncomputable section

open Complex Set Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The genuine original-OS packet distributions are bounded on every fixed
full Schwartz source, uniformly in both anchored packet indices. -/
theorem commonPacketOfOS_fullSource_compact_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η)
    (f : SchwartzNPoint d (k + 1)) :
    ∃ C : ℝ, ∀ timeScale level ζ, ζ ∈ K →
      let P := A.commonPacketAt timeScale level
      ‖((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
          OS P.slope P.slope_gt_one (P.ordered a)).pairing f
            (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)‖ ≤ C := by
  let J := ℕ × (ℕ × K)
  have hcoord :
      ∀ j : J,
        let P := A.commonPacketAt j.1 j.2.1
        osiiNarrowTimeLogCoordinate (d := d) P.slope j.2.2.1 ∈
          osiiAxisPairMultiGapLogDomain d k := by
    intro j
    let P := A.commonPacketAt j.1 j.2.1
    exact osiiNarrowTimeLogCoordinate_mapsTo
      P.slope (lt_trans zero_lt_one P.slope_gt_one)
      η hηsum (hK_subset j.2.2.2)
  let T : J →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin (k + 1) => SchwartzSpacetime d) ℂ :=
    fun j =>
      let P := A.commonPacketAt j.1 j.2.1
      ((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).productCMM
          ⟨osiiNarrowTimeLogCoordinate (d := d) P.slope j.2.2.1,
            hcoord j⟩
  have hT_pointwise :
      ∀ fs : Fin (k + 1) → SchwartzSpacetime d,
        ∃ C : ℝ, ∀ j : J, ‖T j fs‖ ≤ C := by
    intro fs
    obtain ⟨C, hC⟩ :=
      A.commonPacket_toSourcewiseMZFamilyAtSlopeOfOS_compact_bound
        OS a fs η hηsum K hK_compact hK_subset
    refine ⟨C, ?_⟩
    intro j
    simpa [T,
      OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.productCMM_apply]
      using hC j.1 j.2.1 j.2.2.1 j.2.2.2
  have hn : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨C, hC, p, hp⟩ := by
    set_option backward.isDefEq.respectTransparency false in
      exact pointwiseBounded_cmm_productHermite_polyBounded T hn hT_pointwise
  let fRe := realPartSchwartz f
  let fIm := imaginaryPartSchwartz f
  let e := GaussianField.productRapidDecayEquiv
    (D := Fin (d + 1) → ℝ) (k + 1) hn
  refine
    ⟨C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) +
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm), ?_⟩
  intro timeScale level ζ hζK
  dsimp only
  let P := A.commonPacketAt timeScale level
  have hz :
      osiiNarrowTimeLogCoordinate (d := d) P.slope ζ ∈
        osiiAxisPairMultiGapLogDomain d k :=
    osiiNarrowTimeLogCoordinate_mapsTo
      P.slope (lt_trans zero_lt_one P.slope_gt_one)
      η hηsum (hK_subset hζK)
  let D :=
    (P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)
  let zs : {z : Fin k → osiiAxisPairIndex d → ℂ //
      z ∈ osiiAxisPairMultiGapLogDomain d k} :=
    ⟨osiiNarrowTimeLogCoordinate (d := d) P.slope ζ, hz⟩
  have hRe :
      ‖D.distribution zs (complexifyRealSchwartz fRe)‖ ≤
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) := by
    apply D.norm_complexifyRealSchwartz_le_of_productHermite
      zs hn C p
    intro m
    simpa [T, J, D, P, zs,
      OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.productCMM]
      using hp (timeScale, (level, ⟨ζ, hζK⟩)) m
  have hIm :
      ‖D.distribution zs (complexifyRealSchwartz fIm)‖ ≤
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm) := by
    apply D.norm_complexifyRealSchwartz_le_of_productHermite
      zs hn C p
    intro m
    simpa [T, J, D, P, zs,
      OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.productCMM]
      using hp (timeScale, (level, ⟨ζ, hζK⟩)) m
  change
    ‖D.pairing f
      (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)‖ ≤
      C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) +
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm)
  rw [D.pairing_of_mem f
    (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ) hz]
  rw [← complexifyRealSchwartz_realPart_add_I_imaginaryPart f]
  rw [map_add, map_smul]
  calc
    ‖D.distribution zs (complexifyRealSchwartz fRe) +
        Complex.I • D.distribution zs (complexifyRealSchwartz fIm)‖
        ≤ ‖D.distribution zs (complexifyRealSchwartz fRe)‖ +
            ‖Complex.I •
              D.distribution zs (complexifyRealSchwartz fIm)‖ :=
      norm_add_le _ _
    _ = ‖D.distribution zs (complexifyRealSchwartz fRe)‖ +
          ‖D.distribution zs (complexifyRealSchwartz fIm)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) +
          C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm) :=
      add_le_add hRe hIm

/-- Original-OS packet distributions remain uniformly bounded on every
bounded spatially indexed family of full Schwartz sources. -/
theorem commonPacketOfOS_boundedFullSources_compact_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η)
    (fN : ℕ → SchwartzNPoint d (k + 1))
    (hfN : Bornology.IsVonNBounded ℝ (Set.range fN)) :
    ∃ C : ℝ, ∀ timeScale level ζ, ζ ∈ K →
      let P := A.commonPacketAt timeScale level
      ‖((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
          OS P.slope P.slope_gt_one (P.ordered a)).pairing (fN level)
            (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)‖ ≤ C := by
  let J := ℕ × (ℕ × K)
  have hcoord :
      ∀ j : J,
        let P := A.commonPacketAt j.1 j.2.1
        osiiNarrowTimeLogCoordinate (d := d) P.slope j.2.2.1 ∈
          osiiAxisPairMultiGapLogDomain d k := by
    intro j
    let P := A.commonPacketAt j.1 j.2.1
    exact osiiNarrowTimeLogCoordinate_mapsTo
      P.slope (lt_trans zero_lt_one P.slope_gt_one)
      η hηsum (hK_subset j.2.2.2)
  let T : J → SchwartzNPoint d (k + 1) →L[ℝ] ℂ :=
    fun j =>
      let P := A.commonPacketAt j.1 j.2.1
      (((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).distribution
          ⟨osiiNarrowTimeLogCoordinate (d := d) P.slope j.2.2.1,
            hcoord j⟩).restrictScalars ℝ
  have hT_pointwise :
      ∀ f : SchwartzNPoint d (k + 1),
        ∃ C : ℝ, ∀ j : J, ‖T j f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ :=
      A.commonPacketOfOS_fullSource_compact_bound
        a OS η hηsum K hK_compact hK_subset f
    refine ⟨C, ?_⟩
    intro j
    have hj := hC j.1 j.2.1 j.2.2.1 j.2.2.2
    dsimp only at hj
    let P := A.commonPacketAt j.1 j.2.1
    rw [((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)).pairing_of_mem
        f _ (hcoord j)] at hj
    simpa [T, P] using hj
  obtain ⟨s, C, hC, hcommon⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound hT_pointwise
  have hsource :=
    (schwartz_withSeminorms ℝ
      (NPointDomain d (k + 1)) ℂ).isVonNBounded_iff_seminorm_bounded.mp hfN
  choose r hr hseminorm using hsource
  let R : ℝ := ∑ i ∈ s, r i
  have hsum_apply :
      ∀ (level : ℕ) (s' : Finset (ℕ × ℕ)),
        (∑ i ∈ s', schwartzSeminormFamily ℝ
          (NPointDomain d (k + 1)) ℂ i) (fN level) =
          ∑ i ∈ s', schwartzSeminormFamily ℝ
            (NPointDomain d (k + 1)) ℂ i (fN level) := by
    intro level s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert i s' hi ih =>
        simp [Finset.sum_insert, hi, ih]
  refine ⟨(C : ℝ) * R, ?_⟩
  intro timeScale level ζ hζK
  let j : J := (timeScale, (level, ⟨ζ, hζK⟩))
  have hsup :
      (s.sup (schwartzSeminormFamily ℝ
        (NPointDomain d (k + 1)) ℂ)) (fN level) ≤ R := by
    calc
      (s.sup (schwartzSeminormFamily ℝ
          (NPointDomain d (k + 1)) ℂ)) (fN level)
          ≤ (∑ i ∈ s, schwartzSeminormFamily ℝ
              (NPointDomain d (k + 1)) ℂ i) (fN level) :=
        Seminorm.le_def.mp
          (Seminorm.finset_sup_le_sum
            (schwartzSeminormFamily ℝ
              (NPointDomain d (k + 1)) ℂ) s) (fN level)
      _ = ∑ i ∈ s,
          schwartzSeminormFamily ℝ
            (NPointDomain d (k + 1)) ℂ i (fN level) := by
        exact hsum_apply level s
      _ ≤ ∑ i ∈ s, r i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hseminorm i (fN level) (Set.mem_range_self level)).le
      _ = R := rfl
  let P := A.commonPacketAt timeScale level
  calc
    ‖((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).pairing (fN level)
          (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)‖
        = ‖T j (fN level)‖ := by
          have hz := hcoord j
          rw [((P.levelCover.carrier a).schwartzDistributionFamilyAtSlopeOfOS
            OS P.slope P.slope_gt_one (P.ordered a)).pairing_of_mem _ _ hz]
          rfl
    _ ≤ (C • s.sup (schwartzSeminormFamily ℝ
          (NPointDomain d (k + 1)) ℂ)) (fN level) :=
      hcommon j (fN level)
    _ = (C : ℝ) *
        (s.sup (schwartzSeminormFamily ℝ
          (NPointDomain d (k + 1)) ℂ)) (fN level) := rfl
    _ ≤ (C : ℝ) * R :=
      mul_le_mul_of_nonneg_left hsup C.coe_nonneg

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
