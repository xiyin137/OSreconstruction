/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapSemigroupPacket
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison














noncomputable section

open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Full spacetime displacement carried by one chronological gap. -/
noncomputable def osiiAxisPairChronologicalGapTranslation
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) :
    SpacetimeDim d :=
  ∑ a : osiiAxisPairIndex d,
    osiiAxisPairPositiveCoefficients (x i) a •
      osiiAxisPairDir (d := d) T a

/-- The fixed spacetime anchor built into an axis-pair physical chart. The
time coordinate carries the half-center normalization from the coefficient
chart, while the spatial coordinates carry the full center. -/
def osiiAxisPairPhysicalChartAnchor
    (ξ : Fin (d + 1) → ℝ) :
    SpacetimeDim d :=
  Fin.cases (ξ 0 / 2) (fun j => ξ (Fin.succ j))

/-- Absolute displacement of point `j`, obtained by summing all earlier
chronological gaps. -/
noncomputable def osiiAxisPairChronologicalPointTranslation
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (j : Fin (k + 1)) :
    SpacetimeDim d :=
  ∑ i : Fin k,
    if i.val < j.val then
      osiiAxisPairChronologicalGapTranslation T x i
    else 0

/-- The first chronological point has no preceding gap, hence no
displacement. -/
@[simp] theorem osiiAxisPairChronologicalPointTranslation_zero
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairChronologicalPointTranslation T x
        (0 : Fin (k + 1)) = 0 := by
  simp [osiiAxisPairChronologicalPointTranslation]

/-- Adjacent absolute chronological displacements differ by exactly the
intervening gap displacement. -/
theorem osiiAxisPairChronologicalPointTranslation_sub_castSucc
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) :
    osiiAxisPairChronologicalPointTranslation T x i.succ -
        osiiAxisPairChronologicalPointTranslation T x i.castSucc =
      osiiAxisPairChronologicalGapTranslation T x i := by
  rw [osiiAxisPairChronologicalPointTranslation,
    osiiAxisPairChronologicalPointTranslation,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    by_cases hji : j.val < i.val
    · simp [hji, Nat.lt_trans hji (Nat.lt_succ_self _)]
    · have hij : i.val < j.val := by omega
      simp [Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hij),
        Nat.not_lt_of_ge (Nat.le_of_lt hij)]
  · simp

/-- Packet-base displacement of point `j` when gap `selected` is delegated
to the one-variable semigroup packet. -/
noncomputable def osiiAxisPairChronologicalPointTranslationWithoutGap
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (j : Fin (k + 1)) :
    SpacetimeDim d :=
  ∑ i ∈ (Finset.univ : Finset (Fin k)).erase selected,
    if i.val < j.val then
      osiiAxisPairChronologicalGapTranslation T x i
    else 0

/-- Before the selected gap, omitting that gap changes no point
displacement. -/
theorem osiiAxisPairChronologicalPointTranslationWithoutGap_eq
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (j : Fin (k + 1))
    (hbefore : ¬ selected.val < j.val) :
    osiiAxisPairChronologicalPointTranslationWithoutGap
        T x selected j =
      osiiAxisPairChronologicalPointTranslation T x j := by
  rw [osiiAxisPairChronologicalPointTranslationWithoutGap,
    osiiAxisPairChronologicalPointTranslation,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ selected)]
  simp [hbefore]

/-- After the selected gap, adding that one gap to the packet base recovers
the full chronological point displacement. -/
theorem osiiAxisPairChronologicalPointTranslationWithoutGap_add
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (j : Fin (k + 1))
    (hafter : selected.val < j.val) :
    osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected j +
        osiiAxisPairChronologicalGapTranslation T x selected =
      osiiAxisPairChronologicalPointTranslation T x j := by
  rw [osiiAxisPairChronologicalPointTranslationWithoutGap,
    osiiAxisPairChronologicalPointTranslation]
  have hsum :
      (∑ i ∈ (Finset.univ : Finset (Fin k)).erase selected,
          if i.val < j.val then
            osiiAxisPairChronologicalGapTranslation T x i
          else 0) +
          (if selected.val < j.val then
            osiiAxisPairChronologicalGapTranslation T x selected
          else 0) =
        ∑ i : Fin k,
          if i.val < j.val then
            osiiAxisPairChronologicalGapTranslation T x i
          else 0 := by
    rw [Finset.sum_erase_add]
    exact Finset.mem_univ selected
  simpa [hafter] using hsum

/-- A gap displacement away from the selected `(gap, direction)` coordinate
depends only on off-selected coefficients. -/
theorem osiiAxisPairChronologicalGapTranslation_congr_of_gap_ne
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    (i : Fin k)
    (hi : i ≠ q.1) :
    osiiAxisPairChronologicalGapTranslation T x i =
      osiiAxisPairChronologicalGapTranslation T y i := by
  unfold osiiAxisPairChronologicalGapTranslation
  apply Finset.sum_congr rfl
  intro a _ha
  change
    Real.exp (x i a) • osiiAxisPairDir (d := d) T a =
      Real.exp (y i a) • osiiAxisPairDir (d := d) T a
  rw [hxy (i, a) (by
      intro h
      exact hi (congrArg Prod.fst h))]

/-- The cumulative packet base is independent of the selected active
coefficient. -/
theorem
    osiiAxisPairChronologicalPointTranslationWithoutGap_congr_of_eq_off_selected
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    (j : Fin (k + 1)) :
    osiiAxisPairChronologicalPointTranslationWithoutGap T x q.1 j =
      osiiAxisPairChronologicalPointTranslationWithoutGap T y q.1 j := by
  unfold osiiAxisPairChronologicalPointTranslationWithoutGap
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i ≠ q.1 := Finset.ne_of_mem_erase hi
  rw [osiiAxisPairChronologicalGapTranslation_congr_of_gap_ne
    T q hxy i hiq]

/-- The original index of a left-block source is not after its selected
chronological gap. -/
theorem osiiChronologicalGapSplitEquiv_left_not_after
    (selected : Fin k)
    (j : Fin (osiiChronologicalGapLeftArity selected)) :
    ¬ selected.val <
      (osiiChronologicalGapSplitEquiv selected (Sum.inl j)).val := by
  change ¬ selected.val < j.val
  have hj : j.val < selected.val + 1 := by
    simpa [osiiChronologicalGapLeftArity] using j.isLt
  omega

/-- Every original index in the right block lies strictly after the selected
chronological gap. -/
theorem osiiChronologicalGapSplitEquiv_right_after
    (selected : Fin k)
    (j : Fin (osiiChronologicalGapRightArity selected)) :
    selected.val <
      (osiiChronologicalGapSplitEquiv selected (Sum.inr j)).val := by
  change selected.val <
    osiiChronologicalGapLeftArity selected + j.val
  simp [osiiChronologicalGapLeftArity]
  omega

/-- Translate each one-point factor by its full chronological prefix
displacement. -/
noncomputable def osiiAxisPairChronologicalTranslatedFactors
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    Fin (k + 1) → SchwartzSpacetime d :=
  fun j =>
    SCV.translateSchwartz
      (-osiiAxisPairChronologicalPointTranslation T x j) (fs j)

/-- Translate each one-point factor by the packet base with the selected gap
removed. -/
noncomputable def osiiAxisPairChronologicalPacketBaseFactors
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    Fin (k + 1) → SchwartzSpacetime d :=
  fun j =>
    SCV.translateSchwartz
      (-osiiAxisPairChronologicalPointTranslationWithoutGap
        T x selected j) (fs j)

/-- The complete packet-base factor tuple depends only on coefficients away
from the selected `(gap, direction)`. -/
theorem
    osiiAxisPairChronologicalPacketBaseFactors_congr_of_eq_off_selected
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalPacketBaseFactors T x q.1 fs =
      osiiAxisPairChronologicalPacketBaseFactors T y q.1 fs := by
  funext j
  rw [osiiAxisPairChronologicalPacketBaseFactors,
    osiiAxisPairChronologicalPacketBaseFactors,
    osiiAxisPairChronologicalPointTranslationWithoutGap_congr_of_eq_off_selected
      T q hxy j]

/-- Uncut left block of the chronological split. The factors are conjugated
because `commonRealSource` applies pointwise conjugation to the assembled
left source. -/
noncomputable def osiiAxisPairChronologicalUncutLeftSource
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity selected) :=
  SchwartzMap.productTensor
    (fun j =>
      (osiiAxisPairChronologicalPacketBaseFactors T x selected fs
        (osiiChronologicalGapSplitEquiv selected (Sum.inl j))).conj)

/-- Uncut right block of the chronological split. -/
noncomputable def osiiAxisPairChronologicalUncutRightSource
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    SchwartzNPoint d (osiiChronologicalGapRightArity selected) :=
  SchwartzMap.productTensor
    (fun j =>
      osiiAxisPairChronologicalPacketBaseFactors T x selected fs
        (osiiChronologicalGapSplitEquiv selected (Sum.inr j)))

/-- The uncut common-real source at one chronological split. The full
selected-gap translation is restored on the right block. -/
noncomputable def osiiAxisPairChronologicalUncutSplitSource
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    SchwartzNPoint d
      (osiiChronologicalGapLeftArity selected +
        osiiChronologicalGapRightArity selected) :=
  OSIIAxisPairRotatedSourcePacket.commonRealSource
    T (osiiAxisPairPositiveCoefficients (x selected))
    (osiiAxisPairChronologicalUncutLeftSource T x selected fs)
    (osiiAxisPairChronologicalUncutRightSource T x selected fs)

/-- Apply one auxiliary common translation to the uncut left block. This is
the centering operation used to place the left source in a selected negative
rotated cone. -/
noncomputable def osiiAxisPairChronologicalCenteredLeftSource
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (center : SpacetimeDim d)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity selected) :=
  translateSchwartzNPoint (d := d) center
    (osiiAxisPairChronologicalUncutLeftSource T x selected fs)

/-- Apply the same auxiliary common translation to the uncut right block. -/
noncomputable def osiiAxisPairChronologicalCenteredRightSource
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (center : SpacetimeDim d)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    SchwartzNPoint d (osiiChronologicalGapRightArity selected) :=
  translateSchwartzNPoint (d := d) center
    (osiiAxisPairChronologicalUncutRightSource T x selected fs)

/-- The uncut left chronological block depends only on the packet base, hence
only on coordinates away from the selected active coefficient. -/
theorem
    osiiAxisPairChronologicalUncutLeftSource_congr_of_eq_off_selected
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalUncutLeftSource T x q.1 fs =
      osiiAxisPairChronologicalUncutLeftSource T y q.1 fs := by
  rw [osiiAxisPairChronologicalUncutLeftSource,
    osiiAxisPairChronologicalUncutLeftSource,
    osiiAxisPairChronologicalPacketBaseFactors_congr_of_eq_off_selected
      T q hxy fs]

/-- The uncut right chronological block depends only on the packet base. -/
theorem
    osiiAxisPairChronologicalUncutRightSource_congr_of_eq_off_selected
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalUncutRightSource T x q.1 fs =
      osiiAxisPairChronologicalUncutRightSource T y q.1 fs := by
  rw [osiiAxisPairChronologicalUncutRightSource,
    osiiAxisPairChronologicalUncutRightSource,
    osiiAxisPairChronologicalPacketBaseFactors_congr_of_eq_off_selected
      T q hxy fs]

/-- Centered right blocks are frozen-base coherent when the center is. -/
theorem
    osiiAxisPairChronologicalCenteredRightSource_congr_of_eq_off_selected
    (T : ℝ)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2)
    {centerX centerY : SpacetimeDim d}
    (hcenter : centerX = centerY)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalCenteredRightSource
        T x q.1 centerX fs =
      osiiAxisPairChronologicalCenteredRightSource
        T y q.1 centerY fs := by
  rw [osiiAxisPairChronologicalCenteredRightSource,
    osiiAxisPairChronologicalCenteredRightSource, hcenter,
    osiiAxisPairChronologicalUncutRightSource_congr_of_eq_off_selected
      T q hxy fs]

/-- On the left block, packet-base factors are already the full
chronologically translated factors. -/
theorem osiiAxisPairChronologicalPacketBaseFactors_left_eq
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (j : Fin (osiiChronologicalGapLeftArity selected)) :
    osiiAxisPairChronologicalPacketBaseFactors T x selected fs
        (osiiChronologicalGapSplitEquiv selected (Sum.inl j)) =
      osiiAxisPairChronologicalTranslatedFactors T x fs
        (osiiChronologicalGapSplitEquiv selected (Sum.inl j)) := by
  rw [osiiAxisPairChronologicalPacketBaseFactors,
    osiiAxisPairChronologicalTranslatedFactors,
    osiiAxisPairChronologicalPointTranslationWithoutGap_eq
      T x selected
      (osiiChronologicalGapSplitEquiv selected (Sum.inl j))
      (osiiChronologicalGapSplitEquiv_left_not_after selected j)]

/-- Common translation of a product tensor is factorwise translation by the
negative displacement. -/
theorem translateSchwartzNPoint_productTensor
    {n : ℕ}
    (v : SpacetimeDim d)
    (fs : Fin n → SchwartzSpacetime d) :
    translateSchwartzNPoint (d := d) v
        (SchwartzMap.productTensor fs) =
      SchwartzMap.productTensor
        (fun j => SCV.translateSchwartz (-v) (fs j)) := by
  ext y
  simp [translateSchwartzNPoint_apply,
    SchwartzMap.productTensor_apply, SCV.translateSchwartz_apply,
    sub_eq_add_neg]

/-- Translating the selected right-tail packet base by the full selected gap
recovers the globally translated right-tail product tensor. -/
theorem osiiAxisPairChronological_right_product_reconstruct
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    translateSchwartzNPoint (d := d)
        (osiiAxisPairChronologicalGapTranslation T x selected)
        (SchwartzMap.productTensor
          (fun j =>
            osiiAxisPairChronologicalPacketBaseFactors T x selected fs
              (osiiChronologicalGapSplitEquiv selected (Sum.inr j)))) =
      SchwartzMap.productTensor
        (fun j =>
          osiiAxisPairChronologicalTranslatedFactors T x fs
            (osiiChronologicalGapSplitEquiv selected (Sum.inr j))) := by
  rw [translateSchwartzNPoint_productTensor]
  ext y
  simp only [SchwartzMap.productTensor_apply]
  apply Finset.prod_congr rfl
  intro j _hj
  simp only [osiiAxisPairChronologicalPacketBaseFactors,
    osiiAxisPairChronologicalTranslatedFactors,
    SCV.translateSchwartz_apply]
  congr 1
  have hshift :=
    osiiAxisPairChronologicalPointTranslationWithoutGap_add
      T x selected
        (osiiChronologicalGapSplitEquiv selected (Sum.inr j))
      (osiiChronologicalGapSplitEquiv_right_after selected j)
  rw [← hshift]
  module

/-- Before positivity localization, every chronological split reconstructs
the same full factorwise-translated product tensor. The only difference is
the canonical finite-index identification between the two block arities and
the original `(k + 1)` point tuple. -/
theorem osiiAxisPairChronologicalUncutSplitSource_eq_productTensor
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalUncutSplitSource T x selected fs =
      SchwartzMap.productTensor
        (fun j =>
          osiiAxisPairChronologicalTranslatedFactors T x fs
            ((finCongr (osiiChronologicalGap_arity_add selected)) j)) := by
  rw [osiiAxisPairChronologicalUncutSplitSource,
    OSIIAxisPairRotatedSourcePacket.commonRealSource]
  rw [show
      (∑ b : osiiAxisPairIndex d,
          osiiAxisPairPositiveCoefficients (x selected) b •
            osiiAxisPairDir (d := d) T b) =
        osiiAxisPairChronologicalGapTranslation T x selected by
      rfl]
  rw [osiiAxisPairChronologicalUncutRightSource]
  rw [osiiAxisPairChronological_right_product_reconstruct]
  ext y
  rw [SchwartzMap.tensorProduct_apply]
  simp only [osiiAxisPairChronologicalUncutLeftSource,
    SchwartzMap.conj_apply, SchwartzMap.productTensor_apply, map_prod]
  rw [Fin.prod_univ_add]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _hj
    rw [osiiAxisPairChronologicalPacketBaseFactors_left_eq]
    have hidx :
        osiiChronologicalGapSplitEquiv selected (Sum.inl j) =
          (finCongr (osiiChronologicalGap_arity_add selected))
            (Fin.castAdd (osiiChronologicalGapRightArity selected) j) := by
      rfl
    rw [hidx]
    simp [splitFirst]
  · apply Finset.prod_congr rfl
    intro j _hj
    have hidx :
        osiiChronologicalGapSplitEquiv selected (Sum.inr j) =
          (finCongr (osiiChronologicalGap_arity_add selected))
            (Fin.natAdd (osiiChronologicalGapLeftArity selected) j) := by
      rfl
    rw [hidx]
    rfl

/-- Reindexing the uncut split source to the original point tuple removes the
selected split entirely. -/
theorem reindex_osiiAxisPairChronologicalUncutSplitSource_eq_productTensor
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    reindexSchwartz (d := d)
        (finCongr (osiiChronologicalGap_arity_add selected))
        (osiiAxisPairChronologicalUncutSplitSource T x selected fs) =
      SchwartzMap.productTensor
        (osiiAxisPairChronologicalTranslatedFactors T x fs) := by
  rw [osiiAxisPairChronologicalUncutSplitSource_eq_productTensor]
  ext y
  rw [reindexSchwartz_apply, SchwartzMap.productTensor_apply,
    SchwartzMap.productTensor_apply]
  exact Fintype.prod_equiv
    (finCongr (osiiChronologicalGap_arity_add selected))
    (fun j =>
      osiiAxisPairChronologicalTranslatedFactors T x fs
        ((finCongr (osiiChronologicalGap_arity_add selected)) j)
        (y ((finCongr (osiiChronologicalGap_arity_add selected)) j)))
    (fun i => osiiAxisPairChronologicalTranslatedFactors T x fs i (y i))
    (fun _ => rfl)

/-- Transporting only the finite arity index does not change a Schwinger
pairing. This is the heterogeneous-cardinality form of the definitional
identity reindexing. -/
theorem osiiSchwinger_ofClassical_eq_of_reindex_finCongr
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (h : n = m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hfg : reindexSchwartz (d := d) (finCongr h) f = g) :
    OS.S n (ZeroDiagonalSchwartz.ofClassical f) =
      OS.S m (ZeroDiagonalSchwartz.ofClassical g) := by
  subst m
  have hfg' : f = g := by
    ext x
    simpa only [reindexSchwartz_apply, finCongr_apply, Fin.cast_eq_self] using
      congrArg (fun F : SchwartzNPoint d n => F x) hfg
  exact congrArg (fun u => OS.S n (ZeroDiagonalSchwartz.ofClassical u)) hfg'

/-- Every uncut chronological split has the same Schwinger value: the value
of the full factorwise-translated product tensor. -/
theorem osiiAxisPairChronologicalUncutSplitSource_schwinger_eq_productTensor
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    OS.S
        (osiiChronologicalGapLeftArity selected +
          osiiChronologicalGapRightArity selected)
        (ZeroDiagonalSchwartz.ofClassical
          (osiiAxisPairChronologicalUncutSplitSource T x selected fs)) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x fs))) := by
  exact osiiSchwinger_ofClassical_eq_of_reindex_finCongr OS
    (osiiChronologicalGap_arity_add selected)
    (osiiAxisPairChronologicalUncutSplitSource T x selected fs)
    (SchwartzMap.productTensor
      (osiiAxisPairChronologicalTranslatedFactors T x fs))
    (reindex_osiiAxisPairChronologicalUncutSplitSource_eq_productTensor
      T x selected fs)

/-- E1 removes an auxiliary common center from any honest zero-diagonal
Schwartz source. -/
theorem osiiSchwinger_translateSchwartzNPoint_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ}
    (center : SpacetimeDim d)
    (f : SchwartzNPoint d n)
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    OS.S n (ZeroDiagonalSchwartz.ofClassical
        (translateSchwartzNPoint (d := d) center f)) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical f) := by
  have htranslated :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzNPoint (d := d) center f) :=
    (VanishesToInfiniteOrderOnCoincidence.translateSchwartzNPoint_iff
      center f).2 hf
  symm
  refine OS.E1_translation_invariant n (-center)
    (ZeroDiagonalSchwartz.ofClassical f)
    (ZeroDiagonalSchwartz.ofClassical
      (translateSchwartzNPoint (d := d) center f)) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes f hf,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (translateSchwartzNPoint (d := d) center f) htranslated]
  simp [translateSchwartzNPoint_apply, sub_eq_add_neg]

namespace OSIIAxisPairMultiGapSemigroupPacketFamily

end OSIIAxisPairMultiGapSemigroupPacketFamily

end OSReconstruction
