/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductSourceNormalization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation


















noncomputable section

open Set
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

private theorem exists_pos_le_on_compact
    {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K)
    {g : E → ℝ} (hg : Continuous g)
    (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ g x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hx₀_min⟩ :=
      hK.exists_isMinOn hne hg.continuousOn
    have hx₀_pos : 0 < g x₀ := hpos x₀ hx₀
    refine ⟨g x₀ / 2, by linarith, ?_⟩
    intro x hx
    have hle : g x₀ ≤ g x := isMinOn_iff.mp hx₀_min x hx
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

private theorem exists_bounded_center_shift_of_compact_cross_order
    {E : Type*} [TopologicalSpace E]
    {L R : Set E} (hL : IsCompact L) (hR : IsCompact R)
    {t : E → ℝ} (ht : Continuous t)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, t x < t y) :
    ∃ c B : ℝ,
      0 ≤ B ∧
      |c| ≤ 2 * B + 1 ∧
      (∀ B' : ℝ, 0 ≤ B' →
        (∀ x ∈ L, |t x| ≤ B') →
        (∀ y ∈ R, |t y| ≤ B') →
        |c| ≤ 2 * B' + 1) ∧
      (∀ x ∈ L, |t x| ≤ B) ∧
      (∀ y ∈ R, |t y| ≤ B) ∧
      (∀ x ∈ L, t x + c < 0) ∧
      ∀ y ∈ R, 0 < t y + c := by
  let K := L ∪ R
  have hK : IsCompact K := hL.union hR
  obtain ⟨M, hM⟩ :=
    (hK.image ht).isBounded.exists_norm_le
  let B : ℝ := max M 0
  have hB : 0 ≤ B := le_max_right M 0
  have ht_bound :
      ∀ x ∈ K, |t x| ≤ B := by
    intro x hx
    have hxM : ‖t x‖ ≤ M :=
      hM (t x) ⟨x, hx, rfl⟩
    simpa [B, Real.norm_eq_abs] using
      hxM.trans (le_max_left M 0)
  have hleft_bound :
      ∀ x ∈ L, |t x| ≤ B :=
    fun x hx => ht_bound x (Or.inl hx)
  have hright_bound :
      ∀ y ∈ R, |t y| ≤ B :=
    fun y hy => ht_bound y (Or.inr hy)
  by_cases hLne : L.Nonempty
  · obtain ⟨xmax, hxmax, hxmax_bound⟩ :=
      hL.exists_isMaxOn hLne ht.continuousOn
    by_cases hRne : R.Nonempty
    · obtain ⟨ymin, hymin, hymin_bound⟩ :=
        hR.exists_isMinOn hRne ht.continuousOn
      let c := -(t xmax + t ymin) / 2
      have hxy : t xmax < t ymin := hcross xmax hxmax ymin hymin
      have hcB : |c| ≤ 2 * B + 1 := by
        have hadd :
            |t xmax + t ymin| ≤ |t xmax| + |t ymin| :=
          abs_add_le _ _
        have hsum : |t xmax| + |t ymin| ≤ B + B :=
          add_le_add (hleft_bound xmax hxmax)
            (hright_bound ymin hymin)
        calc
          |c| = |t xmax + t ymin| / 2 := by
            dsimp [c]
            rw [abs_div, abs_neg]
            norm_num
          _ ≤ (|t xmax| + |t ymin|) / 2 := by
            gcongr
          _ ≤ (B + B) / 2 := by
            gcongr
          _ ≤ 2 * B + 1 := by linarith
      have hcB' :
          ∀ B' : ℝ, 0 ≤ B' →
            (∀ x ∈ L, |t x| ≤ B') →
            (∀ y ∈ R, |t y| ≤ B') →
            |c| ≤ 2 * B' + 1 := by
        intro B' hB' hleft_bound' hright_bound'
        have hadd :
            |t xmax + t ymin| ≤ |t xmax| + |t ymin| :=
          abs_add_le _ _
        calc
          |c| = |t xmax + t ymin| / 2 := by
            dsimp [c]
            rw [abs_div, abs_neg]
            norm_num
          _ ≤ (|t xmax| + |t ymin|) / 2 := by
            gcongr
          _ ≤ (B' + B') / 2 := by
            gcongr
            · exact hleft_bound' xmax hxmax
            · exact hright_bound' ymin hymin
          _ ≤ 2 * B' + 1 := by linarith
      refine
        ⟨c, B, hB, hcB, hcB', hleft_bound, hright_bound, ?_, ?_⟩
      · intro x hx
        have hxle : t x ≤ t xmax :=
          isMaxOn_iff.mp hxmax_bound x hx
        dsimp [c]
        linarith
      · intro y hy
        have hyle : t ymin ≤ t y :=
          isMinOn_iff.mp hymin_bound y hy
        dsimp [c]
        linarith
    · let c := -t xmax - 1
      have hcB : |c| ≤ 2 * B + 1 := by
        calc
          |c| ≤ |-t xmax| + |(-1 : ℝ)| := by
            simpa [c] using abs_sub (-t xmax) (1 : ℝ)
          _ = |t xmax| + 1 := by simp
          _ ≤ B + 1 := by
            gcongr
            exact hleft_bound xmax hxmax
          _ ≤ 2 * B + 1 := by linarith
      have hcB' :
          ∀ B' : ℝ, 0 ≤ B' →
            (∀ x ∈ L, |t x| ≤ B') →
            (∀ y ∈ R, |t y| ≤ B') →
            |c| ≤ 2 * B' + 1 := by
        intro B' hB' hleft_bound' _hright_bound'
        calc
          |c| ≤ |-t xmax| + |(-1 : ℝ)| := by
            simpa [c] using abs_sub (-t xmax) (1 : ℝ)
          _ = |t xmax| + 1 := by simp
          _ ≤ B' + 1 := by
            gcongr
            exact hleft_bound' xmax hxmax
          _ ≤ 2 * B' + 1 := by linarith
      refine
        ⟨c, B, hB, hcB, hcB', hleft_bound, hright_bound, ?_, ?_⟩
      · intro x hx
        have hxle : t x ≤ t xmax :=
          isMaxOn_iff.mp hxmax_bound x hx
        dsimp [c]
        linarith
      · intro y hy
        exact False.elim (hRne ⟨y, hy⟩)
  · by_cases hRne : R.Nonempty
    · obtain ⟨ymin, hymin, hymin_bound⟩ :=
        hR.exists_isMinOn hRne ht.continuousOn
      let c := -t ymin + 1
      have hcB : |c| ≤ 2 * B + 1 := by
        calc
          |c| ≤ |-t ymin| + |(1 : ℝ)| := by
            simpa [c] using abs_add_le (-t ymin) (1 : ℝ)
          _ = |t ymin| + 1 := by simp
          _ ≤ B + 1 := by
            gcongr
            exact hright_bound ymin hymin
          _ ≤ 2 * B + 1 := by linarith
      have hcB' :
          ∀ B' : ℝ, 0 ≤ B' →
            (∀ x ∈ L, |t x| ≤ B') →
            (∀ y ∈ R, |t y| ≤ B') →
            |c| ≤ 2 * B' + 1 := by
        intro B' hB' _hleft_bound' hright_bound'
        calc
          |c| ≤ |-t ymin| + |(1 : ℝ)| := by
            simpa [c] using abs_add_le (-t ymin) (1 : ℝ)
          _ = |t ymin| + 1 := by simp
          _ ≤ B' + 1 := by
            gcongr
            exact hright_bound' ymin hymin
          _ ≤ 2 * B' + 1 := by linarith
      refine
        ⟨c, B, hB, hcB, hcB', hleft_bound, hright_bound, ?_, ?_⟩
      · intro x hx
        exact False.elim (hLne ⟨x, hx⟩)
      · intro y hy
        have hyle : t ymin ≤ t y :=
          isMinOn_iff.mp hymin_bound y hy
        dsimp [c]
        linarith
    · refine
        ⟨0, B, hB, ?_, ?_, hleft_bound, hright_bound, ?_, ?_⟩
      · simp
        linarith
      · intro B' hB' _hleft_bound' _hright_bound'
        simp
        linarith
      · intro x hx
        exact False.elim (hLne ⟨x, hx⟩)
      · intro y hy
        exact False.elim (hRne ⟨y, hy⟩)

/-- Compact one-point factors with strict pairwise chronological support
order. The tuple has `k + 1` points and therefore `k` chronological gaps. -/
structure OSIIChronologicalCompactFactors (d k : ℕ) where
  factors : Fin (k + 1) → SchwartzSpacetime d
  factor_compact :
    ∀ i, HasCompactSupport
      ((factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  ordered_support :
    ∀ i j : Fin (k + 1), i < j →
      ∀ y ∈ tsupport
          ((factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            ((factors j : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
          y 0 < z 0

namespace OSIIChronologicalCompactFactors

/-- Positive normalization of an ordered compact product source supplies the
factorwise compact chronological data used by the multi-gap packet. -/
def ofPositiveNormalization
    (P : OSIIOrderedCompactProductSource d (k + 1))
    (N : P.PositiveNormalization) :
    OSIIChronologicalCompactFactors d k where
  factors := P.normalizedFactors N.shift
  factor_compact := N.factor_compact
  ordered_support := P.normalizedFactors_ordered N.shift

/-- Compact pairwise chronological supports have one uniform ordinary-time
gap. Empty factor supports cause no problem: the corresponding inequality is
vacuous. -/
theorem exists_uniform_time_gap
    (F : OSIIChronologicalCompactFactors d k) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors j : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
            δ ≤ z 0 - y 0 := by
  let I := {p : Fin (k + 1) × Fin (k + 1) // p.1 < p.2}
  have hI_nonempty : (Finset.univ : Finset I).Nonempty := by
    have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    let i0 : Fin (k + 1) := ⟨0, by omega⟩
    let i1 : Fin (k + 1) := ⟨1, by omega⟩
    have hi : i0 < i1 := by
      change (0 : ℕ) < 1
      omega
    exact ⟨⟨(i0, i1), hi⟩, Finset.mem_univ _⟩
  have hgap :
      ∀ p : I, ∃ ε : ℝ, 0 < ε ∧
        ∀ y ∈ tsupport
            ((F.factors p.1.1 : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors p.1.2 : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ε ≤ z 0 - y 0 := by
    intro p
    let K : Set (SpacetimeDim d × SpacetimeDim d) :=
      tsupport
          ((F.factors p.1.1 : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ×ˢ
        tsupport
          ((F.factors p.1.2 : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)
    have hK : IsCompact K :=
      (F.factor_compact p.1.1).isCompact.prod
        (F.factor_compact p.1.2).isCompact
    obtain ⟨ε, hε, hε_le⟩ :=
      exists_pos_le_on_compact hK
        (show Continuous
          (fun yz : SpacetimeDim d × SpacetimeDim d =>
            yz.2 0 - yz.1 0) by fun_prop)
        (by
          intro yz hyz
          exact sub_pos.mpr
            (F.ordered_support p.1.1 p.1.2 p.2
              yz.1 hyz.1 yz.2 hyz.2))
    refine ⟨ε, hε, ?_⟩
    intro y hy z hz
    exact hε_le (y, z) ⟨hy, hz⟩
  let ε : I → ℝ := fun p => Classical.choose (hgap p)
  have hε_pos : ∀ p : I, 0 < ε p :=
    fun p => (Classical.choose_spec (hgap p)).1
  have hε_le :
      ∀ p : I,
        ∀ y ∈ tsupport
            ((F.factors p.1.1 : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors p.1.2 : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ε p ≤ z 0 - y 0 :=
    fun p => (Classical.choose_spec (hgap p)).2
  let δ : ℝ := (Finset.univ : Finset I).inf' hI_nonempty ε
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact (Finset.lt_inf'_iff hI_nonempty).2
      (fun p _hp => hε_pos p)
  refine ⟨δ, hδ_pos, ?_⟩
  intro i j hij y hy z hz
  let p : I := ⟨(i, j), hij⟩
  have hδ_le_ε : δ ≤ ε p := by
    dsimp [δ]
    exact Finset.inf'_le
      (s := (Finset.univ : Finset I)) (f := ε)
      (b := p) (Finset.mem_univ _)
  exact hδ_le_ε.trans (hε_le p y hy z hz)

/-- All factor supports admit one common nonnegative norm bound. -/
theorem exists_uniform_norm_bound
    (F : OSIIChronologicalCompactFactors d k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Fin (k + 1),
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
          ‖y‖ ≤ C := by
  have hb :
      ∀ i : Fin (k + 1), ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ),
          ‖y‖ ≤ C := by
    intro i
    rcases
        (F.factor_compact i).isCompact.isBounded.subset_closedBall
          (0 : SpacetimeDim d) with ⟨R, hR⟩
    refine ⟨max R 0, le_max_right _ _, ?_⟩
    intro y hy
    have hyR := hR hy
    rw [Metric.mem_closedBall, dist_zero_right] at hyR
    exact hyR.trans (le_max_left _ _)
  let c : Fin (k + 1) → ℝ := fun i => Classical.choose (hb i)
  have hc_nonneg : ∀ i, 0 ≤ c i :=
    fun i => (Classical.choose_spec (hb i)).1
  have hc_bound :
      ∀ i y, y ∈ tsupport
          ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
        ‖y‖ ≤ c i :=
    fun i => (Classical.choose_spec (hb i)).2
  let C : ℝ := ∑ i : Fin (k + 1), c i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hc_nonneg i
  refine ⟨C, hC, ?_⟩
  intro i y hy
  exact (hc_bound i y hy).trans
    (Finset.single_le_sum
      (fun j _ => hc_nonneg j) (Finset.mem_univ i))

/-- One sufficiently steep slope sees the original pairwise chronological
order in every signed axis-pair frame. -/
theorem exists_axisPairSlope_pairwise_ordered
    (F : OSIIChronologicalCompactFactors d k) :
    ∃ T : ℝ, 1 < T ∧
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0 := by
  obtain ⟨δ, hδ, hgap⟩ := F.exists_uniform_time_gap
  obtain ⟨C, hC, hnorm⟩ := F.exists_uniform_norm_bound
  let T : ℝ := max 2 (2 * C / δ + 1)
  have hT_one : 1 < T := by
    have htwo : (2 : ℝ) ≤ T := le_max_left _ _
    linarith
  have hT_ratio : 2 * C / δ < T := by
    have hle : 2 * C / δ + 1 ≤ T := le_max_right _ _
    linarith
  have hTδ : 2 * C < T * δ := (div_lt_iff₀ hδ).mp hT_ratio
  refine ⟨T, hT_one, ?_⟩
  intro a i j hij y hy z hz
  have hycoord :
      |y (Fin.succ a.1)| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm y (Fin.succ a.1)).trans
      (hnorm i y hy)
  have hzcoord :
      |z (Fin.succ a.1)| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm z (Fin.succ a.1)).trans
      (hnorm j z hz)
  have htime := hgap i j hij y hy z hz
  rw [(osiiAxisPairRotationData T a).mulVec_time,
    (osiiAxisPairRotationData T a).mulVec_time]
  rw [mul_lt_mul_iff_right₀
    (inv_pos.mpr (osiiAxisPairRadius_pos T))]
  have hysp := abs_le.mp hycoord
  have hzsp := abs_le.mp hzcoord
  cases a.2 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    nlinarith

end OSIIChronologicalCompactFactors

omit [NeZero d] in
/-- Every positive chronological gap has nonnegative time in every selected
axis-pair frame. -/
theorem OSIIAxisPairRotationData.mulVec_chronologicalGapTranslation_time_nonneg
    (D : OSIIAxisPairRotationData (d := d) T a)
    (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) :
    0 ≤
      (D.matrix.mulVec
        (osiiAxisPairChronologicalGapTranslation T x i)) 0 := by
  simp only [osiiAxisPairChronologicalGapTranslation, Matrix.mulVec_sum,
    Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_nonneg
  intro b _hb
  exact mul_nonneg
    (le_of_lt (osiiAxisPairPositiveCoefficients_pos (x i) b))
    (le_of_lt (D.mulVec_dir_time_pos hT b))

omit [NeZero d] in
/-- Omitting one selected gap leaves cumulative packet-base translations
monotone in every selected rotated time coordinate. -/
theorem
    OSIIAxisPairRotationData.mulVec_chronologicalPointTranslationWithoutGap_time_mono
    (D : OSIIAxisPairRotationData (d := d) T a)
    (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    {i j : Fin (k + 1)}
    (hij : i < j) :
    (D.matrix.mulVec
        (osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected i)) 0 ≤
      (D.matrix.mulVec
        (osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected j)) 0 := by
  simp only [osiiAxisPairChronologicalPointTranslationWithoutGap,
    Matrix.mulVec_sum, Finset.sum_apply]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hri : r.val < i.val
  · have hrj : r.val < j.val := lt_trans hri hij
    simp [hri, hrj]
  · by_cases hrj : r.val < j.val
    · simp [hri, hrj]
      exact D.mulVec_chronologicalGapTranslation_time_nonneg hT x r
    · simp [hri, hrj]

omit [NeZero d] in
theorem
    OSIIAxisPairRotationData.mulVec_chronologicalPointTranslationWithoutGap_time_mono_le
    (D : OSIIAxisPairRotationData (d := d) T a)
    (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    {i j : Fin (k + 1)}
    (hij : i ≤ j) :
    (D.matrix.mulVec
        (osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected i)) 0 ≤
      (D.matrix.mulVec
        (osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected j)) 0 := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · rfl
  · exact
      D.mulVec_chronologicalPointTranslationWithoutGap_time_mono
        hT x selected hij

/-- A support point of a packet-base factor pulls back to the support of the
corresponding original factor after subtracting its cumulative displacement. -/
theorem osiiAxisPairChronologicalPacketBaseFactors_tsupport_sub
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈ tsupport
        ((osiiAxisPairChronologicalPacketBaseFactors
          T x selected fs i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) :
    y - osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected i ∈
      tsupport ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  have hpre :=
    tsupport_comp_subset_preimage
      ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
      (show Continuous
        (fun w : SpacetimeDim d =>
          w - osiiAxisPairChronologicalPointTranslationWithoutGap
            T x selected i) by fun_prop)
      hy
  simpa [osiiAxisPairChronologicalPacketBaseFactors,
    SCV.translateSchwartz_apply] using hpre

/-- The packet base preserves strict factor-support order in every signed
axis-pair frame once the common slope sees the original chronological order. -/
theorem packetBaseFactors_pairwise_ordered
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (a : osiiAxisPairIndex d)
    (i j : Fin (k + 1))
    (hij : i < j)
    {y z : SpacetimeDim d}
    (hy :
      y ∈ tsupport
        ((osiiAxisPairChronologicalPacketBaseFactors
          T x selected F.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ))
    (hz :
      z ∈ tsupport
        ((osiiAxisPairChronologicalPacketBaseFactors
          T x selected F.factors j : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) :
    ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
      ((osiiAxisPairRotationData T a).matrix.mulVec z) 0 := by
  let D := osiiAxisPairRotationData T a
  let vi :=
    osiiAxisPairChronologicalPointTranslationWithoutGap T x selected i
  let vj :=
    osiiAxisPairChronologicalPointTranslationWithoutGap T x selected j
  have hy' :
      y - vi ∈
        tsupport
          ((F.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    exact osiiAxisPairChronologicalPacketBaseFactors_tsupport_sub
      T x selected F.factors i hy
  have hz' :
      z - vj ∈
        tsupport
          ((F.factors j : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    exact osiiAxisPairChronologicalPacketBaseFactors_tsupport_sub
      T x selected F.factors j hz
  have hbase := hordered a i j hij (y - vi) hy' (z - vj) hz'
  have hmono :
      (D.matrix.mulVec vi) 0 ≤ (D.matrix.mulVec vj) 0 :=
    D.mulVec_chronologicalPointTranslationWithoutGap_time_mono
      hT x selected hij
  dsimp [D] at hbase hmono ⊢
  simp only [Matrix.mulVec_sub, Pi.sub_apply] at hbase
  linarith

/-- Union of all original one-point factor supports. -/
def OSIIChronologicalCompactFactors.factorSupportCarrier
    (F : OSIIChronologicalCompactFactors d k) :
    Set (SpacetimeDim d) :=
  ⋃ i : Fin (k + 1),
    tsupport
      ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)

theorem OSIIChronologicalCompactFactors.factorSupportCarrier_compact
    (F : OSIIChronologicalCompactFactors d k) :
    IsCompact F.factorSupportCarrier := by
  apply isCompact_iUnion
  intro i
  exact (F.factor_compact i).isCompact

/-- Canonical bound on all rotated factor-support times in one signed
axis-pair frame. The supremum is zero when every factor support is empty. -/
noncomputable def OSIIChronologicalCompactFactors.axisPairRotatedTimeBound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (a : osiiAxisPairIndex d) :
    ℝ :=
  sSup
    ((fun y : SpacetimeDim d =>
      |((osiiAxisPairRotationData T a).matrix.mulVec y) 0|) ''
        F.factorSupportCarrier)

theorem OSIIChronologicalCompactFactors.axisPairRotatedTimeBound_nonneg
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (a : osiiAxisPairIndex d) :
    0 ≤ F.axisPairRotatedTimeBound T a := by
  let g : SpacetimeDim d → ℝ := fun y =>
    |((osiiAxisPairRotationData T a).matrix.mulVec y) 0|
  have hcompact :
      IsCompact (g '' F.factorSupportCarrier) :=
    F.factorSupportCarrier_compact.image
      (show Continuous g by fun_prop)
  by_cases hK : F.factorSupportCarrier.Nonempty
  · obtain ⟨y, hy⟩ := hK
    have hmem : g y ∈ g '' F.factorSupportCarrier :=
      ⟨y, hy, rfl⟩
    exact (abs_nonneg _).trans (le_csSup hcompact.bddAbove hmem)
  · have hempty : F.factorSupportCarrier = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hK
    simp [axisPairRotatedTimeBound, g, hempty, Real.sSup_empty]

theorem OSIIChronologicalCompactFactors.abs_rotated_factor_time_le_bound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (a : osiiAxisPairIndex d)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈ tsupport
        ((F.factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    |((osiiAxisPairRotationData T a).matrix.mulVec y) 0| ≤
      F.axisPairRotatedTimeBound T a := by
  let g : SpacetimeDim d → ℝ := fun z =>
    |((osiiAxisPairRotationData T a).matrix.mulVec z) 0|
  have hcompact :
      IsCompact (g '' F.factorSupportCarrier) :=
    F.factorSupportCarrier_compact.image
      (show Continuous g by fun_prop)
  exact le_csSup hcompact.bddAbove
    ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩

/-- Union of the original factor supports on the left of one chronological
gap. -/
def OSIIChronologicalCompactFactors.leftSupportCarrier
    (F : OSIIChronologicalCompactFactors d k)
    (selected : Fin k) :
    Set (SpacetimeDim d) :=
  ⋃ i : Fin (osiiChronologicalGapLeftArity selected),
    tsupport
      ((F.factors
        (osiiChronologicalGapSplitEquiv selected (Sum.inl i)) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)

/-- Union of the original factor supports on the right of one chronological
gap. -/
def OSIIChronologicalCompactFactors.rightSupportCarrier
    (F : OSIIChronologicalCompactFactors d k)
    (selected : Fin k) :
    Set (SpacetimeDim d) :=
  ⋃ j : Fin (osiiChronologicalGapRightArity selected),
    tsupport
      ((F.factors
        (osiiChronologicalGapSplitEquiv selected (Sum.inr j)) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)

theorem OSIIChronologicalCompactFactors.leftSupportCarrier_compact
    (F : OSIIChronologicalCompactFactors d k)
    (selected : Fin k) :
    IsCompact (F.leftSupportCarrier selected) := by
  apply isCompact_iUnion
  intro i
  exact
    (F.factor_compact
      (osiiChronologicalGapSplitEquiv selected (Sum.inl i))).isCompact

theorem OSIIChronologicalCompactFactors.rightSupportCarrier_compact
    (F : OSIIChronologicalCompactFactors d k)
    (selected : Fin k) :
    IsCompact (F.rightSupportCarrier selected) := by
  apply isCompact_iUnion
  intro j
  exact
    (F.factor_compact
      (osiiChronologicalGapSplitEquiv selected (Sum.inr j))).isCompact

/-- Quantitative separator data for one packet split in one axis-pair frame.
Besides the sign conditions used by the packet construction, it retains a
common bound on the rotated support times and a corresponding bound on the
chosen offset. -/
structure OSIIAxisPairCenterOffsetData
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) where
  offset : ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  offset_abs_le : |offset| ≤ 2 * bound + 1
  offset_abs_le_of_bound :
    ∀ B : ℝ, 0 ≤ B →
      (∀ y ∈ F.leftSupportCarrier selected,
        |((osiiAxisPairRotationData T a).matrix.mulVec y) 0| ≤ B) →
      (∀ z ∈ F.rightSupportCarrier selected,
        |((osiiAxisPairRotationData T a).matrix.mulVec z) 0| ≤ B) →
      |offset| ≤ 2 * B + 1
  left_abs_le :
    ∀ y ∈ F.leftSupportCarrier selected,
      |((osiiAxisPairRotationData T a).matrix.mulVec y) 0| ≤ bound
  right_abs_le :
    ∀ z ∈ F.rightSupportCarrier selected,
      |((osiiAxisPairRotationData T a).matrix.mulVec z) 0| ≤ bound
  left_negative :
    ∀ y ∈ F.leftSupportCarrier selected,
      ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 + offset < 0
  right_positive :
    ∀ z ∈ F.rightSupportCarrier selected,
      0 < ((osiiAxisPairRotationData T a).matrix.mulVec z) 0 + offset

theorem OSIIChronologicalCompactFactors.nonempty_axisPairCenterOffsetData
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) :
    Nonempty (OSIIAxisPairCenterOffsetData F T selected a) := by
  let D := osiiAxisPairRotationData T a
  obtain
      ⟨c, B, hB, hcB, hcB', hleftB, hrightB, hleft, hright⟩ :=
    exists_bounded_center_shift_of_compact_cross_order
      (F.leftSupportCarrier_compact selected)
      (F.rightSupportCarrier_compact selected)
      (show Continuous
        (fun y : SpacetimeDim d => (D.matrix.mulVec y) 0) by fun_prop)
      (by
        intro y hy z hz
        rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
        have hidx :
            osiiChronologicalGapSplitEquiv selected (Sum.inl i) <
              osiiChronologicalGapSplitEquiv selected (Sum.inr j) := by
          have hli :=
            osiiChronologicalGapSplitEquiv_left_not_after selected i
          have hrj :=
            osiiChronologicalGapSplitEquiv_right_after selected j
          omega
        exact hordered a _ _ hidx y hi z hj)
  exact
    ⟨{
      offset := c
      bound := B
      bound_nonneg := hB
      offset_abs_le := hcB
      offset_abs_le_of_bound := hcB'
      left_abs_le := hleftB
      right_abs_le := hrightB
      left_negative := hleft
      right_positive := hright }⟩

/-- An externally supplied rotated-support bound yields separator data that
records that exact bound. This is the quantitative form needed when the
carrier changes along an exhaustion. -/
theorem OSIIChronologicalCompactFactors.nonempty_axisPairCenterOffsetDataOfBound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d)
    (B : ℝ) (hB : 0 ≤ B)
    (hfactor_bound :
      ∀ i : Fin (k + 1), ∀ y ∈ tsupport
          ((F.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        |((osiiAxisPairRotationData T a).matrix.mulVec y) 0| ≤ B) :
    Nonempty
      {data : OSIIAxisPairCenterOffsetData F T selected a //
        data.bound = B} := by
  let D := osiiAxisPairRotationData T a
  have hleft_bound :
      ∀ y ∈ F.leftSupportCarrier selected,
        |(D.matrix.mulVec y) 0| ≤ B := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact hfactor_bound _ y hi
  have hright_bound :
      ∀ z ∈ F.rightSupportCarrier selected,
        |(D.matrix.mulVec z) 0| ≤ B := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
    exact hfactor_bound _ z hj
  obtain ⟨data⟩ :=
    F.nonempty_axisPairCenterOffsetData T hordered selected a
  have hcB :
      |data.offset| ≤ 2 * B + 1 :=
    data.offset_abs_le_of_bound B hB hleft_bound hright_bound
  exact
    ⟨⟨{
      offset := data.offset
      bound := B
      bound_nonneg := hB
      offset_abs_le := hcB
      offset_abs_le_of_bound := data.offset_abs_le_of_bound
      left_abs_le := hleft_bound
      right_abs_le := hright_bound
      left_negative := data.left_negative
      right_positive := data.right_positive },
      rfl⟩⟩

/-- Separator data selected with the canonical rotated-support-time bound. -/
noncomputable def
    OSIIChronologicalCompactFactors.axisPairCenterOffsetDataOfRotatedTimeBound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) :
    {data : OSIIAxisPairCenterOffsetData F T selected a //
      data.bound = F.axisPairRotatedTimeBound T a} :=
  Classical.choice
    (F.nonempty_axisPairCenterOffsetDataOfBound
      T hordered selected a
      (F.axisPairRotatedTimeBound T a)
      (F.axisPairRotatedTimeBound_nonneg T a)
      (fun i y hy =>
        F.abs_rotated_factor_time_le_bound T a i hy))

/-- The quantitatively controlled separator selected for this split/frame. -/
noncomputable def OSIIChronologicalCompactFactors.axisPairCenterOffsetData
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) :
    OSIIAxisPairCenterOffsetData F T selected a :=
  (F.axisPairCenterOffsetDataOfRotatedTimeBound
    T hordered selected a).1

/-- Fixed split/frame offset supplied by compact support separation. -/
noncomputable def OSIIChronologicalCompactFactors.axisPairCenterOffset
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) :
    ℝ :=
  (F.axisPairCenterOffsetData T hordered selected a).offset

/-- The actual selected separator is controlled by any common rotated-time
bound on the factor supports, not only by the auxiliary bound retained during
its construction. -/
theorem
    OSIIChronologicalCompactFactors.abs_axisPairCenterOffset_le_of_factor_bound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d)
    (B : ℝ) (hB : 0 ≤ B)
    (hfactor_bound :
      ∀ i : Fin (k + 1), ∀ y ∈ tsupport
          ((F.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        |((osiiAxisPairRotationData T a).matrix.mulVec y) 0| ≤ B) :
    |F.axisPairCenterOffset T hordered selected a| ≤ 2 * B + 1 := by
  apply
    (F.axisPairCenterOffsetData T hordered selected a
      ).offset_abs_le_of_bound B hB
  · intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact hfactor_bound _ y hi
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
    exact hfactor_bound _ z hj

theorem OSIIChronologicalCompactFactors.axisPairCenterOffset_spec
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (selected : Fin k)
    (a : osiiAxisPairIndex d) :
    (∀ i : Fin (osiiChronologicalGapLeftArity selected),
      ∀ y ∈ tsupport
          ((F.factors
            (osiiChronologicalGapSplitEquiv selected (Sum.inl i)) :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ),
        ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 +
            F.axisPairCenterOffset T hordered selected a < 0) ∧
    ∀ j : Fin (osiiChronologicalGapRightArity selected),
      ∀ z ∈ tsupport
          ((F.factors
            (osiiChronologicalGapSplitEquiv selected (Sum.inr j)) :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ),
        0 < ((osiiAxisPairRotationData T a).matrix.mulVec z) 0 +
          F.axisPairCenterOffset T hordered selected a :=
  ⟨fun i y hy =>
      (F.axisPairCenterOffsetData T hordered selected a).left_negative
        y (Set.mem_iUnion.mpr ⟨i, hy⟩),
    fun j z hz =>
      (F.axisPairCenterOffsetData T hordered selected a).right_positive
        z (Set.mem_iUnion.mpr ⟨j, hz⟩)⟩

/-- Explicit packet center: cancel the omitted-gap prefix at the first right
point, then add the fixed support-separating offset in the selected direction. -/
noncomputable def OSIIChronologicalCompactFactors.packetCenter
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    SpacetimeDim d :=
  -osiiAxisPairChronologicalPointTranslationWithoutGap
      T x q.1 (Fin.succ q.1) +
    (F.axisPairCenterOffset T hordered q.1 q.2 /
        osiiAxisPairRadius T) •
      osiiAxisPairDir (d := d) T q.2

theorem OSIIChronologicalCompactFactors.packetCenter_congr_of_eq_off_selected
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) :
    F.packetCenter T hordered x q =
      F.packetCenter T hordered y q := by
  rw [OSIIChronologicalCompactFactors.packetCenter,
    OSIIChronologicalCompactFactors.packetCenter,
    osiiAxisPairChronologicalPointTranslationWithoutGap_congr_of_eq_off_selected
      T q hxy]

theorem OSIIChronologicalCompactFactors.mulVec_packetCenter_time
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    ((osiiAxisPairRotationData T q.2).matrix.mulVec
        (F.packetCenter T hordered x q)) 0 =
      -((osiiAxisPairRotationData T q.2).matrix.mulVec
          (osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1 (Fin.succ q.1))) 0 +
        F.axisPairCenterOffset T hordered q.1 q.2 := by
  let D := osiiAxisPairRotationData T q.2
  rw [OSIIChronologicalCompactFactors.packetCenter,
    Matrix.mulVec_add, Matrix.mulVec_neg,
    osiiAxisPairRotation_mulVec_smul_dir
      D.orthogonal D.transpose_timeShift]
  simp only [Pi.add_apply, Pi.neg_apply, timeShiftVec, if_pos]
  rw [div_mul_cancel₀ _ (ne_of_gt (osiiAxisPairRadius_pos T))]

/-- Corrected compensated left source. Reversing the left block is necessary
because the selected negative cone is strictly decreasing in its source index. -/
noncomputable def OSIIChronologicalCompactFactors.packetLeftSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
  translateSchwartzNPoint (d := d) (F.packetCenter T hordered x q)
    (osiiAxisPairChronologicalUncutLeftSource
      T x q.1 F.factors).reverse

/-- Right source paired with `packetLeftSource`. -/
noncomputable def OSIIChronologicalCompactFactors.packetRightSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
  osiiAxisPairChronologicalCenteredRightSource
    T x q.1 (F.packetCenter T hordered x q) F.factors

theorem OSIIChronologicalCompactFactors.packetLeftSource_congr_of_eq_off_selected
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) :
    F.packetLeftSource T hordered x q =
      F.packetLeftSource T hordered y q := by
  rw [OSIIChronologicalCompactFactors.packetLeftSource,
    OSIIChronologicalCompactFactors.packetLeftSource,
    F.packetCenter_congr_of_eq_off_selected T hordered q hxy,
    osiiAxisPairChronologicalUncutLeftSource_congr_of_eq_off_selected
      T q hxy F.factors]

theorem OSIIChronologicalCompactFactors.packetRightSource_congr_of_eq_off_selected
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) :
    F.packetRightSource T hordered x q =
      F.packetRightSource T hordered y q := by
  exact
    osiiAxisPairChronologicalCenteredRightSource_congr_of_eq_off_selected
      T q hxy
      (F.packetCenter_congr_of_eq_off_selected T hordered q hxy)
      F.factors

/-- A coordinate of the corrected left source pulls back to the packet-base
factor indexed by the reversed left-block coordinate. -/
theorem OSIIChronologicalCompactFactors.packetLeftSource_tsupport_factor
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    {y : NPointDomain d (osiiChronologicalGapLeftArity q.1)}
    (hy :
      y ∈ tsupport
        (F.packetLeftSource T hordered x q :
          NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ))
    (i : Fin (osiiChronologicalGapLeftArity q.1)) :
    y i - F.packetCenter T hordered x q ∈
      tsupport
        ((osiiAxisPairChronologicalPacketBaseFactors
          T x q.1 F.factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inl (Fin.rev i))) :
            SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  let center := F.packetCenter T hordered x q
  let uncut :=
    osiiAxisPairChronologicalUncutLeftSource T x q.1 F.factors
  have htranslated :
      (fun j => y j - center) ∈
        tsupport
          ((uncut.reverse :
            SchwartzNPoint d (osiiChronologicalGapLeftArity q.1)) :
              NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        ((uncut.reverse :
          SchwartzNPoint d (osiiChronologicalGapLeftArity q.1)) :
            NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ)
        (show Continuous
          (fun w : NPointDomain d (osiiChronologicalGapLeftArity q.1) =>
            fun j => w j - center) by fun_prop)
        hy
    simpa [OSIIChronologicalCompactFactors.packetLeftSource,
      center, uncut, translateSchwartzNPoint_apply] using hpre
  have hreversed :
      (fun j => (y (Fin.rev j) - center)) ∈
        tsupport
          (uncut :
            NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (uncut :
          NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ)
        (show Continuous
          (fun w : NPointDomain d (osiiChronologicalGapLeftArity q.1) =>
            fun j => w (Fin.rev j)) by fun_prop)
        htranslated
    simpa [SchwartzMap.reverse_apply] using hpre
  have hfactor :=
    tsupport_productTensor_subset_factor_tsupport
      (fun j =>
        (osiiAxisPairChronologicalPacketBaseFactors
          T x q.1 F.factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inl j))).conj)
      (by
        simpa [uncut, osiiAxisPairChronologicalUncutLeftSource] using
          hreversed)
      (Fin.rev i)
  rw [tsupport_schwartzMap_conj] at hfactor
  simpa [Fin.rev_rev] using hfactor

/-- A coordinate of the centered right source pulls back to its packet-base
factor. -/
theorem OSIIChronologicalCompactFactors.packetRightSource_tsupport_factor
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    {y : NPointDomain d (osiiChronologicalGapRightArity q.1)}
    (hy :
      y ∈ tsupport
        (F.packetRightSource T hordered x q :
          NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ))
    (j : Fin (osiiChronologicalGapRightArity q.1)) :
    y j - F.packetCenter T hordered x q ∈
      tsupport
        ((osiiAxisPairChronologicalPacketBaseFactors
          T x q.1 F.factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)) :
            SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  let center := F.packetCenter T hordered x q
  let uncut :=
    osiiAxisPairChronologicalUncutRightSource T x q.1 F.factors
  have htranslated :
      (fun r => y r - center) ∈
        tsupport
          (uncut :
            NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (uncut :
          NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ)
        (show Continuous
          (fun w : NPointDomain d (osiiChronologicalGapRightArity q.1) =>
            fun r => w r - center) by fun_prop)
        hy
    simpa [OSIIChronologicalCompactFactors.packetRightSource,
      osiiAxisPairChronologicalCenteredRightSource,
      center, uncut, translateSchwartzNPoint_apply] using hpre
  exact
    tsupport_productTensor_subset_factor_tsupport
      (fun r =>
        osiiAxisPairChronologicalPacketBaseFactors
          T x q.1 F.factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inr r)))
      (by
        simpa [uncut, osiiAxisPairChronologicalUncutRightSource] using
          htranslated)
      j

/-- The corrected left source lies in the selected rotated negative cone. -/
theorem OSIIChronologicalCompactFactors.packetLeftSource_support
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (F.packetLeftSource T hordered x q :
          NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
      osiiEuclideanRotationOrderedNegativeTimeRegion
        (d := d) (n := osiiChronologicalGapLeftArity q.1)
        (osiiAxisPairRotationData T q.2).matrix := by
  intro y hy
  let D := osiiAxisPairRotationData T q.2
  let center := F.packetCenter T hordered x q
  let splitPoint : Fin (k + 1) := Fin.succ q.1
  intro i
  have hiFactor :=
    F.packetLeftSource_tsupport_factor T hordered x q hy i
  let ri : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev i
  let oi : Fin (k + 1) :=
    osiiChronologicalGapSplitEquiv q.1 (Sum.inl ri)
  let vi :=
    osiiAxisPairChronologicalPointTranslationWithoutGap T x q.1 oi
  have hiOriginal :
      (y i - center) - vi ∈
        tsupport
          ((F.factors oi : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    exact
      osiiAxisPairChronologicalPacketBaseFactors_tsupport_sub
        T x q.1 F.factors oi hiFactor
  have hiOffset :=
    (F.axisPairCenterOffset_spec T hordered q.1 q.2).1
      ri ((y i - center) - vi) hiOriginal
  have hoi_split : oi ≤ splitPoint := by
    have hnot := osiiChronologicalGapSplitEquiv_left_not_after q.1 ri
    change oi.val ≤ splitPoint.val
    dsimp [oi, splitPoint]
    omega
  have hmono :
      (D.matrix.mulVec vi) 0 ≤
        (D.matrix.mulVec
          (osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1 splitPoint)) 0 :=
    D.mulVec_chronologicalPointTranslationWithoutGap_time_mono_le
      hT x q.1 hoi_split
  have hcenter := F.mulVec_packetCenter_time T hordered x q
  constructor
  · dsimp [D, center, splitPoint, vi] at hiOffset hmono hcenter ⊢
    simp only [Matrix.mulVec_sub, Pi.sub_apply] at hiOffset
    linarith
  · intro j hij
    have hjFactor :=
      F.packetLeftSource_tsupport_factor T hordered x q hy j
    let rj : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev j
    let oj : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
    have hrji : rj < ri := by
      dsimp [ri, rj]
      exact Fin.rev_lt_rev.mpr hij
    have hoji : oj < oi := by
      change rj.val < ri.val
      exact hrji
    have hpair :=
      packetBaseFactors_pairwise_ordered F T hT hordered
        x q.1 q.2 oj oi hoji hjFactor hiFactor
    dsimp [D, center] at hpair ⊢
    simp only [Matrix.mulVec_sub, Pi.sub_apply] at hpair
    linarith

/-- The centered right source lies in the selected rotated positive cone. -/
theorem OSIIChronologicalCompactFactors.packetRightSource_support
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (F.packetRightSource T hordered x q :
          NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := osiiChronologicalGapRightArity q.1)
        (osiiAxisPairRotationData T q.2).matrix := by
  intro y hy
  let D := osiiAxisPairRotationData T q.2
  let center := F.packetCenter T hordered x q
  let splitPoint : Fin (k + 1) := Fin.succ q.1
  intro i
  have hiFactor :=
    F.packetRightSource_tsupport_factor T hordered x q hy i
  let oi : Fin (k + 1) :=
    osiiChronologicalGapSplitEquiv q.1 (Sum.inr i)
  let vi :=
    osiiAxisPairChronologicalPointTranslationWithoutGap T x q.1 oi
  have hiOriginal :
      (y i - center) - vi ∈
        tsupport
          ((F.factors oi : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    exact
      osiiAxisPairChronologicalPacketBaseFactors_tsupport_sub
        T x q.1 F.factors oi hiFactor
  have hiOffset :=
    (F.axisPairCenterOffset_spec T hordered q.1 q.2).2
      i ((y i - center) - vi) hiOriginal
  have hsplit_oi : splitPoint ≤ oi := by
    have hafter := osiiChronologicalGapSplitEquiv_right_after q.1 i
    change splitPoint.val ≤ oi.val
    dsimp [splitPoint, oi]
    omega
  have hmono :
      (D.matrix.mulVec
          (osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1 splitPoint)) 0 ≤
        (D.matrix.mulVec vi) 0 :=
    D.mulVec_chronologicalPointTranslationWithoutGap_time_mono_le
      hT x q.1 hsplit_oi
  have hcenter := F.mulVec_packetCenter_time T hordered x q
  constructor
  · dsimp [D, center, splitPoint, vi] at hiOffset hmono hcenter ⊢
    simp only [Matrix.mulVec_sub, Pi.sub_apply] at hiOffset
    linarith
  · intro j hij
    have hjFactor :=
      F.packetRightSource_tsupport_factor T hordered x q hy j
    let oj : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)
    have hoij : oi < oj := by
      change
        osiiChronologicalGapLeftArity q.1 + i.val <
          osiiChronologicalGapLeftArity q.1 + j.val
      omega
    have hpair :=
      packetBaseFactors_pairwise_ordered F T hT hordered
        x q.1 q.2 oi oj hoij hiFactor hjFactor
    dsimp [D, center] at hpair ⊢
    simp only [Matrix.mulVec_sub, Pi.sub_apply] at hpair
    linarith

/-- Uncentered common-real source with the mathematically necessary reversal
of the left chronological block. -/
noncomputable def OSIIChronologicalCompactFactors.reversedUncutSplitSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k) :
    SchwartzNPoint d
      (osiiChronologicalGapLeftArity selected +
        osiiChronologicalGapRightArity selected) :=
  OSIIAxisPairRotatedSourcePacket.commonRealSource
    T (osiiAxisPairPositiveCoefficients (x selected))
    (osiiAxisPairChronologicalUncutLeftSource
      T x selected F.factors).reverse
    (osiiAxisPairChronologicalUncutRightSource
      T x selected F.factors)

@[simp] theorem osiiAxisPairLeftBlockReversePerm_self
    (n m : ℕ) (i : Fin (n + m)) :
    osiiAxisPairLeftBlockReversePerm n m
        (osiiAxisPairLeftBlockReversePerm n m i) =
      i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp

/-- Reversing the left input source is exactly reindexing the old uncut split
source by the first-block reversal permutation. -/
theorem OSIIChronologicalCompactFactors.reversedUncutSplitSource_eq_reindex
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k) :
    F.reversedUncutSplitSource T x selected =
      reindexSchwartz (d := d)
        (osiiAxisPairLeftBlockReversePerm
          (osiiChronologicalGapLeftArity selected)
          (osiiChronologicalGapRightArity selected))
        (osiiAxisPairChronologicalUncutSplitSource
          T x selected F.factors) := by
  ext y
  rw [OSIIChronologicalCompactFactors.reversedUncutSplitSource,
    reindexSchwartz_apply,
    OSIIAxisPairRotatedSourcePacket.commonRealSource_apply,
    osiiAxisPairChronologicalUncutSplitSource,
    OSIIAxisPairRotatedSourcePacket.commonRealSource_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (starRingEnd ℂ)
    rw [SchwartzMap.reverse_apply]
    apply congrArg
      (osiiAxisPairChronologicalUncutLeftSource
        T x selected F.factors)
    funext i
    simp [splitFirst]
  · apply congrArg
      (osiiAxisPairChronologicalUncutRightSource
        T x selected F.factors)
    funext j
    congr 1
    simp [splitLast]

/-- Applying the same block reversal to the reversed split recovers the old
uncut split source. -/
theorem OSIIChronologicalCompactFactors.reindex_reversedUncutSplitSource_eq
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k) :
    reindexSchwartz (d := d)
        (osiiAxisPairLeftBlockReversePerm
          (osiiChronologicalGapLeftArity selected)
          (osiiChronologicalGapRightArity selected))
        (F.reversedUncutSplitSource T x selected) =
      osiiAxisPairChronologicalUncutSplitSource
        T x selected F.factors := by
  rw [F.reversedUncutSplitSource_eq_reindex]
  ext y
  simp [reindexSchwartz_apply]

/-- Centering the corrected left and right blocks translates their reversed
common-real source by the same common spacetime vector. -/
theorem OSIIChronologicalCompactFactors.packet_commonRealSource_eq_translate
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    OSIIAxisPairRotatedSourcePacket.commonRealSource
        T (osiiAxisPairPositiveCoefficients (x q.1))
        (F.packetLeftSource T hordered x q)
        (F.packetRightSource T hordered x q) =
      translateSchwartzNPoint (d := d)
        (F.packetCenter T hordered x q)
        (F.reversedUncutSplitSource T x q.1) := by
  ext y
  simp only [OSIIAxisPairRotatedSourcePacket.commonRealSource_apply,
    OSIIChronologicalCompactFactors.packetLeftSource,
    OSIIChronologicalCompactFactors.packetRightSource,
    osiiAxisPairChronologicalCenteredRightSource,
    OSIIChronologicalCompactFactors.reversedUncutSplitSource,
    translateSchwartzNPoint_apply, SchwartzMap.reverse_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (starRingEnd ℂ)
    apply congrArg
      (osiiAxisPairChronologicalUncutLeftSource
        T x q.1 F.factors)
    funext i
    simp [splitFirst]
  · apply congrArg
      (osiiAxisPairChronologicalUncutRightSource
        T x q.1 F.factors)
    funext j
    change
      (splitLast
          (osiiChronologicalGapLeftArity q.1)
          (osiiChronologicalGapRightArity q.1) y j -
          ∑ b : osiiAxisPairIndex d,
            osiiAxisPairPositiveCoefficients (x q.1) b •
              osiiAxisPairDir (d := d) T b) -
          F.packetCenter T hordered x q =
        (splitLast
          (osiiChronologicalGapLeftArity q.1)
          (osiiChronologicalGapRightArity q.1) y j -
          F.packetCenter T hordered x q) -
          ∑ b : osiiAxisPairIndex d,
            osiiAxisPairPositiveCoefficients (x q.1) b •
              osiiAxisPairDir (d := d) T b
    abel

/-- E1 removes the explicit center and E3 removes the left-block reversal, so
the corrected packet has the same canonical chronological Schwinger edge. -/
theorem OSIIChronologicalCompactFactors.packet_commonRealSource_schwinger_eq
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (hcentered :
      VanishesToInfiniteOrderOnCoincidence
        (OSIIAxisPairRotatedSourcePacket.commonRealSource
          T (osiiAxisPairPositiveCoefficients (x q.1))
          (F.packetLeftSource T hordered x q)
          (F.packetRightSource T hordered x q))) :
    OS.S
        (osiiChronologicalGapLeftArity q.1 +
          osiiChronologicalGapRightArity q.1)
        (ZeroDiagonalSchwartz.ofClassical
          (OSIIAxisPairRotatedSourcePacket.commonRealSource
            T (osiiAxisPairPositiveCoefficients (x q.1))
            (F.packetLeftSource T hordered x q)
            (F.packetRightSource T hordered x q))) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x F.factors))) := by
  let n := osiiChronologicalGapLeftArity q.1
  let m := osiiChronologicalGapRightArity q.1
  let σ : Equiv.Perm (Fin (n + m)) :=
    osiiAxisPairLeftBlockReversePerm n m
  let reversed := F.reversedUncutSplitSource T x q.1
  let uncut :=
    osiiAxisPairChronologicalUncutSplitSource T x q.1 F.factors
  have htranslated :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzNPoint (d := d)
          (F.packetCenter T hordered x q) reversed) := by
    rw [← F.packet_commonRealSource_eq_translate T hordered x q]
    exact hcentered
  have hreversed : VanishesToInfiniteOrderOnCoincidence reversed :=
    (VanishesToInfiniteOrderOnCoincidence.translateSchwartzNPoint_iff
      (F.packetCenter T hordered x q) reversed).1 htranslated
  have hreindex :
      reindexSchwartz (d := d) σ reversed = uncut := by
    dsimp [σ, reversed, uncut, n, m]
    exact F.reindex_reversedUncutSplitSource_eq T x q.1
  have huncut : VanishesToInfiniteOrderOnCoincidence uncut := by
    rw [← hreindex]
    exact
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        hreversed σ
  let reversedZ : ZeroDiagonalSchwartz d (n + m) :=
    ⟨reversed, hreversed⟩
  let uncutZ : ZeroDiagonalSchwartz d (n + m) :=
    ⟨uncut, huncut⟩
  have hE3 : OS.S (n + m) reversedZ = OS.S (n + m) uncutZ := by
    refine OS.E3_symmetric (n := n + m) σ reversedZ uncutZ ?_
    intro y
    change uncut y = reversed (fun i => y (σ i))
    rw [← hreindex]
    rfl
  calc
    OS.S
        (osiiChronologicalGapLeftArity q.1 +
          osiiChronologicalGapRightArity q.1)
        (ZeroDiagonalSchwartz.ofClassical
          (OSIIAxisPairRotatedSourcePacket.commonRealSource
            T (osiiAxisPairPositiveCoefficients (x q.1))
            (F.packetLeftSource T hordered x q)
            (F.packetRightSource T hordered x q))) =
      OS.S (n + m)
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzNPoint (d := d)
            (F.packetCenter T hordered x q) reversed)) := by
              rw [F.packet_commonRealSource_eq_translate]
    _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical reversed) :=
      osiiSchwinger_translateSchwartzNPoint_eq OS
        (F.packetCenter T hordered x q) reversed hreversed
    _ = OS.S (n + m) reversedZ := by
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes reversed hreversed]
    _ = OS.S (n + m) uncutZ := hE3
    _ = OS.S
        (osiiChronologicalGapLeftArity q.1 +
          osiiChronologicalGapRightArity q.1)
        (ZeroDiagonalSchwartz.ofClassical uncut) := by
          dsimp [n, m, uncutZ]
          rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes uncut huncut]
    _ = OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x F.factors))) :=
      osiiAxisPairChronologicalUncutSplitSource_schwinger_eq_productTensor
        OS T x q.1 F.factors

/-- The canonical fully translated chronological product is an honest
zero-diagonal test. This extracts the support argument already used by every
one-variable packet edge, without involving the Schwinger functional. -/
theorem OSIIChronologicalCompactFactors.chronologicalTranslated_productTensor_vanishes
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.productTensor
        (osiiAxisPairChronologicalTranslatedFactors T x F.factors)) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let selected : Fin k := ⟨0, hk⟩
  let a : osiiAxisPairIndex d := (⟨0, hd⟩, false)
  let q : osiiAxisPairMultiGapIndex d k := (selected, a)
  let reversed := F.reversedUncutSplitSource T x q.1
  let uncut :=
    osiiAxisPairChronologicalUncutSplitSource T x q.1 F.factors
  have hcentered :
      VanishesToInfiniteOrderOnCoincidence
        (OSIIAxisPairRotatedSourcePacket.commonRealSource
          T (osiiAxisPairPositiveCoefficients (x q.1))
          (F.packetLeftSource T hordered x q)
          (F.packetRightSource T hordered x q)) :=
    OSIIAxisPairRotatedSourcePacket.commonRealSource_vanishes
      T hT
      (osiiAxisPairPositiveCoefficients (x q.1))
      (fun b =>
        le_of_lt (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
      q.2
      (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
      (F.packetLeftSource T hordered x q)
      (F.packetLeftSource_support T hT hordered x q)
      (F.packetRightSource T hordered x q)
      (F.packetRightSource_support T hT hordered x q)
  have htranslated :
      VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzNPoint (d := d)
          (F.packetCenter T hordered x q) reversed) := by
    rw [← F.packet_commonRealSource_eq_translate T hordered x q]
    exact hcentered
  have hreversed : VanishesToInfiniteOrderOnCoincidence reversed :=
    (VanishesToInfiniteOrderOnCoincidence.translateSchwartzNPoint_iff
      (F.packetCenter T hordered x q) reversed).1 htranslated
  have hreindex :
      reindexSchwartz (d := d)
          (osiiAxisPairLeftBlockReversePerm
            (osiiChronologicalGapLeftArity q.1)
            (osiiChronologicalGapRightArity q.1))
          reversed =
        uncut := by
    dsimp [reversed, uncut]
    exact F.reindex_reversedUncutSplitSource_eq T x q.1
  have huncut : VanishesToInfiniteOrderOnCoincidence uncut := by
    rw [← hreindex]
    exact
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        hreversed
        (osiiAxisPairLeftBlockReversePerm
          (osiiChronologicalGapLeftArity q.1)
          (osiiChronologicalGapRightArity q.1))
  have hfull :
      VanishesToInfiniteOrderOnCoincidence
        (reindexSchwartz (d := d)
          (finCongr (osiiChronologicalGap_arity_add q.1)) uncut) :=
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      huncut (finCongr (osiiChronologicalGap_arity_add q.1))
  rw [reindex_osiiAxisPairChronologicalUncutSplitSource_eq_productTensor] at hfull
  exact hfull

/-- Ordered compact chronological factors produce the physical dependent
multi-gap packet family. The left-block reversal is internal to the packet;
E3 restores the canonical chronological product on every real edge. -/
noncomputable def OSIIChronologicalCompactFactors.multiGapPacketFamily
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc :=
  OSIIAxisPairMultiGapSemigroupPacketFamily.ofCompensatedFrozenDependent
    OS lgc T hT
    (fun x q => F.packetLeftSource T hordered x q)
    (fun x q => F.packetLeftSource_support T hT hordered x q)
    (fun x q => F.packetRightSource T hordered x q)
    (fun x q => F.packetRightSource_support T hT hordered x q)
    (by
      intro x y q hxy
      exact F.packetLeftSource_congr_of_eq_off_selected
        T hordered q hxy)
    (by
      intro x y q hxy
      exact F.packetRightSource_congr_of_eq_off_selected
        T hordered q hxy)
    (fun x =>
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x F.factors))))
    (by
      intro x q
      apply F.packet_commonRealSource_schwinger_eq OS T hordered x q
      exact
        OSIIAxisPairRotatedSourcePacket.commonRealSource_vanishes
          T hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b =>
            le_of_lt (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2
          (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
          (F.packetLeftSource T hordered x q)
          (F.packetLeftSource_support T hT hordered x q)
          (F.packetRightSource T hordered x q)
          (F.packetRightSource_support T hT hordered x q))

end OSReconstruction
