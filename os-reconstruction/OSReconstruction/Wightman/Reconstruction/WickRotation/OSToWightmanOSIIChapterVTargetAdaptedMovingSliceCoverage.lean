/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeReflectedSchwingerGerm



















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Recenter a mixed Hilbert target by the tail of a positive source anchor.
The distinguished head coordinate of the source anchor is omitted. -/
def tailAnchorCenteredPoint
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) :
    Fin m → ℂ :=
  fun i => z i - anchor i.succ

/-- The cutoff-time lower bound that exactly cancels a recentered source
anchor in the reflected pair. -/
def ReflectedTimeDominatesTailAnchor
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (τ : Fin (m + (m + 1)) → ℝ) : Prop :=
  (∀ i : Fin m,
      anchor (Fin.rev i).succ ≤
        τ (Fin.castAdd (m + 1) i)) ∧
    0 < τ (Fin.natAdd m (0 : Fin (m + 1))) ∧
    ∀ i : Fin m,
      anchor i.succ ≤ τ (Fin.natAdd m i.succ)

/-- An open reflected-time neighborhood retaining a prescribed amount of
room below a source anchor.

The reflected source carrier itself only satisfies closed anchor lower
bounds.  A cutoff equal to one on that carrier cannot have support in the
same closed region.  This open thickening spends `margin` below the tail
anchor coordinates and below twice the head anchor at the bridge. -/
def reflectedTimeAnchorMarginRegion
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (margin : ℝ) :
    Set (Fin (m + (m + 1)) → ℝ) :=
  {τ |
    (∀ i : Fin m,
      anchor (Fin.rev i).succ - margin <
        τ (Fin.castAdd (m + 1) i)) ∧
    2 * anchor 0 - margin <
      τ (Fin.natAdd m (0 : Fin (m + 1))) ∧
    ∀ i : Fin m,
      anchor i.succ - margin <
        τ (Fin.natAdd m i.succ)}

theorem sub_two_mul_margin_mem_strictPositive
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {margin : ℝ}
    (hmargin : ∀ i, 2 * margin < anchor i) :
    (fun i => anchor i - 2 * margin) ∈
      section43TimeStrictPositiveRegion (m + 1) := by
  intro i
  linarith [hmargin i]

/-- After translating an open margin region down by `margin`, the reflected
time still dominates the anchor shifted down by `2 * margin`.

This is the useful two-for-one bookkeeping: one half of a radial shift budget
opens room for the cutoff support, and the other half is the actual VI.2
translation. -/
theorem reflectedTimeAnchorMarginRegion_sub_const_dominates
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {margin : ℝ}
    (hmargin_pos : 0 < margin)
    (hmargin : ∀ i, 2 * margin < anchor i)
    {τ : Fin (m + (m + 1)) → ℝ}
    (hτ : τ ∈ reflectedTimeAnchorMarginRegion anchor margin) :
    ReflectedTimeDominatesTailAnchor
      (fun i => anchor i - 2 * margin)
      (fun j => τ j - margin) := by
  constructor
  · intro i
    linarith [hτ.1 i]
  constructor
  · linarith [hτ.2.1, hmargin 0]
  · intro i
    linarith [hτ.2.2 i]

namespace ReflectedTimeDominatesTailAnchor

theorem strictPositive
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {τ : Fin (m + (m + 1)) → ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hτ : ReflectedTimeDominatesTailAnchor anchor τ) :
    τ ∈ section43TimeStrictPositiveRegion (m + (m + 1)) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    exact lt_of_lt_of_le
      (hanchor (Fin.rev i).succ) (hτ.1 i)
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact hτ.2.1
    · exact lt_of_lt_of_le (hanchor i.succ) (hτ.2.2 i)

end ReflectedTimeDominatesTailAnchor

@[simp]
theorem reflectedChronologicalGapMap_left
    {m : ℕ}
    (τleft τright : Fin (m + 1) → ℝ)
    (i : Fin m) :
    reflectedChronologicalGapMap m (τleft, τright)
        (Fin.castAdd (m + 1) i) =
      τleft (Fin.rev i).succ := by
  simp [reflectedChronologicalGapMap]
  congr 1
  apply Fin.ext
  simp
  omega

@[simp]
theorem reflectedChronologicalGapMap_bridge
    {m : ℕ}
    (τleft τright : Fin (m + 1) → ℝ) :
    reflectedChronologicalGapMap m (τleft, τright)
        (Fin.natAdd m (0 : Fin (m + 1))) =
      τleft 0 + τright 0 := by
  simp [reflectedChronologicalGapMap]

@[simp]
theorem reflectedChronologicalGapMap_right
    {m : ℕ}
    (τleft τright : Fin (m + 1) → ℝ)
    (i : Fin m) :
    reflectedChronologicalGapMap m (τleft, τright)
        (Fin.natAdd m i.succ) =
      τright i.succ := by
  simp [reflectedChronologicalGapMap]
  congr 1

/-- Coordinatewise lower bounds on both source-time blocks transport to the
reflected cutoff-time lower bound. -/
theorem reflectedChronologicalGapMap_dominatesTailAnchor
    {m : ℕ}
    {anchor τleft τright : Fin (m + 1) → ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hleft : ∀ i, anchor i ≤ τleft i)
    (hright : ∀ i, anchor i ≤ τright i) :
    ReflectedTimeDominatesTailAnchor anchor
      (reflectedChronologicalGapMap m (τleft, τright)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa using hleft (Fin.rev i).succ
  · have hleft0 :
        0 < τleft (0 : Fin (m + 1)) :=
      lt_of_lt_of_le (hanchor 0) (hleft 0)
    have hright0 :
        0 < τright (0 : Fin (m + 1)) :=
      lt_of_lt_of_le (hanchor 0) (hright 0)
    simpa using add_pos hleft0 hright0
  · intro i
    simpa using hright i.succ

@[simp]
theorem reflectedCauchyShiftedStagePoint_tailAnchorCentered_left
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (t : ℝ)
    (i : Fin m) :
    reflectedCauchyShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z)
        (Fin.castAdd (m + 1) i) =
      (t : ℂ) * starRingEnd ℂ (z (Fin.rev i)) +
        (τ (Fin.castAdd (m + 1) i) -
          t * anchor (Fin.rev i).succ) := by
  rw [reflectedCauchyShiftedStagePoint_left]
  simp only [tailAnchorCenteredPoint, Pi.smul_apply,
    Complex.real_smul, map_mul, map_sub,
    Complex.conj_ofReal]
  ring

@[simp]
theorem reflectedCauchyShiftedStagePoint_tailAnchorCentered_bridge
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (t : ℝ) :
    reflectedCauchyShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z)
        (Fin.natAdd m (0 : Fin (m + 1))) =
      τ (Fin.natAdd m (0 : Fin (m + 1))) := by
  exact reflectedCauchyShiftedStagePoint_bridge τ _

@[simp]
theorem reflectedCauchyShiftedStagePoint_tailAnchorCentered_right
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (t : ℝ)
    (i : Fin m) :
    reflectedCauchyShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z)
        (Fin.natAdd m i.succ) =
      (t : ℂ) * z i +
        (τ (Fin.natAdd m i.succ) - t * anchor i.succ) := by
  rw [reflectedCauchyShiftedStagePoint_right]
  simp only [tailAnchorCenteredPoint, Pi.smul_apply,
    Complex.real_smul]
  ring

@[simp]
theorem zeroAnchorShiftedStagePoint_tailAnchorCentered_right
    {m : ℕ}
    (anchor : Fin (m + 1) → ℝ)
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (t : ℝ)
    (i : Fin m) :
    zeroAnchorShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z)
        (Fin.natAdd m i.succ) =
      (t : ℂ) * z i +
        (τ (Fin.natAdd m i.succ) - t * anchor i.succ) := by
  rw [zeroAnchorShiftedStagePoint_right]
  simp only [tailAnchorCenteredPoint, Pi.smul_apply,
    Complex.real_smul]
  ring

private theorem tailAnchor_residual_nonnegative
    {a shift t : ℝ}
    (ha : 0 < a)
    (hshift : a ≤ shift)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ shift - t * a := by
  have hscaled : t * a ≤ a := by
    exact mul_le_of_le_one_left (le_of_lt ha) ht.2
  linarith

/-- Positive radial rescaling followed by a nonnegative real translation can
only decrease the absolute principal argument.  The statement includes the
radial basepoint `t = 0`. -/
theorem abs_arg_real_smul_add_ofReal_le
    {z : ℂ}
    (hz : 0 < z.re)
    {t s : ℝ}
    (ht : 0 ≤ t)
    (hs : 0 ≤ s) :
    |Complex.arg ((t : ℂ) * z + (s : ℂ))| ≤
      |Complex.arg z| := by
  by_cases ht0 : t = 0
  · subst t
    rw [ofReal_zero, zero_mul, zero_add,
      Complex.arg_ofReal_of_nonneg hs]
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    calc
      |Complex.arg ((t : ℂ) * z + (s : ℂ))| ≤
          |Complex.arg ((t : ℂ) * z)| :=
        abs_arg_add_ofReal_le
          (by
            simpa using mul_pos htpos hz)
          hs
      _ = |Complex.arg z| := by
        rw [Complex.arg_real_mul z htpos]

/-- Anchor domination restores the product right half-plane for the
recentered reflected Cauchy path, even though the centered Hilbert point
itself need not lie in the right half-plane. -/
theorem
    reflectedCauchyShiftedStagePoint_tailAnchorCentered_mem_rightHalfPlane
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    {t : ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hτ : ReflectedTimeDominatesTailAnchor anchor τ)
    (hz : z ∈ osiiTimeRightHalfPlane m)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    reflectedCauchyShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z) ∈
      osiiTimeRightHalfPlane (m + (m + 1)) := by
  have hτpos := hτ.strictPositive hanchor
  by_cases ht0 : t = 0
  · subst t
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_left]
      simpa using hτpos (Fin.castAdd (m + 1) i)
    · intro r
      refine Fin.cases ?_ (fun i => ?_) r
      · rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_bridge]
        simpa using hτpos (Fin.natAdd m (0 : Fin (m + 1)))
      · rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_right]
        simpa using hτpos (Fin.natAdd m i.succ)
  · have htpos : 0 < t :=
      lt_of_le_of_ne ht.1 (Ne.symm ht0)
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_left]
      have hbase :
          0 <
            (((t : ℂ) *
              starRingEnd ℂ (z (Fin.rev i))).re) := by
        simpa using mul_pos htpos (by simpa using hz (Fin.rev i))
      have hres :
          0 ≤
            τ (Fin.castAdd (m + 1) i) -
              t * anchor (Fin.rev i).succ :=
        tailAnchor_residual_nonnegative
          (hanchor (Fin.rev i).succ) (hτ.1 i) ht
      simpa using add_pos_of_pos_of_nonneg hbase hres
    · intro r
      refine Fin.cases ?_ (fun i => ?_) r
      · rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_bridge]
        simpa using hτ.2.1
      · rw [reflectedCauchyShiftedStagePoint_tailAnchorCentered_right]
        have hbase :
            0 < (((t : ℂ) * z i).re) := by
          simpa using mul_pos htpos (hz i)
        have hres :
            0 ≤
              τ (Fin.natAdd m i.succ) -
                t * anchor i.succ :=
          tailAnchor_residual_nonnegative
            (hanchor i.succ) (hτ.2.2 i) ht
        simpa using add_pos_of_pos_of_nonneg hbase hres

/-- Along the recentered reflected Cauchy path, every scalar-stage principal
argument is bounded by the reflected diagonal of the original target. -/
theorem
    abs_argumentVector_reflectedCauchyShiftedStagePoint_tailAnchorCentered_le
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    {t : ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hτ : ReflectedTimeDominatesTailAnchor anchor τ)
    (hz : z ∈ osiiTimeRightHalfPlane m)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j,
      |osiiTimeArgumentVector
          (reflectedCauchyShiftedStagePoint τ
            (t • tailAnchorCenteredPoint anchor z)) j| ≤
        |reflectedMixedDiagonal z j| := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedMixedDiagonal_left]
    simp only [osiiTimeArgumentVector,
      reflectedCauchyShiftedStagePoint_tailAnchorCentered_left,
      abs_neg]
    have hres :
        0 ≤
          τ (Fin.castAdd (m + 1) i) -
            t * anchor (Fin.rev i).succ :=
      tailAnchor_residual_nonnegative
        (hanchor (Fin.rev i).succ) (hτ.1 i) ht
    calc
      |Complex.arg
          ((t : ℂ) * starRingEnd ℂ (z (Fin.rev i)) +
            (τ (Fin.castAdd (m + 1) i) -
              t * anchor (Fin.rev i).succ))| ≤
          |Complex.arg (starRingEnd ℂ (z (Fin.rev i)))| :=
        by
          simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using
            (abs_arg_real_smul_add_ofReal_le
              (z := starRingEnd ℂ (z (Fin.rev i)))
              (t := t)
              (s :=
                τ (Fin.castAdd (m + 1) i) -
                  t * anchor (Fin.rev i).succ)
              (by simpa using hz (Fin.rev i)) ht.1 hres)
      _ = |Complex.arg (z (Fin.rev i))| :=
        abs_arg_conj_eq_of_re_pos (hz (Fin.rev i))
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedMixedDiagonal_bridge]
      simp only [osiiTimeArgumentVector,
        reflectedCauchyShiftedStagePoint_tailAnchorCentered_bridge,
        abs_zero]
      rw [Complex.arg_ofReal_of_nonneg hτ.2.1.le]
      simp
    · rw [reflectedMixedDiagonal_right]
      simp only [osiiTimeArgumentVector,
        reflectedCauchyShiftedStagePoint_tailAnchorCentered_right]
      have hres :
          0 ≤
            τ (Fin.natAdd m i.succ) -
              t * anchor i.succ :=
        tailAnchor_residual_nonnegative
          (hanchor i.succ) (hτ.2.2 i) ht
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using
        (abs_arg_real_smul_add_ofReal_le
          (z := z i)
          (t := t)
          (s :=
            τ (Fin.natAdd m i.succ) -
              t * anchor i.succ)
          (hz i) ht.1 hres)

/-- The same anchor domination restores the right half-plane for the
zero-anchor pairing along the recentered radial path. -/
theorem
    zeroAnchorShiftedStagePoint_tailAnchorCentered_mem_rightHalfPlane
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    {t : ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hτ : ReflectedTimeDominatesTailAnchor anchor τ)
    (hz : z ∈ osiiTimeRightHalfPlane m)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    zeroAnchorShiftedStagePoint τ
        (t • tailAnchorCenteredPoint anchor z) ∈
      osiiTimeRightHalfPlane (m + (m + 1)) := by
  have hτpos := hτ.strictPositive hanchor
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [zeroAnchorShiftedStagePoint_left]
    simpa using hτpos (Fin.castAdd (m + 1) i)
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [zeroAnchorShiftedStagePoint_bridge]
      simpa using hτ.2.1
    · rw [zeroAnchorShiftedStagePoint_tailAnchorCentered_right]
      by_cases ht0 : t = 0
      · subst t
        simpa using hτpos (Fin.natAdd m i.succ)
      · have htpos : 0 < t :=
          lt_of_le_of_ne ht.1 (Ne.symm ht0)
        have hbase :
            0 < (((t : ℂ) * z i).re) := by
          simpa using mul_pos htpos (hz i)
        have hres :
            0 ≤
              τ (Fin.natAdd m i.succ) -
                t * anchor i.succ :=
          tailAnchor_residual_nonnegative
            (hanchor i.succ) (hτ.2.2 i) ht
        simpa using add_pos_of_pos_of_nonneg hbase hres

/-- The zero-anchor pairing obeys the same original-target diagonal bound. -/
theorem
    abs_argumentVector_zeroAnchorShiftedStagePoint_tailAnchorCentered_le
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    {t : ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    (hτ : ReflectedTimeDominatesTailAnchor anchor τ)
    (hz : z ∈ osiiTimeRightHalfPlane m)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j,
      |osiiTimeArgumentVector
          (zeroAnchorShiftedStagePoint τ
            (t • tailAnchorCenteredPoint anchor z)) j| ≤
        |reflectedMixedDiagonal z j| := by
  have hτpos := hτ.strictPositive hanchor
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedMixedDiagonal_left]
    simp only [osiiTimeArgumentVector,
      zeroAnchorShiftedStagePoint_left, abs_neg]
    rw [Complex.arg_ofReal_of_nonneg
      (hτpos (Fin.castAdd (m + 1) i)).le]
    simp
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedMixedDiagonal_bridge]
      simp only [osiiTimeArgumentVector,
        zeroAnchorShiftedStagePoint_bridge, abs_zero]
      rw [Complex.arg_ofReal_of_nonneg hτ.2.1.le]
      simp
    · rw [reflectedMixedDiagonal_right]
      simp only [osiiTimeArgumentVector,
        zeroAnchorShiftedStagePoint_tailAnchorCentered_right]
      have hres :
          0 ≤
            τ (Fin.natAdd m i.succ) -
              t * anchor i.succ :=
        tailAnchor_residual_nonnegative
          (hanchor i.succ) (hτ.2.2 i) ht
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using
        (abs_arg_real_smul_add_ofReal_le
          (z := z i)
          (t := t)
          (s :=
            τ (Fin.natAdd m i.succ) -
              t * anchor i.succ)
          (hz i) ht.1 hres)

namespace TailAnchorRadialTimeRegionData

end TailAnchorRadialTimeRegionData

theorem reflectedChronologicalGapCarrier_dominatesTailAnchor
    {m : ℕ}
    {anchor : Fin (m + 1) → ℝ}
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    {K : Set (Fin (m + 1) → ℝ)}
    (hK_lower : ∀ τ ∈ K, ∀ i, anchor i ≤ τ i) :
    ∀ σ ∈ reflectedChronologicalGapCarrier m K,
      ReflectedTimeDominatesTailAnchor anchor σ := by
  rintro _ ⟨⟨τleft, τright⟩, hτ, rfl⟩
  exact
    reflectedChronologicalGapMap_dominatesTailAnchor
      hanchor (hK_lower τleft hτ.1) (hK_lower τright hτ.2)

end OSIIChapterV
end OSReconstruction
