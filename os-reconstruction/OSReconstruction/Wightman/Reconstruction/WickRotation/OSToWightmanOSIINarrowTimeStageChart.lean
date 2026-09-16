/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapTimeStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter

/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

def osiiPureTimeComplex (z : ℂ) : Fin (d + 1) → ℂ :=
  Fin.cases z (fun _ => 0)

def osiiPureTimeReal (t : ℝ) : SpacetimeDim d :=
  Fin.cases t (fun _ => 0)

/-- The common positive scale appearing in every axis-pair coefficient of the
pure-time chart. -/
def osiiNarrowTimeLogScale (T : ℝ) : ℝ :=
  2 * (d : ℝ) * T

theorem osiiNarrowTimeLogScale_pos
    (T : ℝ) (hT : 0 < T) :
    0 < osiiNarrowTimeLogScale (d := d) T := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [osiiNarrowTimeLogScale]
  positivity

def osiiNarrowTimeCarrier (η : ℝ) :
    Set (OSIITimeGapSpace k) :=
  {ζ | ∀ i : Fin k, 0 < (ζ i).re ∧ |(ζ i).im| < η * (ζ i).re}

theorem isOpen_osiiNarrowTimeCarrier (η : ℝ) :
    IsOpen (osiiNarrowTimeCarrier (k := k) η) := by
  rw [show osiiNarrowTimeCarrier (k := k) η =
      ⋂ i : Fin k,
        {ζ : OSIITimeGapSpace k |
          0 < (ζ i).re ∧ |(ζ i).im| < η * (ζ i).re} by
    ext ζ
    simp [osiiNarrowTimeCarrier]]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_apply i))).inter
      (isOpen_lt
        ((Complex.continuous_im.comp (continuous_apply i)).abs)
        (continuous_const.mul
          (Complex.continuous_re.comp (continuous_apply i))))

/-- The common narrow pure-time carrier is convex. -/
theorem convex_osiiNarrowTimeCarrier (η : ℝ) :
    Convex ℝ (osiiNarrowTimeCarrier (k := k) η) := by
  intro ζ hζ ξ hξ a b ha hb hab
  intro i
  have hcoeff_pos : 0 < a ∨ 0 < b := by
    by_cases ha0 : a = 0
    · right
      linarith
    · left
      exact lt_of_le_of_ne ha (Ne.symm ha0)
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  constructor
  · rcases hcoeff_pos with ha_pos | hb_pos
    · exact
        add_pos_of_pos_of_nonneg
          (mul_pos ha_pos (hζ i).1)
          (mul_nonneg hb (le_of_lt (hξ i).1))
    · exact
        add_pos_of_nonneg_of_pos
          (mul_nonneg ha (le_of_lt (hζ i).1))
          (mul_pos hb_pos (hξ i).1)
  · calc
      |a * (ζ i).im + b * (ξ i).im|
          ≤ a * |(ζ i).im| + b * |(ξ i).im| := by
            simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
              abs_add_le (a * (ζ i).im) (b * (ξ i).im)
      _ < a * (η * (ζ i).re) + b * (η * (ξ i).re) := by
        rcases hcoeff_pos with ha_pos | hb_pos
        · exact
            add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left (hζ i).2 ha_pos)
              (mul_le_mul_of_nonneg_left (le_of_lt (hξ i).2) hb)
        · exact
            add_lt_add_of_le_of_lt
              (mul_le_mul_of_nonneg_left (le_of_lt (hζ i).2) ha)
              (mul_lt_mul_of_pos_left (hξ i).2 hb_pos)
      _ = η * (a * (ζ i).re + b * (ξ i).re) := by ring

/-- A positive-width narrow carrier is connected. -/
theorem isConnected_osiiNarrowTimeCarrier
    (η : ℝ) (hη : 0 < η) :
    IsConnected (osiiNarrowTimeCarrier (k := k) η) := by
  apply (convex_osiiNarrowTimeCarrier (k := k) η).isConnected
  refine ⟨fun _ => 1, ?_⟩
  intro i
  simp [hη]

theorem osiiAxisPairCoeffMap_pureTime_apply
    (T : ℝ) (z : ℂ) (a : osiiAxisPairIndex d) :
    osiiAxisPairCoeffMap T (fun _ => 0)
        (osiiPureTimeComplex (d := d) z) a =
      z / ((osiiNarrowTimeLogScale (d := d) T : ℝ) : ℂ) := by
  rcases a with ⟨j, b⟩
  cases b <;>
    simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff,
      osiiPureTimeComplex, osiiNarrowTimeLogScale]

theorem osiiAxisPairCoeffMap_pureTime_mem_narrowSector
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (z : ℂ)
    (hz : 0 < z.re ∧ |z.im| < η * z.re) :
    osiiAxisPairCoeffMap T (fun _ => 0)
        (osiiPureTimeComplex (d := d) z) ∈
      osiiAxisPairNarrowSector (d := d) η := by
  intro a
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hc : 0 < 2 * (d : ℝ) * T := by positivity
  have hcoeff :
      osiiAxisPairCoeffMap T (fun _ => 0)
          (osiiPureTimeComplex (d := d) z) a =
        z / ((2 * (d : ℝ) * T : ℝ) : ℂ) := by
    simpa [osiiNarrowTimeLogScale] using
      osiiAxisPairCoeffMap_pureTime_apply (d := d) T z a
  rw [hcoeff]
  have hre :
      (z / ((2 * (d : ℝ) * T : ℝ) : ℂ)).re =
        z.re / (2 * (d : ℝ) * T) := by
    simpa using Complex.div_ofReal_re z (2 * (d : ℝ) * T)
  have him :
      (z / ((2 * (d : ℝ) * T : ℝ) : ℂ)).im =
        z.im / (2 * (d : ℝ) * T) := by
    simpa using Complex.div_ofReal_im z (2 * (d : ℝ) * T)
  rw [hre, him]
  constructor
  · exact div_pos hz.1 hc
  · rw [abs_div, abs_of_pos hc]
    have hdiv :=
      div_lt_div_of_pos_right hz.2 hc
    convert hdiv using 1
    · rfl
    · ring

def osiiNarrowTimeLogCoordinate
    (T : ℝ)
    (ζ : OSIITimeGapSpace k) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i =>
    osiiAxisPairLogCoeffMap T (fun _ => 0)
      (osiiPureTimeComplex (d := d) (ζ i))

theorem osiiNarrowTimeLogCoordinate_apply
    (T : ℝ)
    (ζ : OSIITimeGapSpace k)
    (i : Fin k)
    (a : osiiAxisPairIndex d) :
    osiiNarrowTimeLogCoordinate (d := d) T ζ i a =
      Complex.log
        (ζ i / ((osiiNarrowTimeLogScale (d := d) T : ℝ) : ℂ)) := by
  rw [osiiNarrowTimeLogCoordinate, osiiAxisPairLogCoeffMap,
    osiiAxisPairCoeffMap_pureTime_apply]

/-- Recenter the moving logarithmic chart by its common positive scale.  The
point of this coordinate is that its value on the narrow carrier is
independent of both the packet slope and the axis-pair index. -/
def osiiNarrowTimeCenteredLogCoordinate
    (T : ℝ)
    (ζ : OSIITimeGapSpace k) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i a =>
    osiiNarrowTimeLogCoordinate (d := d) T ζ i a +
      (Real.log (osiiNarrowTimeLogScale (d := d) T) : ℂ)

/-- The intrinsic logarithmic coordinate of a pure-time gap tuple.  Repeating
the same value in every axis-pair slot makes its codomain agree with the MZ
chart while removing the auxiliary slope altogether. -/
def osiiNarrowTimeIntrinsicLogCoordinate
    (ζ : OSIITimeGapSpace k) :
    Fin k → osiiAxisPairIndex d → ℂ :=
  fun i _a => Complex.log (ζ i)

theorem osiiNarrowTimeCenteredLogCoordinate_apply
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η)
    (i : Fin k)
    (a : osiiAxisPairIndex d) :
    osiiNarrowTimeCenteredLogCoordinate (d := d) T ζ i a =
      Complex.log (ζ i) := by
  let scale := osiiNarrowTimeLogScale (d := d) T
  have hscale : 0 < scale :=
    osiiNarrowTimeLogScale_pos (d := d) T hT
  have hscale_ne : (scale : ℂ) ≠ 0 := by
    exact_mod_cast hscale.ne'
  have hζi_ne : ζ i ≠ 0 := by
    intro hzero
    have hpos := (hζ i).1
    rw [hzero] at hpos
    simp at hpos
  have hquot_ne : ζ i / (scale : ℂ) ≠ 0 :=
    div_ne_zero hζi_ne hscale_ne
  have hlog :=
    Complex.log_ofReal_mul hscale hquot_ne
  rw [osiiNarrowTimeCenteredLogCoordinate,
    osiiNarrowTimeLogCoordinate_apply]
  change
    Complex.log (ζ i / (scale : ℂ)) + (Real.log scale : ℂ) =
      Complex.log (ζ i)
  calc
    Complex.log (ζ i / (scale : ℂ)) + (Real.log scale : ℂ) =
        (Real.log scale : ℂ) + Complex.log (ζ i / (scale : ℂ)) := add_comm _ _
    _ = Complex.log ((scale : ℂ) * (ζ i / (scale : ℂ))) := hlog.symm
    _ = Complex.log (ζ i) := by rw [mul_div_cancel₀ _ hscale_ne]

theorem osiiNarrowTimeCenteredLogCoordinate_eq_intrinsic
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η) :
    osiiNarrowTimeCenteredLogCoordinate (d := d) T ζ =
      osiiNarrowTimeIntrinsicLogCoordinate (d := d) ζ := by
  funext i a
  exact osiiNarrowTimeCenteredLogCoordinate_apply
    (d := d) T hT η ζ hζ i a

theorem osiiNarrowTimeCenteredLogCoordinate_eq_of_pos
    (T U : ℝ) (hT : 0 < T) (hU : 0 < U)
    (η : ℝ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η) :
    osiiNarrowTimeCenteredLogCoordinate (d := d) T ζ =
      osiiNarrowTimeCenteredLogCoordinate (d := d) U ζ := by
  rw [
    osiiNarrowTimeCenteredLogCoordinate_eq_intrinsic
      (d := d) T hT η ζ hζ,
    osiiNarrowTimeCenteredLogCoordinate_eq_intrinsic
      (d := d) U hU η ζ hζ]

theorem differentiableOn_osiiNarrowTimeLogCoordinate
    (T : ℝ) (hT : 0 < T)
    (η : ℝ) :
    DifferentiableOn ℂ
      (osiiNarrowTimeLogCoordinate (d := d) T)
      (osiiNarrowTimeCarrier (k := k) η) := by
  rw [differentiableOn_pi]
  intro i
  rw [differentiableOn_pi]
  intro a ζ hζ
  have hcoeff :=
    osiiAxisPairCoeffMap_pureTime_mem_narrowSector
      (d := d) T hT η (ζ i) (hζ i) a
  have hslit :
      osiiAxisPairCoeffMap T (fun _ => 0)
          (osiiPureTimeComplex (d := d) (ζ i)) a ∈
        Complex.slitPlane := by
    simp [Complex.slitPlane]
    exact Or.inl hcoeff.1
  have hinner :
      Differentiable ℂ
        (fun w : OSIITimeGapSpace k =>
          osiiAxisPairCoeffMap T (fun _ => 0)
            (osiiPureTimeComplex (d := d) (w i)) a) := by
    rcases a with ⟨j, b⟩
    cases b <;>
      simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff,
        osiiPureTimeComplex] <;>
      fun_prop
  change DifferentiableWithinAt ℂ
    (Complex.log ∘ fun w : OSIITimeGapSpace k =>
      osiiAxisPairCoeffMap T (fun _ => 0)
        (osiiPureTimeComplex (d := d) (w i)) a)
    (osiiNarrowTimeCarrier (k := k) η) ζ
  exact
    (Complex.differentiableAt_log hslit).comp_differentiableWithinAt
      ζ hinner.differentiableAt.differentiableWithinAt

theorem differentiableOn_osiiNarrowTimeCenteredLogCoordinate
    (T : ℝ) (hT : 0 < T)
    (η : ℝ) :
    DifferentiableOn ℂ
      (osiiNarrowTimeCenteredLogCoordinate (d := d) T)
      (osiiNarrowTimeCarrier (k := k) η) := by
  have hcoordinate :=
    differentiableOn_osiiNarrowTimeLogCoordinate
      (d := d) (k := k) T hT η
  rw [differentiableOn_pi] at hcoordinate ⊢
  intro i
  have hi := hcoordinate i
  rw [differentiableOn_pi] at hi ⊢
  intro a ζ hζ
  simpa [osiiNarrowTimeCenteredLogCoordinate] using
    (hi a ζ hζ).add_const
      (Real.log (osiiNarrowTimeLogScale (d := d) T) : ℂ)

theorem isCompact_osiiNarrowTimeCenteredLogCoordinate_image
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (K : Set (OSIITimeGapSpace k))
    (hK : IsCompact K)
    (hKcarrier : K ⊆ osiiNarrowTimeCarrier (k := k) η) :
    IsCompact
      (osiiNarrowTimeCenteredLogCoordinate (d := d) T '' K) := by
  exact hK.image_of_continuousOn
    ((differentiableOn_osiiNarrowTimeCenteredLogCoordinate
      (d := d) (k := k) T hT η).continuousOn.mono hKcarrier)

theorem osiiNarrowTimeLogCoordinate_mapsTo
    [NeZero k]
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    Set.MapsTo
      (osiiNarrowTimeLogCoordinate (d := d) T)
      (osiiNarrowTimeCarrier (k := k) η)
      (osiiAxisPairMultiGapLogDomain d k) := by
  intro ζ hζ
  have harg :
      ∀ i : Fin k, ∀ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiAxisPairCoeffMap T (fun _ => 0)
            (osiiPureTimeComplex (d := d) (ζ i)) a)| <
          Real.arctan η := by
    intro i a
    have hsector :=
      osiiAxisPairCoeffMap_pureTime_mem_narrowSector
        (d := d) T hT η (ζ i) (hζ i) a
    have hratio :
        |(osiiAxisPairCoeffMap T (fun _ => 0)
            (osiiPureTimeComplex (d := d) (ζ i)) a).im /
          (osiiAxisPairCoeffMap T (fun _ => 0)
            (osiiPureTimeComplex (d := d) (ζ i)) a).re| < η := by
      rw [abs_div, abs_of_pos hsector.1]
      exact (div_lt_iff₀ hsector.1).2 hsector.2
    rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hsector.1]
    exact Real.arctan_strictMono hratio
  have hk_nonempty : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  have ha_nonempty :
      (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty := by
    exact
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true),
        Finset.mem_univ _⟩
  simp only [osiiAxisPairMultiGapLogDomain, Set.mem_setOf_eq,
    osiiNarrowTimeLogCoordinate, osiiAxisPairLogCoeffMap,
    Complex.log_im]
  calc
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiAxisPairCoeffMap T (fun _ => 0)
            (osiiPureTimeComplex (d := d) (ζ i)) a)|)
        <
      ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d,
        Real.arctan η :=
      Finset.sum_lt_sum_of_nonempty hk_nonempty fun i _ =>
        Finset.sum_lt_sum_of_nonempty ha_nonempty fun a _ =>
          harg i a
    _ =
        (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η := by
      simp
      ring
    _ < Real.pi / 2 := hηsum

noncomputable def osiiNarrowTimeStageChart
    [NeZero k]
    (T : ℝ) (hT : 0 < T)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    OSIIMultiGapTimeStageChart d k k where
  carrier := osiiNarrowTimeCarrier η
  carrier_open := isOpen_osiiNarrowTimeCarrier η
  coordinate := osiiNarrowTimeLogCoordinate T
  coordinate_differentiable :=
    differentiableOn_osiiNarrowTimeLogCoordinate T hT η
  coordinate_mapsTo :=
    osiiNarrowTimeLogCoordinate_mapsTo T hT η hηsum

theorem osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
    (η : ℝ) (hη : 0 < η)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k) :
    osiiPositiveRealTimeEmbed τ ∈
      osiiNarrowTimeCarrier (k := k) η := by
  intro i
  constructor
  · simpa [osiiPositiveRealTimeEmbed] using hτ i
  · simp [osiiPositiveRealTimeEmbed]
    exact mul_pos hη (hτ i)

def osiiNarrowTimeRealCoordinate
    (T : ℝ)
    (τ : Fin k → ℝ) :
    Fin k → osiiAxisPairIndex d → ℝ :=
  fun i a =>
    Real.log
      (osiiAxisPairCoeffMap T (fun _ => 0)
        (fun ν => (osiiPureTimeReal (d := d) (τ i) ν : ℂ)) a).re

theorem osiiNarrowTimeLogCoordinate_real
    (T : ℝ) (hT : 0 < T)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k) :
    osiiNarrowTimeLogCoordinate (d := d) T
        (osiiPositiveRealTimeEmbed τ) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiNarrowTimeRealCoordinate (d := d) T τ) := by
  funext i
  have hpure :
      osiiPureTimeComplex (d := d)
          (osiiPositiveRealTimeEmbed τ i) =
        fun ν => (osiiPureTimeReal (d := d) (τ i) ν : ℂ) := by
    funext ν
    refine Fin.cases ?_ ?_ ν
    · simp [osiiPureTimeComplex, osiiPureTimeReal,
        osiiPositiveRealTimeEmbed]
    · intro j
      simp [osiiPureTimeComplex, osiiPureTimeReal]
  rw [osiiNarrowTimeLogCoordinate, hpure]
  apply osiiAxisPairLogCoeffMap_real_eq_embed
  intro a
  have hsector :=
    osiiAxisPairCoeffMap_pureTime_mem_narrowSector
      (d := d) T hT 1 (τ i : ℂ)
      (by
        constructor
        · simpa using hτ i
        · simp
          exact hτ i) a
  rw [← hpure]
  exact hsector.1

theorem osiiNarrowTimeRealCoordinate_gapTranslation
    (T : ℝ) (hT : 0 < T)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (i : Fin k) :
    osiiAxisPairChronologicalGapTranslation T
        (osiiNarrowTimeRealCoordinate (d := d) T τ) i =
      osiiPureTimeReal (d := d) (τ i) := by
  rw [osiiAxisPairChronologicalGapTranslation]
  have hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T (fun _ => 0)
          (fun ν => (osiiPureTimeReal (d := d) (τ i) ν : ℂ)) a).re := by
    intro a
    have hsector :=
      osiiAxisPairCoeffMap_pureTime_mem_narrowSector
        (d := d) T hT 1 (τ i : ℂ)
        (by
          constructor
          · simpa using hτ i
          · simp
            exact hτ i) a
    have hpure :
        osiiPureTimeComplex (d := d) (τ i : ℂ) =
          fun ν => (osiiPureTimeReal (d := d) (τ i) ν : ℂ) := by
      funext ν
      refine Fin.cases ?_ ?_ ν
      · simp [osiiPureTimeComplex, osiiPureTimeReal]
      · intro j
        simp [osiiPureTimeComplex, osiiPureTimeReal]
    rw [← hpure]
    exact hsector.1
  calc
    (∑ a : osiiAxisPairIndex d,
        osiiAxisPairPositiveCoefficients
            (osiiNarrowTimeRealCoordinate (d := d) T τ i) a •
          osiiAxisPairDir (d := d) T a) =
        ∑ a : osiiAxisPairIndex d,
          (osiiAxisPairCoeffMap T (fun _ => 0)
            (fun ν =>
              (osiiPureTimeReal (d := d) (τ i) ν : ℂ)) a).re •
            osiiAxisPairDir (d := d) T a := by
          apply Finset.sum_congr rfl
          intro a _ha
          congr 1
          simp [osiiAxisPairPositiveCoefficients,
            osiiNarrowTimeRealCoordinate,
            Real.exp_log (hcoeff_pos a)]
    _ = osiiAxisPairPhysicalShift (fun _ => 0)
          (osiiPureTimeReal (d := d) (τ i)) :=
      osiiAxisPairCoeffMap_real_sum_smul_dir
        (d := d) T (ne_of_gt hT) (fun _ => 0)
          (osiiPureTimeReal (d := d) (τ i))
    _ = osiiPureTimeReal (d := d) (τ i) := by
      funext ν
      refine Fin.cases ?_ ?_ ν
      · simp [osiiAxisPairPhysicalShift, osiiPureTimeReal]
      · intro j
        simp [osiiAxisPairPhysicalShift, osiiPureTimeReal]

end OSReconstruction
