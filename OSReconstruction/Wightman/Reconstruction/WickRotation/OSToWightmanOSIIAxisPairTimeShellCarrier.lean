import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPairTotalBranch

/-!
# OS-II Axis-Pair Time-Shell Carrier

This companion extracts the log-carrier consequence of the general-`d`
axis-pair Lemma 5.1 estimate in corrected time-shell coordinates.  It is used
when returning the weighted Malgrange-Zerner branch from logarithmic
coefficients to the finite semigroup-time side kernel.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- A small complex time-shell window keeps all axis-pair logarithmic
coefficients nonzero. -/
theorem osiiAxisPair_exists_timeShellComplexWindow_coeff_ne
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ τ : Fin (d + 1) → ℂ,
        τ ∈ osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ →
          ∀ a : osiiAxisPairIndex d,
            osiiAxisPairCoeffMap T ξ
              (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a ≠ 0 := by
  classical
  rcases
    osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρ, hρ, hcoeff_pos⟩
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ a hzero
  have hpos :
      0 <
        (osiiAxisPairCoeff T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a).re :=
    hcoeff_pos
      (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ)
      hτ a
  have hzero_re :
      (osiiAxisPairCoeff T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a).re = 0 := by
    simpa [osiiAxisPairCoeffMap] using congrArg Complex.re hzero
  rw [hzero_re] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- On a sufficiently small complex time-shell window, the corrected axis-pair
MZ branch is the finite-height one-variable semigroup side kernel.  This is the
carrier-discharged form of the side-kernel identity used in the local EOW
boundary integrals. -/
theorem osiiAxisPair_complexWindow_weightedTimeShellBranch_realImag_eq_semigroup_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x y : Fin (d + 1) → ℝ,
        (fun ν : Fin (d + 1) =>
          (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) ∈
            osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ →
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) =>
              (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            ((x 0 : ℂ) + ((y 0 : ℝ) : ℂ) * Complex.I) := by
  classical
  rcases
    osiiAxisPair_exists_timeShellComplexWindow_coeff_ne
      (d := d) T hT ξ hξ0 with
    ⟨ρ, hρ, hcoeff⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x y hxy
  exact
    osiiAxisPairWeightedTimeShellBranch_realImag_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T (ne_of_gt hT) ξ x y
      (hcoeff
        (fun ν : Fin (d + 1) =>
          (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)
        hxy)

/-- Real shifted side-kernel form: inside a small real time-shell carrier, the
shifted corrected axis-pair branch is the OS semigroup kernel at the shifted
real total time. -/
theorem osiiAxisPair_realWindow_shiftedTimeShellBranch_eq_semigroup_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ τ : Fin (d + 1) → ℝ, ∀ η : ℝ,
        (fun ν : Fin (d + 1) =>
          if ν = 0 then τ 0 + η else τ ν) ∈
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) =>
              ((if ν = 0 then τ 0 + η else τ ν : ℝ) : ℂ)) =
          OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            (((τ 0 + η : ℝ) : ℂ)) := by
  classical
  rcases
    osiiAxisPair_complexWindow_weightedTimeShellBranch_realImag_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T hT ξ hξ0 with
    ⟨ρ, hρ, hbranch⟩
  refine ⟨ρ, hρ, ?_⟩
  intro τ η hτ
  let x : Fin (d + 1) → ℝ := fun ν =>
    if ν = 0 then τ 0 + η else τ ν
  have hx_window :
      (fun ν : Fin (d + 1) =>
        (x ν : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) ∈
          osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ := by
    simpa [x, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  simpa [x] using hbranch x (fun _ : Fin (d + 1) => 0) hx_window

/-- Support-local transport from a side semigroup kernel to the shifted
axis-pair branch.

The side displacement is kept as an explicit scalar function `η` of the side
height.  Positive side uses `η y = y 0`; lower side uses `η y = -y 0`.  The
only geometric input is eventual membership of the shifted real support in the
carrier window. -/
theorem osiiAxisPair_eventually_side_semigroup_eq_shiftedBranch_of_shift_window
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (η : (Fin (d + 1) → ℝ) → ℝ)
    (Fside : (Fin (d + 1) → ℂ) → ℂ)
    (F : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (l : Filter (Fin (d + 1) → ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ᶠ y in l,
        ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          Fside (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
            OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)
              (((τ 0 + η y : ℝ) : ℂ))) →
      (∀ᶠ y in l,
        ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          (fun ν : Fin (d + 1) =>
            if ν = 0 then τ 0 + η y else τ ν) ∈
              osiiAxisPairTimeShellWindow (d := d) ξ ρ) →
      (∀ᶠ y in l,
        ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          Fside (fun ν : Fin (d + 1) =>
              (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + η y else τ ν : ℝ) : ℂ)))) := by
  classical
  rcases
    osiiAxisPair_realWindow_shiftedTimeShellBranch_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T hT ξ hξ0 with
    ⟨ρ, hρ, hbranch⟩
  refine ⟨ρ, hρ, ?_⟩
  intro hsem hwin
  filter_upwards [hsem, hwin] with y hysem hywin τ hτ
  calc
    Fside (fun ν : Fin (d + 1) =>
        (τ ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)
        =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (((τ 0 + η y : ℝ) : ℂ)) := hysem τ hτ
    _ =
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T ξ
        (fun ν : Fin (d + 1) =>
          ((if ν = 0 then τ 0 + η y else τ ν : ℝ) : ℂ)) :=
        (hbranch τ (η y) (hywin τ hτ)).symm

end OSReconstruction
