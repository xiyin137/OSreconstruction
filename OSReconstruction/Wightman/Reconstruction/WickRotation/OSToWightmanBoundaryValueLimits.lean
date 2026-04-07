/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison

/-!
# OS to Wightman Boundary Value Limits

This module packages the already-proved OS-side `t → 0+` limits of the
`singleSplit_xiShift` holomorphic traces. The point is to isolate the genuine
remaining gap on the active OS route:

- the positive-real `xiShift` shell already converges to the Euclidean/OS term;
- what still remains is the Wightman-side boundary-value identification, not the
  semigroup-side limit.
-/

open scoped Classical NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem unflatten_add_flatTimeShiftDirection_local {n : ℕ}
    (u : Fin (n * (d + 1)) → ℝ) (t : ℝ) :
    (flattenCLEquivReal n (d + 1)).symm (u + t • flatTimeShiftDirection d n) =
      fun i => ((flattenCLEquivReal n (d + 1)).symm u i) - timeShiftVec d t := by
  ext i μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [sub_eq_add_neg]
  · simp [flatTimeShiftDirection, timeShiftVec, hμ]

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_eq_unflatten_translate_local {n : ℕ}
    (t : ℝ) (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) t f =
      unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (t • flatTimeShiftDirection d n)
          (flattenSchwartzNPoint (d := d) f)) := by
  ext x
  simp [SCV.translateSchwartz_apply, unflatten_add_flatTimeShiftDirection_local]

omit [NeZero d] in
private theorem hasCompactSupport_flattenSchwartzNPoint_local {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    HasCompactSupport
      ((flattenSchwartzNPoint (d := d) f :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
  simpa [flattenSchwartzNPoint] using
    hf.comp_homeomorph ((flattenCLEquivReal n (d + 1)).symm.toHomeomorph)

omit [NeZero d] in
private theorem tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport_local {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : HasCompactSupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t f) (nhds t₀)
      (nhds (timeShiftSchwartzNPoint (d := d) t₀ f)) := by
  let ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f
  have hψ : HasCompactSupport ((ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) :
      (Fin (n * (d + 1)) → ℝ) → ℂ) :=
    hasCompactSupport_flattenSchwartzNPoint_local (d := d) f hf
  have hη : Continuous (fun t : ℝ => t • flatTimeShiftDirection d n) :=
    continuous_id.smul continuous_const
  have hflat_full :
      Filter.Tendsto
        (fun s : Fin (n * (d + 1)) → ℝ => SCV.translateSchwartz s ψ)
        (nhds (t₀ • flatTimeShiftDirection d n))
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ
      (t₀ • flatTimeShiftDirection d n)
  have hflat :
      Filter.Tendsto
        (fun t : ℝ => SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ)
        (nhds t₀)
        (nhds (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ)) :=
    hflat_full.comp (hη.tendsto t₀)
  have hunflat :
      Filter.Tendsto
        (fun t : ℝ =>
          unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t • flatTimeShiftDirection d n) ψ))
        (nhds t₀)
        (nhds
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (t₀ • flatTimeShiftDirection d n) ψ))) :=
    (((unflattenSchwartzNPoint (d := d) :
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n).continuous).tendsto
      _).comp hflat
  simpa [ψ, timeShiftSchwartzNPoint_eq_unflatten_translate_local] using hunflat

/-- Compact-support continuity of the reconstructed Wightman pairing along real
time shifts of the right factor.

This is the exact continuity input needed to turn a positive-real identification
of the chosen `singleSplit_xiShift` holomorphic trace into the current theorem-3
limit hypothesis `hHlimit`. -/
theorem tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g))) := by
  have hshift :
      Filter.Tendsto
        (fun t : ℝ => timeShiftSchwartzNPoint (d := d) t g)
        (nhds 0)
        (nhds g) := by
    have hzeroVec : timeShiftVec d 0 = 0 := by
      ext μ
      refine Fin.cases ?_ ?_ μ
      · simp [timeShiftVec]
      · intro i
        simp [timeShiftVec]
    have hzero : timeShiftSchwartzNPoint (d := d) 0 g = g := by
      ext x
      simp [hzeroVec]
    simpa [hzero] using
      tendsto_timeShiftSchwartzNPoint_nhds_of_isCompactSupport_local (d := d) g hg_compact 0
  have hconj :
      Filter.Tendsto
        (fun t : ℝ => f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
        (nhds 0)
        (nhds (f.conjTensorProduct g)) := by
    exact ((SchwartzMap.conjTensorProduct_continuous_right f).tendsto g).comp hshift
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
        (nhds 0)
        (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g))) := by
    exact ((bvt_W_continuous (d := d) OS lgc (n + m)).tendsto
      (f.conjTensorProduct g)).comp hconj
  exact hW.mono_left nhdsWithin_le_nhds

/-- Zero-translation specialization of the proved Schwinger-side `t → 0+` limit
for the compact ordered positive-time `singleSplit_xiShift` shell.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298

This packages the OS/Schwinger side only; it does not identify the Wightman
boundary value yet. -/
theorem bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct g) y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct g)))) := by
  have ha0_zero : (Fin.cons 0 (0 : Fin d → ℝ) : SpacetimeDim d) = 0 := by
    funext μ
    refine Fin.cases ?_ ?_ μ
    · simp
    · intro i
      simp
  have htranslate_zero :
      translateSchwartzNPoint (d := d) (Fin.cons 0 (0 : Fin d → ℝ)) g = g := by
    ext x
    simp [translateSchwartzNPoint_apply, ha0_zero]
  simpa [htranslate_zero] using
    bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact (0 : Fin d → ℝ)

/-- The OS one-variable holomorphic bridge behind the compact ordered
positive-time `singleSplit_xiShift` shell comes with its boundary limit to the
Euclidean Schwinger tensor term.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter V, pp. 290-297 for the holomorphic continuation machinery
- OS II Chapter VI.1, pp. 297-298 for the current boundary-limit stage

This packages the semigroup-side part of the positivity route as an honest
scalar holomorphic statement. -/
theorem bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y) ∧
      Filter.Tendsto
        (fun t : ℝ => H (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct g)))) := by
  rcases bvt_exists_singleSplit_xiShift_holomorphicValue
      (d := d) OS lgc hm f hf_ord g hg_ord hg_compact with
    ⟨H, hH_holo, hH_real⟩
  refine ⟨H, hH_holo, hH_real, ?_⟩
  have htrace :
      (fun t : ℝ => H (t : ℂ))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hH_real t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
      (d := d) OS lgc n m hm f hf_ord hf_compact g hg_ord hg_compact

/-- Chosen scalar holomorphic trace whose positive-real boundary is the
`singleSplit_xiShift` shell for compact ordered positive-time data.

OS paper target:
- OS II Theorem 4.3, p. 289
- OS II Chapter V, pp. 290-297

This is a production wrapper around the already-proved OS-side holomorphic
matrix element. -/
noncomputable def bvt_singleSplit_xiShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) : ℂ → ℂ :=
  Classical.choose <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact

theorem differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    DifferentiableOn ℂ
      (bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
      {z : ℂ | 0 < z.re} :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).1

theorem bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).2.1 t ht

/-- On positive real times, the chosen scalar holomorphic `singleSplit_xiShift`
trace is exactly the Schwinger value of the right time-shifted simple tensor. -/
theorem bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  calc
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y :=
      bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
        (d := d) (OS := OS) (lgc := lgc) hm
        f hf_ord hf_compact g hg_ord hg_compact t ht
    _ =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
      symm
      exact schwinger_simpleTensor_timeShift_eq_xiShift
        (d := d) (OS := OS) (hm := hm) (Ψ := bvt_F OS lgc (n + m))
        (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
        (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct g)))) :=
  (Classical.choose_spec <|
    bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact).2.2

/-- If the positive-real Schwinger values of the chosen `singleSplit_xiShift`
trace are already identified with the reconstructed Wightman pairing against the
right-time-shifted test function, then the current theorem-3 limit hypothesis
follows immediately. -/
/-
Deprecated route note:

The hypothesis `hschw` below is mathematically false on the intended theorem
surface. The left-hand side is the Euclidean/OS time-shifted Schwinger pairing,
whose free-field momentum-space form carries a Laplace factor `e^{-ω_p t}` and
Laplace-transformed test functions. The right-hand side is the reconstructed
Wightman boundary-value pairing against a real Minkowski time translation,
whose free-field momentum-space form carries the oscillatory factor
`e^{-i ω_p t}` and the Fourier-transformed test functions.

So this theorem remains a logically valid implication from a false premise, but
it is dead-end infrastructure and not part of the endorsed theorem-3 route. -/
theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hschw :
      ∀ t : ℝ, 0 < t →
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
          =
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (f.conjTensorProduct g))) := by
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
        =
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :=
        bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
          (d := d) (OS := OS) (lgc := lgc) hm
          f hf_ord hf_compact g hg_ord hg_compact t ht
      _ =
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) :=
        hschw t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (OS := OS) (lgc := lgc) f g hg_compact

/-- If the chosen scalar holomorphic `singleSplit_xiShift` trace agrees on the
positive real axis with the reconstructed Wightman pairing against the
right-time-shifted test function, then its `t → 0+` limit is exactly the
theorem-3 boundary-value target.

This turns the current abstract compact-shell hypothesis `hHlimit` into the
more concrete OS-route task of identifying positive real Euclidean time shifts
with the corresponding Wightman pairing. -/
theorem tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) :
    Filter.Tendsto
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (f.conjTensorProduct g))) := by
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  exact Filter.Tendsto.congr' htrace.symm <|
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (OS := OS) (lgc := lgc) f g hg_compact

/-- On the right half-plane, a holomorphic scalar trace is determined by its
positive-real values.

OS paper role:
- auxiliary uniqueness principle for the OS II theorem-3 lane
- used to keep the remaining gap in the shape "construct the Wightman-side
  holomorphic realization with the same positive-real values"

This is not itself quoted as a numbered OS theorem; it is a local analytic
uniqueness lemma used to keep the production theorem surface honest. -/
theorem eqOn_rightHalfPlane_of_ofReal_eq
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hreal : ∀ t : ℝ, 0 < t → H₀ (t : ℂ) = H₁ (t : ℂ)) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hpos : 0 < 1 + ε := by linarith
    exact hV_sub ⟨hz_in_V, hz_ne⟩ (hreal (1 + ε) hpos)
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Any holomorphic realization of the positive-real `singleSplit_xiShift`
shell must agree with the chosen scalar trace on the full right half-plane. -/
theorem bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real : ∀ t : ℝ, 0 < t →
      H (t : ℂ) =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) :
    Set.EqOn H
      (bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
      {z : ℂ | 0 < z.re} := by
  exact eqOn_rightHalfPlane_of_ofReal_eq H
    (bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
    hH_holo
    (differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
    (fun t ht => by
      rw [hH_real t ht,
        bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
          (d := d) (OS := OS) (lgc := lgc) hm f hf_ord hf_compact g hg_ord hg_compact t ht])

/-- Positivity comparison on compact ordered positive-time Borchers vectors,
restated so that the remaining theorem-3 seam is the Wightman boundary value of
the chosen scalar holomorphic `singleSplit_xiShift` trace rather than a raw
integral net.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current boundary-value substep -/
theorem bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((G : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((G : BorchersSequence d).funcs 0)))))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((G : BorchersSequence d).funcs m))
              (G.ordered_tsupport m)
              (hG_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((G : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d) (G : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  apply
    bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) F G hF_compact hG_compact hzero
  intro n m hm
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n)
          (hF_compact n)
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m)
          (hG_compact m) (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((G : BorchersSequence d).funcs m)) y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n)
      (hF_compact n)
      (((G : BorchersSequence d).funcs m))
      (G.ordered_tsupport m)
      (hG_compact m) t ht
  exact Filter.Tendsto.congr' htrace (hHlimit n m hm)

/-- In the self-pair case, the same chosen scalar holomorphic trace already
reduces positivity to OS reflection positivity.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II IV.2, p. 288
- current substep on the active route: OS II Chapter VI.1, pp. 297-298

This is the sharpened theorem-3 surface: the remaining gap is the Wightman
boundary value of that scalar trace, not any semigroup-side continuity
statement. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)))))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  rw [bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (d := d) (OS := OS) (lgc := lgc) F F hF_compact hF_compact hzero hHlimit]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-- The same theorem-3 positivity reduction, with the degree-`0` repair
internalized via Hermiticity of the reconstructed boundary values.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current boundary-value substep

This is a real blocker shrink on the active OS route: after the OS/Schwinger
limit is packaged for the chosen holomorphic trace, the only remaining exposed
input is the Wightman-side boundary-value identification `hHlimit`. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  apply
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) hherm F hF_compact
  intro n m hm
  have htrace :
      (fun t : ℝ =>
        bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n)
          (hF_compact n)
          (((F : BorchersSequence d).funcs m))
          (F.ordered_tsupport m)
          (hF_compact m) (t : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs m)) y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n)
      (hF_compact n)
      (((F : BorchersSequence d).funcs m))
      (F.ordered_tsupport m)
      (hF_compact m) t ht
  exact Filter.Tendsto.congr' htrace (hHlimit n m hm)
