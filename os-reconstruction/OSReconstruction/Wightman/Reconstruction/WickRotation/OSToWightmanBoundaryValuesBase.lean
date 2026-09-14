/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import OSReconstruction.SCV.LaplaceHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
















open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]
























private def timeReflectionNHomeomorph_local {n : ℕ} :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := timeReflectionN d
  invFun := timeReflectionN d
  left_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  right_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)

/-- Ordered positive-time support forces the OS-conjugated left factor onto the
strict ordered negative-time region, hence away from the coincidence locus. -/
private theorem VanishesToInfiniteOrderOnCoincidence_osConj_of_tsupport_subset_orderedPositiveTimeRegion_local
    {n : ℕ} (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    VanishesToInfiniteOrderOnCoincidence (f.osConj) := by
  have hosConj :
      tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n := by
    intro x hx i
    have hxpre_conj :
        x ∈ tsupport (fun y : NPointDomain d n =>
          starRingEnd ℂ (f (timeReflectionN d y))) := by
      simpa [SchwartzNPoint.osConj_apply] using hx
    have hxpre :
        timeReflectionN d x ∈ tsupport (f : NPointDomain d n → ℂ) := by
      exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
        (f := timeReflectionN d)
        (timeReflectionNHomeomorph_local (d := d) (n := n)).continuous_toFun
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _)
          (fun y : NPointDomain d n => f (timeReflectionN d y))) hxpre_conj)
    have hpos := hf hxpre
    constructor
    · have : 0 < timeReflectionN d x i 0 := (hpos i).1
      simpa [timeReflectionN, timeReflection] using this
    · intro j hij
      have : timeReflectionN d x i 0 < timeReflectionN d x j 0 := (hpos i).2 j hij
      simpa [timeReflectionN, timeReflection] using this
  have hdisj :
      Disjoint
        (tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        (CoincidenceLocus d n) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxsupport hxcoin
    exact
      (not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion
        (hosConj hxsupport)) hxcoin
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint (f := f.osConj) hdisj

/-- Euclidean cluster property specialized to the exact translated single-split
shell appearing in the BV cluster route. This isolates the genuine OS-I
large-spatial input before any boundary-value comparison is applied. -/
theorem schwinger_cluster_osConjTensorProduct_translate_spatial_right_local
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))) -
          OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)) *
            OS.S m (ZeroDiagonalSchwartz.ofClassical g)‖ < ε := by
  let f0 : ZeroDiagonalSchwartz d n := ZeroDiagonalSchwartz.ofClassical (f.osConj)
  let g0 : ZeroDiagonalSchwartz d m := ZeroDiagonalSchwartz.ofClassical g
  intro ε hε
  obtain ⟨R, hR, hcluster⟩ := OS.E4_cluster n m f0 g0 ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  let a0 : SpacetimeDim d := Fin.cons 0 a
  have ha0 : a0 0 = 0 := by simp [a0]
  let g_translated : SchwartzNPoint d m := translateSchwartzNPoint (d := d) a0 g
  have hg_translated_ord :
      tsupport ((g_translated : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a0 ha0 g hg_ord
  have hf0_vanish :
      VanishesToInfiniteOrderOnCoincidence (f.osConj) :=
    VanishesToInfiniteOrderOnCoincidence_osConj_of_tsupport_subset_orderedPositiveTimeRegion_local
      (d := d) f hf_ord
  have hg0_vanish :
      VanishesToInfiniteOrderOnCoincidence g :=
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
      g hg_ord
  have hga_vanish :
      VanishesToInfiniteOrderOnCoincidence g_translated :=
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
      g_translated hg_translated_ord
  let g_a : ZeroDiagonalSchwartz d m := ZeroDiagonalSchwartz.ofClassical g_translated
  have hg_a :
      ∀ x : NPointDomain d m, g_a.1 x = g0.1 (fun i => x i - a0) := by
    intro x
    simp [g_a, g0, g_translated, a0, translateSchwartzNPoint_apply,
      ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes, hg0_vanish, hga_vanish]
  let fg_a : ZeroDiagonalSchwartz d (n + m) := ZeroDiagonalSchwartz.ofClassical
    (f.osConjTensorProduct g_translated)
  have hfg_vanish :
      VanishesToInfiniteOrderOnCoincidence (f.osConjTensorProduct g_translated) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f) (g := g_translated) hf_ord hg_translated_ord
  have hfg_a :
      ∀ x : NPointDomain d (n + m),
        fg_a.1 x = f0.1 (splitFirst n m x) * g_a.1 (splitLast n m x) := by
    intro x
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConjTensorProduct g_translated) hfg_vanish]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConj) hf0_vanish]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := g_translated) hga_vanish]
    simp [g_translated, translateSchwartzNPoint_apply, SchwartzNPoint.osConjTensorProduct]
  simpa [f0, g0, a0] using hcluster a0 ha0 (by simpa [a0] using ha_large) g_a hg_a fg_a hfg_a

