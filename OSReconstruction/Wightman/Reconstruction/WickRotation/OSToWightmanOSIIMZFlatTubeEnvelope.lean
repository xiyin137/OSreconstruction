/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZLogDomain
import OSReconstruction.SCV.TubeDomainExtension

/-!
# OS II Malgrange-Zerner Flat-Tube Envelope

OS II V.1 constructs one-variable continuations on flat log tubes and then uses
Malgrange-Zerner on the convex envelope of their union.  In imaginary
coordinates, that envelope is the `l1` ball `sum_q |t_q| < alpha`.

This file proves the neutral convex-geometry identification.  It does not
assert the analytic Malgrange-Zerner theorem; it supplies the domain geometry
that theorem consumes.
-/

noncomputable section

open Topology
open scoped Classical BigOperators

namespace OSReconstruction

/-- One imaginary-coordinate flat tube: only coordinate `q` is allowed to have
imaginary part, and that part lies in `(-alpha, alpha)`. -/
def osiiMZFlatImaginary (m : ℕ) (alpha : ℝ) (q : Fin m) :
    Set (Fin m → ℝ) :=
  {t | |t q| < alpha ∧ ∀ p : Fin m, p ≠ q → t p = 0}

/-- The union of all one-coordinate flat tubes in imaginary log coordinates. -/
def osiiMZFlatImaginaryUnion (m : ℕ) (alpha : ℝ) : Set (Fin m → ℝ) :=
  ⋃ q : Fin m, osiiMZFlatImaginary m alpha q

/-- The OS-II Malgrange-Zerner convex-envelope imaginary domain. -/
def osiiMZImaginaryL1Domain (m : ℕ) (alpha : ℝ) : Set (Fin m → ℝ) :=
  {t | ∑ q : Fin m, |t q| < alpha}

/-- The corresponding complex flat-tube union in OS-II log variables. -/
def osiiMZFlatLogTubeUnion (m : ℕ) (alpha : ℝ) : Set (Fin m → ℂ) :=
  {z | ∃ q : Fin m, |(z q).im| < alpha ∧ ∀ p : Fin m, p ≠ q → (z p).im = 0}

theorem mem_osiiMZFlatLogTubeUnion_iff
    {m : ℕ} {alpha : ℝ} {z : Fin m → ℂ} :
    z ∈ osiiMZFlatLogTubeUnion m alpha ↔
      (fun q : Fin m => (z q).im) ∈ osiiMZFlatImaginaryUnion m alpha := by
  simp [osiiMZFlatLogTubeUnion, osiiMZFlatImaginaryUnion, osiiMZFlatImaginary]

theorem tubeDomain_flatImaginaryUnion_eq_flatLogTubeUnion
    (m : ℕ) (alpha : ℝ) :
    SCV.TubeDomain (osiiMZFlatImaginaryUnion m alpha) =
      osiiMZFlatLogTubeUnion m alpha := by
  ext z
  simpa [SCV.TubeDomain] using
    (mem_osiiMZFlatLogTubeUnion_iff (m := m) (alpha := alpha) (z := z)).symm

theorem mem_osiiMZLogDomain_iff_mem_tube_l1
    {m : ℕ} {alpha : ℝ} {z : Fin m → ℂ} :
    z ∈ osiiMZLogDomain m alpha ↔
      z ∈ SCV.TubeDomain (osiiMZImaginaryL1Domain m alpha) := by
  rfl

theorem tubeDomain_l1Domain_eq_osiiMZLogDomain
    (m : ℕ) (alpha : ℝ) :
    SCV.TubeDomain (osiiMZImaginaryL1Domain m alpha) =
      osiiMZLogDomain m alpha := by
  rfl

theorem isOpen_osiiMZImaginaryL1Domain (m : ℕ) (alpha : ℝ) :
    IsOpen (osiiMZImaginaryL1Domain m alpha) := by
  have hcont : Continuous fun t : Fin m → ℝ => ∑ q : Fin m, |t q| := by
    exact continuous_finset_sum _ fun q _ => (continuous_apply q).abs
  simpa [osiiMZImaginaryL1Domain] using isOpen_lt hcont continuous_const

theorem convex_osiiMZImaginaryL1Domain (m : ℕ) (alpha : ℝ) :
    Convex ℝ (osiiMZImaginaryL1Domain m alpha) := by
  intro z hz w hw a b ha hb hab
  simp only [osiiMZImaginaryL1Domain, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint : ∀ q : Fin m,
      |((a • z + b • w) q)| ≤ a * |z q| + b * |w q| := by
    intro q
    calc
      |((a • z + b • w) q)|
          = |a * z q + b * w q| := by simp [Pi.smul_apply]
      _ ≤ |a * z q| + |b * w q| := abs_add_le _ _
      _ = a * |z q| + b * |w q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum_le :
      (∑ q : Fin m, |((a • z + b • w) q)|) ≤
        a * (∑ q : Fin m, |z q|) + b * (∑ q : Fin m, |w q|) := by
    calc
      (∑ q : Fin m, |((a • z + b • w) q)|)
          ≤ ∑ q : Fin m, (a * |z q| + b * |w q|) :=
            Finset.sum_le_sum fun q _ => hpoint q
      _ = a * (∑ q : Fin m, |z q|) + b * (∑ q : Fin m, |w q|) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  have hlt :
      a * (∑ q : Fin m, |z q|) + b * (∑ q : Fin m, |w q|) < alpha := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hw
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hz
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hzmul : a * (∑ q : Fin m, |z q|) < a * alpha :=
          mul_lt_mul_of_pos_left hz ha_pos
        have hwmul : b * (∑ q : Fin m, |w q|) < b * alpha :=
          mul_lt_mul_of_pos_left hw hb_pos
        have hcombine : a * alpha + b * alpha = alpha := by
          calc
            a * alpha + b * alpha = (a + b) * alpha := by ring
            _ = alpha := by rw [hab]; ring
        linarith
  exact lt_of_le_of_lt hsum_le hlt

theorem isConnected_osiiMZImaginaryL1Domain
    (m : ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    IsConnected (osiiMZImaginaryL1Domain m alpha) := by
  refine ⟨⟨0, ?_⟩, (convex_osiiMZImaginaryL1Domain m alpha).isPreconnected⟩
  simpa [osiiMZImaginaryL1Domain] using halpha

theorem osiiMZFlatImaginary_subset_l1Domain
    {m : ℕ} {alpha : ℝ} :
    osiiMZFlatImaginaryUnion m alpha ⊆ osiiMZImaginaryL1Domain m alpha := by
  intro t ht
  rcases Set.mem_iUnion.mp ht with ⟨q, hq⟩
  rcases hq with ⟨habs, hzero⟩
  have hsum : (∑ p : Fin m, |t p|) = |t q| := by
    refine Finset.sum_eq_single q ?_ ?_
    · intro p _ hp
      rw [hzero p hp]
      simp
    · intro hq_not
      simp at hq_not
  simpa [osiiMZImaginaryL1Domain, hsum] using habs

/-- The convex envelope of the one-coordinate flat tubes is contained in the
paper's `l1` imaginary log-domain. -/
theorem convexHull_flatImaginary_subset_l1Domain
    (m : ℕ) (alpha : ℝ) :
    convexHull ℝ (osiiMZFlatImaginaryUnion m alpha) ⊆
      osiiMZImaginaryL1Domain m alpha := by
  exact convexHull_min
    (osiiMZFlatImaginary_subset_l1Domain (m := m) (alpha := alpha))
    (convex_osiiMZImaginaryL1Domain m alpha)

theorem zero_mem_osiiMZFlatImaginaryUnion
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    (0 : Fin m → ℝ) ∈ osiiMZFlatImaginaryUnion m alpha := by
  let q : Fin m := Classical.choice ‹Nonempty (Fin m)›
  refine Set.mem_iUnion.mpr ⟨q, ?_⟩
  simp [osiiMZFlatImaginary, halpha]

/-- The paper's `l1` imaginary log-domain is contained in the convex hull of
the one-coordinate flat tubes. -/
theorem l1Domain_subset_convexHull_flatImaginary
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    osiiMZImaginaryL1Domain m alpha ⊆
      convexHull ℝ (osiiMZFlatImaginaryUnion m alpha) := by
  intro t ht
  let S : ℝ := ∑ q : Fin m, |t q|
  have hS_lt : S < alpha := by simpa [S, osiiMZImaginaryL1Domain] using ht
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun q _ => abs_nonneg (t q)
  by_cases hS0 : S = 0
  · have ht_zero : t = 0 := by
      funext q
      have hq_abs : |t q| = 0 := by
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun p _ => abs_nonneg (t p))).1 hS0
        exact hall q (Finset.mem_univ q)
      exact abs_eq_zero.mp hq_abs
    rw [ht_zero]
    exact subset_convexHull ℝ _
      (zero_mem_osiiMZFlatImaginaryUnion (m := m) (alpha := alpha) halpha)
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    let weight : Fin m → ℝ := fun q => |t q| / S
    let axisPoint : Fin m → Fin m → ℝ := fun q =>
      Pi.single q (if 0 ≤ t q then S else -S)
    have hweight_nonneg : ∀ q ∈ (Finset.univ : Finset (Fin m)), 0 ≤ weight q := by
      intro q _
      exact div_nonneg (abs_nonneg (t q)) hS_nonneg
    have hweight_sum : (∑ q : Fin m, weight q) = 1 := by
      calc
        (∑ q : Fin m, weight q) = (∑ q : Fin m, |t q|) / S := by
          simp [weight, Finset.sum_div]
        _ = S / S := rfl
        _ = 1 := div_self hS_pos.ne'
    have haxis_mem :
        ∀ q ∈ (Finset.univ : Finset (Fin m)),
          axisPoint q ∈ convexHull ℝ (osiiMZFlatImaginaryUnion m alpha) := by
      intro q _
      refine subset_convexHull ℝ _ ?_
      refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      constructor
      · have hS_abs : |(if 0 ≤ t q then S else -S)| = S := by
          by_cases htq : 0 ≤ t q
          · simp [htq, abs_of_nonneg hS_nonneg]
          · simp [htq, abs_of_nonneg hS_nonneg]
        simpa [osiiMZFlatImaginary, axisPoint, hS_abs] using hS_lt
      · intro p hp
        simp [axisPoint, Pi.single_eq_of_ne hp]
    have hbary :
        (∑ q : Fin m, weight q • axisPoint q) ∈
          convexHull ℝ (osiiMZFlatImaginaryUnion m alpha) := by
      exact (convex_convexHull ℝ (osiiMZFlatImaginaryUnion m alpha)).sum_mem
        hweight_nonneg hweight_sum haxis_mem
    have hbary_eq : (∑ q : Fin m, weight q • axisPoint q) = t := by
      funext p
      have hsum_single :
          (∑ q : Fin m, (weight q • axisPoint q) p) =
            (weight p • axisPoint p) p := by
        refine Finset.sum_eq_single p ?_ ?_
        · intro q _ hq
          simp [axisPoint, Pi.single_eq_of_ne (Ne.symm hq)]
        · intro hp
          simp at hp
      calc
        (∑ q : Fin m, weight q • axisPoint q) p
            = ∑ q : Fin m, (weight q • axisPoint q) p := by simp
        _ = (weight p • axisPoint p) p := hsum_single
        _ = t p := by
          by_cases htp : 0 ≤ t p
          · have habs : |t p| = t p := abs_of_nonneg htp
            simp [weight, axisPoint, htp, habs, hS_pos.ne']
          · have htp_neg : t p < 0 := lt_of_not_ge htp
            have habs : |t p| = -t p := abs_of_neg htp_neg
            simp [weight, axisPoint, htp, habs, hS_pos.ne']
    simpa [hbary_eq] using hbary

/-- The neutral convex-envelope identity behind the OS-II V.1
Malgrange-Zerner log-domain. -/
theorem convexHull_flatImaginary_eq_l1Domain
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    convexHull ℝ (osiiMZFlatImaginaryUnion m alpha) =
      osiiMZImaginaryL1Domain m alpha := by
  exact Set.Subset.antisymm
    (convexHull_flatImaginary_subset_l1Domain m alpha)
    (l1Domain_subset_convexHull_flatImaginary (m := m) (alpha := alpha) halpha)

/-- Every one-coordinate flat log tube lies in the final OS-II log carrier
`sum |Im r_q| < alpha`. -/
theorem flatLogTubeUnion_subset_osiiMZLogDomain
    {m : ℕ} {alpha : ℝ} :
    osiiMZFlatLogTubeUnion m alpha ⊆ osiiMZLogDomain m alpha := by
  intro z hz
  have him :
      (fun q : Fin m => (z q).im) ∈
        osiiMZFlatImaginaryUnion m alpha :=
    (mem_osiiMZFlatLogTubeUnion_iff (m := m) (alpha := alpha) (z := z)).mp hz
  exact osiiMZFlatImaginary_subset_l1Domain him

/-- The final complex log carrier is convex: only the imaginary coordinates
matter, and their `l1` norm is convex. -/
theorem convex_osiiMZLogDomain_via_flatEnvelope (m : ℕ) (alpha : ℝ) :
    Convex ℝ (osiiMZLogDomain m alpha) := by
  exact convex_osiiMZLogDomain m alpha

/-- The final log carrier is contained in the real convex hull of the complex
flat log-tube union.  This keeps real parts fixed and decomposes the imaginary
vector into signed coordinate-axis points. -/
theorem osiiMZLogDomain_subset_convexHull_flatLogTubeUnion
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    osiiMZLogDomain m alpha ⊆
      convexHull ℝ (osiiMZFlatLogTubeUnion m alpha) := by
  intro z hz
  let S : ℝ := ∑ q : Fin m, |(z q).im|
  have hS_lt : S < alpha := by simpa [S, osiiMZLogDomain] using hz
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun q _ => abs_nonneg (z q).im
  by_cases hS0 : S = 0
  · have him_zero : ∀ q : Fin m, (z q).im = 0 := by
      intro q
      have hq_abs : |(z q).im| = 0 := by
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun p _ => abs_nonneg (z p).im)).1 hS0
        exact hall q (Finset.mem_univ q)
      exact abs_eq_zero.mp hq_abs
    refine subset_convexHull ℝ _ ?_
    let q : Fin m := Classical.choice ‹Nonempty (Fin m)›
    refine ⟨q, ?_, ?_⟩
    · simpa [him_zero q] using halpha
    · intro p _hp
      exact him_zero p
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    let weight : Fin m → ℝ := fun q => |(z q).im| / S
    let axisImag : Fin m → Fin m → ℝ := fun q =>
      Pi.single q (if 0 ≤ (z q).im then S else -S)
    let axisPoint : Fin m → Fin m → ℂ := fun q p =>
      (z p).re + axisImag q p * Complex.I
    have hweight_nonneg : ∀ q ∈ (Finset.univ : Finset (Fin m)), 0 ≤ weight q := by
      intro q _
      exact div_nonneg (abs_nonneg (z q).im) hS_nonneg
    have hweight_sum : (∑ q : Fin m, weight q) = 1 := by
      calc
        (∑ q : Fin m, weight q) = (∑ q : Fin m, |(z q).im|) / S := by
          simp [weight, Finset.sum_div]
        _ = S / S := rfl
        _ = 1 := div_self hS_pos.ne'
    have haxis_mem :
        ∀ q ∈ (Finset.univ : Finset (Fin m)),
          axisPoint q ∈ convexHull ℝ (osiiMZFlatLogTubeUnion m alpha) := by
      intro q _
      refine subset_convexHull ℝ _ ?_
      refine ⟨q, ?_, ?_⟩
      · have hS_abs : |axisImag q q| = S := by
          by_cases hzq : 0 ≤ (z q).im
          · simp [axisImag, hzq, abs_of_nonneg hS_nonneg]
          · simp [axisImag, hzq, abs_of_nonneg hS_nonneg]
        simpa [axisPoint, hS_abs] using hS_lt
      · intro p hp
        simp [axisPoint, axisImag, Pi.single_eq_of_ne hp]
    have hbary :
        (∑ q : Fin m, weight q • axisPoint q) ∈
          convexHull ℝ (osiiMZFlatLogTubeUnion m alpha) := by
      exact (convex_convexHull ℝ (osiiMZFlatLogTubeUnion m alpha)).sum_mem
        hweight_nonneg hweight_sum haxis_mem
    have hbary_eq : (∑ q : Fin m, weight q • axisPoint q) = z := by
      funext p
      apply Complex.ext
      · calc
          ((∑ q : Fin m, weight q • axisPoint q) p).re
              = ∑ q : Fin m, (weight q * (z p).re) := by
                simp [axisPoint, Finset.sum_apply, Pi.smul_apply]
          _ = (∑ q : Fin m, weight q) * (z p).re := by
                rw [Finset.sum_mul]
          _ = (z p).re := by rw [hweight_sum, one_mul]
      · have hsum_single :
            (∑ q : Fin m,
              weight q * axisImag q p) =
              weight p * axisImag p p := by
          refine Finset.sum_eq_single p ?_ ?_
          · intro q _ hq
            simp [axisImag, Pi.single_eq_of_ne (Ne.symm hq)]
          · intro hp
            simp at hp
        calc
          ((∑ q : Fin m, weight q • axisPoint q) p).im
              =
                ∑ q : Fin m,
                  weight q * axisImag q p := by
                simp [axisPoint, Finset.sum_apply, Pi.smul_apply]
          _ = weight p * axisImag p p :=
                hsum_single
          _ = (z p).im := by
            by_cases hzp : 0 ≤ (z p).im
            · have habs : |(z p).im| = (z p).im := abs_of_nonneg hzp
              simp [weight, axisImag, hzp, habs, hS_pos.ne']
            · have hzp_neg : (z p).im < 0 := lt_of_not_ge hzp
              have habs : |(z p).im| = -((z p).im) := abs_of_neg hzp_neg
              simp [weight, axisImag, hzp, habs, hS_pos.ne']
    simpa [hbary_eq] using hbary

/-- Complex convex-envelope form of the OS-II flat-tube geometry.  The real
convex hull of the complex flat log tubes is exactly the log carrier
`sum |Im r_q| < alpha`. -/
theorem convexHull_flatLogTubeUnion_eq_osiiMZLogDomain
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    convexHull ℝ (osiiMZFlatLogTubeUnion m alpha) =
      osiiMZLogDomain m alpha := by
  exact Set.Subset.antisymm
    (convexHull_min
      (flatLogTubeUnion_subset_osiiMZLogDomain (m := m) (alpha := alpha))
      (convex_osiiMZLogDomain m alpha))
    (osiiMZLogDomain_subset_convexHull_flatLogTubeUnion
      (m := m) (alpha := alpha) halpha)

/-- Complex-domain form of the OS-II Malgrange-Zerner envelope geometry:
the tube over the convex hull of the one-coordinate flat imaginary tubes is
exactly the tube over the `l1` imaginary carrier. -/
theorem tubeDomain_convexHull_flatImaginary_eq_l1Tube
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    SCV.TubeDomain (convexHull ℝ (osiiMZFlatImaginaryUnion m alpha)) =
      SCV.TubeDomain (osiiMZImaginaryL1Domain m alpha) := by
  rw [convexHull_flatImaginary_eq_l1Domain (m := m) (alpha := alpha) halpha]

/-- Final complex-log carrier form used in OS II `(5.8)` before exponentiating:
the Malgrange-Zerner convex envelope of the flat log tubes is the domain
`sum_q |Im r_q| < alpha`. -/
theorem tubeDomain_convexHull_flatImaginary_eq_osiiMZLogDomain
    {m : ℕ} [Nonempty (Fin m)] {alpha : ℝ} (halpha : 0 < alpha) :
    SCV.TubeDomain (convexHull ℝ (osiiMZFlatImaginaryUnion m alpha)) =
      osiiMZLogDomain m alpha := by
  rw [tubeDomain_convexHull_flatImaginary_eq_l1Tube
    (m := m) (alpha := alpha) halpha]
  rfl

/-- In one log coordinate, the flat-tube union is already the final `l1`
carrier.  This is the base case of the local flat-tube/Malgrange-Zerner
construction. -/
theorem flatLogTubeUnion_fin1_eq_osiiMZLogDomain
    (alpha : ℝ) :
    osiiMZFlatLogTubeUnion 1 alpha =
      osiiMZLogDomain 1 alpha := by
  ext z
  simp [osiiMZFlatLogTubeUnion, osiiMZLogDomain]

/-- Dimension-one scalar Malgrange-Zerner base case: a branch already
holomorphic on the one-coordinate flat log tube is itself the holomorphic
representative on the convex-envelope carrier. -/
theorem scalar_mz_fin1_from_flat_branch
    {alpha : ℝ} (F : (Fin 1 → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (osiiMZFlatLogTubeUnion 1 alpha)) :
    ∃ Γ : (Fin 1 → ℂ) → ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain 1 alpha) ∧
      Set.EqOn Γ F (osiiMZFlatLogTubeUnion 1 alpha) := by
  refine ⟨F, ?_, ?_⟩
  · rw [← flatLogTubeUnion_fin1_eq_osiiMZLogDomain alpha]
    exact hF
  · intro z hz
    rfl

end OSReconstruction
