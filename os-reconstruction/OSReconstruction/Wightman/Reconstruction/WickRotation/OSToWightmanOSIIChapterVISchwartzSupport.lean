import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIGrowthBoundaryHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertRealEdge
import OSReconstruction.SCV.EuclideanWeylOpen
import Mathlib.Analysis.Distribution.Support

/-!
# Schwartz support and the positive time cone

These pure support lemmas precede both temporal spectrum and Lorentz transport.
Compact localization, radial density, and a positive translation retain the
distinction between pointwise support and topological support. No analytic
boundary or spectral-support assumption is used.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

/-- Vanishing on compactly supported tests extends to arbitrary Schwartz tests
with the same topological-support restriction. -/
theorem osiiSchwartzDistribution_isVanishingOn_of_compact
    {m : Nat} {U : Set (Fin m -> Real)}
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (hcompact : forall phi : SchwartzMap (Fin m -> Real) Complex,
      HasCompactSupport (phi : (Fin m -> Real) -> Complex) ->
      tsupport (phi : (Fin m -> Real) -> Complex) ⊆ U -> T phi = 0) :
    Distribution.IsVanishingOn T U := by
  intro phi hphi
  have hzero : ∀ n : Nat, T (bumpTruncationRadius phi n) = 0 := by
    intro n
    apply hcompact
      (bumpTruncationRadius phi n)
    · exact hasCompactSupport_cutoff_mul_radius
        (bumpTruncationRadiusValue n)
        (bumpTruncationRadiusValue_pos n) phi
    · intro p hp
      apply hphi
      change p ∈ tsupport
        ((SchwartzMap.smulLeftCLM Complex
          (unitBallBumpSchwartzPiRadius m (bumpTruncationRadiusValue n)
            (bumpTruncationRadiusValue_pos n)) phi :
            SchwartzMap (Fin m -> Real) Complex) :
              (Fin m -> Real) -> Complex) at hp
      exact ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := Complex)
        (g := (unitBallBumpSchwartzPiRadius m (bumpTruncationRadiusValue n)
          (bumpTruncationRadiusValue_pos n) : (Fin m -> Real) -> Complex))
        (f := phi)) hp).1
  have hlimit : Tendsto (fun n : Nat => T (bumpTruncationRadius phi n))
      atTop (nhds (T phi)) :=
    (T.continuous.tendsto phi).comp
      (SchwartzMap.tendsto_bump_truncation_nhds phi)
  have hzero_limit : Tendsto (fun n : Nat => T (bumpTruncationRadius phi n))
      atTop (nhds (0 : Complex)) := by
    simp [hzero]
  exact tendsto_nhds_unique hlimit hzero_limit

/-- A compact Schwartz test whose topological support avoids a distribution's
support is annihilated by that distribution.  The local zero neighborhoods are
assembled with a finite smooth Schwartz partition. -/
private theorem osiiSchwartzDistribution_apply_eq_zero_of_compact_tsupport_disjoint
    {m : Nat}
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex)
    (phi : SchwartzMap (Fin m -> Real) Complex)
    (hcompact : HasCompactSupport
      (phi : (Fin m -> Real) -> Complex))
    (hphi : tsupport (phi : (Fin m -> Real) -> Complex) ⊆
      (Distribution.dsupport T)ᶜ) :
    T phi = 0 := by
  let K : Set (Fin m -> Real) :=
    tsupport (phi : (Fin m -> Real) -> Complex)
  let beta := {p : Fin m -> Real // p ∈ K}
  have hlocal : ∀ p : beta,
      ∃ U : Set (Fin m -> Real),
        Distribution.IsVanishingOn T U ∧ IsOpen U ∧ (p : Fin m -> Real) ∈ U := by
    intro p
    apply (Distribution.notMem_dsupport_iff (f := T) (p : Fin m -> Real)).mp
    exact hphi p.property
  let U : beta -> Set (Fin m -> Real) :=
    fun p => Classical.choose (hlocal p)
  have hU : ∀ p : beta,
      Distribution.IsVanishingOn T (U p) ∧
      IsOpen (U p) ∧ (p : Fin m -> Real) ∈ U p := by
    intro p
    exact Classical.choose_spec (hlocal p)
  let V : beta -> Set (Fin m -> Real) :=
    fun p => U p ∩ Metric.ball (p : Fin m -> Real) 1
  have hVopen : ∀ p : beta, IsOpen (V p) := by
    intro p
    exact (hU p).2.1.inter Metric.isOpen_ball
  have hcover : K ⊆ ⋃ p : beta, V p := by
    intro p hp
    exact Set.mem_iUnion.mpr
      ⟨⟨p, hp⟩, ⟨(hU ⟨p, hp⟩).2.2, by simp⟩⟩
  obtain ⟨s, hs⟩ :=
    hcompact.isCompact.elim_finite_subcover V hVopen hcover
  let alpha := {p : beta // p ∈ s}
  let W : alpha -> Set (Fin m -> Real) := fun p => V p.1
  have hWopen : ∀ p : alpha, IsOpen (W p) := by
    intro p
    exact hVopen p.1
  have hWbounded : ∀ p : alpha,
      ∃ c R, W p ⊆ Metric.closedBall c R := by
    intro p
    exact ⟨(p.1 : Fin m -> Real), 1,
      fun q hq => Metric.ball_subset_closedBall hq.2⟩
  have hWcover : K ⊆ ⋃ p : alpha, W p := by
    intro q hq
    obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.mp (hs hq)
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hqp⟩
  obtain ⟨chi, _hchi_compact, hchi_support, hchi_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      hcompact.isCompact hWopen hWbounded hWcover
  have hsum : phi =
      ∑ p : alpha,
        SchwartzMap.smulLeftCLM Complex (chi p : (Fin m -> Real) -> Complex)
          phi := by
    simpa [K] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset alpha) chi phi
        (fun q hq => by simpa [K] using hchi_sum q hq)
  rw [hsum, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  apply (hU p.1).1
  intro q hq
  exact (hchi_support p
    ((SchwartzMap.tsupport_smulLeftCLM_subset
      (F := Complex)
      (g := (chi p : (Fin m -> Real) -> Complex))
      (f := phi)) hq).2).1

/-- A continuous Schwartz functional vanishes on the entire open complement
of its distributional support, including noncompact Schwartz tests. -/
theorem osiiSchwartzDistribution_isVanishingOn_compl_dsupport
    {m : Nat}
    (T : SchwartzMap (Fin m -> Real) Complex →L[Complex] Complex) :
    Distribution.IsVanishingOn T (Distribution.dsupport T)ᶜ :=
  osiiSchwartzDistribution_isVanishingOn_of_compact T
    (osiiSchwartzDistribution_apply_eq_zero_of_compact_tsupport_disjoint T)

/-- The dual of the strict positive time orthant is the closed positive time
orthant, including zero time arity. Spectator coordinates must stay strictly
positive in the separating test vector. -/
theorem dualConeFlat_osiiTimePositiveCone (k : Nat) :
    DualConeFlat (osiiTimePositiveCone k) =
      section43TimePositiveRegion k := by
  ext p
  constructor
  · intro hp j
    by_contra hnonneg
    have hnegative : p j < 0 := lt_of_not_ge hnonneg
    let A : Real := ∑ l : Fin k, if l = j then 0 else p l
    obtain ⟨epsilon, hepsilon, hsmall⟩ :=
      exists_pos_mul_abs_lt_of_neg (c := A) (s := p j) hnegative
    let y : Fin k -> Real := fun l => if l = j then 1 else epsilon
    have hy : y ∈ osiiTimePositiveCone k := by
      intro l
      by_cases hl : l = j <;> simp [y, hl, hepsilon]
    have hpair := hp y hy
    have hsum : (∑ l : Fin k, y l * p l) = p j + epsilon * A := by
      have hterm : ∀ l : Fin k,
          y l * p l =
            (if l = j then p l else 0) +
              epsilon * (if l = j then 0 else p l) := by
        intro l
        by_cases hl : l = j <;> simp [y, hl]
      rw [Finset.sum_congr rfl (fun l _ => hterm l),
        Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [A, Finset.sum_ite_eq']
    rw [hsum] at hpair
    have hA : epsilon * A ≤ epsilon * |A| :=
      mul_le_mul_of_nonneg_left (le_abs_self A) hepsilon.le
    linarith
  · intro hp y hy
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hy j).le (hp j)

/-- For the closed positive orthant, ordinary distributional vanishing and the
literal all-Schwartz Fourier-support predicate agree. A strictly positive
common time translation handles tests whose topological support touches an
orthant face. -/
theorem hasFourierSupportInDualCone_osiiTimePositiveCone_iff_isVanishingOn
    {k : Nat}
    (T : SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex) :
    HasFourierSupportInDualCone (osiiTimePositiveCone k) T ↔
      Distribution.IsVanishingOn T (section43TimePositiveRegion k)ᶜ := by
  rw [HasFourierSupportInDualCone, dualConeFlat_osiiTimePositiveCone]
  constructor
  · intro hT phi hphi
    exact hT phi (fun p hp => hphi (subset_tsupport _ hp))
  · intro hT phi hphi
    let v : Fin k -> Real := fun _ => 1
    have htranslated : ∀ t : Real, 0 < t ->
        tsupport
          ((SCV.translateSchwartz (t • v) phi :
            SchwartzMap (Fin k -> Real) Complex) :
              (Fin k -> Real) -> Complex) ⊆
          (section43TimePositiveRegion k)ᶜ := by
      intro t ht p hp hpnonneg
      let U : Set (Fin k -> Real) :=
        (fun q => q + t • v) ⁻¹' osiiTimePositiveCone k
      have hUopen : IsOpen U :=
        (osiiTimePositiveCone_open k).preimage
          (continuous_id.add continuous_const)
      have hpU : p ∈ U := by
        intro j
        change 0 < p j + t * v j
        simp [v]
        linarith [hpnonneg j]
      have heventually :
          ((SCV.translateSchwartz (t • v) phi :
            SchwartzMap (Fin k -> Real) Complex) :
              (Fin k -> Real) -> Complex) =ᶠ[nhds p] 0 := by
        filter_upwards [hUopen.mem_nhds hpU] with q hq
        rw [SCV.translateSchwartz_apply]
        have hqnonneg : q + t • v ∈ section43TimePositiveRegion k := by
          intro j
          exact (hq j).le
        by_contra hnonzero
        exact hphi _ (Function.mem_support.mpr hnonzero) hqnonneg
      exact (notMem_tsupport_iff_eventuallyEq.mpr heventually) hp
    have hcontinuous :
        Continuous (fun t : Real =>
          T (SCV.translateSchwartz (t • v) phi)) :=
      T.continuous.comp
        ((continuous_translateSchwartz_unrestricted phi).comp
          (continuous_id.smul continuous_const))
    let Z : Set Real :=
      {t | T (SCV.translateSchwartz (t • v) phi) = 0}
    have hclosed : IsClosed Z :=
      isClosed_eq hcontinuous continuous_const
    have hpositive : Set.Ioi (0 : Real) ⊆ Z := by
      intro t ht
      exact hT (SCV.translateSchwartz (t • v) phi)
        (htranslated t ht)
    have hzero : (0 : Real) ∈ Z := by
      apply closure_minimal hpositive hclosed
      rw [closure_Ioi]
      simp
    change T (SCV.translateSchwartz ((0 : Real) • v) phi) = 0 at hzero
    have htranslate : SCV.translateSchwartz ((0 : Real) • v) phi = phi := by
      ext p
      simp
    rwa [htranslate] at hzero

end OSReconstruction
