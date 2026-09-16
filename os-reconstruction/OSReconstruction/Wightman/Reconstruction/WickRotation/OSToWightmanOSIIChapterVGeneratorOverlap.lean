/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.SCV.TotallyRealIdentity











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace GeneratorFamily

variable {d k : ℕ}

/-- A nonempty convex complex domain preserved by componentwise conjugation
contains a real point.  The real point is the midpoint of any point and its
conjugate. -/
theorem exists_real_mem_of_convex_conjMap_invariant
    {U : Set (Fin k → ℂ)}
    (hU_convex : Convex ℝ U)
    (hU_conj : ∀ z ∈ U, SCV.conjMap k z ∈ U)
    (hU_nonempty : U.Nonempty) :
    ∃ x : Fin k → ℝ, SCV.realToComplex x ∈ U := by
  obtain ⟨z, hz⟩ := hU_nonempty
  refine ⟨fun i => (z i).re, ?_⟩
  have hmid :
      midpoint ℝ z (SCV.conjMap k z) ∈ U :=
    hU_convex.midpoint_mem hz (hU_conj z hz)
  convert hmid using 1
  ext i
  apply Complex.ext
  · simp [midpoint_eq_smul_add, SCV.conjMap, SCV.realToComplex]
    ring
  · simp [midpoint_eq_smul_add, SCV.conjMap, SCV.realToComplex]

/-- A common open positive-real edge forces two holomorphic generator
branches to agree throughout every connected overlap. -/
theorem compatible_of_commonPositiveRealEdge
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (distribution :
      GeneratorIndex k →
        OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (weaklyHolomorphic :
      ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i))
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hreal :
      ∀ i τ, τ ∈ U →
        osiiPositiveRealTimeEmbed τ ∈ domain i ∧
          distribution i (osiiPositiveRealTimeEmbed τ) = R τ)
    (overlap_connected :
      ∀ i j, IsConnected (domain i ∩ domain j)) :
    ∀ i j,
      Set.EqOn (distribution i) (distribution j)
        (domain i ∩ domain j) := by
  intro i j z hz
  apply ContinuousLinearMap.ext
  intro χ
  let D : Set (OSIITimeGapSpace k) := domain i ∩ domain j
  let F : OSIITimeGapSpace k → ℂ :=
    fun w => distribution i w χ - distribution j w χ
  have hF :
      DifferentiableOn ℂ F D :=
    ((weaklyHolomorphic i χ).mono Set.inter_subset_left).sub
      ((weaklyHolomorphic j χ).mono Set.inter_subset_right)
  have hU_sub :
      ∀ τ ∈ U, SCV.realToComplex τ ∈ D := by
    intro τ hτ
    have hi := (hreal i τ hτ).1
    have hj := (hreal j τ hτ).1
    change osiiPositiveRealTimeEmbed τ ∈ D
    exact ⟨hi, hj⟩
  have hF_zero :
      ∀ τ ∈ U, F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    have hi := (hreal i τ hτ).2
    have hj := (hreal j τ hτ).2
    simp only [F]
    rw [show SCV.realToComplex τ = osiiPositiveRealTimeEmbed τ by
      rfl, hi, hj, sub_self]
  have hz_zero :
      F z = 0 :=
    SCV.identity_theorem_totally_real
      ((domain_open i).inter (domain_open j))
      (overlap_connected i j)
      hF hU_open hU_nonempty hU_sub hF_zero z hz
  exact sub_eq_zero.mp hz_zero

/-- Build the existing gluable generator-family object from holomorphic local
branches and their common real edge. Pairwise compatibility is derived, not
assumed. -/
def ofCommonPositiveRealEdge
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (distribution :
      GeneratorIndex k →
        OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (weaklyHolomorphic :
      ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i))
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hreal :
      ∀ i τ, τ ∈ U →
        osiiPositiveRealTimeEmbed τ ∈ domain i ∧
          distribution i (osiiPositiveRealTimeEmbed τ) = R τ)
    (overlap_connected :
      ∀ i j, IsConnected (domain i ∩ domain j)) :
    GeneratorFamily d k where
  domain := domain
  domain_open := domain_open
  distribution := distribution
  weaklyHolomorphic := weaklyHolomorphic
  compatible :=
    compatible_of_commonPositiveRealEdge
      domain domain_open distribution weaklyHolomorphic
      R U hU_open hU_nonempty hreal overlap_connected

theorem ofCommonPositiveRealEdge_hasCommonPositiveRealEdge
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (distribution :
      GeneratorIndex k →
        OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (weaklyHolomorphic :
      ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i))
    (R : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hreal :
      ∀ i τ, τ ∈ U →
        osiiPositiveRealTimeEmbed τ ∈ domain i ∧
          distribution i (osiiPositiveRealTimeEmbed τ) = R τ)
    (overlap_connected :
      ∀ i j, IsConnected (domain i ∩ domain j)) :
    (ofCommonPositiveRealEdge
      domain domain_open distribution weaklyHolomorphic
      R U hU_open hU_nonempty hreal overlap_connected).HasCommonPositiveRealEdge
        R U := by
  exact hreal

end GeneratorFamily
end OSIIChapterV
end OSReconstruction
