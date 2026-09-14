/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarTargetSuccessor











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace BoundedScalarTargetChartData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {target : Fin m -> Complex}

/-- Forget the distinguished target of a bounded chart and point it at its
common zero germ. -/
def repointZero
    (D : BoundedScalarTargetChartData A target) :
    BoundedScalarTargetChartData A 0 where
  domain := D.domain
  domain_open := D.domain_open
  domain_convex := D.domain_convex
  zero_mem_domain := D.zero_mem_domain
  target_mem_domain := D.zero_mem_domain
  toFun := D.toFun
  toFun_differentiableOn := D.toFun_differentiableOn
  norm_toFun_le := D.norm_toFun_le
  exists_open_eq_predecessor := D.exists_open_eq_predecessor

end BoundedScalarTargetChartData

/-- A nonempty family of bounded convex scalar branches, all carrying the
same germ at zero as one bounded predecessor. -/
structure BoundedScalarBranchAtlasData
    {m : Nat} {B : Real}
    (A : BoundedScalarContinuationData m B) where
  chart : Type
  chart_nonempty : Nonempty chart
  chartData : chart -> BoundedScalarTargetChartData A 0

namespace BoundedScalarBranchAtlasData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}

/-- The union of all bounded branch domains. -/
def domain (D : BoundedScalarBranchAtlasData A) :
    Set (Fin m -> Complex) :=
  ⋃ a, (D.chartData a).domain

theorem domain_open (D : BoundedScalarBranchAtlasData A) :
    IsOpen D.domain :=
  isOpen_iUnion fun a => (D.chartData a).domain_open

theorem domain_starConvex
    (D : BoundedScalarBranchAtlasData A) :
    StarConvex Real 0 D.domain := by
  apply starConvex_iUnion
  intro a
  exact (D.chartData a).domain_convex.starConvex
    (D.chartData a).zero_mem_domain

/-- Any two atlas branches agree on their complete overlap. -/
theorem compatible
    (D : BoundedScalarBranchAtlasData A)
    (a b : D.chart) :
    Set.EqOn (D.chartData a).toFun (D.chartData b).toFun
      ((D.chartData a).domain ∩ (D.chartData b).domain) := by
  let U : Set (Fin m -> Complex) :=
    (D.chartData a).domain ∩ (D.chartData b).domain
  have hU_open : IsOpen U :=
    (D.chartData a).domain_open.inter (D.chartData b).domain_open
  have hU_connected : IsConnected U := by
    exact
      ((((D.chartData a).domain_convex.starConvex
          (D.chartData a).zero_mem_domain).inter
        ((D.chartData b).domain_convex.starConvex
          (D.chartData b).zero_mem_domain)).isPathConnected
            ⟨(D.chartData a).zero_mem_domain,
              (D.chartData b).zero_mem_domain⟩).isConnected
  have hlocal :
      (D.chartData a).toFun =ᶠ[nhds (0 : Fin m -> Complex)]
        (D.chartData b).toFun := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨U ∩ A.carrier,
      (hU_open.inter A.carrier_open).mem_nhds
        ⟨⟨(D.chartData a).zero_mem_domain,
          (D.chartData b).zero_mem_domain⟩, A.zero_mem⟩, ?_⟩
    intro z hz
    exact
      ((D.chartData a).toFun_eq_predecessor_on_overlap
          ⟨hz.1.1, hz.2⟩).trans
        ((D.chartData b).toFun_eq_predecessor_on_overlap
          ⟨hz.1.2, hz.2⟩).symm
  simpa [U] using
    (identity_theorem_SCV hU_open hU_connected
      ((D.chartData a).toFun_differentiableOn.mono Set.inter_subset_left)
      ((D.chartData b).toFun_differentiableOn.mono Set.inter_subset_right)
      ⟨(D.chartData a).zero_mem_domain,
        (D.chartData b).zero_mem_domain⟩ hlocal)

/-- The scalar branch obtained by gluing the complete atlas. -/
noncomputable def toFun
    (D : BoundedScalarBranchAtlasData A) :
    (Fin m -> Complex) -> Complex :=
  SCV.glued_iUnion (fun a => (D.chartData a).domain)
    (fun a => (D.chartData a).toFun)

theorem toFun_eqOn
    (D : BoundedScalarBranchAtlasData A)
    (a : D.chart) :
    Set.EqOn D.toFun (D.chartData a).toFun (D.chartData a).domain :=
  SCV.glued_iUnion_eqOn D.compatible a

/-- The glued atlas is holomorphic on the union of its domains. -/
theorem toFun_differentiableOn
    (D : BoundedScalarBranchAtlasData A) :
    DifferentiableOn Complex D.toFun D.domain := by
  apply SCV.differentiableOn_glued_iUnion
  · exact Set.Subset.rfl
  · intro a
    exact (D.chartData a).domain_open
  · intro a
    exact (D.chartData a).toFun_differentiableOn
  · exact D.compatible

/-- Gluing preserves the common numerical bound exactly. -/
theorem norm_toFun_le
    (D : BoundedScalarBranchAtlasData A)
    {z : Fin m -> Complex}
    (hz : z ∈ D.domain) :
    ‖D.toFun z‖ <= B := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  rw [D.toFun_eqOn a ha]
  exact (D.chartData a).norm_toFun_le ha

/-- The glued atlas retains the predecessor on its complete overlap. -/
theorem toFun_eq_predecessor_on_overlap
    (D : BoundedScalarBranchAtlasData A) :
    Set.EqOn D.toFun A.toFun (D.domain ∩ A.carrier) := by
  intro z hz
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz.1
  exact
    (D.toFun_eqOn a ha).trans
      ((D.chartData a).toFun_eq_predecessor_on_overlap ⟨ha, hz.2⟩)

/-- The two carriers used to adjoin the complete atlas to its predecessor. -/
def successorDomain
    (D : BoundedScalarBranchAtlasData A)
    (b : Bool) : Set (Fin m -> Complex) :=
  if b then A.carrier else D.domain

/-- The predecessor and glued-atlas representatives. -/
def successorBranch
    (D : BoundedScalarBranchAtlasData A)
    (b : Bool) : (Fin m -> Complex) -> Complex :=
  if b then A.toFun else D.toFun

theorem successorBranch_compatible
    (D : BoundedScalarBranchAtlasData A)
    (b c : Bool) :
    Set.EqOn (D.successorBranch b) (D.successorBranch c)
      (D.successorDomain b ∩ D.successorDomain c) := by
  cases b <;> cases c
  · exact Set.eqOn_refl _ _
  · intro z hz
    exact D.toFun_eq_predecessor_on_overlap hz
  · intro z hz
    exact (D.toFun_eq_predecessor_on_overlap ⟨hz.2, hz.1⟩).symm
  · exact Set.eqOn_refl _ _

/-- Glue the complete bounded atlas to its predecessor, retaining every
chart domain and the same numerical bound. -/
noncomputable def toSuccessor
    (D : BoundedScalarBranchAtlasData A) :
    BoundedScalarContinuationData m B where
  carrier := ⋃ b : Bool, D.successorDomain b
  carrier_open := by
    apply isOpen_iUnion
    intro b
    cases b <;> simp [successorDomain, D.domain_open, A.carrier_open]
  carrier_starConvex := by
    apply starConvex_iUnion
    intro b
    cases b
    · simpa [successorDomain] using D.domain_starConvex
    · simpa [successorDomain] using A.carrier_starConvex
  zero_mem := by
    exact Set.mem_iUnion_of_mem true
      (by simpa [successorDomain] using A.zero_mem)
  toFun := SCV.glued_iUnion D.successorDomain D.successorBranch
  differentiableOn := by
    apply SCV.differentiableOn_glued_iUnion
    · exact Set.Subset.rfl
    · intro b
      cases b <;> simp [successorDomain, D.domain_open, A.carrier_open]
    · intro b
      cases b
      · simpa [successorBranch, successorDomain] using
          D.toFun_differentiableOn
      · simpa [successorBranch, successorDomain] using
          A.differentiableOn
    · exact D.successorBranch_compatible
  norm_le := by
    intro z hz
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
    rw [SCV.glued_iUnion_eqOn D.successorBranch_compatible b hb]
    cases b
    · exact D.norm_toFun_le (by simpa [successorDomain] using hb)
    · exact A.norm_le z (by simpa [successorDomain] using hb)

theorem predecessor_subset_toSuccessor
    (D : BoundedScalarBranchAtlasData A) :
    A.carrier ⊆ D.toSuccessor.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem true
    (by simpa [successorDomain] using hz)

theorem domain_subset_toSuccessor
    (D : BoundedScalarBranchAtlasData A) :
    D.domain ⊆ D.toSuccessor.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem false
    (by simpa [successorDomain] using hz)

theorem toSuccessor_eq_predecessor
    (D : BoundedScalarBranchAtlasData A) :
    Set.EqOn D.toSuccessor.toFun A.toFun A.carrier := by
  intro z hz
  exact SCV.glued_iUnion_eqOn D.successorBranch_compatible true
    (by simpa [successorDomain] using hz)

end BoundedScalarBranchAtlasData
end OSIIChapterV
end OSReconstruction
