import OSReconstruction.SCV.ConnectedNeighborhood
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Bounded scalar continuation data

This file isolates the quantitative scalar invariant used by the bounded
Chapter V angular induction.  The carrier is open and star-convex about zero,
so its intersection with any zero-containing convex target chart is
connected.  That is exactly the geometry needed for identity-theorem gluing.
-/

noncomputable section

open Complex Set Topology

namespace OSReconstruction
namespace OSIIChapterV

/-- A scalar holomorphic continuation on an open star-convex carrier with a
single global norm bound. -/
structure BoundedScalarContinuationData
    (m : Nat) (B : Real) where
  carrier : Set (Fin m -> Complex)
  carrier_open : IsOpen carrier
  carrier_starConvex : StarConvex Real 0 carrier
  zero_mem : (0 : Fin m -> Complex) ∈ carrier
  toFun : (Fin m -> Complex) -> Complex
  differentiableOn : DifferentiableOn Complex toFun carrier
  norm_le : forall z, z ∈ carrier -> ‖toFun z‖ <= B

namespace BoundedScalarContinuationData

/-- Regard a bounded continuation as one with any larger numerical bound.
The analytic carrier and function are unchanged. -/
def weakenBound
    {m : Nat} {B B' : Real}
    (A : BoundedScalarContinuationData m B)
    (hBB' : B <= B') :
    BoundedScalarContinuationData m B' where
  carrier := A.carrier
  carrier_open := A.carrier_open
  carrier_starConvex := A.carrier_starConvex
  zero_mem := A.zero_mem
  toFun := A.toFun
  differentiableOn := A.differentiableOn
  norm_le := fun z hz => (A.norm_le z hz).trans hBB'

@[simp]
theorem weakenBound_carrier
    {m : Nat} {B B' : Real}
    (A : BoundedScalarContinuationData m B)
    (hBB' : B <= B') :
    (A.weakenBound hBB').carrier = A.carrier :=
  rfl

@[simp]
theorem weakenBound_apply
    {m : Nat} {B B' : Real}
    (A : BoundedScalarContinuationData m B)
    (hBB' : B <= B')
    (z : Fin m -> Complex) :
    (A.weakenBound hBB').toFun z = A.toFun z :=
  rfl

/-- A norm-bounded scalar gives a bounded continuation on the complete
parameter space.  In particular, this is the canonical continuation for a
zero-dimensional one-particle endpoint. -/
noncomputable def ofConst
    (m : Nat)
    (c : Complex)
    (hc : ‖c‖ <= B) :
    BoundedScalarContinuationData m B where
  carrier := Set.univ
  carrier_open := isOpen_univ
  carrier_starConvex :=
    convex_univ.starConvex (Set.mem_univ (0 : Fin m -> Complex))
  zero_mem := Set.mem_univ _
  toFun := fun _ => c
  differentiableOn := (differentiable_const c).differentiableOn
  norm_le := fun _ _ => hc

@[simp]
theorem ofConst_carrier
    (m : Nat)
    (c : Complex)
    (hc : ‖c‖ <= B) :
    (ofConst m c hc).carrier = Set.univ :=
  rfl

@[simp]
theorem ofConst_apply
    (m : Nat)
    (c : Complex)
    (hc : ‖c‖ <= B)
    (z : Fin m -> Complex) :
    (ofConst m c hc).toFun z = c :=
  rfl

end BoundedScalarContinuationData

end OSIIChapterV
end OSReconstruction
