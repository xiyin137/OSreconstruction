import OSReconstruction.Wightman.Reconstruction.Core

/-!
# Ordered positive-time topology

The openness of the ordered Euclidean positive-time region is elementary
configuration-space topology. It lives below the OS45 locality development so
Chapter V source calculus can use it without importing the public
continuation endpoint.
-/

open Topology

namespace BHW

variable {d n : ℕ}

/-- The ordered positive-time region is open in the Euclidean configuration
space. -/
theorem isOpen_orderedPositiveTimeRegion :
    IsOpen (OrderedPositiveTimeRegion d n) := by
  suffices h :
      OrderedPositiveTimeRegion d n =
        (⋂ i : Fin n, {x : NPointDomain d n | 0 < x i 0}) ∩
          (⋂ i : Fin n, ⋂ j : Fin n,
            {x : NPointDomain d n | i < j → x i 0 < x j 0}) by
    rw [h]
    apply IsOpen.inter
    · exact isOpen_iInter_of_finite fun i => by
        have hcoord : Continuous (fun x : NPointDomain d n => x i 0) :=
          (continuous_apply 0).comp (continuous_apply i)
        exact isOpen_lt continuous_const hcoord
    · apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      by_cases hij : i < j
      · have hi : Continuous (fun x : NPointDomain d n => x i 0) :=
          (continuous_apply 0).comp (continuous_apply i)
        have hj : Continuous (fun x : NPointDomain d n => x j 0) :=
          (continuous_apply 0).comp (continuous_apply j)
        convert isOpen_lt hi hj using 1
        ext x
        simp [hij]
      · convert isOpen_univ using 1
        ext x
        simp [hij]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      exact (hx i).1
    · intro i j hij
      exact (hx i).2 j hij
  · rintro ⟨hx_pos, hx_lt⟩
    intro i
    exact ⟨hx_pos i, fun j hij => hx_lt i j hij⟩

end BHW
