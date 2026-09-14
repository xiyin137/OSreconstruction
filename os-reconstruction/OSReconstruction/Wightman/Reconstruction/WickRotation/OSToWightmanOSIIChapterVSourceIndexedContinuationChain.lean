/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedCauchyContinuation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A finite sequence of common source-family Cauchy continuation steps.

The predecessor stage is an index of the type.  Consequently a `cons` step
can only continue from the actual successor produced by the preceding common
Cauchy package; preservation of the reflected-Gram contract is built into the
chain rather than carried as a separate proposition. -/
inductive SourceIndexedReflectedGramContinuationChain
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (ι : Type*) (k : ℕ)
    (scalar :
      ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ) :
    SourceIndexedReflectedGramHilbertFieldData
        H ι (k + 1) scalar →
      ℕ → Type _ where
  | nil
      (P : SourceIndexedReflectedGramHilbertFieldData
        H ι (k + 1) scalar) :
      SourceIndexedReflectedGramContinuationChain
        H ι k scalar P 0
  | cons
      {P : SourceIndexedReflectedGramHilbertFieldData
        H ι (k + 1) scalar}
      {n : ℕ}
      (D : SourceIndexedComplexCenteredHilbertCauchyData
        H ι k scalar P)
      (tail : SourceIndexedReflectedGramContinuationChain
        H ι k scalar D.toSuccessor n) :
      SourceIndexedReflectedGramContinuationChain
        H ι k scalar P (n + 1)

namespace SourceIndexedReflectedGramContinuationChain

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {ι : Type*} {k : ℕ}
  {scalar :
    ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
  {P : SourceIndexedReflectedGramHilbertFieldData
    H ι (k + 1) scalar}
  {n : ℕ}

/-- The final reflected-Gram chart reached by a finite chain. -/
def terminal :
    SourceIndexedReflectedGramContinuationChain
        H ι k scalar P n →
      SourceIndexedReflectedGramHilbertFieldData
        H ι (k + 1) scalar := by
  intro C
  induction C with
  | nil Q =>
      exact Q
  | cons _D _tail ih =>
      exact ih

/-- The union of the initial domain and every successor chart domain in the
chain.  No global gluing claim is hidden in this definition. -/
def coveredDomain :
    SourceIndexedReflectedGramContinuationChain
        H ι k scalar P n →
      Set (Fin (k + 1) → ℂ) := by
  intro C
  induction C with
  | nil Q =>
      exact Q.domain
  | @cons Q _n _D _tail ih =>
      exact Q.domain ∪ ih

@[simp] theorem terminal_nil
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar) :
    (SourceIndexedReflectedGramContinuationChain.nil P).terminal = P :=
  rfl

@[simp] theorem terminal_cons
    {P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar}
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (tail : SourceIndexedReflectedGramContinuationChain
      H ι k scalar D.toSuccessor n) :
    (SourceIndexedReflectedGramContinuationChain.cons D tail).terminal =
      tail.terminal :=
  rfl

@[simp] theorem coveredDomain_nil
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar) :
    (SourceIndexedReflectedGramContinuationChain.nil P).coveredDomain =
      P.domain :=
  rfl

@[simp] theorem coveredDomain_cons
    {P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar}
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (tail : SourceIndexedReflectedGramContinuationChain
      H ι k scalar D.toSuccessor n) :
    (SourceIndexedReflectedGramContinuationChain.cons D tail).coveredDomain =
      P.domain ∪ tail.coveredDomain :=
  rfl

/-- The one-step chain associated to one common source-family Cauchy
package. -/
def singleton
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    SourceIndexedReflectedGramContinuationChain
      H ι k scalar P 1 :=
  .cons D (.nil D.toSuccessor)

@[simp] theorem terminal_singleton
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    (singleton D).terminal = D.toSuccessor :=
  rfl

@[simp] theorem coveredDomain_singleton
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    (singleton D).coveredDomain =
      P.domain ∪ D.successorDomain :=
  rfl

/-- The equally spaced list of `steps + 1` points from `start` to `target`.
The positive-step theorems below identify its endpoints and adjacent
distance. -/
def segmentSubdivision
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ) :
    List (Fin (k + 1) → ℂ) :=
  List.ofFn (fun j : Fin (steps + 1) =>
    AffineMap.lineMap (k := ℝ) start target
      ((j.val : ℝ) / (steps : ℝ)))

@[simp] theorem segmentSubdivision_length
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ) :
    (segmentSubdivision start target steps).length = steps + 1 := by
  simp [segmentSubdivision]

theorem segmentSubdivision_ne_nil
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ) :
    segmentSubdivision start target steps ≠ [] := by
  intro h
  have hlength := congrArg List.length h
  simp at hlength

@[simp] theorem segmentSubdivision_head
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ) :
    (segmentSubdivision start target steps).head
        (segmentSubdivision_ne_nil start target steps) =
      start := by
  simp [segmentSubdivision]

@[simp] theorem segmentSubdivision_getLast
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ)
    (hsteps : 0 < steps) :
    (segmentSubdivision start target steps).getLast
        (segmentSubdivision_ne_nil start target steps) =
      target := by
  change
    (List.ofFn (fun j : Fin (steps + 1) =>
      AffineMap.lineMap (k := ℝ) start target
        ((j.val : ℝ) / (steps : ℝ)))).getLast _ =
      target
  rw [List.getLast_ofFn]
  have hindex : steps + 1 - 1 = steps := by omega
  rw [show
    ((⟨steps + 1 - 1, by omega⟩ : Fin (steps + 1))).val =
      steps by exact hindex]
  simp [hsteps.ne']

/-- Every subdivision waypoint lies on the original real segment. -/
theorem mem_segment_of_mem_segmentSubdivision
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ)
    (hsteps : 0 < steps)
    {center : Fin (k + 1) → ℂ}
    (hcenter :
      center ∈ segmentSubdivision start target steps) :
    center ∈ segment ℝ start target := by
  rw [segmentSubdivision, List.mem_ofFn] at hcenter
  obtain ⟨j, rfl⟩ := hcenter
  rw [segment_eq_image_lineMap]
  refine
    ⟨(j.val : ℝ) / (steps : ℝ), ?_, rfl⟩
  have hsteps_real : (0 : ℝ) < (steps : ℝ) := by
    exact_mod_cast hsteps
  have hjle : (j.val : ℝ) ≤ (steps : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  exact
    ⟨div_nonneg (Nat.cast_nonneg _) hsteps_real.le,
      (div_le_one hsteps_real).2 hjle⟩

/-- If the mesh size is smaller than `radius`, consecutive subdivision
points lie in the corresponding open successor polydisc. -/
theorem segmentSubdivision_isChain
    (start target : Fin (k + 1) → ℂ)
    (steps : ℕ)
    (hsteps : 0 < steps)
    (radius : ℝ)
    (hmesh :
      dist start target / (steps : ℝ) < radius) :
    (segmentSubdivision start target steps).IsChain
      (fun center next =>
        next ∈ SCV.Polydisc center (fun _ => radius)) := by
  rw [segmentSubdivision, List.isChain_ofFn]
  intro i hi
  rw [SCV.mem_polydisc_iff]
  intro coordinate
  apply lt_of_le_of_lt
    (dist_le_pi_dist
      (AffineMap.lineMap (k := ℝ) start target
        (((i + 1 : ℕ) : ℝ) / (steps : ℝ)))
      (AffineMap.lineMap (k := ℝ) start target
        ((i : ℝ) / (steps : ℝ)))
      coordinate)
  have hline :
      dist
          (AffineMap.lineMap (k := ℝ) start target
            (((i + 1 : ℕ) : ℝ) / (steps : ℝ)))
          (AffineMap.lineMap (k := ℝ) start target
            ((i : ℝ) / (steps : ℝ))) =
        dist
            (((i + 1 : ℕ) : ℝ) / (steps : ℝ))
            ((i : ℝ) / (steps : ℝ)) *
          dist start target :=
    dist_lineMap_lineMap (𝕜 := ℝ) start target _ _
  rw [hline]
  have hsteps_real : (0 : ℝ) < (steps : ℝ) := by
    exact_mod_cast hsteps
  have hparameter :
      dist
          (((i + 1 : ℕ) : ℝ) / (steps : ℝ))
          ((i : ℝ) / (steps : ℝ)) =
        1 / (steps : ℝ) := by
    rw [Real.dist_eq, ← sub_div]
    simp
  rw [hparameter]
  simpa [div_eq_mul_inv, mul_comm] using hmesh

/-- Any positive radius admits a finite equally spaced subdivision whose
mesh is strictly smaller than that radius. -/
theorem exists_segmentSubdivision_mesh_lt
    (start target : Fin (k + 1) → ℂ)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ∃ steps : ℕ, 0 < steps ∧
      dist start target / (steps : ℝ) < radius := by
  obtain ⟨steps, hsteps⟩ :=
    exists_nat_gt (dist start target / radius)
  have hquotient_nonneg :
      0 ≤ dist start target / radius :=
    div_nonneg dist_nonneg hradius.le
  have hsteps_real : (0 : ℝ) < (steps : ℝ) :=
    lt_of_le_of_lt hquotient_nonneg hsteps
  have hsteps_nat : 0 < steps := by
    exact_mod_cast hsteps_real
  refine ⟨steps, hsteps_nat, ?_⟩
  rw [div_lt_iff₀ hsteps_real]
  rw [div_lt_iff₀ hradius] at hsteps
  simpa [mul_comm] using hsteps

end SourceIndexedReflectedGramContinuationChain

end OSIIChapterV
end OSReconstruction
