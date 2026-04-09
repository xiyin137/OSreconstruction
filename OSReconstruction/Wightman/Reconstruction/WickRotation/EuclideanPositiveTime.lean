import OSReconstruction.Wightman.Reconstruction.Core

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The Euclidean positive-time degree-`n` test space from OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- An equivalent submodule presentation of the Euclidean positive-time domain.

The Section-4.3 transport map is naturally a continuous linear map on this
submodule surface. -/
def euclideanPositiveTimeSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
  zero_mem' := by
    change tsupport (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n
    rw [show (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) = 0 by rfl]
    simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
      (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) hx
    exact hx'.elim (hf ·) (hg ·)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right
      (fun _ : NPointDomain d n => c)
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)).trans hf

@[simp] theorem mem_euclideanPositiveTimeSubmodule
    {n : ℕ} (f : SchwartzNPoint d n) :
    f ∈ euclideanPositiveTimeSubmodule (d := d) n ↔
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := Iff.rfl

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- Package a positive-time submodule element as the corresponding subtype
object. -/
def ofSubmodule
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    EuclideanPositiveTimeComponent d n :=
  ⟨f.1, f.2⟩

end EuclideanPositiveTimeComponent

end OSReconstruction
