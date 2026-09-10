import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource

/-!
# OS-II Chapter V: canonical degree-zero vacuum source

This focused module owns the constant-one degree-zero positive-time source
shared by the Chapter V Hilbert-field construction and the Chapter VI BVT
basepoint comparison.  Keeping it below both consumers avoids importing the
later vacuum-tail continuation merely to name the vacuum class.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The constant-one Schwartz test in particle degree zero. -/
noncomputable def osiiChapterVVacuumUnit (d : ℕ) :
    SchwartzNPoint d 0 := by
  let one : NPointDomain d 0 → ℂ := fun _ => 1
  have hcompact : HasCompactSupport one := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (Set.univ : Set (NPointDomain d 0))) ?_ ?_
    · exact Set.Subsingleton.isCompact Set.subsingleton_univ
    · intro x hx
      simp
  exact hcompact.toSchwartzMap (by
    simpa [one] using
      (contDiff_const :
        ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun _ : NPointDomain d 0 => (1 : ℂ))))

@[simp] theorem osiiChapterVVacuumUnit_apply
    (d : ℕ) (x : NPointDomain d 0) :
    osiiChapterVVacuumUnit d x = 1 :=
  rfl

theorem osiiChapterVVacuumUnit_ordered (d : ℕ) :
    tsupport
        ((osiiChapterVVacuumUnit d : SchwartzNPoint d 0) :
          NPointDomain d 0 → ℂ) ⊆
      OrderedPositiveTimeRegion d 0 := by
  intro x hx
  simp [OrderedPositiveTimeRegion]

variable {d n : ℕ} [NeZero d]

/-- The degree-zero constant-one test as an admissible positive-time source. -/
noncomputable def osiiChapterVVacuumSource :
    euclideanPositiveTimeSubmodule (d := d) 0 :=
  ⟨osiiChapterVVacuumUnit d, osiiChapterVVacuumUnit_ordered d⟩

/-- Removing the empty OS-conjugated vacuum block leaves the right source. -/
@[simp] theorem reindex_osiiChapterVVacuumUnit_osConjTensorProduct
    (g : SchwartzNPoint d n) :
    reindexSchwartz (d := d) (finCongr (Nat.zero_add n))
        ((osiiChapterVVacuumUnit d).osConjTensorProduct g) =
      g := by
  ext x
  simp only [reindexSchwartz_apply, SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply,
    osiiChapterVVacuumUnit_apply, map_one, one_mul]
  congr 1
  funext i
  simp [splitLast]

end OSIIChapterV
end OSReconstruction
