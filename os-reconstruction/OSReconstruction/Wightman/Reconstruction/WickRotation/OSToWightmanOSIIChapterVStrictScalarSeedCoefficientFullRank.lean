/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientChart















noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Real spanning of a finite real seed family implies surjectivity of its
complex coefficient map. -/
theorem osiiStrictScalarSeedCoefficientMap_surjective_of_span_eq_top
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real)
    (hspan :
      Submodule.span Real (Set.range seed) =
        (⊤ : Submodule Real (Fin k -> Real))) :
    Function.Surjective
      (osiiStrictScalarSeedCoefficientMap seed) := by
  have hsurj_real :
      Function.Surjective
        (Fintype.linearCombination Real seed) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (R := Real) (v := seed)).mp hspan
  intro z
  obtain ⟨a, ha⟩ :=
    hsurj_real (fun j => (z j).re)
  obtain ⟨b, hb⟩ :=
    hsurj_real (fun j => (z j).im)
  refine
    ⟨fun i => (a i : Complex) + (b i : Complex) * I, ?_⟩
  funext j
  apply Complex.ext
  · have haj := congrFun ha j
    simpa [osiiStrictScalarSeedCoefficientMap,
      Fintype.linearCombination_apply] using haj
  · have hbj := congrFun hb j
    simpa [osiiStrictScalarSeedCoefficientMap,
      Fintype.linearCombination_apply] using hbj

/-- Appending a surjective seed family preserves surjectivity, independently
of the seed family already present. -/
theorem osiiStrictScalarSeedCoefficientMap_append_surjective
    {n m k : Nat}
    (seed₁ : Fin n -> Fin k -> Real)
    (seed₂ : Fin m -> Fin k -> Real)
    (hseed₂ :
      Function.Surjective
        (osiiStrictScalarSeedCoefficientMap seed₂)) :
    Function.Surjective
      (osiiStrictScalarSeedCoefficientMap
        (Fin.append seed₁ seed₂)) := by
  intro z
  obtain ⟨r₂, hr₂⟩ := hseed₂ z
  let r : Fin (n + m) -> Complex :=
    Fin.append (fun _ : Fin n => 0) r₂
  refine ⟨r, ?_⟩
  funext j
  have hr₂j := congrFun hr₂ j
  simpa [r, osiiStrictScalarSeedCoefficientMap,
    Fin.sum_univ_add] using hr₂j

end OSIIChapterV
end OSReconstruction
