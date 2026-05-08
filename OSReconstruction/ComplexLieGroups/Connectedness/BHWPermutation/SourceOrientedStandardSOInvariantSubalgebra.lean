import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantCoordinateMap
import OSReconstruction.ComplexLieGroups.SOConnected

/-!
# The standard `SO` fixed subalgebra for the oriented invariant packet

This file defines the actual standard-dot fixed subalgebra for the polynomial
action of `SO_D(ℂ)` on `n` tuple vectors.  It proves that the displayed
pairing and ordered-volume generators are invariant, and that the true
invariant-coordinate map is surjective once the genuine FFT equality identifies
the fixed subalgebra with the generated subalgebra.

The reverse FFT inclusion and the SFT kernel theorem are not proved here.
-/

noncomputable section

set_option linter.unnecessarySimpa false

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Contravariant polynomial action induced by the standard left action of
`SO_D(ℂ)` on tuple vectors. -/
def standardSOCoordinateAction
    (D n : ℕ) (g : SOComplex D) :
    standardTupleCoordinateRing D n →ₐ[ℂ] standardTupleCoordinateRing D n :=
  MvPolynomial.aeval
    (fun im : Fin n × Fin D =>
      ∑ ν : Fin D,
        MvPolynomial.C (g.val im.2 ν) * MvPolynomial.X (im.1, ν))

@[simp]
theorem standardSOCoordinateAction_apply_X
    (D n : ℕ) (g : SOComplex D) (im : Fin n × Fin D) :
    standardSOCoordinateAction D n g (MvPolynomial.X im) =
      ∑ ν : Fin D,
        MvPolynomial.C (g.val im.2 ν) * MvPolynomial.X (im.1, ν) := by
  simp [standardSOCoordinateAction]

/-- Pairing coordinates are fixed by the standard special orthogonal action. -/
theorem standardSOCoordinateAction_pairing
    (D n : ℕ) (g : SOComplex D) (ij : Fin n × Fin n) :
    standardSOCoordinateAction D n g
        (standardPairingCoordinatePolynomial D n ij) =
      standardPairingCoordinatePolynomial D n ij := by
  let Xi : Fin D → standardTupleCoordinateRing D n :=
    fun μ => MvPolynomial.X (ij.1, μ)
  let Xj : Fin D → standardTupleCoordinateRing D n :=
    fun μ => MvPolynomial.X (ij.2, μ)
  simp [standardPairingCoordinatePolynomial, standardSOCoordinateAction]
  change (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n)) *ᵥ Xi) ⬝ᵥ
      (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n)) *ᵥ Xj) =
    Xi ⬝ᵥ Xj
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_mulVec]
  have horth :
      (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n))).transpose *
          (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n))) =
        1 := by
    simpa [Matrix.map_mul] using
      congrArg
        (fun M : Matrix (Fin D) (Fin D) ℂ =>
          M.map (algebraMap ℂ (standardTupleCoordinateRing D n)))
        g.orthogonal
  rw [horth]
  simp [Xi]

/-- Ordered volume coordinates are fixed by the standard special orthogonal
action. -/
theorem standardSOCoordinateAction_volume
    (D n : ℕ) (g : SOComplex D) (ι : Fin D ↪ Fin n) :
    standardSOCoordinateAction D n g
        (standardVolumeCoordinatePolynomial D n ι) =
      standardVolumeCoordinatePolynomial D n ι := by
  unfold standardVolumeCoordinatePolynomial
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  change Matrix.det
      (fun a μ : Fin D =>
        standardSOCoordinateAction D n g (MvPolynomial.X (ι a, μ))) =
    Matrix.det (fun a μ : Fin D => MvPolynomial.X (ι a, μ))
  simp only [standardSOCoordinateAction_apply_X]
  let M : Matrix (Fin D) (Fin D) (standardTupleCoordinateRing D n) :=
    fun a μ => MvPolynomial.X (ι a, μ)
  let G : Matrix (Fin D) (Fin D) (standardTupleCoordinateRing D n) :=
    g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n))
  have hmat :
      (fun a μ : Fin D =>
        ∑ ν : Fin D, MvPolynomial.C (g.val μ ν) * MvPolynomial.X (ι a, ν)) =
      M * G.transpose := by
    ext a μ
    simp [M, G, Matrix.mul_apply, mul_comm]
  rw [hmat, Matrix.det_mul, Matrix.det_transpose]
  have hdet : G.det = 1 := by
    change (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n))).det = 1
    calc
      (g.val.map (algebraMap ℂ (standardTupleCoordinateRing D n))).det =
          (algebraMap ℂ (standardTupleCoordinateRing D n)) g.val.det := by
            exact
              (RingHom.map_det
                (algebraMap ℂ (standardTupleCoordinateRing D n)) g.val).symm
      _ = 1 := by
            simp [g.proper]
  rw [hdet]
  simp [M]

/-- The actual fixed subalgebra for the standard-dot special orthogonal action
on tuple-coordinate polynomials. -/
def standardSOInvariantSubalgebra
    (D n : ℕ) : Subalgebra ℂ (standardTupleCoordinateRing D n) where
  carrier :=
    {p | ∀ g : SOComplex D, standardSOCoordinateAction D n g p = p}
  mul_mem' := by
    intro p q hp hq g
    simp [hp g, hq g]
  add_mem' := by
    intro p q hp hq g
    simp [hp g, hq g]
  algebraMap_mem' := by
    intro c g
    simp [standardSOCoordinateAction]

theorem standardPairingCoordinatePolynomial_mem_invariantSubalgebra
    (D n : ℕ) (ij : Fin n × Fin n) :
    standardPairingCoordinatePolynomial D n ij ∈
      standardSOInvariantSubalgebra D n := by
  intro g
  exact standardSOCoordinateAction_pairing D n g ij

theorem standardVolumeCoordinatePolynomial_mem_invariantSubalgebra
    (D n : ℕ) (ι : Fin D ↪ Fin n) :
    standardVolumeCoordinatePolynomial D n ι ∈
      standardSOInvariantSubalgebra D n := by
  intro g
  exact standardSOCoordinateAction_volume D n g ι

/-- Pairing polynomial as an element of the actual fixed subalgebra. -/
def standardPairingInvariantElement
    (D n : ℕ) (ij : Fin n × Fin n) :
    standardSOInvariantSubalgebra D n :=
  ⟨standardPairingCoordinatePolynomial D n ij,
    standardPairingCoordinatePolynomial_mem_invariantSubalgebra D n ij⟩

/-- Ordered volume polynomial as an element of the actual fixed subalgebra. -/
def standardVolumeInvariantElement
    (D n : ℕ) (ι : Fin D ↪ Fin n) :
    standardSOInvariantSubalgebra D n :=
  ⟨standardVolumeCoordinatePolynomial D n ι,
    standardVolumeCoordinatePolynomial_mem_invariantSubalgebra D n ι⟩

/-- The generated presentation subalgebra is contained in the actual fixed
subalgebra.  The reverse inclusion is the genuine FFT theorem. -/
theorem standardSOGeneratorSubalgebra_le_invariantSubalgebra
    (D n : ℕ) :
    standardSOGeneratorSubalgebra D n ≤ standardSOInvariantSubalgebra D n := by
  unfold standardSOGeneratorSubalgebra
  refine Algebra.adjoin_le ?_
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨ij, rfl⟩
    exact standardPairingCoordinatePolynomial_mem_invariantSubalgebra D n ij
  · rcases hx with ⟨ι, rfl⟩
    exact standardVolumeCoordinatePolynomial_mem_invariantSubalgebra D n ι

/-- Inclusion of the generated presentation subalgebra into the actual fixed
subalgebra. -/
def standardSOGeneratorToInvariantAlgHom
    (D n : ℕ) :
    standardSOGeneratorSubalgebra D n →ₐ[ℂ]
      standardSOInvariantSubalgebra D n :=
  Subalgebra.inclusion
    (standardSOGeneratorSubalgebra_le_invariantSubalgebra D n)

/-- The actual invariant-coordinate map, obtained by following the generated
coordinate map with the inclusion into fixed points. -/
def standardSOInvariantCoordinateMap
    (D n : ℕ) :
    standardSOInvariantCoordinateRing D n →ₐ[ℂ]
      standardSOInvariantSubalgebra D n :=
  (standardSOGeneratorToInvariantAlgHom D n).comp
    (standardSOGeneratorCoordinateMap D n)

@[simp]
theorem standardSOInvariantCoordinateMap_apply_pairing
    (D n : ℕ) (ij : Fin n × Fin n) :
    standardSOInvariantCoordinateMap D n (MvPolynomial.X (Sum.inl ij)) =
      standardPairingInvariantElement D n ij := by
  ext
  simp [standardSOInvariantCoordinateMap, standardSOGeneratorToInvariantAlgHom,
    standardPairingInvariantElement, standardPairingGeneratorElement]

@[simp]
theorem standardSOInvariantCoordinateMap_apply_volume
    (D n : ℕ) (ι : Fin D ↪ Fin n) :
    standardSOInvariantCoordinateMap D n (MvPolynomial.X (Sum.inr ι)) =
      standardVolumeInvariantElement D n ι := by
  ext
  simp [standardSOInvariantCoordinateMap, standardSOGeneratorToInvariantAlgHom,
    standardVolumeInvariantElement, standardVolumeGeneratorElement]

/-- The actual invariant-coordinate map is surjective once the FFT identifies
the actual fixed subalgebra with the generated subalgebra. -/
theorem standardSOInvariantCoordinateMap_surjective_of_generator_eq
    (D n : ℕ)
    (hFFT :
      standardSOInvariantSubalgebra D n =
        standardSOGeneratorSubalgebra D n) :
    Function.Surjective (standardSOInvariantCoordinateMap D n) := by
  intro y
  have hyGen : (y : standardTupleCoordinateRing D n) ∈
      standardSOGeneratorSubalgebra D n := by
    simpa [← hFFT] using y.2
  let yg : standardSOGeneratorSubalgebra D n := ⟨y, hyGen⟩
  rcases standardSOGeneratorCoordinateMap_surjective D n yg with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  simpa [standardSOInvariantCoordinateMap, standardSOGeneratorToInvariantAlgHom,
    yg] using congrArg Subtype.val hp

/-- Surjectivity of the actual invariant-coordinate map from the standard
FFT in its displayed pairing/volume adjoin form. -/
theorem standardSOInvariantCoordinateMap_surjective_of_generators
    (D n : ℕ)
    (hFFT :
      standardSOInvariantSubalgebra D n =
        Algebra.adjoin ℂ
          (Set.range (standardPairingCoordinatePolynomial D n) ∪
            Set.range (standardVolumeCoordinatePolynomial D n))) :
    Function.Surjective (standardSOInvariantCoordinateMap D n) :=
  standardSOInvariantCoordinateMap_surjective_of_generator_eq
    D n
    (by
      simpa [standardSOGeneratorSubalgebra] using hFFT)

end BHW
