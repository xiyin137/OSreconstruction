import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantCoordinateRing
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedMinkowskiDotTransport

/-!
# Coordinate-ring transport from source Minkowski coordinates to dot coordinates

This file checks the polynomial-coordinate part of the oriented normality
route.  The transport is contravariant: a source-coordinate polynomial is
evaluated on a dot tuple after pulling that tuple back by
`(complexMinkowskiToDotLinearEquiv d).symm`.  Thus source variables map to the
inverse Wick-scaled standard-dot variables, and selected determinant
polynomials pick up the inverse determinant scale.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Contravariant coordinate-ring map from source Minkowski tuple coordinates
to standard dot tuple coordinates. -/
def sourceMinkowskiToDotCoordinateRingHom
    (d n : ℕ) :
    sourceTupleCoordinateRing d n →ₐ[ℂ]
      standardTupleCoordinateRing (d + 1) n :=
  MvPolynomial.aeval
    (fun im : Fin n × Fin (d + 1) =>
      MvPolynomial.C (complexMinkowskiDotInvScale d im.2) *
        MvPolynomial.X im)

/-- Inverse coordinate-ring map from standard dot tuple coordinates back to
source Minkowski tuple coordinates. -/
def sourceDotToMinkowskiCoordinateRingHom
    (d n : ℕ) :
    standardTupleCoordinateRing (d + 1) n →ₐ[ℂ]
      sourceTupleCoordinateRing d n :=
  MvPolynomial.aeval
    (fun im : Fin n × Fin (d + 1) =>
      MvPolynomial.C (complexMinkowskiDotScale d im.2) *
        MvPolynomial.X im)

@[simp]
theorem sourceMinkowskiToDotCoordinateRingHom_apply_X
    (d n : ℕ) (im : Fin n × Fin (d + 1)) :
    sourceMinkowskiToDotCoordinateRingHom d n (MvPolynomial.X im) =
      MvPolynomial.C (complexMinkowskiDotInvScale d im.2) *
        MvPolynomial.X im := by
  simp [sourceMinkowskiToDotCoordinateRingHom]

@[simp]
theorem sourceDotToMinkowskiCoordinateRingHom_apply_X
    (d n : ℕ) (im : Fin n × Fin (d + 1)) :
    sourceDotToMinkowskiCoordinateRingHom d n (MvPolynomial.X im) =
      MvPolynomial.C (complexMinkowskiDotScale d im.2) *
        MvPolynomial.X im := by
  simp [sourceDotToMinkowskiCoordinateRingHom]

/-- The source-to-dot and dot-to-source coordinate maps compose to the
identity on source tuple coordinates. -/
theorem sourceDotToMinkowskiCoordinateRingHom_comp_sourceMinkowskiToDot
    (d n : ℕ) :
    (sourceDotToMinkowskiCoordinateRingHom d n).comp
        (sourceMinkowskiToDotCoordinateRingHom d n) =
      AlgHom.id ℂ (sourceTupleCoordinateRing d n) := by
  ext im
  simp [sourceMinkowskiToDotCoordinateRingHom,
    sourceDotToMinkowskiCoordinateRingHom]
  rename_i m
  calc
    complexMinkowskiDotInvScale d im.2 *
        (complexMinkowskiDotScale d im.2 *
          MvPolynomial.coeff m (MvPolynomial.X im))
        =
          (complexMinkowskiDotInvScale d im.2 *
            complexMinkowskiDotScale d im.2) *
              MvPolynomial.coeff m (MvPolynomial.X im) := by
          ring
    _ = MvPolynomial.coeff m (MvPolynomial.X im) := by
          rw [complexMinkowskiDotInvScale_mul_scale]
          ring

/-- The source-to-dot and dot-to-source coordinate maps compose to the
identity on standard dot tuple coordinates. -/
theorem sourceMinkowskiToDotCoordinateRingHom_comp_sourceDotToMinkowski
    (d n : ℕ) :
    (sourceMinkowskiToDotCoordinateRingHom d n).comp
        (sourceDotToMinkowskiCoordinateRingHom d n) =
      AlgHom.id ℂ (standardTupleCoordinateRing (d + 1) n) := by
  ext im
  simp [sourceMinkowskiToDotCoordinateRingHom,
    sourceDotToMinkowskiCoordinateRingHom]
  rename_i m
  have hscale :
      complexMinkowskiDotScale d im.2 *
        complexMinkowskiDotInvScale d im.2 = 1 := by
    rw [mul_comm]
    exact complexMinkowskiDotInvScale_mul_scale d im.2
  calc
    complexMinkowskiDotScale d im.2 *
        (complexMinkowskiDotInvScale d im.2 *
          MvPolynomial.coeff m (MvPolynomial.X im))
        =
          (complexMinkowskiDotScale d im.2 *
            complexMinkowskiDotInvScale d im.2) *
              MvPolynomial.coeff m (MvPolynomial.X im) := by
          ring
    _ = MvPolynomial.coeff m (MvPolynomial.X im) := by
          rw [hscale]
          ring

/-- Coordinate-ring equivalence induced by the source Minkowski-to-dot linear
equivalence. -/
def sourceMinkowskiToDotCoordinateRingEquiv
    (d n : ℕ) :
    sourceTupleCoordinateRing d n ≃ₐ[ℂ]
      standardTupleCoordinateRing (d + 1) n :=
  AlgEquiv.ofAlgHom
    (sourceMinkowskiToDotCoordinateRingHom d n)
    (sourceDotToMinkowskiCoordinateRingHom d n)
    (sourceMinkowskiToDotCoordinateRingHom_comp_sourceDotToMinkowski d n)
    (sourceDotToMinkowskiCoordinateRingHom_comp_sourceMinkowskiToDot d n)

@[simp]
theorem sourceMinkowskiToDotCoordinateRingEquiv_apply_X
    (d n : ℕ) (im : Fin n × Fin (d + 1)) :
    sourceMinkowskiToDotCoordinateRingEquiv d n (MvPolynomial.X im) =
      MvPolynomial.C (complexMinkowskiDotInvScale d im.2) *
        MvPolynomial.X im := by
  simp [sourceMinkowskiToDotCoordinateRingEquiv,
    sourceMinkowskiToDotCoordinateRingHom]

/-- Scalar cancellation used by the Gram-coordinate transport. -/
theorem metricSignature_mul_invScale_mul_invScale
    (d : ℕ) (μ : Fin (d + 1)) :
    (MinkowskiSpace.metricSignature d μ : ℂ) *
        complexMinkowskiDotInvScale d μ *
        complexMinkowskiDotInvScale d μ = 1 := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, MinkowskiSpace.metricSignature, hμ]

/-- The coordinate-ring transport sends source Gram polynomials to ordinary
dot-pairing polynomials. -/
theorem sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceGram
    (d n : ℕ)
    (ij : Fin n × Fin n) :
    sourceMinkowskiToDotCoordinateRingEquiv d n
        (sourceGramCoordinatePolynomial d n ij) =
      standardPairingCoordinatePolynomial (d + 1) n ij := by
  unfold sourceGramCoordinatePolynomial standardPairingCoordinatePolynomial
  simp [sourceMinkowskiToDotCoordinateRingEquiv,
    sourceMinkowskiToDotCoordinateRingHom]
  apply Finset.sum_congr rfl
  intro μ _hμ
  have hscaleC :
      MvPolynomial.C (MinkowskiSpace.metricSignature d μ : ℂ) *
          MvPolynomial.C (complexMinkowskiDotInvScale d μ) *
          (MvPolynomial.C (complexMinkowskiDotInvScale d μ) :
            standardTupleCoordinateRing (d + 1) n) = 1 := by
    rw [← map_mul, ← map_mul,
      metricSignature_mul_invScale_mul_invScale d μ]
    simp
  calc
    MvPolynomial.C (MinkowskiSpace.metricSignature d μ : ℂ) *
          (MvPolynomial.C (complexMinkowskiDotInvScale d μ) *
            (MvPolynomial.X (ij.1, μ) :
              standardTupleCoordinateRing (d + 1) n)) *
        (MvPolynomial.C (complexMinkowskiDotInvScale d μ) *
          (MvPolynomial.X (ij.2, μ) :
            standardTupleCoordinateRing (d + 1) n))
        =
          (MvPolynomial.C (MinkowskiSpace.metricSignature d μ : ℂ) *
            MvPolynomial.C (complexMinkowskiDotInvScale d μ) *
              MvPolynomial.C (complexMinkowskiDotInvScale d μ)) *
            (MvPolynomial.X (ij.1, μ) * MvPolynomial.X (ij.2, μ)) := by
          ring
    _ = MvPolynomial.X (ij.1, μ) * MvPolynomial.X (ij.2, μ) := by
          rw [hscaleC]
          ring

/-- The coordinate-ring transport sends selected source determinant
polynomials to the corresponding standard volume polynomial times the inverse
determinant scale. -/
theorem sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceDet
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceMinkowskiToDotCoordinateRingEquiv d n
        (sourceFullFrameDetPolynomial d n ι) =
      MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
        standardVolumeCoordinatePolynomial (d + 1) n ι := by
  change sourceMinkowskiToDotCoordinateRingHom d n
      (sourceFullFrameDetPolynomial d n ι) =
    MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
      standardVolumeCoordinatePolynomial (d + 1) n ι
  unfold sourceFullFrameDetPolynomial standardVolumeCoordinatePolynomial
  rw [AlgHom.map_det]
  rw [AlgHom.mapMatrix_apply]
  change Matrix.det
      (fun a μ : Fin (d + 1) =>
        sourceMinkowskiToDotCoordinateRingHom d n
          (MvPolynomial.X (ι a, μ))) =
    MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
      Matrix.det (fun a μ : Fin (d + 1) => MvPolynomial.X (ι a, μ))
  simp [sourceMinkowskiToDotCoordinateRingHom]
  let M : Matrix (Fin (d + 1)) (Fin (d + 1))
      (standardTupleCoordinateRing (d + 1) n) :=
    fun a μ => MvPolynomial.X (ι a, μ)
  let S : Matrix (Fin (d + 1)) (Fin (d + 1))
      (standardTupleCoordinateRing (d + 1) n) :=
    Matrix.diagonal
      (fun μ => MvPolynomial.C (complexMinkowskiDotInvScale d μ))
  have hmat :
      (fun a μ : Fin (d + 1) =>
          MvPolynomial.C (complexMinkowskiDotInvScale d μ) *
            MvPolynomial.X (ι a, μ)) = M * S := by
    ext a μ
    simp [M, S, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  rw [hmat]
  simp [M, S, sourceMinkowskiToDotInvDetScale, Matrix.det_mul,
    Matrix.det_diagonal, mul_comm]

/-- The tuple-coordinate equivalence transports the source algebra generated
by Gram and selected determinant polynomials to the standard-dot algebra
generated by pairings and selected volume polynomials. -/
theorem sourceMinkowskiToDotCoordinateRingEquiv_adjoin_pairing_volume
    (d n : ℕ) :
    algEquivMapSubalgebra
        (sourceMinkowskiToDotCoordinateRingEquiv d n)
        (Algebra.adjoin ℂ
          (Set.range (sourceGramCoordinatePolynomial d n) ∪
           Set.range (sourceFullFrameDetPolynomial d n))) =
      Algebra.adjoin ℂ
        (Set.range (standardPairingCoordinatePolynomial (d + 1) n) ∪
         Set.range (standardVolumeCoordinatePolynomial (d + 1) n)) := by
  let Ssrc : Set (sourceTupleCoordinateRing d n) :=
    Set.range (sourceGramCoordinatePolynomial d n) ∪
      Set.range (sourceFullFrameDetPolynomial d n)
  let Sdst : Set (standardTupleCoordinateRing (d + 1) n) :=
    Set.range (standardPairingCoordinatePolynomial (d + 1) n) ∪
      Set.range (standardVolumeCoordinatePolynomial (d + 1) n)
  change (Algebra.adjoin ℂ Ssrc).map
      (sourceMinkowskiToDotCoordinateRingEquiv d n).toAlgHom =
    Algebra.adjoin ℂ Sdst
  rw [AlgHom.map_adjoin]
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro y ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · rcases hx with ⟨ij, rfl⟩
      simpa [sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceGram d n ij] using
        Algebra.subset_adjoin
          (show standardPairingCoordinatePolynomial (d + 1) n ij ∈ Sdst from
            Or.inl ⟨ij, rfl⟩)
    · rcases hx with ⟨ι, rfl⟩
      simpa [sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceDet d n ι] using
        (Algebra.adjoin ℂ Sdst).mul_mem
          ((Algebra.adjoin ℂ Sdst).algebraMap_mem
            (sourceMinkowskiToDotInvDetScale d))
          (Algebra.subset_adjoin
            (show standardVolumeCoordinatePolynomial (d + 1) n ι ∈ Sdst from
              Or.inr ⟨ι, rfl⟩))
  · refine Algebra.adjoin_le ?_
    intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨ij, rfl⟩
      refine Algebra.subset_adjoin ?_
      refine ⟨sourceGramCoordinatePolynomial d n ij, ?_, ?_⟩
      · exact Or.inl ⟨ij, rfl⟩
      · simpa using
          sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceGram d n ij
    · rcases hy with ⟨ι, rfl⟩
      let T := Algebra.adjoin ℂ
        ((sourceMinkowskiToDotCoordinateRingEquiv d n).toAlgHom '' Ssrc)
      have himage :
          sourceMinkowskiToDotCoordinateRingEquiv d n
              (sourceFullFrameDetPolynomial d n ι) ∈ T := by
        exact
          Algebra.subset_adjoin
            ⟨sourceFullFrameDetPolynomial d n ι, Or.inr ⟨ι, rfl⟩, rfl⟩
      have hscaled :
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
              sourceMinkowskiToDotCoordinateRingEquiv d n
                (sourceFullFrameDetPolynomial d n ι) ∈ T := by
        exact
          T.mul_mem
            (T.algebraMap_mem (sourceMinkowskiToDotDetScale d))
            himage
      have hEq :
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
              sourceMinkowskiToDotCoordinateRingEquiv d n
                (sourceFullFrameDetPolynomial d n ι) =
            standardVolumeCoordinatePolynomial (d + 1) n ι := by
        rw [sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceDet]
        calc
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
              (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
                standardVolumeCoordinatePolynomial (d + 1) n ι)
              =
                (MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
                  MvPolynomial.C (sourceMinkowskiToDotInvDetScale d)) *
                    standardVolumeCoordinatePolynomial (d + 1) n ι := by
                ring
          _ = standardVolumeCoordinatePolynomial (d + 1) n ι := by
                have hC :
                    MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
                        (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) :
                          standardTupleCoordinateRing (d + 1) n) = 1 := by
                  rw [← map_mul,
                    sourceMinkowskiToDotDetScale_mul_invDetScale]
                  simp
                rw [hC]
                ring
      simpa [T, hEq] using hscaled

/-- Contravariant map on the invariant-coordinate presentation: Gram variables
map to standard pairing variables, and oriented determinant variables map to
the inverse determinant scale times standard volume variables. -/
def sourceMinkowskiToDotInvariantCoordinateRingHom
    (d n : ℕ) :
    sourceOrientedInvariantCoordinateRing d n →ₐ[ℂ]
      standardSOInvariantCoordinateRing (d + 1) n :=
  MvPolynomial.aeval
    (fun x =>
      match x with
      | Sum.inl ij => MvPolynomial.X (Sum.inl ij)
      | Sum.inr ι =>
          MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
            MvPolynomial.X (Sum.inr ι))

/-- Inverse map on invariant-coordinate presentations. -/
def sourceDotToMinkowskiInvariantCoordinateRingHom
    (d n : ℕ) :
    standardSOInvariantCoordinateRing (d + 1) n →ₐ[ℂ]
      sourceOrientedInvariantCoordinateRing d n :=
  MvPolynomial.aeval
    (fun x =>
      match x with
      | Sum.inl ij => MvPolynomial.X (Sum.inl ij)
      | Sum.inr ι =>
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
            MvPolynomial.X (Sum.inr ι))

@[simp]
theorem sourceMinkowskiToDotInvariantCoordinateRingHom_apply_gram
    (d n : ℕ) (ij : Fin n × Fin n) :
    sourceMinkowskiToDotInvariantCoordinateRingHom d n
        (MvPolynomial.X (Sum.inl ij)) =
      (MvPolynomial.X (Sum.inl ij) :
        standardSOInvariantCoordinateRing (d + 1) n) := by
  simp [sourceMinkowskiToDotInvariantCoordinateRingHom]

@[simp]
theorem sourceMinkowskiToDotInvariantCoordinateRingHom_apply_det
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    sourceMinkowskiToDotInvariantCoordinateRingHom d n
        (MvPolynomial.X (Sum.inr ι)) =
      MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
        (MvPolynomial.X (Sum.inr ι) :
          standardSOInvariantCoordinateRing (d + 1) n) := by
  simp [sourceMinkowskiToDotInvariantCoordinateRingHom]

@[simp]
theorem sourceDotToMinkowskiInvariantCoordinateRingHom_apply_pairing
    (d n : ℕ) (ij : Fin n × Fin n) :
    sourceDotToMinkowskiInvariantCoordinateRingHom d n
        (MvPolynomial.X (Sum.inl ij)) =
      (MvPolynomial.X (Sum.inl ij) :
        sourceOrientedInvariantCoordinateRing d n) := by
  simp [sourceDotToMinkowskiInvariantCoordinateRingHom]

@[simp]
theorem sourceDotToMinkowskiInvariantCoordinateRingHom_apply_volume
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    sourceDotToMinkowskiInvariantCoordinateRingHom d n
        (MvPolynomial.X (Sum.inr ι)) =
      MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
        (MvPolynomial.X (Sum.inr ι) :
          sourceOrientedInvariantCoordinateRing d n) := by
  simp [sourceDotToMinkowskiInvariantCoordinateRingHom]

/-- The invariant-coordinate maps compose to the identity on source
Gram/determinant coordinates. -/
theorem sourceDotToMinkowskiInvariantCoordinateRingHom_comp_sourceMinkowskiToDot
    (d n : ℕ) :
    (sourceDotToMinkowskiInvariantCoordinateRingHom d n).comp
        (sourceMinkowskiToDotInvariantCoordinateRingHom d n) =
      AlgHom.id ℂ (sourceOrientedInvariantCoordinateRing d n) := by
  ext x
  cases x with
  | inl ij =>
      simp [sourceDotToMinkowskiInvariantCoordinateRingHom,
        sourceMinkowskiToDotInvariantCoordinateRingHom]
  | inr ι =>
      simp [sourceDotToMinkowskiInvariantCoordinateRingHom,
        sourceMinkowskiToDotInvariantCoordinateRingHom]
      rename_i m
      calc
        sourceMinkowskiToDotInvDetScale d *
            (sourceMinkowskiToDotDetScale d *
              MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)))
            =
              (sourceMinkowskiToDotInvDetScale d *
                sourceMinkowskiToDotDetScale d) *
                  MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)) := by
              ring
        _ = MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)) := by
              rw [sourceMinkowskiToDotInvDetScale_mul_detScale]
              ring

/-- The invariant-coordinate maps compose to the identity on standard
pairing/volume coordinates. -/
theorem sourceMinkowskiToDotInvariantCoordinateRingHom_comp_sourceDotToMinkowski
    (d n : ℕ) :
    (sourceMinkowskiToDotInvariantCoordinateRingHom d n).comp
        (sourceDotToMinkowskiInvariantCoordinateRingHom d n) =
      AlgHom.id ℂ (standardSOInvariantCoordinateRing (d + 1) n) := by
  ext x
  cases x with
  | inl ij =>
      simp [sourceDotToMinkowskiInvariantCoordinateRingHom,
        sourceMinkowskiToDotInvariantCoordinateRingHom]
  | inr ι =>
      simp [sourceDotToMinkowskiInvariantCoordinateRingHom,
        sourceMinkowskiToDotInvariantCoordinateRingHom]
      rename_i m
      calc
        sourceMinkowskiToDotDetScale d *
            (sourceMinkowskiToDotInvDetScale d *
              MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)))
            =
              (sourceMinkowskiToDotDetScale d *
                sourceMinkowskiToDotInvDetScale d) *
                  MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)) := by
              ring
        _ = MvPolynomial.coeff m (MvPolynomial.X (Sum.inr ι)) := by
              rw [sourceMinkowskiToDotDetScale_mul_invDetScale]
              ring

/-- Algebra equivalence between the source and standard-dot invariant
coordinate presentations. -/
def sourceMinkowskiToDotInvariantCoordinateEquiv
    (d n : ℕ) :
    sourceOrientedInvariantCoordinateRing d n ≃ₐ[ℂ]
      standardSOInvariantCoordinateRing (d + 1) n :=
  AlgEquiv.ofAlgHom
    (sourceMinkowskiToDotInvariantCoordinateRingHom d n)
    (sourceDotToMinkowskiInvariantCoordinateRingHom d n)
    (sourceMinkowskiToDotInvariantCoordinateRingHom_comp_sourceDotToMinkowski
      d n)
    (sourceDotToMinkowskiInvariantCoordinateRingHom_comp_sourceMinkowskiToDot
      d n)

@[simp]
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_apply_gram
    (d n : ℕ) (ij : Fin n × Fin n) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
        (MvPolynomial.X (Sum.inl ij)) =
      (MvPolynomial.X (Sum.inl ij) :
        standardSOInvariantCoordinateRing (d + 1) n) := by
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]

@[simp]
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_apply_det
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
        (MvPolynomial.X (Sum.inr ι)) =
      MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
        (MvPolynomial.X (Sum.inr ι) :
          standardSOInvariantCoordinateRing (d + 1) n) := by
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]

/-- Source symmetry relation generators map exactly to the standard-dot
symmetry generators. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_map_symmetryRelation
    (d n : ℕ) (ij : Fin n × Fin n) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
      (MvPolynomial.X (Sum.inl ij) -
        MvPolynomial.X (Sum.inl (ij.2, ij.1)) :
          sourceOrientedInvariantCoordinateRing d n) =
      (MvPolynomial.X (Sum.inl ij) -
        MvPolynomial.X (Sum.inl (ij.2, ij.1)) :
          standardSOInvariantCoordinateRing (d + 1) n) := by
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]

/-- Source rank-minor relation generators map exactly to the standard-dot
rank-minor generators. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_map_rankMinorRelation
    (d n : ℕ)
    (ι : Fin (d + 2) ↪ Fin n) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
      (Matrix.det
        (fun a b : Fin (d + 2) =>
          (MvPolynomial.X (Sum.inl (ι a, ι b)) :
            sourceOrientedInvariantCoordinateRing d n))) =
      (Matrix.det
        (fun a b : Fin (d + 2) =>
          (MvPolynomial.X (Sum.inl (ι a, ι b)) :
            standardSOInvariantCoordinateRing (d + 1) n))) := by
  rw [AlgEquiv.map_det, AlgEquiv.mapMatrix_apply]
  change Matrix.det
      (fun a b : Fin (d + 2) =>
        sourceMinkowskiToDotInvariantCoordinateEquiv d n
          (MvPolynomial.X (Sum.inl (ι a, ι b)))) = _
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]

/-- Source alternation generators map to the inverse determinant scale times
the standard-dot alternation generators. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_map_alternationRelation
    (d n : ℕ)
    (p : (Fin (d + 1) ↪ Fin n) × Equiv.Perm (Fin (d + 1))) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
      (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
        MvPolynomial.C (p.2.sign : ℂ) *
          (MvPolynomial.X (Sum.inr p.1) :
            sourceOrientedInvariantCoordinateRing d n)) =
      MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
        ((MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
          MvPolynomial.C (p.2.sign : ℂ) *
            (MvPolynomial.X (Sum.inr p.1) :
              standardSOInvariantCoordinateRing (d + 1) n))) := by
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]
  ring

/-- Multiplying the mapped source alternation generator by the forward
determinant scale recovers the standard-dot alternation generator. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_detScale_mul_alternationRelation
    (d n : ℕ)
    (p : (Fin (d + 1) ↪ Fin n) × Equiv.Perm (Fin (d + 1))) :
    MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
      sourceMinkowskiToDotInvariantCoordinateEquiv d n
        (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
          MvPolynomial.C (p.2.sign : ℂ) *
            (MvPolynomial.X (Sum.inr p.1) :
              sourceOrientedInvariantCoordinateRing d n)) =
      (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
        MvPolynomial.C (p.2.sign : ℂ) *
          (MvPolynomial.X (Sum.inr p.1) :
            standardSOInvariantCoordinateRing (d + 1) n)) := by
  rw [sourceMinkowskiToDotInvariantCoordinateEquiv_map_alternationRelation]
  have hCprod :
      MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
          (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) :
            standardSOInvariantCoordinateRing (d + 1) n) = 1 := by
    rw [← map_mul, sourceMinkowskiToDotDetScale_mul_invDetScale]
    simp
  calc
    MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
        (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
          (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
            MvPolynomial.C (p.2.sign : ℂ) *
              (MvPolynomial.X (Sum.inr p.1) :
                standardSOInvariantCoordinateRing (d + 1) n)))
        =
          (MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
            MvPolynomial.C (sourceMinkowskiToDotInvDetScale d)) *
            (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
              MvPolynomial.C (p.2.sign : ℂ) *
                (MvPolynomial.X (Sum.inr p.1) :
                  standardSOInvariantCoordinateRing (d + 1) n)) := by
          ring
    _ = MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
        MvPolynomial.C (p.2.sign : ℂ) *
          (MvPolynomial.X (Sum.inr p.1) :
            standardSOInvariantCoordinateRing (d + 1) n) := by
          rw [hCprod]
          ring

/-- Source Cauchy-Binet generators map exactly to standard-dot Cauchy-Binet
generators; the Minkowski metric determinant cancels the two inverse
determinant scales. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_map_cauchyBinetRelation
    (d n : ℕ)
    (p : (Fin (d + 1) ↪ Fin n) × (Fin (d + 1) ↪ Fin n)) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
      (Matrix.det
          (fun a b : Fin (d + 1) =>
            (MvPolynomial.X (Sum.inl (p.1 a, p.2 b)) :
              sourceOrientedInvariantCoordinateRing d n)) -
        MvPolynomial.C (minkowskiMetricDet d) *
          (MvPolynomial.X (Sum.inr p.1) :
            sourceOrientedInvariantCoordinateRing d n) *
          (MvPolynomial.X (Sum.inr p.2) :
            sourceOrientedInvariantCoordinateRing d n)) =
      (Matrix.det
          (fun a b : Fin (d + 1) =>
            (MvPolynomial.X (Sum.inl (p.1 a, p.2 b)) :
              standardSOInvariantCoordinateRing (d + 1) n)) -
        (MvPolynomial.X (Sum.inr p.1) :
          standardSOInvariantCoordinateRing (d + 1) n) *
        (MvPolynomial.X (Sum.inr p.2) :
          standardSOInvariantCoordinateRing (d + 1) n)) := by
  rw [map_sub, AlgEquiv.map_det, AlgEquiv.mapMatrix_apply]
  change Matrix.det
      (fun a b : Fin (d + 1) =>
        sourceMinkowskiToDotInvariantCoordinateEquiv d n
          (MvPolynomial.X (Sum.inl (p.1 a, p.2 b)))) -
      sourceMinkowskiToDotInvariantCoordinateEquiv d n
        (MvPolynomial.C (minkowskiMetricDet d) *
          (MvPolynomial.X (Sum.inr p.1) :
            sourceOrientedInvariantCoordinateRing d n) *
          (MvPolynomial.X (Sum.inr p.2) :
            sourceOrientedInvariantCoordinateRing d n)) = _
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]
  have hCprod :
      MvPolynomial.C (minkowskiMetricDet d) *
          MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
          (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) :
            standardSOInvariantCoordinateRing (d + 1) n) = 1 := by
    rw [← map_mul, ← map_mul,
      minkowskiMetricDet_mul_invDetScale_mul_invDetScale]
    simp
  calc
    MvPolynomial.C (minkowskiMetricDet d) *
        (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
          (MvPolynomial.X (Sum.inr p.1) :
            standardSOInvariantCoordinateRing (d + 1) n)) *
        (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
          (MvPolynomial.X (Sum.inr p.2) :
            standardSOInvariantCoordinateRing (d + 1) n))
        =
          (MvPolynomial.C (minkowskiMetricDet d) *
            MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
              MvPolynomial.C (sourceMinkowskiToDotInvDetScale d)) *
            (MvPolynomial.X (Sum.inr p.1) *
              MvPolynomial.X (Sum.inr p.2)) := by
          ring
    _ = MvPolynomial.X (Sum.inr p.1) *
        (MvPolynomial.X (Sum.inr p.2) :
          standardSOInvariantCoordinateRing (d + 1) n) := by
          rw [hCprod]
          ring

/-- Source linear syzygy generators map to the inverse determinant scale times
the standard-dot linear syzygy generators. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_map_linearSyzygyRelation
    (d n : ℕ)
    (p : Fin n × (Fin (d + 2) ↪ Fin n)) :
    sourceMinkowskiToDotInvariantCoordinateEquiv d n
      (sourceOrientedLinearSyzygyRelation d n p.1 p.2) =
      MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
        standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 := by
  unfold sourceOrientedLinearSyzygyRelation standardSOLinearSyzygyRelation
  rw [map_sum]
  simp [sourceMinkowskiToDotInvariantCoordinateEquiv,
    sourceMinkowskiToDotInvariantCoordinateRingHom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Multiplying the mapped source linear syzygy generator by the forward
determinant scale recovers the standard-dot linear syzygy generator. -/
theorem sourceMinkowskiToDotInvariantCoordinateEquiv_detScale_mul_linearSyzygyRelation
    (d n : ℕ)
    (p : Fin n × (Fin (d + 2) ↪ Fin n)) :
    MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
      sourceMinkowskiToDotInvariantCoordinateEquiv d n
        (sourceOrientedLinearSyzygyRelation d n p.1 p.2) =
      standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 := by
  rw [sourceMinkowskiToDotInvariantCoordinateEquiv_map_linearSyzygyRelation]
  have hCprod :
      MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
          (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) :
            standardSOInvariantCoordinateRing (d + 1) n) = 1 := by
    rw [← map_mul, sourceMinkowskiToDotDetScale_mul_invDetScale]
    simp
  calc
    MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
        (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
          standardSOLinearSyzygyRelation (d + 1) n p.1 p.2)
        =
          (MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
            MvPolynomial.C (sourceMinkowskiToDotInvDetScale d)) *
            standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 := by
          ring
    _ = standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 := by
          rw [hCprod]
          ring

/-- The explicit source-oriented relation ideal transports to the explicit
standard-dot `SO` relation ideal under the invariant-coordinate equivalence.
This is only generator bookkeeping; it does not use the standard `SO` SFT
kernel theorem. -/
theorem sourceOrientedRelationIdeal_transport_dot
    (d n : ℕ) :
    algEquivMapIdeal
        (sourceMinkowskiToDotInvariantCoordinateEquiv d n)
        (sourceOrientedAlgebraicRelationIdeal d n) =
      standardSOAlgebraicRelationIdeal (d + 1) n := by
  unfold algEquivMapIdeal sourceOrientedAlgebraicRelationIdeal
    standardSOAlgebraicRelationIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    unfold sourceOrientedAlgebraicRelationGenerators at hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with hx | hx
          · rcases hx with ⟨ij, rfl⟩
            simpa
              [sourceMinkowskiToDotInvariantCoordinateEquiv_map_symmetryRelation
                d n ij] using
              Ideal.subset_span (by
                unfold standardSOAlgebraicRelationGenerators
                exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ij, rfl⟩))))
          · rcases hx with ⟨ι, rfl⟩
            simpa
              [sourceMinkowskiToDotInvariantCoordinateEquiv_map_rankMinorRelation
                d n ι] using
              Ideal.subset_span (by
                unfold standardSOAlgebraicRelationGenerators
                exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ι, rfl⟩))))
        · rcases hx with ⟨p, rfl⟩
          let sourceAlt : sourceOrientedInvariantCoordinateRing d n :=
            MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
              MvPolynomial.C (p.2.sign : ℂ) *
                MvPolynomial.X (Sum.inr p.1)
          let stdAlt : standardSOInvariantCoordinateRing (d + 1) n :=
            MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
              MvPolynomial.C (p.2.sign : ℂ) *
                MvPolynomial.X (Sum.inr p.1)
          change
            sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceAlt ∈
              Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n)
          have hstd :
              stdAlt ∈
                Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n) :=
            Ideal.subset_span (by
              unfold stdAlt
              unfold standardSOAlgebraicRelationGenerators
              exact Or.inl (Or.inl (Or.inr ⟨p, rfl⟩)))
          have hmul :
              MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) * stdAlt ∈
                Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n) :=
            Ideal.mul_mem_left
              (Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n))
              (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d))
              hstd
          have hmap :
              sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceAlt =
                MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) * stdAlt := by
            unfold sourceAlt stdAlt
            exact
              sourceMinkowskiToDotInvariantCoordinateEquiv_map_alternationRelation
                d n p
          simpa [hmap] using hmul
      · rcases hx with ⟨p, rfl⟩
        simpa
          [sourceMinkowskiToDotInvariantCoordinateEquiv_map_cauchyBinetRelation
            d n p] using
          Ideal.subset_span (by
            unfold standardSOAlgebraicRelationGenerators
            exact Or.inl (Or.inr ⟨p, rfl⟩))
    · rcases hx with ⟨p, rfl⟩
      have hstd :
          standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 ∈
            Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n) :=
        Ideal.subset_span (by
          unfold standardSOAlgebraicRelationGenerators
          exact Or.inr ⟨p, rfl⟩)
      have hmul :
          MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
              standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 ∈
            Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n) :=
        Ideal.mul_mem_left
          (Ideal.span (standardSOAlgebraicRelationGenerators (d + 1) n))
          (MvPolynomial.C (sourceMinkowskiToDotInvDetScale d))
          hstd
      simpa
        [sourceMinkowskiToDotInvariantCoordinateEquiv_map_linearSyzygyRelation
          d n p] using hmul
  · rw [Ideal.span_le]
    intro y hy
    unfold standardSOAlgebraicRelationGenerators at hy
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · rcases hy with hy | hy
        · rcases hy with hy | hy
          · rcases hy with ⟨ij, rfl⟩
            refine Ideal.subset_span ?_
            refine
              ⟨MvPolynomial.X (Sum.inl ij) -
                (MvPolynomial.X (Sum.inl (ij.2, ij.1)) :
                  sourceOrientedInvariantCoordinateRing d n), ?_, ?_⟩
            · unfold sourceOrientedAlgebraicRelationGenerators
              exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ij, rfl⟩)))
            · exact
                sourceMinkowskiToDotInvariantCoordinateEquiv_map_symmetryRelation
                  d n ij
          · rcases hy with ⟨ι, rfl⟩
            refine Ideal.subset_span ?_
            refine
              ⟨Matrix.det
                (fun a b : Fin (d + 2) =>
                  (MvPolynomial.X (Sum.inl (ι a, ι b)) :
                    sourceOrientedInvariantCoordinateRing d n)), ?_, ?_⟩
            · unfold sourceOrientedAlgebraicRelationGenerators
              exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ι, rfl⟩)))
            · simpa using
                sourceMinkowskiToDotInvariantCoordinateEquiv_map_rankMinorRelation
                  d n ι
        · rcases hy with ⟨p, rfl⟩
          let I : Ideal (standardSOInvariantCoordinateRing (d + 1) n) :=
            Ideal.span
              ((sourceMinkowskiToDotInvariantCoordinateEquiv d n).toRingHom ''
                sourceOrientedAlgebraicRelationGenerators d n)
          let sourceAlt : sourceOrientedInvariantCoordinateRing d n :=
            MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
              MvPolynomial.C (p.2.sign : ℂ) *
                MvPolynomial.X (Sum.inr p.1)
          have hsourceAlt :
              sourceAlt ∈ sourceOrientedAlgebraicRelationGenerators d n := by
            unfold sourceAlt sourceOrientedAlgebraicRelationGenerators
            exact Or.inl (Or.inl (Or.inr ⟨p, rfl⟩))
          have himage :
              sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceAlt ∈ I := by
            exact Ideal.subset_span ⟨sourceAlt, hsourceAlt, rfl⟩
          have hscaled :
              MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
                  sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceAlt ∈
                I :=
            Ideal.mul_mem_left I _ himage
          have hEq :
              MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
                  sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceAlt =
                (MvPolynomial.X (Sum.inr (p.2.toEmbedding.trans p.1)) -
                  MvPolynomial.C (p.2.sign : ℂ) *
                    (MvPolynomial.X (Sum.inr p.1) :
                      standardSOInvariantCoordinateRing (d + 1) n)) := by
            unfold sourceAlt
            exact
              sourceMinkowskiToDotInvariantCoordinateEquiv_detScale_mul_alternationRelation
                d n p
          simpa [I, hEq] using hscaled
      · rcases hy with ⟨p, rfl⟩
        refine Ideal.subset_span ?_
        refine
          ⟨Matrix.det
              (fun a b : Fin (d + 1) =>
                (MvPolynomial.X (Sum.inl (p.1 a, p.2 b)) :
                  sourceOrientedInvariantCoordinateRing d n)) -
            MvPolynomial.C (minkowskiMetricDet d) *
              (MvPolynomial.X (Sum.inr p.1) :
                sourceOrientedInvariantCoordinateRing d n) *
              (MvPolynomial.X (Sum.inr p.2) :
                sourceOrientedInvariantCoordinateRing d n), ?_, ?_⟩
        · unfold sourceOrientedAlgebraicRelationGenerators
          exact Or.inl (Or.inr ⟨p, rfl⟩)
        · simpa using
            sourceMinkowskiToDotInvariantCoordinateEquiv_map_cauchyBinetRelation
              d n p
    · rcases hy with ⟨p, rfl⟩
      let I : Ideal (standardSOInvariantCoordinateRing (d + 1) n) :=
        Ideal.span
          ((sourceMinkowskiToDotInvariantCoordinateEquiv d n).toRingHom ''
            sourceOrientedAlgebraicRelationGenerators d n)
      let sourceLin : sourceOrientedInvariantCoordinateRing d n :=
        sourceOrientedLinearSyzygyRelation d n p.1 p.2
      have hsourceLin :
          sourceLin ∈ sourceOrientedAlgebraicRelationGenerators d n := by
        unfold sourceLin sourceOrientedAlgebraicRelationGenerators
        exact Or.inr ⟨p, rfl⟩
      have himage :
          sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceLin ∈ I := by
        exact Ideal.subset_span ⟨sourceLin, hsourceLin, rfl⟩
      have hscaled :
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
              sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceLin ∈ I :=
        Ideal.mul_mem_left I _ himage
      have hEq :
          MvPolynomial.C (sourceMinkowskiToDotDetScale d) *
              sourceMinkowskiToDotInvariantCoordinateEquiv d n sourceLin =
            standardSOLinearSyzygyRelation (d + 1) n p.1 p.2 := by
        unfold sourceLin
        exact
          sourceMinkowskiToDotInvariantCoordinateEquiv_detScale_mul_linearSyzygyRelation
            d n p
      simpa [I, hEq] using hscaled

end BHW
