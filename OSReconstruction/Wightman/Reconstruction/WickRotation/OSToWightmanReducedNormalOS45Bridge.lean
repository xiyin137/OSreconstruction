import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSide
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedNormalEOW
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz

/-!
# Reduced Normal to OS45 Common-Edge Coordinates

This file records the concrete coordinate bridge needed by the local
Jost/Ruelle step in the OS reconstruction locality proof.  A reduced adjacent
normal point is represented by fixing the discarded pair center to zero,
reconstructing an absolute source configuration, and then passing to the OS45
flat common-edge chart.

The lemmas below do not assert the missing analytic branch data.  They expose
the exact remaining leaf: construct a Figure-2-4 source patch containing this
absolute representative.  Once that is supplied, the induced reduced-normal
collar is open and the two OS45 real branch domains contain the real collar.
-/

open scoped Classical NNReal

noncomputable section

namespace SCV

/-- Complexify a real continuous linear coordinate map by applying it to real
and imaginary parts separately. -/
noncomputable def realCLMComplexification {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ)) :
    ComplexChartSpace q →L[ℂ] ComplexChartSpace r where
  toFun := fun z a =>
    (L (fun b => (z b).re) a : ℂ) +
      Complex.I * (L (fun b => (z b).im) a : ℂ)
  map_add' := by
    intro z w
    ext a
    change
      (L ((fun b => (z b).re) + fun b => (w b).re) a : ℂ) +
          Complex.I *
            (L ((fun b => (z b).im) + fun b => (w b).im) a : ℂ) =
        ((L (fun b => (z b).re) a : ℂ) +
            Complex.I * (L (fun b => (z b).im) a : ℂ)) +
          ((L (fun b => (w b).re) a : ℂ) +
            Complex.I * (L (fun b => (w b).im) a : ℂ))
    rw [map_add, map_add]
    simp [Pi.add_apply]
    ring_nf
  map_smul' := by
    intro c z
    ext a
    change
      (L (c.re • (fun b => (z b).re) -
            c.im • (fun b => (z b).im)) a : ℂ) +
          Complex.I *
            (L (c.re • (fun b => (z b).im) +
              c.im • (fun b => (z b).re)) a : ℂ) =
        c * ((L (fun b => (z b).re) a : ℂ) +
          Complex.I * (L (fun b => (z b).im) a : ℂ))
    rw [map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  cont := by
    fun_prop

@[simp]
theorem realCLMComplexification_realEmbed {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x : Fin q → ℝ) :
    realCLMComplexification L (realEmbed x) = realEmbed (L x) := by
  ext a
  change
    (L x a : ℂ) + Complex.I * (L (0 : Fin q → ℝ) a : ℂ) =
      (L x a : ℂ)
  rw [map_zero]
  simp

/-- Complexification sends a real line with positive imaginary direction to the
corresponding image real line. -/
theorem realCLMComplexification_real_add_imag {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x η : Fin q → ℝ) (ε : ℝ) :
    realCLMComplexification L
        (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) =
      fun b => (L x b : ℂ) + (ε : ℂ) * (L η b : ℂ) * Complex.I := by
  ext b
  change
    (L (fun a =>
        ((x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I).re) b : ℂ) +
      Complex.I *
        (L (fun a =>
          ((x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I).im) b : ℂ) =
    (L x b : ℂ) + (ε : ℂ) * (L η b : ℂ) * Complex.I
  have hη : (fun a => ε * η a) = ε • η := by
    ext a
    simp [Pi.smul_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    hη, map_smul]
  ring_nf

/-- Complexification sends a real line with negative imaginary direction to the
corresponding image real line. -/
theorem realCLMComplexification_real_sub_imag {q r : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin r → ℝ))
    (x η : Fin q → ℝ) (ε : ℝ) :
    realCLMComplexification L
        (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) =
      fun b => (L x b : ℂ) - (ε : ℂ) * (L η b : ℂ) * Complex.I := by
  ext b
  change
    (L (fun a =>
        ((x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I).re) b : ℂ) +
      Complex.I *
        (L (fun a =>
          ((x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I).im) b : ℂ) =
    (L x b : ℂ) - (ε : ℂ) * (L η b : ℂ) * Complex.I
  have hηneg : (fun a => -(ε * η a)) = (-ε) • η := by
    ext a
    simp [Pi.smul_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    hηneg, map_smul]
  ring_nf

end SCV

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The canonical OS45 flat source-side direction becomes the canonical reduced
imaginary direction after quotienting by reduced differences. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) =
      fun k μ =>
        canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  ext k μ
  have h :=
    congrFun
      (congrFun
        (BHW.reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id
          (d := d) m) k) μ
  have hdir :
      BHW.reducedDiffMap (m + 1) d
          (fun r ν =>
            (canonicalForwardConeDirection (d := d) (m + 1) r ν : ℂ)) k μ =
        canonicalReducedDirectionC (d := d) m k μ := by
    exact
      congrFun
        (congrFun
          (canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
            (d := d) m) k) μ
  calc
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) k μ =
        BHW.reducedDiffMap (m + 1) d
          (fun r ν =>
            (canonicalForwardConeDirection (d := d) (m + 1) r ν : ℂ)) k μ *
          Complex.I := h
    _ = canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
      rw [hdir]

/-- Canonical identity-labelled OS45 source-side paths descend to the canonical
reduced side-height ray. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_canonical_id_affine
    (m : ℕ) (ε : ℝ) (u : NPointDomain d (m + 1)) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))) u) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) 0
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))) u) +
        (ε : ℂ) •
          (fun k μ =>
            canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine]
  rw [reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id_eq
    (d := d) m]

namespace AdjacentNormal

omit [NeZero d] in
/-- Insert the discarded pair center as zero. -/
noncomputable def reducedNormalZeroCenterCLM
    {m : ℕ} (i j : Fin (m + 1)) :
    ReducedSpace d m i j →L[ℝ] Space d (m + 1) i j :=
  (0 : ReducedSpace d m i j →L[ℝ] SpacetimeDim d).prod
    (ContinuousLinearMap.id ℝ (ReducedSpace d m i j))

omit [NeZero d] in
@[simp]
theorem reducedNormalZeroCenterCLM_apply
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) :
    reducedNormalZeroCenterCLM (d := d) i j p =
      ((0 : SpacetimeDim d), p) := by
  rfl

omit [NeZero d] in
/-- Reconstruct the absolute source representative of a flattened reduced
normal point, with the selected pair center fixed at zero. -/
noncomputable def reducedNormalAbsoluteSectionCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) →L[ℝ] NPointDomain d (m + 1) :=
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := reducedAdjacent_succ_ne i hi
  ((coordCLE (d := d) i j hij).symm.toContinuousLinearMap).comp
    ((reducedNormalZeroCenterCLM (d := d) i j).comp
      ((reducedNormalFlattenCLE (d := d) i j).symm.toContinuousLinearMap))

omit [NeZero d] in
@[simp]
theorem reducedNormalAbsoluteSectionCLM_apply
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalAbsoluteSectionCLM (d := d) i hi u =
      coordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d),
          (reducedNormalFlattenCLE
            (d := d) i ⟨i.val + 1, hi⟩).symm u) := by
  rfl

omit [NeZero d] in
@[simp]
theorem reducedNormalAbsoluteSectionCLM_apply_flatten
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalAbsoluteSectionCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p) =
      coordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d), p) := by
  simp

omit [NeZero d] in
/-- The OS45 flat common-edge coordinates associated to a flattened reduced
normal point. -/
noncomputable def reducedNormalToOS45CommonEdgeFlatCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) →L[ℝ]
      BHW.OS45FlatCommonChartReal d (m + 1) :=
  ((BHW.os45CommonEdgeFlatCLE d (m + 1)
      (1 : Equiv.Perm (Fin (m + 1)))).toContinuousLinearMap).comp
    (reducedNormalAbsoluteSectionCLM (d := d) i hi)

omit [NeZero d] in
/-- Complex-linear extension of the reduced-normal to OS45 flat common-edge
coordinate map. -/
noncomputable def reducedNormalToOS45CommonEdgeComplexCLM
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    SCV.ComplexChartSpace ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
  SCV.realCLMComplexification
    (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)

omit [NeZero d] in
@[simp]
theorem reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (SCV.realEmbed u) =
      SCV.realEmbed
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) := by
  exact
    SCV.realCLMComplexification_realEmbed
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi) u

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeComplexCLM_upperRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (reducedNormalUpperCanonicalRay (d := d) i hi p ε) =
      fun a =>
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p) a : ℂ) +
          (ε : ℂ) *
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
            Complex.I := by
  simpa [reducedNormalToOS45CommonEdgeComplexCLM,
    reducedNormalUpperCanonicalRay] using
    SCV.realCLMComplexification_real_add_imag
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      (reducedNormalFlatCanonicalDirection (d := d) i hi) ε

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeComplexCLM_lowerRay
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
        (reducedNormalLowerCanonicalRay (d := d) i hi p ε) =
      fun a =>
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
            (reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p) a : ℂ) -
          (ε : ℂ) *
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
              (reducedNormalFlatCanonicalDirection (d := d) i hi) a : ℂ) *
            Complex.I := by
  simpa [reducedNormalToOS45CommonEdgeComplexCLM,
    reducedNormalLowerCanonicalRay] using
    SCV.realCLMComplexification_real_sub_imag
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi)
      (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
      (reducedNormalFlatCanonicalDirection (d := d) i hi) ε

set_option maxHeartbeats 1200000 in
omit [NeZero d] in
/-- The signed OS45 source-side direction induced by the reduced-normal
canonical flat direction descends to the signed canonical reduced imaginary
direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_reducedNormalCanonical_eq
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (sgn : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn η) =
      fun k μ =>
        (sgn : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
          Complex.I := by
  intro η
  ext k μ
  have hdiv_succ :
      (finProdFinEquiv
        ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).divNat =
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).1 =
        (⟨k.val + 1, by omega⟩ : Fin (m + 1))
    simp
  have hmod_succ :
      (finProdFinEquiv
        ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  have hdiv_curr :
      (finProdFinEquiv
        ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).divNat =
        (⟨k.val, by omega⟩ : Fin (m + 1)) := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).1 =
        (⟨k.val, by omega⟩ : Fin (m + 1))
    simp
  have hmod_curr :
      (finProdFinEquiv
        ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  have hdir :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            ((0 : SpacetimeDim d),
              (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi))
                (canonicalReducedDirection (d := d) m))
            ⟨k.val + 1, by omega⟩ μ -
          coordInv (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)
            ((0 : SpacetimeDim d),
              (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi))
                (canonicalReducedDirection (d := d) m))
            ⟨k.val, by omega⟩ μ =
        canonicalReducedDirection (d := d) m k μ := by
    have hleft :=
      reducedCoordInv_left (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        (canonicalReducedDirection (d := d) m)
    have h :=
      congrFun (congrFun hleft k) μ
    simpa [reducedCoordInv, reducedCoordCLE, BHW.reducedDiffMapReal_apply]
      using h
  have hdirC :
      ((coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val + 1, by omega⟩ μ : ℂ) -
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val, by omega⟩ μ : ℂ)) =
        (canonicalReducedDirection (d := d) m k μ : ℂ) := by
    exact_mod_cast hdir
  simp only [BHW.reducedDiffMap_eq_successive_differences]
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45FlatCommonChartSourceSideDirection, η,
      reducedNormalToOS45CommonEdgeFlatCLM,
      reducedNormalFlatCanonicalDirection,
      BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply,
      BHW.unflattenCfg, flattenCLEquivReal_apply,
      Pi.smul_apply, canonicalReducedDirectionC,
      hdiv_succ, hmod_succ, hdiv_curr, hmod_curr]
    rw [← hdirC]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  · simp [BHW.os45FlatCommonChartSourceSideDirection, η,
      reducedNormalToOS45CommonEdgeFlatCLM,
      reducedNormalFlatCanonicalDirection,
      BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply,
      BHW.unflattenCfg, flattenCLEquivReal_apply,
      Pi.smul_apply, canonicalReducedDirectionC,
      hμ, hdiv_succ, hmod_succ, hdiv_curr, hmod_curr]
    have hsucc_eq :
        (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val + 1, by omega⟩ μ : ℂ) =
          (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d),
                (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
                  (reducedAdjacent_succ_ne i hi))
                  (canonicalReducedDirection (d := d) m))
              ⟨k.val, by omega⟩ μ : ℂ) := by
      apply sub_eq_zero.mp
      simpa [canonicalReducedDirection, BHW.safeBasepointVec, hμ]
        using hdirC
    rw [hsucc_eq]
    simp [canonicalReducedDirection, BHW.safeBasepointVec, hμ]

/-- With the reduced-normal canonical flat direction, the signed OS45 source-side
path is an affine reduced ray in the signed canonical reduced imaginary
direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_reducedNormalCanonical_affine
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (sgn ε : ℝ) (u : NPointDomain d (m + 1)) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn ε η u) =
      BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) sgn 0 η u) +
        (ε : ℂ) •
          (fun k μ =>
            (sgn : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
              Complex.I) := by
  intro η
  rw [BHW.reducedDiffMap_os45FlatCommonChartSourceSide_affine]
  rw [reducedDiffMap_os45FlatCommonChartSourceSideDirection_reducedNormalCanonical_eq
    (d := d) (i := i) (hi := hi) sgn]

/-- The upper reduced-normal canonical ray is the OS45 source-side branch
evaluation with the flat source point translated by `-εη`.

This is only a coordinate normal form for the OS-I `(4.14)` moving-source
transfer: the analytic comparison with the canonical reduced boundary branch is
still the remaining proof leaf. -/
theorem reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.os45FlatCommonChartSourceSide d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) := by
  intro η x0 uε
  rw [reducedNormalToOS45CommonEdgeComplexCLM_upperRay]
  change BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
      (1 : Equiv.Perm (Fin (m + 1)))
      (fun a => (x0 a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) = _
  rw [show (fun a => (x0 a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) =
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) uε + ((1 : ℝ) * ε) • η) a : ℂ) +
          ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) by
    ext a
    simp [uε, sub_eq_add_neg, Pi.smul_apply]]
  simpa using
    BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF
      d (m + 1) OS lgc
      (1 : Equiv.Perm (Fin (m + 1)))
      (1 : Equiv.Perm (Fin (m + 1)))
      (1 : ℝ) ε η uε

/-- The lower reduced-normal canonical ray is the adjacent OS45 source-side
branch evaluation with the flat source point translated by `+εη`.

This is the signed companion to
`reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving`; the analytic
adjacent `(4.12)`/`(4.14)` source-side transfer remains explicit. -/
theorem reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) (ε : ℝ) :
    let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlatCanonicalDirection (d := d) i hi)
    let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi
        (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)
    let uε : NPointDomain d (m + 1) :=
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
        (reducedNormalToOS45CommonEdgeComplexCLM
          (d := d) i hi
          (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
      BHW.extendF (bvt_F OS lgc (m + 1))
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) := by
  intro η x0 uε
  rw [reducedNormalToOS45CommonEdgeComplexCLM_lowerRay]
  change BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (fun a => (x0 a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) = _
  rw [show (fun a => (x0 a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) =
      (fun a =>
        ((BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) uε + ((-1 : ℝ) * ε) • η) a : ℂ) +
          ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) by
    ext a
    simp [uε, sub_eq_add_neg, Pi.smul_apply]]
  simpa using
    BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF
      d (m + 1) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
      (1 : Equiv.Perm (Fin (m + 1)))
      (-1 : ℝ) ε η uε

omit [NeZero d] in
@[simp]
theorem reducedNormalToOS45CommonEdgeFlatCLM_apply
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u =
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi u) := by
  rfl

/-- The reduced-normal preimage of a Figure-2-4 source patch.  This is the
local real collar used by the support-local Ruelle construction. -/
def reducedNormalOS45SourcePatchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :=
  {u | reducedNormalAbsoluteSectionCLM (d := d) i hi u ∈ P.V}

theorem isOpen_reducedNormalOS45SourcePatchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi) :
    IsOpen (reducedNormalOS45SourcePatchPreimage
      (d := d) i hi P) := by
  exact P.V_open.preimage
    (reducedNormalAbsoluteSectionCLM (d := d) i hi).continuous

theorem reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePatchPreimage (d := d) i hi P ↔
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V := by
  simp [reducedNormalOS45SourcePatchPreimage]

/-- The reduced-normal preimage of an arbitrary source window.  This is the
local form used after a selected Jost seed has narrowed the Figure-2-4 patch to
a smaller source collar. -/
def reducedNormalOS45SourcePreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (U : Set (NPointDomain d (m + 1))) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :=
  {u | reducedNormalAbsoluteSectionCLM (d := d) i hi u ∈ U}

omit [NeZero d] in
theorem isOpen_reducedNormalOS45SourcePreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {U : Set (NPointDomain d (m + 1))}
    (hU_open : IsOpen U) :
    IsOpen (reducedNormalOS45SourcePreimage
      (d := d) i hi U) := by
  exact hU_open.preimage
    (reducedNormalAbsoluteSectionCLM (d := d) i hi).continuous

omit [NeZero d] in
theorem reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (U : Set (NPointDomain d (m + 1)))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈
        reducedNormalOS45SourcePreimage (d := d) i hi U ↔
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
  simp [reducedNormalOS45SourcePreimage]

theorem reducedNormalOS45SourcePreimage_subset_patchPreimage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V) :
    reducedNormalOS45SourcePreimage (d := d) i hi U ⊆
      reducedNormalOS45SourcePatchPreimage (d := d) i hi P := by
  intro u hu
  exact hU_sub hu

omit [NeZero d] in
theorem reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {U : Set (NPointDomain d (m + 1))}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
      BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1))) '' U := by
  exact
    ⟨reducedNormalAbsoluteSectionCLM (d := d) i hi u, hu, rfl⟩

theorem reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ) :
    reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) ↔
      u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P := by
  simpa [reducedNormalOS45SourcePatchPreimage]
    using
      BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d (m + 1) P
        (1 : Equiv.Perm (Fin (m + 1)))
        (reducedNormalAbsoluteSectionCLM (d := d) i hi u)

theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
  have hedge :
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
      (d := d) i hi P u).2 hu
  exact
    BHW.os45FlatCommonChart_real_mem_omega_id
      (d := d) hd (P := P)
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) hedge

theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePatchPreimage (d := d) i hi P) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
  have hedge :
      reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u ∈
        BHW.os45FlatCommonChartEdgeSet d (m + 1) P
          (1 : Equiv.Perm (Fin (m + 1))) :=
    (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
      (d := d) i hi P u).2 hu
  exact
    BHW.os45FlatCommonChart_real_mem_omega_adjacent
      (d := d) hd (P := P)
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u) hedge

/-- Local source-window version of
`reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id`. -/
theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V)
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) := by
  exact
    reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
      (d := d) hd (P := P) (u := u)
      (reducedNormalOS45SourcePreimage_subset_patchPreimage
        (d := d) i hi (P := P) hU_sub hu)

/-- Local source-window version of
`reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent`. -/
theorem reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
    {m : ℕ} (hd : 2 ≤ d)
    {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi}
    {U : Set (NPointDomain d (m + 1))}
    (hU_sub : U ⊆ P.V)
    {u : Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)) → ℝ}
    (hu : u ∈ reducedNormalOS45SourcePreimage (d := d) i hi U) :
    (fun a =>
      (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi u a : ℂ)) ∈
        BHW.os45FlatCommonChartOmega d (m + 1)
          (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))) := by
  exact
    reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
      (d := d) hd (P := P) (u := u)
      (reducedNormalOS45SourcePreimage_subset_patchPreimage
        (d := d) i hi (P := P) hU_sub hu)

/-- Pull an OS45 Figure-2-4 branch packet back to a local reduced-normal
collar over a source window `U ⊆ P.V`.

This is the local form needed after the Ruelle/Jost seed has been restricted to
a neighborhood of the support point.  The assumptions left visible are the
remaining analytic payload on that local source window: source common-edge
equality. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePreimage (d := d) i hi U
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePreimage (d := d) i hi hU_open
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
        (d := d) i hi U p).2 hpU
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have himage :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' U := by
      exact
        reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
          (d := d) i hi (U := U) (u := x) (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
        (d := d) hd OS lgc (P := P) (U := U) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) himage
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  refine
    ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem
      (d := d) (OS := OS) (lgc := lgc) (p := p)
      E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      hplus0 hminus0 Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv hplus_nhds hminus_nhds ?_ ?_
  · simpa [Fplus, L, σ0, q] using hplus_rep
  · simpa [Fminus, L, σadj, σ0, q] using hminus_rep

/-- Pull an OS45 Figure-2-4 branch packet back to a local reduced-normal
sign-flip comparison with asymptotic branch transfer.

This is the OS-I `(4.14)` form of
`reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn`: the two
canonical reduced branches are only required to be asymptotic to the OS45 side
branches along the pulled-back canonical rays. -/
theorem reducedNormalSignFlip_pointwise_of_OS45SourcePatchOn_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePreimage (d := d) i hi U
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePreimage (d := d) i hi hU_open
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePreimage_iff
        (d := d) i hi U p).2 hpU
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent_of_sourcePreimage
          (d := d) hd (P := P) (U := U) hU_sub
          (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have himage :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) '' U := by
      exact
        reducedNormalToOS45CommonEdgeFlatCLM_mem_sourceImage
          (d := d) i hi (U := U) (u := x) (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
        (d := d) hd OS lgc (P := P) (U := U) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) himage
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  exact
    reducedNormalSignFlip_pointwise_of_localEOW_asymptoticBranchDataOn
      (d := d) OS lgc i hi p E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      (reducedNormalFlattened_localWedge_of_openEdge_mem
        (d := d) i hi E Ωplus Ωminus Set.univ
        hΩplus_open hΩminus_open hplus0 hminus0)
      Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
      hFplus_bv hFminus_bv hplus_nhds hminus_nhds
      (by simpa [Fplus, L, σ0, q] using hplus_transfer)
      (by simpa [Fminus, L, σadj, σ0, q] using hminus_transfer)

/-- Pull a Ruelle-overlap equality seed back to the asymptotic reduced-normal
sign-flip comparison.

This is the overlap-seed version of the OS-I `(4.14)` handoff: the seed supplies
common-edge equality on a local source window, while the two side-to-canonical
ray transfers remain asymptotic hypotheses. -/
theorem reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    {W : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d), p)))) ∈ W)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let zc : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun u =>
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ0 u))
  let U : Set (NPointDomain d (m + 1)) := P.V ∩ zc ⁻¹' W
  have hzc_cont : Continuous zc := by
    exact
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm.continuous.comp
        (by
          simpa [σ0] using
            BHW.continuous_realEmbed_os45CommonEdgeRealPoint
              (d := d) (n := m + 1) σ0)
  have hU_open : IsOpen U := by
    exact P.V_open.inter (hW_open.preimage hzc_cont)
  have hU_sub : U ⊆ P.V := by
    intro u hu
    exact hu.1
  have hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
    exact ⟨hpP, by simpa [U, zc, σ0] using hzW⟩
  have hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    exact
      BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
        (d := d) hd OS lgc (P := P) (U := U) (Ucx := W)
        (by
          intro u hu
          simpa [zc, σ0, U] using hu.2)
        heq
  exact
    reducedNormalSignFlip_pointwise_of_OS45SourcePatchOn_asymptotic
      (d := d) OS lgc P U hU_open hU_sub p hpU hsource
      hplus_transfer hminus_transfer

/-- A local source representation of the zero horizontal common-edge
difference supplies the asymptotic reduced-normal sign-flip comparison.

This is the Hdiff-facing version of the reduced-normal OS45 bridge: the
proof-local Figure-2-4 germ first gives `RepresentsDistributionOn 0` on a source
window, the checked local flat EOW bridge turns that representation into the
ambient overlap seed, and the canonical-ray transfer hypotheses identify the
two OS45 side rays with the reduced canonical rays. -/
theorem reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      hU_open hU_sub hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpU)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (hU_sub (by simpa [u0] using hpU))
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- A proof-local Figure-2-4 horizontal difference germ supplies the
asymptotic reduced-normal sign-flip comparison.

This is the Hdiff-facing version of
`reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic`: the
holomorphic germ with zero Wick trace first gives the local source
representation of the horizontal common-edge difference, and the existing
reduced-normal bridge then applies the two explicit side-to-canonical ray
transfers. -/
theorem reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (U : Set (NPointDomain d (m + 1)))
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hU_nonempty : U.Nonempty)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U)
    (Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ))
    (Hdiff : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hUcx_open : IsOpen Ucx)
    (hUcx_connected : IsConnected Ucx)
    (hwick_mem :
      ∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx)
    (hcommon_mem :
      ∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx)
    (hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx)
    (hwick_pairing_zero :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ U →
        ∫ u : NPointDomain d (m + 1),
          Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0)
    (hcommon_trace :
      ∀ u ∈ U,
        Hdiff
          ((BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u))) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) U := by
    exact
      BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
        (d := d) hd OS lgc (P := P) U hU_open hU_nonempty
        Ucx Hdiff hUcx_open hUcx_connected hwick_mem hcommon_mem
        hHdiff_holo hwick_pairing_zero hcommon_trace
  exact
    reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
      (d := d) OS lgc P U hU_open hU_sub p hpU hrep
      hplus_transfer hminus_transfer

/-- Local source-representation packets on adjacent spacelike collars supply the
reduced local boundary-CLM invariant.

This is the CLM-facing Hdiff handoff.  The remaining analytic leaf is now
exactly local OS45 source data on each reduced-normal collar: a Figure-2-4
source window carrying the zero horizontal common-edge representation, together
with the two OS-I `(4.12)`--`(4.14)` side-to-canonical ray transfers. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45SourceRepresentsOn_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ U : Set (NPointDomain d (m + 1)),
                    IsOpen U ∧ U ⊆ P.V ∧
                    coordInv (d := d) i ⟨i.val + 1, hi⟩
                        (reducedAdjacent_succ_ne i hi)
                        ((0 : SpacetimeDim d),
                          reducedCoord
                            (d := d) i ⟨i.val + 1, hi⟩ η) ∈ U ∧
                    SCV.RepresentsDistributionOn
                      (0 : SchwartzMap
                        (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
                      (fun u : NPointDomain d (m + 1) =>
                        BHW.os45PulledRealBranch
                            (d := d) (n := m + 1) OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u)) -
                          BHW.os45PulledRealBranch
                            (d := d) (n := m + 1) OS lgc
                            (1 : Equiv.Perm (Fin (m + 1)))
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u))) U ∧
                    Filter.Tendsto
                      (fun ε : ℝ =>
                        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                            (1 : Equiv.Perm (Fin (m + 1)))
                            (reducedNormalToOS45CommonEdgeComplexCLM
                              (d := d) i hi
                              (reducedNormalUpperCanonicalRay (d := d) i hi
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η) ε)) -
                          canonicalReducedBranch (d := d) OS lgc m ε
                            (reducedCoordInv (d := d)
                              i ⟨i.val + 1, hi⟩
                              (reducedAdjacent_succ_ne i hi)
                              (reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η)))
                      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                      (nhds 0) ∧
                    Filter.Tendsto
                      (fun ε : ℝ =>
                        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                            (reducedNormalToOS45CommonEdgeComplexCLM
                              (d := d) i hi
                              (reducedNormalLowerCanonicalRay (d := d) i hi
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η) ε)) -
                          canonicalReducedBranch (d := d) OS lgc m ε
                            (reducedCoordInv (d := d)
                              i ⟨i.val + 1, hi⟩
                              (reducedAdjacent_succ_ne i hi)
                              (reducedSignFlip
                                (d := d) i ⟨i.val + 1, hi⟩
                                (reducedCoord
                                  (d := d) i ⟨i.val + 1, hi⟩ η))))
                      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
                      (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  exact
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ (by
        intro m i hi φ hφ_compact hφ_tsupport ξ hξ
        rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
          ⟨V, hV_open, hξV, hVlocal⟩
        refine ⟨V, hV_open, hξV, ?_⟩
        intro ψ hψ_compact hψ_tsupport η hη
        rcases hVlocal ψ hψ_compact hψ_tsupport η hη with
          ⟨P, U, hU_open, hU_sub, hpU, hrep, hplus_transfer,
            hminus_transfer⟩
        let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        let p : ReducedSpace d m i j :=
          reducedCoord (d := d) i j η
        have hpU' :
            coordInv (d := d) i j (reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ U := by
          simpa [p, j] using hpU
        have hplus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (1 : Equiv.Perm (Fin (m + 1)))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hplus_transfer
        have hminus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi)
                      (reducedSignFlip (d := d) i j p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hminus_transfer
        simpa [p, j] using
          reducedNormalSignFlip_pointwise_of_OS45SourceRepresentsOn_asymptotic
            (d := d) OS lgc P U hU_open hU_sub p hpU'
            hrep hplus_transfer' hminus_transfer')

/-- Local proof-local Hdiff germs on adjacent spacelike collars supply the
reduced local boundary-CLM invariant.

This is the active Path-2 version of the OS45 handoff.  It exposes the
remaining OS-I §4.5 payload as a genuine local holomorphic horizontal
difference germ plus the two side-to-canonical ray transfers, then uses the
checked reduced-normal sign-flip and reduced local CLM machinery. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ η, ψ η ≠ 0 →
                ∃ P : BHW.OS45Figure24CanonicalSourcePatchData
                    (d := d) hd (m + 1) i hi,
                  ∃ U : Set (NPointDomain d (m + 1)),
                    ∃ Ucx : Set (Fin (m + 1) → Fin (d + 1) → ℂ),
                      ∃ Hdiff :
                          (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
                        IsOpen U ∧ U ⊆ P.V ∧
                        coordInv (d := d) i ⟨i.val + 1, hi⟩
                            (reducedAdjacent_succ_ne i hi)
                            ((0 : SpacetimeDim d),
                              reducedCoord
                                (d := d) i ⟨i.val + 1, hi⟩ η) ∈ U ∧
                        IsOpen Ucx ∧ IsConnected Ucx ∧
                        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
                        (∀ u ∈ U,
                          (BHW.os45QuarterTurnCLE
                              (d := d) (n := m + 1)).symm
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := m + 1)
                                (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Ucx) ∧
                        DifferentiableOn ℂ Hdiff Ucx ∧
                        (∀ θ : SchwartzNPoint d (m + 1),
                          HasCompactSupport
                            (θ : NPointDomain d (m + 1) → ℂ) →
                          tsupport
                              (θ : NPointDomain d (m + 1) → ℂ) ⊆ U →
                          ∫ u : NPointDomain d (m + 1),
                            Hdiff (fun k => wickRotatePoint (u k)) *
                              θ u = 0) ∧
                        (∀ u ∈ U,
                          Hdiff
                            ((BHW.os45QuarterTurnCLE
                                (d := d) (n := m + 1)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := m + 1)
                                  (1 : Equiv.Perm (Fin (m + 1))) u))) =
                            BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (P.τ.symm *
                                  (1 : Equiv.Perm (Fin (m + 1))))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u)) -
                              BHW.os45PulledRealBranch
                                (d := d) (n := m + 1) OS lgc
                                (1 : Equiv.Perm (Fin (m + 1)))
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := m + 1)
                                    (1 : Equiv.Perm (Fin (m + 1))) u))) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            BHW.os45FlatCommonChartBranch
                                d (m + 1) OS lgc
                                (1 : Equiv.Perm (Fin (m + 1)))
                                (reducedNormalToOS45CommonEdgeComplexCLM
                                  (d := d) i hi
                                  (reducedNormalUpperCanonicalRay
                                    (d := d) i hi
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)
                                    ε)) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi)
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0) ∧
                        Filter.Tendsto
                          (fun ε : ℝ =>
                            BHW.os45FlatCommonChartBranch
                                d (m + 1) OS lgc
                                (P.τ.symm *
                                  (1 : Equiv.Perm (Fin (m + 1))))
                                (reducedNormalToOS45CommonEdgeComplexCLM
                                  (d := d) i hi
                                  (reducedNormalLowerCanonicalRay
                                    (d := d) i hi
                                    (reducedCoord
                                      (d := d) i ⟨i.val + 1, hi⟩ η)
                                    ε)) -
                              canonicalReducedBranch
                                  (d := d) OS lgc m ε
                                  (reducedCoordInv (d := d)
                                    i ⟨i.val + 1, hi⟩
                                    (reducedAdjacent_succ_ne i hi)
                                    (reducedSignFlip
                                      (d := d) i ⟨i.val + 1, hi⟩
                                      (reducedCoord
                                        (d := d) i ⟨i.val + 1, hi⟩ η))))
                          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :
                            Filter ℝ)
                          (nhds 0)) :
    _root_.OSReconstruction.ReducedLocalAdjacentBoundaryCLMInvariant
      (d := d) OS lgc χ := by
  exact
    _root_.OSReconstruction.reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ (by
        intro m i hi φ hφ_compact hφ_tsupport ξ hξ
        rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
          ⟨V, hV_open, hξV, hVlocal⟩
        refine ⟨V, hV_open, hξV, ?_⟩
        intro ψ hψ_compact hψ_tsupport η hη
        rcases hVlocal ψ hψ_compact hψ_tsupport η hη with
          ⟨P, U, Ucx, Hdiff, hU_open, hU_sub, hpU, hUcx_open,
            hUcx_connected, hwick_mem, hcommon_mem, hHdiff_holo,
            hwick_pairing_zero, hcommon_trace, hplus_transfer,
            hminus_transfer⟩
        let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        let p : ReducedSpace d m i j :=
          reducedCoord (d := d) i j η
        have hpU' :
            coordInv (d := d) i j (reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ U := by
          simpa [p, j] using hpU
        have hU_nonempty : U.Nonempty := ⟨_, hpU'⟩
        have hplus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (1 : Equiv.Perm (Fin (m + 1)))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hplus_transfer
        have hminus_transfer' :
            Filter.Tendsto
              (fun ε : ℝ =>
                BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
                    (reducedNormalToOS45CommonEdgeComplexCLM
                      (d := d) i hi
                      (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (reducedCoordInv (d := d) i j
                      (reducedAdjacent_succ_ne i hi)
                      (reducedSignFlip (d := d) i j p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) := by
          simpa [p, j] using hminus_transfer
        simpa [p, j] using
          reducedNormalSignFlip_pointwise_of_OS45HdiffGerm_asymptotic
            (d := d) OS lgc P U hU_open hU_sub hU_nonempty
            p hpU' Ucx Hdiff hUcx_open hUcx_connected
            hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero
            hcommon_trace hplus_transfer' hminus_transfer')

/-- Pull a Ruelle-overlap equality seed back to a reduced-normal branch packet.

The complex window `W` is the open connected seed produced by the
Jost/Ruelle overlap argument.  This theorem constructs the local source collar
by pulling `W` back along the OS45 common-edge chart, uses the existing Ruelle
overlap theorem to obtain source common-edge equality there, and then applies
the local reduced-normal OS45 packet constructor. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    {W : Set (Fin (m + 1) → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (coordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              ((0 : SpacetimeDim d), p)))) ∈ W)
    (heq :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let zc : NPointDomain d (m + 1) →
      Fin (m + 1) → Fin (d + 1) → ℂ := fun u =>
    (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1) σ0 u))
  let U : Set (NPointDomain d (m + 1)) := P.V ∩ zc ⁻¹' W
  have hzc_cont : Continuous zc := by
    exact
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm.continuous.comp
        (by
          simpa [σ0] using
            BHW.continuous_realEmbed_os45CommonEdgeRealPoint
              (d := d) (n := m + 1) σ0)
  have hU_open : IsOpen U := by
    exact P.V_open.inter (hW_open.preimage hzc_cont)
  have hU_sub : U ⊆ P.V := by
    intro u hu
    exact hu.1
  have hpU :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ U := by
    exact ⟨hpP, by simpa [U, zc, σ0] using hzW⟩
  have hsource :
      ∀ u ∈ U,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) := by
    exact
      BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
        (d := d) hd OS lgc (P := P) (U := U) (Ucx := W)
        (by
          intro u hu
          simpa [zc, σ0, U] using hu.2)
        heq
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatchOn
      (d := d) OS lgc P U hU_open hU_sub p hpU hsource
      hplus_rep hminus_rep

/-- Local edge pairing supplies the local overlap seed needed by the
reduced-normal OS45 branch packet.

This is the local, non-selected version of the reduced-normal handoff: the
real-edge pairing on `Vedge` produces source common-edge equality on the
source patch, the checked flat common-chart bridge supplies a Ruelle overlap
seed, and the existing reduced-normal pullback builds the canonical-ray EOW
packet.  The two canonical-ray representation formulas remain explicit because
they are the genuine OS-I `(4.12)`--`(4.14)` source-side transfer leaf. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_localEdgePairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) P.τ z ∈
              BHW.ExtendedTube d (m + 1)})
    (Vedge : Set (NPointDomain d (m + 1)))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1))
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈
          BHW.ExtendedTube d (m + 1))
    (hPairing :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) P.V :=
    BHW.os45_sourceCommonEdge_representsZero_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing (Usrc := P.V) (by intro u hu; exact hu)
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      P.V_open (by intro u hu; exact hu) hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_rep hminus_rep

/-- Local edge pairing supplies the asymptotic reduced-normal sign-flip
comparison.

This is the local-edge analogue of
`reducedNormalCanonicalRayEOWBranchDataOn_of_localEdgePairing`, with the OS-I
side-to-canonical ray comparison stated as asymptotic transfer. -/
theorem reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) P.τ z ∈
              BHW.ExtendedTube d (m + 1)})
    (Vedge : Set (NPointDomain d (m + 1)))
    (hVedge_open : IsOpen Vedge)
    (hVedge_nonempty : Vedge.Nonempty)
    (hVedge_ET :
      ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1))
    (hVedge_swapET :
      ∀ x ∈ Vedge,
        BHW.realEmbed (fun k => x (P.τ k)) ∈
          BHW.ExtendedTube d (m + 1))
    (hPairing :
      ∀ φ : SchwartzNPoint d (m + 1),
        HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
        tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
        (∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1))
              (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
          =
        ∫ x : NPointDomain d (m + 1),
            BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  have hrep :
      SCV.RepresentsDistributionOn
        (0 : SchwartzMap (NPointDomain d (m + 1)) ℂ →L[ℂ] ℂ)
        (fun u : NPointDomain d (m + 1) =>
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u)) -
            BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint
                  (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) u))) P.V :=
    BHW.os45_sourceCommonEdge_representsZero_of_localEdgePairing
      (d := d) hd OS lgc (P := P) hOverlap
      Vedge hVedge_open hVedge_nonempty hVedge_ET hVedge_swapET
      hPairing (Usrc := P.V) (by intro u hu; exact hu)
  let hSeed :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceRepresentsOn
      (d := d) hd OS lgc (P := P)
      P.V_open (by intro u hu; exact hu) hrep
      ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- Selected Jost/Ruelle data supplies the local overlap seed needed by the
reduced-normal OS45 branch packet.

This is the support-point version of the OS I Section 4.5 handoff: the
selected distributional Jost anchor and adjacent ET-overlap connectedness
produce the local Ruelle `EqOn` seed at the source point corresponding to the
reduced-normal real edge.  The remaining visible assumptions are the honest
point-local Figure-2-4 membership and the two canonical-ray representation
formulas. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_selectedJostData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      ∀ (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let Uruelle : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d (m + 1) P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    have hconn := hOverlap i hi
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, P.τ_eq, BHW.permAct] using hconn
  have hcommon_mem :
      ∀ u ∈ P.V,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈
        BHW.ruelleOverlapDomain d (m + 1) P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := m + 1) (hd := hd) (P := P)
        (subset_closure hu)
  let hSeed :=
    BHW.os45_flat_seed_of_selectedJostData
      (d := d) hd OS lgc (P := P) hOverlap hData
      (Usrc := P.V) P.V_open (by intro u hu; exact hu)
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalCanonicalRayEOWBranchDataOn_of_OS45RuelleOverlapSeed
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_rep hminus_rep

/-- Selected Jost/Ruelle data supplies the reduced-normal pointwise sign-flip
limit when the OS45 side branches are only asymptotic to the two canonical
reduced rays.

This is the selected-data analogue of
`reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic`: the selected
anchor and adjacent ET-overlap connectedness produce the local Ruelle `EqOn`
seed, while the OS-I `(4.14)` side-to-canonical ray comparisons remain in their
natural asymptotic form. -/
theorem reducedNormalSignFlip_pointwise_of_selectedJostData_asymptotic
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (hOverlap :
      ∀ (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0))
    (hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
                (reducedAdjacent_succ_ne i hi)
                (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  classical
  let u0 : NPointDomain d (m + 1) :=
    coordInv (d := d) i ⟨i.val + 1, hi⟩
      (reducedAdjacent_succ_ne i hi)
      ((0 : SpacetimeDim d), p)
  have hflat_dim : 0 < BHW.os45FlatCommonChartDim d (m + 1) :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d (m + 1) hi
  have hConeReady :=
    BHW.os45FlatCommonChartCone_eowReady d (m + 1)
  have hC_open : IsOpen (BHW.os45FlatCommonChartCone d (m + 1)) :=
    hConeReady.1
  have hC_nonempty : (BHW.os45FlatCommonChartCone d (m + 1)).Nonempty :=
    hConeReady.2.2.2.2
  let hBasis :=
    open_set_contains_basis hflat_dim
      (BHW.os45FlatCommonChartCone d (m + 1)) hC_open hC_nonempty
  let ys : Fin (BHW.os45FlatCommonChartDim d (m + 1)) →
      Fin (BHW.os45FlatCommonChartDim d (m + 1)) → ℝ :=
    Classical.choose hBasis
  have hys_mem :
      ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d (m + 1) :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  let Uruelle : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    BHW.ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_sub :
      Uruelle ⊆ BHW.ruelleOverlapDomain d (m + 1) P.τ := by
    intro z hz
    exact hz
  have hUruelle_open : IsOpen Uruelle := by
    simpa [Uruelle] using BHW.isOpen_ruelleOverlapDomain d (m + 1) P.τ
  have hUruelle_connected : IsConnected Uruelle := by
    have hconn := hOverlap i hi
    simpa [Uruelle, BHW.ruelleOverlapDomain,
      BHW.permutedExtendedTubeSector, P.τ_eq, BHW.permAct] using hconn
  have hcommon_mem :
      ∀ u ∈ P.V,
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈ Uruelle := by
    intro u hu
    change
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u)) ∈
        BHW.ruelleOverlapDomain d (m + 1) P.τ
    exact
      BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
        (d := d) (n := m + 1) (hd := hd) (P := P)
        (subset_closure hu)
  let hSeed :=
    BHW.os45_flat_seed_of_selectedJostData
      (d := d) hd OS lgc (P := P) hOverlap hData
      (Usrc := P.V) P.V_open (by intro u hu; exact hu)
      (Ucx := Uruelle) hUruelle_sub hUruelle_open hUruelle_connected
      hcommon_mem ys hys_mem hys_li u0 (by simpa [u0] using hpP)
  let W : Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    Classical.choose hSeed
  have hSeed_spec := Classical.choose_spec hSeed
  have hW_open : IsOpen W := hSeed_spec.1
  have hzW_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.unflattenCfg (m + 1) d
          (SCV.realEmbed
            (BHW.os45CommonEdgeFlatCLE d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0))) ∈ W :=
    hSeed_spec.2.2.1
  have heqW :
      Set.EqOn
        (BHW.extendF (bvt_F OS lgc (m + 1)))
        (fun z =>
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d) P.τ z))
        W :=
    hSeed_spec.2.2.2.2
  have hflat_base :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0))) =
        (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0)) := by
    have harg :
        BHW.unflattenCfg (m + 1) d
            (SCV.realEmbed
              (BHW.os45CommonEdgeFlatCLE d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u0)) =
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) u0) := by
      simpa [BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
        BHW.flattenCfgReal, flattenCLEquivReal_apply] using
        BHW.unflattenCfg_ofReal_flattenCfgReal
          (m + 1) d
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)
    exact congrArg
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm harg
  have hzW :
      (BHW.os45QuarterTurnCLE (d := d) (n := m + 1)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) u0)) ∈ W := by
    simpa [hflat_base] using hzW_flat
  exact
    reducedNormalSignFlip_pointwise_of_OS45RuelleOverlapSeed_asymptotic
      (d := d) OS lgc P p (by simpa [u0] using hpP)
      (W := W) hW_open (by simpa [u0] using hzW) heqW
      hplus_transfer hminus_transfer

/-- Pull an OS45 Figure-2-4 branch packet back to a reduced-normal collar.

This discharges the topology, holomorphy, and common-boundary-value fields of
`ReducedNormalCanonicalRayEOWBranchDataOn`.  The assumptions left visible are
exactly the remaining Jost/Ruelle payload: source common-edge equality and the
two canonical-ray representation formulas after the OS45 chart pullback. -/
def reducedNormalCanonicalRayEOWBranchDataOn_of_OS45SourcePatch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} {hi : i.val + 1 < m + 1}
    {hd : 2 ≤ d}
    (P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd (m + 1) i hi)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hpP :
      coordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)
          ((0 : SpacetimeDim d), p) ∈ P.V)
    (hsource :
      ∀ u ∈ P.V,
        BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)) =
          BHW.os45PulledRealBranch (d := d) (n := m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint
                (d := d) (n := m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) u)))
    (hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalUpperCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi) p))
    (hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (reducedNormalLowerCanonicalRay (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
              (reducedAdjacent_succ_ne i hi)
              (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p))) :
    ReducedNormalCanonicalRayEOWBranchDataOn (d := d) OS lgc i hi p := by
  let q : ℕ :=
    (d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i ⟨i.val + 1, hi⟩) *
        (d + 1)
  let σ0 : Equiv.Perm (Fin (m + 1)) := 1
  let σadj : Equiv.Perm (Fin (m + 1)) := P.τ.symm * σ0
  let L : SCV.ComplexChartSpace q →L[ℂ]
      SCV.ComplexChartSpace (BHW.os45FlatCommonChartDim d (m + 1)) :=
    reducedNormalToOS45CommonEdgeComplexCLM (d := d) i hi
  let E : Set (Fin q → ℝ) :=
    reducedNormalOS45SourcePatchPreimage (d := d) i hi P
  let Ωplus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σ0
  let Ωminus : Set (SCV.ComplexChartSpace q) :=
    L ⁻¹' BHW.os45FlatCommonChartOmega d (m + 1) σadj
  let Fplus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σ0 (L z)
  let Fminus : SCV.ComplexChartSpace q → ℂ := fun z =>
    BHW.os45FlatCommonChartBranch d (m + 1) OS lgc σadj (L z)
  let bv : (Fin q → ℝ) → ℂ := fun x => Fplus (SCV.realEmbed x)
  have hE_open : IsOpen E := by
    simpa [E] using
      isOpen_reducedNormalOS45SourcePatchPreimage (d := d) i hi P
  have hpE :
      reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p ∈ E := by
    simpa [E] using
      (reducedNormalFlatten_mem_reducedNormalOS45SourcePatchPreimage_iff
        (d := d) i hi P p).2 hpP
  have hΩplus_open : IsOpen Ωplus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σ0).preimage
        L.continuous
  have hΩminus_open : IsOpen Ωminus := by
    exact
      (BHW.isOpen_os45FlatCommonChartOmega d (m + 1) σadj).preimage
        L.continuous
  have hplus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σ0 := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_id
          (d := d) hd (P := P) (u := x) (by simpa [E] using hx)
    simpa [Ωplus] using hxΩ
  have hminus0 :
      ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    have hxΩ :
        L (SCV.realEmbed x) ∈
          BHW.os45FlatCommonChartOmega d (m + 1) σadj := by
      rw [show L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) by
        simpa [L, q] using
          reducedNormalToOS45CommonEdgeComplexCLM_realEmbed
            (d := d) i hi x]
      simpa [σadj, σ0] using
        reducedNormalToOS45CommonEdgeFlatCLM_real_mem_omega_adjacent
          (d := d) hd (P := P) (u := x) (by simpa [E] using hx)
    simpa [Ωminus] using hxΩ
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σ0).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d (m + 1) OS lgc σadj).comp
        L.differentiable.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    have hreal :
        Continuous (fun x : Fin q → ℝ => SCV.realEmbed x) := by
      simpa [SCV.realEmbed] using
        (continuous_pi fun a =>
          Complex.continuous_ofReal.comp (continuous_apply a))
    exact hFplus_diff.continuousOn.comp hreal.continuousOn hplus0
  have htrace :
      ∀ x ∈ E, Fminus (SCV.realEmbed x) = Fplus (SCV.realEmbed x) := by
    intro x hx
    have hedge :
        reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x ∈
          BHW.os45FlatCommonChartEdgeSet d (m + 1) P σ0 := by
      exact
        (reducedNormalToOS45CommonEdgeFlatCLM_mem_edgeSet_iff
          (d := d) i hi P x).2 (by simpa [E] using hx)
    have hflat :=
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eq
        (d := d) hd OS lgc (P := P) hsource
        (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) hedge
    have hL :
        L (SCV.realEmbed x) =
          SCV.realEmbed
            (reducedNormalToOS45CommonEdgeFlatCLM (d := d) i hi x) := by
      simpa [L, q] using
        reducedNormalToOS45CommonEdgeComplexCLM_realEmbed (d := d) i hi x
    simpa [Fplus, Fminus, σadj, σ0, hL] using hflat
  have hFplus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fplus
          (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    simpa [bv] using
      (hFplus_diff.continuousOn.continuousWithinAt
        (hplus0 x hx)).tendsto
  have hFminus_bv :
      ∀ x ∈ E,
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hlim :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) :=
      (hFminus_diff.continuousOn.continuousWithinAt
        (hminus0 x hx)).tendsto
    simpa [bv, htrace x hx] using hlim
  have hplus_nhds :
      Ωplus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds :
      Ωminus ∈ nhds
        (SCV.realEmbed
          (reducedNormalFlattenCLE (d := d) i ⟨i.val + 1, hi⟩ p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  refine
    ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem
      (d := d) (OS := OS) (lgc := lgc) (p := p)
      E hE_open hpE Ωplus Ωminus Set.univ
      hΩplus_open hΩminus_open isOpen_univ convex_univ Set.univ_nonempty
      hplus0 hminus0 Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv hplus_nhds hminus_nhds ?_ ?_
  · simpa [Fplus, L, σ0, q] using hplus_rep
  · simpa [Fminus, L, σadj, σ0, q] using hminus_rep

end AdjacentNormal

end OSReconstruction
