import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedAdjacentNormalForm
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry

/-!
# One Spacelike Reduced Difference as a PET Boundary Point

This file records the one-variable Ruelle/Jost geometry leaf used by the
Theorem 2 locality route.  A real spacelike vector is realized as the reduced
successive difference of an absolute point in the permuted extended tube.  The
proof follows the classical one-point quadric-orbit step: normalize the
spacelike vector to the Lorentz orbit of `i sqrt(q) e_0`, then put the same
forward-tube seed in both full difference-coordinate slots.
-/

open scoped Classical
open Complex Topology Matrix LorentzLieGroup

noncomputable section

namespace OSReconstruction

open BHW

/-- A real spacelike one-difference configuration lies on the reduced
permuted-extended-tube boundary.

This is the one-variable Jost/Ruelle geometric step: the positive Minkowski
quadratic form gives a Lorentz-orbit representative of `i sqrt(q) e_0`; using
that seed in both absolute difference-coordinate slots gives an absolute PET
point whose reduced difference is the prescribed real spacelike vector. -/
theorem oneSpacelikeReducedPET_succ
    (m : ℕ) (v : Fin (m + 2) → ℝ)
    (hv : 0 <
      ∑ μ : Fin (m + 2), minkowskiSignature (m + 1) μ * v μ ^ 2) :
    (fun _ : Fin 1 => fun μ : Fin (m + 2) => (v μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN (m + 1) 1 := by
  let q : ℝ := ∑ μ : Fin (m + 2), minkowskiSignature (m + 1) μ * v μ ^ 2
  let r : ℝ := Real.sqrt q
  let c : ℂ := (r : ℂ) * Complex.I
  let seed : Fin (m + 2) → ℂ := fun μ => if μ = 0 then c else 0
  let diffs : Fin 2 → Fin (m + 2) → ℂ := fun _ => seed
  let w : Fin 2 → Fin (m + 2) → ℂ := (BHW.diffCoordEquiv 2 (m + 1)).symm diffs
  let ztarget : Fin 1 → Fin (m + 2) → ℂ := fun _ μ => (v μ : ℂ)
  have hq_pos : 0 < q := by simpa [q] using hv
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos hq_pos
  have hr_sq : r ^ 2 = q := Real.sq_sqrt (le_of_lt hq_pos)
  have hc_ne : c ≠ 0 := by
    intro hc
    have hc_im : c.im = 0 := by rw [hc]; simp
    have : r = 0 := by simpa [c] using hc_im
    exact (ne_of_gt hr_pos) this
  have hquad :
      ztarget ∈ BHW.onePointQuadricSet_wScalarE0 (m := m) c := by
    change
      BHW.minkowskiColQuadric (m := m) (fun μ => ztarget 0 μ) = -(c ^ 2)
    have hleft :
        BHW.minkowskiColQuadric (m := m) (fun μ => ztarget 0 μ) = (q : ℂ) := by
      simp [BHW.minkowskiColQuadric, ztarget, q]
    have hc_sq : c ^ 2 = -(q : ℂ) := by
      calc
        c ^ 2 = ((r : ℂ) * Complex.I) ^ 2 := rfl
        _ = -((r : ℂ) ^ 2) := by
          rw [mul_pow, Complex.I_sq]
          ring
        _ = -((r ^ 2 : ℝ) : ℂ) := by norm_num
        _ = -(q : ℂ) := by rw [hr_sq]
    rw [hleft, hc_sq]
    ring
  rcases BHW.onePointQuadricSet_subset_orbit_wScalarE0 (m := m) c hc_ne hquad
    with ⟨Λ, hΛ⟩
  have hΛ_seed : BHW.complexLorentzAction (d := m + 1) (n := 1) Λ
      (BHW.wScalarE0 (m := m) c) = ztarget := by
    simpa using hΛ
  have hseed_eq : seed = BHW.wScalarE0 (m := m) c 0 := by
    ext μ
    simp [seed, BHW.wScalarE0]
  have hseed_const_eq :
      (fun _ : Fin 1 => BHW.wScalarE0 (m := m) c 0) =
        BHW.wScalarE0 (m := m) c := by
    ext k μ
    fin_cases k
    rfl
  have hseed_cone :
      BHW.InOpenForwardCone (m + 1) (fun μ => (seed μ).im) := by
    constructor
    · simpa [seed, c, r] using hr_pos
    · have hsum :
          (∑ μ : Fin (m + 2),
              minkowskiSignature (m + 1) μ * (seed μ).im ^ 2) = -(r ^ 2) := by
        rw [Fin.sum_univ_succ]
        simp [seed, c, minkowskiSignature]
      rw [hsum]
      exact neg_lt_zero.mpr (sq_pos_of_ne_zero (ne_of_gt hr_pos))
  have hdiffs_forward : diffs ∈ BHW.ProductForwardCone (m + 1) 2 := by
    intro k
    simpa [diffs] using hseed_cone
  have hw_forward : w ∈ BHW.ForwardTube (m + 1) 2 := by
    simpa [w, BHW.forwardTube_eq_diffCoord_preimage (n := 2) (d := m + 1)]
      using hdiffs_forward
  let z : Fin 2 → Fin (m + 2) → ℂ :=
    BHW.complexLorentzAction (d := m + 1) (n := 2) Λ w
  have hz_pet : z ∈ BHW.PermutedExtendedTube (m + 1) 2 := by
    have hz_ext : z ∈ BHW.ExtendedTube (m + 1) 2 := by
      refine Set.mem_iUnion.mpr ⟨Λ, w, hw_forward, rfl⟩
    exact BHW.extendedTube_subset_permutedExtendedTube hz_ext
  refine ⟨z, hz_pet, ?_⟩
  have hred_w :
      BHW.reducedDiffMap 2 (m + 1) w =
        (fun _ : Fin 1 => seed) := by
    ext j μ
    fin_cases j
    change (BHW.diffCoordEquiv 2 (m + 1) w) 1 μ = seed μ
    have hdiff_full : BHW.diffCoordEquiv 2 (m + 1) w = diffs :=
      (BHW.diffCoordEquiv 2 (m + 1)).apply_symm_apply diffs
    rw [hdiff_full]
  calc
    BHW.reducedDiffMap 2 (m + 1) z
        = BHW.complexLorentzAction (d := m + 1) (n := 1) Λ
            (BHW.reducedDiffMap 2 (m + 1) w) := by
          simpa [z] using BHW.reducedDiffMap_action (d := m + 1) (n := 2) Λ w
    _ = BHW.complexLorentzAction (d := m + 1) (n := 1) Λ
            (fun _ : Fin 1 => seed) := by rw [hred_w]
    _ = BHW.complexLorentzAction (d := m + 1) (n := 1) Λ
            (fun _ : Fin 1 => BHW.wScalarE0 (m := m) c 0) := by rw [hseed_eq]
    _ = BHW.complexLorentzAction (d := m + 1) (n := 1) Λ
            (BHW.wScalarE0 (m := m) c) := by rw [hseed_const_eq]
    _ = ztarget := hΛ_seed

/-- Same one-difference PET leaf, stated in the Wightman spacelike predicate
used by locality hypotheses. -/
theorem oneSpacelikeReducedPET_of_isSpacelike_succ
    (m : ℕ) (v : Fin (m + 2) → ℝ)
    (hv : MinkowskiSpace.IsSpacelike (m + 1) v) :
    (fun _ : Fin 1 => fun μ : Fin (m + 2) => (v μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN (m + 1) 1 := by
  apply oneSpacelikeReducedPET_succ (m := m) (v := v)
  simpa [MinkowskiSpace.IsSpacelike, MinkowskiSpace.minkowskiNormSq,
    MinkowskiSpace.minkowskiInner, MinkowskiSpace.metricSignature,
    minkowskiSignature, sq] using hv

/-- Same one-difference PET leaf, with the dimension stated directly under
the ambient nonzero-dimensionality hypothesis used by the locality files. -/
theorem oneSpacelikeReducedPET_of_isSpacelike
    [NeZero d]
    (v : SpacetimeDim d)
    (hv : MinkowskiSpace.IsSpacelike d v) :
    (fun _ : Fin 1 => fun μ : Fin (d + 1) => (v μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d 1 := by
  have hd0 : d ≠ 0 := NeZero.ne d
  cases d with
  | zero =>
      exact False.elim (hd0 rfl)
  | succ M =>
      simpa using
        oneSpacelikeReducedPET_of_isSpacelike_succ
          (m := M) (v := v) hv

/-- The selected adjacent spacelike coordinate of a many-point reduced edge is
itself a one-difference PET boundary point.

This is the part of the Ruelle/Jost geometry supplied by the one-spacelike
orbit lemma.  It deliberately does not claim that the whole many-point reduced
configuration lies in the reduced PET; the remaining theorem-2 locality step is
the local mixed-tube/EOW patching around this selected coordinate. -/
theorem adjacentReducedEdge_selectedCoord_oneSpacelikeReducedPET_succ
    (M m : ℕ)
    (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain (M + 1) m)
    (hξ : ξ ∈ reducedSpacelikeSwapEdge
      (d := M + 1) m i ⟨i.val + 1, hi⟩) :
    (fun _ : Fin 1 => fun μ : Fin (M + 2) =>
      (ξ ⟨i.val, by omega⟩ μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN (M + 1) 1 := by
  have hsp :
      MinkowskiSpace.IsSpacelike (M + 1) (ξ ⟨i.val, by omega⟩) := by
    exact
      (mem_reducedSpacelikeSwapEdge_adjacent_iff
        (d := M + 1) m i hi ξ).1 hξ
  exact
    oneSpacelikeReducedPET_of_isSpacelike_succ
      (m := M) (v := ξ ⟨i.val, by omega⟩) hsp

/-- Dimension-generic form of the selected-coordinate PET leaf for a reduced
adjacent spacelike edge. -/
theorem adjacentReducedEdge_selectedCoord_oneSpacelikeReducedPET
    [NeZero d]
    {m : ℕ}
    (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m)
    (hξ : ξ ∈ reducedSpacelikeSwapEdge
      (d := d) m i ⟨i.val + 1, hi⟩) :
    (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
      (ξ ⟨i.val, by omega⟩ μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d 1 := by
  have hsp :
      MinkowskiSpace.IsSpacelike d (ξ ⟨i.val, by omega⟩) := by
    exact
      (mem_reducedSpacelikeSwapEdge_adjacent_iff
        (d := d) m i hi ξ).1 hξ
  exact oneSpacelikeReducedPET_of_isSpacelike (d := d)
    (ξ ⟨i.val, by omega⟩) hsp

/-- In reduced frozen-spectator normal coordinates, the selected spacelike
normal coordinate is a one-difference reduced PET boundary point. -/
theorem AdjacentNormal.reducedSelectedCoord_oneSpacelikeReducedPET
    [NeZero d]
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩)
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩) :
    (fun _ : Fin 1 => fun μ : Fin (d + 1) => (p.1 μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d 1 := by
  exact oneSpacelikeReducedPET_of_isSpacelike (d := d) p.1 (by
    simpa [AdjacentNormal.reducedSelectedSpacelike] using hp)

end OSReconstruction
