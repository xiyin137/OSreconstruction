import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedAdjacentNormalForm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedNormalEOW
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

/-- In the two-point/no-spectator chart, the inverse reduced normal coordinate
map is exactly the selected one-difference coordinate. -/
theorem AdjacentNormal.reducedCoordInv_zero_one_eq_selected
    [NeZero d]
    (p : AdjacentNormal.ReducedSpace d 1 (0 : Fin 2) (1 : Fin 2)) :
    (fun k μ => (AdjacentNormal.reducedCoordInv (d := d)
        (0 : Fin 2) (1 : Fin 2) (by decide) p k μ : ℂ)) =
      (fun _ : Fin 1 => fun μ : Fin (d + 1) => (p.1 μ : ℂ)) := by
  let ξ : NPointDomain d 1 :=
    AdjacentNormal.reducedCoordInv (d := d)
      (0 : Fin 2) (1 : Fin 2) (by decide) p
  apply funext
  intro k
  apply funext
  intro μ
  have hk0 : k = (0 : Fin 1) := by
    exact Fin.ext (by omega)
  subst k
  have hfst :
      (AdjacentNormal.reducedCoord (d := d) (0 : Fin 2) (1 : Fin 2) ξ).1 =
        p.1 := by
    simpa [ξ] using congrArg Prod.fst
      (AdjacentNormal.reducedCoordInv_right (d := d)
        (0 : Fin 2) (1 : Fin 2) (by decide) p)
  have hpair := congrFun hfst μ
  rw [AdjacentNormal.reducedCoord_fst_eq_reducedPairDiff] at hpair
  have hproj :
      reducedPairDiff (d := d) 1 (0 : Fin 2) (1 : Fin 2) ξ μ =
        ξ 0 μ := by
    have hL := congrFun
      (congrArg (fun L => L ξ)
        (reducedPairDiffCLM_adjacent_eq_proj
          (d := d) 1 (0 : Fin 2) (by decide))) μ
    simpa using hL
  change (ξ 0 μ : ℂ) = (p.1 μ : ℂ)
  rw [← hproj]
  exact_mod_cast hpair

/-- In the two-point/no-spectator case, the inverse reduced normal chart is
the selected one-difference coordinate.  Thus selected spacelikeness supplies
the full real reduced PET boundary hypothesis needed by the reduced
boundary-value extension theorem. -/
theorem AdjacentNormal.reducedCoordInv_zero_one_mem_reducedPermutedExtendedTubeN_of_selected
    [NeZero d]
    (p : AdjacentNormal.ReducedSpace d 1 (0 : Fin 2) (1 : Fin 2))
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) (0 : Fin 2) (1 : Fin 2)) :
    (fun k μ => (AdjacentNormal.reducedCoordInv (d := d)
        (0 : Fin 2) (1 : Fin 2) (by decide) p k μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d 1 := by
  let ξ : NPointDomain d 1 :=
    AdjacentNormal.reducedCoordInv (d := d)
      (0 : Fin 2) (1 : Fin 2) (by decide) p
  have hpet :
      (fun _ : Fin 1 => fun μ : Fin (d + 1) => (p.1 μ : ℂ)) ∈
        BHW.ReducedPermutedExtendedTubeN d 1 :=
    AdjacentNormal.reducedSelectedCoord_oneSpacelikeReducedPET
      (d := d) (i := (0 : Fin 2)) (hi := by decide) p hp
  have hξeq :
      (fun k μ => (ξ k μ : ℂ)) =
        (fun _ : Fin 1 => fun μ : Fin (d + 1) => (p.1 μ : ℂ)) := by
    simpa [ξ] using
      AdjacentNormal.reducedCoordInv_zero_one_eq_selected (d := d) p
  simpa [ξ, hξeq] using hpet

/-- Adjacent-index form of the two-point/no-spectator PET boundary theorem.
The hypothesis `hi` forces `i = 0`, but this statement matches the generic
adjacent theorem surfaces. -/
theorem AdjacentNormal.reducedCoordInv_noSpectator_mem_reducedPermutedExtendedTubeN_of_selected
    [NeZero d]
    (i : Fin 2) (hi : i.val + 1 < 2)
    (p : AdjacentNormal.ReducedSpace d 1 i ⟨i.val + 1, hi⟩)
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩) :
    (fun k μ => (AdjacentNormal.reducedCoordInv (d := d)
        i ⟨i.val + 1, hi⟩
        (AdjacentNormal.reducedAdjacent_succ_ne i hi) p k μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d 1 := by
  have hi0 : i = (0 : Fin 2) := by
    exact Fin.ext (by omega)
  subst i
  simpa using
    AdjacentNormal.reducedCoordInv_zero_one_mem_reducedPermutedExtendedTubeN_of_selected
      (d := d) p hp

/-- Two-point/no-spectator pointwise reduced boundary convergence at a selected
spacelike reduced-normal point, obtained from the genuine reduced PET extension
route. -/
theorem AdjacentNormal.bvt_F_reduced_two_direction_pointwise_tendsto_zero_zero_one
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := 2)
      (bvt_F_reduced (d := d) OS lgc 1))
    (p : AdjacentNormal.ReducedSpace d 1 (0 : Fin 2) (1 : Fin 2))
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) (0 : Fin 2) (1 : Fin 2)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc 1
            (fun k μ =>
              (AdjacentNormal.reducedCoordInv (d := d)
                  (0 : Fin 2) (1 : Fin 2) (by decide) p k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) 1 (Equiv.swap (0 : Fin 2) (1 : Fin 2)) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc 1
            (fun k μ =>
              (AdjacentNormal.reducedCoordInv (d := d)
                  (0 : Fin 2) (1 : Fin 2) (by decide) p k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) 1 k μ * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  exact
    bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension
      (d := d) OS lgc 1 (0 : Fin 2) (1 : Fin 2) Fred
      (AdjacentNormal.reducedCoordInv (d := d)
        (0 : Fin 2) (1 : Fin 2) (by decide) p)
      (AdjacentNormal.reducedCoordInv_zero_one_mem_reducedPermutedExtendedTubeN_of_selected
        (d := d) p hp)

/-- Adjacent-index form of the two-point/no-spectator pointwise reduced
boundary convergence theorem. -/
theorem AdjacentNormal.bvt_F_reduced_two_direction_pointwise_tendsto_zero_noSpectator
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := 2)
      (bvt_F_reduced (d := d) OS lgc 1))
    (i : Fin 2) (hi : i.val + 1 < 2)
    (p : AdjacentNormal.ReducedSpace d 1 i ⟨i.val + 1, hi⟩)
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc 1
            (fun k μ =>
              (AdjacentNormal.reducedCoordInv (d := d)
                  i ⟨i.val + 1, hi⟩
                  (AdjacentNormal.reducedAdjacent_succ_ne i hi) p k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) 1 (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc 1
            (fun k μ =>
              (AdjacentNormal.reducedCoordInv (d := d)
                  i ⟨i.val + 1, hi⟩
                  (AdjacentNormal.reducedAdjacent_succ_ne i hi) p k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) 1 k μ * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  have hi0 : i = (0 : Fin 2) := by
    exact Fin.ext (by omega)
  subst i
  simpa using
    AdjacentNormal.bvt_F_reduced_two_direction_pointwise_tendsto_zero_zero_one
      (d := d) OS lgc Fred p hp

/-- Two-point/no-spectator reduced-normal EOW branch data at a selected
spacelike point, built directly from the genuine reduced PET extension.

The plus side pulls the reduced extension back along the one-difference chart;
the minus side pulls it back after negating that one difference.  The common
real-edge boundary value is the reduced BHW permutation invariance across the
adjacent transposition. -/
theorem AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_zero_one_of_selected
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := 2)
      (bvt_F_reduced (d := d) OS lgc 1))
    (p : AdjacentNormal.ReducedSpace d 1 (0 : Fin 2) (1 : Fin 2))
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) (0 : Fin 2) (1 : Fin 2)) :
    Nonempty (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
      (d := d) OS lgc (0 : Fin 2) (by decide) p) := by
  let tail : ℕ :=
    Fintype.card (AdjacentNormal.SpectatorIndex 2 (0 : Fin 2) (1 : Fin 2)) *
      (d + 1)
  let E : Set (Fin ((d + 1) + tail) → ℝ) :=
    AdjacentNormal.reducedNormalFlattenedSelectedSpacelike
      (d := d) (0 : Fin 2) (1 : Fin 2)
  let Ωplus : Set (SCV.ComplexChartSpace ((d + 1) + tail)) :=
    {z | (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
      z (Fin.castAdd tail μ) :
      BHW.ReducedNPointConfig d 1) ∈ BHW.ReducedPermutedExtendedTubeN d 1}
  let Ωminus : Set (SCV.ComplexChartSpace ((d + 1) + tail)) :=
    {z | (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
      -z (Fin.castAdd tail μ) :
      BHW.ReducedNPointConfig d 1) ∈ BHW.ReducedPermutedExtendedTubeN d 1}
  let C : Set (Fin ((d + 1) + tail) → ℝ) :=
    AdjacentNormal.reducedNormalFlatForwardCone
      (d := d) (0 : Fin 2) (by decide)
  let Fplus : SCV.ComplexChartSpace ((d + 1) + tail) → ℂ :=
    fun z => Fred.toFun
      (fun _ : Fin 1 => fun μ : Fin (d + 1) => z (Fin.castAdd tail μ))
  let Fminus : SCV.ComplexChartSpace ((d + 1) + tail) → ℂ :=
    fun z => Fred.toFun
      (fun _ : Fin 1 => fun μ : Fin (d + 1) => -z (Fin.castAdd tail μ))
  let bv : (Fin ((d + 1) + tail) → ℝ) → ℂ :=
    fun x => Fred.toFun
      (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
        (x (Fin.castAdd tail μ) : ℂ))
  have hpE : AdjacentNormal.reducedNormalFlattenCLE
        (d := d) (0 : Fin 2) (1 : Fin 2) p ∈ E := by
    simpa [E, tail, AdjacentNormal.reducedNormalFlattenedSelectedSpacelike,
      AdjacentNormal.reducedSelectedSpacelike] using hp
  have hΩplus_open : IsOpen Ωplus := by
    exact (isOpen_reducedPermutedExtendedTubeN (d := d) 1).preimage
      (by continuity)
  have hΩminus_open : IsOpen Ωminus := by
    exact (isOpen_reducedPermutedExtendedTubeN (d := d) 1).preimage
      (by continuity)
  have hC_open : IsOpen C := by
    dsimp [C, tail]
    exact AdjacentNormal.isOpen_reducedNormalFlatForwardCone
      (d := d) (0 : Fin 2) (by decide)
  have hC_conv : Convex ℝ C := by
    dsimp [C, tail]
    exact AdjacentNormal.convex_reducedNormalFlatForwardCone
      (d := d) (0 : Fin 2) (by decide)
  have hC_ne : C.Nonempty := by
    dsimp [C, tail]
    exact AdjacentNormal.reducedNormalFlatForwardCone_nonempty
      (d := d) (0 : Fin 2) (by decide)
  have hplus0 : ∀ x ∈ E, SCV.realEmbed x ∈ Ωplus := by
    intro x hx
    let v : Fin (d + 1) → ℝ := fun μ => x (Fin.castAdd tail μ)
    have hsp : MinkowskiSpace.IsSpacelike d v := by
      simpa [E, tail, v,
        AdjacentNormal.reducedNormalFlattenedSelectedSpacelike]
        using hx
    simpa [Ωplus, SCV.realEmbed, v] using
      oneSpacelikeReducedPET_of_isSpacelike (d := d) v hsp
  have hminus0 : ∀ x ∈ E, SCV.realEmbed x ∈ Ωminus := by
    intro x hx
    let v : Fin (d + 1) → ℝ := fun μ => x (Fin.castAdd tail μ)
    have hsp : MinkowskiSpace.IsSpacelike d v := by
      simpa [E, tail, v,
        AdjacentNormal.reducedNormalFlattenedSelectedSpacelike]
        using hx
    have hsp_neg :
        MinkowskiSpace.IsSpacelike d (fun μ : Fin (d + 1) => -v μ) := by
      simpa using (minkowski_isSpacelike_neg_iff (d := d) v).2 hsp
    simpa [Ωminus, SCV.realEmbed, v] using
      oneSpacelikeReducedPET_of_isSpacelike (d := d)
        (fun μ : Fin (d + 1) => -v μ) hsp_neg
  have hFplus_diff : DifferentiableOn ℂ Fplus Ωplus := by
    have hLdiff : Differentiable ℂ
        (fun z : SCV.ComplexChartSpace ((d + 1) + tail) =>
          (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
            z (Fin.castAdd tail μ) :
            BHW.ReducedNPointConfig d 1)) := by
      fun_prop
    simpa [Fplus, Ωplus] using
      DifferentiableOn.comp Fred.holomorphic hLdiff.differentiableOn
        (by intro z hz; exact hz)
  have hFminus_diff : DifferentiableOn ℂ Fminus Ωminus := by
    have hLdiff : Differentiable ℂ
        (fun z : SCV.ComplexChartSpace ((d + 1) + tail) =>
          (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
            -z (Fin.castAdd tail μ) :
            BHW.ReducedNPointConfig d 1)) := by
      fun_prop
    simpa [Fminus, Ωminus] using
      DifferentiableOn.comp Fred.holomorphic hLdiff.differentiableOn
        (by intro z hz; exact hz)
  have hbv_cont : ContinuousOn bv E := by
    intro x hx
    have hxΩ : SCV.realEmbed x ∈ Ωplus := hplus0 x hx
    have hcw := hFplus_diff.continuousOn.continuousWithinAt hxΩ
    have hrealcont : ContinuousAt SCV.realEmbed x :=
      SCV.continuous_realEmbed.continuousAt
    have hcomp := hcw.comp hrealcont.continuousWithinAt (by
      intro y hy
      exact hplus0 y hy)
    simpa [Fplus, bv] using
      hcomp
  have hminus_edge_eq : ∀ x ∈ E,
      Fminus (SCV.realEmbed x) = bv x := by
    intro x hx
    let v : Fin (d + 1) → ℝ := fun μ => x (Fin.castAdd tail μ)
    let η : BHW.ReducedNPointConfig d 1 :=
      fun _ : Fin 1 => fun μ : Fin (d + 1) => (v μ : ℂ)
    have hη : η ∈ BHW.ReducedPermutedExtendedTubeN d 1 := by
      simpa [η, Ωplus, SCV.realEmbed, v] using hplus0 x hx
    have hperm_eq : BHW.permOnReducedDiff (d := d) (n := 2)
          (Equiv.swap (0 : Fin 2) (1 : Fin 2)) η =
        (fun _ : Fin 1 => fun μ : Fin (d + 1) => -(v μ : ℂ)) := by
      ext k μ
      have hk0 : k = (0 : Fin 1) := by
        exact Fin.ext (by omega)
      subst k
      have hsel :=
        congrFun
          (permOnReducedDiff_adjacentSwap_selected
            (d := d) 1 (0 : Fin 2) (by decide) η) μ
      simpa [η] using hsel
    have hηperm : BHW.permOnReducedDiff (d := d) (n := 2)
          (Equiv.swap (0 : Fin 2) (1 : Fin 2)) η ∈
        BHW.ReducedPermutedExtendedTubeN d 1 := by
      exact reducedPermutedExtendedTubeN_permOnReducedDiff (d := d) 1
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)) hη
    have h := Fred.perm_invariant
      (Equiv.swap (0 : Fin 2) (1 : Fin 2)) η hη hηperm
    rw [hperm_eq] at h
    simpa [Fminus, bv, SCV.realEmbed, η, v] using h
  have hFplus_bv : ∀ x ∈ E,
      Filter.Tendsto Fplus
        (nhdsWithin (SCV.realEmbed x) Ωplus) (nhds (bv x)) := by
    intro x hx
    have hxΩ : SCV.realEmbed x ∈ Ωplus := hplus0 x hx
    simpa [Fplus, bv, SCV.realEmbed] using
      hFplus_diff.continuousOn.continuousWithinAt hxΩ
  have hFminus_bv : ∀ x ∈ E,
      Filter.Tendsto Fminus
        (nhdsWithin (SCV.realEmbed x) Ωminus) (nhds (bv x)) := by
    intro x hx
    have hxΩ : SCV.realEmbed x ∈ Ωminus := hminus0 x hx
    have hlim := hFminus_diff.continuousOn.continuousWithinAt hxΩ
    have hlim' :
        Filter.Tendsto Fminus
          (nhdsWithin (SCV.realEmbed x) Ωminus)
          (nhds (Fminus (SCV.realEmbed x))) := hlim
    rw [hminus_edge_eq x hx] at hlim'
    exact hlim'
  have hplus_nhds : Ωplus ∈ nhds
      (SCV.realEmbed
        (AdjacentNormal.reducedNormalFlattenCLE (d := d)
          (0 : Fin 2) (1 : Fin 2) p)) :=
    hΩplus_open.mem_nhds (hplus0 _ hpE)
  have hminus_nhds : Ωminus ∈ nhds
      (SCV.realEmbed
        (AdjacentNormal.reducedNormalFlattenCLE (d := d)
          (0 : Fin 2) (1 : Fin 2) p)) :=
    hΩminus_open.mem_nhds (hminus0 _ hpE)
  have hplus_ext :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fplus (AdjacentNormal.reducedNormalUpperCanonicalRay
            (d := d) (0 : Fin 2) (by decide) p ε) =
          Fred.toFun
            (AdjacentNormal.reducedNormalCoordFlatComplexCLM
              (d := d) (0 : Fin 2) (by decide)
              (AdjacentNormal.reducedNormalUpperCanonicalRay
                (d := d) (0 : Fin 2) (by decide) p ε)) := by
    filter_upwards with ε
    have hξ :=
      AdjacentNormal.reducedCoordInv_zero_one_eq_selected (d := d) p
    have harg :
        (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
            AdjacentNormal.reducedNormalUpperCanonicalRay
              (d := d) (0 : Fin 2) (by decide) p ε
                (Fin.castAdd tail μ)) =
          (fun k μ =>
            (AdjacentNormal.reducedCoordInv (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide) p k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) 1 k μ *
                Complex.I) := by
      ext k μ
      have hk0 : k = (0 : Fin 1) := by
        exact Fin.ext (by omega)
      subst k
      have hp_head :
              AdjacentNormal.reducedNormalFlattenCLE
                  (d := d) (0 : Fin 2) (1 : Fin 2) p
                  (Fin.castAdd tail μ) = p.1 μ := by
        simp [tail]
      have hdir_head :
          AdjacentNormal.reducedNormalFlatCanonicalDirection
              (d := d) (0 : Fin 2) (by decide)
              (Fin.castAdd tail μ) =
            canonicalReducedDirection (d := d) 1 0 μ := by
        let η : NPointDomain d 1 := canonicalReducedDirection (d := d) 1
        have hcoord :
            ((AdjacentNormal.reducedCoordCLE (d := d)
                (0 : Fin 2) (1 : Fin 2) (by decide)) η).1 μ =
              η 0 μ := by
          have hfst :=
            congrFun
              (AdjacentNormal.reducedCoord_fst_eq_reducedPairDiff
                (d := d) (0 : Fin 2) (1 : Fin 2) η) μ
          have hproj :
              reducedPairDiff (d := d) 1 (0 : Fin 2) (1 : Fin 2) η μ =
                η 0 μ := by
            have hL := congrFun
              (congrArg (fun L => L η)
                (reducedPairDiffCLM_adjacent_eq_proj
                  (d := d) 1 (0 : Fin 2) (by decide))) μ
            simpa using hL
          change (AdjacentNormal.reducedCoord (d := d)
            (0 : Fin 2) (1 : Fin 2) η).1 μ = η 0 μ
          rw [hfst, hproj]
        have hhead :=
          AdjacentNormal.reducedNormalFlattenCLE_apply_head
            (d := d) (0 : Fin 2) (1 : Fin 2)
            ((AdjacentNormal.reducedCoordCLE (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide)) η) μ
        calc
          AdjacentNormal.reducedNormalFlatCanonicalDirection
                (d := d) (0 : Fin 2) (by decide)
                (Fin.castAdd tail μ)
              =
            ((AdjacentNormal.reducedCoordCLE (d := d)
                (0 : Fin 2) (1 : Fin 2) (by decide)) η).1 μ := by
              exact hhead
          _ = η 0 μ := hcoord
          _ = canonicalReducedDirection (d := d) 1 0 μ := rfl
      have hξ0 := congrFun (congrFun hξ (0 : Fin 1)) μ
      simp [AdjacentNormal.reducedNormalUpperCanonicalRay,
        hdir_head, hξ0, canonicalReducedDirectionC]
      exact hp_head
    change Fred.toFun
        (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
          AdjacentNormal.reducedNormalUpperCanonicalRay
            (d := d) (0 : Fin 2) (by decide) p ε
              (Fin.castAdd tail μ)) =
      Fred.toFun
        (AdjacentNormal.reducedNormalCoordFlatComplexCLM
          (d := d) (0 : Fin 2) (by decide)
          (AdjacentNormal.reducedNormalUpperCanonicalRay
            (d := d) (0 : Fin 2) (by decide) p ε))
    rw [AdjacentNormal.reducedNormalCoordFlatComplexCLM_upperCanonicalRay]
    exact congrArg Fred.toFun harg
  have hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Fminus (AdjacentNormal.reducedNormalLowerCanonicalRay
            (d := d) (0 : Fin 2) (by decide) p ε) =
          canonicalReducedBranch (d := d) OS lgc 1 ε
            (AdjacentNormal.reducedCoordInv (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide)
              (AdjacentNormal.reducedSignFlip
                (d := d) (0 : Fin 2) (1 : Fin 2) p)) := by
    have hpos : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        0 < ε := by
      exact self_mem_nhdsWithin
    refine hpos.mono ?_
    intro ε hε
    have hξflip :=
      AdjacentNormal.reducedCoordInv_zero_one_eq_selected (d := d)
        (AdjacentNormal.reducedSignFlip
          (d := d) (0 : Fin 2) (1 : Fin 2) p)
    have harg :
        (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
            -AdjacentNormal.reducedNormalLowerCanonicalRay
              (d := d) (0 : Fin 2) (by decide) p ε
                (Fin.castAdd tail μ)) =
          (fun k μ =>
            (AdjacentNormal.reducedCoordInv (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide)
              (AdjacentNormal.reducedSignFlip
                (d := d) (0 : Fin 2) (1 : Fin 2) p) k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) 1 k μ *
                Complex.I) := by
      ext k μ
      have hk0 : k = (0 : Fin 1) := by
        exact Fin.ext (by omega)
      subst k
      have hp_head :
              AdjacentNormal.reducedNormalFlattenCLE
                  (d := d) (0 : Fin 2) (1 : Fin 2) p
                  (Fin.castAdd tail μ) = p.1 μ := by
        simp [tail]
      have hdir_head :
          AdjacentNormal.reducedNormalFlatCanonicalDirection
              (d := d) (0 : Fin 2) (by decide)
              (Fin.castAdd tail μ) =
            canonicalReducedDirection (d := d) 1 0 μ := by
        let η : NPointDomain d 1 := canonicalReducedDirection (d := d) 1
        have hcoord :
            ((AdjacentNormal.reducedCoordCLE (d := d)
                (0 : Fin 2) (1 : Fin 2) (by decide)) η).1 μ =
              η 0 μ := by
          have hfst :=
            congrFun
              (AdjacentNormal.reducedCoord_fst_eq_reducedPairDiff
                (d := d) (0 : Fin 2) (1 : Fin 2) η) μ
          have hproj :
              reducedPairDiff (d := d) 1 (0 : Fin 2) (1 : Fin 2) η μ =
                η 0 μ := by
            have hL := congrFun
              (congrArg (fun L => L η)
                (reducedPairDiffCLM_adjacent_eq_proj
                  (d := d) 1 (0 : Fin 2) (by decide))) μ
            simpa using hL
          change (AdjacentNormal.reducedCoord (d := d)
            (0 : Fin 2) (1 : Fin 2) η).1 μ = η 0 μ
          rw [hfst, hproj]
        have hhead :=
          AdjacentNormal.reducedNormalFlattenCLE_apply_head
            (d := d) (0 : Fin 2) (1 : Fin 2)
            ((AdjacentNormal.reducedCoordCLE (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide)) η) μ
        calc
          AdjacentNormal.reducedNormalFlatCanonicalDirection
                (d := d) (0 : Fin 2) (by decide)
                (Fin.castAdd tail μ)
              =
            ((AdjacentNormal.reducedCoordCLE (d := d)
                (0 : Fin 2) (1 : Fin 2) (by decide)) η).1 μ := by
              exact hhead
          _ = η 0 μ := hcoord
          _ = canonicalReducedDirection (d := d) 1 0 μ := rfl
      have hξ0 := congrFun (congrFun hξflip (0 : Fin 1)) μ
      rw [AdjacentNormal.reducedNormalLowerCanonicalRay]
      simp [hdir_head, canonicalReducedDirectionC]
      have hp_headC :
          ((AdjacentNormal.reducedNormalFlattenCLE
              (d := d) (0 : Fin 2) (1 : Fin 2) p
              (Fin.castAdd tail μ) : ℝ) : ℂ) = (p.1 μ : ℂ) := by
        exact_mod_cast hp_head
      have hξ0p :
          (AdjacentNormal.reducedCoordInv (d := d)
              (0 : Fin 2) (1 : Fin 2) (by decide)
              (AdjacentNormal.reducedSignFlip
                (d := d) (0 : Fin 2) (1 : Fin 2) p) 0 μ : ℂ) =
            -(p.1 μ : ℂ) := by
        simpa [AdjacentNormal.reducedSignFlip] using hξ0
      rw [hξ0p]
      rw [← hp_headC]
      ring_nf
      rfl
    have heq := bvt_F_reduced_canonicalApproach_eq_reducedExtension
        (d := d) OS lgc 1 Fred
        (AdjacentNormal.reducedCoordInv (d := d)
          (0 : Fin 2) (1 : Fin 2) (by decide)
          (AdjacentNormal.reducedSignFlip
            (d := d) (0 : Fin 2) (1 : Fin 2) p)) hε
    rw [canonicalReducedBranch]
    change Fred.toFun
        (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
          -AdjacentNormal.reducedNormalLowerCanonicalRay
            (d := d) (0 : Fin 2) (by decide) p ε
              (Fin.castAdd tail μ)) =
      bvt_F_reduced (d := d) OS lgc 1
        (fun k μ =>
          (AdjacentNormal.reducedCoordInv (d := d)
            (0 : Fin 2) (1 : Fin 2) (by decide)
            (AdjacentNormal.reducedSignFlip
              (d := d) (0 : Fin 2) (1 : Fin 2) p) k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) 1 k μ * Complex.I)
    rw [harg]
    exact heq.symm
  have hE_open : IsOpen E := by
    dsimp [E, tail]
    exact AdjacentNormal.isOpen_reducedNormalFlattenedSelectedSpacelike
      (d := d) (0 : Fin 2) (1 : Fin 2)
  exact ⟨AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn.ofUpperReducedExtension
    (d := d) (OS := OS) (lgc := lgc)
    (m := 1) (i := (0 : Fin 2)) (hi := by decide) (p := p)
    Fred E hE_open
    hpE Ωplus Ωminus C hΩplus_open hΩminus_open hC_open hC_conv hC_ne
    hplus0 hminus0 Fplus Fminus hFplus_diff hFminus_diff bv hbv_cont
    hFplus_bv hFminus_bv hplus_nhds hminus_nhds hplus_ext hminus_rep⟩

/-- Adjacent-index form of the two-point/no-spectator reduced-normal EOW
branch-data producer. -/
theorem AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_noSpectator_of_selected
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := 2)
      (bvt_F_reduced (d := d) OS lgc 1))
    (i : Fin 2) (hi : i.val + 1 < 2)
    (p : AdjacentNormal.ReducedSpace d 1 i ⟨i.val + 1, hi⟩)
    (hp : p ∈ AdjacentNormal.reducedSelectedSpacelike
      (d := d) i ⟨i.val + 1, hi⟩) :
    Nonempty (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
      (d := d) OS lgc i hi p) := by
  have hi0 : i = (0 : Fin 2) := by
    exact Fin.ext (by omega)
  subst i
  simpa using
    AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_zero_one_of_selected
      (d := d) OS lgc Fred p hp

end OSReconstruction
