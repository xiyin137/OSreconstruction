import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedAdjacentNormalForm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedNormalEOW
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedNormalOS45Bridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedOneSpacelikePET
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport

/-!
# Reduced Forward-Jost Piece of the Ruelle Locality Step

This file records the Lean form of the OS I Section 4.5 / Jost half of the
reduced locality argument.  Once a genuine reduced BHW extension is available,
compact tests supported on real forward-Jost configurations satisfy the
adjacent reduced two-direction distributional boundary limit.  The remaining
theorem-2 gap is Ruelle's classical extension from this Jost-support statement
to arbitrary compact adjacent-spacelike support.
-/

open scoped Classical NNReal
open BigOperators MeasureTheory

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem reducedForwardJost_lift_mem_forwardJostSet
    {m : ℕ} (hd : 1 ≤ d)
    (ξ : NPointDomain d m)
    (hξ : ∀ k : Fin m, |ξ k 0| < ξ k ⟨1, by omega⟩) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m
          (fun μ : Fin (d + 1) =>
            if μ = ⟨1, by omega⟩ then 1 else 0) ξ) ∈
      BHW.ForwardJostSet d (m + 1) hd := by
  let e₁ : Fin (d + 1) := ⟨1, by omega⟩
  let c : SpacetimeDim d := fun μ => if μ = e₁ then 1 else 0
  let x : NPointDomain d (m + 1) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m c ξ)
  have hdiff :
      ∀ k : Fin (m + 1), BHW.consecutiveDiff x k =
        BHW.prependBasepointReal d m c ξ k := by
    intro k
    ext μ
    have hcoord :=
      congrFun
        (congrFun
          ((BHW.realDiffCoordCLE (m + 1) d).apply_symm_apply
            (BHW.prependBasepointReal d m c ξ)) k) μ
    by_cases hk : k.val = 0
    · simpa [x, BHW.realDiffCoordCLE_apply, BHW.consecutiveDiff, hk] using hcoord
    · simpa [x, BHW.realDiffCoordCLE_apply, BHW.consecutiveDiff, hk] using hcoord
  intro k
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst k
    have hbase :
        |BHW.prependBasepointReal d m c ξ 0 0| <
          BHW.prependBasepointReal d m c ξ 0 e₁ := by
      have h0e : (0 : Fin (d + 1)) ≠ e₁ := by
        intro h
        simpa [e₁, Fin.ext_iff] using congrArg Fin.val h
      simp [BHW.prependBasepointReal, c, e₁, h0e]
    have hcd0 := congrFun (hdiff 0) (0 : Fin (d + 1))
    have hcd1 := congrFun (hdiff 0) e₁
    calc
      |BHW.consecutiveDiff x 0 0|
          = |BHW.prependBasepointReal d m c ξ 0 0| := by rw [hcd0]
      _ < BHW.prependBasepointReal d m c ξ 0 e₁ := hbase
      _ = BHW.consecutiveDiff x 0 e₁ := by rw [hcd1]
  · let j : Fin m := ⟨k.val - 1, by omega⟩
    have hk_succ : k = j.succ := by
      ext
      simp [j]
      omega
    have hselected :
        |BHW.prependBasepointReal d m c ξ k 0| <
          BHW.prependBasepointReal d m c ξ k e₁ := by
      rw [hk_succ]
      simpa [BHW.prependBasepointReal, e₁] using hξ j
    have hcd0 := congrFun (hdiff k) (0 : Fin (d + 1))
    have hcd1 := congrFun (hdiff k) e₁
    calc
      |BHW.consecutiveDiff x k 0|
          = |BHW.prependBasepointReal d m c ξ k 0| := by rw [hcd0]
      _ < BHW.prependBasepointReal d m c ξ k e₁ := hselected
      _ = BHW.consecutiveDiff x k e₁ := by rw [hcd1]

omit [NeZero d] in
/-- A reduced real configuration whose successive differences are already in a
common forward-Jost orientation lies on the reduced permuted extended tube.

This is the reduced-coordinate Jost geometry used by the local Ruelle collar
step: choose an absolute spatial basepoint and reconstruct the absolute
configuration from the reduced successive differences. -/
theorem reducedForwardJost_realEmbed_mem_reducedPermutedExtendedTubeN
    {m : ℕ} (hd : 1 ≤ d)
    (ξ : NPointDomain d m)
    (hξ : ∀ k : Fin m, |ξ k 0| < ξ k ⟨1, by omega⟩) :
    (fun k μ => (ξ k μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d m := by
  let e₁ : Fin (d + 1) := ⟨1, by omega⟩
  let c : SpacetimeDim d := fun μ => if μ = e₁ then 1 else 0
  let x : NPointDomain d (m + 1) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m c ξ)
  have hxFJ : x ∈ BHW.ForwardJostSet d (m + 1) hd := by
    simpa [x, c, e₁] using
      reducedForwardJost_lift_mem_forwardJostSet
        (d := d) (m := m) hd ξ hξ
  have hpet :=
    reducedDiffMapReal_mem_reducedPermutedExtendedTubeN_of_forwardJostSet
      (d := d) (m := m) hd x hxFJ
  have hreal :
      (fun k μ => (ξ k μ : ℂ)) =
        fun k μ => ((BHW.reducedDiffMapReal (m + 1) d x) k μ : ℂ) := by
    funext k μ
    rw [BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal]
  simpa [hreal] using hpet

/-- PET-support version of the reduced adjacent Ruelle boundary limit.

This is the exact part of the Ruelle locality step already supplied by the
reduced BHW extension: once every real support point is already a reduced
permuted-extended-tube boundary point, the two positive-side reduced
approaches have the same distributional boundary value by pointwise PET
uniqueness and the existing dominated-convergence theorem. -/
theorem adjacentReducedRuelleDistributionalLimit_of_reducedPETSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (f : SchwartzNPoint d (m + 1))
    (hf_reducedPET :
      ∀ x, f.toFun x ≠ 0 →
        (fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ)) ∈
          BHW.ReducedPermutedExtendedTubeN d m) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) *
              (f x)) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  have hpointwise :
      ∀ x, f x ≠ 0 →
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0) := by
    intro x hx
    exact
      bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension
        (d := d) OS lgc m i j Fred
        (BHW.reducedDiffMapReal (m + 1) d x)
        (hf_reducedPET x hx)
  simpa [j] using
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f hpointwise

/-- Two-point spacelike-support version of the reduced adjacent Ruelle limit.

This is the first assembled use of the one-variable Ruelle/Jost geometry leaf:
for two points, the single reduced successive difference is spacelike on the
support, hence it lies on the reduced PET boundary by
`oneSpacelikeReducedPET_of_isSpacelike_succ`; the existing reduced PET
extension and DCT theorem then give the distributional adjacent-swap limit. -/
theorem adjacentReducedRuelleDistributionalLimit_twoPointSpacelikeSupport_succ
    (M : ℕ)
    (OS : OsterwalderSchraderAxioms (M + 1))
    (lgc : OSLinearGrowthCondition (M + 1) OS)
    (Fred : BHW.ReducedBHWExtensionData (d := M + 1) (n := 2)
      (bvt_F_reduced (d := M + 1) OS lgc 1))
    (f : SchwartzNPoint (M + 1) 2)
    (hf_spacelike :
      ∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated (M + 1) (x 0) (x 1)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain (M + 1) 2,
            bvt_F_reduced (d := M + 1) OS lgc 1
              (fun k μ =>
                (BHW.reducedDiffMapReal 2 (M + 1) x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := M + 1) 1 (Equiv.swap (0 : Fin 2) (1 : Fin 2)) k μ *
                    Complex.I) *
              (f x)) -
          ∫ x : NPointDomain (M + 1) 2,
            bvt_F_reduced (d := M + 1) OS lgc 1
              (fun k μ =>
                (BHW.reducedDiffMapReal 2 (M + 1) x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := M + 1) 1 k μ *
                    Complex.I) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hi : (0 : Fin 2).val + 1 < 2 := by decide
  refine
    adjacentReducedRuelleDistributionalLimit_of_reducedPETSupport
      (d := M + 1) OS lgc 1 (0 : Fin 2) hi Fred f ?_
  intro x hx
  have hsp_edge :
      BHW.reducedDiffMapReal 2 (M + 1) x ∈
        reducedSpacelikeSwapEdge (d := M + 1) 1 (0 : Fin 2) (1 : Fin 2) := by
    simpa using
      reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
        (d := M + 1) 1 (0 : Fin 2) (1 : Fin 2) x
        (hf_spacelike x hx)
  have hsp_coord :
      MinkowskiSpace.IsSpacelike (M + 1)
        (BHW.reducedDiffMapReal 2 (M + 1) x 0) := by
    simpa using
      (mem_reducedSpacelikeSwapEdge_adjacent_iff
        (d := M + 1) 1 (0 : Fin 2) hi
        (BHW.reducedDiffMapReal 2 (M + 1) x)).1 hsp_edge
  have hpet0 :=
    oneSpacelikeReducedPET_of_isSpacelike_succ
      (m := M)
      (v := BHW.reducedDiffMapReal 2 (M + 1) x 0)
      hsp_coord
  have hcfg :
      (fun k μ => ((BHW.reducedDiffMapReal 2 (M + 1) x k μ : ℂ))) =
        (fun _ : Fin 1 => fun μ =>
          ((BHW.reducedDiffMapReal 2 (M + 1) x 0 μ : ℂ))) := by
    ext k μ
    fin_cases k
    rfl
  rw [hcfg]
  exact hpet0

/-- Compact two-point `bvt_W` locality from spacelike support and a reduced PET
extension.

This is the two-point end-to-end assembly of the Ruelle/Jost geometry leaf:
spacelike support gives the reduced two-direction distributional limit above;
the existing reduced/canonical-shell algebra transports that limit to the
ordinary canonical boundary family; and `bvt_boundary_values` identifies the
two Wightman pairings. -/
theorem bvt_W_adjacent_swap_twoPointSpacelikeSupport_reducedExtension_compact_succ
    (M : ℕ)
    (OS : OsterwalderSchraderAxioms (M + 1))
    (lgc : OSLinearGrowthCondition (M + 1) OS)
    (Fred : BHW.ReducedBHWExtensionData (d := M + 1) (n := 2)
      (bvt_F_reduced (d := M + 1) OS lgc 1))
    (f g : SchwartzNPoint (M + 1) 2)
    (hf_compact : HasCompactSupport (f : NPointDomain (M + 1) 2 → ℂ))
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated (M + 1) (x 0) (x 1))
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))) :
    bvt_W OS lgc 2 f = bvt_W OS lgc 2 g := by
  have hi : (0 : Fin 2).val + 1 < 2 := by decide
  have hreduced :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain (M + 1) 2,
              bvt_F_reduced (d := M + 1) OS lgc 1
                (fun k μ =>
                  (BHW.reducedDiffMapReal 2 (M + 1) x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := M + 1) 1 (Equiv.swap (0 : Fin 2) (1 : Fin 2)) k μ *
                      Complex.I) *
                (f x)) -
            ∫ x : NPointDomain (M + 1) 2,
              bvt_F_reduced (d := M + 1) OS lgc 1
                (fun k μ =>
                  (BHW.reducedDiffMapReal 2 (M + 1) x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := M + 1) 1 k μ *
                      Complex.I) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    adjacentReducedRuelleDistributionalLimit_twoPointSpacelikeSupport_succ
      (M := M) OS lgc Fred f hsp
  have hcanonical :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain (M + 1) 2,
              bvt_F OS lgc 2
                (canonicalShell (d := M + 1) 2 x ε) *
                (g x)) -
            ∫ x : NPointDomain (M + 1) 2,
              bvt_F OS lgc 2
                (canonicalShell (d := M + 1) 2 x ε) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    compact_canonicalShell_swap_tendsto_of_reduced_pair_tendsto
      (d := M + 1) OS lgc 1 (0 : Fin 2) (1 : Fin 2) f g hf_compact
      hsp hswap hreduced
  let η := canonicalForwardConeDirection (d := M + 1) 2
  have hη : InForwardCone (M + 1) 2 η :=
    canonicalForwardConeDirection_mem (d := M + 1) 2
  have hfBV :=
    bvt_boundary_values (d := M + 1) OS lgc 2 f η hη
  have hgBV :=
    bvt_boundary_values (d := M + 1) OS lgc 2 g η hη
  have hdiff_limit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain (M + 1) 2,
              bvt_F OS lgc 2
                (canonicalShell (d := M + 1) 2 x ε) *
                (g x)) -
            ∫ x : NPointDomain (M + 1) 2,
              bvt_F OS lgc 2
                (canonicalShell (d := M + 1) 2 x ε) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc 2 g - bvt_W OS lgc 2 f)) := by
    simpa [η, canonicalShell] using hgBV.sub hfBV
  have hzero : bvt_W OS lgc 2 g - bvt_W OS lgc 2 f = 0 :=
    tendsto_nhds_unique hdiff_limit hcanonical
  exact (sub_eq_zero.mp hzero).symm

/-- Full Schwartz two-point `bvt_W` locality from spacelike support and a
reduced PET extension.

This removes the compact-support hypothesis from the preceding theorem by the
standard radial cutoff approximation, preserving vanishing outside the
spacelike set. -/
theorem bvt_W_adjacent_swap_twoPointSpacelikeSupport_reducedExtension_succ
    (M : ℕ)
    (OS : OsterwalderSchraderAxioms (M + 1))
    (lgc : OSLinearGrowthCondition (M + 1) OS)
    (Fred : BHW.ReducedBHWExtensionData (d := M + 1) (n := 2)
      (bvt_F_reduced (d := M + 1) OS lgc 1))
    (f g : SchwartzNPoint (M + 1) 2)
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated (M + 1) (x 0) (x 1))
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))) :
    bvt_W OS lgc 2 f = bvt_W OS lgc 2 g := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) (1 : Fin 2)
  let U : Set (NPointDomain (M + 1) 2) :=
    {x | MinkowskiSpace.AreSpacelikeSeparated (M + 1) (x 0) (x 1)}
  have hf_zero : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    by_contra hfx
    exact hxU (hsp x hfx)
  obtain ⟨fN, hfN_compact, hfN_zero, hfN_tendsto⟩ :=
    exists_compactSupportApprox_zeroOff_npoint (d := M + 1) U f hf_zero
  let P : SchwartzNPoint (M + 1) 2 →L[ℂ] SchwartzNPoint (M + 1) 2 :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (M + 2) → ℝ) τ).toContinuousLinearEquiv)
  let gN : ℕ → SchwartzNPoint (M + 1) 2 := fun N => P (fN N)
  have hcompact_eq :
      ∀ N, bvt_W OS lgc 2 (fN N) =
        bvt_W OS lgc 2 (gN N) := by
    intro N
    refine
      bvt_W_adjacent_swap_twoPointSpacelikeSupport_reducedExtension_compact_succ
        (M := M) OS lgc Fred (fN N) (gN N)
        (hfN_compact N) ?_ ?_
    · intro x hfx
      have hxU : x ∈ U := by
        by_contra hxU
        exact hfx (hfN_zero N x hxU)
      exact hxU
    · intro x
      change
        P (fN N) x =
          (fN N).toFun (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))
      rfl
  have hleft :
      Filter.Tendsto (fun N => bvt_W OS lgc 2 (fN N))
        Filter.atTop (nhds (bvt_W OS lgc 2 f)) :=
    ((bvt_W_continuous (d := M + 1) OS lgc 2).tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    exact (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => bvt_W OS lgc 2 (gN N))
        Filter.atTop (nhds (bvt_W OS lgc 2 g)) :=
    ((bvt_W_continuous (d := M + 1) OS lgc 2).tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => bvt_W OS lgc 2 (fN N))
        Filter.atTop (nhds (bvt_W OS lgc 2 g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

/-- Reduced forward-Jost support version of the adjacent Ruelle boundary
limit.

The input is now stated directly in reduced coordinates, which is the form
used by the Ruelle local-coordinate argument: every reduced support point lies
in one fixed forward-Jost coordinate orientation.  The geometric leaf above
turns that condition into reduced PET membership, and the PET-support theorem
then supplies the distributional boundary limit. -/
theorem adjacentReducedRuelleDistributionalLimit_of_reducedForwardJostSupport
    (hd : 1 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (f : SchwartzNPoint d (m + 1))
    (hf_reducedForwardJost :
      ∀ x, f.toFun x ≠ 0 →
        ∀ k : Fin m,
          |BHW.reducedDiffMapReal (m + 1) d x k 0| <
            BHW.reducedDiffMapReal (m + 1) d x k ⟨1, by omega⟩) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) *
              (f x)) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  exact
    adjacentReducedRuelleDistributionalLimit_of_reducedPETSupport
      (d := d) OS lgc m i hi Fred f
      (fun x hx =>
        reducedForwardJost_realEmbed_mem_reducedPermutedExtendedTubeN
          (d := d) (m := m) hd
          (BHW.reducedDiffMapReal (m + 1) d x)
          (hf_reducedForwardJost x hx))

/-- Reduced adjacent Ruelle boundary limit from the pointwise mixed-tube
Jost/EOW conclusion on the adjacent spacelike edge.

This is the faithful theorem-2 reduction after the monograph/Jost route:
the remaining analytic payload is no longer an integral statement.  It is the
pointwise statement that, at each real adjacent-spacelike reduced difference,
the canonical and adjacent-swapped positive-height approaches have the same
boundary value.  The selected forward-tube growth already supplies the DCT
domination needed to smear this pointwise equality. -/
theorem adjacentReducedRuelleDistributionalLimit_of_reducedSpacelikePointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hpointwise :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (x : NPointDomain d (m + 1)),
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m
                        (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0)) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f _hf_compact hf_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  simpa [j] using
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f
      (fun x hx =>
        by
          simpa [j] using hpointwise m i hi x (hf_support x hx))

/-- Reduced adjacent Ruelle boundary limit from the canonical reduced-branch
boundary equality on the adjacent spacelike edge.

This is the pointwise form closest to the classical Jost/Ruelle proof: the
canonical positive-side branch has the same boundary value at a real reduced
configuration `ξ` and at the adjacent real reduced permutation of `ξ`.  The
preceding theorem then smears this pointwise mixed-tube equality. -/
theorem adjacentReducedRuelleDistributionalLimit_of_canonicalBranch_realPerm_pointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hpointwise :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (ξ : NPointDomain d m),
        ξ ∈ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        Filter.Tendsto
          (fun ε : ℝ =>
            @canonicalReducedBranch d _ OS lgc m ε
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i ⟨i.val + 1, hi⟩) ξ) -
              @canonicalReducedBranch d _ OS lgc m ε ξ)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0)) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_reducedSpacelikePointwise
      (d := d) OS lgc ?_
  intro m i hi x hx
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  have hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
            @canonicalReducedBranch d _ OS lgc m ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [ξ, j] using hpointwise m i hi ξ (by simpa [ξ, j] using hx)
  refine Filter.Tendsto.congr' ?_ hcanon
  filter_upwards with ε
  symm
  have hbranch :
      @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ =
        @canonicalReducedBranch d _ OS lgc m ε
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
    rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ,
      canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
        (d := d) OS lgc m i j ε ξ]
  have hsub :=
    congrArg
      (fun z : ℂ => z - @canonicalReducedBranch d _ OS lgc m ε ξ) hbranch
  simpa [adjacentReducedPermutedBranch, canonicalReducedBranch, ξ, j] using hsub

/-- Reduced adjacent Ruelle boundary limit from the pointwise local EOW
conclusion in frozen-spectator normal coordinates.

This is the faithful Jost/Ruelle handoff shape: after freezing spectators, the
adjacent reduced permutation is only the sign flip of the selected normal
difference.  The analytic local EOW theorem should be applied to the
normal-coordinate pointwise hypothesis below; this theorem transports that
pointwise conclusion back to the existing reduced Ruelle consumer. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalSignFlip_pointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hpointwise :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ AdjacentNormal.reducedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ →
        Filter.Tendsto
          (fun ε : ℝ =>
            @canonicalReducedBranch d _ OS lgc m ε
                (AdjacentNormal.reducedCoordInv (d := d)
                  i ⟨i.val + 1, hi⟩
                  (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                  (AdjacentNormal.reducedSignFlip
                    (d := d) i ⟨i.val + 1, hi⟩ p)) -
              @canonicalReducedBranch d _ OS lgc m ε
                (AdjacentNormal.reducedCoordInv (d := d)
                  i ⟨i.val + 1, hi⟩
                  (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0)) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_canonicalBranch_realPerm_pointwise
      (d := d) OS lgc ?_
  intro m i hi ξ hξ
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := AdjacentNormal.reducedAdjacent_succ_ne i hi
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  have hp_sp :
      p ∈ AdjacentNormal.reducedSelectedSpacelike (d := d) i j := by
    change MinkowskiSpace.IsSpacelike d p.1
    have hξ_sp :
        MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) := by
      simpa [reducedSpacelikeSwapEdge, j] using hξ
    simpa [p, AdjacentNormal.reducedCoord_fst_eq_reducedPairDiff
      (d := d) i j ξ] using hξ_sp
  have hnormal :=
    hpointwise m i hi p (by simpa [j] using hp_sp)
  have hp_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij p = ξ := by
    simpa [p] using
      AdjacentNormal.reducedCoordInv_left (d := d) i j hij ξ
  have hsign_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij
          (AdjacentNormal.reducedSignFlip (d := d) i j p) =
        realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ := by
    have h :=
      AdjacentNormal.reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
        (d := d) i hi p
    simpa [j, hij, hp_inv] using h
  simpa [j, hij, p, hp_inv, hsign_inv] using hnormal

/-
Route note: the `AdjacentReducedRuelleDistributionalLimit` producers below are
kept as checked legacy consumers and diagnostics.  The theorem-2 boundary-value
frontier should use the reduced local CLM path whose paper-facing OS-I input is
the source-side branch-transfer / common-edge source equality.  The `Hdiff`
branch-difference germ is the Lean carrier built from that equality, and the
reduced sign-flip formulation is downstream reduced-normal bookkeeping:
source equality -> `Hdiff` branch difference ->
`ReducedLocalAdjacentBoundaryCLMInvariant` -> closed-support reduced canonical
swap invariance -> Wightman swap locality.
In particular, do not use the selected/local-edge Ruelle path here as the final
producer for `bvt_W_swap_pairing_of_spacelike`, since that can route the old
`BHW.localSPrime_twoSectorBranch_of_EOW_BHW` trust boundary downstream.
-/

/-- Reduced adjacent Ruelle boundary limit from concrete local EOW branch data
in frozen-spectator normal coordinates.

This theorem names the live monograph payload without turning it into a
boundary-locality wrapper: every selected spacelike normal point must supply
the two side domains, holomorphic branches, common boundary value, and
canonical/sign-flipped ray representations packaged by
`AdjacentNormal.ReducedNormalLocalEOWBranchData`. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalLocalEOWBranchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ AdjacentNormal.reducedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ →
        AdjacentNormal.ReducedNormalLocalEOWBranchData
          (d := d) OS lgc i hi p) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_normalSignFlip_pointwise
      (d := d) OS lgc ?_
  intro m i hi p hp
  exact
      AdjacentNormal.ReducedNormalLocalEOWBranchData.signFlip_pointwise
        (d := d) OS lgc i hi p hp (hbranchData m i hi p hp)

/-- Reduced adjacent Ruelle boundary limit from canonical-ray local EOW branch
data in frozen-spectator normal coordinates.

This is the concrete form of the local Jost/Ruelle payload: the side branches
must be represented along the upper/lower canonical imaginary rays in the
flattened normal chart, and the existing local EOW bridge then supplies the
pointwise sign-flip limit. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalCanonicalRayEOWBranchData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩),
        p ∈ AdjacentNormal.reducedSelectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ →
        AdjacentNormal.ReducedNormalCanonicalRayEOWBranchData
          (d := d) OS lgc i hi p) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_normalLocalEOWBranchData
      (d := d) OS lgc ?_
  intro m i hi p hp
  exact (hbranchData m i hi p hp).toLocalEOWBranchData

/-- Support-local form of the reduced adjacent Ruelle boundary limit from
concrete local EOW branch data.

This is the form needed by the monograph proof after the support has been
localized to a spacelike collar: for the compact test currently being smeared,
branch data is required only at reduced normal points hit by nonzero source
points of that test. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalLocalEOWBranchData_on_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          AdjacentNormal.ReducedNormalLocalEOWBranchData
            (d := d) OS lgc i hi
            (AdjacentNormal.reducedCoord (d := d)
              i ⟨i.val + 1, hi⟩
              (BHW.reducedDiffMapReal (m + 1) d x))) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hf_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f ?_
  intro x hx
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let hij : i ≠ j := AdjacentNormal.reducedAdjacent_succ_ne i hi
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  have hξ_edge :
      ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [ξ, j] using hf_support x hx
  have hp_sp :
      p ∈ AdjacentNormal.reducedSelectedSpacelike (d := d) i j := by
    change MinkowskiSpace.IsSpacelike d p.1
    have hξ_sp :
        MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) := by
      simpa [reducedSpacelikeSwapEdge, j] using hξ_edge
    simpa [p, AdjacentNormal.reducedCoord_fst_eq_reducedPairDiff
      (d := d) i j ξ] using hξ_sp
  have hnormal :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij
                (AdjacentNormal.reducedSignFlip (d := d) i j p)) -
            @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    exact
      AdjacentNormal.ReducedNormalLocalEOWBranchData.signFlip_pointwise
        (d := d) OS lgc i hi p (by simpa [j] using hp_sp)
        (by
          simpa [p, ξ, j] using
            hbranchData m i hi f hf_compact hf_support x hx)
  have hp_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij p = ξ := by
    simpa [p] using
      AdjacentNormal.reducedCoordInv_left (d := d) i j hij ξ
  have hsign_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij
          (AdjacentNormal.reducedSignFlip (d := d) i j p) =
        realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ := by
    have h :=
      AdjacentNormal.reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
        (d := d) i hi p
    simpa [j, hij, hp_inv] using h
  have hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
            @canonicalReducedBranch d _ OS lgc m ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [j, hij, p, hp_inv, hsign_inv] using hnormal
  refine Filter.Tendsto.congr' ?_ hcanon
  filter_upwards with ε
  symm
  have hbranch :
      @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ =
        @canonicalReducedBranch d _ OS lgc m ε
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
    rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ,
      canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
        (d := d) OS lgc m i j ε ξ]
  have hsub :=
    congrArg
      (fun z : ℂ => z - @canonicalReducedBranch d _ OS lgc m ε ξ) hbranch
  simpa [adjacentReducedPermutedBranch, canonicalReducedBranch, ξ, j] using hsub

/-- Support-local canonical-ray form of the reduced adjacent Ruelle boundary
limit.

For a compact test supported on the adjacent spacelike edge, it is enough to
construct canonical-ray EOW branch data at the reduced normal points hit by
the nonzero source points of that test. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalCanonicalRayEOWBranchData_on_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          AdjacentNormal.ReducedNormalCanonicalRayEOWBranchData
            (d := d) OS lgc i hi
            (AdjacentNormal.reducedCoord (d := d)
              i ⟨i.val + 1, hi⟩
              (BHW.reducedDiffMapReal (m + 1) d x))) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_normalLocalEOWBranchData_on_support
      (d := d) OS lgc ?_
  intro m i hi f hf_compact hf_support x hx
  exact
    (hbranchData m i hi f hf_compact hf_support x hx).toLocalEOWBranchData

/-- Support-local collar form of the reduced adjacent Ruelle boundary limit.

This is the book-faithful local-collar handoff: for the compact test currently
being smeared, the analytic input only has to provide canonical-ray EOW branch
data on an open reduced-normal real collar around each nonzero support point.
The collar-local EOW theorem supplies the pointwise sign-flip limit, and the
already checked supportwise DCT theorem integrates it. -/
theorem adjacentReducedRuelleDistributionalLimit_of_normalCanonicalRayEOWBranchDataOn_support
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hbranchData :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
            (d := d) OS lgc i hi
            (AdjacentNormal.reducedCoord (d := d)
              i ⟨i.val + 1, hi⟩
              (BHW.reducedDiffMapReal (m + 1) d x))) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hf_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f ?_
  intro x hx
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let hij : i ≠ j := AdjacentNormal.reducedAdjacent_succ_ne i hi
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  have hnormal :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij
                (AdjacentNormal.reducedSignFlip (d := d) i j p)) -
            @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    exact
      AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn.signFlip_pointwise
        (d := d) OS lgc i hi p
        (by
          simpa [p, ξ, j] using
            hbranchData m i hi f hf_compact hf_support x hx)
  have hp_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij p = ξ := by
    simpa [p] using
      AdjacentNormal.reducedCoordInv_left (d := d) i j hij ξ
  have hsign_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij
          (AdjacentNormal.reducedSignFlip (d := d) i j p) =
        realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ := by
    have h :=
      AdjacentNormal.reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
        (d := d) i hi p
    simpa [j, hij, hp_inv] using h
  have hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
            @canonicalReducedBranch d _ OS lgc m ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [j, hij, p, hp_inv, hsign_inv] using hnormal
  refine Filter.Tendsto.congr' ?_ hcanon
  filter_upwards with ε
  symm
  have hbranch :
      @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ =
        @canonicalReducedBranch d _ OS lgc m ε
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
    rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ,
      canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
        (d := d) OS lgc m i j ε ξ]
  have hsub :=
    congrArg
      (fun z : ℂ => z - @canonicalReducedBranch d _ OS lgc m ε ξ) hbranch
  simpa [adjacentReducedPermutedBranch, canonicalReducedBranch, ξ, j] using hsub

/-- Support-local OS45/Ruelle producer for the reduced adjacent boundary limit.

This is the first direct consumer of the checked reduced-normal OS45 bridge in
the Ruelle file.  It does not hide the live analytic leaves: at every nonzero
support point one must still supply a Figure-2-4 source patch containing the
zero-center normal representative and the two OS-I source-side moving-transfer
formulas.  The coordinate conversion from those source-side formulas to the
canonical ray branch normalizations is checked below; the analytic `(4.14)`
transfer itself remains explicit.  Once those concrete leaves are available,
selected Jost data and Ruelle overlap connectedness give the local EOW packet,
and the existing supportwise DCT theorem integrates it. -/
theorem adjacentReducedRuelleDistributionalLimit_of_selectedJostData_OS45NormalBranches_support
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hOverlap :
      ∀ (m : ℕ) (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData :
      ∀ m : ℕ,
        SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (hLocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          { P : BHW.OS45Figure24CanonicalSourcePatchData
              (d := d) hd (m + 1) i hi //
            let p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩ :=
              AdjacentNormal.reducedCoord (d := d)
                i ⟨i.val + 1, hi⟩
                (BHW.reducedDiffMapReal (m + 1) d x);
            AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
                (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ P.V ∧
            (∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
              let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
                AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                  (d := d) i hi
                  (AdjacentNormal.reducedNormalFlatCanonicalDirection
                    (d := d) i hi)
              let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                  (d := d) i hi
                  (AdjacentNormal.reducedNormalFlattenCLE
                    (d := d) i ⟨i.val + 1, hi⟩ p)
              let uε : NPointDomain d (m + 1) :=
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
              BHW.extendF (bvt_F OS lgc (m + 1))
                  (BHW.os45FlatCommonChartSourceSide d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) =
                canonicalReducedBranch (d := d) OS lgc m ε
                  (AdjacentNormal.reducedCoordInv (d := d)
                    i ⟨i.val + 1, hi⟩
                    (AdjacentNormal.reducedAdjacent_succ_ne i hi) p)) ∧
            (∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
              let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
                AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                  (d := d) i hi
                  (AdjacentNormal.reducedNormalFlatCanonicalDirection
                    (d := d) i hi)
              let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                  (d := d) i hi
                  (AdjacentNormal.reducedNormalFlattenCLE
                    (d := d) i ⟨i.val + 1, hi⟩ p)
              let uε : NPointDomain d (m + 1) :=
                (BHW.os45CommonEdgeFlatCLE d (m + 1)
                  (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
              BHW.extendF (bvt_F OS lgc (m + 1))
                  (BHW.permAct (d := d)
                    (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                    (BHW.os45FlatCommonChartSourceSide d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) =
                canonicalReducedBranch (d := d) OS lgc m ε
                  (AdjacentNormal.reducedCoordInv (d := d)
                    i ⟨i.val + 1, hi⟩
                    (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                    (AdjacentNormal.reducedSignFlip
                      (d := d) i ⟨i.val + 1, hi⟩ p))) }) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_normalCanonicalRayEOWBranchDataOn_support
      (d := d) OS lgc ?_
  intro m i hi f hf_compact hf_support x hx
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  rcases hLocal m i hi f hf_compact hf_support x hx with
    ⟨P, hpP, hplus_source, hminus_source⟩
  have hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (AdjacentNormal.reducedNormalUpperCanonicalRay
                (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p) := by
    filter_upwards [hplus_source] with ε hε
    have hcoord :=
      AdjacentNormal.reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    exact (by simpa [p, ξ, j] using hcoord.trans hε)
  have hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (AdjacentNormal.reducedNormalLowerCanonicalRay
                (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
              (AdjacentNormal.reducedSignFlip (d := d) i j p)) := by
    filter_upwards [hminus_source] with ε hε
    have hcoord :=
      AdjacentNormal.reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc P p ε
    exact (by simpa [p, ξ, j] using hcoord.trans hε)
  exact
    AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_of_selectedJostData
      (d := d) OS lgc P (hOverlap m) (hData m) p
      (by simpa [p, ξ, j] using hpP)
      hplus_rep hminus_rep

/-- Support-local OS45/Ruelle producer from selected Jost data and asymptotic
source-side branch transfer.

This is the OS-I `(4.14)` version of
`adjacentReducedRuelleDistributionalLimit_of_selectedJostData_OS45NormalBranches_support`:
the local Figure-2-4 patch and the selected Jost/Ruelle seed still supply the
common EOW branch, but the two side source paths only have to converge to the
canonical reduced branch representatives. -/
theorem adjacentReducedRuelleDistributionalLimit_of_selectedJostData_OS45NormalBranches_asymptotic_support
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hOverlap :
      ∀ (m : ℕ) (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hData :
      ∀ m : ℕ,
        SelectedAdjacentDistributionalJostAnchorData OS lgc (m + 1))
    (hLocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          { P : BHW.OS45Figure24CanonicalSourcePatchData
              (d := d) hd (m + 1) i hi //
            let p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩ :=
              AdjacentNormal.reducedCoord (d := d)
                i ⟨i.val + 1, hi⟩
                (BHW.reducedDiffMapReal (m + 1) d x);
            AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
                (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                ((0 : SpacetimeDim d), p) ∈ P.V ∧
            Filter.Tendsto
              (fun ε : ℝ =>
                let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (AdjacentNormal.reducedNormalFlatCanonicalDirection
                      (d := d) i hi)
                let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (AdjacentNormal.reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)
                let uε : NPointDomain d (m + 1) :=
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
                BHW.extendF (bvt_F OS lgc (m + 1))
                    (BHW.os45FlatCommonChartSourceSide d (m + 1)
                      (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (AdjacentNormal.reducedCoordInv (d := d)
                      i ⟨i.val + 1, hi⟩
                      (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) ∧
            Filter.Tendsto
              (fun ε : ℝ =>
                let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (AdjacentNormal.reducedNormalFlatCanonicalDirection
                      (d := d) i hi)
                let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
                  AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
                    (d := d) i hi
                    (AdjacentNormal.reducedNormalFlattenCLE
                      (d := d) i ⟨i.val + 1, hi⟩ p)
                let uε : NPointDomain d (m + 1) :=
                  (BHW.os45CommonEdgeFlatCLE d (m + 1)
                    (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
                BHW.extendF (bvt_F OS lgc (m + 1))
                    (BHW.permAct (d := d)
                      (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
                      (BHW.os45FlatCommonChartSourceSide d (m + 1)
                        (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) -
                  canonicalReducedBranch (d := d) OS lgc m ε
                    (AdjacentNormal.reducedCoordInv (d := d)
                      i ⟨i.val + 1, hi⟩
                      (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                      (AdjacentNormal.reducedSignFlip
                        (d := d) i ⟨i.val + 1, hi⟩ p)))
              (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
              (nhds 0) }) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hf_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f ?_
  intro x hx
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let hij : i ≠ j := AdjacentNormal.reducedAdjacent_succ_ne i hi
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  rcases hLocal m i hi f hf_compact hf_support x hx with
    ⟨P, hpP, hplus_source_transfer, hminus_source_transfer⟩
  have hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalUpperCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hplus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        hcoord
    simpa [p, ξ, j] using hsub.symm
  have hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalLowerCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hminus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc P p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        hcoord
    simpa [p, ξ, j] using hsub.symm
  have hnormal :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij
                (AdjacentNormal.reducedSignFlip (d := d) i j p)) -
            @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    exact
      AdjacentNormal.reducedNormalSignFlip_pointwise_of_selectedJostData_asymptotic
        (d := d) OS lgc P (hOverlap m) (hData m) p
        (by simpa [p, ξ, j] using hpP)
        hplus_transfer hminus_transfer
  have hp_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij p = ξ := by
    simpa [p] using
      AdjacentNormal.reducedCoordInv_left (d := d) i j hij ξ
  have hsign_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij
          (AdjacentNormal.reducedSignFlip (d := d) i j p) =
        realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ := by
    have h :=
      AdjacentNormal.reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
        (d := d) i hi p
    simpa [j, hij, hp_inv] using h
  have hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
            @canonicalReducedBranch d _ OS lgc m ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [j, hij, p, hp_inv, hsign_inv] using hnormal
  refine Filter.Tendsto.congr' ?_ hcanon
  filter_upwards with ε
  symm
  have hbranch :
      @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ =
        @canonicalReducedBranch d _ OS lgc m ε
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
    rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ,
      canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
        (d := d) OS lgc m i j ε ξ]
  have hsub :=
    congrArg
      (fun z : ℂ => z - @canonicalReducedBranch d _ OS lgc m ε ξ) hbranch
  simpa [adjacentReducedPermutedBranch, canonicalReducedBranch, ξ, j] using hsub

/-- Point-local OS45 data for the reduced-normal Ruelle handoff, stated with
local edge pairing rather than selected Jost anchor data.

The packet keeps the true OS-I input visible: a local adjacent real-edge pairing
window, plus the two `(4.12)`--`(4.14)` moving source-side formulas identifying
the OS45 source rays with the canonical reduced rays. -/
structure LocalEdgePairingOS45NormalBranchPacket
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} (hi : i.val + 1 < m + 1)
    (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩) where
  P : BHW.OS45Figure24CanonicalSourcePatchData
    (d := d) hd (m + 1) i hi
  hpP :
    AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d), p) ∈ P.V
  Vedge : Set (NPointDomain d (m + 1))
  hVedge_open : IsOpen Vedge
  hVedge_nonempty : Vedge.Nonempty
  hVedge_ET :
    ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1)
  hVedge_swapET :
    ∀ x ∈ Vedge,
      BHW.realEmbed (fun k => x (P.τ k)) ∈
        BHW.ExtendedTube d (m + 1)
  hPairing :
    ∀ φ : SchwartzNPoint d (m + 1),
      HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
      tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
      (∫ x : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
        =
      ∫ x : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x
  hplus_source :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
        AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
          (d := d) i hi
          (AdjacentNormal.reducedNormalFlatCanonicalDirection
            (d := d) i hi)
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
          (d := d) i hi
          (AdjacentNormal.reducedNormalFlattenCLE
            (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
      BHW.extendF (bvt_F OS lgc (m + 1))
          (BHW.os45FlatCommonChartSourceSide d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (AdjacentNormal.reducedCoordInv (d := d)
            i ⟨i.val + 1, hi⟩
            (AdjacentNormal.reducedAdjacent_succ_ne i hi) p)
  hminus_source :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
        AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
          (d := d) i hi
          (AdjacentNormal.reducedNormalFlatCanonicalDirection
            (d := d) i hi)
      let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
        AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
          (d := d) i hi
          (AdjacentNormal.reducedNormalFlattenCLE
            (d := d) i ⟨i.val + 1, hi⟩ p)
      let uε : NPointDomain d (m + 1) :=
        (BHW.os45CommonEdgeFlatCLE d (m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
      BHW.extendF (bvt_F OS lgc (m + 1))
          (BHW.permAct (d := d)
            (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) =
        canonicalReducedBranch (d := d) OS lgc m ε
          (AdjacentNormal.reducedCoordInv (d := d)
            i ⟨i.val + 1, hi⟩
            (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip
                  (d := d) i ⟨i.val + 1, hi⟩ p))

/-- Point-local OS45 data for the reduced-normal Ruelle handoff, with the
OS-I source-side transfer stated asymptotically.

This is the form aligned with `(4.12)`--`(4.14)`: the moving source-side rays
need only converge to the canonical reduced branch representatives in boundary
value, not agree at every positive height. -/
structure LocalEdgePairingOS45NormalAsymptoticBranchPacket
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} {i : Fin (m + 1)} (hi : i.val + 1 < m + 1)
    (p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩) where
  P : BHW.OS45Figure24CanonicalSourcePatchData
    (d := d) hd (m + 1) i hi
  hpP :
    AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.reducedAdjacent_succ_ne i hi)
        ((0 : SpacetimeDim d), p) ∈ P.V
  Vedge : Set (NPointDomain d (m + 1))
  hVedge_open : IsOpen Vedge
  hVedge_nonempty : Vedge.Nonempty
  hVedge_ET :
    ∀ x ∈ Vedge, BHW.realEmbed x ∈ BHW.ExtendedTube d (m + 1)
  hVedge_swapET :
    ∀ x ∈ Vedge,
      BHW.realEmbed (fun k => x (P.τ k)) ∈
        BHW.ExtendedTube d (m + 1)
  hPairing :
    ∀ φ : SchwartzNPoint d (m + 1),
      HasCompactSupport (φ : NPointDomain d (m + 1) → ℂ) →
      tsupport (φ : NPointDomain d (m + 1) → ℂ) ⊆ Vedge →
      (∫ x : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.realEmbed (fun k => x (P.τ k))) * φ x)
        =
      ∫ x : NPointDomain d (m + 1),
          BHW.extendF (bvt_F OS lgc (m + 1)) (BHW.realEmbed x) * φ x
  hplus_source_transfer :
    Filter.Tendsto
      (fun ε : ℝ =>
        let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
          AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
            (d := d) i hi
            (AdjacentNormal.reducedNormalFlatCanonicalDirection
              (d := d) i hi)
        let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
          AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
            (d := d) i hi
            (AdjacentNormal.reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p)
        let uε : NPointDomain d (m + 1) :=
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 - ε • η)
        BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.os45FlatCommonChartSourceSide d (m + 1)
              (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ) ε η uε) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i ⟨i.val + 1, hi⟩
              (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0)
  hminus_source_transfer :
    Filter.Tendsto
      (fun ε : ℝ =>
        let η : BHW.OS45FlatCommonChartReal d (m + 1) :=
          AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
            (d := d) i hi
            (AdjacentNormal.reducedNormalFlatCanonicalDirection
              (d := d) i hi)
        let x0 : BHW.OS45FlatCommonChartReal d (m + 1) :=
          AdjacentNormal.reducedNormalToOS45CommonEdgeFlatCLM
            (d := d) i hi
            (AdjacentNormal.reducedNormalFlattenCLE
              (d := d) i ⟨i.val + 1, hi⟩ p)
        let uε : NPointDomain d (m + 1) :=
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))).symm (x0 + ε • η)
        BHW.extendF (bvt_F OS lgc (m + 1))
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin (m + 1)))).symm
              (BHW.os45FlatCommonChartSourceSide d (m + 1)
                (1 : Equiv.Perm (Fin (m + 1))) (-1 : ℝ) ε η uε)) -
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i ⟨i.val + 1, hi⟩
              (AdjacentNormal.reducedAdjacent_succ_ne i hi)
              (AdjacentNormal.reducedSignFlip
                (d := d) i ⟨i.val + 1, hi⟩ p)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0)

/-- Support-local OS45 edge-pairing packets feed the active reduced local CLM
route directly.

This is the theorem-2-facing Path 2 handoff: the local edge-pairing packet and
the two asymptotic `(4.12)`--`(4.14)` source-side transfers supply the
pointwise reduced-normal sign-flip convergence on every support collar, and the
checked reduced local CLM consumer does the smearing.  The proof deliberately
does not pass through `AdjacentReducedRuelleDistributionalLimit`. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_localEdgePairing_OS45NormalBranches_asymptotic
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hOverlap :
      ∀ (m : ℕ) (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hLocal :
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
                Nonempty
                  (LocalEdgePairingOS45NormalAsymptoticBranchPacket
                    (d := d) hd OS lgc hi
                    (AdjacentNormal.reducedCoord (d := d)
                      i ⟨i.val + 1, hi⟩ η))) :
    ReducedLocalAdjacentBoundaryCLMInvariant (d := d) OS lgc χ := by
  refine
    reducedLocalAdjacentBoundaryCLMInvariant_of_local_normalSignFlip_pointwise
      (d := d) OS lgc χ ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hLocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hVlocal⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport η hη
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j η
  rcases hVlocal ψ hψ_compact hψ_tsupport η hη with ⟨packet⟩
  have hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalUpperCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ packet.hplus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        hcoord
    simpa [p, j] using hsub.symm
  have hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (packet.P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalLowerCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ packet.hminus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc packet.P p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        hcoord
    simpa [p, j] using hsub.symm
  have hPOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) packet.P.τ z ∈
              BHW.ExtendedTube d (m + 1)} := by
    have hconn := hOverlap m i hi
    simpa [packet.P.τ_eq] using hconn
  exact
    AdjacentNormal.reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic
      (d := d) OS lgc packet.P hPOverlap
      packet.Vedge packet.hVedge_open packet.hVedge_nonempty
      packet.hVedge_ET packet.hVedge_swapET packet.hPairing p
      (by simpa [p, j] using packet.hpP)
      hplus_transfer hminus_transfer

/-- Legacy support-local OS45/Ruelle producer from concrete local edge pairing.

This is the selected-data-free version of the older Ruelle handoff.  At each
nonzero support point the local edge-pairing packet supplies the OS45 common
edge equality, and the checked reduced-normal bridge turns it into canonical-ray
EOW data; the existing supportwise DCT theorem then integrates the resulting
pointwise sign-flip limit.

Route guard: the theorem-2/E-to-R frontier now uses the Path 2 source-side
zero-representation / reduced-local-CLM route.  This Ruelle producer remains
checked infrastructure for diagnostics and regression comparison, not an active
theorem-2 input. -/
theorem adjacentReducedRuelleDistributionalLimit_of_localEdgePairing_OS45NormalBranches_support
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hOverlap :
      ∀ (m : ℕ) (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hLocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          LocalEdgePairingOS45NormalBranchPacket
            (d := d) hd OS lgc hi
            (AdjacentNormal.reducedCoord (d := d)
              i ⟨i.val + 1, hi⟩
              (BHW.reducedDiffMapReal (m + 1) d x))) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  refine
    adjacentReducedRuelleDistributionalLimit_of_normalCanonicalRayEOWBranchDataOn_support
      (d := d) OS lgc ?_
  intro m i hi f hf_compact hf_support x hx
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  let packet :=
    hLocal m i hi f hf_compact hf_support x hx
  have hplus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (1 : Equiv.Perm (Fin (m + 1)))
            (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (AdjacentNormal.reducedNormalUpperCanonicalRay
                (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p) := by
    filter_upwards [packet.hplus_source] with ε hε
    have hcoord :=
      AdjacentNormal.reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    exact (by simpa [p, ξ, j] using hcoord.trans hε)
  have hminus_rep :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
            (packet.P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
            (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
              (d := d) i hi
              (AdjacentNormal.reducedNormalLowerCanonicalRay
                (d := d) i hi p ε)) =
          canonicalReducedBranch (d := d) OS lgc m ε
            (AdjacentNormal.reducedCoordInv (d := d)
              i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
              (AdjacentNormal.reducedSignFlip (d := d) i j p)) := by
    filter_upwards [packet.hminus_source] with ε hε
    have hcoord :=
      AdjacentNormal.reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc packet.P p ε
    exact (by simpa [p, ξ, j] using hcoord.trans hε)
  have hPOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) packet.P.τ z ∈
              BHW.ExtendedTube d (m + 1)} := by
    have hconn := hOverlap m i hi
    simpa [packet.P.τ_eq] using hconn
  exact
    AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_of_localEdgePairing
      (d := d) OS lgc packet.P hPOverlap
      packet.Vedge packet.hVedge_open packet.hVedge_nonempty
      packet.hVedge_ET packet.hVedge_swapET packet.hPairing p
      (by simpa [p, ξ, j] using packet.hpP)
      hplus_rep hminus_rep

/-- Legacy support-local OS45/Ruelle producer from concrete local edge pairing and
asymptotic source-side branch transfer.

The local pairing window gives the common-edge/Ruelle seed; the source-side
moving families are only required to converge to the two canonical reduced
branch representatives, and the checked reduced-normal bridge supplies the
pointwise sign-flip limit integrated below.

Route guard: despite the source-side hypotheses, this theorem concludes the
legacy `AdjacentReducedRuelleDistributionalLimit` surface.  It should not be
used to close theorem 2 when the axiom-light Path 2
`ReducedLocalAdjacentBoundaryCLMInvariant` route is available. -/
theorem adjacentReducedRuelleDistributionalLimit_of_localEdgePairing_OS45NormalBranches_asymptotic_support
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hOverlap :
      ∀ (m : ℕ) (j : Fin (m + 1)) (hj : j.val + 1 < m + 1),
        IsConnected
          {z : Fin (m + 1) → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d (m + 1) ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d (m + 1)})
    (hLocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge
              (d := d) m i ⟨i.val + 1, hi⟩) →
        ∀ x, f.toFun x ≠ 0 →
          LocalEdgePairingOS45NormalAsymptoticBranchPacket
            (d := d) hd OS lgc hi
            (AdjacentNormal.reducedCoord (d := d)
              i ⟨i.val + 1, hi⟩
              (BHW.reducedDiffMapReal (m + 1) d x))) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hf_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
      (d := d) OS lgc m i j f ?_
  intro x hx
  let ξ : NPointDomain d m := BHW.reducedDiffMapReal (m + 1) d x
  let hij : i ≠ j := AdjacentNormal.reducedAdjacent_succ_ne i hi
  let p : AdjacentNormal.ReducedSpace d m i j :=
    AdjacentNormal.reducedCoord (d := d) i j ξ
  let packet :=
    hLocal m i hi f hf_compact hf_support x hx
  have hplus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (1 : Equiv.Perm (Fin (m + 1)))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalUpperCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ packet.hplus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalUpperCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi) p))
        hcoord
    simpa [p, ξ, j] using hsub.symm
  have hminus_transfer :
      Filter.Tendsto
        (fun ε : ℝ =>
          BHW.os45FlatCommonChartBranch d (m + 1) OS lgc
              (packet.P.τ.symm * (1 : Equiv.Perm (Fin (m + 1))))
              (AdjacentNormal.reducedNormalToOS45CommonEdgeComplexCLM
                (d := d) i hi
                (AdjacentNormal.reducedNormalLowerCanonicalRay
                  (d := d) i hi p ε)) -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ packet.hminus_source_transfer
    filter_upwards with ε
    have hcoord :=
      AdjacentNormal.reducedNormalLowerCanonicalRay_branch_eq_sourceSide_moving
        (d := d) OS lgc packet.P p ε
    have hsub :=
      congrArg
        (fun z : ℂ =>
          z -
            canonicalReducedBranch (d := d) OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d)
                i j (AdjacentNormal.reducedAdjacent_succ_ne i hi)
                (AdjacentNormal.reducedSignFlip (d := d) i j p)))
        hcoord
    simpa [p, ξ, j] using hsub.symm
  have hPOverlap :
      IsConnected
        {z : Fin (m + 1) → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d (m + 1) ∧
            BHW.permAct (d := d) packet.P.τ z ∈
              BHW.ExtendedTube d (m + 1)} := by
    have hconn := hOverlap m i hi
    simpa [packet.P.τ_eq] using hconn
  have hnormal :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij
                (AdjacentNormal.reducedSignFlip (d := d) i j p)) -
            @canonicalReducedBranch d _ OS lgc m ε
              (AdjacentNormal.reducedCoordInv (d := d) i j hij p))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    exact
      AdjacentNormal.reducedNormalSignFlip_pointwise_of_localEdgePairing_asymptotic
        (d := d) OS lgc packet.P hPOverlap
        packet.Vedge packet.hVedge_open packet.hVedge_nonempty
        packet.hVedge_ET packet.hVedge_swapET packet.hPairing p
        (by simpa [p, ξ, j] using packet.hpP)
        hplus_transfer hminus_transfer
  have hp_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij p = ξ := by
    simpa [p] using
      AdjacentNormal.reducedCoordInv_left (d := d) i j hij ξ
  have hsign_inv :
      AdjacentNormal.reducedCoordInv (d := d) i j hij
          (AdjacentNormal.reducedSignFlip (d := d) i j p) =
        realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ := by
    have h :=
      AdjacentNormal.reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
        (d := d) i hi p
    simpa [j, hij, hp_inv] using h
  have hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          @canonicalReducedBranch d _ OS lgc m ε
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
            @canonicalReducedBranch d _ OS lgc m ε ξ)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0) := by
    simpa [j, hij, p, hp_inv, hsign_inv] using hnormal
  refine Filter.Tendsto.congr' ?_ hcanon
  filter_upwards with ε
  symm
  have hbranch :
      @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ =
        @canonicalReducedBranch d _ OS lgc m ε
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
    rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ,
      canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
        (d := d) OS lgc m i j ε ξ]
  have hsub :=
    congrArg
      (fun z : ℂ => z - @canonicalReducedBranch d _ OS lgc m ε ξ) hbranch
  simpa [adjacentReducedPermutedBranch, canonicalReducedBranch, ξ, j] using hsub

/-- Forward-Jost support version of the reduced adjacent Ruelle boundary
limit.

The proof is not a wrapper: the reduced PET extension gives pointwise equality
of the two boundary approaches at each support point, and the already proved
reduced DCT theorem integrates that supportwise convergence. -/
theorem adjacentReducedRuelleDistributionalLimit_of_forwardJostSupport
    (hd : 1 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (f : SchwartzNPoint d (m + 1))
    (hf_forwardJost :
      ∀ x, f.toFun x ≠ 0 → x ∈ BHW.ForwardJostSet d (m + 1) hd) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) *
              (f x)) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  exact
    adjacentReducedRuelleDistributionalLimit_of_reducedPETSupport
      (d := d) OS lgc m i hi Fred f
      (fun x hx =>
        reducedDiffMapReal_mem_reducedPermutedExtendedTubeN_of_forwardJostSet
          (d := d) m hd x (hf_forwardJost x hx))

/-- Compact adjacent `bvt_W` locality on the forward-Jost support.

This is the end-to-end Jost-support half of the theorem-2 locality route:
forward-Jost support gives the reduced distributional boundary limit above,
the reduced/canonical-shell algebra transports it to the ordinary canonical
boundary family, and the boundary-value theorem identifies the two `bvt_W`
limits.  The missing full theorem is still the Ruelle extension from this
forward-Jost support statement to arbitrary compact adjacent-spacelike support. -/
theorem bvt_W_adjacent_swap_of_forwardJostSupport_reducedExtension_compact
    (hd : 1 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (f g : SchwartzNPoint d (m + 1))
    (hf_compact : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ))
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩))
    (hf_forwardJost :
      ∀ x, f.toFun x ≠ 0 → x ∈ BHW.ForwardJostSet d (m + 1) hd)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc (m + 1) f = bvt_W OS lgc (m + 1) g := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  have hreduced :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d (m + 1),
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) *
                (f x)) -
            ∫ x : NPointDomain d (m + 1),
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [j] using
      adjacentReducedRuelleDistributionalLimit_of_forwardJostSupport
        (d := d) hd OS lgc m i hi Fred f hf_forwardJost
  have hcanonical :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (g x)) -
            ∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    compact_canonicalShell_swap_tendsto_of_reduced_pair_tendsto
      (d := d) OS lgc m i j f g hf_compact
      (by simpa [j] using hsp)
      (by simpa [j] using hswap)
      hreduced
  let η := canonicalForwardConeDirection (d := d) (m + 1)
  have hη : InForwardCone d (m + 1) η :=
    canonicalForwardConeDirection_mem (d := d) (m + 1)
  have hfBV :=
    bvt_boundary_values (d := d) OS lgc (m + 1) f η hη
  have hgBV :=
    bvt_boundary_values (d := d) OS lgc (m + 1) g η hη
  have hdiff_limit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (g x)) -
            ∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (m + 1) g - bvt_W OS lgc (m + 1) f)) := by
    simpa [η, canonicalShell] using hgBV.sub hfBV
  have hzero : bvt_W OS lgc (m + 1) g - bvt_W OS lgc (m + 1) f = 0 :=
    tendsto_nhds_unique hdiff_limit hcanonical
  exact (sub_eq_zero.mp hzero).symm

/-- Full Schwartz adjacent `bvt_W` locality on the forward-Jost support.

This is the zero-off compact exhaustion step after the compact Jost-support
theorem above.  The approximants are cut off inside the intersection of the
selected spacelike region and the forward-Jost set, so the compact theorem keeps
both book hypotheses rather than relying on a support shortcut. -/
theorem bvt_W_adjacent_swap_of_forwardJostSupport_reducedExtension
    (hd : 1 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (f g : SchwartzNPoint d (m + 1))
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩))
    (hf_forwardJost :
      ∀ x, f.toFun x ≠ 0 → x ∈ BHW.ForwardJostSet d (m + 1) hd)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc (m + 1) f = bvt_W OS lgc (m + 1) g := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let U : Set (NPointDomain d (m + 1)) :=
    {x |
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) ∧
        x ∈ BHW.ForwardJostSet d (m + 1) hd}
  have hf_zero : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    by_contra hfx
    exact hxU ⟨hsp x hfx, hf_forwardJost x hfx⟩
  obtain ⟨fN, hfN_compact, hfN_zero, hfN_tendsto⟩ :=
    exists_compactSupportApprox_zeroOff_npoint (d := d) U f hf_zero
  let P : SchwartzNPoint d (m + 1) →L[ℂ] SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv)
  let gN : ℕ → SchwartzNPoint d (m + 1) := fun N => P (fN N)
  have hcompact_eq :
      ∀ N, bvt_W OS lgc (m + 1) (fN N) =
        bvt_W OS lgc (m + 1) (gN N) := by
    intro N
    refine
      bvt_W_adjacent_swap_of_forwardJostSupport_reducedExtension_compact
        (d := d) hd OS lgc m i hi Fred (fN N) (gN N)
        (hfN_compact N) ?_ ?_ ?_
    · intro x hfx
      have hxU : x ∈ U := by
        by_contra hxU
        exact hfx (hfN_zero N x hxU)
      exact hxU.1
    · intro x hfx
      have hxU : x ∈ U := by
        by_contra hxU
        exact hfx (hfN_zero N x hxU)
      exact hxU.2
    · intro x
      change
        P (fN N) x =
          (fN N).toFun (fun k => x (Equiv.swap i j k))
      rfl
  have hleft :
      Filter.Tendsto (fun N => bvt_W OS lgc (m + 1) (fN N))
        Filter.atTop (nhds (bvt_W OS lgc (m + 1) f)) :=
    ((bvt_W_continuous (d := d) OS lgc (m + 1)).tendsto f).comp hfN_tendsto
  have hP_tendsto :
      Filter.Tendsto (fun N => P (fN N)) Filter.atTop (nhds (P f)) :=
    (P.continuous.tendsto f).comp hfN_tendsto
  have hP_f : P f = g := by
    ext x
    exact (hswap x).symm
  have hgN_tendsto :
      Filter.Tendsto gN Filter.atTop (nhds g) := by
    simpa [gN, hP_f] using hP_tendsto
  have hright :
      Filter.Tendsto (fun N => bvt_W OS lgc (m + 1) (gN N))
        Filter.atTop (nhds (bvt_W OS lgc (m + 1) g)) :=
    ((bvt_W_continuous (d := d) OS lgc (m + 1)).tendsto g).comp hgN_tendsto
  have hleft_as_right :
      Filter.Tendsto (fun N => bvt_W OS lgc (m + 1) (fN N))
        Filter.atTop (nhds (bvt_W OS lgc (m + 1) g)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N => (hcompact_eq N).symm) hright
  exact tendsto_nhds_unique hleft hleft_as_right

end OSReconstruction
