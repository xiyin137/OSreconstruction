import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
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
  change
    @adjacentReducedPermutedBranch d _ OS lgc m i j ε ξ -
      @canonicalReducedBranch d _ OS lgc m ε ξ
      =
    @canonicalReducedBranch d _ OS lgc m ε
        (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) -
      @canonicalReducedBranch d _ OS lgc m ε ξ
  rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
      (d := d) OS lgc m i j ε ξ]
  rw [canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
      (d := d) OS lgc m i j ε ξ]

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
