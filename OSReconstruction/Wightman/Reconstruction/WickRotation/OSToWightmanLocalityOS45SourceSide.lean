import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal

/-!
# OS45 Source-Side Pullback Support

Small support lemmas for the strict OS-I/OS-II theorem-2 route.  These are
coordinate identities for the genuine OS45 `sourceSide` path; they do not
assert any boundary-value limit and do not package a branch-transfer wrapper.
-/

noncomputable section

open Complex Topology MeasureTheory Filter

namespace BHW

variable {d n : ℕ}

/-- Compact support transports from source variables to the flat common chart
through the inverse OS45 common-edge CLE.

This is a support-only fact for the fixed-test scalar-cancellation leaf; it
does not assert any boundary-value comparison. -/
theorem hasCompactSupport_comp_os45CommonEdgeFlatCLE_symm
    (ρperm : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (BHW.os45CommonEdgeFlatCLE d n ρperm).symm) ψ) :
        BHW.OS45FlatCommonChartReal d n → ℂ) := by
  simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    hψ_compact.comp_homeomorph
      (BHW.os45CommonEdgeFlatCLE d n ρperm).symm.toHomeomorph

variable [NeZero d]

/-- If a source test is supported in the canonical Figure-2-4 source patch,
then its inverse-CLE pullback to the flat common chart is supported on the
corresponding flat edge set.

This is the Lean support lemma used for the auxiliary `psi0Flat` in the
fixed-test scalar-cancellation argument.  It is only support transport; no
branch or distributional equality is used. -/
theorem tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (ρperm : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψV : tsupport (ψ : NPointDomain d n → ℂ) ⊆ P.V) :
    tsupport
      (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (BHW.os45CommonEdgeFlatCLE d n ρperm).symm) ψ) :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
      BHW.os45FlatCommonChartEdgeSet d n P ρperm := by
  intro x hx
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hxpre : e.symm x ∈ tsupport (ψ : NPointDomain d n → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (ψ : NPointDomain d n → ℂ) e.symm.continuous
    simpa [e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hpre hx
  have hxP : e.symm x ∈ P.V := hψV hxpre
  have hx_eq : x = e (e.symm x) := by
    simp [e]
  rw [hx_eq]
  exact
    (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P ρperm
      (e.symm x)).mpr hxP

omit [NeZero d] in
/-- Support transport through the inverse OS45 common-edge flat chart.

This is the source-collar side of the reduced-test lift bridge: once the
absolute source test is supported in a source window `U`, its flat
common-chart pullback is supported in the corresponding flat image of `U`. -/
theorem tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_image
    (ρperm : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    {U : Set (NPointDomain d n)}
    (hψU : tsupport (ψ : NPointDomain d n → ℂ) ⊆ U) :
    tsupport
      (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (BHW.os45CommonEdgeFlatCLE d n ρperm).symm) ψ) :
        BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
      BHW.os45CommonEdgeFlatCLE d n ρperm '' U := by
  intro x hx
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hxpre : e.symm x ∈ tsupport (ψ : NPointDomain d n → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (ψ : NPointDomain d n → ℂ) e.symm.continuous
    simpa [e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hpre hx
  exact ⟨e.symm x, hψU hxpre, by simp [e]⟩

/-- Support packet for the auxiliary fixed flat test used in the OS45
`sourceSide` scalar-cancellation argument.

If the original flat test is supported over a source window `U` contained in
the Figure-2-4 source patch, then the inverse-CLE pullback of the corresponding
zero-diagonal source test is compactly supported and supported on the flat
edge set.  This is only a support/integrability input. -/
theorem OS45Figure24SourceCutoffData.toZeroDiagonalCLM_flatPullback_support
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    {U : Set (NPointDomain d n)}
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n ρperm '' U)
    (hUP : U ⊆ P.V) :
    HasCompactSupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d n ρperm).symm)
          ((D.toZeroDiagonalCLM ρperm φ).1 : SchwartzNPoint d n)) :
          BHW.OS45FlatCommonChartReal d n → ℂ) ∧
      tsupport
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (BHW.os45CommonEdgeFlatCLE d n ρperm).symm)
          ((D.toZeroDiagonalCLM ρperm φ).1 : SchwartzNPoint d n)) :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P ρperm := by
  let ψ0 : SchwartzNPoint d n :=
    ((D.toZeroDiagonalCLM ρperm φ).1 : SchwartzNPoint d n)
  have hψ0_compact :
      HasCompactSupport (ψ0 : NPointDomain d n → ℂ) := by
    simpa [ψ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
      D.toSchwartzNPointCLM_hasCompactSupport ρperm φ
  have hψ0U : tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ U := by
    simpa [ψ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
      D.toSchwartzNPointCLM_tsupport_subset_image ρperm φ hφU
  have hψ0V : tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ P.V := hψ0U.trans hUP
  constructor
  · simpa [ψ0] using
      BHW.hasCompactSupport_comp_os45CommonEdgeFlatCLE_symm
        (d := d) (n := n) ρperm ψ0 hψ0_compact
  · simpa [ψ0] using
      BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet
        (d := d) (n := n) (P := P) ρperm ψ0 hψ0V

/-- Pulling a source test to the flat common-edge chart and then applying the
Figure-2-4 cutoff-pullback recovers the original source test, provided the
source test is supported inside the cutoff-one source patch.

This is the carrier-normalization leaf needed to turn flat common-edge
compact-test statements back into the arbitrary source-test form used by the
transported Wick pairing.  It is only cutoff algebra and support transport; it
does not assert any branch equality or boundary-value limit. -/
theorem OS45Figure24SourceCutoffData.toSchwartzNPointCLM_flatPullback_eq
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψV : tsupport (ψ : NPointDomain d n → ℂ) ⊆ P.V) :
    D.toSchwartzNPointCLM ρperm
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (BHW.os45CommonEdgeFlatCLE d n ρperm).symm) ψ) =
      ψ := by
  ext x
  by_cases hx : x ∈ tsupport (ψ : NPointDomain d n → ℂ)
  · have hxV : x ∈ P.V := hψV hx
    simp [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      D.χ_eq_one_on_V x hxV]
  · have hψx : (ψ : NPointDomain d n → ℂ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    simp [BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hψx]

/-- Zero-diagonal packaging of
`OS45Figure24SourceCutoffData.toSchwartzNPointCLM_flatPullback_eq`.

The equality is stated after forgetting the zero-diagonal subtype because the
target transported Wick pairing is a source-Schwartz pairing. -/
theorem OS45Figure24SourceCutoffData.toZeroDiagonalCLM_flatPullback_eq
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψV : tsupport (ψ : NPointDomain d n → ℂ) ⊆ P.V) :
    ((D.toZeroDiagonalCLM ρperm
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (BHW.os45CommonEdgeFlatCLE d n ρperm).symm) ψ)).1 :
        SchwartzNPoint d n) =
      ψ := by
  simpa [BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
    D.toSchwartzNPointCLM_flatPullback_eq ρperm ψ hψV

/-- Pointwise shifted-source form of the OS45 side-height branch.

After translating the source variable by `-(sgn * ε) • η` in flat common-edge
coordinates, the real base of the flat side-height point is the original
`e u`.  This is the coordinate identity underneath the shifted source-side
endpoint DCT; it deliberately does not identify the resulting point with an
ordinary reduced canonical ray. -/
theorem os45FlatCommonChartBranch_shiftedSource_eq_extendF
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    let e : NPointDomain d n ≃L[ℝ]
        BHW.OS45FlatCommonChartReal d n :=
      BHW.os45CommonEdgeFlatCLE d n ρperm
    let a : BHW.OS45FlatCommonChartReal d n := (sgn * ε) • η
    BHW.os45FlatCommonChartBranch d n OS lgc σ
        (fun j => (e u j : ℂ) + (a j : ℂ) * Complex.I) =
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) σ.symm
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η
            (e.symm (e u - a)))) := by
  intro e a
  rw [show
      (fun j => (e u j : ℂ) + (a j : ℂ) * Complex.I) =
        fun j =>
          ((BHW.os45CommonEdgeFlatCLE d n ρperm (e.symm (e u - a)) +
              (sgn * ε) • η) j : ℂ) +
            (((sgn * ε) • η) j : ℂ) * Complex.I by
    funext j
    simp [e, a, sub_eq_add_neg, Pi.add_apply]]
  simpa [e, a] using
    BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF
      d n OS lgc σ ρperm sgn ε η (e.symm (e u - a))

/-- Signed side-height branch integral pulled to source variables and unfolded
to the exact `extendF` value on the OS45 source-side configuration, without the
Figure-2-4 cutoff specialization.

This is the no-cutoff analogue of
`os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`.
It is only coordinate/Jacobian algebra: the OS-I `(4.14)` boundary-value limit
is a separate proof step. -/
theorem os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_shift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((x + (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ (x + (sgn * ε) • η))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u)) *
            φ (BHW.os45CommonEdgeFlatCLE d n ρperm u +
              (sgn * ε) • η) := by
  calc
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          φ x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((BHW.os45CommonEdgeFlatCLE d n ρperm u +
                    (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
            φ (BHW.os45CommonEdgeFlatCLE d n ρperm u +
              (sgn * ε) • η) :=
        BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift
          (d := d) (n := n) OS lgc σ ρperm
          ((sgn * ε) • η) ((sgn * ε) • η) φ hg_shift
    _ =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u)) *
            φ (BHW.os45CommonEdgeFlatCLE d n ρperm u +
              (sgn * ε) • η) := by
        congr 1

/-- Asymptotic endpoint transport from shifted source variables back to the
fixed flat side-height integral.

This is only the coordinate/Jacobian layer: if the shifted source-side pairing
has the desired endpoint limit, then the corresponding fixed flat side integral
has the same endpoint limit after multiplying by the common-edge Jacobian.  The
analytic/DCT content is exactly the source-side hypothesis. -/
theorem tendsto_flatCommonChart_branch_integral_sub_sourceSide_target_zero_of_shift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (Target : ℝ → ℂ)
    (hflat_int :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc σ
              (fun j =>
                ((x + (sgn * ε) • η) j : ℂ) +
                  (((sgn * ε) • η) j : ℂ) * Complex.I) *
            φ (x + (sgn * ε) • η)))
    (hsource :
      Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide
                  d n ρperm sgn ε η u)) *
              φ (BHW.os45CommonEdgeFlatCLE d n ρperm u +
                (sgn * ε) • η)) -
          Target ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
        (nhds 0)) :
    Tendsto
      (fun ε : ℝ =>
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
            φ x) -
        (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * Target ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let J : ℂ := (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ)
  let flat : ℝ → ℂ := fun ε =>
    ∫ x : BHW.OS45FlatCommonChartReal d n,
      BHW.os45FlatCommonChartBranch d n OS lgc σ
        (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
        φ x
  let source : ℝ → ℂ := fun ε =>
    ∫ u : NPointDomain d n,
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) σ.symm
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u)) *
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η)
  have hsource' :
      Tendsto (fun ε : ℝ => source ε - Target ε) l (nhds 0) := by
    simpa [l, source] using hsource
  have hscaled :
      Tendsto (fun ε : ℝ => J * (source ε - Target ε)) l (nhds 0) := by
    simpa [J] using
      (tendsto_const_nhds.mul hsource' :
        Tendsto (fun ε : ℝ => J * (source ε - Target ε)) l
          (nhds (J * 0)))
  refine Tendsto.congr' ?_ hscaled
  filter_upwards [hflat_int] with ε hε_int
  have hpull :=
    BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_shift
      (d := d) (n := n) OS lgc σ ρperm sgn ε η φ hε_int
  have hflat_source : flat ε = J * source ε := by
    simpa [flat, source, J] using hpull
  change J * (source ε - Target ε) = flat ε - J * Target ε
  rw [hflat_source]
  ring

/-- Reindex the shifted source-side pairing back to the fixed source test.

The source variable is translated by
`(os45CommonEdgeFlatCLE d n ρperm).symm ((sgn * ε) • η)`, so the shifted flat
test `φ (e u + (sgn * ε) • η)` becomes `φ (e u)` and the branch is evaluated
at the moving source point
`e.symm (e u - (sgn * ε) • η)`.  This is pure Lebesgue translation and
coordinate algebra; no branch-limit or boundary-value theorem is used. -/
theorem integral_sourceSide_shiftedTest_eq_movingSource_fixedTest
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (∫ u : NPointDomain d n,
      F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η)) =
      ∫ u : NPointDomain d n,
        F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η
          ((BHW.os45CommonEdgeFlatCLE d n ρperm).symm
            (BHW.os45CommonEdgeFlatCLE d n ρperm u - (sgn * ε) • η))) *
          φ (BHW.os45CommonEdgeFlatCLE d n ρperm u) := by
  let e : NPointDomain d n ≃L[ℝ] BHW.OS45FlatCommonChartReal d n :=
    BHW.os45CommonEdgeFlatCLE d n ρperm
  let a : BHW.OS45FlatCommonChartReal d n := (sgn * ε) • η
  let t : NPointDomain d n := e.symm a
  let g : NPointDomain d n → ℂ := fun u =>
    F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η
      (e.symm (e u - a))) * φ (e u)
  have htranslate :
      (∫ u : NPointDomain d n, g (u + t)) =
        ∫ u : NPointDomain d n, g u :=
    MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (NPointDomain d n))) g t
  calc
    (∫ u : NPointDomain d n,
      F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
        φ (BHW.os45CommonEdgeFlatCLE d n ρperm u + (sgn * ε) • η)) =
        ∫ u : NPointDomain d n, g (u + t) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with u
          simp [g, e, a, t, sub_eq_add_neg, add_assoc]
    _ = ∫ u : NPointDomain d n, g u := htranslate
    _ = ∫ u : NPointDomain d n,
        F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η
          ((BHW.os45CommonEdgeFlatCLE d n ρperm).symm
            (BHW.os45CommonEdgeFlatCLE d n ρperm u - (sgn * ε) • η))) *
          φ (BHW.os45CommonEdgeFlatCLE d n ρperm u) := by
          rfl

/-- Source-side pullback with the flat test translated so the real side-shift
cancels on source variables.

This is the coordinate identity used by the fixed-test `sourceSide` boundary
selection: the left side is a flat moving-test side-height integral, while the
right side is the source integral against the fixed pulled-back test
`ψFlat (e u)`. -/
theorem os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (ψFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hg_shift :
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((x + (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
          (SCV.translateSchwartz (-(sgn * ε) • η) ψFlat)
            (x + (sgn * ε) • η))) :
    ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc σ
          (fun j => (x j : ℂ) + (((sgn * ε) • η) j : ℂ) * Complex.I) *
          (SCV.translateSchwartz (-(sgn * ε) • η) ψFlat) x =
      (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u)) *
            ψFlat (BHW.os45CommonEdgeFlatCLE d n ρperm u) := by
  have h :=
    BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_shift
      (d := d) (n := n) OS lgc σ ρperm sgn ε η
      (SCV.translateSchwartz (-(sgn * ε) • η) ψFlat) hg_shift
  simpa [SCV.translateSchwartz_apply, add_assoc] using h

/-- The complex direction of the signed OS45 source-side ray after undoing the
quarter-turn chart. -/
def os45FlatCommonChartSourceSideDirection
    (_ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    Fin n → Fin (d + 1) → ℂ :=
  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
    (BHW.unflattenCfg n d
      (fun a => ((sgn • η) a : ℂ) + ((sgn • η) a : ℂ) * Complex.I))

/-- The OS45 source-side approach is affine in the side-height parameter.

This is only coordinate algebra.  It does not assert that the resulting
direction is an OS boundary direction or that the branch pairing has a
Schwinger limit; those are the analytic Figure-2-4/Jost boundary-value
lemmas. -/
theorem os45FlatCommonChartSourceSide_affine
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u =
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u +
        fun k μ => (ε : ℂ) *
          BHW.os45FlatCommonChartSourceSideDirection
            (d := d) (n := n) ρperm sgn η k μ := by
  ext k μ
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45FlatCommonChartSourceSide,
      BHW.os45FlatCommonChartSourceSideDirection,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg,
      BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
      flattenCLEquivReal_apply, Pi.add_apply]
    ring_nf
  · simp [BHW.os45FlatCommonChartSourceSide,
      BHW.os45FlatCommonChartSourceSideDirection,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg,
      BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
      flattenCLEquivReal_apply, Pi.add_apply, hμ]
    ring_nf

/-- The OS45 source-side path descends to reduced difference coordinates as an
affine side-height ray.

This is the quotient-coordinate form needed for the flat-to-reduced
distributional descent: before any analytic boundary-value argument is used,
the genuine OS45 side-height path has a fixed reduced base point and a fixed
reduced side direction. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_affine
    (ρperm : Equiv.Perm (Fin n))
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.reducedDiffMap n d
        (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) =
      BHW.reducedDiffMap n d
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) +
        (ε : ℂ) •
          BHW.reducedDiffMap n d
            (BHW.os45FlatCommonChartSourceSideDirection
              (d := d) (n := n) ρperm sgn η) := by
  rw [BHW.os45FlatCommonChartSourceSide_affine]
  change
    BHW.reducedDiffMap n d
        (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u +
          (ε : ℂ) •
            BHW.os45FlatCommonChartSourceSideDirection
              (d := d) (n := n) ρperm sgn η) =
      BHW.reducedDiffMap n d
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) +
        (ε : ℂ) •
          BHW.reducedDiffMap n d
            (BHW.os45FlatCommonChartSourceSideDirection
              (d := d) (n := n) ρperm sgn η)
  rw [map_add, map_smul]

/-- At zero side height, the genuine OS45 source-side chart lands on the
quarter-turned Wick carrier over the selected common-edge ordering. -/
@[simp] theorem os45FlatCommonChartSourceSide_zero
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u =
      BHW.os45QuarterTurnConfig (d := d) (n := n)
        (fun k => wickRotatePoint (u (ρperm k))) := by
  ext k μ
  have hdiv : (finProdFinEquiv (k, μ)).divNat = k := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, μ))).1 = k
    simp
  have hmod : (finProdFinEquiv (k, μ)).modNat = μ := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, μ))).2 = μ
    simp
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45FlatCommonChartSourceSide, BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint, BHW.os45QuarterTurnConfig,
      BHW.os45QuarterTurnCLE_symm_apply, wickRotatePoint,
      flattenCLEquivReal_apply, BHW.unflattenCfg, hdiv, hmod]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [BHW.os45FlatCommonChartSourceSide, BHW.os45CommonEdgeFlatCLE,
      BHW.os45CommonEdgeRealPoint, BHW.os45QuarterTurnConfig,
      BHW.os45QuarterTurnCLE_symm_apply, wickRotatePoint,
      flattenCLEquivReal_apply, BHW.unflattenCfg, hdiv, hmod, hμ]

/-- Zero side-height, after passing to reduced difference coordinates. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSide_zero
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.reducedDiffMap n d
        (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) =
      BHW.reducedDiffMap n d
        (BHW.os45QuarterTurnConfig (d := d) (n := n)
          (fun k => wickRotatePoint (u (ρperm k)))) := by
  rw [BHW.os45FlatCommonChartSourceSide_zero]

omit [NeZero d] in
/-- For the identity common-edge chart, the flat direction induced by the
canonical absolute forward-cone direction descends to the canonical reduced
imaginary direction.

The right hand side is deliberately written as a reduced difference of the
absolute canonical direction, so this OS45 coordinate file does not import the
heavier reduced-boundary modules.  Downstream, this rewrites via
`canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`. -/
theorem reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (BHW.os45FlatCommonChartSourceSideDirection
          (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1))) (1 : ℝ)
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1)))) =
      fun k μ =>
        BHW.reducedDiffMap (m + 1) d
          (fun r ν =>
            (canonicalForwardConeDirection (d := d) (m + 1) r ν : ℂ)) k μ *
          Complex.I := by
  ext k μ
  rw [BHW.reducedDiffMap_eq_successive_differences,
    BHW.reducedDiffMap_eq_successive_differences]
  have hmod_succ :
      (finProdFinEquiv
        ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val + 1, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  have hmod_curr :
      (finProdFinEquiv
        ((⟨k.val, by omega⟩ : Fin (m + 1)), μ)).modNat = μ := by
    change
      (finProdFinEquiv.symm
        (finProdFinEquiv
          ((⟨k.val, by omega⟩ : Fin (m + 1)), μ))).2 = μ
    simp
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45FlatCommonChartSourceSideDirection,
      BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg,
      flattenCLEquivReal_apply, canonicalForwardConeDirection,
      hmod_succ, hmod_curr]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  · simp [BHW.os45FlatCommonChartSourceSideDirection,
      BHW.os45CommonEdgeFlatCLE, BHW.os45CommonEdgeRealPoint,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.unflattenCfg,
      flattenCLEquivReal_apply, canonicalForwardConeDirection, hμ,
      hmod_succ, hmod_curr]

/-- The canonical absolute OS45 common-edge side-height is a valid flat
forward-cone direction.

This is the admissible side-height used for the OS-I Section 4.5 moving-source
comparison.  Together with
`reducedDiffMap_os45FlatCommonChartSourceSideDirection_canonical_id`, it records
that the cone-valid absolute height descends to the canonical reduced imaginary
direction. -/
theorem os45CommonEdgeFlatCLE_canonicalForwardConeDirection_mem_cone
    (m : ℕ) :
    BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1)) ∈
      BHW.os45FlatCommonChartCone d (m + 1) := by
  change BHW.unflattenCfgReal (m + 1) d
      (BHW.os45CommonEdgeFlatCLE d (m + 1)
        (1 : Equiv.Perm (Fin (m + 1)))
        (canonicalForwardConeDirection (d := d) (m + 1))) ∈
    BHW.ProductForwardConeReal d (m + 1)
  have hflat :
      BHW.unflattenCfgReal (m + 1) d
          (BHW.os45CommonEdgeFlatCLE d (m + 1)
            (1 : Equiv.Perm (Fin (m + 1)))
            (canonicalForwardConeDirection (d := d) (m + 1))) =
        BHW.os45CommonEdgeRealPoint (d := d) (n := m + 1)
          (1 : Equiv.Perm (Fin (m + 1)))
          (canonicalForwardConeDirection (d := d) (m + 1)) := by
    ext k μ
    simp [BHW.os45CommonEdgeFlatCLE, BHW.unflattenCfgReal,
      flattenCLEquivReal_apply]
  rw [hflat]
  intro k
  have hscale : 0 < (((k : ℕ) + 1 : ℝ) / 2) := by
    positivity
  have hcone :=
    inOpenForwardCone_smul_pos
      (BHW.safeBasepointVec_mem_forwardCone (d := d)) hscale
  convert hcone using 1
  ext μ
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45CommonEdgeRealPoint, canonicalForwardConeDirection,
      BHW.safeBasepointVec, Pi.smul_apply, smul_eq_mul]
  · simp [BHW.os45CommonEdgeRealPoint, canonicalForwardConeDirection,
      BHW.safeBasepointVec, Pi.smul_apply, smul_eq_mul, hμ]

omit [NeZero d] in
/-- Applying the inverse OS45 quarter-turn to the horizontal common-edge real
point gives the zero-height Wick carrier.

This is a coordinate identity used at the terminal endpoint of the strict
Figure-2-4 proof; it carries no boundary-value or branch-selection content. -/
theorem os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
    (ρperm : Equiv.Perm (Fin n))
    (u : NPointDomain d n) :
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm u)) =
      BHW.os45QuarterTurnConfig (d := d) (n := n)
        (fun k => wickRotatePoint (u (ρperm k))) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.os45QuarterTurnConfig,
      BHW.os45CommonEdgeRealPoint, BHW.realEmbed, wickRotatePoint]
    let a : ℂ := u (ρperm k) 0
    change (1 + Complex.I) * (a / 2) =
      Complex.I * a / 2 - Complex.I * a / 2 * Complex.I
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.os45QuarterTurnConfig,
      BHW.os45CommonEdgeRealPoint, BHW.realEmbed, wickRotatePoint, hμ]

/-- The zero-height source-side endpoint is the inverse quarter-turn of the
horizontal common-edge real point. -/
theorem os45FlatCommonChartSourceSide_zero_eq_commonEdge
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm u)) := by
  rw [BHW.os45FlatCommonChartSourceSide_zero,
    BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick]

/-- At zero side height, the identity common-edge source-side endpoint is the
terminal point of the Figure-2-4 identity path.

This is the coordinate bridge needed by the OS-I `(4.12)`--`(4.14)` transport
body: the source-side endpoint is not the raw Wick section, but the `t = 1`
endpoint of the checked horizontal Figure-2-4 path. -/
theorem os45FlatCommonChartSourceSide_zero_eq_identityPath_one
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartSourceSide d n
        (1 : Equiv.Perm (Fin n)) sgn 0 η u =
      BHW.os45Figure24IdentityPath (d := d) (n := n)
        u (1 : unitInterval) := by
  rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
  simpa using
    (BHW.os45Figure24IdentityPath_one (d := d) (n := n) u).symm

/-- Finite side height is the terminal Figure-2-4 identity-path endpoint plus
the explicit OS45 side direction.

This keeps the live branch/source transport target in the correct coordinates:
the analytic work starts at the `t = 1` Figure-2-4 endpoint and moves along the
signed side-height direction, rather than pretending the source-side ray is a
vertical Wick boundary ray from a real source point. -/
theorem os45FlatCommonChartSourceSide_id_eq_identityPath_one_add_direction
    (sgn ε : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.os45FlatCommonChartSourceSide d n
        (1 : Equiv.Perm (Fin n)) sgn ε η u =
      BHW.os45Figure24IdentityPath (d := d) (n := n)
          u (1 : unitInterval) +
        (ε : ℂ) •
          BHW.os45FlatCommonChartSourceSideDirection
            (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) sgn η := by
  rw [BHW.os45FlatCommonChartSourceSide_affine,
    BHW.os45FlatCommonChartSourceSide_zero_eq_identityPath_one]
  rfl

/-- Zero-height source-side endpoint after applying an additional branch
permutation.  This is the adjacent endpoint carrier coordinate identity used
before the pairing-level OS-I normalization. -/
@[simp] theorem permAct_os45FlatCommonChartSourceSide_zero
    (τ ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    BHW.permAct (d := d) τ
      (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) =
      BHW.os45QuarterTurnConfig (d := d) (n := n)
        (fun k => wickRotatePoint (u (ρperm (τ k)))) := by
  rw [BHW.os45FlatCommonChartSourceSide_zero]
  ext k μ
  simp [BHW.permAct, BHW.os45QuarterTurnConfig]

omit [NeZero d] in
/-- Applying a branch permutation to the inverse-quarter-turned horizontal
common edge gives the corresponding permuted Wick carrier. -/
theorem permAct_os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
    (τ ρperm : Equiv.Perm (Fin n))
    (u : NPointDomain d n) :
    BHW.permAct (d := d) τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρperm u))) =
      BHW.os45QuarterTurnConfig (d := d) (n := n)
        (fun k => wickRotatePoint (u (ρperm (τ k)))) := by
  rw [BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick]
  ext k μ
  simp [BHW.permAct, BHW.os45QuarterTurnConfig]

/-- The genuine OS45 source-side chart is continuous in side height and source
variables for fixed side direction.  This is the coordinate input for the
compact-collar dominated-convergence step. -/
theorem continuous_os45FlatCommonChartSourceSide
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    Continuous (fun p : ℝ × NPointDomain d n =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η p.2) := by
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hscale : Continuous (fun p : ℝ × NPointDomain d n => (sgn * p.1) • η) := by
    exact (continuous_const.mul continuous_fst).smul continuous_const
  have he : Continuous (fun p : ℝ × NPointDomain d n => e p.2) :=
    e.continuous.comp continuous_snd
  have hsum :
      Continuous (fun p : ℝ × NPointDomain d n => e p.2 + (sgn * p.1) • η) :=
    he.add hscale
  have hvec : Continuous (fun p : ℝ × NPointDomain d n =>
      fun a : Fin (n * (d + 1)) =>
        ((e p.2 + (sgn * p.1) • η) a : ℂ) +
          (((sgn * p.1) • η) a : ℂ) * Complex.I) := by
    refine continuous_pi ?_
    intro a
    have hreal : Continuous (fun p : ℝ × NPointDomain d n =>
        (e p.2 + (sgn * p.1) • η) a) :=
      (continuous_apply a).comp hsum
    have him : Continuous (fun p : ℝ × NPointDomain d n =>
        ((sgn * p.1) • η) a) :=
      (continuous_apply a).comp hscale
    exact (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  have hun : Continuous (fun p : ℝ × NPointDomain d n =>
      BHW.unflattenCfg n d
        (fun a : Fin (n * (d + 1)) =>
          ((e p.2 + (sgn * p.1) • η) a : ℂ) +
            (((sgn * p.1) • η) a : ℂ) * Complex.I)) := by
    exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
  have hmain := Q.symm.continuous.comp hun
  convert hmain using 2

/-- Compact-source-support collar for the genuine OS45 source-side path.

If the zero side-height slice of a compact source set lies in an open carrier,
then all sufficiently small positive side heights lie in the same carrier,
uniformly over that compact source set.  This is only topology and continuity;
it asserts no boundary-value limit and no branch normalization. -/
theorem eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ U := by
  have hcont :=
    BHW.continuous_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
  have hlocal :
      ∀ u ∈ K,
        ∀ᶠ p : ℝ × NPointDomain d n in 𝓝 ((0 : ℝ), u),
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η p.2 ∈ U := by
    intro u hu
    exact hcont.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds (h0 u hu))
  have hnhds :
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ U :=
    hK.eventually_forall_of_forall_eventually hlocal
  exact hnhds.filter_mono nhdsWithin_le_nhds

/-- Uniform branch bound on a compact source-side collar.

If a branch is continuous on an open carrier containing the zero side-height
slice of a compact source set, then its values on the genuine OS45 source-side
path are uniformly bounded for all sufficiently small positive side heights.
This is the finite-bound ingredient for dominated convergence only. -/
theorem exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          ‖F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u)‖ ≤ M := by
  have hcont :=
    BHW.continuous_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
  have hlocal :
      ∀ u ∈ K,
        ∀ᶠ p : ℝ × NPointDomain d n in 𝓝 ((0 : ℝ), u),
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η p.2 ∈ U := by
    intro u hu
    exact hcont.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds (h0 u hu))
  have hnhds :
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        ∀ u ∈ K,
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ U :=
    hK.eventually_forall_of_forall_eventually hlocal
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hnhds
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := half_pos hr_pos
  let collar : Set (Fin n → Fin (d + 1) → ℂ) :=
    (fun p : ℝ × NPointDomain d n =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η p.2) ''
        (Set.Icc (0 : ℝ) δ ×ˢ K)
  have hcollar_compact : IsCompact collar := by
    exact (isCompact_Icc.prod hK).image hcont
  have hcollar_sub : collar ⊆ U := by
    rintro z ⟨p, hp, rfl⟩
    rcases p with ⟨eps, u⟩
    rcases hp with ⟨heps, huK⟩
    have heps_ball : eps ∈ Metric.ball (0 : ℝ) r := by
      have heps_lt : eps < r :=
        heps.2.trans_lt (half_lt_self hr_pos)
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg heps.1]
        using heps_lt
    exact hr_sub heps_ball u huK
  obtain ⟨M0, hM0⟩ :=
    hcollar_compact.exists_bound_of_continuousOn
      (hF_cont.mono hcollar_sub)
  refine ⟨max M0 0, le_max_right _ _, ?_⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ_pos)]
    with eps heps_pos heps_lt u huK
  have heps_Icc : eps ∈ Set.Icc (0 : ℝ) δ := ⟨heps_pos.le, heps_lt.le⟩
  have hz_collar :
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ collar :=
    ⟨(eps, u), ⟨heps_Icc, huK⟩, rfl⟩
  exact (hM0 _ hz_collar).trans (le_max_left _ _)

/-- Continuity of the genuine OS45 source-side chart along the shifted source
argument that occurs in the endpoint DCT packet. -/
theorem continuous_os45FlatCommonChartSourceSide_moving
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    Continuous (fun p : ℝ × NPointDomain d n =>
      let e := BHW.os45CommonEdgeFlatCLE d n ρperm
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η
        (e.symm (e p.2 - (sgn * p.1) • η))) := by
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hscale : Continuous (fun p : ℝ × NPointDomain d n => (sgn * p.1) • η) := by
    exact (continuous_const.mul continuous_fst).smul continuous_const
  have he : Continuous (fun p : ℝ × NPointDomain d n => e p.2) :=
    e.continuous.comp continuous_snd
  have hvec : Continuous (fun p : ℝ × NPointDomain d n =>
      fun a : Fin (n * (d + 1)) =>
        ((e p.2) a : ℂ) + (((sgn * p.1) • η) a : ℂ) * Complex.I) := by
    refine continuous_pi ?_
    intro a
    have hreal : Continuous (fun p : ℝ × NPointDomain d n => (e p.2) a) :=
      (continuous_apply a).comp he
    have him : Continuous (fun p : ℝ × NPointDomain d n =>
        ((sgn * p.1) • η) a) :=
      (continuous_apply a).comp hscale
    exact (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  have hun : Continuous (fun p : ℝ × NPointDomain d n =>
      BHW.unflattenCfg n d
        (fun a : Fin (n * (d + 1)) =>
          ((e p.2) a : ℂ) + (((sgn * p.1) • η) a : ℂ) * Complex.I)) := by
    exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
  have hmain := Q.symm.continuous.comp hun
  convert hmain using 2
  funext p
  ext k
  simp [BHW.os45FlatCommonChartSourceSide, e, Q, Pi.add_apply]

/-- The shifted moving-source OS45 source-side path used in endpoint DCT. -/
def os45FlatCommonChartSourceSideMoving
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (eps : ℝ)
    (u : NPointDomain d n) :
    Fin n → Fin (d + 1) → ℂ :=
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η
    (e.symm (e u - (sgn * eps) • η))

/-- Continuity of the moving OS45 source-side path as a function of source
variable with side height fixed. -/
theorem continuous_os45FlatCommonChartSourceSide_moving_fixed_eps
    (ρperm : Equiv.Perm (Fin n))
    (sgn eps : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    Continuous fun u : NPointDomain d n =>
      let e := BHW.os45CommonEdgeFlatCLE d n ρperm
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η
        (e.symm (e u - (sgn * eps) • η)) := by
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hscale : Continuous (fun _u : NPointDomain d n => (sgn * eps) • η) := by
    exact continuous_const
  have he : Continuous (fun u : NPointDomain d n => e u) := e.continuous
  have hvec : Continuous (fun u : NPointDomain d n =>
      fun a : Fin (n * (d + 1)) =>
        ((e u) a : ℂ) + (((sgn * eps) • η) a : ℂ) * Complex.I) := by
    refine continuous_pi ?_
    intro a
    have hreal : Continuous (fun u : NPointDomain d n => (e u) a) :=
      (continuous_apply a).comp he
    have him : Continuous (fun u : NPointDomain d n => ((sgn * eps) • η) a) :=
      (continuous_apply a).comp hscale
    exact (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  have hun : Continuous (fun u : NPointDomain d n =>
      BHW.unflattenCfg n d
        (fun a : Fin (n * (d + 1)) =>
          ((e u) a : ℂ) + (((sgn * eps) • η) a : ℂ) * Complex.I)) := by
    exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
  have hmain := Q.symm.continuous.comp hun
  convert hmain using 2
  funext u
  ext k
  simp [BHW.os45FlatCommonChartSourceSide, e, Q, Pi.add_apply]

/-- Continuity of the moving OS45 source-side path in side height with the
outer source variable fixed. -/
theorem continuous_os45FlatCommonChartSourceSide_moving_fixed_source
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    Continuous fun eps : ℝ =>
      let e := BHW.os45CommonEdgeFlatCLE d n ρperm
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η
        (e.symm (e u - (sgn * eps) • η)) := by
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hscale : Continuous (fun eps : ℝ => (sgn * eps) • η) := by
    exact (continuous_const.mul continuous_id).smul continuous_const
  have hvec : Continuous (fun eps : ℝ =>
      fun a : Fin (n * (d + 1)) =>
        ((e u) a : ℂ) + (((sgn * eps) • η) a : ℂ) * Complex.I) := by
    refine continuous_pi ?_
    intro a
    have hreal : Continuous (fun _eps : ℝ => (e u) a) := continuous_const
    have him : Continuous (fun eps : ℝ => ((sgn * eps) • η) a) :=
      (continuous_apply a).comp hscale
    exact (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  have hun : Continuous (fun eps : ℝ =>
      BHW.unflattenCfg n d
        (fun a : Fin (n * (d + 1)) =>
          ((e u) a : ℂ) + (((sgn * eps) • η) a : ℂ) * Complex.I)) := by
    exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
  have hmain := Q.symm.continuous.comp hun
  convert hmain using 2
  funext eps
  ext k
  simp [BHW.os45FlatCommonChartSourceSide, e, Q, Pi.add_apply]

/-- Compact-source-support collar for the moving OS45 source-side path used by
the shifted endpoint DCT packet. -/
theorem eventually_forall_os45FlatCommonChartSourceSide_moving_mem_of_compact
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u ∈ K,
        let e := BHW.os45CommonEdgeFlatCLE d n ρperm
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η
          (e.symm (e u - (sgn * eps) • η)) ∈ U := by
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let moving : ℝ × NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η
        (e.symm (e p.2 - (sgn * p.1) • η))
  have hcont : Continuous moving := by
    change Continuous (fun p : ℝ × NPointDomain d n =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η
        (e.symm (e p.2 - (sgn * p.1) • η)))
    exact
      BHW.continuous_os45FlatCommonChartSourceSide_moving
        (d := d) (n := n) ρperm sgn η
  have hlocal :
      ∀ u ∈ K,
        ∀ᶠ p : ℝ × NPointDomain d n in 𝓝 ((0 : ℝ), u),
          moving p ∈ U := by
    intro u hu
    have harg_zero :
        e.symm (e u - (sgn * (0 : ℝ)) • η) = u := by
      simp [e]
    have h0_moving : moving ((0 : ℝ), u) ∈ U := by
      change
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn (0 : ℝ) η
          (e.symm (e u - (sgn * (0 : ℝ)) • η)) ∈ U
      rw [harg_zero]
      exact h0 u hu
    exact hcont.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds h0_moving)
  have hnhds :
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        ∀ u ∈ K, moving (eps, u) ∈ U :=
    hK.eventually_forall_of_forall_eventually hlocal
  change
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u ∈ K, moving (eps, u) ∈ U
  exact hnhds.filter_mono nhdsWithin_le_nhds

/-- Uniform branch bound on the compact collar for the moving OS45 source-side
path used by the shifted endpoint DCT packet. -/
theorem exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide_moving
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          let e := BHW.os45CommonEdgeFlatCLE d n ρperm
          ‖F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η
            (e.symm (e u - (sgn * eps) • η)))‖ ≤ M := by
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let moving : ℝ × NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η
        (e.symm (e p.2 - (sgn * p.1) • η))
  have hcont : Continuous moving := by
    change Continuous (fun p : ℝ × NPointDomain d n =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn p.1 η
        (e.symm (e p.2 - (sgn * p.1) • η)))
    exact
      BHW.continuous_os45FlatCommonChartSourceSide_moving
        (d := d) (n := n) ρperm sgn η
  have hlocal :
      ∀ u ∈ K,
        ∀ᶠ p : ℝ × NPointDomain d n in 𝓝 ((0 : ℝ), u),
          moving p ∈ U := by
    intro u hu
    have harg_zero :
        e.symm (e u - (sgn * (0 : ℝ)) • η) = u := by
      simp [e]
    have h0_moving : moving ((0 : ℝ), u) ∈ U := by
      change
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn (0 : ℝ) η
          (e.symm (e u - (sgn * (0 : ℝ)) • η)) ∈ U
      rw [harg_zero]
      exact h0 u hu
    exact hcont.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds h0_moving)
  have hnhds :
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        ∀ u ∈ K, moving (eps, u) ∈ U :=
    hK.eventually_forall_of_forall_eventually hlocal
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hnhds
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := half_pos hr_pos
  let collar : Set (Fin n → Fin (d + 1) → ℂ) :=
    moving '' (Set.Icc (0 : ℝ) δ ×ˢ K)
  have hcollar_compact : IsCompact collar := by
    exact (isCompact_Icc.prod hK).image hcont
  have hcollar_sub : collar ⊆ U := by
    rintro z ⟨p, hp, rfl⟩
    rcases p with ⟨eps, u⟩
    rcases hp with ⟨heps, huK⟩
    have heps_ball : eps ∈ Metric.ball (0 : ℝ) r := by
      have heps_lt : eps < r :=
        heps.2.trans_lt (half_lt_self hr_pos)
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg heps.1]
        using heps_lt
    exact hr_sub heps_ball u huK
  obtain ⟨M0, hM0⟩ :=
    hcollar_compact.exists_bound_of_continuousOn
      (hF_cont.mono hcollar_sub)
  refine ⟨max M0 0, le_max_right _ _, ?_⟩
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ_pos)]
    with eps heps_pos heps_lt u huK
  have heps_Icc : eps ∈ Set.Icc (0 : ℝ) δ := ⟨heps_pos.le, heps_lt.le⟩
  have hz_collar : moving (eps, u) ∈ collar :=
    ⟨(eps, u), ⟨heps_Icc, huK⟩, rfl⟩
  change ‖F (moving (eps, u))‖ ≤ max M0 0
  exact (hM0 _ hz_collar).trans (le_max_left _ _)

/-- Pointwise convergence of a branch along the genuine OS45 source-side path,
from continuity on an open carrier containing the zero side-height endpoint. -/
theorem tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    (h0 :
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    Tendsto
      (fun eps : ℝ =>
        F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u))
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u))) := by
  have hcont :=
    BHW.continuous_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
  have hpath :
      Continuous (fun eps : ℝ =>
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u) := by
    let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
    let e := BHW.os45CommonEdgeFlatCLE d n ρperm
    have hscale : Continuous (fun eps : ℝ => (sgn * eps) • η) := by
      exact (continuous_const.mul continuous_id).smul continuous_const
    have hsum :
        Continuous (fun eps : ℝ => e u + (sgn * eps) • η) :=
      continuous_const.add hscale
    have hvec : Continuous (fun eps : ℝ =>
        fun a : Fin (n * (d + 1)) =>
          ((e u + (sgn * eps) • η) a : ℂ) +
            (((sgn * eps) • η) a : ℂ) * Complex.I) := by
      refine continuous_pi ?_
      intro a
      have hreal : Continuous (fun eps : ℝ =>
          (e u + (sgn * eps) • η) a) :=
        (continuous_apply a).comp hsum
      have him : Continuous (fun eps : ℝ =>
          ((sgn * eps) • η) a) :=
        (continuous_apply a).comp hscale
      exact (Complex.continuous_ofReal.comp hreal).add
        ((Complex.continuous_ofReal.comp him).mul continuous_const)
    have hun : Continuous (fun eps : ℝ =>
        BHW.unflattenCfg n d
          (fun a : Fin (n * (d + 1)) =>
            ((e u + (sgn * eps) • η) a : ℂ) +
              (((sgn * eps) • η) a : ℂ) * Complex.I)) := by
      exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
    have hmain := Q.symm.continuous.comp hun
    convert hmain using 2
  have hF_at :
      ContinuousAt F
        (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) :=
    hF_cont.continuousAt (hU_open.mem_nhds h0)
  have hcomp :
      ContinuousAt
        (fun eps : ℝ =>
          F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u))
        (0 : ℝ) :=
    ContinuousAt.comp
      (x := (0 : ℝ))
      (f := fun eps : ℝ =>
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u)
      (g := F) hF_at hpath.continuousAt
  exact hcomp.tendsto.mono_left nhdsWithin_le_nhds

/-- AEStronglyMeasurability for a compact-support zero extension.

This is the endpoint-DCT measurability ingredient: if the branch factor and
test factor are continuous on the compact support and their product is zero
off that compact set, then the product is AEStronglyMeasurable.  It is a
neutral support lemma and asserts no boundary-value limit. -/
theorem aestronglyMeasurable_zeroExtension_mul_of_compactSupport
    {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α}
    {K : Set α} (hK : IsCompact K)
    {f g : α → ℂ}
    (hf_cont : ContinuousOn f K)
    (hg_cont : ContinuousOn g K)
    (hzero_off : ∀ x ∉ K, f x * g x = 0) :
    AEStronglyMeasurable (fun x : α => f x * g x) μ := by
  let h : α → ℂ := fun x => f x * g x
  have hK_meas : MeasurableSet K := hK.isClosed.measurableSet
  have h_cont : ContinuousOn h K := hf_cont.mul hg_cont
  have hind :
      AEStronglyMeasurable (Set.indicator K h) μ := by
    exact
      (aestronglyMeasurable_indicator_iff
        (μ := μ) (s := K) (f := h) hK_meas).2
        (h_cont.aestronglyMeasurable_of_isCompact hK hK_meas)
  have heq :
      Set.indicator K h =ᵐ[μ] fun x : α => f x * g x :=
    Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp [h, Set.indicator_of_mem hx]
      · simp [h, Set.indicator_of_notMem hx, hzero_off x hx]
  exact AEStronglyMeasurable.congr hind heq

/-- Continuity of the genuine OS45 source-side chart as a function of the
source variable, with side height fixed. -/
theorem continuous_os45FlatCommonChartSourceSide_fixed_eps
    (ρperm : Equiv.Perm (Fin n))
    (sgn eps : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n) :
    Continuous fun u : NPointDomain d n =>
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u := by
  let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  have hscale : Continuous (fun _u : NPointDomain d n => (sgn * eps) • η) := by
    exact continuous_const
  have he : Continuous (fun u : NPointDomain d n => e u) :=
    e.continuous
  have hsum :
      Continuous (fun u : NPointDomain d n => e u + (sgn * eps) • η) :=
    he.add hscale
  have hvec : Continuous (fun u : NPointDomain d n =>
      fun a : Fin (n * (d + 1)) =>
        ((e u + (sgn * eps) • η) a : ℂ) +
          (((sgn * eps) • η) a : ℂ) * Complex.I) := by
    refine continuous_pi ?_
    intro a
    have hreal : Continuous (fun u : NPointDomain d n =>
        (e u + (sgn * eps) • η) a) :=
      (continuous_apply a).comp hsum
    have him : Continuous (fun _u : NPointDomain d n =>
        ((sgn * eps) • η) a) :=
      continuous_const
    exact (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  have hun : Continuous (fun u : NPointDomain d n =>
      BHW.unflattenCfg n d
        (fun a : Fin (n * (d + 1)) =>
          ((e u + (sgn * eps) • η) a : ℂ) +
            (((sgn * eps) • η) a : ℂ) * Complex.I)) := by
    exact (differentiable_unflattenCfg_local n d).continuous.comp hvec
  have hmain := Q.symm.continuous.comp hun
  convert hmain using 2

/-- Fixed-height integrability for a compactly supported test along the genuine
OS45 `sourceSide` collar.

This is the pointwise-in-height version used inside eventual algebraic splits,
where the test itself may depend on the height parameter. -/
theorem integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn eps : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    (hmem :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ U)
    {M : ℝ}
    (hM :
      ∀ u ∈ K,
        ‖F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u)‖ ≤ M)
    (ψ : SchwartzNPoint d n)
    (hψ_zero : ∀ u ∉ K, (ψ : NPointDomain d n → ℂ) u = 0) :
    Integrable
      (fun u : NPointDomain d n =>
        F (BHW.os45FlatCommonChartSourceSide
          d n ρperm sgn eps η u) *
        (ψ : NPointDomain d n → ℂ) u) := by
  have hsource_cont :
      Continuous fun u : NPointDomain d n =>
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u := by
    exact
      BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
        (d := d) (n := n) ρperm sgn eps η
  have hbranch_cont_on_K :
      ContinuousOn
        (fun u : NPointDomain d n =>
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u)) K := by
    exact hF_cont.comp hsource_cont.continuousOn hmem
  have hzero_off :
      ∀ u ∉ K,
        F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u = 0 := by
    intro u hu
    simp [hψ_zero u hu]
  have hmeas :
      AEStronglyMeasurable
        (fun u : NPointDomain d n =>
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u) := by
    exact
      BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
        (μ := volume) (K := K) hK
        hbranch_cont_on_K ψ.continuous.continuousOn hzero_off
  have hbound :
      ∀ᵐ u : NPointDomain d n,
        ‖F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u‖ ≤
        M * ‖(ψ : NPointDomain d n → ℂ) u‖ := by
    filter_upwards with u
    by_cases hu : u ∈ K
    · calc
        ‖F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u‖
            = ‖F (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn eps η u)‖ *
              ‖(ψ : NPointDomain d n → ℂ) u‖ := by
                rw [norm_mul]
        _ ≤ M * ‖(ψ : NPointDomain d n → ℂ) u‖ :=
            mul_le_mul_of_nonneg_right (hM u hu) (norm_nonneg _)
    · simp [hψ_zero u hu]
  have hψ_compact :
      HasCompactSupport (ψ : NPointDomain d n → ℂ) := by
    exact
      HasCompactSupport.of_support_subset_isCompact hK
        (by
          intro u hu
          by_contra huK
          exact hu (hψ_zero u huK))
  have hψ_int : Integrable (ψ : NPointDomain d n → ℂ) :=
    ψ.continuous.integrable_of_hasCompactSupport hψ_compact
  exact (hψ_int.norm.const_mul M).mono' hmeas hbound

/-- Eventual integrability for compactly supported tests along the genuine
OS45 `sourceSide` collar.

This is the integrability input used when a moving source test is split into a
fixed test plus a compactly supported difference.  It uses only compact collar
membership, continuity of the terminal branch on its carrier, and the
Schwartz-test decay; it does not select or identify a boundary functional. -/
theorem eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    (ψ : SchwartzNPoint d n)
    (hψ_zero : ∀ u ∉ K, (ψ : NPointDomain d n → ℂ) u = 0) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      Integrable
        (fun u : NPointDomain d n =>
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u) := by
  rcases
    BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
      hK hU_open h0 hF_cont with
    ⟨M, _hM_nonneg, hM_bound⟩
  have hmem :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u ∈ U :=
    BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
      (d := d) (n := n) ρperm sgn η hK hU_open h0
  filter_upwards [hM_bound, hmem] with eps hM_eps hmem_eps
  have hsource_cont :
      Continuous fun u : NPointDomain d n =>
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u := by
    exact
      BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
        (d := d) (n := n) ρperm sgn eps η
  have hbranch_cont_on_K :
      ContinuousOn
        (fun u : NPointDomain d n =>
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u)) K := by
    exact hF_cont.comp hsource_cont.continuousOn hmem_eps
  have hzero_off :
      ∀ u ∉ K,
        F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u = 0 := by
    intro u hu
    simp [hψ_zero u hu]
  have hmeas :
      AEStronglyMeasurable
        (fun u : NPointDomain d n =>
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u) := by
    exact
      BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
        (μ := volume) (K := K) hK
        hbranch_cont_on_K ψ.continuous.continuousOn hzero_off
  have hbound :
      ∀ᵐ u : NPointDomain d n,
        ‖F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u‖ ≤
        M * ‖(ψ : NPointDomain d n → ℂ) u‖ := by
    filter_upwards with u
    by_cases hu : u ∈ K
    · calc
        ‖F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) *
          (ψ : NPointDomain d n → ℂ) u‖
            = ‖F (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn eps η u)‖ *
              ‖(ψ : NPointDomain d n → ℂ) u‖ := by
                rw [norm_mul]
        _ ≤ M * ‖(ψ : NPointDomain d n → ℂ) u‖ :=
            mul_le_mul_of_nonneg_right (hM_eps u hu) (norm_nonneg _)
    · simp [hψ_zero u hu]
  have hψ_compact :
      HasCompactSupport (ψ : NPointDomain d n → ℂ) := by
    exact
      HasCompactSupport.of_support_subset_isCompact hK
        (by
          intro u hu
          by_contra huK
          exact hu (hψ_zero u huK))
  have hψ_int : Integrable (ψ : NPointDomain d n → ℂ) :=
    ψ.continuous.integrable_of_hasCompactSupport hψ_compact
  exact (hψ_int.norm.const_mul M).mono' hmeas hbound

/-- Endpoint dominated convergence for a terminal branch along the genuine
OS45 source-side path.

This packages only the analytic support work used at the endpoint: compact
support, the source-side collar, the finite branch bound, pointwise continuity,
and zero-extension measurability.  It does not select a boundary functional or
identify any Wick/source pairing. -/
theorem tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {φ : NPointDomain d n → ℂ}
    (hφ_compact : HasCompactSupport φ)
    (hφ_cont : Continuous φ)
    (h0 :
      ∀ u ∈ tsupport φ,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    Tendsto
      (fun eps : ℝ =>
        ∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u) * φ u)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn 0 η u) * φ u)) := by
  let K : Set (NPointDomain d n) := tsupport φ
  have hK_compact : IsCompact K := hφ_compact.isCompact
  have h_eventual_collar :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u ∈ U := by
    exact
      BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
        (d := d) (n := n) ρperm sgn η
        hK_compact hU_open h0
  have h_pointwise :
      ∀ u : NPointDomain d n,
        Tendsto
          (fun eps : ℝ =>
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u) * φ u)
          (𝓝[Set.Ioi 0] (0 : ℝ))
          (𝓝
            (F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn 0 η u) * φ u)) := by
    intro u
    by_cases hu : u ∈ K
    · exact
        (BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
          (d := d) (n := n) ρperm sgn η u
          hU_open hF_cont (h0 u hu)).mul tendsto_const_nhds
    · have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
  rcases
    BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
      hK_compact hU_open h0 hF_cont with
    ⟨M, hM_nonneg, hM_bound⟩
  let g : NPointDomain d n → ℝ := fun u => M * ‖φ u‖
  have hg_int : Integrable g := by
    have hφ_int : Integrable φ := hφ_cont.integrable_of_hasCompactSupport hφ_compact
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using
      (hφ_int.norm.const_mul M)
  have hg_bound :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ᵐ u : NPointDomain d n,
          ‖F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u) * φ u‖ ≤ g u := by
    filter_upwards [hM_bound] with eps hM_eps
    filter_upwards with u
    by_cases hu : u ∈ K
    · calc
        ‖F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u) * φ u‖
            = ‖F (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn eps η u)‖ * ‖φ u‖ := by
                rw [norm_mul]
        _ ≤ M * ‖φ u‖ :=
            mul_le_mul_of_nonneg_right (hM_eps u hu) (norm_nonneg _)
        _ = g u := rfl
    · have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [g, hzero]
  have h_meas :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        AEStronglyMeasurable
          (fun u : NPointDomain d n =>
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u) * φ u) := by
    filter_upwards [h_eventual_collar] with eps heps
    have hsource_cont :
        Continuous fun u : NPointDomain d n =>
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u := by
      exact
        BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
          (d := d) (n := n) ρperm sgn eps η
    have hbranch_cont_on_K :
        ContinuousOn
          (fun u : NPointDomain d n =>
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u)) K := by
      exact hF_cont.comp hsource_cont.continuousOn heps
    have hzero_off :
        ∀ u ∉ K,
          F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u) * φ u = 0 := by
      intro u hu
      have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
    exact
      BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
        (μ := volume) (K := K) hK_compact
        hbranch_cont_on_K hφ_cont.continuousOn hzero_off
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := g)
  · exact h_meas
  · exact hg_bound
  · exact hg_int
  · exact Eventually.of_forall h_pointwise

/-- Endpoint dominated convergence for a terminal branch along the moving OS45
source-side path.

This is the fixed-test DCT packet for the shifted source argument
`e.symm (e u - (sgn * eps) • eta)`.  It proves only compact-support analytic
control for a continuous branch on a carrier; it does not identify the branch
with a reduced boundary value. -/
theorem tendsto_integral_comp_os45FlatCommonChartSourceSide_moving_mul_of_hasCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {φ : NPointDomain d n → ℂ}
    (hφ_compact : HasCompactSupport φ)
    (hφ_cont : Continuous φ)
    (h0 :
      ∀ u ∈ tsupport φ,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    Tendsto
      (fun eps : ℝ =>
        ∫ u : NPointDomain d n,
          F
            (BHW.os45FlatCommonChartSourceSideMoving
              (d := d) (n := n) ρperm sgn η eps u) * φ u)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) * φ u)) := by
  let K : Set (NPointDomain d n) := tsupport φ
  let e := BHW.os45CommonEdgeFlatCLE d n ρperm
  let moving : ℝ → NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
    fun eps u =>
      BHW.os45FlatCommonChartSourceSideMoving
        (d := d) (n := n) ρperm sgn η eps u
  have hK_compact : IsCompact K := hφ_compact.isCompact
  have h_eventual_collar :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K, moving eps u ∈ U := by
    simpa [moving, BHW.os45FlatCommonChartSourceSideMoving, e] using
      BHW.eventually_forall_os45FlatCommonChartSourceSide_moving_mem_of_compact
        (d := d) (n := n) ρperm sgn η hK_compact hU_open h0
  have h_pointwise :
      ∀ u : NPointDomain d n,
        Tendsto
          (fun eps : ℝ => F (moving eps u) * φ u)
          (𝓝[Set.Ioi 0] (0 : ℝ))
          (𝓝 (F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) * φ u)) := by
    intro u
    by_cases hu : u ∈ K
    · have hzero_arg : e.symm (e u - (sgn * (0 : ℝ)) • η) = u := by
        rw [mul_zero, zero_smul, sub_zero]
        exact e.symm_apply_apply u
      have hzero : moving (0 : ℝ) u =
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u := by
        change
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn (0 : ℝ) η
              (e.symm (e u - (sgn * (0 : ℝ)) • η)) =
            BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u
        rw [hzero_arg]
      have hpath_cont : Continuous (fun eps : ℝ => moving eps u) := by
        simpa [moving, BHW.os45FlatCommonChartSourceSideMoving, e] using
          BHW.continuous_os45FlatCommonChartSourceSide_moving_fixed_source
            (d := d) (n := n) ρperm sgn η u
      have hpath_tendsto :
          Tendsto (fun eps : ℝ => moving eps u) (𝓝 (0 : ℝ))
            (𝓝 (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u)) := by
        rw [← hzero]
        exact hpath_cont.continuousAt
      have hF_at :
          ContinuousAt F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) :=
        hF_cont.continuousAt (hU_open.mem_nhds (h0 u hu))
      exact
        ((hF_at.tendsto.comp hpath_tendsto).mono_left nhdsWithin_le_nhds).mul
          tendsto_const_nhds
    · have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
  rcases
    BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide_moving
      (d := d) (n := n) ρperm sgn η hK_compact hU_open h0 hF_cont with
    ⟨M, _hM_nonneg, hM_bound⟩
  let g : NPointDomain d n → ℝ := fun u => M * ‖φ u‖
  have hg_int : Integrable g := by
    have hφ_int : Integrable φ := hφ_cont.integrable_of_hasCompactSupport hφ_compact
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using
      (hφ_int.norm.const_mul M)
  have hg_bound :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ᵐ u : NPointDomain d n,
          ‖F (moving eps u) * φ u‖ ≤ g u := by
    filter_upwards [hM_bound] with eps hM_eps
    filter_upwards with u
    by_cases hu : u ∈ K
    · calc
        ‖F (moving eps u) * φ u‖
            = ‖F (moving eps u)‖ * ‖φ u‖ := by
              rw [norm_mul]
        _ ≤ M * ‖φ u‖ :=
            mul_le_mul_of_nonneg_right (hM_eps u hu) (norm_nonneg _)
        _ = g u := rfl
    · have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [g, hzero]
  have h_meas :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        AEStronglyMeasurable
          (fun u : NPointDomain d n => F (moving eps u) * φ u) := by
    filter_upwards [h_eventual_collar] with eps heps
    have hsource_cont : Continuous fun u : NPointDomain d n => moving eps u := by
      simpa [moving, BHW.os45FlatCommonChartSourceSideMoving, e] using
        BHW.continuous_os45FlatCommonChartSourceSide_moving_fixed_eps
          (d := d) (n := n) ρperm sgn eps η
    have hbranch_cont_on_K :
        ContinuousOn (fun u : NPointDomain d n => F (moving eps u)) K := by
      exact hF_cont.comp hsource_cont.continuousOn heps
    have hzero_off :
        ∀ u ∉ K, F (moving eps u) * φ u = 0 := by
      intro u hu
      have hzero : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
    exact
      BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
        (μ := volume) (K := K) hK_compact
        hbranch_cont_on_K hφ_cont.continuousOn hzero_off
  change Tendsto
    (fun eps : ℝ => ∫ u : NPointDomain d n, F (moving eps u) * φ u)
    (𝓝[Set.Ioi 0] (0 : ℝ))
    (𝓝
      (∫ u : NPointDomain d n,
        F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) * φ u))
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := g)
  · exact h_meas
  · exact hg_bound
  · exact hg_int
  · exact Eventually.of_forall h_pointwise

/-- Compact-support moving-test error estimate along the genuine OS45
`sourceSide` path.

If the moving Schwartz tests have an eventual common compact support with the
limit test, and their zeroth Schwartz seminorm difference tends to zero, then
pairing the difference with a terminal branch that is uniformly bounded on the
corresponding source-side compact collar tends to zero.  This is the analytic
moving-test perturbation used after a fixed-test boundary functional has already
been selected; it does not identify or construct that boundary functional. -/
theorem tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    {α : Type*} {l : Filter α}
    {eps : α → ℝ}
    (heps : Tendsto eps l (𝓝[Set.Ioi 0] (0 : ℝ)))
    {φseq : α → SchwartzNPoint d n} {φ0 : SchwartzNPoint d n}
    (hsupp :
      ∀ᶠ a in l,
        ∀ u ∉ K, ((φseq a - φ0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) u = 0)
    (hseminorm :
      Tendsto
        (fun a : α => SchwartzMap.seminorm ℝ 0 0 (φseq a - φ0 : SchwartzNPoint d n))
        l (𝓝 0)) :
    Tendsto
      (fun a : α =>
        ∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (eps a) η u) *
          ((φseq a - φ0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      l (𝓝 0) := by
  rcases
    BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
      (d := d) (n := n) ρperm sgn η
      hK hU_open h0 hF_cont with
    ⟨M, hM_nonneg, hM_bound⟩
  let C : ℝ := M * (volume K).toReal
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg hM_nonneg ENNReal.toReal_nonneg
  have hscaled :
      Tendsto
        (fun a : α =>
          C * SchwartzMap.seminorm ℝ 0 0 (φseq a - φ0 : SchwartzNPoint d n))
        l (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hseminorm)
  have hbound :
      ∀ᶠ a in l,
        ‖∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (eps a) η u) *
          ((φseq a - φ0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) u‖
        ≤ C * SchwartzMap.seminorm ℝ 0 0
          (φseq a - φ0 : SchwartzNPoint d n) := by
    have hM_comp :
        ∀ᶠ a in l,
          ∀ u ∈ K,
            ‖F (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn (eps a) η u)‖ ≤ M :=
      heps.eventually hM_bound
    filter_upwards [hsupp, hM_comp] with a hsupp_a hM_a
    let ψ : SchwartzNPoint d n := φseq a - φ0
    have hzero :
        ∀ u : NPointDomain d n, u ∉ K →
          F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (eps a) η u) *
            (ψ : NPointDomain d n → ℂ) u = 0 := by
      intro u hu
      have hψ : (ψ : NPointDomain d n → ℂ) u = 0 := by
        simpa [ψ] using hsupp_a u hu
      simp [hψ]
    have hK_fin : volume K < ⊤ := hK.measure_lt_top
    calc
      ‖∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (eps a) η u) *
          (ψ : NPointDomain d n → ℂ) u‖
        = ‖∫ u in K,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (eps a) η u) *
          (ψ : NPointDomain d n → ℂ) u‖ := by
            rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      _ ≤ (M * SchwartzMap.seminorm ℝ 0 0 ψ) * (volume K).toReal := by
            refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hK_fin ?_
            intro u hu
            calc
              ‖F (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn (eps a) η u) *
                  (ψ : NPointDomain d n → ℂ) u‖
                  = ‖F (BHW.os45FlatCommonChartSourceSide
                      d n ρperm sgn (eps a) η u)‖ *
                    ‖(ψ : NPointDomain d n → ℂ) u‖ := norm_mul _ _
              _ ≤ M * SchwartzMap.seminorm ℝ 0 0 ψ := by
                    gcongr
                    · exact hM_a u hu
                    · simpa using (SchwartzMap.le_seminorm ℝ 0 0 ψ u)
      _ = C * SchwartzMap.seminorm ℝ 0 0
          (φseq a - φ0 : SchwartzNPoint d n) := by
            simp [C, ψ, mul_assoc, mul_left_comm, mul_comm]
  exact squeeze_zero_norm' hbound hscaled

/-- Eventual common compact support input for the actual Figure-2-4 signed
side source tests.

If the flattened test is supported in the image of a source window `U`, and
`U` is contained in a compact source carrier `K`, then for sufficiently small
positive side heights both signed moving source tests and the unshifted source
test vanish off `K`.  This is the support hypothesis needed by
`tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport`
for the concrete `toSideZeroDiagonalCLM` family. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
    {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {U K : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub_K : U ⊆ K)
    (Kη : Set (BHW.OS45FlatCommonChartReal d n))
    (hKη : IsCompact Kη)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
      (∀ u ∉ K,
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) -
          ((((D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0) ∧
      (∀ u ∉ K,
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) -
          ((((D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0) := by
  have hside :=
    D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
      hU_open Kη hKη φ hφ_compact hφU
  have hzeroU :
      tsupport ((((D.toZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) ⊆ U := by
    simpa [BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
      D.toSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) φ hφU
  filter_upwards [hside] with ε hε η hη
  have hplusU := (hε η hη).1
  have hminusU := (hε η hη).2
  constructor
  · intro u huK
    have hplus_zero :
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0 := by
      exact
        image_eq_zero_of_notMem_tsupport
          (fun hu =>
            huK (hU_sub_K (hplusU hu)))
    have hbase_zero :
        ((((D.toZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0 := by
      exact
        image_eq_zero_of_notMem_tsupport
          (fun hu =>
            huK (hU_sub_K (hzeroU hu)))
    simp [hplus_zero, hbase_zero]
  · intro u huK
    have hminus_zero :
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0 := by
      exact
        image_eq_zero_of_notMem_tsupport
          (fun hu =>
            huK (hU_sub_K (hminusU hu)))
    have hbase_zero :
        ((((D.toZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) φ).1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0 := by
      exact
        image_eq_zero_of_notMem_tsupport
          (fun hu =>
            huK (hU_sub_K (hzeroU hu)))
    simp [hminus_zero, hbase_zero]

/-- Zeroth-seminorm convergence input for the actual Figure-2-4 signed side
source tests.

This specializes the checked Schwartz-space convergence of
`toSideZeroDiagonalCLM` to the precise seminorm used in the compact-support
moving-test estimate. -/
theorem OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
    {hd : 2 ≤ d} {n : ℕ}
    {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact : HasCompactSupport
      (φ : BHW.OS45FlatCommonChartReal d n → ℂ)) :
    Tendsto
      (fun ε : ℝ =>
        SchwartzMap.seminorm ℝ 0 0
          (((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) -
            ((D.toZeroDiagonalCLM ρperm φ).1 :
              SchwartzNPoint d n) : SchwartzNPoint d n))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hside :
      Tendsto
        (fun ε : ℝ =>
          ((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
            SchwartzNPoint d n))
        (𝓝 (0 : ℝ))
        (𝓝 ((D.toZeroDiagonalCLM ρperm φ).1 :
            SchwartzNPoint d n)) := by
    have h :=
      D.toSideZeroDiagonalCLM_tendsto_zero
        ρperm sgn η φ hφ_compact
    unfold ZeroDiagonalSchwartz at h
    exact (tendsto_subtype_rng.1 h)
  have hsub :
      Tendsto
        (fun ε : ℝ =>
          ((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
              SchwartzNPoint d n) -
            ((D.toZeroDiagonalCLM ρperm φ).1 :
              SchwartzNPoint d n))
        (𝓝 (0 : ℝ))
        (𝓝 (0 : SchwartzNPoint d n)) := by
    simpa using
      (hside.sub tendsto_const_nhds :
        Tendsto
          (fun ε : ℝ =>
            ((D.toSideZeroDiagonalCLM ρperm sgn ε η φ).1 :
                SchwartzNPoint d n) -
              ((D.toZeroDiagonalCLM ρperm φ).1 :
                SchwartzNPoint d n))
          (𝓝 (0 : ℝ))
          (𝓝 (((D.toZeroDiagonalCLM ρperm φ).1 :
              SchwartzNPoint d n) -
            ((D.toZeroDiagonalCLM ρperm φ).1 :
              SchwartzNPoint d n))))
  have hseminorm_cont :
      Continuous
        (fun ψ : SchwartzNPoint d n =>
          SchwartzMap.seminorm ℝ 0 0 ψ) :=
    (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ).continuous_seminorm
      (0, 0)
  simpa using (hseminorm_cont.tendsto (0 : SchwartzNPoint d n)).comp hsub

end BHW
