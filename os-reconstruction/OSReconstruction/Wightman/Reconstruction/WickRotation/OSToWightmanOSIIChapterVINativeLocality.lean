/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativePartialBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedBoundarySupport










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

def osiiAdjacentSpectatorHeight (j : Fin k) : NPointDomain d k :=
  Function.update (canonicalReducedDirection (d := d) k) j 0

theorem osiiAdjacentSpectatorHeight_mem_closure (j : Fin k) :
    osiiAdjacentSpectatorHeight (d := d) j ∈ closure (BHW.ProductForwardConeReal d k) := by
  let y := osiiAdjacentSpectatorHeight (d := d) j
  let eta := canonicalReducedDirection (d := d) k
  have hc : Continuous (fun t : Real => y + t • eta) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun t : Real => y + t • eta) (𝓝[>] 0) (𝓝 y) := by
    simpa using (hc.tendsto (0 : Real)).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro l
  have htpos : 0 < t := ht
  by_cases hl : l = j
  · subst l
    simpa [y, eta, osiiAdjacentSpectatorHeight] using
      BHW.inOpenForwardCone_smul_pos (canonicalReducedDirection_mem_productForwardConeReal k j) htpos
  · have hblock : (y + t • eta) l = (1 + t) • eta l := by
      ext mu
      simp [y, eta, osiiAdjacentSpectatorHeight, hl, add_mul]
    rw [hblock]
    exact BHW.inOpenForwardCone_smul_pos
      (canonicalReducedDirection_mem_productForwardConeReal k l) (by linarith)

omit [NeZero d] in
theorem osiiFlatten_mem_closure_productCone
    {y : NPointDomain d k} (hy : y ∈ closure (BHW.ProductForwardConeReal d k)) :
    flattenCLEquivReal k (d + 1) y ∈ closure (osiiReducedForwardFlatCone d k) := by
  have hclosed : IsClosed {z : NPointDomain d k |
      flattenCLEquivReal k (d + 1) z ∈ closure (osiiReducedForwardFlatCone d k)} :=
    isClosed_closure.preimage (flattenCLEquivReal k (d + 1)).continuous
  have hsub : BHW.ProductForwardConeReal d k ⊆ {z : NPointDomain d k |
      flattenCLEquivReal k (d + 1) z ∈ closure (osiiReducedForwardFlatCone d k)} := by
    intro z hz
    apply subset_closure
    rw [← OSIIReducedForwardTubeBoundaryData.flattenCLEquivReal_image_productForwardConeReal]
    exact ⟨z, hz, rfl⟩
  exact closure_minimal hsub hclosed hy

omit [NeZero d] in
theorem realPermOnReducedDiff_adjacent_eq_self_of_gap_zero
    (j : Fin k) (y : NPointDomain d k) (hy : y j = 0) :
    realPermOnReducedDiff (d := d) k (Equiv.swap j.castSucc j.succ) y = y := by
  let z := fun l mu => (y l mu : Complex)
  let s := BHW.reducedDiffSection (k + 1) d z
  have hpair : s j.succ = s j.castSucc := by
    ext mu
    apply sub_eq_zero.mp
    have h := congrFun (congrFun (BHW.reducedDiffMap_section (k + 1) d z) j) mu
    simpa [BHW.reducedDiffMap_eq_successive_differences, z, s, hy] using h
  have hswap : (fun a => s (Equiv.swap j.castSucc j.succ a)) = s := by
    ext a mu
    by_cases ha : a = j.castSucc
    · subst a
      simpa using congrFun hpair mu
    · by_cases hb : a = j.succ
      · subst a
        simpa using (congrFun hpair mu).symm
      · simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  have hp : BHW.permOnReducedDiff (n := k + 1) (d := d)
      (Equiv.swap j.castSucc j.succ) z = z := by
    rw [BHW.permOnReducedDiff_apply, hswap]
    exact BHW.reducedDiffMap_section (k + 1) d z
  ext l mu
  change (BHW.permOnReducedDiff (n := k + 1) (d := d)
    (Equiv.swap j.castSucc j.succ) z l mu).re = y l mu
  rw [hp]
  rfl

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}

theorem euclideanHolomorphicKernel_reducedPerm
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (sigma : Equiv.Perm (Fin (k + 1))) (z : Fin k -> Fin (d + 1) -> Complex) :
    H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d
      (BHW.permOnReducedDiff (n := k + 1) (d := d) sigma z)) =
      H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d z) := by
  rw [BHW.permOnReducedDiff_apply, BHW.reducedDiffSection_reducedDiffMap_eq_sub_basepoint]
  simpa only [sub_eq_add_neg] using
    (H.euclideanHolomorphicKernel_translate Hstage Rstage
      (fun a => BHW.reducedDiffSection (k + 1) d z (sigma a))
      (-BHW.reducedDiffSection (k + 1) d z (sigma 0))).trans
        (H.euclideanHolomorphicKernel_perm Hstage Rstage sigma (BHW.reducedDiffSection (k + 1) d z))

theorem euclideanHolomorphicKernel_shifted_reducedPerm
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (sigma : Equiv.Perm (Fin (k + 1))) (x y : NPointDomain d k)
    (hy : realPermOnReducedDiff (d := d) k sigma y = y) (u : Real) :
    H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d
      (fun l mu => (realPermOnReducedDiff (d := d) k sigma x l mu : Complex) +
        (u : Complex) * (y l mu : Complex) * I)) =
      H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d
        (fun l mu => (x l mu : Complex) + (u : Complex) * (y l mu : Complex) * I)) := by
  let z := fun l mu => (x l mu : Complex) + (u : Complex) * (y l mu : Complex) * I
  have hz : z = (fun l mu => (x l mu : Complex)) +
      ((u : Complex) * I) • (fun l mu => (y l mu : Complex)) := by
    ext l mu
    simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hperm : BHW.permOnReducedDiff (n := k + 1) (d := d) sigma z =
      fun l mu => (realPermOnReducedDiff (d := d) k sigma x l mu : Complex) +
        (u : Complex) * (y l mu : Complex) * I := by
    rw [hz, map_add, map_smul]
    ext l mu
    have hxC := congrFun (congrFun (ofReal_realPermOnReducedDiff_eq k sigma x) l) mu
    have hyC := congrFun (congrFun (ofReal_realPermOnReducedDiff_eq k sigma y) l) mu
    rw [hy] at hyC
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ = (realPermOnReducedDiff (d := d) k sigma x l mu : Complex) +
          ((u : Complex) * I) * (y l mu : Complex) :=
        congrArg₂ (fun a b : Complex => a + ((u : Complex) * I) * b) hxC.symm hyC.symm
      _ = _ := by ring
  exact (congrArg (fun w : Fin k -> Fin (d + 1) -> Complex =>
    H.euclideanHolomorphicKernel (BHW.reducedDiffSection (k + 1) d w)) hperm.symm).trans
      (H.euclideanHolomorphicKernel_reducedPerm Hstage Rstage sigma z)

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {OS : OsterwalderSchraderAxioms d}

private def spectatorPairing
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (j : Fin k) (u : Real) (phi : SchwartzNPoint d k) : Complex :=
  initial.strictGeneratedClosedFacePairing lgc k
    (flattenCLEquivReal k (d + 1) (osiiAdjacentSpectatorHeight (d := d) j))
    (osiiFlatten_mem_closure_productCone (osiiAdjacentSpectatorHeight_mem_closure j)) u
    (flattenSchwartzNPoint (d := d) phi)

private theorem spectatorPairing_tendsto
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (j : Fin k) (phi : SchwartzNPoint d k) :
    Tendsto (fun u => spectatorPairing initial lgc j u phi) (𝓝[>] (0 : Real))
      (𝓝 ((initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary phi)) := by
  have heq : unflattenSchwartzNPoint (flattenSchwartzNPoint (d := d) phi) = phi := by
    ext x
    simp only [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  simpa only [spectatorPairing, heq] using
    initial.strictGeneratedClosedFacePairing_tendsto lgc k
      (flattenCLEquivReal k (d + 1) (osiiAdjacentSpectatorHeight (d := d) j))
      (osiiFlatten_mem_closure_productCone (osiiAdjacentSpectatorHeight_mem_closure j))
      (flattenSchwartzNPoint (d := d) phi)

private theorem spectatorPairing_eq_integral
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (j : Fin k)
    (phi : SchwartzNPoint d k) (hcompact : HasCompactSupport (phi : _ -> Complex))
    (hsupport : ∀ x ∈ tsupport (phi : _ -> Complex), MinkowskiSpace.IsSpacelike d (x j))
    {u : Real} (hu : 0 < u) :
    spectatorPairing initial lgc j u phi =
      ∫ x : NPointDomain d k,
        (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanHolomorphicKernel
          (BHW.reducedDiffSection (k + 1) d (fun l mu => (x l mu : Complex) +
            (u : Complex) * (osiiAdjacentSpectatorHeight (d := d) j l mu : Complex) * I)) * phi x := by
  let y := flattenCLEquivReal k (d + 1) (osiiAdjacentSpectatorHeight (d := d) j)
  have hy : y ∈ closure (osiiReducedForwardFlatCone d k) :=
    osiiFlatten_mem_closure_productCone (osiiAdjacentSpectatorHeight_mem_closure j)
  let yu := u • y
  have hyu : yu ∈ closure (osiiReducedForwardFlatCone d k) :=
    osiiCone_smul_mem_closure osiiReducedForwardFlatCone_isCone hy hu
  have hyblock (l : Fin k) (mu : Fin (d + 1)) :
      BHW.unflattenCfgReal k d yu l mu = u * osiiAdjacentSpectatorHeight (d := d) j l mu := by
    simp [yu, y, BHW.unflattenCfgReal, flattenCLEquivReal_apply, smul_eq_mul]
  have hzero : BHW.unflattenCfgReal k d yu j = 0 := by
    ext mu
    rw [hyblock]
    simp [osiiAdjacentSpectatorHeight]
  have hother (l : Fin k) (hl : l ≠ j) :
      BHW.InOpenForwardCone d (BHW.unflattenCfgReal k d yu l) := by
    have heq : BHW.unflattenCfgReal k d yu l = u • canonicalReducedDirection (d := d) k l := by
      ext mu
      rw [hyblock]
      simp [osiiAdjacentSpectatorHeight, hl, smul_eq_mul]
    rw [heq]
    exact BHW.inOpenForwardCone_smul_pos (canonicalReducedDirection_mem_productForwardConeReal k l) hu
  have hflatcompact : HasCompactSupport ((flattenSchwartzNPoint (d := d) phi) : _ -> Complex) :=
    hcompact.comp_homeomorph (flattenCLEquivReal k (d + 1)).symm.toHomeomorph
  have hflatsupport : ∀ x ∈ tsupport ((flattenSchwartzNPoint (d := d) phi) : _ -> Complex),
      MinkowskiSpace.IsSpacelike d (BHW.unflattenCfgReal k d x j) := by
    intro x hx
    exact hsupport ((flattenCLEquivReal k (d + 1)).symm x)
      (tsupport_comp_subset_preimage (phi : _ -> Complex)
        (flattenCLEquivReal k (d + 1)).symm.continuous hx)
  have hrep := initial.strictGeneratedClosedFacePairing_eq_integral_of_mixedSpacelike lgc k j
    yu hyu hzero hother (flattenSchwartzNPoint (d := d) phi) hflatcompact hflatsupport
  have hleft : initial.strictGeneratedClosedFacePairing lgc k yu hyu 1
      (flattenSchwartzNPoint (d := d) phi) = spectatorPairing initial lgc j u phi := by
    dsimp only [strictGeneratedClosedFacePairing, spectatorPairing, yu]
    rw [osiiClosedConeDampedTest_smul (osiiReducedForwardFlatCone d k)
      osiiReducedForwardFlatCone_isCone y hy _ hu]
  rw [hleft] at hrep
  rw [hrep]
  symm
  rw [integral_flatten_change_of_variables k (d + 1)]
  apply integral_congr_ae
  filter_upwards with x
  have hphi : flattenSchwartzNPoint (d := d) phi (flattenCLEquivReal k (d + 1) x) = phi x := by
    change phi ((flattenCLEquivReal k (d + 1)).symm (flattenCLEquivReal k (d + 1) x)) = phi x
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hphi]
  simp only [OSIIReducedForwardTubeBoundaryData.flatEuclideanHolomorphicKernel]
  apply congrArg (fun w : Fin k -> Fin (d + 1) -> Complex =>
    (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanHolomorphicKernel
      (BHW.reducedDiffSection (k + 1) d w) * phi x)
  ext l mu
  simp [BHW.unflattenCfg, flattenCLEquivReal_apply, yu, y, smul_eq_mul]

theorem strictGeneratedReducedBoundary_adjacent_swap_of_compact_tsupport
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (j : Fin k)
    (phi : SchwartzNPoint d k) (hcompact : HasCompactSupport (phi : _ -> Complex))
    (hsupport : ∀ x ∈ tsupport (phi : _ -> Complex), MinkowskiSpace.IsSpacelike d (x j)) :
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (realPermOnReducedDiffCLE (d := d) k (Equiv.swap j.castSucc j.succ)) phi) =
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary phi := by
  have hj : j.castSucc.val + 1 < k + 1 := Nat.succ_lt_succ j.isLt
  let sigma := Equiv.swap j.castSucc j.succ
  let e := realPermOnReducedDiffCLE (d := d) k sigma
  let psi := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e phi
  have hpsicompact : HasCompactSupport (psi : _ -> Complex) :=
    hcompact.comp_homeomorph e.toHomeomorph
  have hpsisupport : ∀ x ∈ tsupport (psi : _ -> Complex), MinkowskiSpace.IsSpacelike d (x j) := by
    intro x hx
    have hs := hsupport (e x) (tsupport_comp_subset_preimage (phi : _ -> Complex) e.continuous hx)
    have he : e x j = -x j :=
      realPermOnReducedDiff_adjacentSwap_selected k j.castSucc hj x
    rw [he] at hs
    exact (minkowski_isSpacelike_neg_iff (x j)).mp hs
  have hfix : realPermOnReducedDiff (d := d) k sigma (osiiAdjacentSpectatorHeight (d := d) j) =
      osiiAdjacentSpectatorHeight (d := d) j :=
    realPermOnReducedDiff_adjacent_eq_self_of_gap_zero j _ (by simp [osiiAdjacentSpectatorHeight])
  have hpair (u : Real) (hu : 0 < u) :
      spectatorPairing initial lgc j u psi = spectatorPairing initial lgc j u phi := by
    rw [spectatorPairing_eq_integral initial lgc j psi hpsicompact hpsisupport hu,
      spectatorPairing_eq_integral initial lgc j phi hcompact hsupport hu]
    let F := fun x : NPointDomain d k =>
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanHolomorphicKernel
        (BHW.reducedDiffSection (k + 1) d (fun l mu => (x l mu : Complex) +
          (u : Complex) * (osiiAdjacentSpectatorHeight (d := d) j l mu : Complex) * I))
    have hF (x : NPointDomain d k) : F (e x) = F x :=
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanHolomorphicKernel_shifted_reducedPerm
        (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
        (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k)
        sigma x (osiiAdjacentSpectatorHeight (d := d) j) hfix u
    change (∫ x, F x * psi x) = ∫ x, F x * phi x
    calc
      (∫ x, F x * psi x) = ∫ x, F (e x) * phi (e x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hF]
        rfl
      _ = ∫ x, F x * phi x :=
        MeasurePreserving.integral_comp
          (realPermOnReducedDiff_adjacentSwap_measurePreserving (d := d) k j.castSucc hj)
          e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun x => F x * phi x)
  apply tendsto_nhds_unique (spectatorPairing_tendsto initial lgc j psi)
  apply (spectatorPairing_tendsto initial lgc j phi).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (hpair u hu).symm

theorem strictGeneratedReducedBoundary_adjacent_swap_of_compact_support
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (j : Fin k)
    (phi : SchwartzNPoint d k) (hcompact : HasCompactSupport (phi : _ -> Complex))
    (hsupport : ∀ x ∈ Function.support (phi : _ -> Complex), MinkowskiSpace.IsSpacelike d (x j)) :
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (realPermOnReducedDiffCLE (d := d) k (Equiv.swap j.castSucc j.succ)) phi) =
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary phi := by
  have hj : j.castSucc.val + 1 < k + 1 := Nat.succ_lt_succ j.isLt
  have hedge : Function.support (phi : _ -> Complex) ⊆
      reducedSpacelikeSwapEdge (d := d) k j.castSucc j.succ := by
    intro x hx
    exact (mem_reducedSpacelikeSwapEdge_adjacent_iff k j.castSucc hj x).mpr (hsupport x hx)
  obtain ⟨phiN, hcompactN, hsupportN, hlim⟩ :=
    reducedSpacelikeSwapEdge_strictTSupport_exhaustion_of_publicSupport
      (d := d) (m := k) j.castSucc hj phi hcompact hedge
  let B := (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
  let P : SchwartzNPoint d k →L[Complex] SchwartzNPoint d k :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (realPermOnReducedDiffCLE (d := d) k (Equiv.swap j.castSucc j.succ))
  have heq (N : Nat) : B (P (phiN N)) = B (phiN N) :=
    initial.strictGeneratedReducedBoundary_adjacent_swap_of_compact_tsupport lgc j
      (phiN N) (hcompactN N) (fun x hx =>
        (mem_reducedSpacelikeSwapEdge_adjacent_iff k j.castSucc hj x).mp (hsupportN N hx))
  apply tendsto_nhds_unique (((B.comp P).continuous.tendsto phi).comp hlim)
  apply ((B.continuous.tendsto phi).comp hlim).congr'
  exact Filter.Eventually.of_forall fun N => (heq N).symm

theorem strictGeneratedFullBoundary_adjacent_swap_of_compact_support
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (i : Fin (k + 1)) (hi : i.val + 1 < k + 1) (f g : SchwartzNPoint d (k + 1))
    (hcompact : HasCompactSupport (f : _ -> Complex))
    (hsp : ∀ x, f x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩))
    (hswap : ∀ x, g x = f (fun a => x (Equiv.swap i ⟨i.val + 1, hi⟩ a))) :
    initial.strictGeneratedFullBoundary lgc (k + 1) f = initial.strictGeneratedFullBoundary lgc (k + 1) g := by
  let j : Fin k := ⟨i.val, Nat.lt_of_succ_lt_succ hi⟩
  let sigma := Equiv.swap i ⟨i.val + 1, hi⟩
  have hg : g = SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      ((LinearEquiv.funCongrLeft Real (Fin (d + 1) -> Real) sigma).toContinuousLinearEquiv) f := by
    ext x
    exact hswap x
  let phi := diffVarReduction d k f
  have hphi : (phi : NPointDomain d k -> Complex) = reducedFiberMarginal (d := d) k f :=
    (reducedFiberMarginal_eq_diffVarReduction (d := d) k f).symm
  have hphicompact : HasCompactSupport (phi : _ -> Complex) := by
    rw [hphi]
    exact reducedFiberIntegral_hasCompactSupport k f hcompact
  have hphiedge : Function.support (phi : _ -> Complex) ⊆
      reducedSpacelikeSwapEdge (d := d) k i ⟨i.val + 1, hi⟩ := by
    rw [hphi]
    exact reducedFiberIntegral_support_subset_of_absolute_reduced_support k f _
      (fun x hx => reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
        k i ⟨i.val + 1, hi⟩ x (hsp x hx))
  have heq := initial.strictGeneratedReducedBoundary_adjacent_swap_of_compact_support lgc j phi hphicompact
    (fun x hx => (mem_reducedSpacelikeSwapEdge_adjacent_iff k i hi x).mp (hphiedge hx))
  change (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary (diffVarReduction d k f) =
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary (diffVarReduction d k g)
  rw [hg, diffVarReduction_absPerm_eq]
  exact heq.symm

/-- The literal public locality predicate, on full Schwartz tests and at
every arity, for the boundary reconstructed from the original OS data. -/
theorem strictGeneratedFullBoundary_locality
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (fun n f => initial.strictGeneratedFullBoundary lgc n f) := by
  intro n i hi f g hsp hswap
  cases n with
  | zero => exact Fin.elim0 i
  | succ k =>
      exact bv_local_commutativity_full_of_compact_support_adjacent_locality
        (W_n := initial.strictGeneratedFullBoundary lgc (k + 1))
        (initial.strictGeneratedFullBoundary lgc (k + 1)).continuous i hi
        (fun f g hf hsp hswap =>
          initial.strictGeneratedFullBoundary_adjacent_swap_of_compact_support lgc i hi f g hf hsp hswap)
        f g hsp hswap

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

end OSReconstruction
