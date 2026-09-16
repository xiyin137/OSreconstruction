/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanE0FiniteSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import OSReconstruction.Wightman.Reconstruction.SchwingerOS










noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

/-- The centered reduced block kernel lifted to the absolute Euclidean source
space on which the Schwinger functional is defined. -/
noncomputable def
    osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real) :
    SchwartzNPoint d (k + 1) :=
  BHW.reducedTestLift k d
    (BHW.normalizedCutoffOfBump d).toSchwartz
    (osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y')

/-- Public flat-coordinate map used to state support facts without depending
on the private implementation equivalence in `BlockIntegral`. -/
noncomputable def osiiStep4NPointFlatCLM (d k : Nat) :
    NPointDomain d k →L[Real] (Fin (k * (d + 1)) → Real) :=
  (flattenCLEquivReal k (d + 1)).toContinuousLinearMap

@[simp] theorem osiiStep4NPointFlatCLM_finProdFinEquiv
    (d k : Nat) (x : NPointDomain d k)
    (i : Fin k) (mu : Fin (d + 1)) :
    osiiStep4NPointFlatCLM d k x (finProdFinEquiv (i, mu)) = x i mu := by
  change x (finProdFinEquiv.symm (finProdFinEquiv (i, mu))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, mu))).2 = x i mu
  rw [finProdFinEquiv.symm_apply_apply]

private theorem reducedTestLift_tsupport_subset_local
    (d m : Nat)
    (chi : SchwartzMap (SpacetimeDim d) Complex)
    (phi : SchwartzNPoint d m) :
    tsupport
        ((BHW.reducedTestLift m d chi phi : SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → Complex) ⊆
      (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
        tsupport (phi : NPointDomain d m → Complex) := by
  let f : NPointDomain d (m + 1) → Complex :=
    ((BHW.reducedTestLift m d chi phi : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → Complex)
  have hsupport :
      Function.support f ⊆
        (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
          tsupport (phi : NPointDomain d m → Complex) := by
    intro x hx
    have hphi_ne :
        (phi : NPointDomain d m → Complex)
            (BHW.reducedDiffMapReal (m + 1) d x) ≠ 0 := by
      intro hzero
      apply hx
      change BHW.reducedTestLift m d chi phi x = 0
      rw [BHW.reducedTestLift_apply, mul_eq_zero]
      exact Or.inr hzero
    simpa [BHW.reducedDiffMapRealCLM] using
      subset_tsupport (phi : NPointDomain d m → Complex) hphi_ne
  exact closure_minimal hsupport
    ((isClosed_tsupport (phi : NPointDomain d m → Complex)).preimage
      (BHW.reducedDiffMapRealCLM (m + 1) d).continuous)

/-- The topological support of a centered reduced block kernel remains in the
closed radius-`rho / 4` flat support ball. -/
theorem
    osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_flat_mem_closedBall
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (x : NPointDomain d k)
    (hx : x ∈ tsupport
      ((osiiStep4CenteredPartialConvolutionKernelFullSource
        d k hrho center y y' : SchwartzNPoint d k) :
          NPointDomain d k → Complex)) :
    osiiStep4NPointFlatCLM d k x ∈
      Metric.closedBall center (rho / 4) := by
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  let K : Set (NPointDomain d k) :=
    (osiiStep4NPointFlatCLM d k) ⁻¹'
      Metric.closedBall center (rho / 4)
  have hsupport :
      Function.support (phi : NPointDomain d k → Complex) ⊆ K := by
    intro u hu
    have hflat :
        osiiStep4NPointFlatCLM d k u ∈
          Function.support
            (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
              (d + 1) k hrho center y y' :
                (Fin (k * (d + 1)) → Real) → Complex) := by
      rw [Function.mem_support] at hu ⊢
      intro hzero
      apply hu
      rw [show phi u =
          flattenSchwartzNPoint (d := d) phi
            (osiiStep4NPointFlatCLM d k u) by
        rw [flattenSchwartzNPoint_apply]
        congr 1
        funext i j
        simp [osiiStep4NPointFlatCLM, flattenCLEquivReal_apply]]
      rw [flatten_osiiStep4CenteredPartialConvolutionKernelFullSource]
      exact hzero
    exact
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
        (d + 1) k hrho center y y' hflat
  have hK : IsClosed K :=
    isClosed_closedBall.preimage (osiiStep4NPointFlatCLM d k).continuous
  exact closure_minimal hsupport hK hx

/-- The centered reduced partial-kernel source is compactly supported. -/
theorem
    osiiStep4CenteredPartialConvolutionKernelFullSource_hasCompactSupport
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real) :
    HasCompactSupport
      ((osiiStep4CenteredPartialConvolutionKernelFullSource
        d k hrho center y y' : SchwartzNPoint d k) :
          NPointDomain d k → Complex) := by
  have hflat :
      HasCompactSupport
        ((osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          (d + 1) k hrho center y y' :
            SchwartzMap (Fin (k * (d + 1)) → Real) Complex) :
              (Fin (k * (d + 1)) → Real) → Complex) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall center (rho / 4))
      (isCompact_closedBall center (rho / 4)) ?_
    exact
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_support_subset
        (d + 1) k hrho center y y'
  have hflat' :
      HasCompactSupport
        ((flattenSchwartzNPoint (d := d)
          (osiiStep4CenteredPartialConvolutionKernelFullSource
            d k hrho center y y')) :
              (Fin (k * (d + 1)) → Real) → Complex) := by
    convert hflat using 1
    ext z
    exact flatten_osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y' z
  convert hflat'.comp_homeomorph
      (flattenCLEquivReal k (d + 1)).toHomeomorph using 1
  ext z
  rw [Function.comp_apply, flattenSchwartzNPoint_apply]
  congr 1
  funext i j
  simp [flattenCLEquivReal_apply]

/-- If every center time is at least `rho`, every reduced time gap on the
support of the centered partial kernel is strictly positive. -/
theorem
    osiiStep4CenteredPartialConvolutionKernelFullSource_reduced_time_pos
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (xi : NPointDomain d k)
    (hxi : xi ∈ tsupport
      ((osiiStep4CenteredPartialConvolutionKernelFullSource
        d k hrho center y y' : SchwartzNPoint d k) :
          NPointDomain d k → Complex))
    (i : Fin k) :
    0 < xi i 0 := by
  have hball :=
    osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_flat_mem_closedBall
      d k hrho center y y' xi hxi
  have hnorm :
      ‖osiiStep4NPointFlatCLM d k xi - center‖ ≤ rho / 4 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  let idx : Fin (k * (d + 1)) :=
    finProdFinEquiv (i, (0 : Fin (d + 1)))
  have hcoord :
      |osiiStep4NPointFlatCLM d k xi idx - center idx| ≤ rho / 4 := by
    calc
      |osiiStep4NPointFlatCLM d k xi idx - center idx| =
          ‖(osiiStep4NPointFlatCLM d k xi - center) idx‖ := by
            simp [Real.norm_eq_abs]
      _ ≤ ‖osiiStep4NPointFlatCLM d k xi - center‖ :=
        norm_le_pi_norm _ idx
      _ ≤ rho / 4 := hnorm
  have hlower := (abs_le.mp hcoord).1
  have hc := hcenter i
  have hpositive : 0 < osiiStep4NPointFlatCLM d k xi idx := by
    dsimp only [idx] at hlower hc
    change 0 < osiiStep4NPointFlatCLM d k xi
      (finProdFinEquiv (i, (0 : Fin (d + 1))))
    nlinarith
  simpa [idx] using hpositive

/-- Positive reduced time centers keep the lifted source off every absolute
coincidence locus, so it is an honest zero-diagonal Euclidean test. -/
theorem
    osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource_vanishes
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    VanishesToInfiniteOrderOnCoincidence
      (osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho center y y') := by
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k → Complex) := by
    exact reducedTestLift_tsupport_subset_local d k
      (BHW.normalizedCutoffOfBump d).toSchwartz phi hx
  have hgap : ∀ i : Fin k, 0 < x i.succ 0 - x i.castSucc 0 := by
    intro i
    have hpositive :=
      osiiStep4CenteredPartialConvolutionKernelFullSource_reduced_time_pos
        d k hrho center y y' hcenter
          (BHW.reducedDiffMapReal (k + 1) d x) hred i
    rw [BHW.reducedDiffMapReal_apply] at hpositive
    exact hpositive
  have htime : StrictMono (fun i : Fin (k + 1) => x i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  rcases hcoin with ⟨i, j, hij, hxij⟩
  have htime_eq : x i 0 = x j 0 :=
    congrArg (fun z : SpacetimeDim d => z 0) hxij
  exact hij (htime.injective htime_eq)

/-- The lifted block-kernel source, packaged in the zero-diagonal test space
required by the Euclidean Schwinger functional. -/
noncomputable def
    osiiStep4ReducedLiftedCenteredPartialConvolutionKernelZeroDiagonal
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ZeroDiagonalSchwartz d (k + 1) :=
  ⟨osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource
      d k hrho center y y',
    osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource_vanishes
      d k hrho center y y' hcenter⟩

@[simp] theorem
    osiiStep4ReducedLiftedCenteredPartialConvolutionKernelZeroDiagonal_coe
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    (osiiStep4ReducedLiftedCenteredPartialConvolutionKernelZeroDiagonal
      d k hrho center y y' hcenter).1 =
        osiiStep4ReducedLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho center y y' := rfl

end OSReconstruction
