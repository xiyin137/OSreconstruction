import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialEndpointSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds

/-!
# OS II Chapter VI: Radial positive-source seminorm bounds

The Chapter-VI selected source is the reduced-test lift of a centered radial
endpoint bump and a centered reduced partial kernel.  This file first proves
a finite-seminorm product estimate for `BHW.reducedTestLift` by factoring the
prepend operation through the existing Schwartz tensor product.  It then
combines the endpoint and partial-kernel scale estimates.
-/

noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

set_option maxHeartbeats 4000000

/-- Every finite family of target seminorms of `reducedTestLift` is bounded
by a product of finite seminorm families in its head and tail inputs. -/
theorem exists_reducedTestLift_finsetSeminorm_product_bound
    (d k : Nat) (t : Finset (Nat × Nat)) :
    ∃ sHead sTail : Finset (Nat × Nat), ∃ C : Real, 0 <= C ∧
      ∀ (chi : SchwartzMap (SpacetimeDim d) Complex)
          (phi : SchwartzNPoint d k),
        t.sup (schwartzSeminormFamily Real
            (NPointDomain d (k + 1)) Complex)
            (BHW.reducedTestLift k d chi phi) <=
          C * sHead.sup
              (schwartzSeminormFamily Real (SpacetimeDim d) Complex) chi *
            sTail.sup
              (schwartzSeminormFamily Real (NPointDomain d k) Complex) phi := by
  let toOnePt :
      SchwartzMap (SpacetimeDim d) Complex →L[Complex]
        SchwartzMap (Fin 1 -> SpacetimeDim d) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (ContinuousLinearEquiv.funUnique (Fin 1) Real (SpacetimeDim d))
  let castCLE :
      (Fin (k + 1) -> SpacetimeDim d) ≃L[Real]
        (Fin (1 + k) -> SpacetimeDim d) :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin (1 + k) => SpacetimeDim d)
      (finCongr (Nat.add_comm k 1))
  let reindex :
      SchwartzMap (Fin (1 + k) -> SpacetimeDim d) Complex →L[Complex]
        SchwartzMap (Fin (k + 1) -> SpacetimeDim d) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex castCLE
  let U :
      SchwartzMap (Fin (1 + k) -> SpacetimeDim d) Complex →L[Complex]
        SchwartzNPoint d (k + 1) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (BHW.realDiffCoordCLE (k + 1) d)).comp reindex
  obtain ⟨u, CU, hCU, hU⟩ :=
    exists_schwartzCLM_finsetRealSeminormBound_between U t
  let pMax : Nat := u.sup fun j => j.1
  let lMax : Nat := u.sup fun j => j.2
  let sRect : Finset (Nat × Nat) :=
    (Finset.range (pMax + 1)).product (Finset.range (lMax + 1))
  obtain ⟨sHead, CHead, hCHead, hHead⟩ :=
    exists_schwartzCLM_finsetRealSeminormBound_between toOnePt sRect
  let B : Nat × Nat -> Real := fun j =>
    2 ^ j.1 *
      ∑ i ∈ Finset.range (j.2 + 1),
        (j.2.choose i : Real) * (1 + 1)
  let K : Real := ∑ j ∈ u, B j
  have hB : ∀ j, 0 <= B j := by
    intro j
    dsimp [B]
    positivity
  have hK : 0 <= K := by
    dsimp [K]
    exact Finset.sum_nonneg fun j _ => hB j
  let C : Real := CU * K * CHead
  have hC : 0 <= C := mul_nonneg (mul_nonneg hCU hK) hCHead
  refine ⟨sHead, sRect, C, hC, ?_⟩
  intro chi phi
  let one := toOnePt chi
  let product := one.tensorProduct phi
  let H : Real :=
    sRect.sup
      (schwartzSeminormFamily Real (Fin 1 -> SpacetimeDim d) Complex) one
  let T : Real :=
    sRect.sup
      (schwartzSeminormFamily Real (NPointDomain d k) Complex) phi
  have hH : 0 <= H := apply_nonneg _ _
  have hT : 0 <= T := apply_nonneg _ _
  have hproduct :
      u.sup (schwartzSeminormFamily Real
          (Fin (1 + k) -> SpacetimeDim d) Complex) product <=
        K * H * T := by
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (mul_nonneg hK hH) hT)
    intro j hj
    have hjp : j.1 <= pMax :=
      Finset.le_sup (f := fun z => z.1) hj
    have hjl : j.2 <= lMax :=
      Finset.le_sup (f := fun z => z.2) hj
    have hseminorm :=
      SchwartzMap.tensorProduct_seminorm_le j.1 j.2 one phi
    have hsum :
        ∑ i ∈ Finset.range (j.2 + 1), (j.2.choose i : Real) *
            (SchwartzMap.seminorm Real j.1 i one *
                SchwartzMap.seminorm Real 0 (j.2 - i) phi +
              SchwartzMap.seminorm Real 0 i one *
                SchwartzMap.seminorm Real j.1 (j.2 - i) phi) <=
          ∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (H * T + H * T) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_le : i <= j.2 := by
        simpa [Finset.mem_range] using hi
      have hi_lMax : i <= lMax := hi_le.trans hjl
      have hsub_lMax : j.2 - i <= lMax :=
        (Nat.sub_le j.2 i).trans hjl
      have hHeadPi : (j.1, i) ∈ sRect := by
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjp),
            Finset.mem_range.mpr (Nat.lt_succ_of_le hi_lMax)⟩
      have hHeadZero : (0, i) ∈ sRect := by
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.zero_lt_succ pMax),
            Finset.mem_range.mpr (Nat.lt_succ_of_le hi_lMax)⟩
      have hTailZero : (0, j.2 - i) ∈ sRect := by
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.zero_lt_succ pMax),
            Finset.mem_range.mpr (Nat.lt_succ_of_le hsub_lMax)⟩
      have hTailP : (j.1, j.2 - i) ∈ sRect := by
        exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjp),
            Finset.mem_range.mpr (Nat.lt_succ_of_le hsub_lMax)⟩
      have hHeadPi_le :
          SchwartzMap.seminorm Real j.1 i one <= H := by
        simpa only [H] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily Real
              (Fin 1 -> SpacetimeDim d) Complex) hHeadPi)
      have hHeadZero_le :
          SchwartzMap.seminorm Real 0 i one <= H := by
        simpa only [H] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily Real
              (Fin 1 -> SpacetimeDim d) Complex) hHeadZero)
      have hTailZero_le :
          SchwartzMap.seminorm Real 0 (j.2 - i) phi <= T := by
        simpa only [T] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily Real
              (NPointDomain d k) Complex) hTailZero)
      have hTailP_le :
          SchwartzMap.seminorm Real j.1 (j.2 - i) phi <= T := by
        simpa only [T] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily Real
              (NPointDomain d k) Complex) hTailP)
      have hchoose : (0 : Real) <= (j.2.choose i : Real) := by positivity
      apply mul_le_mul_of_nonneg_left _ hchoose
      exact add_le_add
        (mul_le_mul hHeadPi_le hTailZero_le
          (apply_nonneg _ _) hH)
        (mul_le_mul hHeadZero_le hTailP_le
          (apply_nonneg _ _) hH)
    have hsum_eq :
        (∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (H * T + H * T)) =
          (∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (1 + 1)) * H * T := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hBjK : B j <= K := by
      dsimp [K]
      exact Finset.single_le_sum
        (f := B) (fun z _ => hB z) hj
    calc
      SchwartzMap.seminorm Real j.1 j.2 product <=
          2 ^ j.1 *
            ∑ i ∈ Finset.range (j.2 + 1), (j.2.choose i : Real) *
              (SchwartzMap.seminorm Real j.1 i one *
                  SchwartzMap.seminorm Real 0 (j.2 - i) phi +
                SchwartzMap.seminorm Real 0 i one *
                  SchwartzMap.seminorm Real j.1 (j.2 - i) phi) := by
        simpa [product] using hseminorm
      _ <= 2 ^ j.1 *
          ∑ i ∈ Finset.range (j.2 + 1),
            (j.2.choose i : Real) * (H * T + H * T) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = B j * H * T := by
        rw [hsum_eq]
        dsimp [B]
        ring
      _ <= K * H * T := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBjK hH) hT
  have hprepend :
      reindex product = chi.prependField phi := by
    ext x
    simp only [product, one, reindex, toOnePt, castCLE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.tensorProduct_apply, SchwartzMap.prependField_apply,
      ContinuousLinearEquiv.coe_funUnique, Function.eval, Function.comp,
      splitFirst, ContinuousLinearEquiv.piCongrLeft]
    congr 1
    congr 1
    ext j
    simp [splitLast, Homeomorph.piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft']
  have hlift : U product = BHW.reducedTestLift k d chi phi := by
    change
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (BHW.realDiffCoordCLE (k + 1) d)) (reindex product) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (BHW.realDiffCoordCLE (k + 1) d)) (chi.prependField phi)
    rw [hprepend]
  have htransport := hU product
  have hheadTransport := hHead chi
  let H0 : Real :=
    sHead.sup
      (schwartzSeminormFamily Real (SpacetimeDim d) Complex) chi
  have hH0 : 0 <= H0 := apply_nonneg _ _
  calc
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
        (BHW.reducedTestLift k d chi phi) =
      t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex) (U product) := by
          rw [hlift]
    _ <= CU *
        u.sup (schwartzSeminormFamily Real
          (Fin (1 + k) -> SpacetimeDim d) Complex) product := htransport
    _ <= CU * (K * H * T) :=
      mul_le_mul_of_nonneg_left hproduct hCU
    _ <= CU * (K * (CHead * H0) * T) := by
      apply mul_le_mul_of_nonneg_left _ hCU
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by simpa [H, one, H0] using hheadTransport) hK) hT
    _ = C * H0 * T := by
      dsimp [C]
      ring

set_option maxHeartbeats 800000 in
/-- The full radial endpoint source has simultaneous inverse-radius bounds
for every finite family of Schwartz seminorms.  The two center-growth factors
are kept separate for later selected-block geometry. -/
theorem
    exists_osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_finsetSeminorm_scale_bound
    (d k : Nat) [NeZero d] (t : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M NEndpoint NTail : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (endpointCenter endpointImag : SpacetimeDim d),
          endpointImag ∈ Metric.closedBall 0 (rho / 8) ->
            ∀ (center : Fin (k * (d + 1)) -> Real),
              ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho,
                t.sup (schwartzSeminormFamily Real
                    (NPointDomain d (k + 1)) Complex)
                    (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
                      d k hrho endpointCenter endpointImag center p.1 p.2) <=
                  C * (16 / rho) ^ M *
                    (1 + norm endpointCenter) ^ NEndpoint *
                    (1 + norm center) ^ NTail := by
  obtain ⟨sHead, sTail, CLift, hCLift, hlift⟩ :=
    exists_reducedTestLift_finsetSeminorm_product_bound d k t
  obtain ⟨CHead, MHead, NEndpoint, hCHead, hhead⟩ :=
    exists_osiiStep4CenteredComplexBlockRadialGRealSchwartz_finsetSeminorm_scale_bound
      (d + 1) sHead
  obtain ⟨CTail, MTail, NTail, hCTail, htail⟩ :=
    exists_osiiStep4CenteredPartialConvolutionKernelFullSource_finsetSeminorm_scale_bound
      d k sTail
  let C : Real := CLift * CHead * CTail
  let M : Nat := MHead + MTail
  have hC : 0 <= C := mul_nonneg (mul_nonneg hCLift hCHead) hCTail
  refine ⟨C, M, NEndpoint, NTail, hC, ?_⟩
  intro rho hrho hrho_le endpointCenter endpointImag hEndpointImag
    center p hp
  let chi : SchwartzMap (SpacetimeDim d) Complex :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter endpointImag
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center p.1 p.2
  have hliftBound := hlift chi phi
  have hheadBound :=
    hhead hrho hrho_le endpointCenter endpointImag hEndpointImag
  have htailBound := htail hrho hrho_le center p hp
  calc
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho endpointCenter endpointImag center p.1 p.2) <=
      CLift * sHead.sup
          (schwartzSeminormFamily Real (SpacetimeDim d) Complex) chi *
        sTail.sup
          (schwartzSeminormFamily Real (NPointDomain d k) Complex) phi := by
      simpa [chi, phi,
        osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource]
        using hliftBound
    _ <= CLift *
          (CHead * (16 / rho) ^ MHead *
            (1 + norm endpointCenter) ^ NEndpoint) *
        (CTail * (16 / rho) ^ MTail *
          (1 + norm center) ^ NTail) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (by simpa [chi] using hheadBound) hCLift)
        (by simpa [phi] using htailBound)
        (apply_nonneg _ _)
        (mul_nonneg hCLift (by positivity))
    _ = C * (16 / rho) ^ M *
          (1 + norm endpointCenter) ^ NEndpoint *
          (1 + norm center) ^ NTail := by
      dsimp [C, M]
      rw [pow_add]
      ring

end OSReconstruction
