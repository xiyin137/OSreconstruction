/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockNorm
















noncomputable section

open Matrix MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- Add a spacetime vector to one selected flattened difference block. -/
def osiiStep4AddSelectedRealBlock
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real)
    (v : Fin q -> Real) :
    Fin ((n + 1 + m) * q) -> Real :=
  fun a =>
    let p := finProdFinEquiv.symm a
    x a + if p.1 = osiiStep4SelectedBlockIndex n m then v p.2 else 0

@[simp] theorem addSelectedRealBlock_selected
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real)
    (v : Fin q -> Real) (mu : Fin q) :
    osiiStep4AddSelectedRealBlock n m q x v
        (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu)) =
      x (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu)) + v mu := by
  simp [osiiStep4AddSelectedRealBlock]

@[simp] theorem addSelectedRealBlock_other
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real)
    (v : Fin q -> Real) (i : Fin (n + 1 + m)) (mu : Fin q)
    (hi : i ≠ osiiStep4SelectedBlockIndex n m) :
    osiiStep4AddSelectedRealBlock n m q x v
        (finProdFinEquiv (i, mu)) =
      x (finProdFinEquiv (i, mu)) := by
  simp [osiiStep4AddSelectedRealBlock, hi]

theorem beforeBlockIndex_ne_selectedBlockIndex
    (n m : Nat) (i : Fin n) :
    osiiStep4BeforeBlockIndex n m i ≠
      osiiStep4SelectedBlockIndex n m := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

theorem afterBlockIndex_ne_selectedBlockIndex
    (n m : Nat) (i : Fin m) :
    osiiStep4AfterBlockIndex n m i ≠
      osiiStep4SelectedBlockIndex n m := by
  intro h
  have hval := congrArg Fin.val h
  simp [osiiStep4AfterBlockIndex] at hval
  omega

theorem addSelectedRealBlock_time_lower
    (d n m : Nat) {rho : Real}
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (v : SpacetimeDim d)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hv : 0 <= v 0) :
    forall i : Fin (n + 1 + m),
      rho / 2 <= osiiStep4AddSelectedRealBlock n m (d + 1) center v
        (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
  intro i
  by_cases hi : i = osiiStep4SelectedBlockIndex n m
  · subst i
    rw [addSelectedRealBlock_selected]
    linarith [hcenter (osiiStep4SelectedBlockIndex n m)]
  · rw [addSelectedRealBlock_other _ _ _ _ _ _ _ hi]
    exact hcenter i

theorem selectedBlockKernelFactor_addSelected_center
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m))
    (v : SpacetimeDim d)
    (i : Fin (n + 1 + m))
    (hi : i ≠ osiiStep4SelectedBlockIndex n m) :
    osiiStep4SelectedBlockKernelFactor d n m rho center y y'
        (Function.update xi (osiiStep4SelectedBlockIndex n m)
          (xi (osiiStep4SelectedBlockIndex n m) - v)) i =
      osiiStep4SelectedBlockKernelFactor d n m rho
        (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
        y y' xi i := by
  simp [osiiStep4SelectedBlockKernelFactor, Function.update, hi,
    osiiStep4AddSelectedRealBlock]

theorem selectedBlockPartialConvolutionIntegrand_addSelected_center
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m))
    (v x' : SpacetimeDim d) :
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
        (osiiStep4ComplexOfRealImag
          ((Function.update xi (osiiStep4SelectedBlockIndex n m)
              (xi (osiiStep4SelectedBlockIndex n m) - v))
                (osiiStep4SelectedBlockIndex n m) -
            fun mu => center (finProdFinEquiv
              (osiiStep4SelectedBlockIndex n m, mu)))
          (fun mu => y (finProdFinEquiv
            (osiiStep4SelectedBlockIndex n m, mu))))
        (fun mu => y' (finProdFinEquiv
          (osiiStep4SelectedBlockIndex n m, mu))) x' =
      osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (xi (osiiStep4SelectedBlockIndex n m) -
            fun mu => osiiStep4AddSelectedRealBlock n m (d + 1)
              center v (finProdFinEquiv
                (osiiStep4SelectedBlockIndex n m, mu)))
          (fun mu => y (finProdFinEquiv
            (osiiStep4SelectedBlockIndex n m, mu))))
        (fun mu => y' (finProdFinEquiv
          (osiiStep4SelectedBlockIndex n m, mu))) x' := by
  have hreal :
      (Function.update xi (osiiStep4SelectedBlockIndex n m)
          (xi (osiiStep4SelectedBlockIndex n m) - v))
            (osiiStep4SelectedBlockIndex n m) -
          (fun mu => center (finProdFinEquiv
            (osiiStep4SelectedBlockIndex n m, mu))) =
        xi (osiiStep4SelectedBlockIndex n m) -
          (fun mu => osiiStep4AddSelectedRealBlock n m (d + 1)
            center v (finProdFinEquiv
              (osiiStep4SelectedBlockIndex n m, mu))) := by
    ext mu
    simp
    ring
  rw [hreal]

theorem selectedBlockConvolutionDensity_addSelected_center
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m))
    (v x' : SpacetimeDim d) :
    osiiStep4SelectedBlockConvolutionDensity d n m rho center y y'
        (Function.update xi (osiiStep4SelectedBlockIndex n m)
          (xi (osiiStep4SelectedBlockIndex n m) - v)) x' =
      osiiStep4SelectedBlockConvolutionDensity d n m rho
        (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
        y y' xi x' := by
  unfold osiiStep4SelectedBlockConvolutionDensity
  have hbefore :
      (Finset.univ.prod fun i : Fin n =>
        osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (Function.update xi (osiiStep4SelectedBlockIndex n m)
            (xi (osiiStep4SelectedBlockIndex n m) - v))
          (osiiStep4BeforeBlockIndex n m i)) =
        Finset.univ.prod fun i : Fin n =>
          osiiStep4SelectedBlockKernelFactor d n m rho
            (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
            y y' xi (osiiStep4BeforeBlockIndex n m i) := by
    apply Finset.prod_congr rfl
    intro i _hi
    exact selectedBlockKernelFactor_addSelected_center
      d n m rho center y y' xi v _
        (beforeBlockIndex_ne_selectedBlockIndex n m i)
  have hafter :
      (Finset.univ.prod fun j : Fin m =>
        osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (Function.update xi (osiiStep4SelectedBlockIndex n m)
            (xi (osiiStep4SelectedBlockIndex n m) - v))
          (osiiStep4AfterBlockIndex n m j)) =
        Finset.univ.prod fun j : Fin m =>
          osiiStep4SelectedBlockKernelFactor d n m rho
            (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
            y y' xi (osiiStep4AfterBlockIndex n m j) := by
    apply Finset.prod_congr rfl
    intro j _hj
    exact selectedBlockKernelFactor_addSelected_center
      d n m rho center y y' xi v _
        (afterBlockIndex_ne_selectedBlockIndex n m j)
  rw [hbefore, hafter]
  rw [selectedBlockPartialConvolutionIntegrand_addSelected_center
    d n m rho center y y' xi v x']

/-- Translate only the chronological points on the right of the selected
gap. -/
def osiiStep4ShiftChronologicalRight
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (v : SpacetimeDim d) :
    NPointDomain d ((n + 1) + (m + 1)) :=
  fun i => if i.val < n + 1 then x i else x i - v

theorem shiftChronologicalRight_leftConfig
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (v : SpacetimeDim d) :
    osiiStep4SelectedBlockChronologicalLeftConfig d n m
        (osiiStep4ShiftChronologicalRight d n m x v) =
      osiiStep4SelectedBlockChronologicalLeftConfig d n m x := by
  ext i mu
  rw [osiiStep4SelectedBlockChronologicalLeftConfig_apply,
    osiiStep4SelectedBlockChronologicalLeftConfig_apply]
  simp [osiiStep4ShiftChronologicalRight]

theorem shiftChronologicalRight_rightConfig
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (v : SpacetimeDim d) :
    osiiStep4SelectedBlockChronologicalRightConfig d n m
        (osiiStep4ShiftChronologicalRight d n m x v) =
      fun j => osiiStep4SelectedBlockChronologicalRightConfig d n m x j - v := by
  ext j mu
  rw [osiiStep4SelectedBlockChronologicalRightConfig_apply,
    osiiStep4SelectedBlockChronologicalRightConfig_apply]
  simp only [osiiStep4ShiftChronologicalRight, Fin.natAdd]
  split_ifs with h
  · omega
  · rfl

theorem reducedDiffMap_shiftChronologicalRight
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (v : SpacetimeDim d) :
    BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d
        (osiiStep4ShiftChronologicalRight d n m x v) =
      Function.update
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
        (osiiStep4SelectedBlockIndex n m)
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
          (osiiStep4SelectedBlockIndex n m) - v) := by
  ext i mu
  by_cases hi : i = osiiStep4SelectedBlockIndex n m
  · subst i
    simp only [Function.update_self, Pi.sub_apply,
      BHW.reducedDiffMapReal_apply]
    simp [osiiStep4ShiftChronologicalRight,
      osiiStep4SelectedBlockIndex]
    ring
  · rw [Function.update_of_ne hi]
    simp only [BHW.reducedDiffMapReal_apply]
    by_cases hbefore : i.val < n
    · have hle : i.val ≤ n := by omega
      simp [osiiStep4ShiftChronologicalRight, hbefore, hle]
    · have hafter : n < i.val := by
        have hine : i.val ≠ n := by
          intro hval
          apply hi
          apply Fin.ext
          simpa [osiiStep4SelectedBlockIndex] using hval
        omega
      have hnlt : ¬ i.val < n := by omega
      have hnle : ¬ i.val ≤ n := by omega
      simp [osiiStep4ShiftChronologicalRight, hnlt, hnle]

theorem chronologicalOSSource_translate_right_apply
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    (v : SpacetimeDim d)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalOSSource d n m f
        (translateSchwartzNPoint (d := d) v g) x =
      osiiStep4SelectedBlockChronologicalOSSource d n m f g
        (osiiStep4ShiftChronologicalRight d n m x v) := by
  rw [osiiStep4SelectedBlockChronologicalOSSource_apply,
    osiiStep4SelectedBlockChronologicalOSSource_apply,
    translateSchwartzNPoint_apply,
    shiftChronologicalRight_leftConfig,
    shiftChronologicalRight_rightConfig]

theorem selectedBlockChronologicalSource_translate_right_diffVarReduction
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (v : SpacetimeDim d) :
    diffVarReduction d (n + 1 + m)
        (osiiStep4SelectedBlockChronologicalOSSource d n m
          (osiiStep4SelectedBlockLeftPositiveTimeSource
            d n m hrho center y y' hcenter).1
          (translateSchwartzNPoint (d := d) v
            (osiiStep4SelectedBlockRightPositiveTimeSource
              d n m hrho center y y' hcenter).1)) =
      osiiStep4CenteredPartialConvolutionKernelFullSource
        d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y' := by
  apply DFunLike.ext
  intro xi
  let shift : SpacetimeDim d :=
    diffVarSection d (n + 1 + m) xi
        (Fin.natAdd (n + 1) (0 : Fin (m + 1))) -
      osiiStep4SelectedBlockRightEndpointCenter d n m center
  change
    (∫ a : SpacetimeDim d,
      osiiStep4SelectedBlockChronologicalOSSource d n m
          (osiiStep4SelectedBlockLeftPositiveTimeSource
            d n m hrho center y y' hcenter).1
          (translateSchwartzNPoint (d := d) v
            (osiiStep4SelectedBlockRightPositiveTimeSource
              d n m hrho center y y' hcenter).1)
          (fun k mu =>
            a mu + diffVarSection d (n + 1 + m) xi k mu)) =
      osiiStep4CenteredPartialConvolutionKernelFullSource
        d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y' xi
  have hred : forall a : SpacetimeDim d,
      BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d
          (osiiStep4ShiftChronologicalRight d n m
            (fun k mu =>
              a mu + diffVarSection d (n + 1 + m) xi k mu) v) =
        Function.update xi (osiiStep4SelectedBlockIndex n m)
          (xi (osiiStep4SelectedBlockIndex n m) - v) := by
    intro a
    rw [reducedDiffMap_shiftChronologicalRight]
    have hbase :
        BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d
            (fun k mu =>
              a mu + diffVarSection d (n + 1 + m) xi k mu) = xi := by
      simpa only [Nat.add_assoc] using
        OSIIChapterV.reducedDiffMapReal_diffVarSection a xi
    rw [hbase]
    rfl
  have hright : forall a : SpacetimeDim d,
      osiiStep4SelectedBlockChronologicalRightConfig d n m
          (osiiStep4ShiftChronologicalRight d n m
            (fun k mu =>
              a mu + diffVarSection d (n + 1 + m) xi k mu) v) 0 -
        osiiStep4SelectedBlockRightEndpointCenter d n m center =
      a + shift - v := by
    intro a
    rw [shiftChronologicalRight_rightConfig]
    have horig :
      osiiStep4SelectedBlockChronologicalRightConfig d n m
          (fun k mu =>
            a mu + diffVarSection d (n + 1 + m) xi k mu) 0 -
        osiiStep4SelectedBlockRightEndpointCenter d n m center =
          a + shift := by
      simpa [shift] using
        osiiStep4SelectedBlockChronologicalRightConfig_fiber_zero_sub
          d n m center a xi
    calc
      (osiiStep4SelectedBlockChronologicalRightConfig d n m
            (fun k mu =>
              a mu + diffVarSection d (n + 1 + m) xi k mu) 0 - v) -
          osiiStep4SelectedBlockRightEndpointCenter d n m center =
        (osiiStep4SelectedBlockChronologicalRightConfig d n m
            (fun k mu =>
              a mu + diffVarSection d (n + 1 + m) xi k mu) 0 -
          osiiStep4SelectedBlockRightEndpointCenter d n m center) - v := by
            abel
      _ = a + shift - v := by rw [horig]
  simp_rw [chronologicalOSSource_translate_right_apply]
  change
    (∫ a : SpacetimeDim d,
      osiiStep4SelectedBlockChronologicalPositiveSource
        d n m hrho center y y' hcenter
        (osiiStep4ShiftChronologicalRight d n m
          (fun k mu =>
            a mu + diffVarSection d (n + 1 + m) xi k mu) v)) = _
  simp_rw [osiiStep4SelectedBlockChronologicalPositiveSource_apply_eq_density,
    hred, hright,
    selectedBlockConvolutionDensity_addSelected_center]
  calc
    (∫ a : SpacetimeDim d,
        (osiiStep4SelectedBlockConvolutionDensity d n m rho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
          y y' xi (a + shift - v) : Complex)) =
      ∫ a : SpacetimeDim d,
        (osiiStep4SelectedBlockConvolutionDensity d n m rho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
          y y' xi a : Complex) := by
            have hadd : forall a : SpacetimeDim d,
                a + shift - v = a + (shift - v) := by
              intro a
              abel
            simp_rw [hadd]
            exact MeasureTheory.integral_add_right_eq_self
              (μ := (MeasureTheory.volume :
                MeasureTheory.Measure (SpacetimeDim d)))
              (fun a : SpacetimeDim d =>
                (osiiStep4SelectedBlockConvolutionDensity d n m rho
                  (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
                  y y' xi a : Complex)) (shift - v)
    _ = ((∫ a : SpacetimeDim d,
        osiiStep4SelectedBlockConvolutionDensity d n m rho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
          y y' xi a : Real) : Complex) := by
            rw [integral_complex_ofReal]
    _ = osiiStep4CenteredPartialConvolutionKernelFullSource
        d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y' xi := by
      exact
        (osiiStep4CenteredPartialConvolutionKernelFullSource_apply_eq_integral_selectedDensity
          d n m hrho
            (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
            y y' xi).symm

theorem chronologicalOSSource_compactPositiveSupport
    (d n m : Nat) [NeZero d]
    (fL : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (fR : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hfLcompact : HasCompactSupport
      (fL.1 : NPointDomain d (n + 1) -> Complex))
    (hfRcompact : HasCompactSupport
      (fR.1 : NPointDomain d (m + 1) -> Complex)) :
    OSIIChapterV.HasCompactStrictPositiveReducedTimeSupport
      (osiiStep4SelectedBlockChronologicalOSSource d n m fL.1 fR.1) := by
  have hchronCompact : HasCompactSupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m fL.1 fR.1 :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex) :=
    osiiStep4SelectedBlockChronologicalOSSource_hasCompactSupport
      d n m fL.1 fR.1 hfLcompact hfRcompact
  apply osiiStep4_hasCompactStrictPositiveReducedTimeSupport_of_gap_pos
    d (n + 1 + m)
      (osiiStep4SelectedBlockChronologicalOSSource d n m fL.1 fR.1)
      hchronCompact
  intro x hx i
  have hxL : osiiStep4SelectedBlockChronologicalLeftConfig d n m x ∈
      tsupport (fL.1 : NPointDomain d (n + 1) -> Complex) :=
    osiiStep4SelectedBlockChronologicalLeftConfig_mem_tsupport
      d n m fL.1 fR.1 hx
  have hxR : osiiStep4SelectedBlockChronologicalRightConfig d n m x ∈
      tsupport (fR.1 : NPointDomain d (m + 1) -> Complex) :=
    osiiStep4SelectedBlockChronologicalRightConfig_mem_tsupport
      d n m fL.1 fR.1 hx
  have hL := fL.2 hxL
  have hR := fR.2 hxR
  by_cases hleft : i.val < n
  · let i0 : Fin n := ⟨i.val, hleft⟩
    let j : Fin n := Fin.rev i0
    have hindex : osiiStep4ReversedBeforeBlockIndex n m j = i := by
      rw [osiiStep4ReversedBeforeBlockIndex_eq_before_rev]
      apply Fin.ext
      simp [j, i0]
    have hgapL : 0 <
        BHW.reducedDiffMapReal (n + 1) d
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x) j 0 := by
      rw [BHW.reducedDiffMapReal_apply]
      exact sub_pos.mpr ((hL j.castSucc).2 j.succ (by simp))
    rw [osiiStep4SelectedBlockChronologicalLeft_reducedDiff] at hgapL
    simpa [hindex] using hgapL
  · by_cases hbridge : i.val = n
    · have hi : i = osiiStep4SelectedBlockIndex n m := by
        apply Fin.ext
        simpa [osiiStep4SelectedBlockIndex] using hbridge
      rw [hi]
      have hsum := congrFun
        (osiiStep4SelectedBlockChronologicalEndpoint_sum d n m x) 0
      simp only [Pi.add_apply] at hsum
      rw [osiiStep4EuclideanParityMatrix_mulVec_zero] at hsum
      have hpos : 0 <
          BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
            (osiiStep4SelectedBlockIndex n m) 0 := by
        rw [← hsum]
        exact add_pos (hL 0).1 (hR 0).1
      simpa only [Nat.add_assoc] using hpos
    · have hright : n + 1 <= i.val := by omega
      let j : Fin m := ⟨i.val - (n + 1), by omega⟩
      have hindex : osiiStep4AfterBlockIndex n m j = i := by
        apply Fin.ext
        simp [j, osiiStep4AfterBlockIndex]
        omega
      have hgapR : 0 <
          BHW.reducedDiffMapReal (m + 1) d
            (osiiStep4SelectedBlockChronologicalRightConfig d n m x) j 0 := by
        rw [BHW.reducedDiffMapReal_apply]
        exact sub_pos.mpr ((hR j.castSucc).2 j.succ (by simp))
      rw [osiiStep4SelectedBlockChronologicalRight_reducedDiff] at hgapR
      simpa [hindex] using hgapR

theorem hasCompactSupport_translateSchwartzNPoint
    (d k : Nat)
    (f : SchwartzNPoint d k)
    (hf : HasCompactSupport (f : NPointDomain d k -> Complex))
    (v : SpacetimeDim d) :
    HasCompactSupport
      (translateSchwartzNPoint (d := d) v f : NPointDomain d k -> Complex) := by
  change HasCompactSupport
    (fun x : NPointDomain d k => f (fun i => x i - v))
  simpa [Pi.add_apply, sub_eq_add_neg] using
    hf.comp_homeomorph
      (Homeomorph.addRight (fun _ : Fin k => -v))

theorem selectedBlockTranslatedRight_schwinger_eq_positiveLifted
    (d n m : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (v : SpacetimeDim d) (hv : 0 <= v 0) :
    OS.S ((n + 1) + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((osiiStep4SelectedBlockLeftPositiveTimeSource
              d n m hrho center y y' hcenter).1.osConjTensorProduct
            (translateSchwartzNPoint (d := d) v
              (osiiStep4SelectedBlockRightPositiveTimeSource
                d n m hrho center y y' hcenter).1))) =
      OS.S ((n + 1) + (m + 1))
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
          d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y'
          (addSelectedRealBlock_time_lower
            d n m center v hcenter hv)) := by
  let fL : euclideanPositiveTimeSubmodule (d := d) (n + 1) :=
    osiiStep4SelectedBlockLeftPositiveTimeSource
      d n m hrho center y y' hcenter
  let fR0 : euclideanPositiveTimeSubmodule (d := d) (m + 1) :=
    osiiStep4SelectedBlockRightPositiveTimeSource
      d n m hrho center y y' hcenter
  let fR : euclideanPositiveTimeSubmodule (d := d) (m + 1) :=
    ⟨translateSchwartzNPoint (d := d) v fR0.1,
      osiiEuclideanTranslation_preserves_orderedPositive
        v hv fR0.1 fR0.2⟩
  let raw : SchwartzNPoint d ((n + 1) + (m + 1)) :=
    fL.1.osConjTensorProduct fR.1
  let chron : SchwartzNPoint d ((n + 1) + (m + 1)) :=
    osiiStep4SelectedBlockChronologicalOSSource d n m fL.1 fR.1
  let hcenterV := addSelectedRealBlock_time_lower
    d n m center v hcenter hv
  let target : SchwartzNPoint d ((n + 1) + (m + 1)) :=
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
      d (n + 1 + m) hrho
        (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y'
  have hraw : VanishesToInfiniteOrderOnCoincidence raw := by
    exact
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        fL.1 fR.1 fL.2 fR.2
  have hchron : VanishesToInfiniteOrderOnCoincidence chron :=
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      hraw (osiiStep4SelectedBlockLeftReversePerm n m)
  let rawZ : ZeroDiagonalSchwartz d ((n + 1) + (m + 1)) :=
    ⟨raw, hraw⟩
  let chronZ : ZeroDiagonalSchwartz d ((n + 1) + (m + 1)) :=
    ⟨chron, hchron⟩
  let targetZ : ZeroDiagonalSchwartz d ((n + 1) + (m + 1)) :=
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
      d (n + 1 + m) hrho
        (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y' hcenterV
  have hE3 :
      OS.S ((n + 1) + (m + 1)) rawZ =
        OS.S ((n + 1) + (m + 1)) chronZ := by
    refine OS.E3_symmetric
      (n := (n + 1) + (m + 1))
      (σ := osiiStep4SelectedBlockLeftReversePerm n m)
      rawZ chronZ ?_
    intro x
    rfl
  have hfLcompact : HasCompactSupport
      (fL.1 : NPointDomain d (n + 1) -> Complex) := by
    simpa [fL] using
      selectedBlockLeftPositiveTimeSource_hasCompactSupport
        d n m hrho center y y' hcenter
  have hfR0compact : HasCompactSupport
      (fR0.1 : NPointDomain d (m + 1) -> Complex) := by
    simpa [fR0] using
      selectedBlockRightPositiveTimeSource_hasCompactSupport
        d n m hrho center y y' hcenter
  have hfRcompact : HasCompactSupport
      (fR.1 : NPointDomain d (m + 1) -> Complex) := by
    simpa [fR] using
      hasCompactSupport_translateSchwartzNPoint
        d (m + 1) fR0.1 hfR0compact v
  have hchronSupport :
      OSIIChapterV.HasCompactStrictPositiveReducedTimeSupport chron := by
    simpa [chron] using
      chronologicalOSSource_compactPositiveSupport
        d n m fL fR hfLcompact hfRcompact
  have htargetSupport :
      OSIIChapterV.HasCompactStrictPositiveReducedTimeSupport target := by
    exact
      osiiStep4CenteredPartialConvolutionKernel_reducedTestLift_compactPositiveSupport
        d (n + 1 + m)
        (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
        hrho (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
          y y' hcenterV
  have hred :
      diffVarReduction d (n + 1 + m) chron =
        diffVarReduction d (n + 1 + m) target := by
    let phi : SchwartzNPoint d (n + 1 + m) :=
      osiiStep4CenteredPartialConvolutionKernelFullSource
        d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y'
    have hchronRed :=
      selectedBlockChronologicalSource_translate_right_diffVarReduction
        d n m hrho center y y' hcenter v
    have htargetRed := OSIIChapterV.diffVarReduction_reducedTestLift
      (osiiStep4PositiveTimeBasepointCutoff d) phi
    simpa [chron, target, phi, fL, fR, fR0] using
      hchronRed.trans htargetRed.symm
  have hReducedSchwinger :
      OS.S ((n + 1) + (m + 1)) chronZ =
        OS.S ((n + 1) + (m + 1)) targetZ := by
    have h := OSIIChapterV.schwinger_eq_of_diffVarReduction_eq
      OS chron target hchronSupport htargetSupport hchron targetZ.2 hred
    simpa only [Nat.add_assoc] using h
  calc
    OS.S ((n + 1) + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((osiiStep4SelectedBlockLeftPositiveTimeSource
              d n m hrho center y y' hcenter).1.osConjTensorProduct
            (translateSchwartzNPoint (d := d) v
              (osiiStep4SelectedBlockRightPositiveTimeSource
                d n m hrho center y y' hcenter).1))) =
      OS.S ((n + 1) + (m + 1)) rawZ := by
        rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes raw hraw]
    _ = OS.S ((n + 1) + (m + 1)) chronZ := hE3
    _ = OS.S ((n + 1) + (m + 1)) targetZ := hReducedSchwinger
    _ = OS.S ((n + 1) + (m + 1))
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
          d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center v) y y'
          (addSelectedRealBlock_time_lower
            d n m center v hcenter hv)) := rfl

theorem axisPairFullTranslation_time_nonneg
    (d : Nat) [NeZero d]
    (T : Real) (hT : 0 <= T)
    (c : osiiAxisPairIndex d -> Real)
    (hc : forall a, 0 <= c a) :
    0 <= (∑ a : osiiAxisPairIndex d,
      c a • osiiAxisPairDir (d := d) T a) 0 := by
  simp [osiiAxisPairDir]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hc a) hT

theorem selectedBlockAxisPairPacket_realEdge_eq_positiveLiftedSchwinger
    (d n m : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (P : OSIIAxisPairCompactCommonSourcePackage
      (osiiStep4SelectedBlockLeftPositiveTimeSource
        d n m hrho center y y' hcenter).1
      (osiiStep4SelectedBlockRightPositiveTimeSource
        d n m hrho center y y' hcenter).1)
    (x : osiiAxisPairIndex d -> Real) :
    (P.toSemigroupPacketFamily OS lgc).realEdge x =
      OS.S ((n + 1) + (m + 1))
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
          d (n + 1 + m) hrho
          (osiiStep4AddSelectedRealBlock n m (d + 1) center
            (∑ a : osiiAxisPairIndex d,
              osiiAxisPairPositiveCoefficients x a •
                osiiAxisPairDir (d := d) P.T a))
          y y'
          (addSelectedRealBlock_time_lower
            d n m center
              (∑ a : osiiAxisPairIndex d,
                osiiAxisPairPositiveCoefficients x a •
                  osiiAxisPairDir (d := d) P.T a)
              hcenter
              (axisPairFullTranslation_time_nonneg
                d P.T (le_trans (by norm_num) (le_of_lt P.hT))
                (osiiAxisPairPositiveCoefficients x)
                (fun a => le_of_lt
                  (osiiAxisPairPositiveCoefficients_pos x a))))) := by
  let v : SpacetimeDim d :=
    ∑ a : osiiAxisPairIndex d,
      osiiAxisPairPositiveCoefficients x a •
        osiiAxisPairDir (d := d) P.T a
  have hv : 0 <= v 0 := by
    exact axisPairFullTranslation_time_nonneg
      d P.T (le_trans (by norm_num) (le_of_lt P.hT))
      (osiiAxisPairPositiveCoefficients x)
      (fun a => le_of_lt (osiiAxisPairPositiveCoefficients_pos x a))
  have hcenterV := addSelectedRealBlock_time_lower
    d n m center v hcenter hv
  calc
    (P.toSemigroupPacketFamily OS lgc).realEdge x =
      OS.S ((n + 1) + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((osiiStep4SelectedBlockLeftPositiveTimeSource
              d n m hrho center y y' hcenter).1.osConjTensorProduct
            (translateSchwartzNPoint (d := d) v
              (osiiStep4SelectedBlockRightPositiveTimeSource
                d n m hrho center y y' hcenter).1))) := by
      simpa [v] using P.toSemigroupPacketFamily_realEdge OS lgc x
    _ = OS.S ((n + 1) + (m + 1))
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
          d (n + 1 + m) hrho
            (osiiStep4AddSelectedRealBlock n m (d + 1) center v)
            y y' hcenterV) := by
      simpa [hcenterV] using
        selectedBlockTranslatedRight_schwinger_eq_positiveLifted
          d n m OS hrho center y y' hcenter v hv

end OSReconstruction
