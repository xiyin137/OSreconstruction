import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputBPointwise

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Swap the two Euclidean arguments of a two-point configuration. -/
def swapTwoPointAssembly_local (x : NPointDomain d 2) : NPointDomain d 2 :=
  fun i => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) i)

@[simp] theorem swapTwoPointAssembly_local_apply_zero
    (x : NPointDomain d 2) :
    swapTwoPointAssembly_local (d := d) x 0 = x 1 := by
  simp [swapTwoPointAssembly_local]

@[simp] theorem swapTwoPointAssembly_local_apply_one
    (x : NPointDomain d 2) :
    swapTwoPointAssembly_local (d := d) x 1 = x 0 := by
  simp [swapTwoPointAssembly_local]

/-- The one-variable common zero-anchor kernel, reflected on negative time. -/
def commonDifferenceKernel_real_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) :
    SpacetimeDim d → ℂ := fun ξ =>
  if hξ : 0 < ξ 0 then
    k2TimeParametricKernel (d := d) G
      (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)
  else if hξ' : ξ 0 < 0 then
    k2TimeParametricKernel (d := d) G
      (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2)
  else
    0

/-- The honest sectorwise Euclidean two-point kernel attached to the common
diff-block witness. -/
def commonK2TimeParametricKernel_real_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) :
    NPointDomain d 2 → ℂ :=
  twoPointDifferenceKernel (d := d) (commonDifferenceKernel_real_local (d := d) G)

/-- Explicit piecewise form of the common honest real Euclidean kernel. -/
theorem commonK2TimeParametricKernel_real_eq_piecewise_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (x : NPointDomain d 2) :
    commonK2TimeParametricKernel_real_local (d := d) G x =
      if x 0 0 < x 1 0 then
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2)
      else if x 1 0 < x 0 0 then
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), x 0 - x 1] : NPointDomain d 2)
      else
        0 := by
  by_cases hpos : x 0 0 < x 1 0
  · have hneg : ¬ x 1 0 < x 0 0 := by linarith
    have hdiff_pos : 0 < (x 1 - x 0) 0 := by
      simpa using sub_pos.mpr hpos
    have hdiff_not_neg : ¬ (x 1 - x 0) 0 < 0 := by linarith
    simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel,
      commonDifferenceKernel_real_local, hpos, hneg, hdiff_pos, hdiff_not_neg]
  · by_cases hneg : x 1 0 < x 0 0
    · have hdiff_not_pos : ¬ 0 < (x 1 - x 0) 0 := by
        have : (x 1 - x 0) 0 < 0 := by simpa using sub_neg.mpr hneg
        linarith
      have hdiff_neg : (x 1 - x 0) 0 < 0 := by
        simpa using sub_neg.mpr hneg
      have hneg_arg : -(x 1 - x 0) = x 0 - x 1 := by
        ext i
        simp
      simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel,
        commonDifferenceKernel_real_local, hpos, hneg, hdiff_not_pos, hdiff_neg, hneg_arg]
    · have hdiff_not_pos : ¬ 0 < (x 1 - x 0) 0 := by
        intro hdiff_pos
        have : x 0 0 < x 1 0 := by simpa using hdiff_pos
        exact hpos this
      have hdiff_not_neg : ¬ (x 1 - x 0) 0 < 0 := by
        intro hdiff_neg
        have : x 1 0 < x 0 0 := by simpa using hdiff_neg
        exact hneg this
      simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel,
        commonDifferenceKernel_real_local, hpos, hneg, hdiff_not_pos, hdiff_not_neg]

/-- On the positive time-ordering sector, the common honest real Euclidean
kernel is the direct Euclidean section of the common witness. -/
theorem commonK2TimeParametricKernel_real_eq_of_pos_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (x : NPointDomain d 2)
    (hx : x 0 0 < x 1 0) :
    commonK2TimeParametricKernel_real_local (d := d) G x =
      k2TimeParametricKernel (d := d) G x := by
  have hnot : ¬ x 1 0 < x 0 0 := by
    linarith
  calc
    commonK2TimeParametricKernel_real_local (d := d) G x =
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) := by
          simp [commonK2TimeParametricKernel_real_eq_piecewise_local, hx, hnot]
    _ = k2TimeParametricKernel (d := d) G x := by
          symm
          exact euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
            (d := d) G hG_diff x

/-- On the negative time-ordering sector, the common honest real Euclidean
kernel is the swapped Euclidean section of the common witness. -/
theorem commonK2TimeParametricKernel_real_eq_of_neg_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (x : NPointDomain d 2)
    (hx : x 1 0 < x 0 0) :
    commonK2TimeParametricKernel_real_local (d := d) G x =
      k2TimeParametricKernel (d := d) G
        (swapTwoPointAssembly_local (d := d) x) := by
  have hnot : ¬ x 0 0 < x 1 0 := by
    linarith
  calc
    commonK2TimeParametricKernel_real_local (d := d) G x =
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), x 0 - x 1] : NPointDomain d 2) := by
          simp [commonK2TimeParametricKernel_real_eq_piecewise_local, hx, hnot]
    _ = k2TimeParametricKernel (d := d) G
          (swapTwoPointAssembly_local (d := d) x) := by
          symm
          exact euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
            (d := d) G hG_diff (swapTwoPointAssembly_local (d := d) x)

/-- On the reduced zero-origin shell class, the common sectorwise kernel already
depends on the center cutoff only through `∫ χ`. This is the exact kernel-side
companion to `schwingerDifferenceZeroOriginCLM_eq_centerValue`. -/
theorem twoPointZeroDiagonalKernelCLM_commonK2TimeParametricKernel_real_eq_centerValue_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hK_meas : AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (χ : SchwartzSpacetime d)
    (h : zeroOriginAvoidingSubmodule d) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) := by
  have hv :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d)) := by
    exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ
      (h : SchwartzSpacetime d) h.property
  calc
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) =
      ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          (twoPointDifferenceLift χ (h : SchwartzSpacetime d) x) := by
            rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply]
            rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
              (f := twoPointDifferenceLift χ (h : SchwartzSpacetime d)) hv]
    _ =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) := by
            simpa [commonK2TimeParametricKernel_real_local] using
              (integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
                (d := d)
                (commonDifferenceKernel_real_local (d := d) G)
                χ (h : SchwartzSpacetime d))

/-- Pairing a difference-only kernel with the swapped two-point difference shell
reduces to the reflected one-variable pairing `h(ξ) ↦ h(-ξ)`. -/
theorem integral_twoPointDifferenceKernel_mul_swappedDifferenceLift_factorizes_local
    (K : SpacetimeDim d → ℂ)
    (χ h : SchwartzSpacetime d) :
    ∫ x : NPointDomain d 2,
      twoPointDifferenceKernel (d := d) K x *
        twoPointSwappedDifferenceLift (d := d) χ h x =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d, K (-ξ) * h ξ := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin 2 => SpacetimeDim d)
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))
  have he : MeasureTheory.MeasurePreserving e volume volume := by
    simpa [e] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin 2 => SpacetimeDim d)
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
  have heq : (e : NPointDomain d 2 → NPointDomain d 2) = swapTwoPointAssembly_local (d := d) := by
    funext x
    let x' : (a : Fin 2) → (fun _ : Fin 2 => SpacetimeDim d) ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) a) := x
    funext i
    fin_cases i
    · simpa [e, swapTwoPointAssembly_local] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
          (β := fun _ : Fin 2 => SpacetimeDim d)
          (x := x') (i := (1 : Fin 2)))
    · simpa [e, swapTwoPointAssembly_local] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
          (β := fun _ : Fin 2 => SpacetimeDim d)
          (x := x') (i := (0 : Fin 2)))
  calc
    ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel (d := d) K x *
          twoPointSwappedDifferenceLift (d := d) χ h x
      =
      ∫ y : NPointDomain d 2,
        (fun x : NPointDomain d 2 =>
          twoPointDifferenceKernel (d := d) K x *
            twoPointSwappedDifferenceLift (d := d) χ h x) (e y) := by
          symm
          exact he.integral_comp' (f := e)
            (g := fun x : NPointDomain d 2 =>
              twoPointDifferenceKernel (d := d) K x *
                twoPointSwappedDifferenceLift (d := d) χ h x)
    _ =
      ∫ y : NPointDomain d 2,
        twoPointDifferenceKernel (d := d) (fun ξ : SpacetimeDim d => K (-ξ)) y *
          twoPointDifferenceLift χ h y := by
          refine integral_congr_ae ?_
          filter_upwards with y
          simp [heq, swapTwoPointAssembly_local, twoPointDifferenceKernel,
            twoPointDifferenceLift_apply, twoPointSwappedDifferenceLift_apply]
    _ =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d, K (-ξ) * h ξ := by
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) (fun ξ : SpacetimeDim d => K (-ξ)) χ h

/-- Zero-origin-avoiding version of the common zero-anchor integral formula.

Once the common witness has Euclidean reproduction and diff-block dependence,
the reduced zero-origin Schwinger functional is already represented by the
unshifted common zero-anchor section `ξ ↦ k2TimeParametricKernel G ![0, ξ]`. -/
theorem schwingerDifferenceZeroOriginCLM_eq_integral_commonZeroAnchor_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (h : zeroOriginAvoidingSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
      (d := d) OS χ₀) h =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
  have hrepr :
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
    have hrepr0 := hG_euclid (twoPointDifferenceLiftFixedCenterZeroDiagCLM χ₀ h)
    have hv :
        VanishesToInfiniteOrderOnCoincidence
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) :=
      twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
        (h : SchwartzSpacetime d) h.property
    rw [twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical] at hrepr0
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) hv] at hrepr0
    calc
      OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
        ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
              exact hrepr0
      _ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
                (d := d) G hG_diff x]
  calc
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
        (d := d) OS χ₀) h =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
        rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply]
    _ =
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
          twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := hrepr
    _ =
      ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)) x *
          twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
        simp [OSReconstruction.twoPointDifferenceKernel]
    _ =
      (∫ u : SpacetimeDim d, χ₀ u) *
        ∫ ξ : SpacetimeDim d,
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
            ((h : SchwartzSpacetime d) ξ) := by
        exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2))
          χ₀ (h : SchwartzSpacetime d)
    _ =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
        rw [hχ₀, one_mul]

/-- Swapped zero-origin version of the common zero-anchor integral formula.

Using `E3` on the support-away-from-zero shell class, the common zero-origin
Schwinger functional is also represented by the reflected common zero-anchor
section `ξ ↦ k2TimeParametricKernel G ![0, -ξ]`. -/
theorem schwingerDifferenceZeroOriginCLM_eq_integral_reflected_commonZeroAnchor_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (h : zeroOriginAvoidingSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
      (d := d) OS χ₀) h =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
  have hrepr_swapped :
      OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ (h : SchwartzSpacetime d) h.property) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointSwappedDifferenceLift (d := d) χ₀ (h : SchwartzSpacetime d) x := by
    have hrepr0 :=
      hG_euclid (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ (h : SchwartzSpacetime d) h.property)
    calc
      OS.S 2 (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ (h : SchwartzSpacetime d) h.property) =
        ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
            twoPointSwappedDifferenceLift (d := d) χ₀ (h : SchwartzSpacetime d) x := by
              simpa [twoPointSwappedDifferenceLiftZeroDiag]
                using hrepr0
      _ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointSwappedDifferenceLift (d := d) χ₀ (h : SchwartzSpacetime d) x := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
                (d := d) G hG_diff x]
  calc
    (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
        (d := d) OS χ₀) h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
          rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply]
    _ = OS.S 2
          (twoPointSwappedDifferenceLiftZeroDiag (d := d) χ₀ (h : SchwartzSpacetime d) h.property) := by
            exact OS.schwinger_twoPointDifferenceLift_eq_swapped
              (d := d) χ₀ (h : SchwartzSpacetime d) h.property
    _ =
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
          twoPointSwappedDifferenceLift (d := d) χ₀ (h : SchwartzSpacetime d) x := hrepr_swapped
    _ =
      ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)) x *
          twoPointSwappedDifferenceLift (d := d) χ₀ (h : SchwartzSpacetime d) x := by
            simp [OSReconstruction.twoPointDifferenceKernel]
    _ =
      (∫ u : SpacetimeDim d, χ₀ u) *
        ∫ ξ : SpacetimeDim d,
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2) *
            ((h : SchwartzSpacetime d) ξ) := by
        exact integral_twoPointDifferenceKernel_mul_swappedDifferenceLift_factorizes_local
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2))
          χ₀ (h : SchwartzSpacetime d)
    _ =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
        rw [hχ₀, one_mul]

/-- On positive-time compact shells, the canonical sectorwise common kernel
already reproduces the Schwinger two-point functional. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x *
        twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) := by
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x
      =
      ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            by_cases hhx : (h : SchwartzSpacetime d) (x 1 - x 0) = 0
            · simp [twoPointDifferenceLift_apply, hhx]
            · have hmem :
                x 1 - x 0 ∈ tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
                subset_tsupport _ (by simpa [Function.mem_support] using hhx)
              have hpos : 0 < (x 1 - x 0) 0 := h.property.1 hmem
              have hx : x 0 0 < x 1 0 := by simpa using hpos
              rw [commonK2TimeParametricKernel_real_eq_of_pos_local (d := d) G hG_diff x hx]
              rw [k2TimeParametricKernel]
              rw [euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
                (d := d) G hG_diff x]
              simp [twoPointDifferenceKernel]
    _ =
      (∫ u : SpacetimeDim d, χ u) *
        (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h := by
            rw [integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d)
              (fun ξ : SpacetimeDim d =>
                k2TimeParametricKernel (d := d) G
                  (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2))
              χ (h : SchwartzSpacetime d)]
            rw [schwingerDifferencePositiveCLM_eq_integral_commonZeroAnchor_local
              (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff h]
    _ =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) := by
            symm
            rw [OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_eq_centerValue
              (d := d) (OS := OS) χ₀ hχ₀ χ h]
            ring

/-- On compact shells supported in negative time, the same sectorwise common
kernel reproduces the Schwinger two-point functional via the reflected
zero-origin common anchor. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_negativeSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (χ h : SchwartzSpacetime d)
    (hh_neg : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x *
        twoPointDifferenceLift χ h x =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  have hzero_not_mem : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hmem
    have := hh_neg hmem
    simpa using this
  let hmem : zeroOriginAvoidingSubmodule d := ⟨h, hzero_not_mem⟩
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          twoPointDifferenceLift χ h x
      =
      ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2)) x *
          twoPointDifferenceLift χ h x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            by_cases hhx : h (x 1 - x 0) = 0
            · simp [twoPointDifferenceLift_apply, hhx]
            · have hts :
                x 1 - x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) :=
                subset_tsupport _ (by simpa [Function.mem_support] using hhx)
              have hneg : (x 1 - x 0) 0 < 0 := hh_neg hts
              have hx : x 1 0 < x 0 0 := by simpa using hneg
              have hnot : ¬ x 0 0 < x 1 0 := by linarith
              rw [commonK2TimeParametricKernel_real_eq_piecewise_local (d := d) G x]
              simp [twoPointDifferenceKernel, hx, hnot, twoPointDifferenceLift_apply]
    _ =
      (∫ u : SpacetimeDim d, χ u) *
        (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
          (d := d) OS χ₀) hmem := by
            rw [integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d)
              (fun ξ : SpacetimeDim d =>
                k2TimeParametricKernel (d := d) G
                  (![(0 : SpacetimeDim d), -ξ] : NPointDomain d 2))
              χ h]
            rw [schwingerDifferenceZeroOriginCLM_eq_integral_reflected_commonZeroAnchor_local
              (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff hmem]
    _ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
            symm
            rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
              (d := d) (OS := OS) χ₀ hχ₀ χ hmem]
            ring

/-- Final assembly can be reduced to the one-variable zero-origin pairing for
the sectorwise common difference kernel. Once that reduced pairing is known on
the canonical origin-avoiding test space, the full two-point shell agreement
for the honest sectorwise kernel is purely formal. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCLM_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hReduced : ∀ h : zeroOriginAvoidingSubmodule d,
      ∫ ξ : SpacetimeDim d,
        commonDifferenceKernel_real_local (d := d) G ξ * ((h : SchwartzSpacetime d) ξ) =
          (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
            (d := d) OS χ₀) h)
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x *
        twoPointDifferenceLift χ h x =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  simpa [commonK2TimeParametricKernel_real_local] using
    twoPointDifferenceKernel_eq_schwinger_on_differenceShell_of_zeroOriginCLM_pairing
      (d := d) OS χ₀ hχ₀
      (commonDifferenceKernel_real_local (d := d) G)
      hReduced χ h h0

end OSReconstruction
