/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFrequencyReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanACRProducerPackage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSupport
import OSReconstruction.Wightman.SpectralEquivalence












noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d m : Nat} [NeZero d]

namespace OSIIReducedForwardTubeBoundaryData

omit [NeZero d] in
/-- The real full-difference inverse is the standard basepoint plus
successive-difference section. -/
theorem realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
    (x₀ : SpacetimeDim d) (ξ : NPointDomain d m) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ) =
      fun k μ => x₀ μ + diffVarSection d m ξ k μ := by
  exact OSReconstruction.realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
    m x₀ ξ

/-- Fiber reduction is exactly the inner integral obtained after the
Jacobian-one full-difference coordinate change. -/
theorem integral_reducedDiffKernel_eq_diffVarReduction
    (f : SchwartzNPoint d (m + 1))
    (G : NPointDomain d m → Complex)
    (hGf : Integrable
      (fun x : NPointDomain d (m + 1) =>
        G (BHW.reducedDiffMapReal (m + 1) d x) * f x) volume) :
    (∫ x : NPointDomain d (m + 1),
        G (BHW.reducedDiffMapReal (m + 1) d x) * f x) =
      ∫ ξ : NPointDomain d m,
        G ξ * (diffVarReduction d m f) ξ := by
  let H : NPointDomain d (m + 1) → Complex := fun x =>
    G (BHW.reducedDiffMapReal (m + 1) d x) * f x
  rw [BHW.integral_realDiffCoord_change_variables (d := d) m H hGf]
  have hred :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        BHW.reducedDiffMapReal (m + 1) d
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) = ξ := by
    intro ξ x₀
    exact BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
      d m x₀ ξ
  simp_rw [H, hred]
  congr 1
  funext ξ
  rw [show
      (fun x₀ : SpacetimeDim d =>
        G ξ * f ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ))) =
        fun x₀ : SpacetimeDim d =>
          G ξ • f ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) by
      funext x₀
      simp [smul_eq_mul]]
  rw [integral_smul]
  simp only [smul_eq_mul]
  congr 1
  simp only [diffVarReduction]
  apply integral_congr_ae
  filter_upwards with x₀
  rw [realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection]

/-- An absolute forward-cone direction has product-forward successive
differences. -/
theorem reducedDiffMapReal_mem_productForwardConeReal_of_mem_forwardConeAbs
    (η : NPointDomain d (m + 1))
    (hη : η ∈ ForwardConeAbs d (m + 1)) :
    BHW.reducedDiffMapReal (m + 1) d η ∈
      BHW.ProductForwardConeReal d m := by
  intro j
  have hj := hη j.succ
  have hj' : InOpenForwardCone d
      (fun μ => η j.succ μ - η j.castSucc μ) := by
    convert hj using 1
    funext μ
    congr 2
  have heq : BHW.reducedDiffMapReal (m + 1) d η j =
      (fun μ => η j.succ μ - η j.castSucc μ) := by
    ext μ
    rw [BHW.reducedDiffMapReal_apply]
    rfl
  apply (inOpenForwardCone_iff _).2
  rw [heq]
  exact hj'

omit [NeZero d] in
/-- Taking successive differences commutes with a real forward-tube
approach ray. -/
theorem reducedDiffMap_complex_approach
    (x η : NPointDomain d (m + 1)) (ε : Real) :
    BHW.reducedDiffMap (m + 1) d
        (fun j μ =>
          (x j μ : Complex) + (ε : Complex) * (η j μ : Complex) * I) =
      fun j μ =>
        (BHW.reducedDiffMapReal (m + 1) d x j μ : Complex) +
          (ε : Complex) *
            (BHW.reducedDiffMapReal (m + 1) d η j μ : Complex) *
              I := by
  ext j μ
  rw [BHW.reducedDiffMap_eq_successive_differences]
  rw [BHW.reducedDiffMapReal_apply, BHW.reducedDiffMapReal_apply]
  push_cast
  ring

/-- A reduced fixed-height forward-tube slice remains integrable after
pullback to absolute coordinates. -/
theorem pullback_boundarySlice_integrable
    {W : SchwartzNPoint d m →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (η : NPointDomain d (m + 1))
    (hη : η ∈ ForwardConeAbs d (m + 1))
    (ε : Real) (hε : 0 < ε)
    (φ : SchwartzNPoint d (m + 1)) :
    Integrable
      (fun x : NPointDomain d (m + 1) =>
        H.kernel (fun j μ =>
          (BHW.reducedDiffMapReal (m + 1) d x j μ : Complex) +
            (ε : Complex) *
              (BHW.reducedDiffMapReal (m + 1) d η j μ : Complex) *
                I) *
          φ x) := by
  let L := BHW.reducedDiffMapRealCLM (m + 1) d
  let ηred : NPointDomain d m := L η
  let y : NPointDomain d m := ε • ηred
  have hηred : ηred ∈ BHW.ProductForwardConeReal d m := by
    simpa [ηred, L, BHW.reducedDiffMapRealCLM] using
      reducedDiffMapReal_mem_productForwardConeReal_of_mem_forwardConeAbs η hη
  have hy : y ∈ BHW.ProductForwardConeReal d m := by
    intro j
    simpa [y, Pi.smul_apply] using
      BHW.inOpenForwardCone_smul_pos (d := d) (hηred j) hε
  obtain ⟨C, N, hC, hbound⟩ :=
    H.compactSubsetGrowth {y} isCompact_singleton
      (by simpa [Set.singleton_subset_iff] using hy)
  let g : NPointDomain d (m + 1) → Complex := fun x =>
    H.kernel (fun j μ =>
      (L x j μ : Complex) + (y j μ : Complex) * I)
  have hslice_mem :
      ∀ x : NPointDomain d (m + 1),
        (fun j μ =>
          (L x j μ : Complex) + (y j μ : Complex) * I) ∈
          TubeDomainSetPi (BHW.ProductForwardConeReal d m) := by
    intro x
    simpa [TubeDomainSetPi] using hy
  have hg_cont : Continuous g := by
    apply ContinuousOn.comp_continuous H.holomorphic.continuousOn
    · fun_prop
    · exact hslice_mem
  have hg :
      ∀ x : NPointDomain d (m + 1),
        ‖g x‖ ≤
          (C * (1 + ‖L‖) ^ N) * (1 + ‖x‖) ^ N := by
    intro x
    have hx := hbound (L x) y (Set.mem_singleton y)
    have hLx : ‖L x‖ ≤ ‖L‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm L x
    have hbase :
        1 + ‖L x‖ ≤ (1 + ‖L‖) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg L, norm_nonneg x]
    have hpow :
        (1 + ‖L x‖) ^ N ≤
          ((1 + ‖L‖) * (1 + ‖x‖)) ^ N :=
      pow_le_pow_left₀ (by positivity) hbase N
    calc
      ‖g x‖ ≤ C * (1 + ‖L x‖) ^ N := by
        simpa [g] using hx
      _ ≤ C * ((1 + ‖L‖) * (1 + ‖x‖)) ^ N := by
        gcongr
      _ = (C * (1 + ‖L‖) ^ N) * (1 + ‖x‖) ^ N := by
        rw [mul_pow]
        ring
  have hC' : 0 < C * (1 + ‖L‖) ^ N :=
    mul_pos hC (pow_pos (by positivity) _)
  have hint :
      Integrable (fun x : NPointDomain d (m + 1) => g x * φ x) :=
    polynomial_growth_mul_schwartz_integrable
      g hg_cont.aestronglyMeasurable
      (C * (1 + ‖L‖) ^ N) N hC' hg φ
  simpa [g, y, ηred, L, BHW.reducedDiffMapRealCLM,
    Pi.smul_apply, Complex.ofReal_mul, mul_assoc] using hint

/-- At every positive height, an absolute pairing of a reduced kernel is the
reduced pairing against the canonical fiber reduction of the test. -/
theorem absolute_boundarySlice_integral_eq
    {W : SchwartzNPoint d m →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (η : NPointDomain d (m + 1))
    (hη : η ∈ ForwardConeAbs d (m + 1))
    (ε : Real) (hε : 0 < ε)
    (φ : SchwartzNPoint d (m + 1)) :
    (∫ x : NPointDomain d (m + 1),
        H.kernel (fun j μ =>
          (BHW.reducedDiffMapReal (m + 1) d x j μ : Complex) +
            (ε : Complex) *
              (BHW.reducedDiffMapReal (m + 1) d η j μ : Complex) *
                I) *
          φ x) =
      ∫ ξ : NPointDomain d m,
        H.kernel (fun j μ =>
          (ξ j μ : Complex) +
            (ε : Complex) *
              (BHW.reducedDiffMapReal (m + 1) d η j μ : Complex) *
                I) *
          (diffVarReduction d m φ) ξ := by
  let G : NPointDomain d m → Complex := fun ξ =>
    H.kernel (fun j μ =>
      (ξ j μ : Complex) +
        (ε : Complex) *
          (BHW.reducedDiffMapReal (m + 1) d η j μ : Complex) *
            I)
  have hGφ :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          G (BHW.reducedDiffMapReal (m + 1) d x) * φ x) := by
    simpa [G] using
      H.pullback_boundarySlice_integrable η hη ε hε φ
  simpa [G] using
    integral_reducedDiffKernel_eq_diffVarReduction φ G hGφ

end OSIIReducedForwardTubeBoundaryData

end OSReconstruction
