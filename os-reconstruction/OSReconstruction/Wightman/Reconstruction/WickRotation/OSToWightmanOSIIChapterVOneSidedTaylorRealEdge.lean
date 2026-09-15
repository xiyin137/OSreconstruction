/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertVectorRealEdge














noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d n k : ℕ} [NeZero d]

/-- A globally defined representative of the multivariable positive-time
source-translation germ. Near zero it is the genuine source translation;
outside the local positive-time region it falls back to the original source. -/
noncomputable def localPositiveTimeParameterTranslate
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n)
    (x : Fin k → ℝ) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  if h :
      tsupport
          ((translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) f.1 :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n then
    ⟨translateSchwartzConfiguration
      (sourceParameterDisplacementCLM directions x) f.1, h⟩
  else
    f

/-- The globally defined translation germ fixes every positive-time source at
the zero parameter. -/
@[simp] theorem localPositiveTimeParameterTranslate_zero
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n) :
    localPositiveTimeParameterTranslate f directions 0 = f := by
  have hdisp :
      sourceParameterDisplacementCLM directions 0 =
        (0 : NPointDomain d n) := by
    simp [sourceParameterDisplacementCLM_apply]
  have htranslate :
      translateSchwartzConfiguration (0 : NPointDomain d n) f.1 = f.1 := by
    ext y
    change f.1 (y + 0) = f.1 y
    simp
  simp only [localPositiveTimeParameterTranslate, hdisp]
  rw [dif_pos]
  · apply Subtype.ext
    exact htranslate
  · rw [htranslate]
    exact f.2

/-- With no source parameters, the globally defined translation germ is
literally the original positive-time source. -/
@[simp] theorem localPositiveTimeParameterTranslate_fin_zero
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin 0 → NPointDomain d n)
    (x : Fin 0 → ℝ) :
    localPositiveTimeParameterTranslate f directions x = f := by
  have hdisp :
      sourceParameterDisplacementCLM directions x =
        (0 : NPointDomain d n) := by
    rw [sourceParameterDisplacementCLM_apply]
    simp
  have htranslate :
      translateSchwartzConfiguration (0 : NPointDomain d n) f.1 = f.1 := by
    ext y
    change f.1 (y + 0) = f.1 y
    simp
  simp only [localPositiveTimeParameterTranslate, hdisp]
  rw [dif_pos]
  · apply Subtype.ext
    exact htranslate
  · rw [htranslate]
    exact f.2

/-- A local right-source real edge identifies every Cauchy coefficient with
the fixed-left pairing against the corresponding normalized source
multi-derivative. -/
theorem cauchyCoeffPolydisc_eq_localRightSource_normalized
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi : IsScalarTower ℝ ℂ (Fin (k + 1) → ℂ))
    (T : SchwartzNPoint d (n + n) →L[ℂ] ℂ)
    (g f : SchwartzNPoint d n)
    (directions : Fin (k + 1) → NPointDomain d n)
    {scalar : (Fin (k + 1) → ℂ) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (k + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU :
      SCV.closedPolydisc (0 : Fin (k + 1) → ℂ) (fun _ => R) ⊆ U)
    (hscalar : DifferentiableOn ℂ scalar U)
    (hreal :
      (fun x : Fin (k + 1) → ℝ => scalar (fun i => (x i : ℂ))) =ᶠ[𝓝 0]
        (fun x =>
          T (g.osConjTensorProduct
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) f))))
    (β : Fin (k + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc scalar 0 (fun _ => R) β =
      T (g.osConjTensorProduct
        (normalizedSourceMultiDerivative directions β f)) := by
  let Tg : SchwartzNPoint d n →L[ℂ] ℂ :=
    T.comp (osConjTensorProductRightCLM g)
  have hreal' :
      (fun x : Fin (k + 1) → ℝ => realAffineSlice scalar 0 x) =ᶠ[𝓝 0]
        (fun x =>
          Tg (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) f)) := by
    rw [show
      (fun x : Fin (k + 1) → ℝ => realAffineSlice scalar 0 x) =
        (fun x => scalar (fun i => (x i : ℂ))) by
      funext x
      unfold realAffineSlice
      congr 1
      funext i
      simp]
    simpa [Tg] using hreal
  rw [cauchyCoeffPolydisc_eq_realEdge_iteratedFDeriv
    hTowerC hTowerPi hR hU hRU hscalar hreal' β]
  rw [iteratedFDeriv_apply_translateSchwartzConfiguration_clm_zero]
  rw [show
      LineDeriv.iteratedLineDerivOp
          (fun j =>
            sourceParameterDisplacementCLM directions
              (fun i =>
                if i = SCV.multiIndexEnumeration β j then 1 else 0)) f =
        sourceMultiDerivative directions β f by
      simp only [sourceParameterDisplacementCLM_basis]
      exact
        (sourceMultiDerivative_eq_iteratedLineDerivOp_multiIndexEnumeration
          directions β f).symm]
  rw [← Tg.map_smul]
  change
    Tg (((((∏ i, (β i).factorial : ℕ) : ℂ))⁻¹) •
      sourceMultiDerivative directions β f) =
      Tg (normalizedSourceMultiDerivative directions β f)
  rw [normalizedSourceMultiDerivative, multiFactorial]

/-- Explicit-radius version of the fixed-left mixed-pairing identity.

Unlike `eventually_inner_holomorphicField_eq_localRightSource`, this theorem
evaluates at one specified complex increment. The quantitative Cauchy radius
is what allows a later moving-left argument to substitute the same small real
parameter into both the left and right slots. -/
theorem inner_holomorphicField_eq_localRightScalar_of_norm_lt
    {d n k : ℕ} [NeZero d]
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi : IsScalarTower ℝ ℂ (Fin (k + 1) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (T : SchwartzNPoint d (n + n) →L[ℂ] ℂ)
    (g f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin (k + 1) → NPointDomain d n)
    {scalar : (Fin (k + 1) → ℂ) → ℂ}
    {R Rw : ℝ}
    (hR : 0 < R)
    (hRw : R < Rw)
    {U : Set (Fin (k + 1) → ℂ)}
    (hU : IsOpen U)
    (hRwU :
      SCV.closedPolydisc (0 : Fin (k + 1) → ℂ) (fun _ => Rw) ⊆ U)
    (hscalar : DifferentiableOn ℂ scalar U)
    (hreal :
      (fun x : Fin (k + 1) → ℝ => scalar (fun i => (x i : ℂ))) =ᶠ[𝓝 0]
        (fun x =>
          T (g.1.osConjTensorProduct
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) f.1))))
    (Ψ : (Fin (k + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          f directions).partialSum OS)
        Ψ atTop
        (SCV.Polydisc
          (0 : Fin (k + 1) → ℂ) (fun _ => Rw)))
    (hT :
      ∀ z p,
        T (g.1.osConjTensorProduct
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            f directions).homogeneousSource z p).1) =
        OS.S (n + n)
          (ZeroDiagonalSchwartz.ofClassical
            (g.1.osConjTensorProduct
              ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
                f directions).homogeneousSource z p).1)))
    (z : Fin (k + 1) → ℂ)
    (hz :
      ‖z‖ < R / (2 * ((k : ℝ) + 2)))
    (hzP :
      z ∈ SCV.Polydisc
        (0 : Fin (k + 1) → ℂ) (fun _ => Rw)) :
    @inner ℂ (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS n g)
        (Ψ z) =
      scalar z := by
  let F := PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives f directions
  let Tg : SchwartzNPoint d n →L[ℂ] ℂ :=
    T.comp (osConjTensorProductRightCLM g.1)
  have hcoeff :
      ∀ β : Fin (k + 1) → ℕ,
        SCV.cauchyCoeffPolydisc scalar 0 (fun _ => R) β =
          Tg (normalizedSourceMultiDerivative directions β f.1) := by
    intro β
    exact
      cauchyCoeffPolydisc_eq_localRightSource_normalized
        hTowerC hTowerPi T g.1 f.1 directions hR hU
          (fun w hw => hRwU
            (SCV.closedPolydisc_mono (fun _ => le_of_lt hRw) hw))
          hscalar hreal β
  have hsumC :
      HasSum
        (fun p =>
          SCV.cauchyPowerSeriesPolydisc scalar 0 (fun _ => R) p
            (fun _ => z))
        (scalar z) := by
    simpa using
      SCV.hasSum_cauchyPowerSeriesPolydisc_diag_of_differentiableOn
        hR hRw hU hRwU hscalar hz
  have hterms :
      (fun p =>
        Tg (F.homogeneousSource z p).1) =
      (fun p =>
        SCV.cauchyPowerSeriesPolydisc scalar 0 (fun _ => R) p
          (fun _ => z)) := by
    funext p
    rw [SCV.cauchyPowerSeriesPolydisc_apply_diag]
    simp only [hcoeff]
    change
      Tg (F.homogeneousSource z p).1 =
        (∑ β ∈ Finset.Nat.antidiagonalTuple (k + 1) p,
          (∏ i, z i ^ β i) •
            Tg (normalizedSourceMultiDerivative directions β f.1))
    simp [F, PositiveTimeSourceTaylorFamily.homogeneousSource,
      PositiveTimeSourceTaylorFamily.monomial,
      PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives,
      map_sum, map_smul]
  have hsumT :
      HasSum
        (fun p => Tg (F.homogeneousSource z p).1)
        (scalar z) := by
    rw [hterms]
    exact hsumC
  have hΨz :
      Tendsto (fun N => F.partialSum OS N z) atTop (𝓝 (Ψ z)) :=
    hΨ.tendsto_at hzP
  have hinner :
      Tendsto
        (fun N =>
          @inner ℂ (OSHilbertSpace OS) _
            (osiiPositiveTimeSingleVectorCLM OS n g)
            (F.partialSum OS N z))
        atTop
        (𝓝 (@inner ℂ (OSHilbertSpace OS) _
          (osiiPositiveTimeSingleVectorCLM OS n g) (Ψ z))) := by
    have hc :
        Tendsto
          (innerSL ℂ (osiiPositiveTimeSingleVectorCLM OS n g))
          (𝓝 (Ψ z))
          (𝓝 ((innerSL ℂ
            (osiiPositiveTimeSingleVectorCLM OS n g)) (Ψ z))) :=
      (innerSL ℂ
        (osiiPositiveTimeSingleVectorCLM OS n g)).continuous.continuousAt
    exact hc.comp hΨz
  have hpartial :
      (fun N =>
        @inner ℂ (OSHilbertSpace OS) _
          (osiiPositiveTimeSingleVectorCLM OS n g)
          (F.partialSum OS N z)) =
      (fun N =>
        ∑ p ∈ Finset.range N,
          Tg (F.homogeneousSource z p).1) := by
    funext N
    rw [F.partialSum_eq_source]
    simp only [map_sum, inner_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
    exact (hT z p).symm
  rw [hpartial] at hinner
  exact (tendsto_nhds_unique hsumT.tendsto_sum_nat hinner).symm

/-- Equal norm and the expected self pairing identify two OS Hilbert
vectors. This is the final Hilbert-space step in the positive-time real-edge
argument. -/
theorem eq_of_norm_sq_eq_and_inner_eq_inner_self
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (v w : OSHilbertSpace OS)
    (hnorm : ‖w‖ ^ 2 = ‖v‖ ^ 2)
    (hinner :
      @inner ℂ (OSHilbertSpace OS) _ v w =
        @inner ℂ (OSHilbertSpace OS) _ v v) :
    w = v := by
  have hcross :
      RCLike.re (@inner ℂ (OSHilbertSpace OS) _ w v) =
        ‖v‖ ^ 2 := by
    calc
      RCLike.re (@inner ℂ (OSHilbertSpace OS) _ w v) =
          RCLike.re (@inner ℂ (OSHilbertSpace OS) _ v w) := by
        simpa using inner_re_symm (𝕜 := ℂ) w v
      _ = RCLike.re (@inner ℂ (OSHilbertSpace OS) _ v v) := by
        rw [hinner]
      _ = ‖v‖ ^ 2 := inner_self_eq_norm_sq v
  have hzero : ‖w - v‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℂ (OSHilbertSpace OS) _ _ _, hnorm, hcross]
    ring
  have hnorm_zero : ‖w - v‖ = 0 :=
    sq_eq_zero_iff.mp hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

end OSIIChapterV
end OSReconstruction
