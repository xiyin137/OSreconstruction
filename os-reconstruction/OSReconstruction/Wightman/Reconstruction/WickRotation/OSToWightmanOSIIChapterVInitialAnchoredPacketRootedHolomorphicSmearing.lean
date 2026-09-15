/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedCanonicalFields
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSimultaneousStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap











noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- The operator-valued middle-root integrand for the genuine original-OS
complex semigroup. -/
noncomputable def semigroupBridgeRootOperatorIntegrandOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (t : ℝ) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  D.semigroupBridgeRootWeight i timeScale t •
    osiiOriginalOSHilbertComplex OS (t : ℂ)

/-- Compact positive support makes the original-OS middle-root integrand
Bochner integrable without any arity-growth hypothesis. -/
theorem integrable_semigroupBridgeRootOperatorIntegrandOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    Integrable
      (D.semigroupBridgeRootOperatorIntegrandOfOS i timeScale) := by
  obtain ⟨J, hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  let S : Set ℝ := tsupport (weight : ℝ → ℂ)
  have hS_compact : IsCompact S := by
    simpa [S, weight, semigroupBridgeRootWeight] using!
      (A.rootedBridgeHead R i
        (timeScale + D.commonTailStart i)).compact
  have hS_positive : S ⊆ Set.Ioi 0 :=
    (hsupport timeScale).trans hJ_positive
  have hsemigroup :
      ContinuousOn
        (fun t : ℝ =>
          osiiOriginalOSHilbertComplex OS (t : ℂ))
        S := by
    exact
      (continuousOn_osiiOriginalOSHilbertComplex OS).comp
        Complex.continuous_ofReal.continuousOn
        (by
          intro t ht
          change 0 < ((t : ℂ).re)
          simpa using hS_positive ht)
  have hintegrand_cont :
      ContinuousOn
        (fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ))
        S :=
    (SchwartzMap.continuous weight).continuousOn.smul hsemigroup
  have hintegrableOn :
      IntegrableOn
        (fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ))
        S :=
    hintegrand_cont.integrableOn_compact hS_compact
  have hindicator :
      Integrable
        (S.indicator
          (fun t : ℝ =>
            weight t • osiiOriginalOSHilbertComplex OS (t : ℂ))) := by
    exact
      (MeasureTheory.integrable_indicator_iff
        (μ := MeasureTheory.volume)
        (f := fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ))
        hS_compact.measurableSet).2 hintegrableOn
  have hindicator_eq :
      S.indicator
          (fun t : ℝ =>
            weight t • osiiOriginalOSHilbertComplex OS (t : ℂ)) =
        fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ) := by
    funext t
    by_cases ht : t ∈ S
    · simp [Set.indicator_of_mem ht]
    · have hzero : weight t = 0 :=
        image_eq_zero_of_notMem_tsupport (by simpa [S] using ht)
      simp [Set.indicator_of_notMem ht, hzero]
  rw [hindicator_eq] at hindicator
  simpa [semigroupBridgeRootOperatorIntegrandOfOS, weight] using! hindicator

/-- The synchronized middle root integrated against the original-OS complex
contraction semigroup. -/
noncomputable def semigroupBridgeRootOperatorOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  ∫ t : ℝ, D.semigroupBridgeRootOperatorIntegrandOfOS i timeScale t

/-- Compatibility presentation of the original-OS middle-root operator. -/
noncomputable def semigroupBridgeRootOperator
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
  D.semigroupBridgeRootOperatorOfOS i timeScale

@[simp]
theorem semigroupBridgeRootOperatorOfOS_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (v : OSHilbertSpace OS) :
    D.semigroupBridgeRootOperatorOfOS i timeScale v =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t •
          osiiOriginalOSHilbertComplex OS (t : ℂ) v := by
  rw [semigroupBridgeRootOperatorOfOS,
    ContinuousLinearMap.integral_apply
      (D.integrable_semigroupBridgeRootOperatorIntegrandOfOS
        i timeScale) v]
  rfl

/-- Positivity, unit mass, and the sharp original-OS semigroup contraction
make every synchronized middle-root operator contractive. -/
theorem semigroupBridgeRootOperatorOfOS_norm_le_one
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    ‖D.semigroupBridgeRootOperatorOfOS i timeScale‖ ≤ 1 := by
  obtain ⟨J, hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  have hmajorant :
      Integrable (fun t : ℝ => ‖weight t‖) :=
    (SchwartzMap.integrable weight).norm
  calc
    ‖D.semigroupBridgeRootOperatorOfOS i timeScale‖
        ≤ ∫ t : ℝ,
            ‖D.semigroupBridgeRootOperatorIntegrandOfOS
              i timeScale t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖weight t‖ := by
      exact integral_mono_of_nonneg
        (Eventually.of_forall fun _ => norm_nonneg _)
        hmajorant
        (Eventually.of_forall fun t => by
          by_cases hweight : weight t = 0
          · simp [semigroupBridgeRootOperatorIntegrandOfOS, weight, hweight]
          · have htJ : t ∈ J := by
              apply hsupport timeScale
              exact subset_tsupport _
                (by simpa [Function.mem_support, weight] using hweight)
            change
              ‖weight t • osiiOriginalOSHilbertComplex OS (t : ℂ)‖ ≤
                ‖weight t‖
            rw [norm_smul]
            calc
              ‖weight t‖ *
                    ‖osiiOriginalOSHilbertComplex OS (t : ℂ)‖ ≤
                  ‖weight t‖ * 1 :=
                mul_le_mul_of_nonneg_left
                  (osiiOriginalOSHilbertComplex_norm_le_one OS (t : ℂ)
                    (by simpa using hJ_positive htJ))
                  (norm_nonneg _)
              _ = ‖weight t‖ := mul_one _)
    _ = 1 := by
      simpa [weight] using
        D.semigroupBridgeRootWeight_integral_norm_one i timeScale

/-- Compatibility wrapper for sharp original-OS middle-root contraction. -/
theorem semigroupBridgeRootOperator_norm_le_one
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    ‖D.semigroupBridgeRootOperator _lgc i timeScale‖ ≤ 1 :=
  D.semigroupBridgeRootOperatorOfOS_norm_le_one i timeScale

/-- The original-OS semigroup translates the middle-root operator by the
exact positive bridge time. -/
theorem osiiOriginalOSHilbertComplex_semigroupBridgeRootOperatorOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s : ℝ)
    (hs : 0 < s)
    (v : OSHilbertSpace OS) :
    osiiOriginalOSHilbertComplex OS (s : ℂ)
        (D.semigroupBridgeRootOperatorOfOS i timeScale v) =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t •
          osiiOriginalOSHilbertComplex OS ((s + t : ℝ) : ℂ) v := by
  obtain ⟨J, hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  have hvector :
      Integrable
        (fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ) v) := by
    simpa [semigroupBridgeRootOperatorIntegrandOfOS, weight] using
      (D.integrable_semigroupBridgeRootOperatorIntegrandOfOS
        i timeScale).apply_continuousLinearMap v
  rw [D.semigroupBridgeRootOperatorOfOS_apply]
  calc
    osiiOriginalOSHilbertComplex OS (s : ℂ)
        (∫ t : ℝ,
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ) v)
        =
      ∫ t : ℝ,
        osiiOriginalOSHilbertComplex OS (s : ℂ)
          (weight t • osiiOriginalOSHilbertComplex OS (t : ℂ) v) := by
            exact
              (ContinuousLinearMap.integral_comp_comm
                (osiiOriginalOSHilbertComplex OS (s : ℂ))
                hvector).symm
    _ =
      ∫ t : ℝ,
        weight t •
          osiiOriginalOSHilbertComplex OS ((s + t : ℝ) : ℂ) v := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by
              by_cases hweight : weight t = 0
              · simp [hweight]
              · have htJ : t ∈ J := by
                  apply hsupport timeScale
                  exact subset_tsupport _
                    (by
                      simpa [Function.mem_support, weight] using hweight)
                have ht : 0 < t := hJ_positive htJ
                change
                  osiiOriginalOSHilbertComplex OS (s : ℂ)
                      (weight t •
                        osiiOriginalOSHilbertComplex OS (t : ℂ) v) =
                    weight t •
                      osiiOriginalOSHilbertComplex OS
                        ((s + t : ℝ) : ℂ) v
                calc
                  osiiOriginalOSHilbertComplex OS (s : ℂ)
                      (weight t •
                        osiiOriginalOSHilbertComplex OS (t : ℂ) v)
                      =
                    weight t •
                      osiiOriginalOSHilbertComplex OS (s : ℂ)
                        (osiiOriginalOSHilbertComplex OS (t : ℂ) v) := by
                          exact map_smul _ _ _
                  _ =
                    weight t •
                      ((osiiOriginalOSHilbertComplex OS (s : ℂ)).comp
                        (osiiOriginalOSHilbertComplex OS (t : ℂ))) v := rfl
                  _ =
                    weight t •
                      osiiOriginalOSHilbertComplex OS
                        ((s + t : ℝ) : ℂ) v := by
                          rw [← osiiOriginalOSHilbertComplex_add OS
                            (s : ℂ) (t : ℂ)
                            (by simpa using hs) (by simpa using ht)]
                          norm_cast

/-- The middle-root average commutes with the original-OS complex semigroup. -/
theorem semigroupBridgeRootOperatorOfOS_commute_complex
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) (timeScale : Nat)
    (z : Complex) (hz : 0 < z.re)
    (v : OSHilbertSpace OS) :
    osiiOriginalOSHilbertComplex OS z
        (D.semigroupBridgeRootOperatorOfOS i timeScale v) =
      D.semigroupBridgeRootOperatorOfOS i timeScale
        (osiiOriginalOSHilbertComplex OS z v) := by
  obtain ⟨J, _hJcompact, hJpositive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  have hvector : Integrable (fun t : Real =>
      D.semigroupBridgeRootWeight i timeScale t •
        osiiOriginalOSHilbertComplex OS (t : Complex) v) := by
    simpa [semigroupBridgeRootOperatorIntegrandOfOS] using
      (D.integrable_semigroupBridgeRootOperatorIntegrandOfOS
        i timeScale).apply_continuousLinearMap v
  rw [D.semigroupBridgeRootOperatorOfOS_apply,
    ← ContinuousLinearMap.integral_comp_comm
      (osiiOriginalOSHilbertComplex OS z) hvector,
    D.semigroupBridgeRootOperatorOfOS_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases hweight : D.semigroupBridgeRootWeight i timeScale t = 0
    · simp [hweight]
    · have ht : 0 < t := hJpositive (hsupport timeScale
        (subset_tsupport _ (by simpa [Function.mem_support] using hweight)))
      change osiiOriginalOSHilbertComplex OS z
          (D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS (t : Complex) v) =
        D.semigroupBridgeRootWeight i timeScale t •
          osiiOriginalOSHilbertComplex OS (t : Complex)
            (osiiOriginalOSHilbertComplex OS z v)
      rw [map_smul]
      congr 1
      have hcomm :
          (osiiOriginalOSHilbertComplex OS z).comp
              (osiiOriginalOSHilbertComplex OS (t : Complex)) =
            (osiiOriginalOSHilbertComplex OS (t : Complex)).comp
              (osiiOriginalOSHilbertComplex OS z) := by
        rw [← osiiOriginalOSHilbertComplex_add OS z (t : Complex)
            hz (by simpa using ht),
          ← osiiOriginalOSHilbertComplex_add OS (t : Complex) z
            (by simpa using ht) hz,
          add_comm z (t : Complex)]
      exact congrArg (fun L : OSHilbertSpace OS →L[Complex] OSHilbertSpace OS =>
        L v) hcomm

/-- The genuine middle-root smoothing preserves the prescribed-shift
reflected bound with coefficient one. Its time scale is unrestricted. -/
theorem norm_inner_semigroupBridgeRootOperatorOfOS_shift_le
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) (timeScale : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {z : Complex} (hz : 0 < z.re)
    (x y : OSHilbertSpace OS) :
    ‖@inner Complex (OSHilbertSpace OS) _ x
        (osiiOriginalOSHilbertComplex OS (z + (epsilon : Complex))
          (D.semigroupBridgeRootOperatorOfOS i timeScale y))‖ <=
      Real.sqrt
        (‖@inner Complex (OSHilbertSpace OS) _ x
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)‖ *
          ‖@inner Complex (OSHilbertSpace OS) _ y
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) y)‖) := by
  let B := D.semigroupBridgeRootOperatorOfOS i timeScale
  let T := osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
  have hcontract : ‖T (B y)‖ <= ‖T y‖ := by
    rw [show T (B y) = B (T y) from
      D.semigroupBridgeRootOperatorOfOS_commute_complex i timeScale
        ((epsilon / 2 : Real) : Complex) (by simpa using half_pos hepsilon) y]
    calc
      ‖B (T y)‖ <= ‖B‖ * ‖T y‖ := ContinuousLinearMap.le_opNorm _ _
      _ <= 1 * ‖T y‖ := mul_le_mul_of_nonneg_right
        (D.semigroupBridgeRootOperatorOfOS_norm_le_one i timeScale) (norm_nonneg _)
      _ = ‖T y‖ := one_mul _
  have hdiagonal :
      ‖@inner Complex (OSHilbertSpace OS) _ (B y)
          (osiiOriginalOSHilbertComplex OS (epsilon : Complex) (B y))‖ <=
        ‖@inner Complex (OSHilbertSpace OS) _ y
          (osiiOriginalOSHilbertComplex OS (epsilon : Complex) y)‖ := by
    rw [← osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon,
      ← osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon,
      ← inner_self_re_eq_norm, inner_self_eq_norm_sq,
      ← inner_self_re_eq_norm, inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hcontract 2
  exact (norm_osiiOriginalOSHilbertComplex_inner_shift_le
    OS hepsilon hz x (B y)).trans
      (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hdiagonal (norm_nonneg _)))

/-- Compatibility wrapper for the original-OS shifted middle-root identity. -/
theorem osTimeShiftHilbertComplex_semigroupBridgeRootOperator
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s : ℝ)
    (hs : 0 < s)
    (v : OSHilbertSpace OS) :
    osTimeShiftHilbertComplex OS lgc (s : ℂ)
        (D.semigroupBridgeRootOperator lgc i timeScale v) =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t •
          osTimeShiftHilbertComplex OS lgc ((s + t : ℝ) : ℂ) v :=
  D.osiiOriginalOSHilbertComplex_semigroupBridgeRootOperatorOfOS
    i timeScale s hs v

/-- The shifted original-OS vector-valued middle-root integrand remains
Bochner integrable on every positive real bridge. -/
theorem integrable_semigroupBridgeRootWeight_smul_originalTimeShift_add
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s : ℝ)
    (hs : 0 < s)
    (v : OSHilbertSpace OS) :
    Integrable
      (fun t : ℝ =>
        D.semigroupBridgeRootWeight i timeScale t •
          osiiOriginalOSHilbertComplex OS ((s + t : ℝ) : ℂ) v) := by
  obtain ⟨J, hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  have hbase :
      Integrable
        (fun t : ℝ =>
          weight t • osiiOriginalOSHilbertComplex OS (t : ℂ) v) := by
    simpa [semigroupBridgeRootOperatorIntegrandOfOS, weight] using
      (D.integrable_semigroupBridgeRootOperatorIntegrandOfOS
        i timeScale).apply_continuousLinearMap v
  have hshifted :
      Integrable
        (fun t : ℝ =>
          osiiOriginalOSHilbertComplex OS (s : ℂ)
            (weight t •
              osiiOriginalOSHilbertComplex OS (t : ℂ) v)) :=
    (osiiOriginalOSHilbertComplex OS (s : ℂ)).integrable_comp hbase
  refine hshifted.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases hweight : weight t = 0
  · simp [weight, hweight]
  · have htJ : t ∈ J := by
      apply hsupport timeScale
      exact subset_tsupport _
        (by simpa [Function.mem_support, weight] using hweight)
    have ht : 0 < t := hJ_positive htJ
    change
      osiiOriginalOSHilbertComplex OS (s : ℂ)
          (weight t •
            osiiOriginalOSHilbertComplex OS (t : ℂ) v) =
        weight t •
          osiiOriginalOSHilbertComplex OS ((s + t : ℝ) : ℂ) v
    calc
      osiiOriginalOSHilbertComplex OS (s : ℂ)
          (weight t •
            osiiOriginalOSHilbertComplex OS (t : ℂ) v)
          =
        weight t •
          osiiOriginalOSHilbertComplex OS (s : ℂ)
            (osiiOriginalOSHilbertComplex OS (t : ℂ) v) := by
              exact map_smul _ _ _
      _ =
        weight t •
          ((osiiOriginalOSHilbertComplex OS (s : ℂ)).comp
            (osiiOriginalOSHilbertComplex OS (t : ℂ))) v := rfl
      _ =
        weight t •
          osiiOriginalOSHilbertComplex OS ((s + t : ℝ) : ℂ) v := by
            rw [← osiiOriginalOSHilbertComplex_add OS
              (s : ℂ) (t : ℂ)
              (by simpa using hs) (by simpa using ht)]
            norm_cast

/-- Compatibility wrapper for shifted original-OS root integrability. -/
theorem integrable_semigroupBridgeRootWeight_smul_timeShift_add
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s : ℝ)
    (hs : 0 < s)
    (v : OSHilbertSpace OS) :
    Integrable
      (fun t : ℝ =>
        D.semigroupBridgeRootWeight i timeScale t •
          osTimeShiftHilbertComplex OS lgc ((s + t : ℝ) : ℂ) v) :=
  D.integrable_semigroupBridgeRootWeight_smul_originalTimeShift_add
    i timeScale s hs v

/-- The rooted right Hermite field after applying the synchronized
middle-root operator. -/
noncomputable def rootSmearedRightSpatialHermiteGeneratorFieldOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    D.semigroupBridgeRootOperatorOfOS i timeScale
      (D.rightSpatialHermiteGeneratorField i timeScale mode z)

/-- Compatibility presentation of the original-OS root-smeared right field. -/
noncomputable def rootSmearedRightSpatialHermiteGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    D.semigroupBridgeRootOperator lgc i timeScale
      (D.rightSpatialHermiteGeneratorField i timeScale mode z)

/-- The rooted scalar mode formed from the growth-free semigroup pairing and
the original-OS synchronized middle-root operator. -/
noncomputable def rootSmearedSpatialHermiteGeneratorModeOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  fun w =>
    osiiSemigroupMixedHilbertPairing OS
      (D.leftSpatialHermiteGeneratorField i timeScale mode)
      (D.rootSmearedRightSpatialHermiteGeneratorFieldOfOS
        i timeScale mode)
      (i.splitCoordinatesCLM w)

/-- Compatibility presentation of the original-OS root-smeared scalar mode. -/
noncomputable def rootSmearedSpatialHermiteGeneratorMode
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  generatorSemigroupCandidate OS lgc i
    (D.leftSpatialHermiteGeneratorField i timeScale mode)
    (D.rootSmearedRightSpatialHermiteGeneratorField
      lgc i timeScale mode)

@[simp]
theorem rootSmearedRightSpatialHermiteGeneratorField_eq_ofOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    D.rootSmearedRightSpatialHermiteGeneratorField
        lgc i timeScale mode =
      D.rootSmearedRightSpatialHermiteGeneratorFieldOfOS
        i timeScale mode :=
  rfl

@[simp]
theorem rootSmearedSpatialHermiteGeneratorMode_eq_ofOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ) :
    D.rootSmearedSpatialHermiteGeneratorMode
        lgc i timeScale mode =
      D.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode :=
  rfl

/-- On the positive real edge, the original-OS rooted mode is exactly the
normalized middle-root integral of the unsmeared original-OS mode. -/
theorem rootSmearedSpatialHermiteGeneratorModeOfOS_positiveReal_eq_integral
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex) :
    D.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode
        (osiiPositiveRealTimeEmbed τ) =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) := by
  let u : OSHilbertSpace OS :=
    D.leftSpatialHermiteGeneratorField i timeScale mode
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)))
  let v : OSHilbertSpace OS :=
    D.rightSpatialHermiteGeneratorField i timeScale mode
      (fun b =>
        osiiPositiveRealTimeEmbed τ
          (i.rightGlobalIndex b))
  have hvector :
      Integrable
        (fun t : ℝ =>
          D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS
              (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v) := by
    exact
      D.integrable_semigroupBridgeRootWeight_smul_originalTimeShift_add
        i timeScale (τ i.bridgeGlobalIndex) hbridge v
  rw [rootSmearedSpatialHermiteGeneratorModeOfOS,
    generatorSemigroupPairing_apply]
  change
    @inner ℂ (OSHilbertSpace OS) _ u
        (osiiOriginalOSHilbertComplex OS
          ((τ i.bridgeGlobalIndex : ℝ) : ℂ)
          (D.semigroupBridgeRootOperatorOfOS i timeScale v)) =
      _
  rw [D.osiiOriginalOSHilbertComplex_semigroupBridgeRootOperatorOfOS
    i timeScale (τ i.bridgeGlobalIndex) hbridge v]
  calc
    @inner ℂ (OSHilbertSpace OS) _ u
        (∫ t : ℝ,
          D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS
              (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v)
        =
      ∫ t : ℝ,
          @inner ℂ (OSHilbertSpace OS) _ u
            (D.semigroupBridgeRootWeight i timeScale t •
              osiiOriginalOSHilbertComplex OS
                (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v) := by
            exact (integral_inner hvector u).symm
    _ =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by
              simp only [inner_smul_right]
              congr 1
              rw [spatialHermiteGeneratorModeOfOS,
                generatorSemigroupPairing_apply]
              simp only [osiiPositiveRealTimeEmbed,
                generatorBridgeVariation_left,
                generatorBridgeVariation_bridge,
                generatorBridgeVariation_right,
                u, v]

/-- The genuine original-OS scalar integrand in the positive-root identity
is integrable at every Hermite mode. -/
theorem
    integrable_semigroupBridgeRootWeight_mul_spatialHermiteGeneratorModeOfOS_add
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex) :
    Integrable
      (fun t : ℝ =>
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t)))) := by
  let u : OSHilbertSpace OS :=
    D.leftSpatialHermiteGeneratorField i timeScale mode
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)))
  let v : OSHilbertSpace OS :=
    D.rightSpatialHermiteGeneratorField i timeScale mode
      (fun b =>
        osiiPositiveRealTimeEmbed τ
          (i.rightGlobalIndex b))
  have hvector :=
    D.integrable_semigroupBridgeRootWeight_smul_originalTimeShift_add
      i timeScale (τ i.bridgeGlobalIndex) hbridge v
  have hinner :
      Integrable
        (fun t : ℝ =>
          @inner ℂ (OSHilbertSpace OS) _ u
            (D.semigroupBridgeRootWeight i timeScale t •
              osiiOriginalOSHilbertComplex OS
                (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v)) :=
    (innerSL ℂ u).integrable_comp hvector
  refine hinner.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [inner_smul_right]
  congr 1
  rw [spatialHermiteGeneratorModeOfOS,
    generatorSemigroupPairing_apply]
  simp only [osiiPositiveRealTimeEmbed,
    generatorBridgeVariation_left,
    generatorBridgeVariation_bridge,
    generatorBridgeVariation_right,
    u, v]

/-- Original OS continuity and the sharp middle-root contraction give a
packet-scale-uniform Hermite bound on each compact generator domain. -/
theorem
    exists_rootSmearedSpatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_complex_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain :
      K ⊆ generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (timeScale mode : ℕ) (w : OSIITimeGapSpace k), w ∈ K →
        ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode w‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let KL : Set (Fin (i.n - 1) → ℂ) :=
    (fun w => star (i.leftCoordinatesCLM w)) '' K
  let KR : Set (Fin (i.m - 1) → ℂ) :=
    i.rightCoordinatesCLM '' K
  have hKL_compact : IsCompact KL :=
    hK_compact.image
      (continuous_star.comp i.leftCoordinatesCLM.continuous)
  have hKR_compact : IsCompact KR :=
    hK_compact.image i.rightCoordinatesCLM.continuous
  have hKL_domain : KL ⊆ (D.left i).domain := by
    rintro _ ⟨w, hw, rfl⟩
    have hdom := hK_domain hw
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (D.left i).domain (D.right i).domain at hdom
    exact hdom.2.1
  have hKR_domain : KR ⊆ (D.right i).domain := by
    rintro _ ⟨w, hw, rfl⟩
    have hdom := hK_domain hw
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (D.left i).domain (D.right i).domain at hdom
    exact hdom.2.2
  obtain ⟨CL, hCL, qL, hleftBound⟩ :=
    D.exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
      i KL hKL_compact hKL_domain
  obtain ⟨CR, hCR, qR, hrightBound⟩ :=
    D.exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
      i KR hKR_compact hKR_domain
  refine ⟨CL * CR, by positivity, qL + qR, ?_⟩
  intro timeScale mode w hw
  have hdom := hK_domain hw
  have hbridge : 0 < (w i.bridgeGlobalIndex).re := by
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (D.left i).domain (D.right i).domain at hdom
    exact hdom.1
  let u : OSHilbertSpace OS :=
    D.leftSpatialHermiteGeneratorField i timeScale mode
      (fun a => -star (w (i.leftGlobalIndex a)))
  let v0 : OSHilbertSpace OS :=
    D.rightSpatialHermiteGeneratorField i timeScale mode
      (fun b => w (i.rightGlobalIndex b))
  let v : OSHilbertSpace OS :=
    D.semigroupBridgeRootOperatorOfOS i timeScale v0
  have hu :
      ‖u‖ ≤ CL * (1 + (mode : ℝ)) ^ qL := by
    have hcoord :
        (fun a => -star (w (i.leftGlobalIndex a))) =
          star (i.leftCoordinatesCLM w) := by
      ext a
      simp
    change
      ‖D.leftSpatialHermiteGeneratorField i timeScale mode
          (fun a => -star (w (i.leftGlobalIndex a)))‖ ≤ _
    rw [hcoord]
    exact hleftBound timeScale _ ⟨w, hw, rfl⟩ mode
  have hv0 :
      ‖v0‖ ≤ CR * (1 + (mode : ℝ)) ^ qR := by
    have hcoord :
        (fun b => w (i.rightGlobalIndex b)) =
          i.rightCoordinatesCLM w := by
      ext b
      rfl
    change
      ‖D.rightSpatialHermiteGeneratorField i timeScale mode
          (fun b => w (i.rightGlobalIndex b))‖ ≤ _
    rw [hcoord]
    exact hrightBound timeScale _ ⟨w, hw, rfl⟩ mode
  have hv :
      ‖v‖ ≤ CR * (1 + (mode : ℝ)) ^ qR := by
    calc
      ‖v‖ ≤
          ‖D.semigroupBridgeRootOperatorOfOS i timeScale‖ * ‖v0‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (CR * (1 + (mode : ℝ)) ^ qR) := by
        exact mul_le_mul
          (D.semigroupBridgeRootOperatorOfOS_norm_le_one
            i timeScale)
          hv0 (norm_nonneg _) (by positivity)
      _ = CR * (1 + (mode : ℝ)) ^ qR := one_mul _
  calc
    ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode w‖ ≤ ‖u‖ * ‖v‖ := by
      simpa [rootSmearedSpatialHermiteGeneratorModeOfOS,
        rootSmearedRightSpatialHermiteGeneratorFieldOfOS, u, v, v0] using
          norm_generatorSemigroupPairing_le_norm_mul
            OS i
            (D.leftSpatialHermiteGeneratorField i timeScale mode)
            (D.rootSmearedRightSpatialHermiteGeneratorFieldOfOS
              i timeScale mode)
            w hbridge
    _ ≤
        (CL * (1 + (mode : ℝ)) ^ qL) *
          (CR * (1 + (mode : ℝ)) ^ qR) := by
      exact mul_le_mul hu hv (norm_nonneg _) (by positivity)
    _ =
        (CL * CR) *
          (1 + (mode : ℝ)) ^ (qL + qR) := by
      rw [pow_add]
      ring

/-- A finite rooted Hermite shell built directly from original-OS scalar
modes. -/
noncomputable def rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d (k + 1) :=
  ∑ mode ∈ Finset.range shell,
    (D.rootSmearedSpatialHermiteGeneratorModeOfOS
      i timeScale mode z) •
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode

/-- Compatibility presentation of the original-OS finite rooted shell. -/
noncomputable def rootSmearedSpatialHermiteGeneratorFiniteShell
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d (k + 1) :=
  ∑ mode ∈ Finset.range shell,
    (D.rootSmearedSpatialHermiteGeneratorMode
      lgc i timeScale mode z) •
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode

@[simp]
theorem rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell z F =
      ∑ mode ∈ Finset.range shell,
        D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode z *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F := by
  simp [rootSmearedSpatialHermiteGeneratorFiniteShellOfOS]

@[simp]
theorem rootSmearedSpatialHermiteGeneratorFiniteShell_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootSmearedSpatialHermiteGeneratorFiniteShell
        lgc i timeScale shell z F =
      ∑ mode ∈ Finset.range shell,
        D.rootSmearedSpatialHermiteGeneratorMode
            lgc i timeScale mode z *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F := by
  simp [rootSmearedSpatialHermiteGeneratorFiniteShell]

/-- On the positive real edge, an original-OS rooted shell is the exact
middle-root integral of its translated unsmeared original-OS shell. -/
theorem
    rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_positiveReal_eq_integral
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell
        (osiiPositiveRealTimeEmbed τ) F =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) F := by
  let coefficient : ℕ → ℂ :=
    fun mode =>
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F
  have hint :
      ∀ mode,
        Integrable
          (fun t : ℝ =>
            D.semigroupBridgeRootWeight i timeScale t *
              D.spatialHermiteGeneratorModeOfOS
                i timeScale mode
                (osiiPositiveRealTimeEmbed
                  (generatorBridgeVariation i τ
                    (τ i.bridgeGlobalIndex + t)))) := by
    intro mode
    exact
      D.integrable_semigroupBridgeRootWeight_mul_spatialHermiteGeneratorModeOfOS_add
        i timeScale mode τ hbridge
  rw [D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_apply]
  simp_rw [
    D.rootSmearedSpatialHermiteGeneratorModeOfOS_positiveReal_eq_integral
      i timeScale _ τ hbridge]
  change
    (∑ mode ∈ Finset.range shell,
      (∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t)))) *
        coefficient mode) =
      _
  calc
    (∑ mode ∈ Finset.range shell,
      (∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t)))) *
        coefficient mode)
        =
      ∑ mode ∈ Finset.range shell,
        ∫ t : ℝ,
          (D.semigroupBridgeRootWeight i timeScale t *
            D.spatialHermiteGeneratorModeOfOS
              i timeScale mode
              (osiiPositiveRealTimeEmbed
                (generatorBridgeVariation i τ
                  (τ i.bridgeGlobalIndex + t)))) *
            coefficient mode := by
              apply Finset.sum_congr rfl
              intro mode hmode
              exact
                (integral_mul_const
                  (coefficient mode)
                  (fun t : ℝ =>
                    D.semigroupBridgeRootWeight i timeScale t *
                      D.spatialHermiteGeneratorModeOfOS
                        i timeScale mode
                        (osiiPositiveRealTimeEmbed
                          (generatorBridgeVariation i τ
                            (τ i.bridgeGlobalIndex + t))))).symm
    _ =
      ∫ t : ℝ,
        ∑ mode ∈ Finset.range shell,
          (D.semigroupBridgeRootWeight i timeScale t *
            D.spatialHermiteGeneratorModeOfOS
              i timeScale mode
              (osiiPositiveRealTimeEmbed
                (generatorBridgeVariation i τ
                  (τ i.bridgeGlobalIndex + t)))) *
            coefficient mode := by
              rw [MeasureTheory.integral_finset_sum _
                (fun mode _ => (hint mode).mul_const (coefficient mode))]
    _ =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          D.spatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) F := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun t => by
                change
                  (∑ mode ∈ Finset.range shell,
                    (D.semigroupBridgeRootWeight i timeScale t *
                      D.spatialHermiteGeneratorModeOfOS
                        i timeScale mode
                        (osiiPositiveRealTimeEmbed
                          (generatorBridgeVariation i τ
                            (τ i.bridgeGlobalIndex + t)))) *
                      coefficient mode) =
                    D.semigroupBridgeRootWeight i timeScale t *
                      D.spatialHermiteGeneratorFiniteShellOfOS
                        i timeScale shell
                        (osiiPositiveRealTimeEmbed
                          (generatorBridgeVariation i τ
                            (τ i.bridgeGlobalIndex + t))) F
                rw [D.spatialHermiteGeneratorFiniteShellOfOS_apply,
                  Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro mode hmode
                simp only [coefficient]
                ring

/-- The full root-smeared spatial Hermite series at one packet scale. -/
noncomputable def rootSmearedSpatialHermiteGeneratorSum
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  ∑' mode : ℕ,
    D.rootSmearedSpatialHermiteGeneratorMode
        lgc i timeScale mode z *
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F

/-- The complete rooted Hermite series using genuine original-OS modes. -/
noncomputable def rootSmearedSpatialHermiteGeneratorSumOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  ∑' mode : ℕ,
    D.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode z *
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F

/-- Original-OS rooted Hermite shells converge uniformly on every compact
subset of their common complex generator domain. -/
theorem
    tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain :
      K ⊆ generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) :
    TendstoUniformlyOn
      (fun shell z =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell z F)
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale z F)
      atTop K := by
  obtain ⟨C, hC, q, hmode⟩ :=
    D.exists_rootSmearedSpatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_complex_compact
      i K hK_compact hK_domain
  let coefficient : ℕ → ℂ :=
    fun mode =>
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F
  let majorant : ℕ → ℝ :=
    fun mode =>
      C * (‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q)
  have hcoefficient :
      Summable fun mode =>
        ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q := by
    simpa [coefficient,
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM]
      using
        (summable_norm_coefficient_mul_weight q
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F))
  have hmajorant : Summable majorant := by
    simpa [majorant] using hcoefficient.mul_left C
  have huniform :=
    tendstoUniformlyOn_tsum_nat hmajorant
      (s := K)
      (f := fun mode z =>
        D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode z *
          coefficient mode)
      (fun mode z hz => by
        rw [norm_mul]
        calc
          ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
                i timeScale mode z‖ * ‖coefficient mode‖
              ≤ (C * (1 + (mode : ℝ)) ^ q) *
                  ‖coefficient mode‖ := by
                exact mul_le_mul_of_nonneg_right
                  (hmode timeScale mode z hz)
                  (norm_nonneg _)
          _ = majorant mode := by
                simp only [majorant]
                ring)
  simpa only [
    rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_apply,
    rootSmearedSpatialHermiteGeneratorSumOfOS, coefficient] using huniform

/-- Compatibility wrapper for compact original-OS rooted-shell convergence. -/
theorem
    tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShell_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain :
      K ⊆ generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) :
    TendstoUniformlyOn
      (fun shell z =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShell
          _lgc i timeScale shell z F)
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorSum
          _lgc i timeScale z F)
      atTop K :=
  D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_on_compact
    i timeScale F K hK_compact hK_domain

/-- Original-OS rooted Hermite shells converge with one compact modulus
valid for every shrinking-packet scale. -/
theorem
    tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_uniform_scale_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain :
      K ⊆ generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) :
    TendstoUniformlyOn
      (fun shell (p : ℕ × OSIITimeGapSpace k) =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i p.1 shell p.2 F)
      (fun p =>
        D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i p.1 p.2 F)
      atTop (Set.univ ×ˢ K) := by
  obtain ⟨C, hC, q, hmode⟩ :=
    D.exists_rootSmearedSpatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_complex_compact
      i K hK_compact hK_domain
  let coefficient : ℕ → ℂ :=
    fun mode =>
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F
  let majorant : ℕ → ℝ :=
    fun mode =>
      C * (‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q)
  have hcoefficient :
      Summable fun mode =>
        ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q := by
    simpa [coefficient,
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM]
      using
        (summable_norm_coefficient_mul_weight q
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F))
  have hmajorant : Summable majorant := by
    simpa [majorant] using hcoefficient.mul_left C
  have huniform :=
    tendstoUniformlyOn_tsum_nat hmajorant
      (s := Set.univ ×ˢ K)
      (f := fun mode (p : ℕ × OSIITimeGapSpace k) =>
        D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i p.1 mode p.2 *
          coefficient mode)
      (fun mode p hp => by
        rw [norm_mul]
        calc
          ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
                i p.1 mode p.2‖ * ‖coefficient mode‖
              ≤ (C * (1 + (mode : ℝ)) ^ q) *
                  ‖coefficient mode‖ := by
                exact mul_le_mul_of_nonneg_right
                  (hmode p.1 mode p.2 hp.2)
                  (norm_nonneg _)
          _ = majorant mode := by
                simp only [majorant]
                ring)
  simpa only [
    rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_apply,
    rootSmearedSpatialHermiteGeneratorSumOfOS, coefficient] using huniform

/-- The original-OS middle-root operator preserves holomorphy of the right
Hilbert block. -/
theorem differentiableOn_rootSmearedRightSpatialHermiteGeneratorFieldOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (hright :
      DifferentiableOn ℂ
        (D.rightSpatialHermiteGeneratorField i timeScale mode)
        (D.right i).domain) :
    DifferentiableOn ℂ
      (D.rootSmearedRightSpatialHermiteGeneratorFieldOfOS
        i timeScale mode)
      (D.right i).domain := by
  exact
    (D.semigroupBridgeRootOperatorOfOS i timeScale
      ).differentiable.differentiableOn.comp hright
        (fun _ _ => Set.mem_univ _)

/-- The genuine original-OS rooted scalar mode is holomorphic on the common
generator domain. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorModeOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (hleft_open : IsOpen (D.left i).domain)
    (hright_open : IsOpen (D.right i).domain)
    (hleft :
      DifferentiableOn ℂ
        (D.leftSpatialHermiteGeneratorField i timeScale mode)
        (D.left i).domain)
    (hright :
      DifferentiableOn ℂ
        (D.rightSpatialHermiteGeneratorField i timeScale mode)
        (D.right i).domain) :
    DifferentiableOn ℂ
      (D.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) := by
  exact
    differentiableOn_generatorSemigroupPairing
      OS i hleft_open hright_open hleft
      (D.differentiableOn_rootSmearedRightSpatialHermiteGeneratorFieldOfOS
        i timeScale mode hright)

/-- Every original-OS finite rooted Hermite shell is holomorphic. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (hleft_open : IsOpen (D.left i).domain)
    (hright_open : IsOpen (D.right i).domain)
    (hleft :
      ∀ mode,
        DifferentiableOn ℂ
          (D.leftSpatialHermiteGeneratorField i timeScale mode)
          (D.left i).domain)
    (hright :
      ∀ mode,
        DifferentiableOn ℂ
          (D.rightSpatialHermiteGeneratorField i timeScale mode)
          (D.right i).domain) :
    DifferentiableOn ℂ
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell z F)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) := by
  apply
    (DifferentiableOn.sum
      (u := Finset.range shell)
      (fun mode _ =>
        (D.differentiableOn_rootSmearedSpatialHermiteGeneratorModeOfOS
          i timeScale mode hleft_open hright_open
          (hleft mode) (hright mode)).mul
          (differentiableOn_const
            (c :=
              GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
                (d := d) i mode F)))).congr
  intro z hz
  simp [rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_apply]

/-- Compact-uniform original-OS shell convergence produces a holomorphic
full rooted generator branch. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (hleft_open : IsOpen (D.left i).domain)
    (hright_open : IsOpen (D.right i).domain)
    (hleft :
      ∀ mode,
        DifferentiableOn ℂ
          (D.leftSpatialHermiteGeneratorField i timeScale mode)
          (D.left i).domain)
    (hright :
      ∀ mode,
        DifferentiableOn ℂ
          (D.rightSpatialHermiteGeneratorField i timeScale mode)
          (D.right i).domain) :
    DifferentiableOn ℂ
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale z F)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) := by
  let U :=
    generatorSemigroupDomain i
      (D.left i).domain (D.right i).domain
  have hU_open : IsOpen U :=
    isOpen_generatorSemigroupDomain i hleft_open hright_open
  have hlocal :
      TendstoLocallyUniformlyOn
        (fun shell z =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell z F)
        (fun z =>
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
            i timeScale z F)
        atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU_open]
    intro K hK_domain hK_compact
    exact
      D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_on_compact
        i timeScale F K hK_compact hK_domain
  exact
    hlocal.differentiableOn_finite
      (Filter.Eventually.of_forall fun shell =>
        D.differentiableOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell F hleft_open hright_open hleft hright)
      hU_open

end RootedA0BlockContinuousTranslationData

namespace RootedA0BlockHolomorphicTranslationData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- Canonical rooted fields make each genuine original-OS finite shell
holomorphic on its common generator domain. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    let D := H.toContinuousTranslationData
    DifferentiableOn ℂ
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell z F)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) := by
  let D := H.toContinuousTranslationData
  apply
    D.differentiableOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
      i timeScale shell F
      (H.left i).domain_open
      (H.right i).domain_open
  · intro mode
    simpa [D,
      RootedA0BlockContinuousTranslationData.leftSpatialHermiteGeneratorField]
      using!
        (H.left i).field_holomorphic
          (D.leftCofinalIndex i timeScale)
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)
  · intro mode
    simpa [D,
      RootedA0BlockContinuousTranslationData.rightSpatialHermiteGeneratorField]
      using!
        (H.right i).field_holomorphic
          (D.rightCofinalIndex i timeScale)
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)

/-- The genuine original-OS canonical rooted series is holomorphic on the
common generator domain. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    let D := H.toContinuousTranslationData
    DifferentiableOn ℂ
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale z F)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) := by
  let D := H.toContinuousTranslationData
  apply
    D.differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
      i timeScale F
      (H.left i).domain_open
      (H.right i).domain_open
  · intro mode
    simpa [D,
      RootedA0BlockContinuousTranslationData.leftSpatialHermiteGeneratorField]
      using!
        (H.left i).field_holomorphic
          (D.leftCofinalIndex i timeScale)
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)
  · intro mode
    simpa [D,
      RootedA0BlockContinuousTranslationData.rightSpatialHermiteGeneratorField]
      using!
        (H.right i).field_holomorphic
          (D.rightCofinalIndex i timeScale)
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)

/-- Compatibility wrapper for growth-free canonical rooted-series holomorphy. -/
theorem differentiableOn_rootSmearedSpatialHermiteGeneratorSum
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    let D := H.toContinuousTranslationData
    DifferentiableOn ℂ
      (fun z =>
        D.rootSmearedSpatialHermiteGeneratorSum
          _lgc i timeScale z F)
      (generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain) :=
  H.differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
    i timeScale F

end RootedA0BlockHolomorphicTranslationData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
