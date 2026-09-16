/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.SCV.GaussianRegularization
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli











noncomputable section

open Complex Filter MeasureTheory Topology
open scoped Classical BigOperators RealInnerProductSpace UniformConvergence

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The one-variable branch obtained by varying one axis-pair logarithmic
coordinate while keeping the inactive real base fixed. -/
def OSIIAxisPairFlatCrossData.coordinateLine
    (X : OSIIAxisPairFlatCrossData d)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d)
    (w : ℂ) : ℂ :=
  X.family.flatTubeBranch
    (Function.update (osiiAxisPairLogRealEmbed x) a w)

omit [NeZero d] in
/-- Every real axis-pair log point lies in the full MZ carrier. -/
theorem osiiAxisPairLogRealEmbed_mem
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairLogRealEmbed x ∈ osiiAxisPairLogDomain (d := d) := by
  simp [osiiAxisPairLogDomain, osiiAxisPairLogRealEmbed]
  positivity

omit [NeZero d] in
/-- The full axis-pair logarithmic MZ carrier is open. -/
theorem isOpen_osiiAxisPairLogDomain :
    IsOpen (osiiAxisPairLogDomain (d := d)) := by
  have hcont :
      Continuous fun r : osiiAxisPairIndex d → ℂ =>
        ∑ a : osiiAxisPairIndex d, |(r a).im| := by
    exact continuous_finset_sum _ fun a _ =>
      (Complex.continuous_im.comp (continuous_apply a)).abs
  simpa [osiiAxisPairLogDomain] using isOpen_lt hcont continuous_const

omit [NeZero d] in
/-- The axis-pair logarithmic MZ carrier is convex. -/
theorem convex_osiiAxisPairLogDomain :
    Convex ℝ (osiiAxisPairLogDomain (d := d)) := by
  intro z hz w hw a b ha hb hab
  simp only [osiiAxisPairLogDomain, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint : ∀ q : osiiAxisPairIndex d,
      |((a • z + b • w) q).im| ≤
        a * |(z q).im| + b * |(w q).im| := by
    intro q
    have him :
        ((a • z + b • w) q).im =
          a * (z q).im + b * (w q).im := by
      simp [Pi.smul_apply, Complex.add_im]
    rw [him]
    calc
      |a * (z q).im + b * (w q).im|
          ≤ |a * (z q).im| + |b * (w q).im| := abs_add_le _ _
      _ = a * |(z q).im| + b * |(w q).im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum_le :
      (∑ q : osiiAxisPairIndex d, |((a • z + b • w) q).im|) ≤
        a * (∑ q : osiiAxisPairIndex d, |(z q).im|) +
          b * (∑ q : osiiAxisPairIndex d, |(w q).im|) := by
    calc
      (∑ q : osiiAxisPairIndex d, |((a • z + b • w) q).im|)
          ≤ ∑ q : osiiAxisPairIndex d,
              (a * |(z q).im| + b * |(w q).im|) :=
            Finset.sum_le_sum fun q _ => hpoint q
      _ = a * (∑ q : osiiAxisPairIndex d, |(z q).im|) +
            b * (∑ q : osiiAxisPairIndex d, |(w q).im|) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]
  have hlt :
      a * (∑ q : osiiAxisPairIndex d, |(z q).im|) +
          b * (∑ q : osiiAxisPairIndex d, |(w q).im|) <
        Real.pi / 2 := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hw
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hz
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hzmul :
            a * (∑ q : osiiAxisPairIndex d, |(z q).im|) <
              a * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hz ha_pos
        have hwmul :
            b * (∑ q : osiiAxisPairIndex d, |(w q).im|) <
              b * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hw hb_pos
        have hcombine :
            a * (Real.pi / 2) + b * (Real.pi / 2) =
              Real.pi / 2 := by
          calc
            a * (Real.pi / 2) + b * (Real.pi / 2) =
                (a + b) * (Real.pi / 2) := by ring
            _ = Real.pi / 2 := by rw [hab]; ring
        linarith
  exact hsum_le.trans_lt hlt

omit [NeZero d] in
/-- The axis-pair logarithmic MZ carrier is connected. -/
theorem isConnected_osiiAxisPairLogDomain :
    IsConnected (osiiAxisPairLogDomain (d := d)) := by
  refine ⟨⟨0, ?_⟩, convex_osiiAxisPairLogDomain.isPreconnected⟩
  simp [osiiAxisPairLogDomain]
  positivity

/-- The common real edge, viewed as a function on the Euclidean integration
space used by Gaussian regularization. -/
def OSIIAxisPairFlatCrossData.gaussianRealEdgeInput
    (X : OSIIAxisPairFlatCrossData d)
    (y : EuclideanSpace ℝ (osiiAxisPairIndex d)) : ℂ :=
  X.family.realEdge (fun a => y a)

/-- Move one selected coordinate of a real Euclidean input to a fixed
horizontal line in the corresponding flat OS-II branch. -/
def OSIIAxisPairFlatCrossData.gaussianShiftedFlatTubeInput
    (X : OSIIAxisPairFlatCrossData d)
    (a : osiiAxisPairIndex d)
    (y : ℝ)
    (u : EuclideanSpace ℝ (osiiAxisPairIndex d)) : ℂ :=
  X.family.flatTubeBranch
    (Function.update
      (osiiAxisPairLogRealEmbed (fun b => u b)) a
      ((u a : ℂ) + y * I))

/-- The Euclidean form of a flat cross's common real edge is continuous. -/
theorem OSIIAxisPairFlatCrossData.continuous_gaussianRealEdgeInput
    (X : OSIIAxisPairFlatCrossData d) :
    Continuous X.gaussianRealEdgeInput := by
  apply X.continuous_realEdge.comp
  apply continuous_pi
  intro a
  exact
    (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : osiiAxisPairIndex d => ℝ) a).continuous

/-- A fixed horizontal slice of a continuous flat-cross chart is continuous
as a function of all real coordinates. -/
theorem OSIIAxisPairFlatCrossData.continuous_gaussianShiftedFlatTubeInput
    (X : OSIIAxisPairFlatCrossData d)
    (a : osiiAxisPairIndex d)
    (y : ℝ)
    (hy : |y| < Real.pi / 2) :
    Continuous (X.gaussianShiftedFlatTubeInput a y) := by
  let chartPoint :
      EuclideanSpace ℝ (osiiAxisPairIndex d) →
        (osiiAxisPairIndex d → ℝ) × ℂ :=
    fun u => ((fun b => u b), (u a : ℂ) + y * I)
  have hchartPoint : Continuous chartPoint := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro b
      exact
        (PiLp.proj (𝕜 := ℝ) 2
          (fun _ : osiiAxisPairIndex d => ℝ) b).continuous
    · exact
        (Complex.continuous_ofReal.comp
          (PiLp.proj (𝕜 := ℝ) 2
            (fun _ : osiiAxisPairIndex d => ℝ) a).continuous).add
          continuous_const
  have hmaps :
      Set.MapsTo chartPoint Set.univ
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
    intro u _hu
    refine ⟨Set.mem_univ _, ?_⟩
    simpa [chartPoint] using hy
  have hcont :=
    (X.chart_continuous a).comp_continuous hchartPoint
      (fun u => hmaps (Set.mem_univ u))
  exact hcont.congr (fun u => by rfl)

/-- A global coordinate-chart bound controls every shifted Gaussian input on
that horizontal line. -/
theorem OSIIAxisPairFlatCrossData.norm_gaussianShiftedFlatTubeInput_le
    (X : OSIIAxisPairFlatCrossData d)
    (a : osiiAxisPairIndex d)
    (y C : ℝ)
    (hy : |y| < Real.pi / 2)
    (hbound :
      ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
        |w.im| < Real.pi / 2 →
          ‖X.family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (u : EuclideanSpace ℝ (osiiAxisPairIndex d)) :
    ‖X.gaussianShiftedFlatTubeInput a y u‖ ≤ C := by
  apply hbound (fun b => u b) ((u a : ℂ) + y * I)
  simpa using hy

set_option maxHeartbeats 1200000 in
/-- Moving one Gaussian center into a flat OS-II coordinate tube is exactly
the same as keeping the Gaussian center real and replacing the common real
edge by the corresponding shifted flat-branch input. -/
theorem OSIIAxisPairFlatCrossData.gaussianRegularization_flatTube_eq_shifted
    (X : OSIIAxisPairFlatCrossData d)
    (a : osiiAxisPairIndex d)
    (c : ℝ) (hc : 0 < c)
    (x : EuclideanSpace ℝ (osiiAxisPairIndex d))
    (y B C : ℝ)
    (hy : |y| < Real.pi / 2)
    (hB : ∀ u, ‖X.gaussianRealEdgeInput u‖ ≤ B)
    (hC : 0 ≤ C)
    (hchart :
      ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
        |w.im| < Real.pi / 2 →
          ‖X.family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C) :
    SCV.gaussianRegularization c X.gaussianRealEdgeInput
        (Function.update (SCV.gaussianRealEmbed x) a
          ((x a : ℂ) + y * I)) =
      SCV.gaussianRegularization c
        (X.gaussianShiftedFlatTubeInput a y)
        (SCV.gaussianRealEmbed x) := by
  have hreal_input :
      SCV.gaussianRealSliceInput X.family.flatTubeBranch =
        X.gaussianRealEdgeInput := by
    funext u
    change
      X.family.flatTubeBranch
          (osiiAxisPairLogRealEmbed (fun b => u b)) =
        X.family.realEdge (fun b => u b)
    exact X.family.flatTubeBranch_real_edge _
  have hshift_input :
      SCV.gaussianCoordinateShiftedInput
          X.family.flatTubeBranch a y =
        X.gaussianShiftedFlatTubeInput a y := by
    rfl
  have hline_diff :
      ∀ xBase : osiiAxisPairIndex d → ℝ,
        DifferentiableOn ℂ
          (SCV.gaussianCoordinateLine
            X.family.flatTubeBranch xBase a)
          (Set.univ ×ℂ Set.uIcc 0 y) := by
    intro xBase
    change DifferentiableOn ℂ (X.coordinateLine xBase a) _
    apply (X.coordinateLine_differentiableOn xBase a).mono
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have him_le : |w.im| ≤ |y| := by
      rcases Set.mem_uIcc.mp hw.2 with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        exact neg_le_neg h.1
    exact him_le.trans_lt hy
  have hline_bound :
      ∀ (xBase : osiiAxisPairIndex d → ℝ) (t v : ℝ),
        v ∈ Set.uIcc 0 y →
          ‖SCV.gaussianCoordinateLine
            X.family.flatTubeBranch xBase a (t + v * I)‖ ≤ C := by
    intro xBase t v hv
    change
      ‖X.family.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed xBase) a
          (t + v * I))‖ ≤ C
    apply hchart
    have hv_abs : |v| ≤ |y| := by
      rcases Set.mem_uIcc.mp hv with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
        exact neg_le_neg h.1
    simpa using hv_abs.trans_lt hy
  have hcenter :
      Function.update (SCV.gaussianRealEmbed x) a (x a : ℂ) =
        SCV.gaussianRealEmbed x := by
    funext b
    by_cases hba : b = a
    · subst b
      simp [SCV.gaussianRealEmbed]
    · simp [hba, SCV.gaussianRealEmbed]
  have hshift :=
    SCV.gaussianRegularization_update_eq_shifted
      X.family.flatTubeBranch a c hc
      (SCV.gaussianRealEmbed x) (x a) y B C
      (by simpa [hreal_input] using X.continuous_gaussianRealEdgeInput)
      (by
        simpa [hshift_input] using
          X.continuous_gaussianShiftedFlatTubeInput a y hy)
      (by simpa [hreal_input] using hB)
      (by
        simpa [hshift_input] using
          X.norm_gaussianShiftedFlatTubeInput_le a y C hy hchart)
      hC hline_diff hline_bound
  simpa [hreal_input, hshift_input, hcenter] using hshift

/-- The canonical entire Gaussian approximation to an axis-pair common real
edge. -/
def OSIIAxisPairFlatCrossData.gaussianApproximant
    (X : OSIIAxisPairFlatCrossData d)
    (n : ℕ)
    (z : osiiAxisPairIndex d → ℂ) : ℂ :=
  SCV.gaussianRegularization ((n + 1 : ℕ) : ℝ) X.gaussianRealEdgeInput z

/-- A globally bounded common real edge has entire Gaussian approximants. -/
theorem OSIIAxisPairFlatCrossData.gaussianApproximant_holomorphic
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (n : ℕ) :
    DifferentiableOn ℂ (X.gaussianApproximant n)
      (osiiAxisPairLogDomain (d := d)) := by
  exact
    (SCV.differentiable_gaussianRegularization_of_bounded
      ((n + 1 : ℕ) : ℝ) (by positivity)
      X.continuous_gaussianRealEdgeInput.aestronglyMeasurable B
      (fun y => hB (fun a => y a))).differentiableOn

/-- The canonical Gaussian approximants converge pointwise to a globally
bounded common real edge. -/
theorem OSIIAxisPairFlatCrossData.gaussianApproximant_realEdge_tendsto
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (x : osiiAxisPairIndex d → ℝ) :
    Tendsto
      (fun n => X.gaussianApproximant n (osiiAxisPairLogRealEmbed x))
      atTop (nhds (X.family.realEdge x)) := by
  let xE : EuclideanSpace ℝ (osiiAxisPairIndex d) := WithLp.toLp 2 x
  have hinput_bound :
      ∀ y : EuclideanSpace ℝ (osiiAxisPairIndex d),
        ‖X.gaussianRealEdgeInput y‖ ≤ B := by
    intro y
    exact hB (fun a => y a)
  have hbase :=
    SCV.tendsto_gaussianRegularization_real_of_bounded
      X.continuous_gaussianRealEdgeInput B hinput_bound xE
  have hscale :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  convert hbase.comp hscale using 1 <;> rfl

/-- A global bound on one coordinate chart gives the same scale-independent
bound for every Gaussian approximant on that flat tube. -/
theorem OSIIAxisPairFlatCrossData.norm_gaussianApproximant_flatTube_le
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (a : osiiAxisPairIndex d)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hchart :
      ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
        |w.im| < Real.pi / 2 →
          ‖X.family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (x : osiiAxisPairIndex d → ℝ)
    (y : ℝ)
    (hy : |y| < Real.pi / 2)
    (n : ℕ) :
    ‖X.gaussianApproximant n
      (Function.update (osiiAxisPairLogRealEmbed x) a
        ((x a : ℂ) + y * I))‖ ≤ C := by
  let xE : EuclideanSpace ℝ (osiiAxisPairIndex d) := WithLp.toLp 2 x
  have hinput_bound :
      ∀ u : EuclideanSpace ℝ (osiiAxisPairIndex d),
        ‖X.gaussianRealEdgeInput u‖ ≤ B := by
    intro u
    exact hB (fun b => u b)
  have hshift_bound :
      ∀ u : EuclideanSpace ℝ (osiiAxisPairIndex d),
        ‖X.gaussianShiftedFlatTubeInput a y u‖ ≤ C :=
    X.norm_gaussianShiftedFlatTubeInput_le a y C hy hchart
  have heq :=
    X.gaussianRegularization_flatTube_eq_shifted
      a ((n + 1 : ℕ) : ℝ) (by positivity) xE y B C hy
      hinput_bound hC hchart
  rw [gaussianApproximant]
  rw [show
    Function.update (osiiAxisPairLogRealEmbed x) a
        ((x a : ℂ) + y * I) =
      Function.update (SCV.gaussianRealEmbed xE) a
        ((xE a : ℂ) + y * I) by
          ext b
          by_cases hba : b = a
          · subst b
            simp [xE]
          · simp [xE, Function.update, hba, osiiAxisPairLogRealEmbed,
              SCV.gaussianRealEmbed]]
  rw [heq]
  exact
    SCV.norm_gaussianRegularization_real_le_of_bounded
      ((n + 1 : ℕ) : ℝ) (by positivity)
      (X.continuous_gaussianShiftedFlatTubeInput a y hy).aestronglyMeasurable
      C hshift_bound xE

/-- Flat imaginary directions are uniformly bounded for every canonical
Gaussian approximant when all coordinate charts share one bound. -/
theorem OSIIAxisPairFlatCrossData.gaussianApproximant_flatImaginary_bound
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (n : ℕ) :
    fintypeFlatImaginaryUnion
        (osiiAxisPairIndex d) (Real.pi / 2) ⊆
      SCV.horizontalBoundSet (X.gaussianApproximant n) C := by
  rintro y ⟨a, ha, hzero⟩ x
  have hpoint :
      SCV.horizontalPoint x y =
        Function.update (osiiAxisPairLogRealEmbed x) a
          ((x a : ℂ) + y a * I) := by
    ext b
    by_cases hba : b = a
    · subst b
      simp [SCV.horizontalPoint, osiiAxisPairLogRealEmbed]
    · simp [SCV.horizontalPoint, osiiAxisPairLogRealEmbed,
        Function.update, hba, hzero b hba]
  rw [hpoint]
  exact
    X.norm_gaussianApproximant_flatTube_le
      B hB a C hC (hchart a) x (y a) ha n

/-- Uniform flat-tube bounds propagate to the complete axis-pair logarithmic
carrier, independently of the Gaussian scale. -/
theorem OSIIAxisPairFlatCrossData.norm_gaussianApproximant_le_on_logDomain
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (n : ℕ)
    (z : osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairLogDomain (d := d)) :
    ‖X.gaussianApproximant n z‖ ≤ C := by
  let realPart : osiiAxisPairIndex d → ℝ := fun a => (z a).re
  let imagPart : osiiAxisPairIndex d → ℝ := fun a => (z a).im
  have himag :
      imagPart ∈
        fintypeImaginaryL1Domain
          (osiiAxisPairIndex d) (Real.pi / 2) := by
    simpa [imagPart, fintypeImaginaryL1Domain,
      osiiAxisPairLogDomain] using hz
  have himag_hull :
      imagPart ∈
        convexHull ℝ
          (fintypeFlatImaginaryUnion
            (osiiAxisPairIndex d) (Real.pi / 2)) := by
    rw [convexHull_fintypeFlatImaginary_eq_l1Domain
      (ι := osiiAxisPairIndex d) (alpha := Real.pi / 2) (by positivity)]
    exact himag
  have hinput_bound :
      ∀ u : EuclideanSpace ℝ (osiiAxisPairIndex d),
        ‖X.gaussianRealEdgeInput u‖ ≤ B := by
    intro u
    exact hB (fun a => u a)
  have hconvex :=
    SCV.gaussianRegularization_horizontalBound_convexHull_of_bounded
      ((n + 1 : ℕ) : ℝ) (by positivity)
      X.continuous_gaussianRealEdgeInput.aestronglyMeasurable
      B hinput_bound hC
      (X.gaussianApproximant_flatImaginary_bound
        B hB C hC.le hchart n)
  have hbound := hconvex himag_hull realPart
  have hz_horizontal :
      SCV.horizontalPoint realPart imagPart = z := by
    ext a
    apply Complex.ext <;> simp [SCV.horizontalPoint, realPart, imagPart]
  simpa [gaussianApproximant, hz_horizontal] using hbound

/-- The uniformly bounded canonical Gaussian approximants are equicontinuous
on the complete axis-pair logarithmic carrier. -/
theorem OSIIAxisPairFlatCrossData.equicontinuousOn_gaussianApproximant
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C) :
    EquicontinuousOn X.gaussianApproximant
      (osiiAxisPairLogDomain (d := d)) := by
  intro z hz
  apply EquicontinuousAt.equicontinuousWithinAt
  obtain ⟨R, hR, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_osiiAxisPairLogDomain z hz
  let modulus : (osiiAxisPairIndex d → ℂ) → ℝ :=
    fun q => (2 * C / R) * dist q z
  have hmodulus :
      Tendsto modulus (nhds z) (nhds 0) := by
    have hdist :
        Tendsto (fun q : osiiAxisPairIndex d → ℂ => dist q z)
          (nhds z) (nhds 0) := by
      simpa using
        ((tendsto_id : Tendsto id (nhds z) (nhds z)).dist
          (tendsto_const_nhds :
            Tendsto
              (fun _ : osiiAxisPairIndex d → ℂ => z)
              (nhds z) (nhds z)))
    simpa [modulus] using hdist.const_mul (2 * C / R)
  apply
    Metric.equicontinuousAt_of_continuity_modulus
      modulus hmodulus X.gaussianApproximant
  filter_upwards [Metric.ball_mem_nhds z hR] with q hq
  intro n
  have hdiff :
      DifferentiableOn ℂ (X.gaussianApproximant n) (Metric.ball z R) := by
    exact
      (X.gaussianApproximant_holomorphic B hB n).mono hball
  have hmaps :
      Set.MapsTo (X.gaussianApproximant n) (Metric.ball z R)
        (Metric.closedBall (X.gaussianApproximant n z) (2 * C)) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖X.gaussianApproximant n u - X.gaussianApproximant n z‖ ≤
          ‖X.gaussianApproximant n u‖ +
            ‖X.gaussianApproximant n z‖ :=
        norm_sub_le _ _
      _ ≤ C + C := by
        gcongr
        · exact X.norm_gaussianApproximant_le_on_logDomain
            B hB C hC hchart n u (hball hu)
        · exact X.norm_gaussianApproximant_le_on_logDomain
            B hB C hC hchart n z hz
      _ = 2 * C := by ring
  simpa [modulus, mul_comm, dist_comm] using
    dist_le_div_mul_dist_of_mapsTo_ball
      hdiff hmaps hq

/-- Uniform bounds on all coordinate charts force the canonical Gaussian
approximants to converge locally uniformly on the full logarithmic carrier.

The proof is a normal-family argument. Arzela-Ascoli gives compact closure in
the compact-open topology. Every cluster limit is holomorphic, has the common
real edge, and hence is unique by the finite-dimensional totally-real identity
theorem. Compactness then upgrades uniqueness of cluster points to convergence
of the complete sequence. -/
theorem OSIIAxisPairFlatCrossData.exists_gaussianApproximant_locallyUniform_limit
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C) :
    ∃ limit : (osiiAxisPairIndex d → ℂ) → ℂ,
      TendstoLocallyUniformlyOn X.gaussianApproximant limit atTop
        (osiiAxisPairLogDomain (d := d)) := by
  let U : Set (osiiAxisPairIndex d → ℂ) :=
    osiiAxisPairLogDomain (d := d)
  let D := {z : osiiAxisPairIndex d → ℂ // z ∈ U}
  let 𝔖 : Set (Set D) := {K | IsCompact K}
  let approx : ℕ → D → ℂ := fun n z => X.gaussianApproximant n z
  let G : ℕ → (D →ᵤ[𝔖] ℂ) :=
    fun n => UniformOnFun.ofFun 𝔖 (approx n)
  let T : (D →ᵤ[𝔖] ℂ) → D → ℂ :=
    UniformOnFun.toFun 𝔖
  have hcompact :
      IsCompact (closure (Set.range G)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := 𝔖) (F := T)
    · intro K hK
      exact hK
    · have hid :
          UniformOnFun.ofFun 𝔖 ∘ T =
            (id : (D →ᵤ[𝔖] ℂ) → (D →ᵤ[𝔖] ℂ)) := by
        funext f
        simp [T]
      rw [hid]
      exact IsClosedEmbedding.id
    · intro K _hK
      have hambient :
          EquicontinuousOn X.gaussianApproximant U :=
        X.equicontinuousOn_gaussianApproximant B hB C hC hchart
      have hsub :
          Equicontinuous (U.restrict ∘ X.gaussianApproximant) :=
        equicontinuous_restrict_iff X.gaussianApproximant |>.2 hambient
      let pick : Set.range G → ℕ :=
        fun f => Classical.choose f.property
      have hfamily :
          T ∘ ((↑) : Set.range G → (D →ᵤ[𝔖] ℂ)) =
            (U.restrict ∘ X.gaussianApproximant) ∘ pick := by
        funext f
        have hpick := Classical.choose_spec f.property
        funext z
        change T f z = X.gaussianApproximant (pick f) z
        rw [show f.1 = G (pick f) by simpa [pick] using hpick.symm]
        simp [T, G, approx, U, D]
      rw [hfamily]
      exact (hsub.equicontinuousOn K).comp pick
    · intro K _hK z _hz
      refine ⟨Metric.closedBall 0 C, isCompact_closedBall 0 C, ?_⟩
      intro f hf
      rcases hf with ⟨n, rfl⟩
      rw [Metric.mem_closedBall]
      simpa [T, G, approx, dist_zero_right] using
        X.norm_gaussianApproximant_le_on_logDomain
          B hB C hC hchart n z z.property
  have hcover : ⋃₀ 𝔖 = Set.univ := by
    ext z
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact ⟨{z}, by simpa [𝔖] using isCompact_singleton, Set.mem_singleton z⟩
  letI : T2Space (D →ᵤ[𝔖] ℂ) :=
    UniformOnFun.t2Space_of_covering hcover
  letI : LocallyCompactSpace D := by
    exact (show IsOpen U from isOpen_osiiAxisPairLogDomain).locallyCompactSpace
  let ambient :
      (D →ᵤ[𝔖] ℂ) → (osiiAxisPairIndex d → ℂ) → ℂ :=
    fun f z => if hz : z ∈ U then T f ⟨z, hz⟩ else 0
  have hcluster_properties :
      ∀ y : D →ᵤ[𝔖] ℂ, MapClusterPt y atTop G →
        DifferentiableOn ℂ (ambient y) U ∧
          ∀ x : osiiAxisPairIndex d → ℝ,
            ambient y (osiiAxisPairLogRealEmbed x) =
              X.family.realEdge x := by
    intro y hy
    obtain ⟨V, hV_le, hGy⟩ :=
      mapClusterPt_iff_ultrafilter.mp hy
    have hlocal_subtype :
        TendstoLocallyUniformly
          (fun n (z : D) => X.gaussianApproximant n z)
          (T y) V := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      have huniform :=
        (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hGy)
          K (by simpa [𝔖] using hK)
      simpa [G, T, approx, Function.comp_def] using huniform
    have hlocal_ambient :
        TendstoLocallyUniformlyOn X.gaussianApproximant
          (ambient y) V U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      simpa [ambient, U, D, T, Function.comp_def] using hlocal_subtype
    constructor
    · exact hlocal_ambient.differentiableOn_finite
        (Filter.Eventually.of_forall
          (X.gaussianApproximant_holomorphic B hB))
        isOpen_osiiAxisPairLogDomain
    · intro x
      exact tendsto_nhds_unique
        (hlocal_ambient.tendsto_at (osiiAxisPairLogRealEmbed_mem x))
        ((X.gaussianApproximant_realEdge_tendsto B hB x).mono_left hV_le)
  have hG_mem :
      ∀ᶠ n in atTop, G n ∈ closure (Set.range G) :=
    Filter.Eventually.of_forall fun n =>
      subset_closure (Set.mem_range_self n)
  have hG_map :
      Filter.map G atTop ≤
        Filter.principal (closure (Set.range G)) := by
    rw [Filter.le_principal_iff]
    exact hG_mem
  obtain ⟨y₀, _hy₀_mem, hy₀_cluster⟩ :=
    hcompact.exists_mapClusterPt hG_map
  have hy₀_properties :=
    hcluster_properties y₀ hy₀_cluster
  have hunique :
      ∀ y ∈ closure (Set.range G), MapClusterPt y atTop G → y = y₀ := by
    intro y _hy_mem hy_cluster
    have hy_properties :=
      hcluster_properties y hy_cluster
    have hambient_eq :
        Set.EqOn (ambient y) (ambient y₀) U := by
      exact SCV.holomorphic_eq_of_eq_on_real_of_connected_finite
        isOpen_osiiAxisPairLogDomain
        isConnected_osiiAxisPairLogDomain
        hy_properties.1 hy₀_properties.1
        (x₀ := 0)
        (by
          change osiiAxisPairLogRealEmbed
            (0 : osiiAxisPairIndex d → ℝ) ∈ U
          exact osiiAxisPairLogRealEmbed_mem
            (d := d) (0 : osiiAxisPairIndex d → ℝ))
        (fun x _hx => by
          change ambient y (osiiAxisPairLogRealEmbed x) =
            ambient y₀ (osiiAxisPairLogRealEmbed x)
          exact (hy_properties.2 x).trans (hy₀_properties.2 x).symm)
    funext z
    have hz_eq := hambient_eq z.property
    change ambient y z = ambient y₀ z at hz_eq
    change T y z = T y₀ z
    simpa only [ambient, dif_pos z.property] using hz_eq
  have hG_tendsto :
      Tendsto G atTop (nhds y₀) :=
    hcompact.tendsto_nhds_of_unique_mapClusterPt hG_mem hunique
  have hlocal_subtype :
      TendstoLocallyUniformly
        (fun n (z : D) => X.gaussianApproximant n z)
        (T y₀) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have huniform :=
      (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hG_tendsto)
        K (by simpa [𝔖] using hK)
    simpa [G, T, approx, Function.comp_def] using huniform
  refine ⟨ambient y₀, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa [ambient, U, D, T, Function.comp_def] using hlocal_subtype

/-- Concrete approximation data sufficient for continuous-edge
Malgrange-Zerner extension.

The intended approximants are entire Gaussian regularizations of the common
real edge. The remaining hard estimates are precisely `locallyUniform` and
`realEdge_tendsto`. -/
structure OSIIAxisPairMZApproximationData
    (X : OSIIAxisPairFlatCrossData d) where
  approximant :
    ℕ → (osiiAxisPairIndex d → ℂ) → ℂ
  limit :
    (osiiAxisPairIndex d → ℂ) → ℂ
  approximant_holomorphic :
    ∀ n, DifferentiableOn ℂ (approximant n)
      (osiiAxisPairLogDomain (d := d))
  locallyUniform :
    TendstoLocallyUniformlyOn approximant limit atTop
      (osiiAxisPairLogDomain (d := d))
  realEdge_tendsto :
    ∀ x : osiiAxisPairIndex d → ℝ,
      Tendsto
        (fun n => approximant n (osiiAxisPairLogRealEmbed x))
        atTop (nhds (X.family.realEdge x))

/-- Package the canonical Gaussian approximants into the MZ criterion. The
only remaining analytic input is locally uniform convergence on the full
logarithmic carrier. -/
def OSIIAxisPairFlatCrossData.gaussianMZApproximationData
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (limit : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hlocallyUniform :
      TendstoLocallyUniformlyOn X.gaussianApproximant limit atTop
        (osiiAxisPairLogDomain (d := d))) :
    OSIIAxisPairMZApproximationData X where
  approximant := X.gaussianApproximant
  limit := limit
  approximant_holomorphic := X.gaussianApproximant_holomorphic B hB
  locallyUniform := hlocallyUniform
  realEdge_tendsto := X.gaussianApproximant_realEdge_tendsto B hB

namespace OSIIAxisPairMZApproximationData

/-- The approximation limit is jointly holomorphic on the full logarithmic
carrier. -/
theorem limit_holomorphic
    {X : OSIIAxisPairFlatCrossData d}
    (A : OSIIAxisPairMZApproximationData X) :
    DifferentiableOn ℂ A.limit (osiiAxisPairLogDomain (d := d)) := by
  exact A.locallyUniform.differentiableOn_finite
    (Filter.Eventually.of_forall A.approximant_holomorphic)
    isOpen_osiiAxisPairLogDomain

/-- The approximation limit has the prescribed common real edge. -/
theorem limit_realEdge
    {X : OSIIAxisPairFlatCrossData d}
    (A : OSIIAxisPairMZApproximationData X)
    (x : osiiAxisPairIndex d → ℝ) :
    A.limit (osiiAxisPairLogRealEmbed x) = X.family.realEdge x := by
  exact tendsto_nhds_unique
    (A.locallyUniform.tendsto_at (osiiAxisPairLogRealEmbed_mem x))
    (A.realEdge_tendsto x)

/-- Approximation criterion in the reduced output shape consumed by the
axis-pair MZ producer. -/
theorem exists_holomorphic_realEdge_extension
    {X : OSIIAxisPairFlatCrossData d}
    (A : OSIIAxisPairMZApproximationData X) :
    ∃ Gamma : (osiiAxisPairIndex d → ℂ) → ℂ,
      DifferentiableOn ℂ Gamma (osiiAxisPairLogDomain (d := d)) ∧
        ∀ x : osiiAxisPairIndex d → ℝ,
          Gamma (osiiAxisPairLogRealEmbed x) = X.family.realEdge x :=
  ⟨A.limit, A.limit_holomorphic, A.limit_realEdge⟩

end OSIIAxisPairMZApproximationData

/-- Bounded continuous flat-cross data admits a simultaneous holomorphic
representative on the complete axis-pair logarithmic MZ carrier. -/
theorem OSIIAxisPairFlatCrossData.exists_holomorphic_realEdge_extension_of_bounds
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ)
    (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C) :
    ∃ Gamma : (osiiAxisPairIndex d → ℂ) → ℂ,
      DifferentiableOn ℂ Gamma (osiiAxisPairLogDomain (d := d)) ∧
        ∀ x : osiiAxisPairIndex d → ℝ,
          Gamma (osiiAxisPairLogRealEmbed x) = X.family.realEdge x := by
  obtain ⟨limit, hlimit⟩ :=
    X.exists_gaussianApproximant_locallyUniform_limit
      B hB C hC hchart
  exact
    (X.gaussianMZApproximationData B hB limit hlimit
      ).exists_holomorphic_realEdge_extension

/-- The canonical Gaussian sequence converges pointwise to every holomorphic
extension with the prescribed common real edge. The normal-family limit is
therefore independent of all choices made when selecting an extension. -/
theorem OSIIAxisPairFlatCrossData.gaussianApproximant_tendsto_extension
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ) (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (Gamma : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairLogDomain (d := d)))
    (hreal :
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) =
          X.family.realEdge x)
    (z : osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairLogDomain (d := d)) :
    Filter.Tendsto
      (fun q => X.gaussianApproximant q z)
      Filter.atTop (nhds (Gamma z)) := by
  obtain ⟨limit, hlimit⟩ :=
    X.exists_gaussianApproximant_locallyUniform_limit
      B hB C hC hchart
  let A : OSIIAxisPairMZApproximationData X :=
    X.gaussianMZApproximationData B hB limit hlimit
  have heq :
      ∀ w ∈ osiiAxisPairLogDomain (d := d),
        limit w = Gamma w := by
    intro w hw
    apply
      SCV.holomorphic_eq_of_eq_on_real_of_connected_finite
        isOpen_osiiAxisPairLogDomain
        isConnected_osiiAxisPairLogDomain
        A.limit_holomorphic hGamma
        (x₀ := (0 : osiiAxisPairIndex d → ℝ))
        (by
          change osiiAxisPairLogRealEmbed
            (0 : osiiAxisPairIndex d → ℝ) ∈
              osiiAxisPairLogDomain (d := d)
          exact osiiAxisPairLogRealEmbed_mem
            (d := d) (0 : osiiAxisPairIndex d → ℝ))
        (fun x _hx => by
          change
            limit (osiiAxisPairLogRealEmbed x) =
              Gamma (osiiAxisPairLogRealEmbed x)
          calc
            limit (osiiAxisPairLogRealEmbed x) =
                X.family.realEdge x := by
              exact A.limit_realEdge x
            _ = Gamma (osiiAxisPairLogRealEmbed x) :=
              (hreal x).symm)
        w hw
  simpa [heq z hz] using hlimit.tendsto_at hz

/-- A uniform coordinate-chart bound survives the Gaussian normal-family
limit.  Thus analytic continuation does not enlarge the quantitative bound
used to construct it. -/
theorem OSIIAxisPairFlatCrossData.norm_holomorphic_realEdge_extension_le
    (X : OSIIAxisPairFlatCrossData d)
    (B : ℝ)
    (hB : ∀ x, ‖X.family.realEdge x‖ ≤ B)
    (C : ℝ) (hC : 0 < C)
    (hchart :
      ∀ a : osiiAxisPairIndex d,
        ∀ (x : osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
            ‖X.family.flatTubeBranch
              (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤ C)
    (Gamma : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hGamma :
      DifferentiableOn ℂ Gamma
        (osiiAxisPairLogDomain (d := d)))
    (hreal :
      ∀ x : osiiAxisPairIndex d → ℝ,
        Gamma (osiiAxisPairLogRealEmbed x) =
          X.family.realEdge x)
    (z : osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairLogDomain (d := d)) :
    ‖Gamma z‖ ≤ C := by
  apply le_of_tendsto
    ((X.gaussianApproximant_tendsto_extension
      B hB C hC hchart Gamma hGamma hreal z hz).norm)
  exact Filter.Eventually.of_forall fun q =>
    X.norm_gaussianApproximant_le_on_logDomain
      B hB C hC hchart q z hz

end OSReconstruction
