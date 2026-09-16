/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIComplexSemigroupContraction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.SCV.EuclideanWeylFrechet










noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private theorem continuousAt_euclideanTranslateSchwartz_zero
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    ContinuousAt
      (fun h : EuclideanSpace ℝ ι => SCV.euclideanTranslateSchwartzCLM h φ)
      0 := by
  rw [ContinuousAt]
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
  intro p ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    SCV.exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm
      φ p.1 p.2
  let L := SCV.euclideanLineDerivDirectionCLM φ
  have hL :
      Filter.Tendsto (fun h : EuclideanSpace ℝ ι => L h)
        (nhds 0) (nhds 0) := by
    convert L.continuous.tendsto (0 : EuclideanSpace ℝ ι) using 1
    all_goals simp
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _] at hL
  specialize hL p (ε / 2) (by positivity)
  let δ : ℝ := min 1 (ε / (2 * (C + 1)))
  have hδ_pos : 0 < δ := by
    have hC1 : 0 < C + 1 := by linarith
    exact lt_min zero_lt_one (by positivity)
  filter_upwards [hL, Metric.ball_mem_nhds (0 : EuclideanSpace ℝ ι) hδ_pos]
      with h hLh hh
  have hh_norm : ‖h‖ < δ := by
    simpa [dist_eq_norm] using hh
  have hh_unit : ‖h‖ ≤ 1 :=
    le_trans (le_of_lt hh_norm) (min_le_left _ _)
  have hh_small : ‖h‖ < ε / (2 * (C + 1)) :=
    lt_of_lt_of_le hh_norm (min_le_right _ _)
  have hrem := hC h hh_unit
  have hrem_small :
      SchwartzMap.seminorm ℝ p.1 p.2
          (SCV.euclideanTranslateSchwartzCLM h φ - φ - L h) < ε / 2 := by
    calc
      SchwartzMap.seminorm ℝ p.1 p.2
          (SCV.euclideanTranslateSchwartzCLM h φ - φ - L h)
          ≤ C * ‖h‖ ^ 2 := hrem
      _ ≤ C * ‖h‖ := by
        gcongr
        nlinarith [norm_nonneg h]
      _ ≤ (C + 1) * ‖h‖ := by
        gcongr
        linarith
      _ < (C + 1) * (ε / (2 * (C + 1))) := by
        gcongr
      _ = ε / 2 := by
        have hC1 : C + 1 ≠ 0 := ne_of_gt (by linarith)
        field_simp
  have hsplit :
      SCV.euclideanTranslateSchwartzCLM h φ - φ =
        (SCV.euclideanTranslateSchwartzCLM h φ - φ - L h) + L h := by
    abel
  simp only [SCV.euclideanTranslateSchwartzCLM_zero]
  rw [hsplit]
  exact lt_of_le_of_lt
    (map_add_le_add (SchwartzMap.seminorm ℝ p.1 p.2) _ _)
    (by
      simp only [sub_zero] at hLh
      change SchwartzMap.seminorm ℝ p.1 p.2 (L h) < ε / 2 at hLh
      linarith)

private theorem continuous_euclideanTranslateSchwartz
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Continuous
      (fun h : EuclideanSpace ℝ ι =>
        SCV.euclideanTranslateSchwartzCLM h φ) := by
  rw [continuous_iff_continuousAt]
  intro h₀
  let φ₀ := SCV.euclideanTranslateSchwartzCLM h₀ φ
  have hzero := continuousAt_euclideanTranslateSchwartz_zero φ₀
  have hshift :
      ContinuousAt (fun h : EuclideanSpace ℝ ι => h - h₀) h₀ := by
    fun_prop
  have hcomp :
      ContinuousAt
        (fun h : EuclideanSpace ℝ ι =>
          SCV.euclideanTranslateSchwartzCLM (h - h₀) φ₀)
        h₀ := by
    change ContinuousAt
      ((fun h => SCV.euclideanTranslateSchwartzCLM h φ₀) ∘
        fun h => h - h₀) h₀
    exact ContinuousAt.comp_of_eq hzero hshift (by simp)
  convert hcomp using 1
  funext h
  rw [SCV.euclideanTranslateSchwartzCLM_comp]
  congr 2
  abel

private theorem continuous_translateSchwartz_fin
    {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Continuous (fun a : Fin m → ℝ => SCV.translateSchwartz a φ) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let φE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ
  let unE :
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
        SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  have hparam : Continuous (fun a : Fin m → ℝ => e.symm a) :=
    e.symm.continuous
  have htransE :
      Continuous
        (fun a : Fin m → ℝ =>
          SCV.euclideanTranslateSchwartzCLM (e.symm a) φE) :=
    (continuous_euclideanTranslateSchwartz φE).comp hparam
  refine (unE.continuous.comp htransE).congr ?_
  intro a
  ext x
  change φ (e (e.symm x + e.symm a)) = φ (x + a)
  rw [map_add, e.apply_symm_apply, e.apply_symm_apply]

/-- Translation of a fixed Schwartz function is continuous in its full
translation vector, without a compact-support hypothesis. -/
theorem continuous_translateSchwartz_unrestricted
    {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Continuous (fun a : Fin m → ℝ => SCV.translateSchwartz a φ) :=
  continuous_translateSchwartz_fin φ

omit [NeZero d] in
/-- Every `n`-point Schwartz source varies continuously under common spacetime
translation; compact support is not needed. -/
theorem continuous_translateSchwartzNPoint
    {n : Nat} (f : SchwartzNPoint d n) :
    Continuous
      (fun a : SpacetimeDim d =>
        translateSchwartzNPoint (d := d) a f) := by
  let fFlat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f
  let diagonalNegFlat :
      SpacetimeDim d → Fin (n * (d + 1)) → ℝ :=
    fun a p => -a (finProdFinEquiv.symm p).2
  have hdiagonal : Continuous diagonalNegFlat := by
    apply continuous_pi
    intro p
    exact
      ((continuous_apply (finProdFinEquiv.symm p).2).neg :
        Continuous fun a : SpacetimeDim d =>
          -a (finProdFinEquiv.symm p).2)
  have hflat :
      Continuous
        (fun a : SpacetimeDim d =>
          SCV.translateSchwartz (diagonalNegFlat a) fFlat) :=
    (continuous_translateSchwartz_fin fFlat).comp hdiagonal
  refine ((unflattenSchwartzNPoint (d := d)).continuous.comp hflat).congr ?_
  intro a
  ext x
  simp only [Function.comp_apply, unflattenSchwartzNPoint_apply,
    SCV.translateSchwartz_apply, fFlat, flattenSchwartzNPoint_apply,
    translateSchwartzNPoint_apply]
  congr 1
  ext i j
  have hmod : (finProdFinEquiv (i, j)).modNat = j := by
    change (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = j
    simp
  simp [diagonalNegFlat, hmod, sub_eq_add_neg]

/-- The completed genuine OS time shifts satisfy the semigroup law without an
arity-uniform or legacy linear-growth assumption. -/
theorem osiiOriginalOSHilbertShift_semigroup
    (OS : OsterwalderSchraderAxioms d)
    (s t : Real) (hs : 0 < s) (ht : 0 < t) :
    (osTimeShiftHilbertOfOS (d := d) OS s hs).comp
        (osTimeShiftHilbertOfOS (d := d) OS t ht) =
      osTimeShiftHilbertOfOS (d := d) OS (s + t) (add_pos hs ht) := by
  ext x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((osTimeShiftHilbertOfOS (d := d) OS s hs).comp
        (osTimeShiftHilbertOfOS (d := d) OS t ht)).continuous
      (osTimeShiftHilbertOfOS (d := d) OS (s + t) (add_pos hs ht)).continuous
  · intro a
    change
      osTimeShiftHilbertOfOS (d := d) OS s hs
          (osTimeShiftHilbertOfOS (d := d) OS t ht
            (a : OSHilbertSpace OS)) =
        osTimeShiftHilbertOfOS (d := d) OS (s + t) (add_pos hs ht)
          (a : OSHilbertSpace OS)
    rw [osTimeShiftHilbertOfOS_coe (d := d) OS t ht a,
      osTimeShiftHilbertOfOS_coe (d := d) OS s hs
        (osTimeShiftLinear (d := d) OS t ht a),
      osTimeShiftHilbertOfOS_coe (d := d) OS (s + t) (add_pos hs ht) a]
    have hlin := congrArg
      (fun L : OSPreHilbertSpace OS →ₗ[Complex] OSPreHilbertSpace OS => L a)
      ((euclideanSemigroup_of_OS OS).semigroup s t hs ht)
    exact congrArg
      (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hlin

omit [NeZero d] in
/-- Ordinary Schwartz translation continuity applies to every positive-time
source; compact support is not needed. -/
theorem continuous_osiiOriginalOSTimeShiftSchwartzNPoint
    {n : Nat} (f : SchwartzNPoint d n) :
    Continuous
      (fun t : Real => timeShiftSchwartzNPoint (d := d) t f) := by
  apply (continuous_translateSchwartzNPoint f).comp
  apply continuous_pi
  intro mu
  by_cases hmu : mu = 0
  · subst mu
    simp only [timeShiftVec, if_pos rfl]
    exact continuous_id
  · simpa [timeShiftVec, hmu] using
      (continuous_const : Continuous (fun _ : Real => (0 : Real)))

omit [NeZero d] in
@[simp] theorem osiiOriginalOSTimeShiftSchwartzNPoint_zero
    {n : Nat} (f : SchwartzNPoint d n) :
    timeShiftSchwartzNPoint (d := d) 0 f = f := by
  ext x
  change f (fun i => x i - timeShiftVec d 0) = f x
  congr 1
  funext i mu
  simp [timeShiftVec]

/-- Ordered-positive sources remain invariant under every nonnegative
Euclidean time translation, including the identity at zero. -/
def osiiOriginalOSNonnegativeTimeShiftSource
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (t : {t : Real // 0 ≤ t}) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨timeShiftSchwartzNPoint (d := d) t.1 f.1, by
    by_cases ht : 0 < t.1
    · exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) t.1 ht f.1 f.2
    · have hzero : t.1 = 0 := le_antisymm (le_of_not_gt ht) t.2
      have hshift :
          timeShiftSchwartzNPoint (d := d) t.1 f.1 = f.1 := by
        rw [hzero, osiiOriginalOSTimeShiftSchwartzNPoint_zero]
      rw [hshift]
      exact f.2⟩

theorem continuous_osiiOriginalOSNonnegativeTimeShiftSource
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    Continuous (osiiOriginalOSNonnegativeTimeShiftSource f) := by
  apply continuous_induced_rng.mpr
  exact
    (continuous_osiiOriginalOSTimeShiftSchwartzNPoint f.1).comp
      continuous_subtype_val

/-- Positive translation remains inside the original ordered-positive source
submodule. -/
def osiiOriginalOSPositiveTimeShiftSource
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (t : {t : Real // 0 < t}) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  ⟨timeShiftSchwartzNPoint (d := d) t.1 f.1,
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t.1 t.2 f.1 f.2⟩

theorem continuous_osiiOriginalOSPositiveTimeShiftSource
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    Continuous (osiiOriginalOSPositiveTimeShiftSource f) := by
  apply continuous_induced_rng.mpr
  exact
    (continuous_osiiOriginalOSTimeShiftSchwartzNPoint f.1).comp
      continuous_subtype_val

/-- On homogeneous OS source vectors, the completed shift is literally
translation of the underlying Schwartz source. -/
theorem osiiOriginalOSHilbertShift_single_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (t : {t : Real // 0 < t}) :
    osTimeShiftHilbertOfOS (d := d) OS t.1 t.2
        (osiiPositiveTimeSingleVectorCLM OS n f) =
      osiiPositiveTimeSingleVectorCLM OS n
        (osiiOriginalOSPositiveTimeShiftSource f t) := by
  have hf := f.2
  change tsupport (f.1 : NPointDomain d n → ℂ) ⊆
    OrderedPositiveTimeRegion d n at hf
  let ft := osiiOriginalOSPositiveTimeShiftSource f t
  have hft := ft.2
  change tsupport (ft.1 : NPointDomain d n → ℂ) ⊆
    OrderedPositiveTimeRegion d n at hft
  let x₀ : OSPreHilbertSpace OS :=
    ⟦PositiveTimeBorchersSequence.single n f.1 hf⟧
  rw [osiiPositiveTimeSingleVectorCLM_apply]
  change osTimeShiftHilbertOfOS (d := d) OS t.1 t.2
      (x₀ : OSHilbertSpace OS) = _
  rw [osTimeShiftHilbertOfOS_coe]
  rw [osiiPositiveTimeSingleVectorCLM_apply]
  apply congrArg (fun x : OSPreHilbertSpace OS => (x : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro k
  change
    (timeShiftPositiveTimeBorchers t.1 t.2
      (PositiveTimeBorchersSequence.single n f.1 hf)).toBorchersSequence.funcs k =
    (PositiveTimeBorchersSequence.single n ft.1 hft).toBorchersSequence.funcs k
  by_cases hk : k = n
  · subst k
    rw [PositiveTimeBorchersSequence.single_toBorchersSequence]
    simp [BorchersSequence.single]
    rfl
  · rw [PositiveTimeBorchersSequence.single_toBorchersSequence]
    simp [BorchersSequence.single, hk]

/-- The original Euclidean shift is strongly continuous on every homogeneous
positive-time Schwartz source vector. -/
theorem continuous_osiiOriginalOSHilbertShift_single
    (OS : OsterwalderSchraderAxioms d)
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    Continuous
      (fun t : {t : Real // 0 < t} =>
        osTimeShiftHilbertOfOS (d := d) OS t.1 t.2
          (osiiPositiveTimeSingleVectorCLM OS n f)) := by
  have hcontinuous :=
    (osiiPositiveTimeSingleVectorCLM OS n).continuous.comp
      (continuous_osiiOriginalOSPositiveTimeShiftSource f)
  change Continuous
    ((osiiPositiveTimeSingleVectorCLM OS n) ∘
      osiiOriginalOSPositiveTimeShiftSource f) at hcontinuous
  convert hcontinuous using 1
  funext t
  exact osiiOriginalOSHilbertShift_single_eq OS f t

/-- Positivity and the genuine semigroup law identify every positive rational
shift with the spectral power of the time-one shift. -/
theorem osiiOriginalOSHilbertShift_rational_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d)
    (p q : Nat) (hp : 0 < p) (hq : 0 < q) :
    osTimeShiftHilbertOfOS (d := d) OS ((p : Real) * (q : Real)⁻¹)
        (mul_pos (by exact_mod_cast hp)
          (inv_pos.mpr (by exact_mod_cast hq))) =
      CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
        ((p : NNReal) * (q : NNReal)⁻¹) := by
  simpa using ContinuousLinearMap.semigroup_rational_eq_positive_qroot
    (T := fun t ht => osTimeShiftHilbertOfOS (d := d) OS t ht)
    (hsemigroup := by
      intro s hs t ht
      simpa [show (HMul.hMul :
          (OSHilbertSpace OS →L[Complex] OSHilbertSpace OS) → _ → _) =
          ContinuousLinearMap.comp from rfl] using
        (osiiOriginalOSHilbertShift_semigroup OS s t hs ht).symm)
    (hnonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS)
    p q hp hq

/-- The positive real spectral continuation is the nonnegative spectral power
of the time-one shift. -/
theorem osiiOriginalOSHilbertComplex_ofReal_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d)
    (t : Real) (ht : 0 < t) :
    osiiOriginalOSHilbertComplex OS (t : Complex) =
      CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
        (Real.toNNReal t) := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_ofReal_eq_nnrpow
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)
      (t := t) ht)

private theorem denseRange_osiiPositiveRatCast :
    DenseRange
      (fun q : {q : Rat // 0 < (q : Real)} =>
        (⟨(q : Real), q.2⟩ : {t : Real // 0 < t})) := by
  intro x
  rcases x with ⟨x, hx⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
  rw [isOpen_induced_iff] at hV_open
  obtain ⟨W, hW_open, hW_eq⟩ := hV_open
  have hxW : x ∈ W := by
    rw [← hW_eq] at hxV
    exact hxV
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hW_open x hxW
  have hinterval : max (x / 2) (x - epsilon) < x + epsilon :=
    max_lt (by linarith) (by linarith)
  obtain ⟨q, hq_lower, hq_upper⟩ := exists_rat_btwn hinterval
  have hq_positive : (0 : Real) < q :=
    lt_trans (lt_max_of_lt_left (by linarith)) hq_lower
  refine ⟨⟨q, hq_positive⟩, ?_, ⟨⟨q, hq_positive⟩, rfl⟩⟩
  apply hVU
  rw [← hW_eq]
  exact hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;>
      linarith [le_max_right (x / 2) (x - epsilon)])

private theorem osiiPositiveRat_as_nat_fraction
    (q : Rat) (hq : 0 < (q : Real)) :
    ∃ (p m : Nat), 0 < p ∧ 0 < m ∧
      (q : Real) = (p : Real) / (m : Real) := by
  have hq_positive : 0 < q := by exact_mod_cast hq
  have hnumerator : 0 < q.num := Rat.num_pos.mpr hq_positive
  refine ⟨q.num.toNat, q.den, by omega, q.den_pos, ?_⟩
  have hnumerator_cast : (q.num.toNat : Int) = q.num :=
    Int.toNat_of_nonneg hnumerator.le
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast hnumerator_cast.symm

/-- Strong Schwartz-source continuity and rational density identify the
original shift with its spectral power at every positive real time. -/
theorem osiiOriginalOSHilbertShift_single_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d)
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (t : Real) (ht : 0 < t) :
    osTimeShiftHilbertOfOS (d := d) OS t ht
        (osiiPositiveTimeSingleVectorCLM OS n f) =
      CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
        (Real.toNNReal t)
        (osiiPositiveTimeSingleVectorCLM OS n f) := by
  let x : OSHilbertSpace OS := osiiPositiveTimeSingleVectorCLM OS n f
  let g : {s : Real // 0 < s} -> OSHilbertSpace OS := fun s =>
    osTimeShiftHilbertOfOS (d := d) OS s.1 s.2 x
  let h : {s : Real // 0 < s} -> OSHilbertSpace OS := fun s =>
    CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (Real.toNNReal s.1) x
  have hg : Continuous g := by
    simpa [g, x] using continuous_osiiOriginalOSHilbertShift_single OS f
  have hh0 :
      ContinuousOn
        (fun s : Real =>
          CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
            (Real.toNNReal s) x)
        (Set.Ioi 0) :=
    (ContinuousLinearMap.apply Complex (OSHilbertSpace OS) x).continuous.comp_continuousOn
      (ContinuousLinearMap.continuousOn_nnrpow_posReal
        (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos))
  have hh : Continuous h := by
    rw [continuousOn_iff_continuous_restrict] at hh0
    change Continuous
      (fun s : {s : Real // 0 < s} =>
        CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
          (Real.toNNReal s.1) x) at hh0
    exact hh0
  let ratCast : {q : Rat // 0 < (q : Real)} -> {s : Real // 0 < s} :=
    fun q => ⟨(q : Real), q.2⟩
  have hrat : g ∘ ratCast = h ∘ ratCast := by
    funext q
    obtain ⟨p, m, hp, hm, hq⟩ :=
      osiiPositiveRat_as_nat_fraction q.1 q.2
    have hratio_positive : 0 < (p : Real) * (m : Real)⁻¹ :=
      mul_pos (by exact_mod_cast hp)
        (inv_pos.mpr (by exact_mod_cast hm))
    have hratio : (q : Real) = (p : Real) * (m : Real)⁻¹ := by
      simpa [div_eq_mul_inv] using hq
    have hsubtype :
        ratCast q =
          ⟨(p : Real) * (m : Real)⁻¹, hratio_positive⟩ :=
      Subtype.ext hratio
    calc
      g (ratCast q) =
          g ⟨(p : Real) * (m : Real)⁻¹, hratio_positive⟩ :=
        congrArg g hsubtype
      _ = h ⟨(p : Real) * (m : Real)⁻¹, hratio_positive⟩ := by
        have hexponent :
            Real.toNNReal ((p : Real) * (m : Real)⁻¹) =
              (p : NNReal) * (m : NNReal)⁻¹ := by
          apply NNReal.eq
          rw [Real.coe_toNNReal]
          · simp
          · positivity
        rw [show g ⟨(p : Real) * (m : Real)⁻¹, hratio_positive⟩ =
            osTimeShiftHilbertOfOS (d := d) OS
              ((p : Real) * (m : Real)⁻¹) hratio_positive x by rfl]
        rw [show h ⟨(p : Real) * (m : Real)⁻¹, hratio_positive⟩ =
            CFC.nnrpow (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
              (Real.toNNReal ((p : Real) * (m : Real)⁻¹)) x by rfl]
        rw [hexponent]
        exact congrArg (fun A => A x)
          (osiiOriginalOSHilbertShift_rational_eq_nnrpow OS p m hp hm)
      _ = h (ratCast q) := (congrArg h hsubtype).symm
  have heverywhere : g = h :=
    DenseRange.equalizer (f := ratCast)
      denseRange_osiiPositiveRatCast hg hh hrat
  exact congrFun heverywhere ⟨t, ht⟩

/-- The holomorphic original-OS spectral semigroup has exactly the actual
Euclidean real edge on every homogeneous positive-time Schwartz source. -/
theorem osiiOriginalOSHilbertComplex_ofReal_single_eq_shift
    (OS : OsterwalderSchraderAxioms d)
    {n : Nat}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (t : Real) (ht : 0 < t) :
    osiiOriginalOSHilbertComplex OS (t : Complex)
        (osiiPositiveTimeSingleVectorCLM OS n f) =
      osTimeShiftHilbertOfOS (d := d) OS t ht
        (osiiPositiveTimeSingleVectorCLM OS n f) := by
  rw [osiiOriginalOSHilbertComplex_ofReal_eq_nnrpow OS t ht]
  exact (osiiOriginalOSHilbertShift_single_eq_nnrpow OS f t ht).symm

/-- Every completed OS Borchers source is the finite sum of its homogeneous
source vectors. -/
theorem osiiOriginalOSBorchersVector_eq_sum_single
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        osiiPositiveTimeSingleVectorCLM OS n
          ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩ := by
  apply ext_inner_left Complex
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)
  · intro y
    induction y using Quotient.inductionOn with
    | h G =>
      rw [inner_sum]
      let g₀ : OSPreHilbertSpace OS := ⟦G⟧
      let f₀ : OSPreHilbertSpace OS := ⟦F⟧
      change @inner Complex (OSHilbertSpace OS) inferInstance
          (g₀ : OSHilbertSpace OS) (f₀ : OSHilbertSpace OS) = _
      rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
      rw [PositiveTimeBorchersSequence.osInner_eq_sum_right_singles]
      apply Finset.sum_congr rfl
      intro i hi
      rw [osiiPositiveTimeSingleVectorCLM_apply]
      let s₀ : OSPreHilbertSpace OS :=
        ⟦PositiveTimeBorchersSequence.single i
          (F.toBorchersSequence.funcs i) (F.ordered_tsupport i)⟧
      change _ = @inner Complex (OSHilbertSpace OS) inferInstance
          (g₀ : OSHilbertSpace OS) (s₀ : OSHilbertSpace OS)
      rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]

/-- On the whole completed OS Hilbert space, the holomorphic spectral
semigroup agrees with the actual Euclidean shift at every positive real time. -/
theorem osiiOriginalOSHilbertComplex_ofReal_eq_shift
    (OS : OsterwalderSchraderAxioms d)
    (t : Real) (ht : 0 < t) :
    osiiOriginalOSHilbertComplex OS (t : Complex) =
      osTimeShiftHilbertOfOS (d := d) OS t ht := by
  ext x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (osiiOriginalOSHilbertComplex OS (t : Complex)).continuous
      (osTimeShiftHilbertOfOS (d := d) OS t ht).continuous
  · intro y
    induction y using Quotient.inductionOn with
    | h F =>
      rw [osiiOriginalOSBorchersVector_eq_sum_single OS F]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      exact osiiOriginalOSHilbertComplex_ofReal_single_eq_shift OS
        ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩ t ht

/-- The original OS Hilbert shift gives a continuous real-time pairing in the
right source without a growth hypothesis. -/
noncomputable def osiiOriginalOSPositiveTimeRealShiftPairingRightCLM
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat) (t : Real) (ht : 0 < t)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) m →L[Complex] Complex :=
  (innerSL Complex (osiiPositiveTimeSingleVectorCLM OS n f)).comp
    ((osTimeShiftHilbertOfOS (d := d) OS t ht).comp
      (osiiPositiveTimeSingleVectorCLM OS m))

/-- The original-OS real-shift pairing is exactly the zero-diagonal Schwinger
product shell, for unrestricted positive-time Schwartz sources. -/
theorem osiiOriginalOSPositiveTimeRealShiftPairingRightCLM_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat) (t : Real) (ht : 0 < t)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiOriginalOSPositiveTimeRealShiftPairingRightCLM
        OS n m t ht f g =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  rw [osiiOriginalOSPositiveTimeRealShiftPairingRightCLM]
  change
    @inner Complex (OSHilbertSpace OS) inferInstance
        (osiiPositiveTimeSingleVectorCLM OS n f)
        ((osTimeShiftHilbertOfOS (d := d) OS t ht)
          (osiiPositiveTimeSingleVectorCLM OS m g)) = _
  have hf := f.2
  change tsupport (f.1 : NPointDomain d n → ℂ) ⊆
    OrderedPositiveTimeRegion d n at hf
  have hg := g.2
  change tsupport (g.1 : NPointDomain d m → ℂ) ⊆
    OrderedPositiveTimeRegion d m at hg
  let F₀ := PositiveTimeBorchersSequence.single n f.1 hf
  let G₀ := PositiveTimeBorchersSequence.single m g.1 hg
  let x₀ : OSPreHilbertSpace OS :=
    ⟦F₀⟧
  let y₀ : OSPreHilbertSpace OS :=
    ⟦G₀⟧
  rw [osiiPositiveTimeSingleVectorCLM_apply,
    osiiPositiveTimeSingleVectorCLM_apply]
  change
    @inner Complex (OSHilbertSpace OS) inferInstance
      (x₀ : OSHilbertSpace OS)
      ((osTimeShiftHilbertOfOS (d := d) OS t ht)
        (y₀ : OSHilbertSpace OS)) = _
  rw [osTimeShiftHilbertOfOS_coe (d := d) OS t ht]
  rw [UniformSpace.Completion.inner_coe]
  dsimp [x₀, y₀, osTimeShiftLinear, osTimeShift]
  change @inner Complex (OSPreHilbertSpace OS) inferInstance
      (⟦F₀⟧) (⟦timeShiftPositiveTimeBorchers t ht G₀⟧) = _
  rw [OSPreHilbertSpace.inner_eq]
  simpa [F₀, G₀, osTimeShiftLinear, osTimeShift,
    PositiveTimeBorchersSequence.osInner,
    timeShiftPositiveTimeBorchers,
    PositiveTimeBorchersSequence.single_toBorchersSequence] using
    OSInnerProduct_single_right_timeShift
      (d := d) OS f.1 g.1 t

/-- The source-continuous original-OS holomorphic semigroup pairing needs
neither the legacy growth record nor compactly supported source blocks. -/
noncomputable def osiiOriginalOSPositiveTimeSemigroupPairingRightCLM
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat) (z : Complex)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSubmodule (d := d) m →L[Complex] Complex :=
  osiiPositiveTimeSingleSemigroupPairingRightCLM OS n m z f

@[simp] theorem osiiOriginalOSPositiveTimeSemigroupPairingRightCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat) (z : Complex)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiOriginalOSPositiveTimeSemigroupPairingRightCLM
        OS n m z f g =
      @inner Complex (OSHilbertSpace OS) inferInstance
        (osiiPositiveTimeSingleVectorCLM OS n f)
        (osiiOriginalOSHilbertComplex OS z
          (osiiPositiveTimeSingleVectorCLM OS m g)) :=
  rfl

/-- The original-OS source pairing is holomorphic throughout the physical
right half-plane. -/
theorem differentiableOn_osiiOriginalOSPositiveTimeSemigroupPairing
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    DifferentiableOn Complex
      (fun z =>
        osiiOriginalOSPositiveTimeSemigroupPairingRightCLM
          OS n m z f g)
      {z : Complex | 0 < z.re} := by
  simpa only [osiiOriginalOSPositiveTimeSemigroupPairingRightCLM_apply]
    using
      differentiableOn_osiiOriginalOSHilbertComplex_inner OS
        (osiiPositiveTimeSingleVectorCLM OS n f)
        (osiiPositiveTimeSingleVectorCLM OS m g)

/-- The original-OS holomorphic pairing recovers the literal zero-diagonal
Schwinger product shell at every positive real time. -/
theorem osiiOriginalOSPositiveTimeSemigroupPairing_ofReal_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (n m : Nat) (t : Real) (ht : 0 < t)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiOriginalOSPositiveTimeSemigroupPairingRightCLM
        OS n m (t : Complex) f g =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  rw [osiiOriginalOSPositiveTimeSemigroupPairingRightCLM_apply,
    osiiOriginalOSHilbertComplex_ofReal_single_eq_shift OS g t ht]
  exact
    osiiOriginalOSPositiveTimeRealShiftPairingRightCLM_eq_schwinger
      OS n m t ht f g

/-- On positive real time, the spectral complex semigroup and the honest OS
time-shift pairing agree on every positive-time source. -/
theorem osiiPositiveTimeSingleSemigroupPairing_ofReal_eq_realShift
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (t : ℝ) (ht : 0 < t)
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    osiiPositiveTimeSingleSemigroupPairingRightCLM
        OS n m (t : ℂ) f =
      osiiOriginalOSPositiveTimeRealShiftPairingRightCLM
        OS n m t ht f := by
  ext g
  change
    @inner Complex (OSHilbertSpace OS) inferInstance
      (osiiPositiveTimeSingleVectorCLM OS n f)
      (osiiOriginalOSHilbertComplex OS (t : Complex)
        (osiiPositiveTimeSingleVectorCLM OS m g)) =
    @inner Complex (OSHilbertSpace OS) inferInstance
      (osiiPositiveTimeSingleVectorCLM OS n f)
      (osTimeShiftHilbertOfOS (d := d) OS t ht
        (osiiPositiveTimeSingleVectorCLM OS m g))
  rw [osiiOriginalOSHilbertComplex_ofReal_single_eq_shift OS g t ht]

/-- Positive-real recovery of the Schwinger product shell, with no compact
support hypothesis on the right source. -/
theorem osiiPositiveTimeSingleSemigroupPairing_ofReal_eq_schwinger_all
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (t : ℝ) (ht : 0 < t)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m) :
    osiiPositiveTimeSingleSemigroupPairingRightCLM
        OS n m (t : ℂ) f g =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  rw [osiiPositiveTimeSingleSemigroupPairing_ofReal_eq_realShift
    OS n m t ht f]
  exact
    osiiOriginalOSPositiveTimeRealShiftPairingRightCLM_eq_schwinger
      OS n m t ht f g

end OSReconstruction
