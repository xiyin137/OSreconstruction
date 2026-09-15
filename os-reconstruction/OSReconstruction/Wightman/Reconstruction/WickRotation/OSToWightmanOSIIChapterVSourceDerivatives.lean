/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.TranslationDifferentiation
import OSReconstruction.SCV.EuclideanWeylFrechet
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceTaylor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIConfigurationTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOrderedPositiveTimeTopology




















noncomputable section

open Complex Topology
open scoped BigOperators Classical SchwartzMap LineDeriv

namespace OSReconstruction
namespace OSIIChapterV

private abbrev flattenSource
    {d n : ℕ} :
    SchwartzNPoint d n →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenCLEquivReal n (d + 1)).symm

private abbrev unflattenSource
    {d n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenCLEquivReal n (d + 1))

private abbrev unflattenSourceReal
    {d n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℝ]
      SchwartzNPoint d n :=
  (unflattenSource (d := d) (n := n)).restrictScalars ℝ

private theorem flattenSource_translate
    {d n : ℕ}
    (t : ℝ)
    (v : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    flattenSource (translateSchwartzConfiguration (t • v) f) =
      SCV.translateSchwartz
        (t • flattenCLEquivReal n (d + 1) v)
        (flattenSource f) := by
  ext u
  change
    f ((flattenCLEquivReal n (d + 1)).symm u + t • v) =
      f ((flattenCLEquivReal n (d + 1)).symm
        (u + t • flattenCLEquivReal n (d + 1) v))
  congr 1
  rw [map_add, map_smul, ContinuousLinearEquiv.symm_apply_apply]

private theorem flattenSource_translate_general
    {d n : ℕ}
    (a : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    flattenSource (translateSchwartzConfiguration a f) =
      SCV.translateSchwartz
        (flattenCLEquivReal n (d + 1) a)
        (flattenSource f) := by
  ext u
  change
    f ((flattenCLEquivReal n (d + 1)).symm u + a) =
      f ((flattenCLEquivReal n (d + 1)).symm
        (u + flattenCLEquivReal n (d + 1) a))
  congr 1
  rw [map_add, ContinuousLinearEquiv.symm_apply_apply]

private theorem unflattenSource_flattenSource
    {d n : ℕ}
    (f : SchwartzNPoint d n) :
    unflattenSource (flattenSource f) = f := by
  ext x
  simp [flattenSource, unflattenSource]

private theorem unflattenSourceReal_flattenSource
    {d n : ℕ}
    (f : SchwartzNPoint d n) :
    unflattenSourceReal (flattenSource f) = f :=
  unflattenSource_flattenSource f

private theorem flattenSource_lineDeriv
    {d n : ℕ}
    (v : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    flattenSource (∂_{v} f) =
      ∂_{flattenCLEquivReal n (d + 1) v} (flattenSource f) := by
  symm
  simpa [flattenSource] using
    (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv
      (𝕜 := ℂ)
      (m := flattenCLEquivReal n (d + 1) v)
      (g := (flattenCLEquivReal n (d + 1)).symm)
      (f := f))

private theorem flattenSource_iteratedLineDeriv
    {d n N : ℕ}
    (u : Fin N → NPointDomain d n)
    (f : SchwartzNPoint d n) :
    flattenSource (LineDeriv.iteratedLineDerivOp u f) =
      LineDeriv.iteratedLineDerivOp
        (fun i => flattenCLEquivReal n (d + 1) (u i))
        (flattenSource f) := by
  induction N generalizing f with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ N ih =>
      change
        flattenSource
            (∂_{u 0} (LineDeriv.iteratedLineDerivOp (Fin.tail u) f)) =
          ∂_{flattenCLEquivReal n (d + 1) (u 0)}
            (LineDeriv.iteratedLineDerivOp
              (fun i : Fin N =>
                flattenCLEquivReal n (d + 1) (u i.succ))
              (flattenSource f))
      rw [flattenSource_lineDeriv, ih]
      congr 2

/-- Configuration-translation difference quotients converge to the expected
Schwartz directional derivative.

The statement is made directly in the locally convex Schwartz topology.
Ordinary `HasDerivAt` statements are obtained after composing with a
continuous linear map into a normed target. -/
theorem tendsto_diffQuotient_translateSchwartzConfiguration_zero
    {d n : ℕ}
    (v : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ • (translateSchwartzConfiguration (t • v) f - f))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (∂_{v} f)) := by
  have hflat :=
    SCV.tendsto_diffQuotient_translateSchwartz_zero
      (flattenSource f)
      (flattenCLEquivReal n (d + 1) v)
  have hunflat :=
    (unflattenSourceReal (d := d) (n := n)).continuous.tendsto
      (∂_{flattenCLEquivReal n (d + 1) v} (flattenSource f)) |>.comp hflat
  convert hunflat using 1
  · funext t
    simp only [Function.comp_apply]
    rw [map_smul, map_sub, ← flattenSource_translate,
      unflattenSourceReal_flattenSource,
      unflattenSourceReal_flattenSource]
  · rw [← flattenSource_lineDeriv, unflattenSourceReal_flattenSource]

/-- A continuous functional evaluated on the configuration-translation orbit
is smooth in the full configuration displacement. -/
theorem contDiff_apply_translateSchwartzConfiguration
    {d n : ℕ}
    (T : SchwartzNPoint d n →L[ℂ] ℂ)
    (f : SchwartzNPoint d n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun a : NPointDomain d n =>
        T (translateSchwartzConfiguration a f)) := by
  let e := flattenCLEquivReal n (d + 1)
  let eCLM : NPointDomain d n →L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
    e.toContinuousLinearMap
  let Tflat :
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp unflattenSource
  let Fflat : (Fin (n * (d + 1)) → ℝ) → ℂ :=
    fun a => Tflat (SCV.translateSchwartz a (flattenSource f))
  have hfun :
      (fun a : NPointDomain d n =>
        T (translateSchwartzConfiguration a f)) =
      Fflat ∘ eCLM := by
    funext a
    simp only [Function.comp_apply, Fflat, Tflat,
      ContinuousLinearMap.comp_apply, eCLM, e]
    apply congrArg T
    calc
      translateSchwartzConfiguration a f =
          unflattenSource
            (flattenSource (translateSchwartzConfiguration a f)) :=
        (unflattenSource_flattenSource _).symm
      _ = unflattenSource
          (SCV.translateSchwartz
            (flattenCLEquivReal n (d + 1) a)
            (flattenSource f)) := by
        rw [flattenSource_translate_general]
  rw [hfun]
  exact
    (SCV.contDiff_apply_translateSchwartz
      Tflat (flattenSource f)).comp eCLM.contDiff

/-- A continuous functional on multipoint Schwartz space carries every mixed
derivative of the configuration-translation chart to the matching iterated
directional derivative of the source. -/
theorem iteratedFDeriv_apply_translateSchwartzConfiguration_zero
    {d n N : ℕ}
    (T : SchwartzNPoint d n →L[ℂ] ℂ)
    (f : SchwartzNPoint d n)
    (u : Fin N → NPointDomain d n) :
    iteratedFDeriv ℝ N
        (fun a : NPointDomain d n =>
          T (translateSchwartzConfiguration a f))
        0 u =
      T (LineDeriv.iteratedLineDerivOp u f) := by
  let e := flattenCLEquivReal n (d + 1)
  let eCLM : NPointDomain d n →L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
    e.toContinuousLinearMap
  let Tflat :
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp unflattenSource
  let Fflat : (Fin (n * (d + 1)) → ℝ) → ℂ :=
    fun a => Tflat (SCV.translateSchwartz a (flattenSource f))
  have hfun :
      (fun a : NPointDomain d n =>
        T (translateSchwartzConfiguration a f)) =
      Fflat ∘ eCLM := by
    funext a
    simp only [Function.comp_apply, Fflat, Tflat,
      ContinuousLinearMap.comp_apply, eCLM, e]
    apply congrArg T
    calc
      translateSchwartzConfiguration a f =
          unflattenSource
            (flattenSource (translateSchwartzConfiguration a f)) :=
        (unflattenSource_flattenSource _).symm
      _ = unflattenSource
          (SCV.translateSchwartz
            (flattenCLEquivReal n (d + 1) a)
            (flattenSource f)) := by
        rw [flattenSource_translate_general]
  have hsmooth :
      ContDiff ℝ (⊤ : ℕ∞) Fflat := by
    simpa [Fflat] using
      SCV.contDiff_apply_translateSchwartz
        Tflat (flattenSource f)
  have hsmoothN : ContDiff ℝ (N : ℕ) Fflat :=
    hsmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcomp :=
    eCLM.iteratedFDeriv_comp_right hsmoothN
      (0 : NPointDomain d n) (i := N) le_rfl
  rw [hfun, hcomp]
  change
    iteratedFDeriv ℝ N Fflat 0
        (fun i => eCLM (u i)) =
      T (LineDeriv.iteratedLineDerivOp u f)
  rw [SCV.iteratedFDeriv_apply_translateSchwartz]
  simp only [Tflat, ContinuousLinearMap.comp_apply]
  apply congrArg T
  calc
    unflattenSource
        (SCV.translateSchwartz 0
          (LineDeriv.iteratedLineDerivOp
            (fun i => flattenCLEquivReal n (d + 1) (u i))
            (flattenSource f))) =
        unflattenSource
          (LineDeriv.iteratedLineDerivOp
            (fun i => flattenCLEquivReal n (d + 1) (u i))
            (flattenSource f)) := by
      apply congrArg unflattenSource
      ext x
      simp
    _ = LineDeriv.iteratedLineDerivOp u f := by
      rw [← flattenSource_iteratedLineDeriv,
        unflattenSource_flattenSource]

/-- Mixed derivatives after a real-linear parameterization of configuration
displacements are obtained by applying that parameter map to every derivative
direction. -/
theorem iteratedFDeriv_apply_translateSchwartzConfiguration_clm_zero
    {d n N : ℕ}
    {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : SchwartzNPoint d n →L[ℂ] ℂ)
    (f : SchwartzNPoint d n)
    (L : P →L[ℝ] NPointDomain d n)
    (u : Fin N → P) :
    iteratedFDeriv ℝ N
        (fun x : P =>
          T (translateSchwartzConfiguration (L x) f))
        0 u =
      T (LineDeriv.iteratedLineDerivOp (fun i => L (u i)) f) := by
  let F : NPointDomain d n → ℂ :=
    fun a => T (translateSchwartzConfiguration a f)
  have hsmooth :
      ContDiff ℝ (N : ℕ) F :=
    (contDiff_apply_translateSchwartzConfiguration T f).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcomp :=
    L.iteratedFDeriv_comp_right hsmooth
      (0 : P) (i := N) le_rfl
  change iteratedFDeriv ℝ N (F ∘ L) 0 u = _
  rw [hcomp]
  simpa [F, ContinuousMultilinearMap.compContinuousLinearMap_apply] using
    (iteratedFDeriv_apply_translateSchwartzConfiguration_zero
      T f (fun i => L (u i)))

/-- Configuration translation transports topological support by the inverse
point translation. -/
theorem tsupport_translateSchwartzConfiguration_eq_preimage
    {d n : ℕ}
    (a : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    tsupport
        ((translateSchwartzConfiguration a f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) =
      (Homeomorph.addRight a) ⁻¹'
        tsupport (f : NPointDomain d n → ℂ) := by
  change
    tsupport
        ((f : NPointDomain d n → ℂ) ∘
          (Homeomorph.addRight a : NPointDomain d n → NPointDomain d n)) =
      (Homeomorph.addRight a) ⁻¹'
        tsupport (f : NPointDomain d n → ℂ)
  exact tsupport_comp_eq_preimage
    (g := (f : NPointDomain d n → ℂ))
    (Homeomorph.addRight a)

/-- The configuration direction attached to one chronological gap.

Changing gap `i` by the spacetime vector `v` translates precisely the points
strictly after `i`. -/
def chronologicalTailDirection
    {d k : ℕ}
    (i : Fin k)
    (v : SpacetimeDim d) :
    NPointDomain d (k + 1) :=
  fun j => if i.val < j.val then v else 0

/-- The source-side derivative direction for a chronological gap.

The minus sign is forced by pullback: translating points by `+v` sends a test
function to `x ↦ f (x - v)` on the affected tail. -/
def chronologicalSourceDirection
    {d k : ℕ}
    (i : Fin k)
    (v : SpacetimeDim d) :
    NPointDomain d (k + 1) :=
  -chronologicalTailDirection i v

/-- The time direction used for the real positive-time Chapter V base slice. -/
def chronologicalTimeSourceDirection
    {d k : ℕ}
    (i : Fin k) :
    NPointDomain d (k + 1) :=
  chronologicalSourceDirection i (timeShiftVec d 1)

/-- The chronological time direction indexed by the predecessor of a positive
particle number. This is the particle-number-native form used by generator
blocks, whose internal time coordinates are `Fin (n - 1)`. -/
def chronologicalTimeSourceDirectionOfPositive
    {d n : ℕ}
    (hn : 0 < n)
    (i : Fin (n - 1)) :
    NPointDomain d n :=
  _root_.cast
    (congrArg (NPointDomain d) (Nat.sub_add_cancel hn))
    (chronologicalTimeSourceDirection (d := d) i)

@[simp]
theorem chronologicalTimeSourceDirectionOfPositive_succ
    {d k : ℕ}
    (i : Fin k) :
    chronologicalTimeSourceDirectionOfPositive
        (d := d) (n := k + 1) (Nat.succ_pos k) i =
      chronologicalTimeSourceDirection (d := d) i := by
  rfl

/-- Translating a source in chronological time direction `i` changes exactly
the corresponding internal difference-time coordinate `i.succ`. -/
theorem section43DiffCoordRealCLE_chronologicalTimeSourceDirection_time
    {d k : ℕ} [NeZero d]
    (i : Fin k)
    (t : ℝ)
    (x : NPointDomain d (k + 1)) :
    section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (x + t • chronologicalTimeSourceDirection i)) =
      Function.update
        (section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x))
        i.succ
        (section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) i.succ - t) := by
  classical
  funext j
  by_cases hji : j = i.succ
  · subst j
    simp [Function.update, section43QTime, nPointTimeSpatialCLE,
      chronologicalTimeSourceDirection, chronologicalSourceDirection,
      chronologicalTailDirection, timeShiftVec]
    ring
  · have hval_ne : j.val ≠ i.val + 1 := by
      intro h
      apply hji
      ext
      simpa using h
    by_cases hj0 : j.val = 0
    · simp [Function.update, hji, section43QTime, nPointTimeSpatialCLE,
        chronologicalTimeSourceDirection, chronologicalSourceDirection,
        chronologicalTailDirection, hj0]
    · by_cases hjle : j.val ≤ i.val
      · have hprev_le : j.val - 1 ≤ i.val := by omega
        simp [Function.update, hji, section43QTime, nPointTimeSpatialCLE,
          chronologicalTimeSourceDirection, chronologicalSourceDirection,
          chronologicalTailDirection, not_lt_of_ge hjle,
          not_lt_of_ge hprev_le]
      · have hilt : i.val < j.val := by omega
        have hiprev : i.val < j.val - 1 := by omega
        have hjne0 : j ≠ 0 := by
          intro hj
          subst j
          exact hj0 rfl
        simp [Function.update, hji, section43QTime, nPointTimeSpatialCLE,
          chronologicalTimeSourceDirection, chronologicalSourceDirection,
          chronologicalTailDirection, timeShiftVec, hjne0, hilt, hiprev]

/-- A chronological time source direction is the negative coordinate basis
vector at the corresponding internal difference-time gap. -/
theorem section43DiffCoordRealCLE_chronologicalTimeSourceDirection_time_apply
    {d k : ℕ} [NeZero d]
    (i : Fin k)
    (j : Fin (k + 1)) :
    section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (chronologicalTimeSourceDirection i)) j =
      if j = i.succ then -1 else 0 := by
  have h :=
    congr_fun
      (section43DiffCoordRealCLE_chronologicalTimeSourceDirection_time
        (d := d) i 1 (0 : NPointDomain d (k + 1)))
      j
  simpa [Function.update, section43QTime, nPointTimeSpatialCLE] using h

/-- Chronological time source translations leave all spatial
difference-coordinate components unchanged. -/
theorem section43DiffCoordRealCLE_chronologicalTimeSourceDirection_spatial
    {d k : ℕ} [NeZero d]
    (i : Fin k)
    (t : ℝ)
    (x : NPointDomain d (k + 1)) :
    section43QSpatial (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (x + t • chronologicalTimeSourceDirection i)) =
      section43QSpatial (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1) x) := by
  ext p
  have hdir (j : Fin (k + 1)) :
      chronologicalTimeSourceDirection i j p.2.succ = 0 := by
    by_cases hij : i.val < j.val
    · simp [chronologicalTimeSourceDirection, chronologicalSourceDirection,
        chronologicalTailDirection, timeShiftVec, hij]
    · simp [chronologicalTimeSourceDirection, chronologicalSourceDirection,
        chronologicalTailDirection, hij]
  simp [section43QSpatial, nPointTimeSpatialCLE, hdir]

/-- Repeat one Schwartz directional derivative `r` times. -/
def iteratedSourceDirection
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) :
    ℕ → SchwartzMap E ℂ → SchwartzMap E ℂ
  | 0, f => f
  | r + 1, f => ∂_{v} (iteratedSourceDirection v r f)

@[simp] theorem iteratedSourceDirection_zero
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E)
    (f : SchwartzMap E ℂ) :
    iteratedSourceDirection v 0 f = f :=
  rfl

@[simp] theorem iteratedSourceDirection_succ
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E)
    (r : ℕ)
    (f : SchwartzMap E ℂ) :
    iteratedSourceDirection v (r + 1) f =
      ∂_{v} (iteratedSourceDirection v r f) :=
  rfl

/-- Apply the prescribed power of each directional derivative.

The recursive order is immaterial for Schwartz functions because directional
derivatives commute, but fixing an order gives a simple definitional object
for support and Taylor-coefficient proofs. -/
def sourceMultiDerivative :
    {E : Type*} →
    [NormedAddCommGroup E] → [NormedSpace ℝ E] →
    {k : ℕ} →
    (Fin k → E) →
    (Fin k → ℕ) →
    SchwartzMap E ℂ →
    SchwartzMap E ℂ
  | _, _, _, 0, _, _, f => f
  | _, _, _, k + 1, directions, α, f =>
      iteratedSourceDirection (directions 0) (α 0)
        (sourceMultiDerivative
          (fun i : Fin k => directions i.succ)
          (fun i : Fin k => α i.succ)
          f)

@[simp] theorem sourceMultiDerivative_fin_zero
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (directions : Fin 0 → E)
    (α : Fin 0 → ℕ)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative directions α f = f :=
  rfl

@[simp] theorem sourceMultiDerivative_fin_succ
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin (k + 1) → E)
    (α : Fin (k + 1) → ℕ)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative directions α f =
      iteratedSourceDirection (directions 0) (α 0)
        (sourceMultiDerivative
          (fun i : Fin k => directions i.succ)
          (fun i : Fin k => α i.succ)
          f) :=
  rfl

@[simp] theorem sourceMultiDerivative_zero
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative directions 0 f = f := by
  induction k with
  | zero =>
      exact sourceMultiDerivative_fin_zero directions 0 f
  | succ k ih =>
      rw [sourceMultiDerivative_fin_succ]
      change
        iteratedSourceDirection (directions 0) 0
            (sourceMultiDerivative
              (fun i : Fin k => directions i.succ) 0 f) =
          f
      rw [iteratedSourceDirection_zero,
        ih (fun i : Fin k => directions i.succ)]

private theorem lineDerivOp_comm_schwartz
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ)
    (v w : E) :
    ∂_{v} ((∂_{w} f : SchwartzMap E ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap E ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap E ℂ))) x =
        (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : E → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : E → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap E ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- Iterated Schwartz differentiation is the right fold of its finite
direction list. -/
theorem iteratedLineDerivOp_eq_foldr
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ}
    (u : Fin N → E)
    (f : SchwartzMap E ℂ) :
    LineDeriv.iteratedLineDerivOp u f =
      (List.ofFn u).foldr
        (fun (v : E) (g : SchwartzMap E ℂ) => ∂_{v} g) f := by
  induction N generalizing f with
  | zero =>
      rfl
  | succ N ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left, List.ofFn_succ]
      simp only [List.foldr_cons]
      rw [ih]
      congr 2

private theorem count_ofFn_eq_multiIdx
    {N k : ℕ}
    (σ : Fin N → Fin k)
    (i : Fin k) :
    (List.ofFn σ).count i = SCV.multiIdx σ i := by
  rw [List.ofFn_eq_map, List.count_eq_countP,
    List.countP_eq_length_filter, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup
    ((List.nodup_finRange N).filter _)]
  unfold SCV.multiIdx
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange,
    true_and, Function.comp_apply, beq_iff_eq, Finset.mem_filter,
    Finset.mem_univ]

private def sourceMultiIndexBlockList
    {k : ℕ}
    (α : Fin k → ℕ) :
    List (Fin k) :=
  (List.finRange k).flatMap fun i => List.replicate (α i) i

@[simp] private theorem count_sourceMultiIndexBlockList
    {k : ℕ}
    (α : Fin k → ℕ)
    (i : Fin k) :
    (sourceMultiIndexBlockList α).count i = α i := by
  classical
  simp only [sourceMultiIndexBlockList, List.count_flatMap]
  rw [← List.sum_toFinset _ (List.nodup_finRange k),
    List.toFinset_finRange]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    change List.count i (List.replicate (α j) j) = 0
    rw [List.count_replicate]
    simp [hji]
  · simp

private theorem iteratedSourceDirection_eq_foldr_replicate
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E)
    (r : ℕ)
    (f : SchwartzMap E ℂ) :
    iteratedSourceDirection v r f =
      (List.replicate r v).foldr
        (fun (w : E) (g : SchwartzMap E ℂ) => ∂_{w} g) f := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      rw [iteratedSourceDirection_succ, List.replicate_succ,
        List.foldr_cons, ih]

private theorem sourceMultiDerivative_eq_foldr_blockList
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative directions α f =
      ((sourceMultiIndexBlockList α).map directions).foldr
        (fun (v : E) (g : SchwartzMap E ℂ) => ∂_{v} g) f := by
  induction k generalizing f with
  | zero =>
      rfl
  | succ k ih =>
      rw [sourceMultiDerivative_fin_succ,
        sourceMultiIndexBlockList, List.finRange_succ,
        List.flatMap_cons, List.map_append, List.foldr_append,
        iteratedSourceDirection_eq_foldr_replicate]
      simp only [List.map_replicate]
      congr 1
      rw [ih
        (fun i : Fin k => directions i.succ)
        (fun i : Fin k => α i.succ)]
      congr 1
      simp [sourceMultiIndexBlockList, List.map_flatMap,
        List.flatMap_map, List.map_replicate]

/-- The recursive source multi-derivative agrees with the canonical
multi-index enumeration used by the Cauchy coefficient theorem. -/
theorem sourceMultiDerivative_eq_iteratedLineDerivOp_multiIndexEnumeration
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative directions α f =
      LineDeriv.iteratedLineDerivOp
        (fun j => directions (SCV.multiIndexEnumeration α j)) f := by
  let op : E → SchwartzMap E ℂ → SchwartzMap E ℂ :=
    fun v g => ∂_{v} g
  letI : LeftCommutative op :=
    ⟨fun v w g => lineDerivOp_comm_schwartz g v w⟩
  have hp :
      List.Perm
        (sourceMultiIndexBlockList α)
        (List.ofFn (SCV.multiIndexEnumeration α)) := by
    rw [List.perm_iff_count]
    intro i
    rw [count_sourceMultiIndexBlockList,
      count_ofFn_eq_multiIdx,
      SCV.multiIdx_multiIndexEnumeration]
  rw [sourceMultiDerivative_eq_foldr_blockList,
    iteratedLineDerivOp_eq_foldr]
  have hmap :
      List.ofFn
          (fun j => directions (SCV.multiIndexEnumeration α j)) =
        List.map directions
          (List.ofFn (SCV.multiIndexEnumeration α)) := by
    simpa [Function.comp_def] using
      (List.map_ofFn
        (f := SCV.multiIndexEnumeration α)
        (g := directions)).symm
  rw [hmap]
  exact List.Perm.foldr_eq (f := op) (hp.map directions) f

/-- Appended source-coordinate blocks differentiate the right block first and
then the left block, matching the recursive order of `sourceMultiDerivative`. -/
theorem sourceMultiDerivative_append
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ}
    (left : Fin p → E)
    (right : Fin q → E)
    (α : Fin p → ℕ)
    (β : Fin q → ℕ)
    (f : SchwartzMap E ℂ) :
    sourceMultiDerivative
        (Fin.addCases left right)
        (Fin.append α β) f =
      sourceMultiDerivative left α
        (sourceMultiDerivative right β f) := by
  let op : E → SchwartzMap E ℂ → SchwartzMap E ℂ :=
    fun v g => ∂_{v} g
  letI : LeftCommutative op :=
    ⟨fun v w g => lineDerivOp_comm_schwartz g v w⟩
  have hp :
      List.Perm
        (sourceMultiIndexBlockList (Fin.append α β))
        ((sourceMultiIndexBlockList α).map (Fin.castAdd q) ++
          (sourceMultiIndexBlockList β).map (Fin.natAdd p)) := by
    rw [List.perm_iff_count]
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [count_sourceMultiIndexBlockList, Fin.append_left]
      have hleft :
          List.count (Fin.castAdd q j)
              ((sourceMultiIndexBlockList α).map (Fin.castAdd q)) =
            α j := by
        rw [List.count_map_of_injective
          (sourceMultiIndexBlockList α) (Fin.castAdd q)
          (Fin.castAdd_injective p q) j,
          count_sourceMultiIndexBlockList]
      have hcross :
          List.count (Fin.castAdd q j)
              ((sourceMultiIndexBlockList β).map (Fin.natAdd p)) = 0 := by
        apply List.count_eq_zero_of_not_mem
        simp only [List.mem_map]
        rintro ⟨i, hi, hEq⟩
        have hval := congrArg Fin.val hEq
        simp at hval
        omega
      rw [List.count_append, hleft, hcross, Nat.add_zero]
    · intro j
      rw [count_sourceMultiIndexBlockList, Fin.append_right]
      have hright :
          List.count (Fin.natAdd p j)
              ((sourceMultiIndexBlockList β).map (Fin.natAdd p)) =
            β j := by
        rw [List.count_map_of_injective
          (sourceMultiIndexBlockList β) (Fin.natAdd p)
          (Fin.natAdd_injective q p) j,
          count_sourceMultiIndexBlockList]
      have hcross :
          List.count (Fin.natAdd p j)
              ((sourceMultiIndexBlockList α).map (Fin.castAdd q)) = 0 := by
        apply List.count_eq_zero_of_not_mem
        simp only [List.mem_map]
        rintro ⟨i, hi, hEq⟩
        have hval := congrArg Fin.val hEq
        simp at hval
        omega
      rw [List.count_append, hcross, zero_add, hright]
  rw [sourceMultiDerivative_eq_foldr_blockList,
    sourceMultiDerivative_eq_foldr_blockList,
    sourceMultiDerivative_eq_foldr_blockList]
  change
    List.foldr op f
        (List.map (Fin.addCases left right)
          (sourceMultiIndexBlockList (Fin.append α β))) =
      List.foldr op
        (List.foldr op f
          (List.map right (sourceMultiIndexBlockList β)))
        (List.map left (sourceMultiIndexBlockList α))
  have hpE :
      List.Perm
        (List.map (Fin.addCases left right)
          (sourceMultiIndexBlockList (Fin.append α β)))
        (List.map left (sourceMultiIndexBlockList α) ++
          List.map right (sourceMultiIndexBlockList β)) := by
    simpa [List.map_append, List.map_map, Function.comp_def] using
      hp.map (Fin.addCases left right)
  calc
    List.foldr op f
        (List.map (Fin.addCases left right)
          (sourceMultiIndexBlockList (Fin.append α β))) =
      List.foldr op f
        (List.map left (sourceMultiIndexBlockList α) ++
          List.map right (sourceMultiIndexBlockList β)) :=
      List.Perm.foldr_eq (f := op) hpE f
    _ = List.foldr op
          (List.foldr op f
            (List.map right (sourceMultiIndexBlockList β)))
          (List.map left (sourceMultiIndexBlockList α)) := by
      rw [List.foldr_append]

/-- Repeated directional derivatives do not enlarge topological support. -/
theorem tsupport_iteratedSourceDirection_subset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E)
    (r : ℕ)
    (f : SchwartzMap E ℂ) :
    tsupport
        ((iteratedSourceDirection v r f : SchwartzMap E ℂ) : E → ℂ) ⊆
      tsupport (f : E → ℂ) := by
  induction r with
  | zero =>
      exact Set.Subset.rfl
  | succ r ih =>
      exact
        (SchwartzMap.tsupport_lineDerivOp_subset
          (m := v) (f := iteratedSourceDirection v r f)).trans ih

/-- A multi-index directional derivative does not enlarge topological
support. -/
theorem tsupport_sourceMultiDerivative_subset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    tsupport
        ((sourceMultiDerivative directions α f : SchwartzMap E ℂ) : E → ℂ) ⊆
      tsupport (f : E → ℂ) := by
  induction k with
  | zero =>
      exact Set.Subset.rfl
  | succ k ih =>
      exact
        (tsupport_iteratedSourceDirection_subset
          (directions 0) (α 0)
          (sourceMultiDerivative
            (fun i : Fin k => directions i.succ)
            (fun i : Fin k => α i.succ)
            f)).trans
          (ih
            (fun i : Fin k => directions i.succ)
            (fun i : Fin k => α i.succ))

/-- Product of the coordinate factorials in a multi-index. -/
def multiFactorial
    {k : ℕ}
    (α : Fin k → ℕ) : ℕ :=
  ∏ i, (α i).factorial

/-- The normalized source Taylor coefficient `∂^α f / α!`. -/
def normalizedSourceMultiDerivative
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    SchwartzMap E ℂ :=
  ((multiFactorial α : ℕ) : ℂ)⁻¹ •
    sourceMultiDerivative directions α f

/-- Normalized source multi-differentiation as a continuous complex-linear
operator on Schwartz space. -/
noncomputable def normalizedSourceMultiDerivativeCLM
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  (((multiFactorial α : ℕ) : ℂ)⁻¹) •
    LineDeriv.iteratedLineDerivOpCLM ℂ (SchwartzMap E ℂ)
      (fun j => directions (SCV.multiIndexEnumeration α j))

@[simp]
theorem normalizedSourceMultiDerivativeCLM_apply
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    normalizedSourceMultiDerivativeCLM directions α f =
      normalizedSourceMultiDerivative directions α f := by
  simp only [normalizedSourceMultiDerivativeCLM,
    ContinuousLinearMap.smul_apply,
    LineDeriv.iteratedLineDerivOpCLM_apply,
    normalizedSourceMultiDerivative]
  rw [sourceMultiDerivative_eq_iteratedLineDerivOp_multiIndexEnumeration]

@[simp] theorem normalizedSourceMultiDerivative_zero
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (f : SchwartzMap E ℂ) :
    normalizedSourceMultiDerivative directions 0 f = f := by
  simp [normalizedSourceMultiDerivative, multiFactorial]

/-- Factorial normalization also preserves the original support. -/
theorem tsupport_normalizedSourceMultiDerivative_subset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ}
    (directions : Fin k → E)
    (α : Fin k → ℕ)
    (f : SchwartzMap E ℂ) :
    tsupport
        ((normalizedSourceMultiDerivative directions α f :
          SchwartzMap E ℂ) : E → ℂ) ⊆
      tsupport (f : E → ℂ) := by
  exact
    (tsupport_smul_subset_right
      (fun _ : E => (((multiFactorial α : ℕ) : ℂ)⁻¹))
      ((sourceMultiDerivative directions α f : SchwartzMap E ℂ) : E → ℂ)).trans
      (tsupport_sourceMultiDerivative_subset directions α f)

/-- Package normalized multi-derivatives of a positive-time source as the
source coefficient data consumed by the Chapter V Hilbert Taylor theorem. -/
def PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
    {d n k : ℕ} [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n)
    (increment : Fin k → ℂ) :
    PositiveTimeSourceCoefficientData d n k where
  coefficient α :=
    ⟨normalizedSourceMultiDerivative directions α f.1,
      (tsupport_normalizedSourceMultiDerivative_subset
        directions α f.1).trans f.2⟩
  increment := increment

@[simp] theorem PositiveTimeSourceCoefficientData.coefficient_ofNormalizedDerivatives
    {d n k : ℕ} [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin k → NPointDomain d n)
    (increment : Fin k → ℂ)
    (α : Fin k → ℕ) :
    ((PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
      f directions increment).coefficient α).1 =
      normalizedSourceMultiDerivative directions α f.1 :=
  rfl

end OSIIChapterV
end OSReconstruction
