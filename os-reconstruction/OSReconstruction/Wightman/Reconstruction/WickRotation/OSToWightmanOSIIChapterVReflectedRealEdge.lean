/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRealEdgeCauchy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger















noncomputable section

open Complex Topology
open scoped BigOperators Classical SchwartzMap LineDeriv ContDiff

namespace OSReconstruction
namespace OSIIChapterV

private theorem timeReflectionN_add
    {d n : ℕ}
    (x y : NPointDomain d n) :
    timeReflectionN d (x + y) =
      timeReflectionN d x + timeReflectionN d y := by
  ext i μ
  by_cases hμ : μ = 0
  · subst μ
    simp [timeReflectionN, timeReflection]
    ring
  · simp [timeReflectionN, timeReflection, hμ]

private theorem timeReflectionN_smul
    {d n : ℕ}
    (t : ℝ)
    (x : NPointDomain d n) :
    timeReflectionN d (t • x) =
      t • timeReflectionN d x := by
  ext i μ
  by_cases hμ : μ = 0
  · subst μ
    simp [timeReflectionN, timeReflection]
  · simp [timeReflectionN, timeReflection, hμ]

private theorem timeReflectionN_involutive
    {d n : ℕ}
    (x : NPointDomain d n) :
    timeReflectionN d (timeReflectionN d x) = x := by
  ext i μ
  by_cases hμ : μ = 0
  · subst μ
    simp [timeReflectionN, timeReflection]
  · simp [timeReflectionN, timeReflection, hμ]

/-- Separate left/right source translations are one ordinary translation of
the fixed reflected tensor product. -/
theorem osConjTensorProduct_translateSchwartzConfiguration
    {d n m : ℕ} [NeZero d]
    (a : NPointDomain d n)
    (b : NPointDomain d m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    (translateSchwartzConfiguration a f).osConjTensorProduct
        (translateSchwartzConfiguration b g) =
      translateSchwartzConfiguration
        (Fin.append (timeReflectionN d a) b)
        (f.osConjTensorProduct g) := by
  ext x
  simp only [SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply,
    translateSchwartzConfiguration_apply]
  congr 2
  · congr 1
    rw [show
      splitFirst n m (x + Fin.append (timeReflectionN d a) b) =
        splitFirst n m x + timeReflectionN d a by
      ext i
      simp [splitFirst]]
    rw [timeReflectionN_add, timeReflectionN_involutive]
  · rw [show
      splitLast n m (x + Fin.append (timeReflectionN d a) b) =
        splitLast n m x + b by
      ext i
      simp [splitLast]]

/-- Real-linear map from source-coordinate parameters to a configuration
translation. -/
def sourceParameterDisplacementCLM
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n) :
    (Fin k → ℝ) →L[ℝ] NPointDomain d n := by
  let L : (Fin k → ℝ) →ₗ[ℝ] NPointDomain d n :=
    { toFun := fun x => ∑ i, x i • directions i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro t x
        simp [smul_smul, Finset.smul_sum] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

@[simp] theorem sourceParameterDisplacementCLM_apply
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n)
    (x : Fin k → ℝ) :
    sourceParameterDisplacementCLM directions x =
      ∑ i, x i • directions i :=
  rfl

/-- The source displacement map sends the standard coordinate basis to the
corresponding source direction. -/
@[simp] theorem sourceParameterDisplacementCLM_basis
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n)
    (j : Fin k) :
    sourceParameterDisplacementCLM directions
        (fun i => if i = j then 1 else 0) =
      directions j := by
  simp [sourceParameterDisplacementCLM_apply]

/-- Simultaneous chronological source translations are the affine chart that
fixes the absolute time coordinate and subtracts parameter `i` from internal
difference-time coordinate `i.succ`. -/
theorem chronologicalSourceParameterDisplacement_diff_time_apply
    {d k : ℕ} [NeZero d]
    (u : Fin k → ℝ)
    (x : NPointDomain d (k + 1))
    (j : Fin (k + 1)) :
    section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (x + sourceParameterDisplacementCLM
            (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) u)) j =
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) j -
        Fin.cases 0 u j := by
  rw [map_add]
  change
    section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) j +
        section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (sourceParameterDisplacementCLM
              (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) u)) j =
      _
  rw [sourceParameterDisplacementCLM_apply, map_sum]
  simp only [map_smul]
  have hadd (q r : NPointDomain d (k + 1)) :
      section43QTime (d := d) (n := k + 1) (q + r) j =
        section43QTime (d := d) (n := k + 1) q j +
          section43QTime (d := d) (n := k + 1) r j := by
    simp [section43QTime]
  have hsmul (a : ℝ) (q : NPointDomain d (k + 1)) :
      section43QTime (d := d) (n := k + 1) (a • q) j =
        a * section43QTime (d := d) (n := k + 1) q j := by
    simp [section43QTime, Pi.smul_apply, smul_eq_mul]
  have hsum :
      section43QTime (d := d) (n := k + 1)
          (∑ i : Fin k, u i •
            section43DiffCoordRealCLE d (k + 1)
              (chronologicalTimeSourceDirection i)) j =
        ∑ i : Fin k, u i •
          section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (chronologicalTimeSourceDirection i)) j := by
    have hs (s : Finset (Fin k)) :
        section43QTime (d := d) (n := k + 1)
            (∑ i ∈ s, u i •
              section43DiffCoordRealCLE d (k + 1)
                (chronologicalTimeSourceDirection i)) j =
          ∑ i ∈ s, u i *
            section43QTime (d := d) (n := k + 1)
              (section43DiffCoordRealCLE d (k + 1)
                (chronologicalTimeSourceDirection i)) j := by
      induction s using Finset.induction_on with
      | empty =>
          simp [section43QTime]
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          rw [hadd, hsmul, ih]
    simpa using hs Finset.univ
  rw [hsum]
  simp_rw [section43DiffCoordRealCLE_chronologicalTimeSourceDirection_time_apply]
  refine Fin.cases ?_ (fun r => ?_) j
  · have hz (i : Fin k) : (0 : Fin (k + 1)) ≠ i.succ :=
      (Fin.succ_ne_zero i).symm
    simp [hz]
  · simp
    ring

/-- Function-valued form of the chronological source affine chart. -/
theorem chronologicalSourceParameterDisplacement_diff_time
    {d k : ℕ} [NeZero d]
    (u : Fin k → ℝ)
    (x : NPointDomain d (k + 1)) :
    section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (x + sourceParameterDisplacementCLM
            (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) u)) =
      fun j =>
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) j -
          Fin.cases 0 u j := by
  funext j
  exact chronologicalSourceParameterDisplacement_diff_time_apply u x j

/-- Simultaneous chronological source translations leave the spatial
difference-coordinate block fixed. -/
theorem chronologicalSourceParameterDisplacement_diff_spatial
    {d k : ℕ} [NeZero d]
    (u : Fin k → ℝ)
    (x : NPointDomain d (k + 1)) :
    section43QSpatial (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (x + sourceParameterDisplacementCLM
            (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i) u)) =
      section43QSpatial (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1) x) := by
  have hadd (q r : NPointDomain d (k + 1)) :
      section43QSpatial (d := d) (n := k + 1) (q + r) =
        section43QSpatial (d := d) (n := k + 1) q +
          section43QSpatial (d := d) (n := k + 1) r := by
    simp [section43QSpatial]
  have hdir (i : Fin k) (a : ℝ) :
      section43QSpatial (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1)
            (a • chronologicalTimeSourceDirection i)) = 0 := by
    have h :=
      section43DiffCoordRealCLE_chronologicalTimeSourceDirection_spatial
        (d := d) i a (0 : NPointDomain d (k + 1))
    have h' :
        section43QSpatial (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (a • chronologicalTimeSourceDirection i)) =
          section43QSpatial (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (0 : NPointDomain d (k + 1))) := by
      simpa only [zero_add] using h
    exact h'.trans (by simp [section43QSpatial])
  have hdir' (i : Fin k) (a : ℝ) :
      section43QSpatial (d := d) (n := k + 1)
          (a • section43DiffCoordRealCLE d (k + 1)
            (chronologicalTimeSourceDirection i)) = 0 := by
    rw [← map_smul]
    exact hdir i a
  have hs (s : Finset (Fin k)) :
      section43QSpatial (d := d) (n := k + 1)
          (∑ i ∈ s, u i •
            section43DiffCoordRealCLE d (k + 1)
              (chronologicalTimeSourceDirection i)) = 0 := by
    induction s using Finset.induction_on with
    | empty =>
        simp [section43QSpatial]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        rw [hadd, hdir', ih, zero_add]
  rw [map_add]
  rw [hadd]
  rw [sourceParameterDisplacementCLM_apply, map_sum]
  simp only [map_smul]
  rw [show
      section43QSpatial (d := d) (n := k + 1)
          (∑ i : Fin k, u i •
            section43DiffCoordRealCLE d (k + 1)
              (chronologicalTimeSourceDirection i)) = 0 by
        simpa using hs Finset.univ]
  exact add_zero _

/-- Combined reflected-left/right displacement of the fixed product source. -/
def reflectedSourceParameterDisplacementCLM
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n) :
    (Fin (k + k) → ℝ) →L[ℝ] NPointDomain d (n + n) := by
  let L : (Fin (k + k) → ℝ) →ₗ[ℝ] NPointDomain d (n + n) :=
    { toFun := fun x =>
        Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM directions
              (fun i => x (Fin.castAdd k i))))
          (sourceParameterDisplacementCLM directions
            (fun i => x (Fin.natAdd k i)))
      map_add' := by
        intro x y
        ext i μ
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.append_left, Pi.add_apply]
          rw [show
            (fun i => x (Fin.castAdd k i) + y (Fin.castAdd k i)) =
              (fun i => x (Fin.castAdd k i)) +
                (fun i => y (Fin.castAdd k i)) by rfl]
          rw [map_add, timeReflectionN_add, Pi.add_apply, Pi.add_apply]
        · intro j
          simp only [Fin.append_right, Pi.add_apply]
          rw [show
            (fun i => x (Fin.natAdd k i) + y (Fin.natAdd k i)) =
              (fun i => x (Fin.natAdd k i)) +
                (fun i => y (Fin.natAdd k i)) by rfl]
          rw [map_add, Pi.add_apply]
          rfl
      map_smul' := by
        intro t x
        ext i μ
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
          rw [show
            (fun i => t • x (Fin.castAdd k i)) =
              t • (fun i => x (Fin.castAdd k i)) by rfl]
          rw [map_smul, timeReflectionN_smul, Pi.smul_apply]
          rfl
        · intro j
          simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]
          rw [show
            (fun i => t • x (Fin.natAdd k i)) =
              t • (fun i => x (Fin.natAdd k i)) by rfl]
          rw [map_smul, Pi.smul_apply]
          rfl }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

/-- Fixed-right OS-conjugated tensoring is real-linear in the left source. -/
noncomputable def osConjTensorProductLeftRCLM
    {d n m : ℕ} [NeZero d]
    (g : SchwartzNPoint d m) :
    SchwartzNPoint d n →L[ℝ] SchwartzNPoint d (n + m) :=
  { toLinearMap :=
      { toFun := fun f => f.osConjTensorProduct g
        map_add' := fun f h =>
          SchwartzNPoint.osConjTensorProduct_add_left
            (d := d) f h g
        map_smul' := by
          intro t f
          simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),
            Complex.conj_ofReal] using
            (SchwartzNPoint.osConjTensorProduct_smul_left
              (d := d) (t : ℂ) f g) }
    cont := by
      have h :
          Continuous
            (fun f : SchwartzNPoint d n =>
              (f, g)) :=
        continuous_id.prodMk continuous_const
      exact
        (SchwartzNPoint.osConjTensorProduct_continuous
          (d := d) (n := n) (m := m)).comp h }

@[simp] theorem osConjTensorProductLeftRCLM_apply
    {d n m : ℕ} [NeZero d]
    (g : SchwartzNPoint d m)
    (f : SchwartzNPoint d n) :
    osConjTensorProductLeftRCLM g f =
      f.osConjTensorProduct g :=
  rfl

private noncomputable def schwartzEvalRCLM
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) :
    SchwartzMap E ℂ →L[ℝ] ℂ :=
  ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)).restrictScalars ℝ

@[simp] private theorem schwartzEvalRCLM_apply
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    (f : SchwartzMap E ℂ) :
    schwartzEvalRCLM x f = f x :=
  rfl

/-- A full-product derivative supported in the right block differentiates
only the right source. -/
theorem lineDerivOp_osConjTensorProduct_right
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (v : NPointDomain d m) :
    ∂_{Fin.append (0 : NPointDomain d n) v}
        (f.osConjTensorProduct g) =
      f.osConjTensorProduct (∂_{v} g : SchwartzNPoint d m) := by
  let w : NPointDomain d (n + m) :=
    Fin.append (0 : NPointDomain d n) v
  let R :=
    (osConjTensorProductRightCLM
      (d := d) (n := n) (m := m) f).restrictScalars ℝ
  have hfull :=
    tendsto_diffQuotient_translateSchwartzConfiguration_zero
      w (f.osConjTensorProduct g)
  have hright :=
    (R.continuous.tendsto (∂_{v} g)).comp
      (tendsto_diffQuotient_translateSchwartzConfiguration_zero v g)
  have hquot :
      ∀ t : ℝ,
        R (t⁻¹ •
            (translateSchwartzConfiguration (t • v) g - g)) =
          t⁻¹ •
            (translateSchwartzConfiguration (t • w)
                (f.osConjTensorProduct g) -
              f.osConjTensorProduct g) := by
    intro t
    rw [map_smul, map_sub]
    change
      t⁻¹ •
          (f.osConjTensorProduct
              (translateSchwartzConfiguration (t • v) g) -
            f.osConjTensorProduct g) =
        _
    congr 1
    have hdir :
        t • w =
          Fin.append
            (timeReflectionN d (0 : NPointDomain d n))
            (t • v) := by
      ext i μ
      refine Fin.addCases ?_ ?_ i
      · intro j
        by_cases hμ : μ = 0
        · subst μ
          simp [w, timeReflectionN, timeReflection]
        · simp [w, timeReflectionN, timeReflection, hμ]
      · intro j
        simp [w]
    rw [hdir]
    exact congrArg
      (fun h : SchwartzNPoint d (n + m) =>
        h - f.osConjTensorProduct g)
      (by
        have hzero :
            translateSchwartzConfiguration
                (0 : NPointDomain d n) f = f := by
          ext x
          simp [translateSchwartzConfiguration_apply]
        calc
          f.osConjTensorProduct
                (translateSchwartzConfiguration (t • v) g) =
              (translateSchwartzConfiguration
                  (0 : NPointDomain d n) f).osConjTensorProduct
                (translateSchwartzConfiguration (t • v) g) := by
            rw [hzero]
          _ = _ :=
            osConjTensorProduct_translateSchwartzConfiguration
              (0 : NPointDomain d n) (t • v) f g)
  have hright' :
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (translateSchwartzConfiguration (t • w)
                (f.osConjTensorProduct g) -
              f.osConjTensorProduct g))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (𝓝 (f.osConjTensorProduct (∂_{v} g : SchwartzNPoint d m))) := by
    simpa [R, Function.comp_def] using
      hright.congr' (Filter.Eventually.of_forall hquot)
  ext x
  let ev := schwartzEvalRCLM x
  have hfull_x :=
    (ev.continuous.tendsto (∂_{w} (f.osConjTensorProduct g))).comp
      hfull
  have hright_x :=
    (ev.continuous.tendsto
      (f.osConjTensorProduct (∂_{v} g : SchwartzNPoint d m))).comp
      hright'
  simpa [ev, w] using tendsto_nhds_unique hfull_x hright_x

/-- A full-product derivative supported in the reflected left block
differentiates only the left source. -/
theorem lineDerivOp_osConjTensorProduct_left
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (v : NPointDomain d n) :
    ∂_{Fin.append (timeReflectionN d v) (0 : NPointDomain d m)}
        (f.osConjTensorProduct g) =
      (∂_{v} f : SchwartzNPoint d n).osConjTensorProduct g := by
  let w : NPointDomain d (n + m) :=
    Fin.append (timeReflectionN d v) (0 : NPointDomain d m)
  let L := osConjTensorProductLeftRCLM
    (d := d) (n := n) (m := m) g
  have hfull :=
    tendsto_diffQuotient_translateSchwartzConfiguration_zero
      w (f.osConjTensorProduct g)
  have hleft :=
    (L.continuous.tendsto (∂_{v} f)).comp
      (tendsto_diffQuotient_translateSchwartzConfiguration_zero v f)
  have hquot :
      ∀ t : ℝ,
        L (t⁻¹ •
            (translateSchwartzConfiguration (t • v) f - f)) =
          t⁻¹ •
            (translateSchwartzConfiguration (t • w)
                (f.osConjTensorProduct g) -
              f.osConjTensorProduct g) := by
    intro t
    rw [map_smul, map_sub]
    change
      t⁻¹ •
          ((translateSchwartzConfiguration (t • v) f).osConjTensorProduct g -
            f.osConjTensorProduct g) =
        _
    congr 1
    have hdir :
        t • w =
          Fin.append
            (timeReflectionN d (t • v))
            (0 : NPointDomain d m) := by
      ext i μ
      refine Fin.addCases ?_ ?_ i
      · intro j
        by_cases hμ : μ = 0
        · subst μ
          simp [w, timeReflectionN, timeReflection]
        · simp [w, timeReflectionN, timeReflection, hμ]
      · intro j
        simp [w]
    rw [hdir]
    exact congrArg
      (fun h : SchwartzNPoint d (n + m) =>
        h - f.osConjTensorProduct g)
      (by
        have hzero :
            translateSchwartzConfiguration
                (0 : NPointDomain d m) g = g := by
          ext x
          simp [translateSchwartzConfiguration_apply]
        calc
          (translateSchwartzConfiguration
                (t • v) f).osConjTensorProduct g =
              (translateSchwartzConfiguration
                (t • v) f).osConjTensorProduct
                (translateSchwartzConfiguration
                  (0 : NPointDomain d m) g) := by
            rw [hzero]
          _ = _ :=
            osConjTensorProduct_translateSchwartzConfiguration
              (t • v) (0 : NPointDomain d m) f g)
  have hleft' :
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (translateSchwartzConfiguration (t • w)
                (f.osConjTensorProduct g) -
              f.osConjTensorProduct g))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (𝓝 ((∂_{v} f : SchwartzNPoint d n).osConjTensorProduct g)) := by
    simpa [L, Function.comp_def] using
      hleft.congr' (Filter.Eventually.of_forall hquot)
  ext x
  let ev := schwartzEvalRCLM x
  have hfull_x :=
    (ev.continuous.tendsto (∂_{w} (f.osConjTensorProduct g))).comp
      hfull
  have hleft_x :=
    (ev.continuous.tendsto
      ((∂_{v} f : SchwartzNPoint d n).osConjTensorProduct g)).comp
      hleft'
  simpa [ev, w] using tendsto_nhds_unique hfull_x hleft_x

/-- Repeated derivatives supported in the right block act only on the right
source. -/
theorem iteratedSourceDirection_osConjTensorProduct_right
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (v : NPointDomain d m)
    (r : ℕ) :
    iteratedSourceDirection
        (Fin.append (0 : NPointDomain d n) v) r
        (f.osConjTensorProduct g) =
      f.osConjTensorProduct (iteratedSourceDirection v r g) := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      rw [iteratedSourceDirection_succ, iteratedSourceDirection_succ, ih,
        lineDerivOp_osConjTensorProduct_right]

/-- Repeated derivatives supported in the reflected left block act only on
the left source. -/
theorem iteratedSourceDirection_osConjTensorProduct_left
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (v : NPointDomain d n)
    (r : ℕ) :
    iteratedSourceDirection
      (Fin.append (timeReflectionN d v) (0 : NPointDomain d m)) r
        (f.osConjTensorProduct g) =
      SchwartzNPoint.osConjTensorProduct
        (iteratedSourceDirection v r f : SchwartzNPoint d n) g := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      rw [iteratedSourceDirection_succ, iteratedSourceDirection_succ, ih,
        lineDerivOp_osConjTensorProduct_left]

/-- A right-block source multi-derivative acts only on the right source. -/
theorem sourceMultiDerivative_osConjTensorProduct_right
    {d n m k : ℕ} [NeZero d]
    (directions : Fin k → NPointDomain d m)
    (β : Fin k → ℕ)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    sourceMultiDerivative
        (fun i =>
          Fin.append (0 : NPointDomain d n) (directions i))
        β (f.osConjTensorProduct g) =
      f.osConjTensorProduct
        (sourceMultiDerivative directions β g) := by
  induction k generalizing f g with
  | zero =>
      rfl
  | succ k ih =>
      rw [sourceMultiDerivative_fin_succ,
        sourceMultiDerivative_fin_succ]
      rw [ih
        (fun i : Fin k => directions i.succ)
        (fun i : Fin k => β i.succ)]
      exact
        iteratedSourceDirection_osConjTensorProduct_right
          f
          (sourceMultiDerivative
            (fun i : Fin k => directions i.succ)
            (fun i : Fin k => β i.succ) g)
          (directions 0) (β 0)

/-- A reflected-left source multi-derivative acts only on the left source. -/
theorem sourceMultiDerivative_osConjTensorProduct_left
    {d n m k : ℕ} [NeZero d]
    (directions : Fin k → NPointDomain d n)
    (α : Fin k → ℕ)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    sourceMultiDerivative
        (fun i =>
          Fin.append (timeReflectionN d (directions i))
            (0 : NPointDomain d m))
        α (f.osConjTensorProduct g) =
      SchwartzNPoint.osConjTensorProduct
        (sourceMultiDerivative directions α f : SchwartzNPoint d n) g := by
  induction k generalizing f g with
  | zero =>
      rfl
  | succ k ih =>
      rw [sourceMultiDerivative_fin_succ,
        sourceMultiDerivative_fin_succ]
      rw [ih
        (fun i : Fin k => directions i.succ)
        (fun i : Fin k => α i.succ)]
      exact
        iteratedSourceDirection_osConjTensorProduct_left
          (sourceMultiDerivative
            (fun i : Fin k => directions i.succ)
            (fun i : Fin k => α i.succ) f)
          g (directions 0) (α 0)

/-- Directions on the reflected product source: reflected directions occupy
the left block and ordinary directions occupy the right block. -/
def reflectedProductSourceDirections
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n) :
    Fin (k + k) → NPointDomain d (n + n) :=
  Fin.addCases
    (fun i =>
      Fin.append (timeReflectionN d (directions i))
        (0 : NPointDomain d n))
    (fun i =>
      Fin.append (0 : NPointDomain d n) (directions i))

/-- The reflected displacement map sends each standard coordinate basis
vector to the matching left- or right-block source direction. -/
@[simp] theorem reflectedSourceParameterDisplacementCLM_basis
    {d n k : ℕ}
    (directions : Fin k → NPointDomain d n)
    (j : Fin (k + k)) :
    reflectedSourceParameterDisplacementCLM directions
        (fun i => if i = j then 1 else 0) =
      reflectedProductSourceDirections directions j := by
  unfold reflectedProductSourceDirections
  refine Fin.addCases (motive := fun j =>
    reflectedSourceParameterDisplacementCLM directions
        (fun i => if i = j then 1 else 0) =
      Fin.addCases
        (fun i =>
          Fin.append (timeReflectionN d (directions i))
            (0 : NPointDomain d n))
        (fun i =>
          Fin.append (0 : NPointDomain d n) (directions i))
        j) ?_ ?_ j
  · intro l
    simp [reflectedSourceParameterDisplacementCLM,
      sourceParameterDisplacementCLM_apply]
    have hcross :
        (∑ x : Fin k,
          if x.addNat k = Fin.castAdd k l then directions x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [if_neg]
      intro heq
      have hval := congrArg Fin.val heq
      simp at hval
      omega
    rw [hcross]
  · intro r
    simp [reflectedSourceParameterDisplacementCLM,
      sourceParameterDisplacementCLM_apply]
    have hcross :
        (∑ x : Fin k,
          if Fin.castAdd k x = r.addNat k then directions x else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [if_neg]
      intro heq
      have hval := congrArg Fin.val heq
      simp at hval
      omega
    rw [hcross]
    have hr : r.addNat k = Fin.natAdd k r := by
      ext
      simp [Nat.add_comm]
    rw [hr, Fin.addCases_right]
    congr 1
    ext i μ
    by_cases hμ : μ = 0
    · subst μ
      simp [timeReflectionN, timeReflection]
    · simp [timeReflectionN, timeReflection, hμ]

/-- The appended reflected-left/right source multi-derivative factors as the
OS-conjugated tensor product of the separate source multi-derivatives. -/
theorem sourceMultiDerivative_reflectedProduct_append
    {d n k : ℕ} [NeZero d]
    (directions : Fin k → NPointDomain d n)
    (α β : Fin k → ℕ)
    (f g : SchwartzNPoint d n) :
    sourceMultiDerivative
        (reflectedProductSourceDirections directions)
        (Fin.append α β)
        (f.osConjTensorProduct g) =
      SchwartzNPoint.osConjTensorProduct
        (sourceMultiDerivative directions α f : SchwartzNPoint d n)
        (sourceMultiDerivative directions β g :
          SchwartzNPoint d n) := by
  unfold reflectedProductSourceDirections
  rw [sourceMultiDerivative_append,
    sourceMultiDerivative_osConjTensorProduct_right,
    sourceMultiDerivative_osConjTensorProduct_left]

/-- Canonically enumerated mixed derivatives of the reflected product source
factor into the corresponding left and right source multi-derivatives. -/
theorem iteratedLineDerivOp_reflectedProduct_multiIndexEnumeration
    {d n k : ℕ} [NeZero d]
    (directions : Fin k → NPointDomain d n)
    (α β : Fin k → ℕ)
    (f g : SchwartzNPoint d n) :
    LineDeriv.iteratedLineDerivOp
        (fun j =>
          reflectedProductSourceDirections directions
            (SCV.multiIndexEnumeration (Fin.append α β) j))
        (f.osConjTensorProduct g) =
      SchwartzNPoint.osConjTensorProduct
        (sourceMultiDerivative directions α f : SchwartzNPoint d n)
        (sourceMultiDerivative directions β g :
          SchwartzNPoint d n) := by
  rw [← sourceMultiDerivative_eq_iteratedLineDerivOp_multiIndexEnumeration]
  exact sourceMultiDerivative_reflectedProduct_append
    directions α β f g

/-- Coordinate factorial products split across appended multi-indices. -/
@[simp] theorem multiFactorial_append
    {p q : ℕ}
    (α : Fin p → ℕ)
    (β : Fin q → ℕ) :
    multiFactorial (Fin.append α β) =
      multiFactorial α * multiFactorial β := by
  simp [multiFactorial, Fin.prod_univ_add]

/-- The normalized mixed derivative of a reflected product is the reflected
product of the separately normalized source derivatives. -/
theorem normalizedSourceMultiDerivative_reflectedProduct_append
    {d n k : ℕ} [NeZero d]
    (directions : Fin k → NPointDomain d n)
    (α β : Fin k → ℕ)
    (f g : SchwartzNPoint d n) :
    normalizedSourceMultiDerivative
        (reflectedProductSourceDirections directions)
        (Fin.append α β)
        (f.osConjTensorProduct g) =
      SchwartzNPoint.osConjTensorProduct
        (normalizedSourceMultiDerivative directions α f :
          SchwartzNPoint d n)
        (normalizedSourceMultiDerivative directions β g :
          SchwartzNPoint d n) := by
  rw [normalizedSourceMultiDerivative,
    normalizedSourceMultiDerivative,
    normalizedSourceMultiDerivative,
    sourceMultiDerivative_reflectedProduct_append,
    multiFactorial_append,
    SchwartzNPoint.osConjTensorProduct_smul_left,
    SchwartzNPoint.osConjTensorProduct_smul_right]
  simp [Nat.cast_mul, mul_inv_rev, mul_comm, smul_smul]

/-- The canonical real mixed derivative of a reflected product translation is
the local functional applied to the separate left/right source derivatives. -/
theorem iteratedFDeriv_reflectedProduct_zero
    {d n k : ℕ} [NeZero d]
    (T : SchwartzNPoint d (n + n) →L[ℂ] ℂ)
    (directions : Fin k → NPointDomain d n)
    (α β : Fin k → ℕ)
    (f g : SchwartzNPoint d n) :
    iteratedFDeriv ℝ (∑ i, (Fin.append α β) i)
        (fun x : Fin (k + k) → ℝ =>
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions x)
            (f.osConjTensorProduct g)))
        0
        (fun j i =>
          if i = SCV.multiIndexEnumeration (Fin.append α β) j then 1 else 0) =
      T (SchwartzNPoint.osConjTensorProduct
        (sourceMultiDerivative directions α f : SchwartzNPoint d n)
        (sourceMultiDerivative directions β g : SchwartzNPoint d n)) := by
  rw [iteratedFDeriv_apply_translateSchwartzConfiguration_clm_zero]
  simp only [reflectedSourceParameterDisplacementCLM_basis]
  rw [iteratedLineDerivOp_reflectedProduct_multiIndexEnumeration]

/-- A local scalar real-edge identity converts the Cauchy coefficient for an
appended multi-index into the local functional evaluated on the normalized
left/right source derivatives. -/
theorem cauchyCoeffPolydisc_eq_localReflectedProduct_normalized
    {d n k : ℕ} [NeZero d]
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ (Fin ((k + 1) + (k + 1)) → ℂ))
    (T : SchwartzNPoint d (n + n) →L[ℂ] ℂ)
    (directions : Fin (k + 1) → NPointDomain d n)
    (f g : SchwartzNPoint d n)
    {scalar : (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
    {center : Fin ((k + 1) + (k + 1)) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin ((k + 1) + (k + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc center (fun _ => R) ⊆ U)
    (hscalar : DifferentiableOn ℂ scalar U)
    (hreal :
      (fun x : Fin ((k + 1) + (k + 1)) → ℝ =>
        realAffineSlice scalar center x) =ᶠ[𝓝 0]
        (fun x =>
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions x)
            (f.osConjTensorProduct g))))
    (α β : Fin (k + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc scalar center (fun _ => R)
        (@Fin.append (k + 1) (k + 1) ℕ α β) =
      T (SchwartzNPoint.osConjTensorProduct
        (normalizedSourceMultiDerivative directions α f :
          SchwartzNPoint d n)
        (normalizedSourceMultiDerivative directions β g :
          SchwartzNPoint d n)) := by
  let γ : Fin ((k + 1) + (k + 1)) → ℕ :=
    @Fin.append (k + 1) (k + 1) ℕ α β
  change
    SCV.cauchyCoeffPolydisc scalar center (fun _ => R) γ =
      _
  have hcauchy :=
    SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
      hR hU hRU hscalar γ
  have hcenter : center ∈ U :=
    hRU (SCV.center_mem_closedPolydisc (fun _ => hR.le))
  have hderiv :=
    iteratedFDeriv_eq_realEdge_iteratedFDeriv
      hTowerC hTowerPi hU hcenter hscalar hreal
      (fun j (i : Fin ((k + 1) + (k + 1))) =>
        if i = SCV.multiIndexEnumeration γ j then 1 else 0)
  calc
    SCV.cauchyCoeffPolydisc scalar center (fun _ => R) γ =
        (((((∏ i,
          (γ i).factorial : ℕ) : ℂ))⁻¹)) •
          iteratedFDeriv ℂ
            (∑ i, γ i)
            scalar center
            (fun j i =>
              if i = SCV.multiIndexEnumeration γ j then 1 else 0) := by
      simpa only using hcauchy
    _ = (((((∏ i,
          (γ i).factorial : ℕ) : ℂ))⁻¹)) •
        iteratedFDeriv ℝ
          (∑ i, γ i)
          (fun x =>
            T (translateSchwartzConfiguration
              (reflectedSourceParameterDisplacementCLM directions x)
              (f.osConjTensorProduct g)))
          0
          (fun j i =>
              if i = SCV.multiIndexEnumeration γ j then 1 else 0) := by
      congr 1
      convert hderiv using 1
      congr 1
      funext j i
      split <;> simp_all
    _ = (((multiFactorial
          (@Fin.append (k + 1) (k + 1) ℕ α β) : ℕ) : ℂ)⁻¹) •
        T (SchwartzNPoint.osConjTensorProduct
          (sourceMultiDerivative directions α f : SchwartzNPoint d n)
          (sourceMultiDerivative directions β g : SchwartzNPoint d n)) := by
      dsimp [γ]
      rw [iteratedFDeriv_reflectedProduct_zero]
      rfl
    _ = T (SchwartzNPoint.osConjTensorProduct
          (normalizedSourceMultiDerivative directions α f :
            SchwartzNPoint d n)
          (normalizedSourceMultiDerivative directions β g :
            SchwartzNPoint d n)) := by
      rw [← T.map_smul,
        ← sourceMultiDerivative_reflectedProduct_append]
      change
        T (normalizedSourceMultiDerivative
          (reflectedProductSourceDirections directions)
          (@Fin.append (k + 1) (k + 1) ℕ α β)
          (f.osConjTensorProduct g)) = _
      rw [normalizedSourceMultiDerivative_reflectedProduct_append]

end OSIIChapterV
end OSReconstruction
