/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.SCV.IdentityTheorem
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric



















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

private theorem eqOn_rightHalfPlane_of_positiveReal
    (f g : Complex -> Complex)
    (hf : DifferentiableOn Complex f {z : Complex | 0 < z.re})
    (hg : DifferentiableOn Complex g {z : Complex | 0 < z.re})
    (hreal : forall t : Real, 0 < t -> f (t : Complex) = g (t : Complex)) :
    Set.EqOn f g {z : Complex | 0 < z.re} := by
  let U : Set Complex := {z : Complex | 0 < z.re}
  have hU_open : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hU_convex : Convex Real U := convex_halfSpace_re_gt 0
  have hU_connected : IsConnected U :=
    ⟨⟨1, by simp [U]⟩, hU_convex.isPreconnected⟩
  have hfreq : ∃ᶠ z in nhdsWithin (1 : Complex) ({(1 : Complex)}ᶜ),
      f z = g z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1V, hV_sub⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV_open 1 h1V
    let eps : Real := r / 2
    have heps : 0 < eps := half_pos hr
    have heps_lt : eps < r := by
      dsimp [eps]
      linarith
    have hmem : ((1 + eps : Real) : Complex) ∈ V := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      norm_num
      simpa [Real.norm_eq_abs, abs_of_pos heps] using heps_lt
    have hne : ((1 + eps : Real) : Complex) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
      linarith
    exact hV_sub ⟨hmem, hne⟩ (hreal (1 + eps) (by linarith))
  exact identity_theorem_connected hU_open hU_connected f g
    hf hg 1 (by simp [U]) hfreq

variable {d : Nat} [NeZero d]

/-- On the positive real axis, the original-OS spectral continuation is the
nonnegative functional-calculus power of its time-one contraction. -/
private theorem originalOSHilbertComplex_ofReal_eq_nnrpow
    (OS : OsterwalderSchraderAxioms d)
    (t : Real) (ht : 0 < t) :
    osiiOriginalOSHilbertComplex OS (t : Complex) =
      CFC.nnrpow
        (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
        (Real.toNNReal t) := by
  simpa [osiiOriginalOSHilbertComplex] using
    (ContinuousLinearMap.spectralSemigroupComplex_ofReal_eq_nnrpow
      (A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (hA := osTimeShiftHilbertOfOS_isSelfAdjoint (d := d) OS 1 one_pos)
      (hA_nonneg := osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbertOfOS_subset_Icc
        (d := d) OS 1 one_pos)
      (t := t) ht)

private theorem originalOSHilbertComplex_ofReal_isSelfAdjoint
    (OS : OsterwalderSchraderAxioms d)
    (t : Real) (ht : 0 < t) :
    IsSelfAdjoint (osiiOriginalOSHilbertComplex OS (t : Complex)) := by
  rw [originalOSHilbertComplex_ofReal_eq_nnrpow OS t ht]
  exact
    (CFC.nnrpow_nonneg
      (a := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
      (x := Real.toNNReal t)).isSelfAdjoint

private theorem originalOSHilbertComplex_ofReal_add
    (OS : OsterwalderSchraderAxioms d)
    (s t : Real) (hs : 0 < s) (ht : 0 < t) :
    osiiOriginalOSHilbertComplex OS ((s + t : Real) : Complex) =
      (osiiOriginalOSHilbertComplex OS (s : Complex)).comp
        (osiiOriginalOSHilbertComplex OS (t : Complex)) := by
  rw [originalOSHilbertComplex_ofReal_eq_nnrpow OS (s + t)
    (add_pos hs ht)]
  rw [originalOSHilbertComplex_ofReal_eq_nnrpow OS s hs]
  rw [originalOSHilbertComplex_ofReal_eq_nnrpow OS t ht]
  have hs' : (0 : NNReal) < Real.toNNReal s := Real.toNNReal_pos.mpr hs
  have ht' : (0 : NNReal) < Real.toNNReal t := Real.toNNReal_pos.mpr ht
  simpa [show (HMul.hMul :
      (OSHilbertSpace OS →L[Complex] OSHilbertSpace OS) → _ → _) =
      ContinuousLinearMap.comp from rfl,
    Real.toNNReal_of_nonneg hs.le,
    Real.toNNReal_of_nonneg ht.le,
    Real.toNNReal_add hs.le ht.le,
    Real.toNNReal_of_nonneg (add_nonneg hs.le ht.le)] using
      (CFC.nnrpow_add
        (a := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
        hs' ht')

/-- Complex conjugation gives the Hilbert adjoint of the genuine original-OS
spectral semigroup, without an arity-growth hypothesis. -/
theorem osiiOriginalOSHilbertComplex_adjoint
    (OS : OsterwalderSchraderAxioms d)
    (z : Complex) (hz : 0 < z.re) :
    (osiiOriginalOSHilbertComplex OS z).adjoint =
      osiiOriginalOSHilbertComplex OS (star z) := by
  let T := fun w : Complex => osiiOriginalOSHilbertComplex OS w
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff (T (star z)) (T z)).2
  intro x y
  let f : Complex -> Complex := fun w =>
    @inner Complex (OSHilbertSpace OS) _ x (T w y)
  let g : Complex -> Complex := fun w =>
    @inner Complex (OSHilbertSpace OS) _ (T (star w) x) y
  have hf : DifferentiableOn Complex f {w : Complex | 0 < w.re} := by
    simpa [f, T] using
      differentiableOn_osiiOriginalOSHilbertComplex_inner OS x y
  have hg : DifferentiableOn Complex g {w : Complex | 0 < w.re} := by
    intro w hw
    have hstar_mem : 0 < (star w).re := by simpa using hw
    have hh : DifferentiableAt Complex
        (fun u => @inner Complex (OSHilbertSpace OS) _ y (T u x))
        (star w) :=
      (differentiableOn_osiiOriginalOSHilbertComplex_inner OS y x
        (star w) hstar_mem).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          hstar_mem)
    have hcc := DifferentiableAt.conj_conj
      (𝕜 := Complex)
      (f := fun u => @inner Complex (OSHilbertSpace OS) _ y (T u x))
      (x := star w) hh
    simpa [g, T, Function.comp_def, inner_conj_symm] using
      hcc.differentiableWithinAt
  have hreal : forall t : Real, 0 < t ->
      f (t : Complex) = g (t : Complex) := by
    intro t ht
    have hself := originalOSHilbertComplex_ofReal_isSelfAdjoint OS t ht
    simpa [f, g, T] using (hself.isSymmetric x y).symm
  have heq := eqOn_rightHalfPlane_of_positiveReal f g hf hg hreal hz
  simpa [f, g, T] using heq.symm

private theorem originalOSHilbertComplex_add_ofReal_left
    (OS : OsterwalderSchraderAxioms d)
    (t : Real) (ht : 0 < t)
    (z : Complex) (hz : 0 < z.re) :
    osiiOriginalOSHilbertComplex OS ((t : Complex) + z) =
      (osiiOriginalOSHilbertComplex OS (t : Complex)).comp
        (osiiOriginalOSHilbertComplex OS z) := by
  let T := fun w : Complex => osiiOriginalOSHilbertComplex OS w
  ext y
  apply ext_inner_left Complex
  intro x
  let f : Complex -> Complex := fun w =>
    @inner Complex (OSHilbertSpace OS) _ x (T ((t : Complex) + w) y)
  let g : Complex -> Complex := fun w =>
    @inner Complex (OSHilbertSpace OS) _ x (T (t : Complex) (T w y))
  have hf : DifferentiableOn Complex f {w : Complex | 0 < w.re} := by
    exact
      (differentiableOn_osiiOriginalOSHilbertComplex_inner OS x y).comp
        ((differentiable_const (c := (t : Complex))).add
          differentiable_id).differentiableOn
        (fun w hw => by
          change 0 < w.re at hw
          change 0 < ((t : Complex) + w).re
          simp only [add_re, ofReal_re]
          linarith)
  have hself := originalOSHilbertComplex_ofReal_isSelfAdjoint OS t ht
  have hg : DifferentiableOn Complex g {w : Complex | 0 < w.re} := by
    have hbase :=
      differentiableOn_osiiOriginalOSHilbertComplex_inner OS
        (T (t : Complex) x) y
    exact hbase.congr (fun w hw => by
      simpa [g, T] using (hself.isSymmetric x (T w y)).symm)
  have hreal : forall s : Real, 0 < s ->
      f (s : Complex) = g (s : Complex) := by
    intro s hs
    have hcomp := originalOSHilbertComplex_ofReal_add OS t s ht hs
    have happ := congrArg
      (fun L : OSHilbertSpace OS →L[Complex] OSHilbertSpace OS =>
        @inner Complex (OSHilbertSpace OS) _ x (L y)) hcomp
    simpa [f, g, T, ContinuousLinearMap.comp_apply] using happ
  exact eqOn_rightHalfPlane_of_positiveReal f g hf hg hreal hz

/-- The original-OS complex spectral semigroup obeys the full right-half-plane
semigroup law without the legacy growth condition. -/
theorem osiiOriginalOSHilbertComplex_add
    (OS : OsterwalderSchraderAxioms d)
    (z w : Complex) (hz : 0 < z.re) (hw : 0 < w.re) :
    osiiOriginalOSHilbertComplex OS (z + w) =
      (osiiOriginalOSHilbertComplex OS z).comp
        (osiiOriginalOSHilbertComplex OS w) := by
  let T := fun u : Complex => osiiOriginalOSHilbertComplex OS u
  ext y
  apply ext_inner_left Complex
  intro x
  let f : Complex -> Complex := fun u =>
    @inner Complex (OSHilbertSpace OS) _ x (T (u + w) y)
  let g : Complex -> Complex := fun u =>
    @inner Complex (OSHilbertSpace OS) _ x (T u (T w y))
  have hf : DifferentiableOn Complex f {u : Complex | 0 < u.re} := by
    exact
      (differentiableOn_osiiOriginalOSHilbertComplex_inner OS x y).comp
        (differentiable_id.add (differentiable_const (c := w))
          ).differentiableOn
        (fun u hu => by
          change 0 < u.re at hu
          change 0 < (u + w).re
          simp only [add_re]
          linarith)
  have hg : DifferentiableOn Complex g {u : Complex | 0 < u.re} := by
    simpa [g, T] using
      differentiableOn_osiiOriginalOSHilbertComplex_inner OS x (T w y)
  have hreal : forall t : Real, 0 < t ->
      f (t : Complex) = g (t : Complex) := by
    intro t ht
    have hcomp := originalOSHilbertComplex_add_ofReal_left OS t ht w hw
    have happ := congrArg
      (fun L : OSHilbertSpace OS →L[Complex] OSHilbertSpace OS =>
        @inner Complex (OSHilbertSpace OS) _ x (L y)) hcomp
    simpa [f, g, T, ContinuousLinearMap.comp_apply] using happ
  exact eqOn_rightHalfPlane_of_positiveReal f g hf hg hreal hz

/-- The genuine original-OS complex spectral semigroup is a contraction on
the whole right half-plane, with no linear-growth hypothesis. -/
theorem osiiOriginalOSHilbertComplex_norm_le_one
    (OS : OsterwalderSchraderAxioms d)
    (z : Complex) (hz : 0 < z.re) :
    ‖osiiOriginalOSHilbertComplex OS z‖ <= 1 := by
  let T := fun u : Complex => osiiOriginalOSHilbertComplex OS u
  have hstar_re : 0 < (star z).re := by simpa using hz
  have hsum : star z + z = ((2 * z.re : Real) : Complex) := by
    apply Complex.ext
    · simp
      ring
    · simp
  have hproduct :
      (T z).adjoint.comp (T z) =
        T ((2 * z.re : Real) : Complex) := by
    calc
      (T z).adjoint.comp (T z) = (T (star z)).comp (T z) := by
        rw [osiiOriginalOSHilbertComplex_adjoint OS z hz]
      _ = T (star z + z) :=
        (osiiOriginalOSHilbertComplex_add OS (star z) z hstar_re hz).symm
      _ = T ((2 * z.re : Real) : Complex) := by rw [hsum]
  have htwo_re : 0 < 2 * z.re := by positivity
  have hreal_norm :
      ‖T ((2 * z.re : Real) : Complex)‖ <= 1 := by
    rw [show T ((2 * z.re : Real) : Complex) =
        CFC.nnrpow
          (osTimeShiftHilbertOfOS (d := d) OS 1 one_pos)
          (Real.toNNReal (2 * z.re)) by
      exact originalOSHilbertComplex_ofReal_eq_nnrpow OS (2 * z.re) htwo_re]
    let A := osTimeShiftHilbertOfOS (d := d) OS 1 one_pos
    have hA_nonneg : 0 <= A :=
      osTimeShiftHilbertOfOS_nonneg (d := d) OS 1 one_pos
    have hnormpow :
        ‖CFC.nnrpow A (Real.toNNReal (2 * z.re))‖ =
          ‖A‖ ^ ((Real.toNNReal (2 * z.re) : NNReal) : Real) := by
      simpa only [CFC.nnrpow_eq_pow] using
        CFC.norm_nnrpow A (Real.toNNReal_pos.mpr htwo_re) hA_nonneg
    rw [hnormpow]
    exact Real.rpow_le_one
      (norm_nonneg A)
      (osTimeShiftHilbertOfOS_norm_le_one (d := d) OS 1 one_pos)
      (Real.toNNReal (2 * z.re)).coe_nonneg
  have hsq : ‖T z‖ * ‖T z‖ <= 1 := by
    rw [← ContinuousLinearMap.norm_adjoint_comp_self, hproduct]
    exact hreal_norm
  nlinarith [norm_nonneg (T z)]

/-- A prescribed positive real shift can be split equally between the two
actual OS Hilbert vectors. The remaining bridge stays in the right half-plane. -/
theorem osiiOriginalOSHilbertComplex_inner_halfShift
    (OS : OsterwalderSchraderAxioms d)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {z : Complex} (hz : 0 < z.re)
    (x y : OSHilbertSpace OS) :
    @inner Complex (OSHilbertSpace OS) _
        (osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex) x)
        (osiiOriginalOSHilbertComplex OS z
          (osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex) y)) =
      @inner Complex (OSHilbertSpace OS) _ x
        (osiiOriginalOSHilbertComplex OS (z + (epsilon : Complex)) y) := by
  let h : Complex := ((epsilon / 2 : Real) : Complex)
  have hh : 0 < h.re := by simpa [h] using half_pos hepsilon
  have hhz : 0 < (h + z).re := by simpa using add_pos hh hz
  have hself : (osiiOriginalOSHilbertComplex OS h).adjoint =
      osiiOriginalOSHilbertComplex OS h := by
    rw [osiiOriginalOSHilbertComplex_adjoint OS h hh]
    simp [h]
  have hsum : h + z + h = z + (epsilon : Complex) := by
    dsimp [h]
    push_cast
    ring
  change @inner Complex (OSHilbertSpace OS) _
      (osiiOriginalOSHilbertComplex OS h x)
      (osiiOriginalOSHilbertComplex OS z
        (osiiOriginalOSHilbertComplex OS h y)) = _
  rw [← ContinuousLinearMap.adjoint_inner_right, hself]
  rw [← ContinuousLinearMap.comp_apply,
    ← osiiOriginalOSHilbertComplex_add OS h z hh hz,
    ← ContinuousLinearMap.comp_apply,
    ← osiiOriginalOSHilbertComplex_add OS (h + z) h hhz hh,
    hsum]

/-- The diagonal at the full shift is the norm square of the half-shifted
vector. This keeps the reflected source, rather than its undamped norm. -/
theorem osiiOriginalOSHilbertComplex_inner_halfShift_self
    (OS : OsterwalderSchraderAxioms d)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (x y : OSHilbertSpace OS) :
    @inner Complex (OSHilbertSpace OS) _
        (osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex) x)
        (osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex) y) =
      @inner Complex (OSHilbertSpace OS) _ x
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex) y) := by
  let h : Complex := ((epsilon / 2 : Real) : Complex)
  have hh : 0 < h.re := by simpa [h] using half_pos hepsilon
  have hsum : h + h = (epsilon : Complex) := by
    dsimp [h]
    push_cast
    ring
  change @inner Complex (OSHilbertSpace OS) _
      (osiiOriginalOSHilbertComplex OS h x)
      (osiiOriginalOSHilbertComplex OS h y) = _
  rw [← ContinuousLinearMap.adjoint_inner_right,
    osiiOriginalOSHilbertComplex_adjoint OS h hh]
  have hstar : star h = h := by simp [h]
  rw [hstar, ← ContinuousLinearMap.comp_apply,
    ← osiiOriginalOSHilbertComplex_add OS h h hh hh, hsum]

/-- Sharp reflected Schwarz estimate at every prescribed positive shift.
No cutoff-size restriction or growth hypothesis enters this inequality. -/
theorem norm_osiiOriginalOSHilbertComplex_inner_shift_le
    (OS : OsterwalderSchraderAxioms d)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {z : Complex} (hz : 0 < z.re)
    (x y : OSHilbertSpace OS) :
    ‖@inner Complex (OSHilbertSpace OS) _ x
        (osiiOriginalOSHilbertComplex OS (z + (epsilon : Complex)) y)‖ <=
      Real.sqrt
        (‖@inner Complex (OSHilbertSpace OS) _ x
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)‖ *
          ‖@inner Complex (OSHilbertSpace OS) _ y
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) y)‖) := by
  let T := osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
  rw [← osiiOriginalOSHilbertComplex_inner_halfShift OS hepsilon hz x y,
    ← osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon x x,
    ← osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon y y]
  change ‖@inner Complex (OSHilbertSpace OS) _ (T x)
      (osiiOriginalOSHilbertComplex OS z (T y))‖ <= _
  have hnorm : ‖osiiOriginalOSHilbertComplex OS z (T y)‖ <= ‖T y‖ := by
    calc
      _ <= ‖osiiOriginalOSHilbertComplex OS z‖ * ‖T y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ <= 1 * ‖T y‖ :=
        mul_le_mul_of_nonneg_right
          (osiiOriginalOSHilbertComplex_norm_le_one OS z hz) (norm_nonneg _)
      _ = ‖T y‖ := one_mul _
  calc
    _ <= ‖T x‖ * ‖T y‖ :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    _ = Real.sqrt
        (‖@inner Complex (OSHilbertSpace OS) _ (T x) (T x)‖ *
          ‖@inner Complex (OSHilbertSpace OS) _ (T y) (T y)‖) := by
      rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq,
        ← inner_self_re_eq_norm, inner_self_eq_norm_sq,
        ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

end OSReconstruction
