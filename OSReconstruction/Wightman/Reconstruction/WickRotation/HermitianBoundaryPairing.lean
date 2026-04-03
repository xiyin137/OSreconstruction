import OSReconstruction.Wightman.Reconstruction

open scoped Topology
open MeasureTheory Complex

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace OSReconstruction

variable {d n : ℕ} [NeZero d]

/-- Pull back an `n`-point Schwartz test by the global sign map `x ↦ -x`. -/
def negSchwartzNPoint (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := NPointDomain d n)) f

@[simp] theorem negSchwartzNPoint_apply
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    negSchwartzNPoint (d := d) (n := n) f x = f (-x) := rfl

/-- Reverse the point order and then negate every component. -/
def negReverseNPoint (x : NPointDomain d n) : NPointDomain d n :=
  fun k μ => -x (Fin.rev k) μ

omit [NeZero d] in
theorem negReverseNPoint_involutive (x : NPointDomain d n) :
    negReverseNPoint (d := d) (n := n) (negReverseNPoint (d := d) (n := n) x) = x := by
  ext k μ
  simp [negReverseNPoint]

theorem negReverseNPoint_measurePreserving :
    MeasureTheory.MeasurePreserving (negReverseNPoint (d := d) (n := n))
      MeasureTheory.volume MeasureTheory.volume := by
  have hcomp :
      negReverseNPoint (d := d) (n := n) =
        (fun x : NPointDomain d n => -fun i => x (Fin.rev i)) := by
    rfl
  rw [hcomp]
  exact (MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n))).comp
    (reverseNPoint_measurePreserving (d := d) (n := n))

def negReverseNPointMeasEquiv : NPointDomain d n ≃ᵐ NPointDomain d n where
  toEquiv :=
    { toFun := negReverseNPoint (d := d) (n := n)
      invFun := negReverseNPoint (d := d) (n := n)
      left_inv := negReverseNPoint_involutive (d := d) (n := n)
      right_inv := negReverseNPoint_involutive (d := d) (n := n) }
  measurable_toFun := (negReverseNPoint_measurePreserving (d := d) (n := n)).measurable
  measurable_invFun := (negReverseNPoint_measurePreserving (d := d) (n := n)).measurable

/-- Change variables for the rapidity-reduced partner boundary pairing. -/
theorem integral_star_comp_negReverse_mul
    (g : NPointDomain d n → ℂ) (f : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, starRingEnd ℂ (g (negReverseNPoint (d := d) (n := n) x)) * f x
      =
    starRingEnd ℂ
      (∫ x : NPointDomain d n, g x * starRingEnd ℂ (f (negReverseNPoint (d := d) (n := n) x))) := by
  let h : NPointDomain d n → ℂ := fun x =>
    starRingEnd ℂ (g x) * f (negReverseNPoint (d := d) (n := n) x)
  calc
    ∫ x : NPointDomain d n, starRingEnd ℂ (g (negReverseNPoint (d := d) (n := n) x)) * f x
        = ∫ x : NPointDomain d n, h (negReverseNPoint (d := d) (n := n) x) := by
            simp [h, negReverseNPoint_involutive]
    _ = ∫ x : NPointDomain d n, h x := by
          simpa [h] using
            ((negReverseNPoint_measurePreserving (d := d) (n := n)).integral_comp'
              (f := negReverseNPointMeasEquiv (d := d) (n := n)) (g := h))
    _ = starRingEnd ℂ
          (∫ x : NPointDomain d n, g x * starRingEnd ℂ (f (negReverseNPoint (d := d) (n := n) x))) := by
            rw [show h = fun x : NPointDomain d n =>
              starRingEnd ℂ (g x * starRingEnd ℂ (f (negReverseNPoint (d := d) (n := n) x))) by
                funext x; simp [h, map_mul, mul_comm],
              ← _root_.integral_conj]

theorem negSchwartzNPoint_reverse_osConj_apply
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    ((negSchwartzNPoint (d := d) (n := n) f).reverse.conj) x =
      starRingEnd ℂ (f (negReverseNPoint (d := d) (n := n) x)) := by
  have hnegRev : (-fun i => x (Fin.rev i)) = negReverseNPoint (d := d) (n := n) x := by
    ext i μ
    simp [negReverseNPoint]
  simp [SchwartzMap.conj_apply, SchwartzMap.reverse_apply, negSchwartzNPoint, hnegRev]

theorem wightman_hermitian_negSchwartz
    (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n) :
    Wfn.W n (((negSchwartzNPoint (d := d) (n := n) f).reverse).conj) =
      starRingEnd ℂ (Wfn.W n (negSchwartzNPoint (d := d) (n := n) f)) := by
  apply Wfn.hermitian n (negSchwartzNPoint (d := d) (n := n) f)
    (((negSchwartzNPoint (d := d) (n := n) f).reverse).conj)
  intro x
  exact negSchwartzNPoint_reverse_osConj_apply (d := d) (n := n) f x

theorem star_wightman_hermitian_negSchwartz
    (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n) :
    starRingEnd ℂ
        (Wfn.W n (((negSchwartzNPoint (d := d) (n := n) f).reverse).conj)) =
      Wfn.W n (negSchwartzNPoint (d := d) (n := n) f) := by
  rw [wightman_hermitian_negSchwartz (Wfn := Wfn) (f := f)]
  simp

/-- Boundary pairing for the rapidity-reduced partner term: after the `π i` rapidity shift,
the partner boundary value is the Wightman pairing against the globally negated test. -/
theorem tendsto_boundary_negReverse_pairing
    (Wfn : WightmanFunctions d)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)))
    (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        starRingEnd ℂ
          (F (fun k μ => ↑((negReverseNPoint (d := d) (n := n) x) k μ) +
            ε * ↑(η k μ) * Complex.I)) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n (negSchwartzNPoint (d := d) (n := n) f))) := by
  let h : SchwartzNPoint d n := ((negSchwartzNPoint (d := d) (n := n) f).reverse).conj
  have hlim : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (h x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n h)) := hF_bv h η hη
  have hEq :
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        starRingEnd ℂ
          (F (fun k μ => ↑((negReverseNPoint (d := d) (n := n) x) k μ) +
            ε * ↑(η k μ) * Complex.I)) * (f x))
      =
      (fun ε : ℝ => starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (h x))) := by
    funext ε
    have hnegRev : ∀ x : NPointDomain d n,
        negReverseNPoint (d := d) (n := n) x = -fun i => x (Fin.rev i) := by
      intro x
      ext i μ
      simp [negReverseNPoint]
    rw [integral_star_comp_negReverse_mul
      (g := fun z : NPointDomain d n =>
        F (fun k μ => ↑(z k μ) + ε * ↑(η k μ) * Complex.I))
      (f := f)]
    simp [h, hnegRev]
  rw [hEq]
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ => starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (h x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (Wfn.W n h))) :=
    (continuous_star.tendsto (Wfn.W n h)).comp hlim
  simpa [h, star_wightman_hermitian_negSchwartz (Wfn := Wfn) (f := f)] using hstar

end OSReconstruction
