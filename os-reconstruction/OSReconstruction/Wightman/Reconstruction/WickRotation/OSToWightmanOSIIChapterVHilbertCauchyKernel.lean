/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMixedHilbertPairing
import Mathlib.Analysis.InnerProductSpace.Dual



















noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private def hilbertToDualRealLinearIsometry
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    H →ₗᵢ[ℝ] StrongDual ℂ H where
  toFun := InnerProductSpace.toDual ℂ H
  map_add' x y := by
    exact map_add (InnerProductSpace.toDual ℂ H) x y
  map_smul' r x := by
    change
      InnerProductSpace.toDual ℂ H ((r : ℂ) • x) =
        (r : ℂ) • InnerProductSpace.toDual ℂ H x
    simpa using
      (InnerProductSpace.toDual ℂ H).map_smulₛₗ (r : ℂ) x
  norm_map' x := (InnerProductSpace.toDual ℂ H).norm_map x

private theorem star_circleMap_star
    (c : ℂ) (R : ℝ) (θ : ℝ) :
    starRingEnd ℂ (circleMap (starRingEnd ℂ c) R θ) =
      circleMap c R (-θ) := by
  rw [circleMap, circleMap, map_add, map_mul, ← exp_conj]
  simp

private theorem star_deriv_circleMap_star
    (c : ℂ) (R : ℝ) (θ : ℝ) :
    starRingEnd ℂ (deriv (circleMap (starRingEnd ℂ c) R) θ) =
      -deriv (circleMap c R) (-θ) := by
  rw [
    show deriv (circleMap (starRingEnd ℂ c) R) θ =
        circleMap 0 R θ * I from deriv_circleMap _ _ _,
    show deriv (circleMap c R) (-θ) =
        circleMap 0 R (-θ) * I from deriv_circleMap _ _ _,
    map_mul
  ]
  have hcircle :
      starRingEnd ℂ (circleMap 0 R θ) =
        circleMap 0 R (-θ) := by
    simpa using star_circleMap_star (0 : ℂ) R θ
  have hI : starRingEnd ℂ I = -I := by
    exact Complex.conj_I
  rw [hcircle, hI]
  ring

private theorem hilbertToDual_intervalIntegral_comp
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : ℝ → H) (a b : ℝ) :
    (∫ θ in a..b, InnerProductSpace.toDual ℂ H (f θ)) =
      InnerProductSpace.toDual ℂ H (∫ θ in a..b, f θ) := by
  let A := hilbertToDualRealLinearIsometry (H := H)
  change (∫ θ in a..b, A (f θ)) = A (∫ θ in a..b, f θ)
  simp only [intervalIntegral]
  have hab :
      (∫ x in Set.Ioc a b, A (f x) ∂volume) =
        A (∫ x in Set.Ioc a b, f x ∂volume) :=
    A.integral_comp_comm
      (μ := volume.restrict (Set.Ioc a b)) f
  have hba :
      (∫ x in Set.Ioc b a, A (f x) ∂volume) =
        A (∫ x in Set.Ioc b a, f x ∂volume) :=
    A.integral_comp_comm
      (μ := volume.restrict (Set.Ioc b a)) f
  rw [hab, hba, map_sub]

private theorem circleIntegral_conjugateDual
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : ℂ → H) (c : ℂ) (R : ℝ) :
    (∮ z in C(starRingEnd ℂ c, R),
        InnerProductSpace.toDual ℂ H (f (starRingEnd ℂ z))) =
      -InnerProductSpace.toDual ℂ H
        (∮ z in C(c, R), f z) := by
  let A := hilbertToDualRealLinearIsometry (H := H)
  let h : ℝ → H :=
    fun θ =>
      deriv (circleMap c R) θ • f (circleMap c R θ)
  have hperiodic : Function.Periodic h (2 * Real.pi) := by
    intro θ
    simp only [h]
    rw [
      show deriv (circleMap c R) (θ + 2 * Real.pi) =
          circleMap 0 R (θ + 2 * Real.pi) * I from
        deriv_circleMap _ _ _,
      show deriv (circleMap c R) θ =
          circleMap 0 R θ * I from deriv_circleMap _ _ _,
      (periodic_circleMap 0 R) θ,
      (periodic_circleMap c R) θ
    ]
  have hintegrand (θ : ℝ) :
      deriv (circleMap (starRingEnd ℂ c) R) θ •
          InnerProductSpace.toDual ℂ H
            (f (starRingEnd ℂ
              (circleMap (starRingEnd ℂ c) R θ))) =
        A (-h (-θ)) := by
    calc
      deriv (circleMap (starRingEnd ℂ c) R) θ •
          InnerProductSpace.toDual ℂ H
            (f (starRingEnd ℂ
              (circleMap (starRingEnd ℂ c) R θ))) =
        InnerProductSpace.toDual ℂ H
          ((starRingEnd ℂ
              (deriv (circleMap (starRingEnd ℂ c) R) θ)) •
            f (starRingEnd ℂ
              (circleMap (starRingEnd ℂ c) R θ))) := by
          symm
          simpa using
            (InnerProductSpace.toDual ℂ H).map_smulₛₗ
              (starRingEnd ℂ
                (deriv (circleMap (starRingEnd ℂ c) R) θ))
              (f (starRingEnd ℂ
                (circleMap (starRingEnd ℂ c) R θ)))
      _ = A (-h (-θ)) := by
        change
          InnerProductSpace.toDual ℂ H
              ((starRingEnd ℂ
                  (deriv (circleMap (starRingEnd ℂ c) R) θ)) •
                f (starRingEnd ℂ
                  (circleMap (starRingEnd ℂ c) R θ))) =
            InnerProductSpace.toDual ℂ H (-h (-θ))
        congr 1
        rw [star_deriv_circleMap_star, star_circleMap_star]
        simp [h]
  rw [circleIntegral, circleIntegral]
  change
    (∫ θ in 0..2 * Real.pi,
      deriv (circleMap (starRingEnd ℂ c) R) θ •
        InnerProductSpace.toDual ℂ H
          (f (starRingEnd ℂ
            (circleMap (starRingEnd ℂ c) R θ)))) =
      -InnerProductSpace.toDual ℂ H (∫ θ in 0..2 * Real.pi, h θ)
  simp_rw [hintegrand]
  change
    (∫ θ in 0..2 * Real.pi,
      InnerProductSpace.toDual ℂ H (-h (-θ))) =
      -InnerProductSpace.toDual ℂ H
        (∫ θ in 0..2 * Real.pi, h θ)
  rw [hilbertToDual_intervalIntegral_comp]
  change
    A (∫ θ in 0..2 * Real.pi, -h (-θ)) =
      -A (∫ θ in 0..2 * Real.pi, h θ)
  rw [← map_neg]
  apply congrArg A
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg]
  congr 1
  calc
    (∫ θ in -(2 * Real.pi)..-0, h θ) =
        ∫ θ in 0..2 * Real.pi, h (θ - 2 * Real.pi) := by
      simpa [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_add_right h
          (-(2 * Real.pi))).symm
    _ = ∫ θ in 0..2 * Real.pi, h θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact hperiodic.sub_eq θ

private theorem iteratedCircleIntegral_conjugateDual
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (m : ℕ)
    (f : (Fin m → ℂ) → H)
    (c : Fin m → ℂ) (r : Fin m → ℝ) :
    SCV.iteratedCircleIntegral m
        (fun z =>
          InnerProductSpace.toDual ℂ H (f (star z)))
        (star c) r =
      (-1 : ℂ) ^ m •
        InnerProductSpace.toDual ℂ H
          (SCV.iteratedCircleIntegral m f c r) := by
  induction m with
  | zero =>
      simp only [SCV.iteratedCircleIntegral, pow_zero, one_smul]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      rw [SCV.iteratedCircleIntegral_succ,
        SCV.iteratedCircleIntegral_succ]
      have hcenter :
          star c ∘ Fin.castSucc =
            star (c ∘ Fin.castSucc) := by
        rfl
      rw [hcenter]
      have hinner (z : Fin m → ℂ) :
          (∮ w in C(starRingEnd ℂ (c (Fin.last m)),
              r (Fin.last m)),
            InnerProductSpace.toDual ℂ H
              (f (star (Fin.snoc z w)))) =
            -InnerProductSpace.toDual ℂ H
              (∮ w in C(c (Fin.last m), r (Fin.last m)),
                f (Fin.snoc (star z) w)) := by
        have h :=
          circleIntegral_conjugateDual
            (fun w => f (Fin.snoc (star z) w))
            (c (Fin.last m)) (r (Fin.last m))
        have hstar (w : ℂ) :
            star (@Fin.snoc m (fun _ => ℂ) z w) =
              @Fin.snoc m (fun _ => ℂ) (star z)
                (starRingEnd ℂ w) := by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j
            simp
        simpa only [hstar] using h
      have hlast :
          star c (Fin.last m) =
            starRingEnd ℂ (c (Fin.last m)) := rfl
      rw [hlast]
      have hfun :
          (fun z : Fin m → ℂ =>
            (∮ w in C(starRingEnd ℂ (c (Fin.last m)),
                r (Fin.last m)),
              InnerProductSpace.toDual ℂ H
                (f (star (Fin.snoc z w))))) =
            (fun z =>
              -InnerProductSpace.toDual ℂ H
                (∮ w in C(c (Fin.last m), r (Fin.last m)),
                  f (Fin.snoc (star z) w))) := by
        funext z
        exact hinner z
      rw [hfun]
      have hneg :
          (fun z : Fin m → ℂ =>
            -InnerProductSpace.toDual ℂ H
              (∮ w in C(c (Fin.last m), r (Fin.last m)),
                f (Fin.snoc (star z) w))) =
            (fun z =>
              (-1 : ℂ) • InnerProductSpace.toDual ℂ H
                (∮ w in C(c (Fin.last m), r (Fin.last m)),
                  f (Fin.snoc (star z) w))) := by
        funext z
        exact (neg_one_smul ℂ _).symm
      rw [hneg, SCV.iteratedCircleIntegral_smul]
      let g : (Fin m → ℂ) → H :=
        fun z =>
          ∮ w in C(c (Fin.last m), r (Fin.last m)),
            f (Fin.snoc z w)
      change
        (-1 : ℂ) •
            SCV.iteratedCircleIntegral m
              (fun z => InnerProductSpace.toDual ℂ H (g (star z)))
              (star (c ∘ Fin.castSucc)) (r ∘ Fin.castSucc) =
          (-1 : ℂ) ^ (m + 1) •
            InnerProductSpace.toDual ℂ H
              (SCV.iteratedCircleIntegral m g
                (c ∘ Fin.castSucc) (r ∘ Fin.castSucc))
      rw [ih g (c ∘ Fin.castSucc) (r ∘ Fin.castSucc)]
      simp only [smul_smul, pow_succ]
      congr 1
      ring

theorem cauchyCoeffPolydisc_conjugateDual
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m : ℕ}
    (f : (Fin m → ℂ) → H)
    (c : Fin m → ℂ) (r : Fin m → ℝ)
    (α : Fin m → ℕ) :
    SCV.cauchyCoeffPolydisc
        (fun z => InnerProductSpace.toDual ℂ H (f (star z)))
        (star c) r α =
      InnerProductSpace.toDual ℂ H
        (SCV.cauchyCoeffPolydisc f c r α) := by
  let kernel : (Fin m → ℂ) → ℂ :=
    fun w => ∏ i, (w i - c i)⁻¹ ^ (α i + 1)
  let reflectedKernel : (Fin m → ℂ) → ℂ :=
    fun z => ∏ i, (z i - star c i)⁻¹ ^ (α i + 1)
  have hkernel (z : Fin m → ℂ) :
      starRingEnd ℂ (kernel (star z)) = reflectedKernel z := by
    simp only [kernel, reflectedKernel, map_prod, map_pow,
      map_inv₀, map_sub]
    apply Finset.prod_congr rfl
    intro i hi
    change
      (starRingEnd ℂ (starRingEnd ℂ (z i)) -
          starRingEnd ℂ (c i))⁻¹ ^ (α i + 1) =
        (z i - starRingEnd ℂ (c i))⁻¹ ^ (α i + 1)
    have hzz :
        starRingEnd ℂ (starRingEnd ℂ (z i)) = z i := by
      apply Complex.ext <;> simp
    exact congrArg
      (fun t : ℂ =>
        (t - starRingEnd ℂ (c i))⁻¹ ^ (α i + 1))
      hzz
  have hintegrand :
      (fun z =>
        reflectedKernel z •
          InnerProductSpace.toDual ℂ H (f (star z))) =
      (fun z =>
        InnerProductSpace.toDual ℂ H
          (kernel (star z) • f (star z))) := by
    funext z
    rw [(InnerProductSpace.toDual ℂ H).map_smulₛₗ,
      hkernel]
  simp only [SCV.cauchyCoeffPolydisc]
  change
    (2 * Real.pi * I)⁻¹ ^ m •
        SCV.iteratedCircleIntegral m
          (fun z =>
            reflectedKernel z •
              InnerProductSpace.toDual ℂ H (f (star z)))
          (star c) r =
      InnerProductSpace.toDual ℂ H
        ((2 * Real.pi * I)⁻¹ ^ m •
          SCV.iteratedCircleIntegral m
            (fun w => kernel w • f w) c r)
  rw [hintegrand,
    iteratedCircleIntegral_conjugateDual
      m (fun w => kernel w • f w) c r,
    (InnerProductSpace.toDual ℂ H).map_smulₛₗ]
  have hstar :
      starRingEnd ℂ ((2 * Real.pi * I)⁻¹) =
        -((2 * Real.pi * I)⁻¹) := by
    rw [map_inv₀, map_mul, map_mul]
    norm_num [map_ofNat]
  rw [map_pow, hstar]
  have hscalar :
      (2 * Real.pi * I)⁻¹ ^ m * (-1 : ℂ) ^ m =
        (-((2 * Real.pi * I)⁻¹)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  rw [smul_smul, hscalar]

omit [CompleteSpace E] in
theorem iteratedCircleIntegral_append
    {a b : ℕ}
    (f : (Fin (a + b) → ℂ) → E)
    (ca : Fin a → ℂ) (ra : Fin a → ℝ)
    (cb : Fin b → ℂ) (rb : Fin b → ℝ) :
    SCV.iteratedCircleIntegral (a + b) f
        (Fin.append ca cb) (Fin.append ra rb) =
      SCV.iteratedCircleIntegral a
        (fun x =>
          SCV.iteratedCircleIntegral b
            (fun y => f (Fin.append x y)) cb rb)
        ca ra := by
  induction b with
  | zero =>
      simp only [Nat.add_zero, SCV.iteratedCircleIntegral]
      have hca : Fin.append ca cb = ca := by
        funext i
        exact Fin.append_left ca cb i
      have hra : Fin.append ra rb = ra := by
        funext i
        exact Fin.append_left ra rb i
      rw [hca, hra]
      congr 1
      funext x
      congr 1
      funext i
      exact (Fin.append_left x Fin.elim0 i).symm
  | succ b ih =>
      simp only [Nat.add_succ]
      rw [SCV.iteratedCircleIntegral_succ]
      have hcenter :
          Fin.append ca cb ∘ Fin.castSucc =
            Fin.append ca (cb ∘ Fin.castSucc) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · have hidx :
              Fin.castSucc (Fin.castAdd b j) =
                Fin.castAdd (b + 1) j := by
            ext
            rfl
          rw [Function.comp_apply, hidx, Fin.append_left,
            Fin.append_left]
        · have hidx :
              Fin.castSucc (Fin.natAdd a j) =
                Fin.natAdd a (Fin.castSucc j) := by
            ext
            rfl
          rw [Function.comp_apply, hidx, Fin.append_right,
            Fin.append_right, Function.comp_apply]
      have hradius :
          Fin.append ra rb ∘ Fin.castSucc =
            Fin.append ra (rb ∘ Fin.castSucc) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · have hidx :
              Fin.castSucc (Fin.castAdd b j) =
                Fin.castAdd (b + 1) j := by
            ext
            rfl
          rw [Function.comp_apply, hidx, Fin.append_left,
            Fin.append_left]
        · have hidx :
              Fin.castSucc (Fin.natAdd a j) =
                Fin.natAdd a (Fin.castSucc j) := by
            ext
            rfl
          rw [Function.comp_apply, hidx, Fin.append_right,
            Fin.append_right, Function.comp_apply]
      rw [hcenter, hradius, ih]
      congr 1
      funext x
      rw [SCV.iteratedCircleIntegral_succ]
      have hcenter_last :
          Fin.append ca cb (Fin.last (a + b)) =
            cb (Fin.last b) := by
        rw [← Fin.natAdd_last, Fin.append_right]
      have hradius_last :
          Fin.append ra rb (Fin.last (a + b)) =
            rb (Fin.last b) := by
        rw [← Fin.natAdd_last, Fin.append_right]
      rw [hcenter_last, hradius_last]
      congr 1
      funext y
      congr 1
      funext w
      rw [Fin.append_snoc]

theorem cauchyCoeffPolydisc_append
    {a b : ℕ}
    (f : (Fin (a + b) → ℂ) → E)
    (ca : Fin a → ℂ) (ra : Fin a → ℝ) (α : Fin a → ℕ)
    (cb : Fin b → ℂ) (rb : Fin b → ℝ) (β : Fin b → ℕ) :
    SCV.cauchyCoeffPolydisc f
        (Fin.append ca cb) (Fin.append ra rb) (Fin.append α β) =
      SCV.cauchyCoeffPolydisc
        (fun x =>
          SCV.cauchyCoeffPolydisc
            (fun y => f (Fin.append x y)) cb rb β)
        ca ra α := by
  simp only [SCV.cauchyCoeffPolydisc]
  rw [iteratedCircleIntegral_append]
  have hprod (x : Fin a → ℂ) (y : Fin b → ℂ) :
      (∏ i : Fin (a + b),
          (Fin.append x y i - Fin.append ca cb i)⁻¹ ^
            (Fin.append α β i + 1)) =
        (∏ i : Fin a, (x i - ca i)⁻¹ ^ (α i + 1)) *
          ∏ i : Fin b, (y i - cb i)⁻¹ ^ (β i + 1) := by
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp
    · apply Finset.prod_congr rfl
      intro i hi
      simp
  simp_rw [hprod, mul_smul, SCV.iteratedCircleIntegral_smul]
  rw [pow_add]
  have hpoint (w : Fin a → ℂ) :
      (∏ i : Fin a, (w i - ca i)⁻¹ ^ (α i + 1)) •
          ((2 * Real.pi * I)⁻¹ ^ b •
            SCV.iteratedCircleIntegral b
              (fun y =>
                (∏ i : Fin b, (y i - cb i)⁻¹ ^ (β i + 1)) •
                  f (Fin.append w y))
              cb rb) =
        (2 * Real.pi * I)⁻¹ ^ b •
          ((∏ i : Fin a, (w i - ca i)⁻¹ ^ (α i + 1)) •
            SCV.iteratedCircleIntegral b
              (fun y =>
                (∏ i : Fin b, (y i - cb i)⁻¹ ^ (β i + 1)) •
                  f (Fin.append w y))
              cb rb) := by
    simp only [smul_smul]
    congr 1
    ring
  simp_rw [hpoint, SCV.iteratedCircleIntegral_smul, smul_smul]

theorem cauchyCoeffPolydisc_comp_continuousLinearMap
    {m : ℕ}
    (L : E →L[ℂ] F)
    {f : (Fin (m + 1) → ℂ) → E}
    {center : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc center (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (α : Fin (m + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc (fun z => L (f z))
        center (fun _ => R) α =
      L (SCV.cauchyCoeffPolydisc f center (fun _ => R) α) := by
  have hLf : DifferentiableOn ℂ (fun z => L (f z)) U :=
    L.differentiable.comp_differentiableOn hf
  rw [
    SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
      hR hU hRU hLf α,
    SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
      hR hU hRU hf α
  ]
  have hcenter : center ∈ U :=
    hRU (SCV.center_mem_closedPolydisc (fun _ => hR.le))
  have hcontDiff :
      ContDiffAt ℂ (∑ i, α i) f center :=
    (SCV.differentiableOn_analyticAt hU hf hcenter).contDiffAt
  let directions : Fin (∑ i, α i) → (Fin (m + 1) → ℂ) :=
    fun j i =>
      if i = SCV.multiIndexEnumeration α j then 1 else 0
  have hderiv :=
    L.iteratedFDeriv_comp_left hcontDiff
      (i := ∑ i, α i) (by exact_mod_cast le_rfl)
  have happ := congrArg (fun D => D directions) hderiv
  let q : ℂ :=
    ((((∏ i, (α i).factorial : ℕ) : ℂ))⁻¹)
  change
    q • iteratedFDeriv ℂ (∑ i, α i)
        (fun z => L (f z)) center directions =
      L (q • iteratedFDeriv ℂ (∑ i, α i) f center directions)
  calc
    q • iteratedFDeriv ℂ (∑ i, α i)
        (fun z => L (f z)) center directions =
      q • L (iteratedFDeriv ℂ (∑ i, α i) f center directions) := by
      apply congrArg (fun v => q • v)
      simpa [directions, Function.comp_def] using happ
    _ = L (q • iteratedFDeriv ℂ (∑ i, α i) f center directions) := by
      rw [map_smul]

theorem cauchyCoeffPolydisc_eq_of_eventuallyEq
    {m : ℕ}
    (hm : 0 < m)
    {f g : (Fin m → ℂ) → E}
    {center : Fin m → ℂ}
    {Rf Rg : ℝ}
    (hRf : 0 < Rf) (hRg : 0 < Rg)
    {Uf Ug : Set (Fin m → ℂ)}
    (hUf : IsOpen Uf) (hUg : IsOpen Ug)
    (hRfUf : SCV.closedPolydisc center (fun _ => Rf) ⊆ Uf)
    (hRgUg : SCV.closedPolydisc center (fun _ => Rg) ⊆ Ug)
    (hf : DifferentiableOn ℂ f Uf)
    (hg : DifferentiableOn ℂ g Ug)
    (hfg : f =ᶠ[𝓝 center] g)
    (α : Fin m → ℕ) :
    SCV.cauchyCoeffPolydisc f center (fun _ => Rf) α =
      SCV.cauchyCoeffPolydisc g center (fun _ => Rg) α := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [
    SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
      hRf hUf hRfUf hf α,
    SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
      hRg hUg hRgUg hg α
  ]
  congr 1
  exact congrArg
    (fun D =>
      D (fun j i =>
        if i = SCV.multiIndexEnumeration α j then 1 else 0))
    ((Filter.EventuallyEq.iteratedFDeriv ℂ hfg
      (∑ i, α i)).eq_of_nhds)

/-- The scalar reflected kernel of a Hilbert-valued field. -/
def reflectedHilbertKernel
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    (field : (Fin m → ℂ) → H) :
    (Fin (m + m) → ℂ) → ℂ :=
  fun w =>
    @inner ℂ H _
      (field (star (fun i => w (Fin.castAdd m i))))
      (field (fun i => w (Fin.natAdd m i)))

/-- The reflected mixed scalar kernel of two Hilbert-valued fields.

Unlike `reflectedHilbertKernel`, the left and right fields may come from
different source indices.  This is the kernel required by the source-indexed
`(P_N)` scalar-product identity. -/
def reflectedHilbertPairKernel
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    (left right : (Fin m → ℂ) → H) :
    (Fin (m + m) → ℂ) → ℂ :=
  fun w =>
    @inner ℂ H _
      (left (star (fun i => w (Fin.castAdd m i))))
      (right (fun i => w (Fin.natAdd m i)))

/-- The natural flattened domain of the reflected kernel.  Its left block is
conjugated before entering the Hilbert field, while its right block enters
unchanged. -/
def reflectedHilbertKernelDomain
    {m : ℕ}
    (U : Set (Fin m → ℂ)) :
    Set (Fin (m + m) → ℂ) :=
  {w |
    star (fun i => w (Fin.castAdd m i)) ∈ U ∧
      (fun i => w (Fin.natAdd m i)) ∈ U}

/-- The natural flattened domain of a reflected pair kernel with possibly
different left and right field domains. -/
def reflectedHilbertPairKernelDomain
    {m : ℕ}
    (U V : Set (Fin m → ℂ)) :
    Set (Fin (m + m) → ℂ) :=
  {w |
    star (fun i => w (Fin.castAdd m i)) ∈ U ∧
      (fun i => w (Fin.natAdd m i)) ∈ V}

@[simp]
theorem reflectedHilbertPairKernel_self
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    (field : (Fin m → ℂ) → H) :
    reflectedHilbertPairKernel field field =
      reflectedHilbertKernel field :=
  rfl

@[simp]
theorem reflectedHilbertPairKernelDomain_self
    {m : ℕ}
    (U : Set (Fin m → ℂ)) :
    reflectedHilbertPairKernelDomain U U =
      reflectedHilbertKernelDomain U :=
  rfl

theorem reflectedHilbertKernelDomain_open
    {m : ℕ}
    {U : Set (Fin m → ℂ)}
    (hU : IsOpen U) :
    IsOpen (reflectedHilbertKernelDomain U) := by
  change
    IsOpen
      ((fun w : Fin (m + m) → ℂ =>
          ((fun i => w (Fin.castAdd m i)),
            (fun i => w (Fin.natAdd m i)))) ⁻¹'
        mixedHilbertPairingDomain U U)
  exact
    (isOpen_mixedHilbertPairingDomain hU hU).preimage
      (by fun_prop)

theorem reflectedHilbertPairKernelDomain_open
    {m : ℕ}
    {U V : Set (Fin m → ℂ)}
    (hU : IsOpen U)
    (hV : IsOpen V) :
    IsOpen (reflectedHilbertPairKernelDomain U V) := by
  change
    IsOpen
      ((fun w : Fin (m + m) → ℂ =>
          ((fun i => w (Fin.castAdd m i)),
            (fun i => w (Fin.natAdd m i)))) ⁻¹'
        mixedHilbertPairingDomain U V)
  exact
    (isOpen_mixedHilbertPairingDomain hU hV).preimage
      (by fun_prop)

/-- Convex Hilbert-field domains give a convex reflected pair-kernel
domain. -/
theorem convex_reflectedHilbertPairKernelDomain
    {m : ℕ}
    {U V : Set (Fin m → ℂ)}
    (hU : Convex ℝ U)
    (hV : Convex ℝ V) :
    Convex ℝ (reflectedHilbertPairKernelDomain U V) := by
  intro z hz w hw a b ha hb hab
  constructor
  · have hcombo := hU hz.1 hw.1 ha hb hab
    convert hcombo using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    change
      starRingEnd ℂ
          ((a : ℂ) * z (Fin.castAdd m i) +
            (b : ℂ) * w (Fin.castAdd m i)) =
        (a : ℂ) *
            starRingEnd ℂ (z (Fin.castAdd m i)) +
          (b : ℂ) *
            starRingEnd ℂ (w (Fin.castAdd m i))
    simp [map_add, map_mul]
  · have hcombo := hV hz.2 hw.2 ha hb hab
    exact hcombo

theorem reflectedHilbertKernel_holomorphic
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    {field : (Fin m → ℂ) → H}
    {U : Set (Fin m → ℂ)}
    (hU : IsOpen U)
    (hfield : DifferentiableOn ℂ field U) :
    DifferentiableOn ℂ
      (reflectedHilbertKernel field)
      (reflectedHilbertKernelDomain U) := by
  have hpair :
      DifferentiableOn ℂ
        (mixedHilbertPairing field field)
        (mixedHilbertPairingDomain U U) :=
    differentiableOn_mixedHilbertPairing hU hU hfield hfield
  have hsplit :
      Differentiable ℂ
        (fun w : Fin (m + m) → ℂ =>
          ((fun i => w (Fin.castAdd m i)),
            (fun i => w (Fin.natAdd m i)))) := by
    fun_prop
  simpa only [reflectedHilbertKernel, mixedHilbertPairing,
    reflectedHilbertKernelDomain, mixedHilbertPairingDomain,
    conjugateFieldDomain, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod] using
      hpair.comp hsplit.differentiableOn (fun _ hw => hw)

/-- A reflected pair kernel is holomorphic when both source-indexed Hilbert
fields are holomorphic on their respective domains. -/
theorem reflectedHilbertPairKernel_holomorphic
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    {left right : (Fin m → ℂ) → H}
    {U V : Set (Fin m → ℂ)}
    (hU : IsOpen U)
    (hV : IsOpen V)
    (hleft : DifferentiableOn ℂ left U)
    (hright : DifferentiableOn ℂ right V) :
    DifferentiableOn ℂ
      (reflectedHilbertPairKernel left right)
      (reflectedHilbertPairKernelDomain U V) := by
  have hpair :
      DifferentiableOn ℂ
        (mixedHilbertPairing left right)
        (mixedHilbertPairingDomain U V) :=
    differentiableOn_mixedHilbertPairing hU hV hleft hright
  have hsplit :
      Differentiable ℂ
        (fun w : Fin (m + m) → ℂ =>
          ((fun i => w (Fin.castAdd m i)),
            (fun i => w (Fin.natAdd m i)))) := by
    fun_prop
  simpa only [reflectedHilbertPairKernel, mixedHilbertPairing,
    reflectedHilbertPairKernelDomain, mixedHilbertPairingDomain,
    conjugateFieldDomain, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod] using
      hpair.comp hsplit.differentiableOn (fun _ hw => hw)

/-- The reflected scalar center corresponding to a Hilbert-field center. -/
def reflectedCauchyCenter
    {m : ℕ} (center : Fin m → ℂ) :
    Fin (m + m) → ℂ :=
  Fin.append (star center) center

@[simp] theorem reflectedCauchyCenter_left
    {m : ℕ} (center : Fin m → ℂ) (i : Fin m) :
    reflectedCauchyCenter center (Fin.castAdd m i) =
      starRingEnd ℂ (center i) := by
  simp [reflectedCauchyCenter]

@[simp] theorem reflectedCauchyCenter_right
    {m : ℕ} (center : Fin m → ℂ) (i : Fin m) :
    reflectedCauchyCenter center (Fin.natAdd m i) =
      center i := by
  change
    Fin.append (star center) center (Fin.natAdd m i) =
      center i
  rw [Fin.append_right]

theorem closedPolydisc_reflectedCauchyCenter_subset_kernelDomain
    {m : ℕ}
    {center : Fin m → ℂ}
    {R : ℝ}
    {U : Set (Fin m → ℂ)}
    (hRU : SCV.closedPolydisc center (fun _ => R) ⊆ U) :
    SCV.closedPolydisc
        (reflectedCauchyCenter center) (fun _ => R) ⊆
      reflectedHilbertKernelDomain U := by
  intro w hw
  constructor
  · apply hRU
    intro i
    rw [Metric.mem_closedBall, Complex.dist_eq]
    change
      ‖starRingEnd ℂ (w (Fin.castAdd m i)) - center i‖ ≤ R
    have heq :
        starRingEnd ℂ (w (Fin.castAdd m i)) - center i =
          starRingEnd ℂ
            (w (Fin.castAdd m i) -
              starRingEnd ℂ (center i)) := by
      simp [map_sub]
    rw [heq]
    have hwi := hw (Fin.castAdd m i)
    rw [Metric.mem_closedBall, Complex.dist_eq] at hwi
    have hwi' :
        ‖w (Fin.castAdd m i) -
          starRingEnd ℂ (center i)‖ ≤ R := by
      simpa only [reflectedCauchyCenter_left] using hwi
    exact
      (norm_star
        (w (Fin.castAdd m i) -
          starRingEnd ℂ (center i))).trans_le hwi'
  · apply hRU
    intro i
    have hwi := hw (Fin.natAdd m i)
    simpa only [reflectedCauchyCenter_right] using hwi

theorem reflectedHilbertKernelDomain_polydisc
    {m : ℕ}
    (center : Fin m → ℂ)
    (R : ℝ) :
    reflectedHilbertKernelDomain
        (SCV.Polydisc center (fun _ => R)) =
      SCV.Polydisc
        (reflectedCauchyCenter center) (fun _ => R) := by
  ext w
  constructor
  · intro hw j
    refine Fin.addCases ?_ ?_ j
    · intro i
      have hi := hw.1 i
      change
        dist (starRingEnd ℂ (w (Fin.castAdd m i)))
          (center i) < R at hi
      rw [Complex.dist_conj_comm] at hi
      change
        dist (w (Fin.castAdd m i))
          (reflectedCauchyCenter center (Fin.castAdd m i)) < R
      simpa only [reflectedCauchyCenter_left] using hi
    · intro i
      have hi := hw.2 i
      simpa only [reflectedCauchyCenter_right] using hi
  · intro hw
    constructor
    · intro i
      have hi := hw (Fin.castAdd m i)
      rw [Metric.mem_ball] at hi
      have hi' :
        dist (w (Fin.castAdd m i))
          (starRingEnd ℂ (center i)) < R := by
        simpa only [reflectedCauchyCenter_left] using hi
      rw [Metric.mem_ball]
      change
        dist (starRingEnd ℂ (w (Fin.castAdd m i)))
          (center i) < R
      rw [Complex.dist_conj_comm]
      exact hi'
    · intro i
      have hi := hw (Fin.natAdd m i)
      simpa only [reflectedCauchyCenter_right] using hi

/-- Local equality of both source-indexed fields induces local equality of
their reflected mixed kernels. -/
theorem reflectedHilbertPairKernel_eventuallyEq
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {m : ℕ}
    {left₁ left₂ right₁ right₂ : (Fin m → ℂ) → H}
    {center : Fin m → ℂ}
    (hleft : left₁ =ᶠ[𝓝 center] left₂)
    (hright : right₁ =ᶠ[𝓝 center] right₂) :
    reflectedHilbertPairKernel left₁ right₁ =ᶠ[
        𝓝 (reflectedCauchyCenter center)]
      reflectedHilbertPairKernel left₂ right₂ := by
  let leftCoordinate :
      (Fin (m + m) → ℂ) → (Fin m → ℂ) :=
    fun w => star (fun i => w (Fin.castAdd m i))
  let rightCoordinate :
      (Fin (m + m) → ℂ) → (Fin m → ℂ) :=
    fun w => fun i => w (Fin.natAdd m i)
  have hleftCoordinate :
      Tendsto leftCoordinate
        (𝓝 (reflectedCauchyCenter center)) (𝓝 center) := by
    have hcontinuous : Continuous leftCoordinate := by
      dsimp [leftCoordinate]
      fun_prop
    have hvalue :
        leftCoordinate (reflectedCauchyCenter center) = center := by
      funext i
      simp [leftCoordinate]
    simpa only [hvalue] using
      hcontinuous.tendsto (reflectedCauchyCenter center)
  have hrightCoordinate :
      Tendsto rightCoordinate
        (𝓝 (reflectedCauchyCenter center)) (𝓝 center) := by
    have hcontinuous : Continuous rightCoordinate := by
      dsimp [rightCoordinate]
      fun_prop
    have hvalue :
        rightCoordinate (reflectedCauchyCenter center) = center := by
      funext i
      exact reflectedCauchyCenter_right center i
    simpa only [hvalue] using
      hcontinuous.tendsto (reflectedCauchyCenter center)
  filter_upwards
    [hleftCoordinate.eventually hleft,
      hrightCoordinate.eventually hright]
      with w hwleft hwright
  simp only [reflectedHilbertPairKernel,
    leftCoordinate, rightCoordinate] at hwleft hwright ⊢
  rw [hwleft, hwright]

theorem cauchyCoeffPolydisc_reflectedHilbertKernel_append
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m : ℕ}
    {field : (Fin (m + 1) → ℂ) → H}
    {center : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc center (fun _ => R) ⊆ U)
    (hfield : DifferentiableOn ℂ field U)
    (α β : Fin (m + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc
        (reflectedHilbertKernel field)
        (reflectedCauchyCenter center)
        (Fin.append (fun _ => R) (fun _ => R))
        (Fin.append α β) =
      @inner ℂ H _
        (SCV.cauchyCoeffPolydisc field center (fun _ => R) α)
        (SCV.cauchyCoeffPolydisc field center (fun _ => R) β) := by
  unfold reflectedHilbertKernel reflectedCauchyCenter
  rw [cauchyCoeffPolydisc_append]
  simp only [Fin.append_left, Fin.append_right]
  let rightCoefficient : H :=
    SCV.cauchyCoeffPolydisc field center (fun _ => R) β
  have hright (x : Fin (m + 1) → ℂ) :
      SCV.cauchyCoeffPolydisc
          (fun y =>
            @inner ℂ H _ (field (star x)) (field y))
          center (fun _ => R) β =
        @inner ℂ H _ (field (star x)) rightCoefficient := by
    let L : H →L[ℂ] ℂ := innerSL ℂ (field (star x))
    simpa only [L, innerSL_apply_apply, rightCoefficient] using
      cauchyCoeffPolydisc_comp_continuousLinearMap
        L hR hU hRU hfield β
  simp_rw [hright]
  let dualField : (Fin (m + 1) → ℂ) → StrongDual ℂ H :=
    conjugateDualField field
  let eval : StrongDual ℂ H →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ rightCoefficient
  have hconjugateOpen :
      IsOpen (conjugateFieldDomain U) :=
    isOpen_conjugateFieldDomain hU
  have hdual :
      DifferentiableOn ℂ dualField (conjugateFieldDomain U) := by
    intro z hz
    have hfieldAt : DifferentiableAt ℂ field (star z) :=
      (hfield (star z) hz).differentiableAt
        (hU.mem_nhds hz)
    exact
      (differentiableAt_conjugateDualField field z hfieldAt)
        |>.differentiableWithinAt
  have hclosedConjugate :
      SCV.closedPolydisc (star center) (fun _ => R) ⊆
        conjugateFieldDomain U := by
    intro z hz
    change star z ∈ U
    apply hRU
    intro i
    rw [Metric.mem_closedBall, Complex.dist_eq]
    simp only [Pi.star_apply]
    change ‖starRingEnd ℂ (z i) - center i‖ ≤ R
    have heq :
        starRingEnd ℂ (z i) - center i =
          starRingEnd ℂ
            (z i - starRingEnd ℂ (center i)) := by
      simp [map_sub]
    rw [heq]
    have hzi := hz i
    rw [Metric.mem_closedBall, Complex.dist_eq] at hzi
    exact (norm_star (z i - starRingEnd ℂ (center i))).trans_le hzi
  calc
    SCV.cauchyCoeffPolydisc
        (fun x => @inner ℂ H _ (field (star x)) rightCoefficient)
        (star center) (fun _ => R) α =
      eval
        (SCV.cauchyCoeffPolydisc dualField
          (star center) (fun _ => R) α) := by
      simpa only [dualField, eval, conjugateDualField,
        ContinuousLinearMap.apply_apply, innerSL_apply_apply] using
        cauchyCoeffPolydisc_comp_continuousLinearMap
          eval hR hconjugateOpen hclosedConjugate hdual α
    _ = eval
        (InnerProductSpace.toDual ℂ H
          (SCV.cauchyCoeffPolydisc field center
            (fun _ => R) α)) := by
      change
        eval
            (SCV.cauchyCoeffPolydisc
              (fun z =>
                InnerProductSpace.toDual ℂ H (field (star z)))
              (star center) (fun _ => R) α) =
          _
      rw [cauchyCoeffPolydisc_conjugateDual]
    _ = @inner ℂ H _
        (SCV.cauchyCoeffPolydisc field center (fun _ => R) α)
        rightCoefficient := by
      rfl
    _ = _ := by
      rfl

/-- A scalar holomorphic germ locally equal to a reflected Hilbert kernel has
the Hilbert Gram Cauchy coefficients, even when the scalar and Hilbert
coefficients are computed using different valid radii. -/
theorem cauchyCoeffPolydisc_eq_inner_of_eventuallyEq_reflectedHilbertKernel
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m : ℕ}
    {scalar : (Fin ((m + 1) + (m + 1)) → ℂ) → ℂ}
    {field : (Fin (m + 1) → ℂ) → H}
    {center : Fin (m + 1) → ℂ}
    {scalarRadius fieldRadius : ℝ}
    (hscalarRadius : 0 < scalarRadius)
    (hfieldRadius : 0 < fieldRadius)
    {scalarDomain : Set (Fin ((m + 1) + (m + 1)) → ℂ)}
    {fieldDomain : Set (Fin (m + 1) → ℂ)}
    (hscalarDomain : IsOpen scalarDomain)
    (hfieldDomain : IsOpen fieldDomain)
    (hscalarClosed :
      SCV.closedPolydisc
          (reflectedCauchyCenter center) (fun _ => scalarRadius) ⊆
        scalarDomain)
    (hfieldClosed :
      SCV.closedPolydisc center (fun _ => fieldRadius) ⊆
        fieldDomain)
    (hscalar : DifferentiableOn ℂ scalar scalarDomain)
    (hfield : DifferentiableOn ℂ field fieldDomain)
    (hlocal :
      scalar =ᶠ[𝓝 (reflectedCauchyCenter center)]
        reflectedHilbertKernel field)
    (α β : Fin (m + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc scalar
        (reflectedCauchyCenter center)
        (fun _ => scalarRadius) (Fin.append α β) =
      @inner ℂ H _
        (SCV.cauchyCoeffPolydisc field center
          (fun _ => fieldRadius) α)
        (SCV.cauchyCoeffPolydisc field center
          (fun _ => fieldRadius) β) := by
  have hkernelOpen :
      IsOpen (reflectedHilbertKernelDomain fieldDomain) :=
    reflectedHilbertKernelDomain_open hfieldDomain
  have hkernelClosed :
      SCV.closedPolydisc
          (reflectedCauchyCenter center) (fun _ => fieldRadius) ⊆
        reflectedHilbertKernelDomain fieldDomain :=
    closedPolydisc_reflectedCauchyCenter_subset_kernelDomain hfieldClosed
  have hkernel :
      DifferentiableOn ℂ
        (reflectedHilbertKernel field)
        (reflectedHilbertKernelDomain fieldDomain) :=
    reflectedHilbertKernel_holomorphic hfieldDomain hfield
  let γ : Fin ((m + 1) + (m + 1)) → ℕ :=
    Fin.append α β
  have hcoeff :=
    cauchyCoeffPolydisc_eq_of_eventuallyEq
      (m := (m + 1) + (m + 1)) (by omega)
      hscalarRadius hfieldRadius
      hscalarDomain hkernelOpen
      hscalarClosed hkernelClosed
      hscalar hkernel hlocal γ
  have hradius :
      Fin.append
          (fun _ : Fin (m + 1) => fieldRadius)
          (fun _ : Fin (m + 1) => fieldRadius) =
        (fun _ : Fin ((m + 1) + (m + 1)) => fieldRadius) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  calc
    SCV.cauchyCoeffPolydisc scalar
        (reflectedCauchyCenter center)
        (fun _ => scalarRadius) (Fin.append α β) =
      SCV.cauchyCoeffPolydisc
        (reflectedHilbertKernel field)
        (reflectedCauchyCenter center)
        (fun _ => fieldRadius) (Fin.append α β) :=
      hcoeff
    _ =
      SCV.cauchyCoeffPolydisc
        (reflectedHilbertKernel field)
        (reflectedCauchyCenter center)
        (Fin.append
          (fun _ => fieldRadius) (fun _ => fieldRadius))
        (Fin.append α β) := by
      rw [hradius]
    _ = _ :=
      cauchyCoeffPolydisc_reflectedHilbertKernel_append
        hfieldRadius hfieldDomain hfieldClosed hfield α β

end OSIIChapterV
end OSReconstruction
