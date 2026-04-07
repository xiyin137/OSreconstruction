/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase

/-!
# OS to Wightman Boundary Value Transfer Support

This module keeps only the valid boundary-value transfer and positivity-support
infrastructure needed by `OSToWightmanBoundaryValues.lean`.

The previous two-point same-shell comparison route has been removed. In
particular, this file does not contain any theorem family comparing `bvt_W`
and `OS.S` on the same test shell.

The surviving conditional comparison chain uses the standard OS bridge shape:

- the Wightman side is paired against `f.conjTensorProduct g`, i.e. the
  Borchers adjoint tensor on Minkowski test functions;
- the OS side is paired against `f.osConjTensorProduct g`, i.e. the Euclidean
  time-reflected tensor appearing in `OSInnerProduct`.

So the live comparison surface in this file is an ordered-positive-time
isometry statement, not a same-shell identity. The remaining unresolved content
is the `xiShift` boundary-value convergence hypothesis, not the theorem shape
itself.
-/

open scoped Classical NNReal
open BigOperators Finset

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {d : ℕ} [NeZero d]

def canonicalForwardConeDirection (n : ℕ) : Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ = 0 then (↑(k : ℕ) + 1 : ℝ) else 0

theorem canonicalForwardConeDirection_mem (n : ℕ) :
    InForwardCone d n (canonicalForwardConeDirection (d := d) n) := by
  let η₀ : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i
        split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  rw [inForwardCone_iff_mem_forwardConeAbs]
  intro k
  simp only []
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [canonicalForwardConeDirection, η₀, h]
  · by_cases hμ : μ = 0
    · simp [canonicalForwardConeDirection, η₀, hμ]
      have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hk_pos]
        simp
      rw [this]
      ring
    · simp [canonicalForwardConeDirection, η₀, hμ]


theorem bvt_F_negCanonical (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) -
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
  by
    intro x ε hε
    have hF_negCanonical :
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          starRingEnd ℂ
            ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
              (fun j μ =>
                ↑(x j μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
          (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
            (fun j μ =>
              ↑(x j μ) -
                ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I) := by
      rcases (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec with
        ⟨_hhol, hrest⟩
      rcases hrest with ⟨_hF_euclid, hrest⟩
      rcases hrest with ⟨_hF_perm, hrest⟩
      rcases hrest with ⟨_hF_trans, hrest⟩
      exact hrest.1
    change
      starRingEnd ℂ
        ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
          (fun j μ =>
            ↑(x j μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
      (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
        (fun j μ =>
          ↑(x j μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)
    simpa [bvt_F, canonicalForwardConeDirection] using
      hF_negCanonical x ε hε

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n -/

theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      InForwardCone d 0 η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  intro f
  let η0 : Fin 0 → Fin (d + 1) → ℝ := fun k => Fin.elim0 k
  have hη0 : InForwardCone d 0 η0 := by
    intro k
    exact Fin.elim0 k
  set I0 : ℂ := ∫ x : Fin 0 → Fin (d + 1) → ℝ,
      F_0 (fun k => wickRotatePoint (x k)) * (f x)
  have hconst :
      ∀ ε : ℝ,
        (∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) * (f x)) = I0 := by
    intro ε
    unfold I0
    congr 1
    ext x
    have hz : (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) =
        (fun k => wickRotatePoint (x k)) := by
      funext k
      exact Fin.elim0 k
    simp [hz]
  have hBV0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W_0 f)) := by
    simpa [hconst] using hBV f η0 hη0
  have hI0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I0) :=
    tendsto_const_nhds
  have hW0 : W_0 f = I0 :=
    tendsto_nhds_unique hBV0 hI0
  let f0 : ZeroDiagonalSchwartz d 0 := ⟨f, by
    intro k x hx
    rcases hx with ⟨i, _, _, _⟩
    exact Fin.elim0 i⟩
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f0 := by simpa [I0, f0] using (hEuclid f0).symm
    _ = f 0 := lgc.normalized_zero f0

/-- If the left factor is concentrated in degree `0`, the full compact ordered
positive-time comparison against an arbitrary right Borchers vector is already
formal: the `m = 0` term is normalization, and every `m > 0` term is the
singleton/singleton `xiShift` comparison already established above. -/
theorem bvt_wightmanInner_zero_left_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzNPoint d 0)
    (hg_ord : tsupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ))
    (G : PositiveTimeBorchersSequence d)
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hWlimit :
      ∀ m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (0 + m),
              bvt_F OS lgc (0 + m)
                  (xiShift ⟨0, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((g.osConjTensorProduct ((G : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (0 + m)
              (g.conjTensorProduct ((G : BorchersSequence d).funcs m))))) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (BorchersSequence.single 0 g) (G : BorchersSequence d)
      =
    PositiveTimeBorchersSequence.osInner OS
      (PositiveTimeBorchersSequence.single 0 g hg_ord) G := by
  rw [WightmanInnerProduct_eq_sum_right_singles (d := d) (W := bvt_W OS lgc)
    (bvt_W_linear (d := d) OS lgc) (F := BorchersSequence.single 0 g)
    (G := (G : BorchersSequence d))]
  rw [PositiveTimeBorchersSequence.osInner_eq_sum_right_singles (d := d) OS
    (PositiveTimeBorchersSequence.single 0 g hg_ord) G]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    let x0 : NPointDomain d 0 := 0
    have hconj0 : g.borchersConj = g.osConj := by
      ext x
      have hx : x = x0 := by
        funext i
        exact Fin.elim0 i
      subst hx
      have harg : (fun i => x0 (Fin.rev i)) = timeReflectionN d x0 := by
        ext i μ
        exact Fin.elim0 i
      rw [SchwartzMap.borchersConj_apply, SchwartzNPoint.osConj_apply]
      simpa [harg]
    have hvanish0 :
        VanishesToInfiniteOrderOnCoincidence
          (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) := by
      intro k x hx
      rcases hx with ⟨i, _, _, _⟩
      exact Fin.elim0 i
    have hW0_eval :
        bvt_W OS lgc 0 (g.conjTensorProduct ((G : BorchersSequence d).funcs 0))
          =
        (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
      simpa [x0] using
        bv_zero_point_is_evaluation (d := d) OS lgc
          (bvt_W OS lgc 0) (bvt_F OS lgc 0)
          (bvt_boundary_values OS lgc 0)
          (bvt_euclidean_restriction (d := d) OS lgc 0)
          (g.conjTensorProduct ((G : BorchersSequence d).funcs 0))
    calc
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g)
          (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0))
        =
          bvt_W OS lgc 0
            (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) := by
              simpa using
                WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
                  (bvt_W_linear (d := d) OS lgc) 0 0 g ((G : BorchersSequence d).funcs 0)
      _ =
          (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
            exact hW0_eval
      _ =
          (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
            simpa [SchwartzMap.conjTensorProduct, SchwartzNPoint.osConjTensorProduct, hconj0]
      _ =
          (ZeroDiagonalSchwartz.ofClassical
            (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0))).1 x0 := by
              simpa using congrArg
                (fun h : SchwartzNPoint d 0 => h x0)
                (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                  (f := g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) hvanish0).symm
      _ =
          OS.S 0
            (ZeroDiagonalSchwartz.ofClassical
              (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0))) := by
                symm
                simpa [x0] using lgc.normalized_zero
                  (ZeroDiagonalSchwartz.ofClassical
                    (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)))
      _ =
          OSInnerProduct d OS.S
            (BorchersSequence.single 0 g)
            (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0)) := by
              symm
              simpa using
                OSInnerProduct_single_single (d := d) OS.S OS.E0_linear
                  0 0 g ((G : BorchersSequence d).funcs 0)
      _ =
          PositiveTimeBorchersSequence.osInner OS
            (PositiveTimeBorchersSequence.single 0 g hg_ord)
            (PositiveTimeBorchersSequence.single 0 ((G : BorchersSequence d).funcs 0)
              (G.ordered_tsupport 0)) := by
              rfl
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    simpa using
      bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
        (d := d) (OS := OS) (lgc := lgc) 0 m hm_pos
        g hg_ord hg_compact
        (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m) (hG_compact m)
        (hWlimit m hm_pos)

/-- The new degree-`0`-on-the-left comparison can be flipped to the missing
degree-`0`-on-the-right pointwise comparison once Hermiticity of `bvt_W` is
available. This is the exact shape needed for the remaining `m = 0` positivity
seam.

Important: this is still the standard OS bridge surface

`bvt_W (f.conjTensorProduct g) = OS.S (ofClassical (f.osConjTensorProduct g))`

and not a deleted same-shell identity. -/
theorem bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (n : ℕ) (hn : 0 < n)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d 0)
    (hg_ord : tsupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ))
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (0 + n),
            bvt_F OS lgc (0 + n)
                (xiShift ⟨0, Nat.lt_add_of_pos_right hn⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((g.osConjTensorProduct f) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (0 + n)
            (g.conjTensorProduct f)))) :
    bvt_W OS lgc n (f.conjTensorProduct g) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  let Fn : PositiveTimeBorchersSequence d := PositiveTimeBorchersSequence.single n f hf_ord
  have hFn_compact :
      ∀ m,
        HasCompactSupport ((((Fn : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)) := by
    intro m
    by_cases hm : m = n
    · subst hm
      simpa [Fn] using hf_compact
    · simpa [Fn, BorchersSequence.single_funcs_ne hm] using
        (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d m → ℂ))
  have hFn_limit :
      ∀ m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (0 + m),
              bvt_F OS lgc (0 + m)
                  (xiShift ⟨0, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((g.osConjTensorProduct ((Fn : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (0 + m)
              (g.conjTensorProduct ((Fn : BorchersSequence d).funcs m)))) := by
    intro m hm
    by_cases hmn : m = n
    · subst hmn
      simpa [Fn] using hWlimit
    · have hfunc0 : ((Fn : BorchersSequence d).funcs m) = 0 := by
        simpa [Fn] using (BorchersSequence.single_funcs_ne hmn f)
      rw [hfunc0, SchwartzNPoint.osConjTensorProduct_zero_right]
      have htarget :
          bvt_W OS lgc (0 + m) (g.conjTensorProduct (0 : SchwartzNPoint d m)) = 0 := by
        rw [SchwartzMap.conjTensorProduct_zero_right,
          (bvt_W_linear (d := d) OS lgc (0 + m)).map_zero]
      rw [htarget]
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
  have hleft :
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g) (Fn : BorchersSequence d)
        =
      PositiveTimeBorchersSequence.osInner OS
        (PositiveTimeBorchersSequence.single 0 g hg_ord) Fn := by
    exact
      bvt_wightmanInner_zero_left_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
        (d := d) (OS := OS) (lgc := lgc) g hg_ord hg_compact Fn hFn_compact hFn_limit
  have hright :
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n f) (BorchersSequence.single 0 g)
        =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := by
    calc
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n f) (BorchersSequence.single 0 g)
        =
      starRingEnd ℂ
        (WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g) (BorchersSequence.single n f)) := by
            simpa using
              WightmanInnerProduct_hermitian_of (d := d) (W := bvt_W OS lgc)
                hherm (BorchersSequence.single n f) (BorchersSequence.single 0 g)
      _ =
      starRingEnd ℂ
        (PositiveTimeBorchersSequence.osInner OS
          (PositiveTimeBorchersSequence.single 0 g hg_ord) Fn) := by
            simpa [Fn] using congrArg (starRingEnd ℂ) hleft
      _ =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := by
            simpa [Fn] using
              (PositiveTimeBorchersSequence.osInner_hermitian OS Fn
                (PositiveTimeBorchersSequence.single 0 g hg_ord)).symm
  calc
    bvt_W OS lgc n (f.conjTensorProduct g)
      =
    WightmanInnerProduct d (bvt_W OS lgc)
      (BorchersSequence.single n f) (BorchersSequence.single 0 g) := by
        symm
        simpa using
          WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
            (bvt_W_linear (d := d) OS lgc) n 0 f g
    _ =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := hright
    _ =
      OSInnerProduct d OS.S (Fn : BorchersSequence d)
        (BorchersSequence.single 0 g) := by
          rfl
    _ = OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
          simpa [Fn] using
            OSInnerProduct_single_single (d := d) OS.S OS.E0_linear n 0 f g

/-- For compact ordered positive-time Borchers vectors, the componentwise
single-split `xiShift` shell comparisons imply the full self-pair comparison
once the remaining degree-`0` right component is discharged using Hermiticity.
This packages the exact repair used by the active positivity lane. -/
theorem bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((F : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F F := by
  have hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)))) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      let x0 : NPointDomain d 0 := 0
      have hconj0 :
          ((F : BorchersSequence d).funcs 0).borchersConj =
            ((F : BorchersSequence d).funcs 0).osConj := by
        ext x
        have hx : x = x0 := by
          funext i
          exact Fin.elim0 i
        subst hx
        have harg : (fun i => x0 (Fin.rev i)) = timeReflectionN d x0 := by
          ext i μ
          exact Fin.elim0 i
        rw [SchwartzMap.borchersConj_apply, SchwartzNPoint.osConj_apply]
        simpa [harg]
      have hvanish0 :
          VanishesToInfiniteOrderOnCoincidence
            (((F : BorchersSequence d).funcs 0).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)) := by
        intro k x hx
        rcases hx with ⟨i, _, _, _⟩
        exact Fin.elim0 i
      have hW0_eval :
          bvt_W OS lgc 0
            (((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))
            =
          ((((F : BorchersSequence d).funcs 0).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) x0 := by
        simpa [x0] using
          bv_zero_point_is_evaluation (d := d) OS lgc
            (bvt_W OS lgc 0) (bvt_F OS lgc 0)
            (bvt_boundary_values OS lgc 0)
            (bvt_euclidean_restriction (d := d) OS lgc 0)
            ((((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0)))
      calc
        bvt_W OS lgc 0
            (((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))
          =
            ((((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))) x0 := hW0_eval
        _ =
            ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0))) x0 := by
                simpa [SchwartzMap.conjTensorProduct, SchwartzNPoint.osConjTensorProduct, hconj0]
        _ =
            (ZeroDiagonalSchwartz.ofClassical
              (((F : BorchersSequence d).funcs 0).osConjTensorProduct
                ((F : BorchersSequence d).funcs 0))).1 x0 := by
                  simpa using congrArg
                    (fun h : SchwartzNPoint d 0 => h x0)
                    (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                      (f := ((F : BorchersSequence d).funcs 0).osConjTensorProduct
                        ((F : BorchersSequence d).funcs 0)) hvanish0).symm
        _ =
            OS.S 0 (ZeroDiagonalSchwartz.ofClassical
              ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
                ((F : BorchersSequence d).funcs 0)))) := by
                  symm
                  simpa [x0] using lgc.normalized_zero
                    (ZeroDiagonalSchwartz.ofClassical
                      ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
                        ((F : BorchersSequence d).funcs 0))))
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      exact
        bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian
          (d := d) (OS := OS) (lgc := lgc) hherm
          n hn
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n) (hF_compact n)
          (((F : BorchersSequence d).funcs 0))
          (F.ordered_tsupport 0) (hF_compact 0)
          (hWlimit 0 n hn)
  exact
    bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) F F hF_compact hF_compact hzero hWlimit

/-- The Hermitian repair immediately yields nonnegativity of the reconstructed
self-pair on the compact positive-time shell controlled by the componentwise
single-split `xiShift` limits. This is the exact positivity payoff of the
comparison lane before any approximation from general Borchers vectors. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((F : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  rw [bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
    (d := d) (OS := OS) (lgc := lgc) hherm F hF_compact hWlimit]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F


private theorem boundary_ray_translation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x i + a) =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  let aN : NPointDomain d n := fun _ => a
  let gfun : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f x
  have hga :
      (fun x : NPointDomain d n => gfun (x + aN)) =
        fun x : NPointDomain d n =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
    ext x
    calc
      gfun (x + aN)
          = F_n (fun k μ => ↑((x + aN) k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
              rfl
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
            congr
            ext k μ
            simp [aN, Pi.add_apply, add_sub_cancel_right]
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
            rfl
  rw [← hga, MeasureTheory.integral_add_right_eq_self gfun aN]
  simp only [gfun]
  congr 1
  ext x
  exact congrArg (fun z : ℂ => z * f x) (hF_inv a x η ε hε)

private theorem bv_translation_invariance_transfer_of_F_invariant
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  intro a f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun i => x i + a) := by
      congr 1
      ext x
      have hxg : g x = f (fun i => x i + a) := by
        simpa using hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => x i + a) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_translation_invariant_of_F_invariant (d := d) n F_n hF_inv a f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_translation_invariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  exact bv_translation_invariance_transfer_of_F_invariant (d := d) n W_n F_n hBV hF_inv

theorem integral_lorentz_eq_self_full {n : ℕ}
    (Λ : FullLorentzGroup d)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have habs : |Λ.val.det| = 1 := by
    rcases FullLorentzGroup.det_eq_pm_one Λ with hdet | hdet
    · rw [hdet]
      simp
    · rw [hdet]
      simp
  have hdet_ne : Λ.val.det ≠ 0 := by
    intro hzero
    rw [hzero] at habs
    norm_num at habs
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmv : (fun v => Λ.val.mulVec v) = Matrix.toLin' Λ.val := by
    ext v
    simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d + 1) → ℝ => Λ.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]
    constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [habs]
  let e : (Fin n → Fin (d + 1) → ℝ) ≃ᵐ (Fin n → Fin (d + 1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.mulVec (a i)
        invFun := fun a i => Λ⁻¹.val.mulVec (a i)
        left_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛinv_mul]
        right_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛ_mul_inv] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_Λ.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Λinv.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

private noncomputable def lorentzInvCLEquivFull
    (Λ : LorentzGroup d) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
    simpa using hΛinv_mul
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' (Λ⁻¹).val
          invFun := Matrix.toLin' Λ.val
          left_inv := fun v => by
            show (Matrix.toLin' Λ.val) ((Matrix.toLin' (Λ⁻¹).val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛ_mul_inv, Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' (Λ⁻¹).val) ((Matrix.toLin' Λ.val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛinv_mul, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

private noncomputable def lorentzCompSchwartzFull {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight
      (fun (_ : Fin n) => lorentzInvCLEquivFull (d := d) Λ)) f

private theorem lorentzCompSchwartzFull_apply {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartzFull (d := d) Λ f).toFun x =
      f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartzFull, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquivFull]
  rfl

private theorem boundary_ray_lorentz_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I))
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
    simpa using hΛinv_mul
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hΛinv_mul_full] using
      (integral_lorentz_eq_self_full (d := d) (n := n) Λ
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x ε hε] with x hx
    simp [hx]
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x := hcov.symm
    _ =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := hrewrite

theorem bv_lorentz_covariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hcanonical_pairing :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
    intro Λ f g ε hε hfg
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          simpa using
            boundary_ray_lorentz_invariant_of_F_invariant (d := d) n F_n
              hF_lorentz
              Λ f ε hε
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hcanonical_pairing Λ f g ε hε hfg
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_lorentz_covariance_transfer_of_fixed_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (Λ : LorentzGroup d)
    (hF_lorentz_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
            simpa using hΛinv_mul
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul_full] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_orthochronous
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ =>
            ↑((Matrix.mulVec Λ.val (x k)) μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ f g hfg
  have hF_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
    hF_lorentz Λ hΛ
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
            simpa using hΛinv_mul
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul_full] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_restricted_of_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d)
        (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := restricted_preserves_forward_cone Λ diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, lorentz_inv_mul_eq_one (d := d) Λ] using
        (integral_lorentz_eq_self (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x η ε hε] with x hx
      simp [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

theorem bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d),
        LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
          F_n (fun k μ => ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ_ortho f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := orthochronous_preserves_forward_cone (d := d) Λ hΛ_ortho diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
      have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
      rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
      rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
      exact h1
    have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
      simpa using hΛinv_mul
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, hΛinv_mul_full] using
        (integral_lorentz_eq_self_full (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ hΛ_ortho x ε hε] with x hx
      rw [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g


theorem bv_local_commutativity_transfer_of_swap_pairing (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_swapCanonical_pairing :
      ∀ (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, f.toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
        (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  intro i j f g hsupp hswap
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_swapCanonical_pairing i j f g ε hε hsupp hswap
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_hermitian_pairing_of_F_negCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      F_n (fun j => z (σ j)) = F_n z)
    (hF_trans : ∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
      F_n (fun j => z j + a) = F_n z)
    (hF_neg :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
        F_n (fun k μ =>
          ↑(x k μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
  let η := canonicalForwardConeDirection (d := d) n
  intro f g ε hε hfg
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := by
            intro x
            ext i μ
            simp [Ψfun]
          right_inv := by
            intro x
            ext i μ
            simp [Ψfun] }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hreflect :
      ∀ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
    intro x
    let a : Fin (d + 1) → ℂ := fun μ =>
      if μ = 0 then (((n : ℝ) + 1) * ε : ℂ) * Complex.I else 0
    let zrev : Fin n → Fin (d + 1) → ℂ := fun k μ =>
      ↑(x k μ) + ε * ↑(η (Fin.rev k) μ) * Complex.I
    have hshift :
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) =
          F_n zrev := by
      have hzrev :
          (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) = zrev := by
        funext k
        funext μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [a, zrev, η, canonicalForwardConeDirection, Fin.val_rev]
          ring_nf
        · simp [a, zrev, η, canonicalForwardConeDirection, hμ]
      calc
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I)
            =
          F_n (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) := by
              symm
              exact hF_trans _ a
        _ = F_n zrev := by rw [hzrev]
    have hperm :
        F_n zrev =
          F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
      simpa [zrev] using (hF_perm Fin.revPerm zrev).symm
    calc
      starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) := hF_neg x ε hε
      _ = F_n zrev := hshift
      _ = F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := hperm
  let h : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑((Ψfun x) k μ) + ε * ↑(η k μ) * Complex.I) * starRingEnd ℂ (f x)
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n, h x := by
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n, h (Ψ x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall hfg] with x _hxg
          have hxg : g x = starRingEnd ℂ (f (fun i => x (Fin.rev i))) := by
            simpa using hfg x
          rw [hxg]
          simp [h, Ψ, Ψfun]
      _ = ∫ x : NPointDomain d n, h x := by
        simpa [h, Ψ, Ψfun] using
          ((reverseNPoint_measurePreserving (d := d) (n := n)).integral_comp'
            (f := Ψ) (g := h))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
            rw [hrewrite]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall hreflect] with x hx
            have hx' :
                F_n (fun k μ => ↑(Ψfun x k μ) + ε * ↑(η k μ) * Complex.I) =
                  starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
              simpa [Ψfun] using hx.symm
            calc
              h x =
                starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
                  starRingEnd ℂ (f x) := by
                    simp [h, Ψfun, hx']
              _ =
                starRingEnd ℂ
                  ((F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * f x) := by
                    simp [map_mul, mul_comm]
    _ =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
            simpa using
              (_root_.integral_conj
                (f := fun x : NPointDomain d n =>
                  (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * f x))

private theorem bv_hermiticity_transfer_of_F_reflect
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_reflect : ∀ (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
      0 < ε →
      starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  intro f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            starRingEnd ℂ (f (Ψ x)) := by
      congr 1
      ext x
      have hxg : g x = starRingEnd ℂ (f (Ψ x)) := by
        simpa [Ψ, Ψfun] using hfg x
      rw [hxg]
    have hpattern :
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              starRingEnd ℂ (f (Ψ x)) := by
      simpa [Ψ, Ψfun] using
          (SCV.bv_reality_pattern (μ := MeasureTheory.volume)
          (F := fun x : NPointDomain d n =>
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          (f := f) (Ψ := Ψ)
          (by simpa [Ψ, Ψfun] using reverseNPoint_measurePreserving (d := d) (n := n))
          (fun x => by simpa [Ψ] using hΨ_invol x)
          (Filter.Eventually.of_forall <| by
            intro x
            simpa [Ψ, Ψfun] using hF_reflect x η ε hε))
    exact hrewrite.trans hpattern.symm
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm

theorem bv_timeReversal_transfer
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_timeReflect_pairing :
      ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (timeReflectionN d x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (timeReflectionN d x)) →
      W_n f = W_n g := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          simpa [η] using hF_timeReflect_pairing f ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_timeReversal :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  intro f ε hε
  have hTT_mul :
      (LorentzGroup.timeReversal (d := d)).val *
          (LorentzGroup.timeReversal (d := d)).val
        = 1 := by
    change Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) *
        Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0 <;> simp [Matrix.diagonal, hi0]
    · simp [Matrix.diagonal, hij]
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hTT_mul] using
      (integral_lorentz_eq_self_full (d := d) (n := n)
        (LorentzGroup.timeReversal (d := d))
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (y i))))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          exact hcov.symm
    _ =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards
            [Filter.Eventually.of_forall fun x =>
              hF_timeReversal x ε hε] with x hx
          rw [hx]

theorem bv_hermiticity_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_reflect_pairing :
      ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x))) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_reflect_pairing f g ε hε hfg
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm
