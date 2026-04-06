import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum

/-!
# Compact-Approximation Support for Boundary-Value Positivity

This file isolates the compact-approximation continuity package used on the
OS-II theorem-3 route. The goal is to keep the public boundary-value frontier
small while allowing the finite-sum convergence proof to compile behind a
separate import.
-/

noncomputable section

open scoped Classical NNReal
open BigOperators Finset

variable {d : ℕ} [NeZero d]

private theorem borchersConj_continuous_bvt {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
  let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := fun y i => y (Fin.rev i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y i => y (Fin.rev i)
      left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i)
      continuous_invFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i) }
  let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
  have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
    intro f
    ext x
    simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.reverse_apply, revCLE]
  have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
    let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzMap.conj
        map_add' := fun f g => by
          ext x
          simp [SchwartzMap.conj_apply]
        map_smul' := fun c f => by
          simpa using (SchwartzMap.conj_smul (c := (c : ℂ)) f) }
    exact Seminorm.continuous_from_bounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      conjL (fun q => by
        rcases q with ⟨k, l⟩
        refine ⟨{(k, l)}, 1, ?_⟩
        intro f
        simpa [Finset.sup_singleton] using SchwartzMap.seminorm_conj_le k l f)
  show Continuous (fun f => (revCLM f).conj)
  exact hconj_cont.comp revCLM.continuous |>.congr (fun f => by
    show (revCLM f).conj = f.borchersConj
    rw [hrev]
    rfl)

private theorem conjTensorProduct_continuous_bvt {n m : ℕ} :
    Continuous
      (fun p : SchwartzNPoint d n × SchwartzNPoint d m => p.1.conjTensorProduct p.2) := by
  have hpair :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          (p.1.borchersConj, p.2)) :=
    ((borchersConj_continuous_bvt (d := d)).comp continuous_fst).prodMk continuous_snd
  let h :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          p.1.borchersConj.tensorProduct p.2) :=
    SchwartzMap.tensorProduct_continuous.comp hpair
  simpa [SchwartzMap.conjTensorProduct] using h

private noncomputable def compactApproxPositiveTimeBorchersTerm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (n m N : ℕ) : ℂ :=
  bvt_W OS lgc (n + m)
    ((((compactApproxPositiveTimeBorchers F N : PositiveTimeBorchersSequence d) :
        BorchersSequence d).funcs n).conjTensorProduct
      (((compactApproxPositiveTimeBorchers F N : PositiveTimeBorchersSequence d) :
        BorchersSequence d).funcs m))

private noncomputable def compactApproxPositiveTimeBorchersTermLimit
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (n m : ℕ) : ℂ :=
  bvt_W OS lgc (n + m)
    ((((F : BorchersSequence d).funcs n).conjTensorProduct
      ((F : BorchersSequence d).funcs m)))

private noncomputable def compactApproxPositiveTimeBorchersSelf
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) (N : ℕ) : ℂ :=
  WightmanInnerProduct d (bvt_W OS lgc)
    (compactApproxPositiveTimeBorchers F N : BorchersSequence d)
    (compactApproxPositiveTimeBorchers F N : BorchersSequence d)

private noncomputable def compactApproxPositiveTimeBorchersSelfLimit
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) : ℂ :=
  WightmanInnerProduct d (bvt_W OS lgc)
    (F : BorchersSequence d) (F : BorchersSequence d)

set_option maxHeartbeats 4000000 in
private theorem tendsto_compactApproxPositiveTimeBorchers_term
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (n m : ℕ) :
    Filter.Tendsto
      (compactApproxPositiveTimeBorchersTerm OS lgc F n m)
      Filter.atTop
      (nhds (compactApproxPositiveTimeBorchersTermLimit OS lgc F n m)) := by
  let approxF : ℕ → PositiveTimeBorchersSequence d := fun N => compactApproxPositiveTimeBorchers F N
  have hpair :
      Filter.Tendsto
        (fun N : ℕ =>
          ((((approxF N : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
              SchwartzNPoint d n),
            (((approxF N : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs m :
              SchwartzNPoint d m)))
        Filter.atTop
        (nhds
          ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n),
            (((F : BorchersSequence d).funcs m : SchwartzNPoint d m))))) := by
    simpa [approxF] using
      (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F n).prodMk_nhds
        (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F m)
  have hcont :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          bvt_W OS lgc (n + m) (p.1.conjTensorProduct p.2)) :=
    (bvt_W_continuous (d := d) OS lgc (n + m)).comp
      (conjTensorProduct_continuous_bvt (d := d) (n := n) (m := m))
  simpa [compactApproxPositiveTimeBorchersTerm, compactApproxPositiveTimeBorchersTermLimit, approxF] using
    (hcont.tendsto
      ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n),
        (((F : BorchersSequence d).funcs m : SchwartzNPoint d m))))).comp hpair

set_option maxHeartbeats 4000000 in
private theorem tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    Filter.Tendsto
      (compactApproxPositiveTimeBorchersSelf OS lgc F)
      Filter.atTop
      (nhds (compactApproxPositiveTimeBorchersSelfLimit OS lgc F)) := by
  let approxF : ℕ → PositiveTimeBorchersSequence d := fun N => compactApproxPositiveTimeBorchers F N
  have houter :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            ∑ m ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
              bvt_W OS lgc (n + m)
                ((((approxF N : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n).conjTensorProduct
                  (((approxF N : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs m)))
        Filter.atTop
        (nhds
          (∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            ∑ m ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
              bvt_W OS lgc (n + m)
                ((((F : BorchersSequence d).funcs n).conjTensorProduct
                  ((F : BorchersSequence d).funcs m))))) := by
    refine tendsto_finset_sum _ (fun n hn => ?_)
    refine tendsto_finset_sum _ (fun m hm => ?_)
    simpa [compactApproxPositiveTimeBorchersTerm, approxF] using
      tendsto_compactApproxPositiveTimeBorchers_term (d := d) OS lgc F n m
  simpa [compactApproxPositiveTimeBorchersSelf, compactApproxPositiveTimeBorchersSelfLimit,
    WightmanInnerProduct, approxF, compactApproxPositiveTimeBorchers] using
    houter

private theorem tendsto_wightmanInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : BorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))) :
    Filter.Tendsto
      (fun t : ℝ =>
        WightmanInnerProduct d (bvt_W OS lgc) F
          (timeShiftBorchers (d := d) t G))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (WightmanInnerProduct d (bvt_W OS lgc) F G)) := by
  unfold WightmanInnerProduct
  refine tendsto_finset_sum _ ?_
  intro n hn
  refine tendsto_finset_sum _ ?_
  intro m hm
  simpa [timeShiftBorchers_funcs] using
    tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc)
      (f := F.funcs n) (g := G.funcs m) (hg_compact := hG_compact m)

private theorem tendsto_osInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))) :
    Filter.Tendsto
      (fun t : ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d) t (G : BorchersSequence d)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OSInnerProduct d OS.S (F : BorchersSequence d) (G : BorchersSequence d))) := by
  let xF : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
  let ζ : ℝ → OSHilbertSpace OS := fun t =>
    if ht : 0 < t then
      osTimeShiftHilbert (d := d) OS lgc t ht xG
    else
      xG
  have hshift :
      Filter.Tendsto
        ζ
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds xG) := by
    simpa [ζ, xG] using
      tendsto_osTimeShiftHilbert_nhdsWithin_zero_of_isCompactSupport
        (d := d) (OS := OS) (lgc := lgc) G hG_compact
  let κ : ℝ → ℂ := fun t => @inner ℂ (OSHilbertSpace OS) _ xF (ζ t)
  have hinner :
      Filter.Tendsto
        κ
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (@inner ℂ (OSHilbertSpace OS) _ xF xG)) := by
    have hinner_cont :
        Continuous (fun y : OSHilbertSpace OS =>
          @inner ℂ (OSHilbertSpace OS) _ xF y) :=
      continuous_const.inner continuous_id
    have hinner0 :
        Filter.Tendsto
          ((fun y : OSHilbertSpace OS =>
            @inner ℂ (OSHilbertSpace OS) _ xF y) ∘ ζ)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (@inner ℂ (OSHilbertSpace OS) _ xF xG)) :=
      (hinner_cont.tendsto xG).comp hshift
    simpa [κ] using hinner0
  have hEq :
      κ
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d) t (G : BorchersSequence d))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    calc
      κ t
        = @inner ℂ (OSHilbertSpace OS) _ xF
            (osTimeShiftHilbert (d := d) OS lgc t ht' xG) := by
              simp [κ, ζ, ht']
      _ = OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) t (G : BorchersSequence d)) := by
            rw [osTimeShiftHilbert_coe (d := d) (OS := OS) (lgc := lgc) (t := t) (ht := ht')
              (x := (⟦G⟧ : OSPreHilbertSpace OS))]
            rw [UniformSpace.Completion.inner_coe]
            simp [osTimeShiftLinear, osTimeShift, PositiveTimeBorchersSequence.osInner,
              timeShiftPositiveTimeBorchers]
  exact Filter.Tendsto.congr' hEq <| by
    simpa [xF, xG, PositiveTimeBorchersSequence.osInner, OSPreHilbertSpace.inner_eq,
      UniformSpace.Completion.inner_coe] using hinner

/-- Compact-support truncations reduce theorem 3 to scalar time-shift kernel
comparisons on the compact approximants.

If the reconstructed Wightman kernel against the right Euclidean time-shifted
compact approximants agrees for every positive real time with the honest OS
semigroup matrix element, then positivity follows by taking `t → 0+` on each
compact approximant and finally `N → ∞`. -/
theorem bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hkernel :
      ∀ N (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          WightmanInnerProduct d (bvt_W OS lgc)
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d))
          =
          OSInnerProduct d OS.S
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  let approxF : ℕ → PositiveTimeBorchersSequence d := fun N => compactApproxPositiveTimeBorchers F N
  have hnonneg :
      ∀ N : ℕ,
        0 ≤
          (WightmanInnerProduct d (bvt_W OS lgc)
            (approxF N : BorchersSequence d)
            (approxF N : BorchersSequence d)).re := by
    intro N
    let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
    have hcompact :
        ∀ n,
          HasCompactSupport ((((F_N : BorchersSequence d).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)) := by
      intro n
      simpa [F_N] using
        compactApproxPositiveTimeBorchers_component_compact F N n
    have hW :
        Filter.Tendsto
          (fun t : ℝ =>
            WightmanInnerProduct d (bvt_W OS lgc)
              (F_N : BorchersSequence d)
              (timeShiftBorchers (d := d) t (F_N : BorchersSequence d)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (WightmanInnerProduct d (bvt_W OS lgc)
              (F_N : BorchersSequence d)
              (F_N : BorchersSequence d))) :=
      tendsto_wightmanInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport
        (d := d) OS lgc (F := (F_N : BorchersSequence d)) (G := (F_N : BorchersSequence d))
        hcompact
    have hOS :
        Filter.Tendsto
          (fun t : ℝ =>
            OSInnerProduct d OS.S
              (F_N : BorchersSequence d)
              (timeShiftBorchers (d := d) t (F_N : BorchersSequence d)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (OSInnerProduct d OS.S
              (F_N : BorchersSequence d) (F_N : BorchersSequence d))) :=
      tendsto_osInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport
        (d := d) OS lgc F_N F_N hcompact
    have hEq :
        (fun t : ℝ =>
          WightmanInnerProduct d (bvt_W OS lgc)
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d)))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun t : ℝ =>
          OSInnerProduct d OS.S
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [F_N] using hkernel N t ht
    have hOS' :
        Filter.Tendsto
          (fun t : ℝ =>
            WightmanInnerProduct d (bvt_W OS lgc)
              (F_N : BorchersSequence d)
              (timeShiftBorchers (d := d) t (F_N : BorchersSequence d)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (OSInnerProduct d OS.S
              (F_N : BorchersSequence d) (F_N : BorchersSequence d))) :=
      Filter.Tendsto.congr' hEq.symm hOS
    have hcmp :
        WightmanInnerProduct d (bvt_W OS lgc)
            (F_N : BorchersSequence d)
            (F_N : BorchersSequence d)
          =
        OSInnerProduct d OS.S
          (F_N : BorchersSequence d) (F_N : BorchersSequence d) :=
      tendsto_nhds_unique hW hOS'
    rw [hcmp]
    simpa [PositiveTimeBorchersSequence.osInner] using
      PositiveTimeBorchersSequence.osInner_nonneg_self OS F_N
  have hconv :=
    tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self
      (d := d) OS lgc F
  have hre :
      Filter.Tendsto
        (fun N : ℕ =>
          (WightmanInnerProduct d (bvt_W OS lgc)
            (approxF N : BorchersSequence d)
            (approxF N : BorchersSequence d)).re)
        Filter.atTop
        (nhds
          ((WightmanInnerProduct d (bvt_W OS lgc)
            (F : BorchersSequence d)
            (F : BorchersSequence d)).re)) := by
    simpa [Function.comp, approxF] using
      (Complex.continuous_re.continuousAt.tendsto.comp hconv)
  exact isClosed_Ici.mem_of_tendsto hre (Filter.Eventually.of_forall hnonneg)

/-- Compact-support truncations reduce theorem 3 for a general positive-time
Borchers vector to the honest compact-shell `hHlimit` seam.

This keeps the remaining content on the strict OS-II route: positivity follows
once the chosen scalar holomorphic `singleSplit_xiShift` trace is identified
with the reconstructed Wightman boundary values on the compact approximants. -/
theorem bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hHlimit :
      ∀ N : ℕ,
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
        ∀ n m (hm : 0 < m),
          Filter.Tendsto
            (fun t : ℝ =>
              bvt_singleSplit_xiShiftHolomorphicValue
                (d := d) OS lgc hm
                (((F_N : BorchersSequence d).funcs n))
                (F_N.ordered_tsupport n)
                (compactApproxPositiveTimeBorchers_component_compact F N n)
                (((F_N : BorchersSequence d).funcs m))
                (F_N.ordered_tsupport m)
                (compactApproxPositiveTimeBorchers_component_compact F N m) (t : ℂ))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds
              (bvt_W OS lgc (n + m)
                ((((F_N : BorchersSequence d).funcs n).conjTensorProduct
                  ((F_N : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  let approxF : ℕ → PositiveTimeBorchersSequence d := fun N => compactApproxPositiveTimeBorchers F N
  have hnonneg :
      ∀ N : ℕ,
        0 ≤
          (WightmanInnerProduct d (bvt_W OS lgc)
            (approxF N : BorchersSequence d)
            (approxF N : BorchersSequence d)).re := by
    intro N
    let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
    have hcompact :
        ∀ n,
          HasCompactSupport ((((F_N : BorchersSequence d).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)) := by
      intro n
      simpa [F_N] using
        compactApproxPositiveTimeBorchers_component_compact F N n
    have hlimitN0 := hHlimit N
    have hlimitN :
        ∀ n m (hm : 0 < m),
          Filter.Tendsto
            (fun t : ℝ =>
              bvt_singleSplit_xiShiftHolomorphicValue
                (d := d) OS lgc hm
                (((F_N : BorchersSequence d).funcs n))
                (F_N.ordered_tsupport n)
                (hcompact n)
                (((F_N : BorchersSequence d).funcs m))
                (F_N.ordered_tsupport m)
                (hcompact m) (t : ℂ))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds
              (bvt_W OS lgc (n + m)
                (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                  ((F_N : BorchersSequence d).funcs m)))) := by
      intro n m hm
      simpa [F_N, hcompact] using hlimitN0 n m hm
    have hnonnegN :
        0 ≤
          (WightmanInnerProduct d (bvt_W OS lgc)
            (F_N : BorchersSequence d)
            (F_N : BorchersSequence d)).re := by
      exact
        bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
          (d := d) OS lgc hherm F_N hcompact hlimitN
    simpa [F_N, approxF] using hnonnegN
  have hconv :=
    tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self
      (d := d) OS lgc F
  have hre :
      Filter.Tendsto
        (fun N : ℕ =>
          (WightmanInnerProduct d (bvt_W OS lgc)
            (approxF N : BorchersSequence d)
            (approxF N : BorchersSequence d)).re)
        Filter.atTop
        (nhds
          ((WightmanInnerProduct d (bvt_W OS lgc)
            (F : BorchersSequence d)
            (F : BorchersSequence d)).re)) := by
    simpa [Function.comp, approxF] using
      (Complex.continuous_re.continuousAt.tendsto.comp hconv)
  exact isClosed_Ici.mem_of_tendsto hre (Filter.Eventually.of_forall hnonneg)

/-- Compact-support truncations reduce theorem 3 even further: it is enough to
identify the chosen scalar holomorphic `singleSplit_xiShift` trace on positive
real times with the reconstructed Wightman pairing against the right
time-shifted compact approximants.

This is the honest compact-shell reformulation of the remaining OS-II theorem-3
gap. -/
theorem bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hreal :
      ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm
            (((F_N : BorchersSequence d).funcs n))
            (F_N.ordered_tsupport n)
            (compactApproxPositiveTimeBorchers_component_compact F N n)
            (((F_N : BorchersSequence d).funcs m))
            (F_N.ordered_tsupport m)
            (compactApproxPositiveTimeBorchers_component_compact F N m) (t : ℂ)
          =
            (bvt_W OS lgc (n + m)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs m))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  apply
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) OS lgc hherm F
  intro N
  let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
  dsimp
  intro n m hm
  simpa [F_N] using
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift
      (OS := OS) (lgc := lgc) (hm := hm)
      (f := ((F_N : BorchersSequence d).funcs n))
      (hf_ord := F_N.ordered_tsupport n)
      (hf_compact := compactApproxPositiveTimeBorchers_component_compact F N n)
      (g := ((F_N : BorchersSequence d).funcs m))
      (hg_ord := F_N.ordered_tsupport m)
      (hg_compact := compactApproxPositiveTimeBorchers_component_compact F N m)
      (fun t ht => by
        simpa [F_N] using hreal N n m hm t ht)

/-- Compact-support truncations reduce theorem 3 all the way to the explicit
positive-real Schwinger-vs-Wightman identification for the right-time-shifted
compact shells. -/
/-
Deprecated route note:

The hypothesis `hschw` below packages the old same-shell Schwinger/Wightman
comparison route. That hypothesis is mathematically false on the intended
theorem surface: the Euclidean/OS side is Laplace/semigroup data
(`e^{-ω_p t}`), while the reconstructed Wightman boundary-value side is a real
Minkowski time-translation/Fourier object (`e^{-i ω_p t}`).

This theorem is still a valid implication from its hypothesis and therefore
harmless to keep, but it should now be treated as dead-end legacy
infrastructure rather than an active theorem-3 route. -/
theorem bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hschw :
      ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            ((((F_N : BorchersSequence d).funcs n).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t
                ((F_N : BorchersSequence d).funcs m)))))
          =
            (bvt_W OS lgc (n + m)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs m))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  apply
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) OS lgc hherm F
  intro N
  let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
  dsimp
  intro n m hm
  simpa [F_N] using
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift
      (OS := OS) (lgc := lgc) (hm := hm)
      (f := ((F_N : BorchersSequence d).funcs n))
      (hf_ord := F_N.ordered_tsupport n)
      (hf_compact := compactApproxPositiveTimeBorchers_component_compact F N n)
      (g := ((F_N : BorchersSequence d).funcs m))
      (hg_ord := F_N.ordered_tsupport m)
      (hg_compact := compactApproxPositiveTimeBorchers_component_compact F N m)
      (fun t ht => by
        simpa [F_N] using hschw N n m hm t ht)
