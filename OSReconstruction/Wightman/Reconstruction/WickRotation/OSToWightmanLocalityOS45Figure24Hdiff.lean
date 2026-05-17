import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving

/-!
# OS45 Figure 2-4 Hdiff Producer

This downstream companion is the Lean entry point for the direct
`os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` proof.  It contains only
proof-local algebra and the eventual Hdiff producer; it does not wrap an
assumed difference germ or common-boundary CLM.
-/

noncomputable section

open Complex Topology MeasureTheory Filter

namespace BHW

variable {d n : ℕ}

/-- Fixed-test boundary value for the ordinary OS-I `(4.1)` branch written in
the `extendF` model used by the Figure-2-4 charts. -/
private theorem ordinary41_fixed_test_boundaryValue_extendF
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (ψ : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (fun k μ =>
            (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) *
        ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc n ψ)) := by
  have hbvt :=
    bvt_boundary_values (d := d) OS lgc n ψ η hη
  refine hbvt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).1 hη
  have hscaled_abs : ε • η ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n ε hε η hη_abs
  have hz :
      (fun k μ =>
        (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        (fun k μ =>
          (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [Pi.smul_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
          bvt_F OS lgc n z := by
    intro Λ z hz
    have hΛz : BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z ∈
        BHW.ForwardTube d n :=
      BHW.ofReal_preserves_forwardTube Λ z hz
    have hcinv :=
      bvt_F_complexLorentzInvariant_forwardTube
        (d := d) OS lgc n (ComplexLorentzGroup.ofReal Λ) z
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
    simpa [BHW.complexLorentzAction] using hcinv
  have heq :
      BHW.extendF (bvt_F OS lgc n)
        (fun k μ =>
          (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) =
        bvt_F OS lgc n
          (fun k μ =>
            (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) := by
    exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv
      _ hz
  exact congrArg (fun c : ℂ => c * ψ x) heq.symm

/-- Moving-test boundary value for the ordinary OS-I `(4.1)` branch written in
the `extendF` model.  This is the ordinary moving-test input for the later
side-height/source comparison; it is still before the OS45 source-side
pullback, so it does not assert a side-transfer theorem. -/
private theorem ordinary41_moving_boundaryValue_extendF
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (εseq : α → ℝ)
    (hεseq : Filter.Tendsto εseq l (nhdsWithin 0 (Set.Ioi 0)))
    {fseq : α → SchwartzNPoint d n}
    {f0 : SchwartzNPoint d n}
    (hfseq : Filter.Tendsto fseq l (nhds f0)) :
    Filter.Tendsto
      (fun a : α => ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (fun k μ =>
            (x k μ : ℂ) + (εseq a : ℂ) *
              (η k μ : ℂ) * Complex.I) *
        fseq a x)
      l
      (nhds (bvt_W OS lgc n f0)) := by
  have hbvt :=
    bvt_boundary_values_moving
      (d := d) OS lgc n η hη εseq hεseq hfseq
  refine hbvt.congr' ?_
  have hpos : ∀ᶠ a in l, εseq a ∈ Set.Ioi (0 : ℝ) :=
    hεseq.eventually self_mem_nhdsWithin
  filter_upwards [hpos] with a ha
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).1 hη
  have hscaled_abs : εseq a • η ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n (εseq a) ha η hη_abs
  have hz :
      (fun k μ =>
        (x k μ : ℂ) + (εseq a : ℂ) *
          (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        (fun k μ =>
          (x k μ : ℂ) + (εseq a : ℂ) *
            (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [Pi.smul_apply, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
          bvt_F OS lgc n z := by
    intro Λ z hz
    have hΛz : BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z ∈
        BHW.ForwardTube d n :=
      BHW.ofReal_preserves_forwardTube Λ z hz
    have hcinv :=
      bvt_F_complexLorentzInvariant_forwardTube
        (d := d) OS lgc n (ComplexLorentzGroup.ofReal Λ) z
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
    simpa [BHW.complexLorentzAction] using hcinv
  have heq :
      BHW.extendF (bvt_F OS lgc n)
        (fun k μ =>
          (x k μ : ℂ) + (εseq a : ℂ) *
            (η k μ : ℂ) * Complex.I) =
        bvt_F OS lgc n
          (fun k μ =>
            (x k μ : ℂ) + (εseq a : ℂ) *
              (η k μ : ℂ) * Complex.I) := by
    exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv _ hz
  exact congrArg (fun c : ℂ => c * fseq a x) heq.symm

/-- Fixed-test boundary value for the genuine raw OS-I `(4.12)` seed.

This is one of the two real side-height leaves used inside the eventual
`os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` producer.  It proves the
raw adjacent seed limit directly from the selected OS boundary-value theorem
and the source-label change of variables; it does not introduce a transported
adjacent branch, `Wadj`, `Hdiff`, or a common-boundary packet. -/
private theorem raw412_fixed_test_boundaryValue
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hητ : (fun k μ => η (τ k) μ) ∈ ForwardConeAbs d n) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I)) *
        ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm ψ))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ :=
    fun k μ => η (τ k) μ
  let ψτ : SchwartzNPoint d n :=
    BHW.permuteSchwartz (d := d) τ.symm ψ
  have hbvt :
      Filter.Tendsto
        (fun ε : ℝ => ∫ y : NPointDomain d n,
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (ε : ℂ) * (ητ k μ : ℂ) * Complex.I) *
          ψτ y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n ψτ)) := by
    exact bvt_boundary_values (d := d) OS lgc n ψτ ητ
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) ητ).2
        (by simpa [ητ] using hητ))
  refine hbvt.congr' ?_
  filter_upwards with ε
  have hperm :=
    BHW.integral_perm_eq_self (d := d) (n := n) τ
      (fun y : NPointDomain d n =>
        bvt_F OS lgc n
          (fun k μ =>
            (y k μ : ℂ) + (ε : ℂ) * (ητ k μ : ℂ) * Complex.I) *
        ψτ y)
  simpa [ητ, ψτ, BHW.permAct, BHW.permuteSchwartz_apply,
    Equiv.apply_symm_apply] using hperm.symm

/-- Moving-test boundary value for the genuine raw OS-I `(4.12)` seed.  This
is the adjacent moving-test input before terminal transport; the limit is the
permuted selected OS boundary functional, not a downstream deterministic
`extendF o permAct` branch. -/
private theorem raw412_moving_boundaryValue
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Equiv.Perm (Fin n))
    (η : Fin n → Fin (d + 1) → ℝ)
    (hητ : (fun k μ => η (τ k) μ) ∈ ForwardConeAbs d n)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (εseq : α → ℝ)
    (hεseq : Filter.Tendsto εseq l (nhdsWithin 0 (Set.Ioi 0)))
    {fseq : α → SchwartzNPoint d n}
    {f0 : SchwartzNPoint d n}
    (hfseq : Filter.Tendsto fseq l (nhds f0)) :
    Filter.Tendsto
      (fun a : α => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) *
        fseq a x)
      l
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm f0))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ :=
    fun k μ => η (τ k) μ
  let Lτ : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ
        (Fin (d + 1) → ℝ) τ.symm).toContinuousLinearEquiv)
  have hfseqτ :
      Filter.Tendsto (fun a : α => Lτ (fseq a)) l
        (nhds (Lτ f0)) :=
    (Lτ.continuous.tendsto f0).comp hfseq
  have hbvt :
      Filter.Tendsto
        (fun a : α => ∫ y : NPointDomain d n,
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (εseq a : ℂ) *
                (ητ k μ : ℂ) * Complex.I) *
          (Lτ (fseq a)) y)
        l
        (nhds (bvt_W OS lgc n (Lτ f0))) := by
    exact bvt_boundary_values_moving (d := d) OS lgc n ητ
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) ητ).2
        (by simpa [ητ] using hητ))
      εseq hεseq hfseqτ
  have hfun :
      (fun a : α => ∫ y : NPointDomain d n,
        bvt_F OS lgc n
          (fun k μ =>
            (y k μ : ℂ) + (εseq a : ℂ) *
              (ητ k μ : ℂ) * Complex.I) *
        (Lτ (fseq a)) y)
      =ᶠ[l]
      (fun a : α => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) *
        fseq a x) := by
    filter_upwards with a
    have hperm :=
      BHW.integral_perm_eq_self (d := d) (n := n) τ
        (fun y : NPointDomain d n =>
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (εseq a : ℂ) *
                (ητ k μ : ℂ) * Complex.I) *
          (Lτ (fseq a)) y)
    simpa [ητ, Lτ, BHW.permAct, BHW.permuteSchwartz_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Equiv.apply_symm_apply] using hperm.symm
  have hlim :
      bvt_W OS lgc n (Lτ f0) =
        bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm f0) := by
    simp [Lτ, BHW.permuteSchwartz]
  simpa [hlim] using hbvt.congr' hfun

private theorem finite_pointed_eqOn_nat
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} (N : ℕ → Set E) (f : ℕ → E → F) :
    ∀ len : ℕ,
      (∀ j, j ≤ len → IsOpen (N j)) →
      (∀ j, j ≤ len → z0 ∈ N j) →
      (∀ j, j < len →
        ∃ W : Set E,
          IsOpen W ∧ z0 ∈ W ∧ W ⊆ N j ∩ N (j + 1) ∧
          Set.EqOn (f j) (f (j + 1)) W) →
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N len ∧
        Set.EqOn (f 0) (f len) W
  | 0, hN_open, hzN, _hstep => by
      refine ⟨N 0, hN_open 0 le_rfl, hzN 0 le_rfl, ?_, ?_⟩
      · intro z hz
        exact ⟨hz, hz⟩
      · intro _z _hz
        rfl
  | len + 1, hN_open, hzN, hstep => by
      obtain ⟨Wprev, hWprev_open, hzWprev, hWprev_sub, hWprev_eq⟩ :=
        finite_pointed_eqOn_nat (N := N) (f := f) len
          (fun j hj => hN_open j (Nat.le_trans hj (Nat.le_succ len)))
          (fun j hj => hzN j (Nat.le_trans hj (Nat.le_succ len)))
          (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self len)))
      obtain ⟨Wedge, hWedge_open, hzWedge, hWedge_sub, hWedge_eq⟩ :=
        hstep len (Nat.lt_succ_self len)
      refine
        ⟨Wprev ∩ Wedge, hWprev_open.inter hWedge_open,
          ⟨hzWprev, hzWedge⟩, ?_, ?_⟩
      · intro z hz
        exact ⟨(hWprev_sub hz.1).1, (hWedge_sub hz.2).2⟩
      · intro z hz
        exact (hWprev_eq hz.1).trans (hWedge_eq hz.2)

private theorem finite_pointed_eqOn_fin
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {len : ℕ}
    (N : Fin (len + 1) → Set E) (f : Fin (len + 1) → E → F)
    (hN_open : ∀ j, IsOpen (N j))
    (hzN : ∀ j, z0 ∈ N j)
    (hstep :
      ∀ j : Fin len,
        ∃ W : Set E,
          IsOpen W ∧ z0 ∈ W ∧
          W ⊆ N (Fin.castSucc j) ∩ N (Fin.succ j) ∧
          Set.EqOn (f (Fin.castSucc j)) (f (Fin.succ j)) W) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N (Fin.last len) ∧
      Set.EqOn (f 0) (f (Fin.last len)) W := by
  classical
  let Nnat : ℕ → Set E := fun j =>
    if h : j ≤ len then N ⟨j, Nat.lt_succ_of_le h⟩ else ∅
  let fnat : ℕ → E → F := fun j =>
    if h : j ≤ len then f ⟨j, Nat.lt_succ_of_le h⟩ else f 0
  obtain ⟨W, hW_open, hzW, hW_sub, hW_eq⟩ :=
    finite_pointed_eqOn_nat (N := Nnat) (f := fnat) len
      (fun j hj => by
        dsimp [Nnat]
        rw [dif_pos hj]
        exact hN_open ⟨j, Nat.lt_succ_of_le hj⟩)
      (fun j hj => by
        dsimp [Nnat]
        rw [dif_pos hj]
        exact hzN ⟨j, Nat.lt_succ_of_le hj⟩)
      (fun j hj => by
        have hj_le : j ≤ len := Nat.le_of_lt hj
        have hjs_le : j + 1 ≤ len := Nat.succ_le_of_lt hj
        rcases hstep ⟨j, hj⟩ with
          ⟨Wj, hWj_open, hzWj, hWj_sub, hWj_eq⟩
        refine ⟨Wj, hWj_open, hzWj, ?_, ?_⟩
        · simpa [Nnat, hj_le, hjs_le] using hWj_sub
        · simpa [fnat, hj_le, hjs_le] using hWj_eq)
  refine ⟨W, hW_open, hzW, ?_, ?_⟩
  · simpa [Nnat] using hW_sub
  · simpa [fnat] using hW_eq

private structure PointedSeedEdge
    {E F : Type*} [TopologicalSpace E]
    (z0 : E) (N₁ N₂ : Set E) (f₁ f₂ : E → F) where
  W : Set E
  W_open : IsOpen W
  z0_mem : z0 ∈ W
  W_sub : W ⊆ N₁ ∩ N₂
  eqOn : Set.EqOn f₁ f₂ W

private def PointedSeedEdge.symm
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {N₁ N₂ : Set E} {f₁ f₂ : E → F}
    (h : PointedSeedEdge z0 N₁ N₂ f₁ f₂) :
    PointedSeedEdge z0 N₂ N₁ f₂ f₁ := by
  exact
    { W := h.W
      W_open := h.W_open
      z0_mem := h.z0_mem
      W_sub := by
        intro z hz
        exact ⟨(h.W_sub hz).2, (h.W_sub hz).1⟩
      eqOn := by
        intro z hz
        exact (h.eqOn hz).symm }

private theorem pointed_seed_gallery_endpoint_seed
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {len : ℕ}
    (N : Fin (len + 1) → Set E) (f : Fin (len + 1) → E → F)
    (hN_open : ∀ j, IsOpen (N j))
    (hzN : ∀ j, z0 ∈ N j)
    (hstep :
      ∀ j : Fin len,
        PointedSeedEdge z0
          (N (Fin.castSucc j)) (N (Fin.succ j))
          (f (Fin.castSucc j)) (f (Fin.succ j))) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N (Fin.last len) ∧
      Set.EqOn (f 0) (f (Fin.last len)) W :=
  finite_pointed_eqOn_fin N f hN_open hzN
    (fun j =>
      let E := hstep j
      ⟨E.W, E.W_open, E.z0_mem, E.W_sub, E.eqOn⟩)

private structure PointedMetricBranchChart
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  branch : E → F
  holo : DifferentiableOn ℂ branch (Metric.ball center radius)

private def PointedMetricBranchChart.carrier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) : Set E :=
  Metric.ball A.center A.radius

private theorem PointedMetricBranchChart.carrier_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) :
    IsOpen A.carrier := by
  simp [PointedMetricBranchChart.carrier]

private theorem PointedMetricBranchChart.center_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) :
    A.center ∈ A.carrier := by
  simpa [PointedMetricBranchChart.carrier] using
    Metric.mem_ball_self (x := A.center) A.radius_pos

private theorem PointedMetricBranchChart.restrict_center
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F)
    {z0 : E} (hz0 : z0 ∈ A.carrier) :
    ∃ A0 : PointedMetricBranchChart E F,
      A0.center = z0 ∧
      A0.carrier ⊆ A.carrier ∧
      Nonempty
        (PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch) := by
  rcases
      SCV.exists_metric_ball_differentiableOn_subset_of_mem_open
        A.carrier_open hz0
        (by simpa [PointedMetricBranchChart.carrier] using A.holo) with
    ⟨r, hr_pos, hball_sub, hholo⟩
  let A0 : PointedMetricBranchChart E F :=
    { center := z0
      radius := r
      radius_pos := hr_pos
      branch := A.branch
      holo := by
        simpa [PointedMetricBranchChart.carrier] using hholo }
  refine ⟨A0, rfl, ?_, ⟨?_⟩⟩
  · simpa [A0, PointedMetricBranchChart.carrier] using hball_sub
  · refine
      { W := A0.carrier
        W_open := A0.carrier_open
        z0_mem := by
          simpa [A0] using A0.center_mem
        W_sub := ?_
        eqOn := ?_ }
    · intro z hz
      exact ⟨by simpa [A0, PointedMetricBranchChart.carrier] using
        hball_sub hz, hz⟩
    · intro _z _hz
      rfl

private theorem pointed_seed_gallery_endpoint_seed_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} {len : ℕ}
    (chart : Fin (len + 1) → PointedMetricBranchChart E F)
    (hz : ∀ j, z0 ∈ (chart j).carrier)
    (hstep :
      ∀ j : Fin len,
        PointedSeedEdge z0
          ((chart (Fin.castSucc j)).carrier)
          ((chart (Fin.succ j)).carrier)
          ((chart (Fin.castSucc j)).branch)
          ((chart (Fin.succ j)).branch)) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ (chart 0).carrier ∩ (chart (Fin.last len)).carrier ∧
        Set.EqOn (chart 0).branch (chart (Fin.last len)).branch W :=
  pointed_seed_gallery_endpoint_seed
    (fun j => (chart j).carrier)
    (fun j => (chart j).branch)
    (fun j => (chart j).carrier_open)
    hz hstep

private theorem pointed_seed_via_common_center
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB NC : Set E} {fA fB fC : E → F}
    (hAC :
      ∃ WA : Set E,
        IsOpen WA ∧ z0 ∈ WA ∧ WA ⊆ NA ∩ NC ∧ Set.EqOn fA fC WA)
    (hBC :
      ∃ WB : Set E,
        IsOpen WB ∧ z0 ∈ WB ∧ WB ⊆ NB ∩ NC ∧ Set.EqOn fB fC WB) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W := by
  rcases hAC with ⟨WA, hWA_open, hzWA, hWA_sub, hWA_eq⟩
  rcases hBC with ⟨WB, hWB_open, hzWB, hWB_sub, hWB_eq⟩
  refine ⟨WA ∩ WB, hWA_open.inter hWB_open, ⟨hzWA, hzWB⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(hWA_sub hz.1).1, (hWB_sub hz.2).1⟩
  · intro z hz
    exact (hWA_eq hz.1).trans ((hWB_eq hz.2).symm)

private structure PointedCommonCenterGalleryPair
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (z0 : E) where
  leftLen : ℕ
  rightLen : ℕ
  center : PointedMetricBranchChart E F
  left : Fin (leftLen + 1) → PointedMetricBranchChart E F
  right : Fin (rightLen + 1) → PointedMetricBranchChart E F
  left_last_eq_center : left (Fin.last leftLen) = center
  right_last_eq_center : right (Fin.last rightLen) = center
  left_mem : ∀ j, z0 ∈ (left j).carrier
  right_mem : ∀ j, z0 ∈ (right j).carrier
  left_step :
    ∀ j : Fin leftLen,
      PointedSeedEdge z0
        ((left (Fin.castSucc j)).carrier)
        ((left (Fin.succ j)).carrier)
        ((left (Fin.castSucc j)).branch)
        ((left (Fin.succ j)).branch)
  right_step :
    ∀ j : Fin rightLen,
      PointedSeedEdge z0
        ((right (Fin.castSucc j)).carrier)
        ((right (Fin.succ j)).carrier)
        ((right (Fin.castSucc j)).branch)
        ((right (Fin.succ j)).branch)

private theorem PointedCommonCenterGalleryPair.endpoint_seed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (G : PointedCommonCenterGalleryPair E F z0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ (G.left 0).carrier ∩ (G.right 0).carrier ∧
        Set.EqOn (G.left 0).branch (G.right 0).branch W := by
  obtain ⟨WL, hWL_open, hzWL, hWL_sub, hWL_eq⟩ :=
    pointed_seed_gallery_endpoint_seed_chart G.left G.left_mem G.left_step
  obtain ⟨WR, hWR_open, hzWR, hWR_sub, hWR_eq⟩ :=
    pointed_seed_gallery_endpoint_seed_chart G.right G.right_mem G.right_step
  have hLC :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ (G.left 0).carrier ∩ G.center.carrier ∧
          Set.EqOn (G.left 0).branch G.center.branch W := by
    refine ⟨WL, hWL_open, hzWL, ?_, ?_⟩
    · intro z hz
      exact ⟨(hWL_sub hz).1, by
        simpa [G.left_last_eq_center] using (hWL_sub hz).2⟩
    · intro z hz
      simpa [G.left_last_eq_center] using hWL_eq hz
  have hRC :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ (G.right 0).carrier ∩ G.center.carrier ∧
          Set.EqOn (G.right 0).branch G.center.branch W := by
    refine ⟨WR, hWR_open, hzWR, ?_, ?_⟩
    · intro z hz
      exact ⟨(hWR_sub hz).1, by
        simpa [G.right_last_eq_center] using (hWR_sub hz).2⟩
    · intro z hz
      simpa [G.right_last_eq_center] using hWR_eq hz
  exact pointed_seed_via_common_center hLC hRC

private theorem pointed_seed_of_retargeted_common_center_gallery
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (A B A0 B0 : PointedMetricBranchChart E F)
    (edgeA : PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch)
    (edgeB : PointedSeedEdge z0 B.carrier B0.carrier B.branch B0.branch)
    (hA0B0 :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A0.carrier ∩ B0.carrier ∧ Set.EqOn A0.branch B0.branch W) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  rcases hA0B0 with ⟨WG, hWG_open, hzWG, hWG_sub, hWG_eq⟩
  refine
    ⟨edgeA.W ∩ (WG ∩ edgeB.W),
      edgeA.W_open.inter (hWG_open.inter edgeB.W_open),
      ⟨edgeA.z0_mem, hzWG, edgeB.z0_mem⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(edgeA.W_sub hz.1).1, (edgeB.W_sub hz.2.2).1⟩
  · intro z hz
    exact
      (edgeA.eqOn hz.1).trans
        ((hWG_eq hz.2.1).trans ((edgeB.eqOn hz.2.2).symm))

private theorem pointed_retargeted_gallery_pair_seed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} {A B A0 B0 : PointedMetricBranchChart E F}
    (edgeA : PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch)
    (edgeB : PointedSeedEdge z0 B.carrier B0.carrier B.branch B0.branch)
    (G : PointedCommonCenterGalleryPair E F z0)
    (hleft0 : G.left 0 = A0)
    (hright0 : G.right 0 = B0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  obtain ⟨WG, hWG_open, hzWG, hWG_sub, hWG_eq⟩ := G.endpoint_seed
  have hA0B0 :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A0.carrier ∩ B0.carrier ∧ Set.EqOn A0.branch B0.branch W := by
    refine ⟨WG, hWG_open, hzWG, ?_, ?_⟩
    · intro z hz
      exact ⟨by simpa [hleft0] using (hWG_sub hz).1,
        by simpa [hright0] using (hWG_sub hz).2⟩
    · intro z hz
      simpa [hleft0, hright0] using hWG_eq hz
  exact
    pointed_seed_of_retargeted_common_center_gallery
      A B A0 B0 edgeA edgeB hA0B0

private theorem pointed_metric_seed_of_restricted_gallery_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (A B : PointedMetricBranchChart E F)
    (hzA : z0 ∈ A.carrier) (hzB : z0 ∈ B.carrier)
    (hgrid :
      ∀ (A0 B0 : PointedMetricBranchChart E F),
        A0.center = z0 →
        A0.carrier ⊆ A.carrier →
        B0.center = z0 →
        B0.carrier ⊆ B.carrier →
        ∃ G : PointedCommonCenterGalleryPair E F z0,
          G.left 0 = A0 ∧ G.right 0 = B0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  rcases A.restrict_center hzA with
    ⟨A0, hA0_center, hA0_sub, ⟨edgeA⟩⟩
  rcases B.restrict_center hzB with
    ⟨B0, hB0_center, hB0_sub, ⟨edgeB⟩⟩
  rcases hgrid A0 B0 hA0_center hA0_sub hB0_center hB0_sub with
    ⟨G, hleft0, hright0⟩
  exact pointed_retargeted_gallery_pair_seed edgeA edgeB G hleft0 hright0

private theorem PointedMetricBranchChart.eqOn_inter_of_seed
    {p q : ℕ} {z0 : Fin p → Fin q → ℂ}
    (A B : PointedMetricBranchChart (Fin p → Fin q → ℂ) ℂ)
    (hseed :
      ∃ W : Set (Fin p → Fin q → ℂ),
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W) :
    Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) := by
  rcases hseed with ⟨W, hW_open, hzW, hW_sub, hW_eq⟩
  have hfull :
      Set.EqOn A.branch B.branch
        (Metric.ball A.center A.radius ∩ Metric.ball B.center B.radius) :=
    SCV.identity_theorem_product_inter_metric_ball_of_eqOn_open
      hW_open ⟨z0, hzW⟩
      (by simpa [PointedMetricBranchChart.carrier] using hW_sub)
      (by simpa [PointedMetricBranchChart.carrier] using A.holo)
      (by simpa [PointedMetricBranchChart.carrier] using B.holo)
      hW_eq
  simpa [PointedMetricBranchChart.carrier] using hfull

private theorem PointedMetricBranchChart.sub_eqOn_inter_of_two_seeds
    {p q : ℕ} {z0 : Fin p → Fin q → ℂ}
    (A B : PointedMetricBranchChart (Fin p → Fin q → ℂ) ℂ)
    {fA gA fB gB : (Fin p → Fin q → ℂ) → ℂ}
    (hfA : DifferentiableOn ℂ fA A.carrier)
    (hgA : DifferentiableOn ℂ gA A.carrier)
    (hfB : DifferentiableOn ℂ fB B.carrier)
    (hgB : DifferentiableOn ℂ gB B.carrier)
    (hf_seed :
      ∃ Wf : Set (Fin p → Fin q → ℂ),
        IsOpen Wf ∧ z0 ∈ Wf ∧
          Wf ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn fA fB Wf)
    (hg_seed :
      ∃ Wg : Set (Fin p → Fin q → ℂ),
        IsOpen Wg ∧ z0 ∈ Wg ∧
          Wg ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn gA gB Wg) :
    Set.EqOn
      (fun z => fA z - gA z)
      (fun z => fB z - gB z)
      (A.carrier ∩ B.carrier) := by
  rcases hf_seed with ⟨Wf, hWf_open, hzWf, hWf_sub, hf_eq⟩
  rcases hg_seed with ⟨Wg, hWg_open, hzWg, hWg_sub, hg_eq⟩
  have hfull :
      Set.EqOn
        (fun z => fA z - gA z)
        (fun z => fB z - gB z)
        (Metric.ball A.center A.radius ∩ Metric.ball B.center B.radius) :=
    SCV.identity_theorem_product_inter_metric_ball_sub_of_two_eqOn_open
      hWf_open hzWf
      (by simpa [PointedMetricBranchChart.carrier] using hWf_sub)
      hWg_open hzWg
      (by simpa [PointedMetricBranchChart.carrier] using hWg_sub)
      (by simpa [PointedMetricBranchChart.carrier] using hfA)
      (by simpa [PointedMetricBranchChart.carrier] using hgA)
      (by simpa [PointedMetricBranchChart.carrier] using hfB)
      (by simpa [PointedMetricBranchChart.carrier] using hgB)
      hf_eq hg_eq
  simpa [PointedMetricBranchChart.carrier] using hfull

private theorem pointed_seed_of_ambient_eqOn_models
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB M : Set E}
    {fA fB modelA modelB : E → F}
    (hNA_open : IsOpen NA) (hNB_open : IsOpen NB) (hM_open : IsOpen M)
    (hzA : z0 ∈ NA) (hzB : z0 ∈ NB) (hzM : z0 ∈ M)
    (hA_model : Set.EqOn fA modelA NA)
    (hB_model : Set.EqOn fB modelB NB)
    (hmodel : Set.EqOn modelA modelB M) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W := by
  refine
    ⟨NA ∩ (NB ∩ M), hNA_open.inter (hNB_open.inter hM_open),
      ⟨hzA, hzB, hzM⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨hz.1, hz.2.1⟩
  · intro z hz
    exact (hA_model hz.1).trans
      ((hmodel hz.2.2).trans ((hB_model hz.2.1).symm))

private noncomputable def pointed_seed_edge_of_exists
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB : Set E} {fA fB : E → F}
    (h :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W) :
    PointedSeedEdge z0 NA NB fA fB :=
  let W := Classical.choose h
  let hW := Classical.choose_spec h
  { W := W
    W_open := hW.1
    z0_mem := hW.2.1
    W_sub := hW.2.2.1
    eqOn := hW.2.2.2 }

private noncomputable def pointed_seed_edge_of_common_model
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB : Set E} {fA fB model : E → F}
    (hNA_open : IsOpen NA) (hNB_open : IsOpen NB)
    (hzA : z0 ∈ NA) (hzB : z0 ∈ NB)
    (hA_model : Set.EqOn fA model NA)
    (hB_model : Set.EqOn fB model NB) :
    PointedSeedEdge z0 NA NB fA fB :=
  pointed_seed_edge_of_exists
    (pointed_seed_of_ambient_eqOn_models
      hNA_open hNB_open isOpen_univ hzA hzB trivial
      hA_model hB_model (fun _ _ => rfl))

private def pointed_seed_edge_retarget_both
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB NA0 NB0 : Set E}
    {fA fB fA0 fB0 : E → F}
    (hA0 : PointedSeedEdge z0 NA NA0 fA fA0)
    (hAB : PointedSeedEdge z0 NA NB fA fB)
    (hB0 : PointedSeedEdge z0 NB NB0 fB fB0) :
    PointedSeedEdge z0 NA0 NB0 fA0 fB0 := by
  refine
    { W := hA0.W ∩ (hAB.W ∩ hB0.W)
      W_open := hA0.W_open.inter (hAB.W_open.inter hB0.W_open)
      z0_mem := ⟨hA0.z0_mem, hAB.z0_mem, hB0.z0_mem⟩
      W_sub := ?_
      eqOn := ?_ }
  · intro z hz
    exact ⟨(hA0.W_sub hz.1).2, (hB0.W_sub hz.2.2).2⟩
  · intro z hz
    exact (hA0.eqOn hz.1).symm.trans
      ((hAB.eqOn hz.2.1).trans (hB0.eqOn hz.2.2))

private noncomputable def flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {E : Set (BHW.OS45FlatCommonChartReal d n)}
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (A B : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (hzA :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ A.carrier)
    (hzB :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ B.carrier)
    (hA_model :
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier)
    (hB_model :
      Set.EqOn B.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) B.carrier) :
    PointedSeedEdge
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)))
      A.carrier B.carrier A.branch B.branch := by
  let hflat :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧
        IsPreconnected W ∧
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
        W ⊆
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W :=
      BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
        (d := d) hd OS lgc (P := P)
        hE_open hE_sub ys hys_mem hys_li x0 hx0 T hzero_plus hzero_minus
  let Wflat := Classical.choose hflat
  let hWflat := Classical.choose_spec hflat
  exact pointed_seed_edge_of_exists
    (pointed_seed_of_ambient_eqOn_models
      A.carrier_open B.carrier_open hWflat.1 hzA hzB hWflat.2.2.1
      hA_model hB_model hWflat.2.2.2.2)

private theorem zeroHeight_pairings_eq_common_of_sideLimits
    {ι α : Type*} {l : Filter ι} [NeBot l]
    {K : Set α} (hK_nonempty : K.Nonempty)
    {F G : ι → α → ℂ} {cF cG c : ℂ}
    (hF_zero : TendstoUniformlyOn F (fun _ : α => cF) l K)
    (hG_zero : TendstoUniformlyOn G (fun _ : α => cG) l K)
    (hF_common : TendstoUniformlyOn F (fun _ : α => c) l K)
    (hG_common : TendstoUniformlyOn G (fun _ : α => c) l K) :
    cF = c ∧ cG = c := by
  rcases hK_nonempty with ⟨η, hηK⟩
  have hFη_zero : Tendsto (fun eps => F eps η) l (𝓝 cF) := by
    simpa using hF_zero.tendsto_at hηK
  have hFη_common : Tendsto (fun eps => F eps η) l (𝓝 c) := by
    simpa using hF_common.tendsto_at hηK
  have hGη_zero : Tendsto (fun eps => G eps η) l (𝓝 cG) := by
    simpa using hG_zero.tendsto_at hηK
  have hGη_common : Tendsto (fun eps => G eps η) l (𝓝 c) := by
    simpa using hG_common.tendsto_at hηK
  exact
    ⟨tendsto_nhds_unique hFη_zero hFη_common,
      tendsto_nhds_unique hGη_zero hGη_common⟩

private abbrev OS45PointedChart (d n : ℕ) :=
  PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ

private structure OrdModelAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (OrdGlobal : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (A : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  eq_ord : Set.EqOn A.branch OrdGlobal A.carrier

private structure RawRetargetAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (A rawLocal : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  edge_to_raw :
    PointedSeedEdge z0 A.carrier rawLocal.carrier A.branch rawLocal.branch

private structure FlatMinusAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (A Cminus : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  to_Cminus_edge :
    PointedSeedEdge z0 A.carrier Cminus.carrier A.branch Cminus.branch

private structure FlatCrossingAtZ0
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (Cplus Cminus : OS45PointedChart d n) where
  E : Set (BHW.OS45FlatCommonChartReal d n)
  E_open : IsOpen E
  E_sub :
    E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  ys :
    Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ
  ys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n
  ys_li : LinearIndependent ℝ ys
  x0 : BHW.OS45FlatCommonChartReal d n
  x0_mem : x0 ∈ E
  T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ
  zero_plus :
    ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x)
      = T φ
  zero_minus :
    ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x)
      = T φ
  z0_flat :
    z0 =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed x0))
  z0_mem_plus : z0 ∈ Cplus.carrier
  z0_mem_minus : z0 ∈ Cminus.carrier
  plus_model :
    Set.EqOn Cplus.branch (BHW.extendF (bvt_F OS lgc n)) Cplus.carrier
  minus_model :
    Set.EqOn Cminus.branch
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z)) Cminus.carrier

private inductive LocalOverlapAtZ0
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (A0 B0 : OS45PointedChart d n) : Type where
  | ordinary
      (hA_ord : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
      (hB_ord : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0)
      (Ccommon : OS45PointedChart d n)
      (hCcommon_ord :
        OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) Ccommon) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | adjacent
      (rawLocal : OS45PointedChart d n)
      (hA_adj : RawRetargetAtZ0 d n z0 A0 rawLocal)
      (hB_adj : RawRetargetAtZ0 d n z0 B0 rawLocal)
      (hzRawLocal : z0 ∈ rawLocal.carrier) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | flat_plus_minus
      (Cplus Cminus : OS45PointedChart d n)
      (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
      (hA_plus : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
      (hB_minus : FlatMinusAtZ0 d n z0 B0 Cminus) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | flat_minus_plus
      (Cplus Cminus : OS45PointedChart d n)
      (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
      (hA_minus : FlatMinusAtZ0 d n z0 A0 Cminus)
      (hB_plus : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0

private theorem os45_pointed_gallery_pair_one_one
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B C : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzC : z0 ∈ C.carrier)
    (edgeAC : PointedSeedEdge z0 A.carrier C.carrier A.branch C.branch)
    (edgeBC : PointedSeedEdge z0 B.carrier C.carrier B.branch C.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then A else C
  let right : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then B else C
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzC]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzC]
  have hleft_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [left] using edgeAC
  have hright_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [right] using edgeBC
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 1
      rightLen := 1
      center := C
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem os45_pointed_gallery_pair_one_two
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B Cplus Cminus : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzPlus : z0 ∈ Cplus.carrier)
    (hzMinus : z0 ∈ Cminus.carrier)
    (edgeAPlus :
      PointedSeedEdge z0 A.carrier Cplus.carrier A.branch Cplus.branch)
    (edgeBMinus :
      PointedSeedEdge z0 B.carrier Cminus.carrier B.branch Cminus.branch)
    (edgeMinusPlus :
      PointedSeedEdge z0 Cminus.carrier Cplus.carrier
        Cminus.branch Cplus.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then A else Cplus
  let right : Fin (2 + 1) → OS45PointedChart d n :=
    fun j =>
      if (j : ℕ) = 0 then B else
        if (j : ℕ) = 1 then Cminus else Cplus
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzPlus]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzMinus, hzPlus]
  have hleft_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [left] using edgeAPlus
  have hright_step :
      ∀ j : Fin 2,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j
    · simpa [right] using edgeBMinus
    · simpa [right] using edgeMinusPlus
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 1
      rightLen := 2
      center := Cplus
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem os45_pointed_gallery_pair_two_one
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B Cplus Cminus : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzPlus : z0 ∈ Cplus.carrier)
    (hzMinus : z0 ∈ Cminus.carrier)
    (edgeAMinus :
      PointedSeedEdge z0 A.carrier Cminus.carrier A.branch Cminus.branch)
    (edgeMinusPlus :
      PointedSeedEdge z0 Cminus.carrier Cplus.carrier
        Cminus.branch Cplus.branch)
    (edgeBPlus :
      PointedSeedEdge z0 B.carrier Cplus.carrier B.branch Cplus.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (2 + 1) → OS45PointedChart d n :=
    fun j =>
      if (j : ℕ) = 0 then A else
        if (j : ℕ) = 1 then Cminus else Cplus
  let right : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then B else Cplus
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzMinus, hzPlus]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzPlus]
  have hleft_step :
      ∀ j : Fin 2,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j
    · simpa [left] using edgeAMinus
    · simpa [left] using edgeMinusPlus
  have hright_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [right] using edgeBPlus
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 2
      rightLen := 1
      center := Cplus
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem localOverlapAtZ0_galleryPair
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 : OS45PointedChart d n}
    (hcase : LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A0 ∧ G.right 0 = B0 := by
  classical
  have edge_symm
      {A B : OS45PointedChart d n}
      (h : PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch) :
      PointedSeedEdge z0 B.carrier A.carrier B.branch A.branch :=
    h.symm
  have edge_common
      {A B : OS45PointedChart d n}
      (hzA : z0 ∈ A.carrier) (hzB : z0 ∈ B.carrier)
      (hA_model :
        Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier)
      (hB_model :
        Set.EqOn B.branch (BHW.extendF (bvt_F OS lgc n)) B.carrier) :
      PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch :=
    pointed_seed_edge_of_common_model
      A.carrier_open B.carrier_open hzA hzB hA_model hB_model
  cases hcase with
  | ordinary hA_ord hB_ord Ccommon hCcommon_ord =>
      exact
        os45_pointed_gallery_pair_one_one A0 B0 Ccommon
          hA_ord.z0_mem hB_ord.z0_mem hCcommon_ord.z0_mem
          (edge_common hA_ord.z0_mem hCcommon_ord.z0_mem
            hA_ord.eq_ord hCcommon_ord.eq_ord)
          (edge_common hB_ord.z0_mem hCcommon_ord.z0_mem
            hB_ord.eq_ord hCcommon_ord.eq_ord)
  | adjacent rawLocal hA_adj hB_adj hzRawLocal =>
      exact
        os45_pointed_gallery_pair_one_one A0 B0 rawLocal
          hA_adj.z0_mem hB_adj.z0_mem hzRawLocal
          hA_adj.edge_to_raw hB_adj.edge_to_raw
  | flat_plus_minus Cplus Cminus hflat hA_plus hB_minus =>
      have hflat_edge :
          PointedSeedEdge z0 Cplus.carrier Cminus.carrier
            Cplus.branch Cminus.branch := by
        simpa [hflat.z0_flat] using
          flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
            (d := d) hd OS lgc (P := P)
            (E := hflat.E) hflat.E_open hflat.E_sub
            hflat.ys hflat.ys_mem hflat.ys_li hflat.x0 hflat.x0_mem
            hflat.T hflat.zero_plus hflat.zero_minus
            Cplus Cminus
            (by simpa [hflat.z0_flat] using hflat.z0_mem_plus)
            (by simpa [hflat.z0_flat] using hflat.z0_mem_minus)
            hflat.plus_model hflat.minus_model
      exact
        os45_pointed_gallery_pair_one_two A0 B0 Cplus Cminus
          hA_plus.z0_mem hB_minus.z0_mem
          hflat.z0_mem_plus hflat.z0_mem_minus
          (edge_common hA_plus.z0_mem hflat.z0_mem_plus
            hA_plus.eq_ord hflat.plus_model)
          hB_minus.to_Cminus_edge
          (edge_symm hflat_edge)
  | flat_minus_plus Cplus Cminus hflat hA_minus hB_plus =>
      have hflat_edge :
          PointedSeedEdge z0 Cplus.carrier Cminus.carrier
            Cplus.branch Cminus.branch := by
        simpa [hflat.z0_flat] using
          flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
            (d := d) hd OS lgc (P := P)
            (E := hflat.E) hflat.E_open hflat.E_sub
            hflat.ys hflat.ys_mem hflat.ys_li hflat.x0 hflat.x0_mem
            hflat.T hflat.zero_plus hflat.zero_minus
            Cplus Cminus
            (by simpa [hflat.z0_flat] using hflat.z0_mem_plus)
            (by simpa [hflat.z0_flat] using hflat.z0_mem_minus)
            hflat.plus_model hflat.minus_model
      exact
        os45_pointed_gallery_pair_two_one A0 B0 Cplus Cminus
          hA_minus.z0_mem hB_plus.z0_mem
          hflat.z0_mem_plus hflat.z0_mem_minus
          hA_minus.to_Cminus_edge
          (edge_symm hflat_edge)
          (edge_common hB_plus.z0_mem hflat.z0_mem_plus
            hB_plus.eq_ord hflat.plus_model)

private theorem OS45BHWJostHullData.OS412SeedWindow_pointedChart
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        (({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
          (BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ)) ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) A.carrier ∧
      A.branch A.center =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
  rcases H.OS412SeedWindow_initialSectorOverlap_metricBallChart OS lgc hx with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.ordinaryWick_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hwickW : (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center = (fun k => wickRotatePoint (x k)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
      A.branch A.center =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x k)
  rcases H.ordinaryWick_metricBallChartInWindow OS lgc hx hW_open hwickW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.ordinaryCommonEdge_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.ordinaryCommonEdge_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.adjacentCommonEdge_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.adjacentCommonEdge_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.commonEdgeDifference_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        ((BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)) -
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.commonEdgeDifference_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

/-- Direct OS I §4.5 producer for the local Figure-2-4 common-edge
holomorphic difference germ.

This is the hard Stage-A producer consumed by
`os45CommonEdge_localHorizontalDifference_representsZero_of_germ`.  The proof
enters the flat real-Jost crossing directly: the ordinary zero-height pairing
is supplied by the checked ordinary edge representation, while the selected
raw-adjacent zero-height pairing is the live OS-I side-height
branch/source-transfer block. -/
theorem os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  rcases hU_nonempty with ⟨u0, hu0⟩
  have hx0 : e u0 ∈ E := ⟨u0, hu0, rfl⟩
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  obtain ⟨ys, hys_mem, hys_li⟩ :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  have hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc (P := P) Tlocal
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact (hφE.trans hE_sub)
  have hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    let D : BHW.OS45Figure24SourceCutoffData P :=
      Classical.choice (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
    let ψ0 : SchwartzNPoint d n :=
      (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ).1
    let Kη : Set (BHW.OS45FlatCommonChartReal d n) := Set.range ys
    have hKη_nonempty : Kη.Nonempty := by
      exact ⟨ys 0, ⟨0, rfl⟩⟩
    have hKη_compact : IsCompact Kη := by
      simpa [Kη] using (Set.finite_range ys).isCompact
    have hKη_cone : Kη ⊆ BHW.os45FlatCommonChartCone d n := by
      rintro η ⟨j, rfl⟩
      exact hys_mem j
    have hψ0_compact :
        HasCompactSupport (ψ0 : NPointDomain d n → ℂ) := by
      simpa [ψ0, D, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_hasCompactSupport
          (1 : Equiv.Perm (Fin n)) φ
    have hψ0_suppU :
        tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ U := by
      simpa [ψ0, D,
        BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_tsupport_subset_image
          (1 : Equiv.Perm (Fin n)) φ hφE
    let Fplus :
        ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
      fun ε η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ) +
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x
    let Fminus :
        ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
      fun ε η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ) -
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x
    let cMinus : ℂ :=
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x
    have hplus_zero_uniform :
        TendstoUniformlyOn Fplus
          (fun _ : BHW.OS45FlatCommonChartReal d n => Tlocal φ)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      simpa [Fplus] using
        BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
          (d := d) hd OS lgc (P := P)
          Tlocal Kη hKη_compact hKη_cone
          φ hφ_compact (hφE.trans hE_sub)
          (hzero_plus φ hφ_compact hφE)
    have hminus_zero_uniform :
        TendstoUniformlyOn Fminus
          (fun _ : BHW.OS45FlatCommonChartReal d n => cMinus)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      have hF_cont :
          ContinuousOn
            (BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n))))
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
      have hside :
          ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K →
            K ⊆ BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) →
            ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
              Kη ⊆ BHW.os45FlatCommonChartCone d n →
              ∃ r : ℝ, 0 < r ∧
                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
                  (fun a => (x a : ℂ) +
                    ((-1 : ℝ) : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                    BHW.os45FlatCommonChartOmega d n
                      (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
        intro K hK hKE Kη hKη hKηC
        obtain ⟨r, hr_pos, hr_mem⟩ :=
          BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
            (d := d) hd (P := P) K hK hKE Kη hKη hKηC
        refine ⟨r, hr_pos, ?_⟩
        intro x hx η hη ε hε_pos hε_lt
        have hmem := (hr_mem x hx η hη ε hε_pos hε_lt).2
        simpa [sub_eq_add_neg, neg_mul, one_mul] using hmem
      simpa [Fminus, cMinus, sub_eq_add_neg, neg_mul, one_mul] using
        (SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
          (m := BHW.os45FlatCommonChartDim d n)
          (E := BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)))
          (C := BHW.os45FlatCommonChartCone d n)
          (Ωc := BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (BHW.isOpen_os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          hF_cont
          (BHW.os45FlatCommonChart_real_mem_omega_adjacent
            (d := d) hd (P := P))
          (-1 : ℝ) hside
          Kη hKη_compact hKη_cone φ hφ_compact (hφE.trans hE_sub)
          cMinus
          (by rfl))
    have hsource_uniform :=
      D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
        OS lgc Kη hKη_compact hKη_cone
        φ hφ_compact (hφE.trans hE_sub)
    have hminus_common :
        TendstoUniformlyOn Fminus
          (fun _ : BHW.OS45FlatCommonChartReal d n => Tlocal φ)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
      have hTlocal_source :
          Tlocal φ =
            J * OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ) := by
        have hplus_source :
            TendstoUniformlyOn Fplus
              (fun _ : BHW.OS45FlatCommonChartReal d n =>
                J * OS.S n (D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ))
              (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
          have hsource_plus := hsource_uniform.1
          dsimp [Fplus, J]
        rcases hKη_nonempty with ⟨η0, hη0⟩
        exact tendsto_nhds_unique
          (hplus_zero_uniform.tendsto_at hη0)
          (hplus_source.tendsto_at hη0)
      have hminus_source :
          TendstoUniformlyOn Fminus
            (fun _ : BHW.OS45FlatCommonChartReal d n =>
              J * OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ))
            (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
        have hsource_minus :=
          hsource_uniform.2.2.2
        dsimp [Fminus, J]
      simpa [hTlocal_source] using hminus_source
    have hcMinus :
        cMinus = Tlocal φ :=
      SCV.eq_zeroHeight_of_common_sideLimit hKη_nonempty
        hminus_zero_uniform hplus_zero_uniform
        hminus_common hplus_zero_uniform
    simpa [cMinus] using hcMinus
  have hflat_seed :
        ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
          IsOpen W ∧
          IsPreconnected W ∧
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.unflattenCfg n d (SCV.realEmbed (e u0))) ∈ W ∧
          W ⊆
            BHW.ExtendedTube d n ∩
              BHW.permutedExtendedTubeSector d n P.τ ∧
          Set.EqOn
            (BHW.extendF (bvt_F OS lgc n))
            (fun z =>
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ z))
            W := by
      exact
        BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
          (d := d) hd OS lgc (P := P)
          hE_open hE_sub ys hys_mem hys_li (e u0) hx0
          Tlocal hzero_plus hzero_minus

end BHW
