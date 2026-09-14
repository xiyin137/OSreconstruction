/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected












open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Core translation-invariance statement for `W_analytic` on
    `ForwardTube d n ∩ (ForwardTube d n - c)`.

    For `z ∈ ForwardTube d n` with `z + c ∈ ForwardTube d n`, the holomorphic
    continuation from `spectrum_condition` should satisfy
    `W_analytic (z + c) = W_analytic z`.

    This is the analytic lift of distributional translation invariance of `W_n`.
    The missing formal step is a uniqueness argument on the non-conic intersection
    geometry `ForwardTube ∩ (ForwardTube - c)`, which is not directly covered by
    the existing conic tube uniqueness infrastructure.

    Ref: Streater-Wightman §2.5; Vladimirov §26.

    Status: fully proved. The nontrivial branch is obtained by:
    (1) real-shift invariance via `distributional_uniqueness_forwardTube`,
    then (2) extension to complex shifts by the totally-real identity theorem
    in the shift parameter. -/
theorem W_analytic_translation_on_forwardTube {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ ForwardTube d n) :
    (Wfn.spectrum_condition n).choose (fun k μ => z k μ + c μ) =
    (Wfn.spectrum_condition n).choose z := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hn : n = 0
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simp [hshift]
  let W_analytic := (Wfn.spectrum_condition n).choose
  have hW_holo : DifferentiableOn ℂ W_analytic (ForwardTube d n) :=
    (Wfn.spectrum_condition n).choose_spec.1
  have hW_growth := (Wfn.spectrum_condition n).choose_spec.2.1
  have hW_bv := (Wfn.spectrum_condition n).choose_spec.2.2

  have forwardTube_add_real_shift :
      ∀ (w : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℝ),
        w ∈ ForwardTube d n →
        (fun k μ => w k μ + (a μ : ℂ)) ∈ ForwardTube d n := by
    intro w a hw k
    by_cases hk : (k : ℕ) = 0
    · simpa [hk, Complex.add_im, Complex.ofReal_im] using hw k
    · simpa [hk, Complex.sub_im, Complex.add_im, Complex.ofReal_im] using hw k

  have hreal_shift :
      ∀ (a : Fin (d + 1) → ℝ) (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        W_analytic (fun k μ => w k μ + (a μ : ℂ)) = W_analytic w := by
    intro a w hw
    let aN : NPointDomain d n := fun _ => a
    let shiftW : (Fin n → Fin (d + 1) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
      fun z => z + (fun _ μ => (a μ : ℂ))
    let F₁ : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
      fun z => W_analytic (shiftW z)
    have hF₁_holo : DifferentiableOn ℂ F₁ (ForwardTube d n) := by
      intro z hz
      have hz_shift : shiftW z ∈ ForwardTube d n := by
        simpa [shiftW] using
        forwardTube_add_real_shift z a hz
      have hshift_diff : Differentiable ℂ shiftW := by
        have hconst_shift :
            Differentiable ℂ
              (fun _x : Fin n → Fin (d + 1) → ℂ =>
                (fun _k : Fin n => fun μ : Fin (d + 1) => (a μ : ℂ))) := by
          exact
            (differentiable_const
              (c := (fun _k : Fin n => fun μ : Fin (d + 1) => (a μ : ℂ))))
        change Differentiable ℂ
          (fun z' : Fin n → Fin (d + 1) → ℂ =>
            z' + (fun _k : Fin n => fun μ : Fin (d + 1) => (a μ : ℂ)))
        exact differentiable_id.add hconst_shift
      exact (hW_holo _ hz_shift).comp z hshift_diff.differentiableAt.differentiableWithinAt
        (by
          intro y hy
          simpa [shiftW] using (forwardTube_add_real_shift y a hy))
    have h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            (F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) -
             W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
      intro f η hη
      let g : SchwartzNPoint d n :=
        poincareActNPoint (PoincareGroup.translation' a) f
      have hInv :
          (PoincareGroup.translation' a : PoincareGroup d)⁻¹ =
          PoincareGroup.translation' (-a) := by
        ext <;> simp [PoincareGroup.translation']
      have hg_shift : ∀ x : NPointDomain d n, g x = f (fun i => x i - a) := by
        intro x
        have harg :
            poincareActNPointDomain (PoincareGroup.translation' (-a)) x =
            (fun i => x i - a) := by
          ext i μ
          simp [poincareActNPointDomain, PoincareGroup.pureTranslation_act, sub_eq_add_neg]
        simp [g, poincareActNPoint_apply, hInv, harg]
      have hg_add : ∀ x : NPointDomain d n, g (x + aN) = f x := by
        intro x
        rw [hg_shift]
        congr 1
        ext i μ
        simp [aN]
      have hI₁_eq : ∀ ε : ℝ,
          ∫ x : NPointDomain d n,
            F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) =
          ∫ x : NPointDomain d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x) := by
        intro ε
        let hε : NPointDomain d n → ℂ := fun x =>
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        have htrans : ∫ x : NPointDomain d n, hε (x + aN) =
            ∫ x : NPointDomain d n, hε x :=
          MeasureTheory.integral_add_right_eq_self hε aN
        calc
          ∫ x : NPointDomain d n,
              F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)
              = ∫ x : NPointDomain d n, hε (x + aN) := by
                  congr 1
                  ext x
                  have harg :
                      F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
                      W_analytic (fun k μ => ↑((x + aN) k μ) + ε * ↑(η k μ) * Complex.I) := by
                    have hsum :
                        (fun x μ => (a μ : ℂ)) + (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
                        (fun k μ => (a μ : ℂ) + (↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
                      ext k μ
                      rfl
                    simp [F₁, shiftW, aN, hsum, add_assoc, add_comm]
                  rw [harg]
                  simp [hε, hg_add]
          _ = ∫ x : NPointDomain d n, hε x := htrans
          _ = ∫ x : NPointDomain d n,
                W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x) := by
                rfl
      have hlim₁ : Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Wfn.W n g)) := by
        refine Filter.Tendsto.congr' ?_ (hW_bv g η hη)
        exact Filter.Eventually.of_forall (fun ε => (hI₁_eq ε).symm)
      have hlim₂ : Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Wfn.W n f)) :=
        hW_bv f η hη
      have hW_eq_fg : Wfn.W n f = Wfn.W n g :=
        Wfn.translation_invariant n (-a) f g (by
          intro x
          simpa [sub_eq_add_neg] using hg_shift x)
      have hdiff : Filter.Tendsto
          (fun ε : ℝ =>
            (∫ x : NPointDomain d n,
              F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) -
            (∫ x : NPointDomain d n,
              W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Wfn.W n g - Wfn.W n f)) :=
        Filter.Tendsto.sub hlim₁ hlim₂
      have hW_eq : Wfn.W n g = Wfn.W n f := hW_eq_fg.symm
      have hW_sub : Wfn.W n g - Wfn.W n f = 0 := by simp [hW_eq]
      have hdiff0 : Filter.Tendsto
          (fun ε : ℝ =>
            (∫ x : NPointDomain d n,
              F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) -
            (∫ x : NPointDomain d n,
              W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
        simpa [hW_sub] using hdiff
      refine hdiff0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hInt_F₁f : MeasureTheory.Integrable (fun x : NPointDomain d n =>
          F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
        let hεg : NPointDomain d n → ℂ := fun x =>
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        have hInt_hεg : MeasureTheory.Integrable hεg := by
          exact forward_tube_bv_integrable_of_compact
            W_analytic hW_holo
            hW_growth
            g η hη ε (Set.mem_Ioi.mp hε)
        have hEq :
            (fun x : NPointDomain d n =>
              F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
            (fun x : NPointDomain d n => hεg (x + aN)) := by
          funext x
          have harg :
              F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
              W_analytic (fun k μ => ↑((x + aN) k μ) + ε * ↑(η k μ) * Complex.I) := by
            have hsum :
                (fun x μ => (a μ : ℂ)) + (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
                (fun k μ => (a μ : ℂ) + (↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
              ext k μ
              rfl
            simp [F₁, shiftW, aN, hsum, add_assoc, add_comm]
          rw [harg]
          simp [hεg, hg_add]
        rw [hEq]
        exact hInt_hεg.comp_add_right aN
      have hInt_Wf : MeasureTheory.Integrable (fun x : NPointDomain d n =>
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
        exact forward_tube_bv_integrable_of_compact
          W_analytic hW_holo
          hW_growth
          f η hη ε (Set.mem_Ioi.mp hε)
      rw [← MeasureTheory.integral_sub hInt_F₁f hInt_Wf]
      congr 1
      ext x
      ring
    have huniq := distributional_uniqueness_forwardTube
      hF₁_holo hW_holo
      (fun f η ε hε hη => by
        have hInt_F₁f : MeasureTheory.Integrable (fun x : NPointDomain d n =>
            F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
          let g : SchwartzNPoint d n :=
            poincareActNPoint (PoincareGroup.translation' a) f
          have hInv :
              (PoincareGroup.translation' a : PoincareGroup d)⁻¹ =
              PoincareGroup.translation' (-a) := by
            ext <;> simp [PoincareGroup.translation']
          have hg_shift : ∀ x : NPointDomain d n, g x = f (fun i => x i - a) := by
            intro x
            have harg :
                poincareActNPointDomain (PoincareGroup.translation' (-a)) x =
                (fun i => x i - a) := by
              ext i μ
              simp [poincareActNPointDomain, PoincareGroup.pureTranslation_act, sub_eq_add_neg]
            simp [g, poincareActNPoint_apply, hInv, harg]
          have hg_add : ∀ x : NPointDomain d n, g (x + aN) = f x := by
            intro x
            rw [hg_shift]
            congr 1
            ext i μ
            simp [aN]
          let hεg : NPointDomain d n → ℂ := fun x =>
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          have hInt_hεg : MeasureTheory.Integrable hεg := by
            exact forward_tube_bv_integrable_of_compact
              W_analytic hW_holo
              hW_growth
              g η hη ε hε
          have hEq :
              (fun x : NPointDomain d n =>
                F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
              (fun x : NPointDomain d n => hεg (x + aN)) := by
            funext x
            have harg :
                F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
                W_analytic (fun k μ => ↑((x + aN) k μ) + ε * ↑(η k μ) * Complex.I) := by
              have hsum :
                  (fun x μ => (a μ : ℂ)) + (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
                  (fun k μ => (a μ : ℂ) + (↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
                ext k μ
                rfl
              simp [F₁, shiftW, aN, hsum, add_assoc, add_comm]
            rw [harg]
            simp [hεg, hg_add]
          rw [hEq]
          exact hInt_hεg.comp_add_right aN
        have hInt_Wf : MeasureTheory.Integrable (fun x : NPointDomain d n =>
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
          exact forward_tube_bv_integrable_of_compact
            W_analytic hW_holo
            hW_growth
            f η hη ε hε
        simpa [sub_mul] using hInt_F₁f.sub hInt_Wf)
      h_agree
    exact huniq w hw

  let D : Set (Fin (d + 1) → ℂ) :=
    {s | (fun k μ => z k μ + s μ) ∈ ForwardTube d n}
  let hfun : (Fin (d + 1) → ℂ) → ℂ :=
    fun s => W_analytic (fun k μ => z k μ + s μ) - W_analytic z
  have hD_open : IsOpen D := by
    have hFT_open : IsOpen (ForwardTube d n) :=
      BHW_forwardTube_eq (d := d) (n := n) ▸ BHW.isOpen_forwardTube
    have hshift_cont : Continuous (fun s : Fin (d + 1) → ℂ =>
      (fun k μ => z k μ + s μ)) := by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      exact continuous_const.add (continuous_apply μ)
    simpa [D] using (hFT_open.preimage hshift_cont)
  have hD_convex : Convex ℝ D := by
    intro s hs t ht a b ha hb hab
    have hsFT : (fun k μ => z k μ + s μ) ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hs
    have htFT : (fun k μ => z k μ + t μ) ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using ht
    have hconv : a • (fun k μ => z k μ + s μ) + b • (fun k μ => z k μ + t μ) ∈ ForwardTube d n := by
      have hconv' := BHW.forwardTube_convex hsFT htFT ha hb hab
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hconv'
    have hcomb :
        a • (fun k μ => z k μ + s μ) + b • (fun k μ => z k μ + t μ) =
        (fun k μ => z k μ + (a • s + b • t) μ) := by
      ext k μ
      have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      calc
        (a • (fun k μ => z k μ + s μ) + b • (fun k μ => z k μ + t μ)) k μ
            = (a : ℂ) * z k μ + (a : ℂ) * s μ + ((b : ℂ) * z k μ + (b : ℂ) * t μ) := by
                simp [Pi.smul_apply, add_assoc]
        _ = ((a : ℂ) + (b : ℂ)) * z k μ + ((a : ℂ) * s μ + (b : ℂ) * t μ) := by
              ring
        _ = z k μ + ((a : ℂ) * s μ + (b : ℂ) * t μ) := by
              simp [habC]
        _ = z k μ + (a • s + b • t) μ := by
              simp [Pi.smul_apply]
    have htarget : (fun k μ => z k μ + (a • s + b • t) μ) ∈ ForwardTube d n := by
      simpa [hcomb] using hconv
    simpa [D] using htarget
  have hD_ne : D.Nonempty := ⟨0, by simpa [D] using hz⟩
  have hD_conn : IsConnected D := hD_convex.isConnected hD_ne
  have hhfun_holo : DifferentiableOn ℂ hfun D := by
    let rep : (Fin (d + 1) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
      fun s => fun _ μ => s μ
    let constZ : (Fin (d + 1) → ℂ) → (Fin n → Fin (d + 1) → ℂ) :=
      fun _ => fun k μ => z k μ
    have hrep_diff : Differentiable ℂ rep := by
      refine (differentiable_pi).2 ?_
      intro k
      unfold rep
      exact (differentiable_id : Differentiable ℂ (fun s : Fin (d + 1) → ℂ => s))
    have hconstZ_diff : Differentiable ℂ constZ := by
      have hconstZ_base :
          Differentiable ℂ
            (fun _s : Fin (d + 1) → ℂ =>
              (fun k : Fin n => fun μ : Fin (d + 1) => z k μ)) := by
        exact
          (differentiable_const
            (c := (fun k : Fin n => fun μ : Fin (d + 1) => z k μ)))
      change Differentiable ℂ
        (fun _s : Fin (d + 1) → ℂ => (fun k : Fin n => fun μ : Fin (d + 1) => z k μ))
      exact hconstZ_base
    have hshift_diff' : Differentiable ℂ (fun s : Fin (d + 1) → ℂ => constZ s + rep s) :=
      hconstZ_diff.add hrep_diff
    have hshift_eq :
        (fun s : Fin (d + 1) → ℂ => constZ s + rep s) =
        (fun s : Fin (d + 1) → ℂ => (fun k μ => z k μ + s μ)) := by
      funext s
      ext k μ
      simp [constZ, rep]
    have hshift_diff : Differentiable ℂ (fun s : Fin (d + 1) → ℂ =>
      (fun k μ => z k μ + s μ)) := by
      rw [← hshift_eq]
      exact hshift_diff'
    intro s hs
    have hcomp : DifferentiableWithinAt ℂ
        (fun s : Fin (d + 1) → ℂ => W_analytic (fun k μ => z k μ + s μ)) D s :=
      (hW_holo _ hs).comp s hshift_diff.differentiableAt.differentiableWithinAt (by
        intro y hy
        exact hy)
    exact hcomp.sub (differentiableWithinAt_const _)
  have hV_sub : ∀ x ∈ (Set.univ : Set (Fin (d + 1) → ℝ)),
      (fun μ => (x μ : ℂ)) ∈ D := by
    intro x _
    simpa [D] using (forwardTube_add_real_shift z x hz)
  have hhfun_zero_real : ∀ x ∈ (Set.univ : Set (Fin (d + 1) → ℝ)),
      hfun (fun μ => (x μ : ℂ)) = 0 := by
    intro x _
    exact sub_eq_zero.mpr (hreal_shift x z hz)
  have hzero_on_D := SCV.identity_theorem_totally_real (m := d + 1)
      hD_open hD_conn hhfun_holo
      (V := Set.univ) isOpen_univ Set.univ_nonempty
      (by intro x hx; simpa [SCV.realToComplex] using hV_sub x hx)
      (by intro x hx; simpa [SCV.realToComplex] using hhfun_zero_real x hx)
  have hcD : c ∈ D := by simpa [D] using hzc
  have hc_zero : hfun c = 0 := hzero_on_D c hcD
  exact sub_eq_zero.mp (by simpa [hfun] using hc_zero)

