/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.SCV.PaleyWiener

/-!
# BHW Translation Invariance

Translation invariance of the BHW extension, proved via the identity theorem
on the connected permuted extended tube. Also defines the Schwinger function
construction and proves distributional boundary value correspondence.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! #### BHW extension helper lemmas and translation invariance

The BHW extension inherits translation invariance from the Wightman functions.
The proof uses the identity theorem for holomorphic functions on connected domains,
applied to `D = PET ∩ (PET - c)` — the overlap domain where both F_ext and
`z ↦ F_ext(z+c)` are holomorphic.

The proof is decomposed into helpers:
1. `permutedExtendedTube_translation_closed` — trivial closure cases (c=0 or n=0)
2. `W_analytic_translation_on_forwardTube` — W_analytic is translation-invariant on FT
3. `bhw_translation_invariant_of_common_perm` — common-permutation witness case
4. `bhw_translation_local` — local translation invariance via a BHW witness chain
5. `bhw_translation_invariant_of_baseFiber_isPreconnected` — global translation
   invariance once the fixed-tail base fiber is preconnected
6. `isPreconnected_baseFiber` — the remaining global geometric blocker

The main theorem `bhw_translation_invariant` now uses the base-fiber route:
fix the tail difference coordinates, show the BHW extension has zero derivative
in the base variable by local translation invariance, and then propagate that
local constancy across the preconnected base fiber. -/

/-- Trivial translation-closure cases for the permuted extended tube.

    This records the only currently formalized regimes where closure under
    `z ↦ z + c` is immediate in our absolute-coordinate PET:
    - `c = 0` (identity shift),
    - `n = 0` (empty configuration index).

    The nontrivial geometric closure claim (`n > 0`, `c ≠ 0`) is deferred and
    must be treated separately. -/
theorem permutedExtendedTube_translation_closed {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hc : c = 0 ∨ n = 0) :
    (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
  rcases hc with hc | hn
  · simpa [hc] using hz
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simpa [hshift] using hz

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
  have hW_bv := (Wfn.spectrum_condition n).choose_spec.2

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
          exact forward_tube_bv_integrable
            W_analytic hW_holo ⟨Wfn.W n, Wfn.tempered n, hW_bv⟩ g η hη ε (Set.mem_Ioi.mp hε)
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
        exact forward_tube_bv_integrable
          W_analytic hW_holo ⟨Wfn.W n, Wfn.tempered n, hW_bv⟩ f η hη ε (Set.mem_Ioi.mp hε)
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
            exact forward_tube_bv_integrable
              W_analytic hW_holo ⟨Wfn.W n, Wfn.tempered n, hW_bv⟩ g η hη ε hε
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
          exact forward_tube_bv_integrable
            W_analytic hW_holo ⟨Wfn.W n, Wfn.tempered n, hW_bv⟩ f η hη ε hε
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

/-- The permuted extended tube is connected.

    PET = ⋃_{π,Λ} Λ·π·FT is connected because the forward tube FT is connected
    (it is convex), adjacent permutation sectors are joined via the edge-of-the-wedge
    theorem at Jost points (spacelike boundary configurations), and the complex Lorentz
    group is connected.

    This fact is used in the BHW uniqueness proof (Property 5 of
    `bargmann_hall_wightman_theorem` in Connectedness.lean) where it currently
    appears as a local sorry. This lemma extracts it as a standalone statement.

    Ref: Jost, "The General Theory of Quantized Fields" Ch. IV -/
theorem permutedExtendedTube_isConnected (d n : ℕ) [NeZero d] :
    IsConnected (PermutedExtendedTube d n) := by
  rw [← BHW_permutedExtendedTube_eq]
  exact BHW.isConnected_permutedExtendedTube (d := d) (n := n)

/-- The forward tube intersected with its c-translate is nonempty.

    For any c ∈ ℂ^{d+1}, there exists z ∈ FT with z + c ∈ FT. We construct such z
    by choosing Im(z₀) deep enough in V₊ that Im(z₀) + Im(c) remains in V₊, and
    choosing successive differences with large enough forward-cone components. -/
theorem forwardTube_inter_translate_nonempty {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n := by
  -- Witness: z_k(μ) = i·(k+1)·M·δ_{μ,0} for M large enough.
  -- Successive differences have imaginary part M·e₀ ∈ V₊.
  -- For z+c at k=0, need (M + Im(c 0), Im(c 1), ...) ∈ V₊, ensured by large M.
  set Ssp := MinkowskiSpace.spatialNormSq d (fun μ => (c μ).im)
  set M : ℝ := 1 + |(c 0).im| + Real.sqrt Ssp
  have hSsp_nn : 0 ≤ Ssp := by
    simp only [Ssp, MinkowskiSpace.spatialNormSq]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hM_pos : M > 0 := by positivity
  have hMc_pos : M + (c 0).im > 0 := by
    have := neg_abs_le (c 0).im; linarith [Real.sqrt_nonneg Ssp]
  have hMc_gt_sqrt : M + (c 0).im > Real.sqrt Ssp := by
    have h1 : -|(c 0).im| ≤ (c 0).im := neg_abs_le (c 0).im
    linarith
  -- M·e₀ ∈ V₊
  have hMe0_cone : InOpenForwardCone d (fun μ => if μ = 0 then M else 0) := by
    refine ⟨by simp; exact hM_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [MinkowskiSpace.spatialNormSq, ↓reduceIte, Fin.succ_ne_zero]
    simp; nlinarith [sq_nonneg M]
  -- (M + Im(c 0), Im(c 1), ...) ∈ V₊
  have hMc_cone : InOpenForwardCone d
      (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) := by
    refine ⟨by simp; exact hMc_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [↓reduceIte]
    -- spatialNormSq of the shifted vector = Ssp
    have hsp : MinkowskiSpace.spatialNormSq d
        (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) = Ssp := by
      simp only [MinkowskiSpace.spatialNormSq, Ssp, Fin.succ_ne_zero, ↓reduceIte]
    rw [hsp]
    have h1 : (M + (c 0).im) ^ 2 > Ssp := by
      have hsq : Real.sqrt Ssp ^ 2 = Ssp := Real.sq_sqrt hSsp_nn
      have hge : Real.sqrt Ssp ≥ 0 := Real.sqrt_nonneg Ssp
      nlinarith [sq_abs (M + (c 0).im - Real.sqrt Ssp)]
    linarith
  -- The witness z
  set z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = 0 then Complex.I * ((↑(k : ℕ) + 1) * M) else 0
  -- Imaginary successive differences for z equal M·e₀
  have him_diff_z : ∀ k : Fin n, (fun μ =>
      (z k μ - (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ)
        else z ⟨k.val - 1, by omega⟩) μ).im) =
      fun μ => if μ = 0 then M else 0 := by
    intro k
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [z, hk]; split_ifs with hμ
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      · simp
    · simp only [z, hk, ↓reduceDIte]; split_ifs with hμ
      · subst hμ; simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        have hk1 : (1 : ℕ) ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
        rw [Nat.cast_sub hk1]; ring
      · simp
  -- For z+c at k > 0, c cancels in successive differences
  have him_diff_zc_pos : ∀ k : Fin n, (k : ℕ) ≠ 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => (z k μ - (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ)
        else z ⟨k.val - 1, by omega⟩) μ).im := by
    intro k hk; ext μ; simp [hk, Complex.sub_im]
  -- For z+c at k = 0, get (M + Im(c 0), Im(c_i))
  have him_diff_zc_zero : ∀ k : Fin n, (k : ℕ) = 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => if μ = 0 then M + (c 0).im else (c μ).im := by
    intro k hk; ext μ; simp [hk]; split_ifs with hμ
    · subst hμ; simp [z, hk, Complex.mul_im, Complex.I_re, Complex.I_im]
    · simp [z, hμ]
  refine ⟨z, ?_, ?_⟩
  · -- z ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    rw [him_diff_z]; exact hMe0_cone
  · -- z + c ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    by_cases hk : (k : ℕ) = 0
    · rw [him_diff_zc_zero k hk]; exact hMc_cone
    · rw [him_diff_zc_pos k hk, him_diff_z]; exact hMe0_cone

/-- **BHW extension is translation-invariant when a common permutation witness exists.**

    If z∘π ∈ FT and (z+c)∘π ∈ FT for the SAME permutation π, then F_ext(z+c) = F_ext(z).

    The proof uses the chain:
      F_ext(z+c) = F_ext((z+c)∘π)   [perm inv, since (z+c) ∈ PET from hzc_ft]
               = W_analytic((z+c)∘π) [BHW prop 2, (z+c)∘π ∈ FT]
               = W_analytic(z∘π)     [trans inv on FT: z∘π ∈ FT, (z∘π)+c ∈ FT]
               = F_ext(z∘π)          [BHW prop 2, z∘π ∈ FT]
               = F_ext(z)            [perm inv, since z ∈ PET from hz_ft]

    This avoids needing D = PET ∩ (PET-c) to be connected, and applies directly
    to the Euclidean case where the same ordering permutation works for both z and z+c.

    Used in `F_ext_translation_invariant` for the Euclidean application. -/
theorem bhw_translation_invariant_of_common_perm {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin n))
    (hz_ft : (fun k => z (π k)) ∈ ForwardTube d n)
    (hzc_ft : (fun k μ => z (π k) μ + c μ) ∈ ForwardTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
  set W_analytic := (Wfn.spectrum_condition n).choose
  -- hF_eq : F_ext z = W_analytic z for z ∈ FT
  have hF_eq := (W_analytic_BHW Wfn n).property.2.1
  -- hF_perm : F_ext (z ∘ π) = F_ext z for z ∈ PET
  have hF_perm := (W_analytic_BHW Wfn n).property.2.2.2
  -- Establish PET membership for z and z+c via PermutedForwardTube π ⊆ PET
  -- Strategy: work in BHW namespace and use complexLorentzAction_one
  have hz_pet : z ∈ PermutedExtendedTube d n := by
    rw [← BHW_permutedExtendedTube_eq]
    -- Show z ∈ BHW.PermutedExtendedTube: take π, Λ = 1, w = z
    refine Set.mem_iUnion.mpr ⟨π, 1, z, ?_, (BHW.complexLorentzAction_one z).symm⟩
    -- z ∈ BHW.PermutedForwardTube π: (fun k => z (π k)) ∈ BHW.ForwardTube
    simp only [BHW.PermutedForwardTube, Set.mem_setOf_eq]
    rwa [BHW_forwardTube_eq]
  have hzc_pet : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
    rw [← BHW_permutedExtendedTube_eq]
    -- Show (z+c) ∈ BHW.PermutedExtendedTube: take π, Λ = 1, w = (z+c)
    refine Set.mem_iUnion.mpr ⟨π, 1, fun k μ => z k μ + c μ,
      ?_, (BHW.complexLorentzAction_one _).symm⟩
    -- (z+c) ∈ BHW.PermutedForwardTube π: (fun k => (z+c) (π k)) ∈ BHW.ForwardTube
    simp only [BHW.PermutedForwardTube, Set.mem_setOf_eq]
    rwa [BHW_forwardTube_eq]
  -- Step 1: F_ext(z+c) = F_ext((z+c)∘π) by perm invariance
  -- hF_perm π (z+c) hzc_pet : F_ext (fun k => (z+c) (π k)) = F_ext (z+c)
  -- Note: (fun k => (fun k' μ => z k' μ + c μ) (π k)) = (fun k μ => z (π k) μ + c μ) by rfl
  have h1 : F_ext (fun k μ => z k μ + c μ) = F_ext (fun k μ => z (π k) μ + c μ) :=
    (hF_perm π (fun k μ => z k μ + c μ) hzc_pet).symm
  -- Step 2: F_ext((z+c)∘π) = W_analytic((z+c)∘π) since (z+c)∘π ∈ FT
  -- hF_eq gives F_ext w = W_analytic w for w ∈ FT
  have h2 : F_ext (fun k μ => z (π k) μ + c μ) = W_analytic (fun k μ => z (π k) μ + c μ) :=
    hF_eq (fun k μ => z (π k) μ + c μ) hzc_ft
  -- Step 3: W_analytic((z+c)∘π) = W_analytic(z∘π) by translation invariance on FT
  have h3 : W_analytic (fun k μ => z (π k) μ + c μ) = W_analytic (fun k => z (π k)) :=
    W_analytic_translation_on_forwardTube Wfn c (fun k => z (π k)) hz_ft hzc_ft
  -- Step 4: W_analytic(z∘π) = F_ext(z∘π) since z∘π ∈ FT
  have h4 : W_analytic (fun k => z (π k)) = F_ext (fun k => z (π k)) :=
    (hF_eq _ hz_ft).symm
  -- Step 5: F_ext(z∘π) = F_ext(z) by perm invariance
  have h5 : F_ext (fun k => z (π k)) = F_ext z :=
    hF_perm π z hz_pet
  calc F_ext (fun k μ => z k μ + c μ)
      = F_ext (fun k μ => z (π k) μ + c μ) := h1
    _ = W_analytic (fun k μ => z (π k) μ + c μ) := h2
    _ = W_analytic (fun k => z (π k)) := h3
    _ = F_ext (fun k => z (π k)) := h4
    _ = F_ext z := h5

/-- **Local translation invariance of the BHW extension.**

    For any z ∈ PET and shift direction c, there exists ε > 0 such that
    for all |t| < ε, `z + tc ∈ PET` and `F_ext(z + tc) = F_ext(z)`.

    **Proof.** Extract the PET witness (π, Λ, w) with `w ∈ PFT(π)` and
    `z = Λ · w`. Form `w' = w + t · Λ⁻¹c`. Successive imaginary-part differences
    are unchanged by the uniform shift `Λ⁻¹c`, so `w' ∈ PFT(π)` for small `t`
    (only the k = 0 condition shifts, and FT is open). Then chain BHW properties:
      `F_ext(z + tc) = F_ext(Λ · w') = F_ext(w') = F_ext(w) = F_ext(Λ · w) = F_ext(z)`
    using Lorentz invariance, the common-permutation lemma (which invokes
    permutation invariance + FT agreement + translation invariance on FT).

    This captures the "BHW witness chain" argument and shows F_ext is locally
    constant under uniform translations at every point of PET.

    Ref: Streater-Wightman §2.5; Jost, "General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_local {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    ∃ ε > 0, ∀ (t : ℂ), ‖t‖ < ε →
      (fun k μ => z k μ + t * c μ) ∈ PermutedExtendedTube d n ∧
      (W_analytic_BHW Wfn n).val (fun k μ => z k μ + t * c μ) =
      (W_analytic_BHW Wfn n).val z := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, one_pos, fun t _ => ?_⟩
    have htriv : (fun k μ => z k μ + t * c μ) = z := by ext k; exact Fin.elim0 k
    rw [htriv]; exact ⟨hz, rfl⟩
  -- PET is open → z + tc ∈ PET for small t
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hshift_cont : Continuous (fun t : ℂ => fun k μ => z k μ + t * c μ) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    exact continuous_const.add (continuous_id.mul continuous_const)
  obtain ⟨ε₁, hε₁_pos, hε₁_ball⟩ := Metric.isOpen_iff.mp
    (hPET_open.preimage hshift_cont) 0
    (show (fun k μ => z k μ + (0 : ℂ) * c μ) ∈ PermutedExtendedTube d n by simp [hz])
  -- Extract PET witness: z = Λ₀ · w₀ with w₀ ∈ PFT(π₀)
  rw [← BHW_permutedExtendedTube_eq] at hz
  obtain ⟨π₀, Λ₀, w₀, hw₀_pft, hz_eq⟩ := Set.mem_iUnion.mp hz
  -- w₀ ∘ π₀ ∈ FT
  have hw₀π₀_ft : (fun k => w₀ (π₀ k)) ∈ ForwardTube d n := by
    rw [← BHW_forwardTube_eq]; exact hw₀_pft
  -- Define inverse-rotated shift: c' = Λ₀⁻¹ · c (single-point Lorentz action)
  let c' : Fin (d + 1) → ℂ := fun μ => ∑ ν, (Λ₀⁻¹).val μ ν * c ν
  -- FT is open → perturbed w₀∘π₀ stays in FT for small t
  have hFT_open : IsOpen (ForwardTube d n) :=
    BHW_forwardTube_eq (d := d) (n := n) ▸ BHW.isOpen_forwardTube
  have hshift_cont' : Continuous (fun t : ℂ => fun k μ => w₀ (π₀ k) μ + t * c' μ) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    exact continuous_const.add (continuous_id.mul continuous_const)
  obtain ⟨ε₂, hε₂_pos, hε₂_ball⟩ := Metric.isOpen_iff.mp
    (hFT_open.preimage hshift_cont') 0
    (show (fun k μ => w₀ (π₀ k) μ + (0 : ℂ) * c' μ) ∈ ForwardTube d n by simp [hw₀π₀_ft])
  -- Take ε = min(ε₁, ε₂)
  refine ⟨min ε₁ ε₂, lt_min hε₁_pos hε₂_pos, fun t ht => ?_⟩
  have ht₁ : ‖t‖ < ε₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : ‖t‖ < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
  constructor
  -- Part 1: z + tc ∈ PET (from PET openness)
  · exact hε₁_ball (Metric.mem_ball.mpr (show dist t 0 < ε₁ by rwa [dist_comm, dist_zero_left]))
  -- Part 2: F_ext(z + tc) = F_ext(z)
  · -- Abbreviations
    set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
    have hF_lorentz := (W_analytic_BHW Wfn n).property.2.2.1
    -- Perturbed FT membership: (w₀∘π₀) + t*c' ∈ FT
    have hw't_ft : (fun k μ => w₀ (π₀ k) μ + t * c' μ) ∈ ForwardTube d n :=
      hε₂_ball (Metric.mem_ball.mpr (show dist t 0 < ε₂ by rwa [dist_comm, dist_zero_left]))
    -- Common permutation lemma: F_ext(w₀ + tc') = F_ext(w₀)
    have hF_w : F_ext (fun k μ => w₀ k μ + t * c' μ) = F_ext w₀ :=
      bhw_translation_invariant_of_common_perm Wfn (fun μ => t * c' μ) w₀ π₀ hw₀π₀_ft hw't_ft
    -- w₀ ∈ PET (PFT(π₀) ⊆ PET via Λ = 1)
    have hw₀_pet : w₀ ∈ PermutedExtendedTube d n := by
      rw [← BHW_permutedExtendedTube_eq]
      exact Set.mem_iUnion.mpr ⟨π₀, 1, w₀, hw₀_pft, (BHW.complexLorentzAction_one w₀).symm⟩
    -- w' ∈ PET (PFT(π₀) ⊆ PET via Λ = 1)
    have hw'_pet : (fun k μ => w₀ k μ + t * c' μ) ∈ PermutedExtendedTube d n := by
      rw [← BHW_permutedExtendedTube_eq]
      refine Set.mem_iUnion.mpr ⟨π₀, 1, fun k μ => w₀ k μ + t * c' μ, ?_,
        (BHW.complexLorentzAction_one _).symm⟩
      show (fun k μ => w₀ (π₀ k) μ + t * c' μ) ∈ BHW.ForwardTube d n
      rwa [BHW_forwardTube_eq]
    -- Algebraic identity: z + tc = Λ₀ · (w₀ + tc')
    -- Key: Λ₀ · (Λ₀⁻¹ · c_broadcast) = c_broadcast (matrix cancellation)
    have hΛΛinv_cancel : ∀ μ : Fin (d + 1),
        ∑ ν, Λ₀.val μ ν * (∑ ρ, (Λ₀⁻¹).val ν ρ * c ρ) = c μ := by
      intro μ
      have h := congr_fun (congr_fun
        (show BHW.complexLorentzAction Λ₀
          (BHW.complexLorentzAction Λ₀⁻¹ (fun (_k : Fin n) => c)) = fun _k => c
        from by rw [← BHW.complexLorentzAction_mul, mul_inv_cancel,
                     BHW.complexLorentzAction_one])
        ⟨0, Nat.pos_of_ne_zero hn⟩) μ
      simpa [BHW.complexLorentzAction] using h
    have hshift_eq : (fun k μ => z k μ + t * c μ) =
        (fun k μ => ∑ ν, Λ₀.val μ ν * (w₀ k ν + t * c' ν)) := by
      ext k μ
      have hz_k : z k μ = ∑ ν, Λ₀.val μ ν * w₀ k ν := congr_fun (congr_fun hz_eq k) μ
      rw [hz_k]
      simp only [mul_add, Finset.sum_add_distrib, c']
      congr 1
      -- ∑ ν, Λ₀.val μ ν * (t * (∑ ρ, (Λ₀⁻¹).val ν ρ * c ρ)) = t * c μ
      simp_rw [← mul_assoc, mul_comm (Λ₀.val μ _) t, mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact (hΛΛinv_cancel μ).symm
    -- Chain: F_ext(z+tc) = F_ext(Λ₀·w') = F_ext(w') = F_ext(w₀) = F_ext(z)
    have hF_z_eq_w₀ : F_ext z = F_ext w₀ := by
      conv_lhs => rw [hz_eq]
      exact hF_lorentz Λ₀ w₀ hw₀_pet
    calc F_ext (fun k μ => z k μ + t * c μ)
        = F_ext (fun k μ => ∑ ν, Λ₀.val μ ν * (w₀ k ν + t * c' ν)) := by rw [hshift_eq]
      _ = F_ext (fun k μ => w₀ k μ + t * c' μ) :=
          hF_lorentz Λ₀ (fun k μ => w₀ k μ + t * c' μ) hw'_pet
      _ = F_ext w₀ := hF_w
      _ = F_ext z := hF_z_eq_w₀.symm

/-- Reconstruct a cumulative-sum configuration from a fixed tail of difference
variables and a varying base difference variable `ζ₀`. This is the natural
coordinate chart for translation invariance: simultaneous translation changes
only `ζ₀`, leaving the tail differences fixed. -/
def baseFiberConfig (m d : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → (Fin (m + 1) → Fin (d + 1) → ℂ) :=
  fun ζ₀ => BHW.partialSumFun (m + 1) d (Fin.cons ζ₀ ζtail)

/-- The base fiber over a fixed tail `ζ₁, ..., ζₘ`: those base variables `ζ₀`
whose reconstructed cumulative configuration lies in the permuted extended
tube. -/
def baseFiber (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) : Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | baseFiberConfig m d ζtail ζ₀ ∈ PermutedExtendedTube d (m + 1)}

@[simp] theorem baseFiberConfig_zero_apply {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ : Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    baseFiberConfig m d ζtail ζ₀ 0 μ = ζ₀ μ := by
  simp [baseFiberConfig, BHW.partialSumFun]

@[simp] theorem baseFiberConfig_succ_apply {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ : Fin (d + 1) → ℂ) (k : Fin m) (μ : Fin (d + 1)) :
    baseFiberConfig m d ζtail ζ₀ k.succ μ =
      ζ₀ μ + ∑ j : Fin (k.val + 1), ζtail ⟨j.val, by omega⟩ μ := by
  simp [baseFiberConfig, BHW.partialSumFun, Fin.sum_univ_succ, add_assoc]
  let ξ : Fin (m + 1) → Fin (d + 1) → ℂ := Fin.cons ζ₀ ζtail
  have hm : 0 < m := by
    cases m with
    | zero => exact Fin.elim0 k
    | succ m' => simp
  have h1idx : (1 : ℕ) < m + 1 := by omega
  have h0idx : (0 : ℕ) < m := hm
  have h1 : ξ ⟨1, h1idx⟩ μ = ζtail ⟨0, h0idx⟩ μ := rfl
  have hsum :
      (∑ x : Fin k.val, ξ ⟨x.val + 2, by omega⟩ μ) =
        ∑ x : Fin k.val, ζtail ⟨x.val + 1, by omega⟩ μ := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rfl
  simp [ξ, h1, hsum]

/-- Shifting the base difference variable by `c` translates every cumulative
coordinate by the same `c`. -/
theorem baseFiberConfig_add {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ c : Fin (d + 1) → ℂ) :
    baseFiberConfig m d ζtail (ζ₀ + c) =
      fun k μ => baseFiberConfig m d ζtail ζ₀ k μ + c μ := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [baseFiberConfig_zero_apply]
  · intro i
    simp [baseFiberConfig_succ_apply, add_assoc, add_left_comm, add_comm]

/-- Reconstructing from the base variable and the tail of the difference
coordinates recovers the original cumulative configuration. -/
theorem baseFiberConfig_diffCoord_tail {m d : ℕ}
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    baseFiberConfig m d (Fin.tail (BHW.diffCoordFun (m + 1) d z))
      (BHW.diffCoordFun (m + 1) d z 0) = z := by
  have hcons :
      Fin.cons (BHW.diffCoordFun (m + 1) d z 0)
        (Fin.tail (BHW.diffCoordFun (m + 1) d z))
        = BHW.diffCoordFun (m + 1) d z := by
    ext k μ
    refine Fin.cases ?_ ?_ k
    · rfl
    · intro i
      rfl
  simp [baseFiberConfig, hcons, BHW.partialSum_diffCoord]

/-- Translating a cumulative configuration by `c` changes only the base
difference variable. -/
theorem diffCoord_translate_head_tail {m d : ℕ}
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    BHW.diffCoordFun (m + 1) d (fun k μ => z k μ + c μ) =
      Fin.cons (BHW.diffCoordFun (m + 1) d z 0 + c)
        (Fin.tail (BHW.diffCoordFun (m + 1) d z)) := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [BHW.diffCoordFun]
  · intro i
    simp [BHW.diffCoordFun, Fin.tail, sub_eq_add_neg]
    ring

/-- Difference coordinates commute with the coordinatewise complex Lorentz
action. This is the algebraic bridge from absolute-coordinate sector witnesses
to the fixed-tail difference-coordinate geometry. -/
private theorem diffCoordFun_complexLorentzAction {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    BHW.diffCoordFun (m + 1) d (BHW.complexLorentzAction Λ z) =
      BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d z) := by
  ext k μ
  by_cases hk : k.val = 0
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]

/-- Partial sums commute with the coordinatewise complex Lorentz action. -/
private theorem partialSumFun_complexLorentzAction {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (ξ : Fin (m + 1) → Fin (d + 1) → ℂ) :
    BHW.partialSumFun (m + 1) d (BHW.complexLorentzAction Λ ξ) =
      BHW.complexLorentzAction Λ (BHW.partialSumFun (m + 1) d ξ) := by
  ext k μ
  simp [BHW.partialSumFun, BHW.complexLorentzAction, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Evaluate the BHW extension on a fixed-tail base fiber. -/
def baseFiberValue {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → ℂ :=
  fun ζ₀ => (W_analytic_BHW Wfn (m + 1)).val (baseFiberConfig m d ζtail ζ₀)

private theorem differentiable_baseFiberConfig {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    Differentiable ℂ (baseFiberConfig m d ζtail) := by
  intro ζ₀
  rw [differentiableAt_pi]
  intro k
  rw [differentiableAt_pi]
  intro μ
  refine Fin.cases ?_ ?_ k
  · simpa using
      (differentiableAt_apply (𝕜 := ℂ) μ ζ₀ : DifferentiableAt ℂ
        (fun ζ : Fin (d + 1) → ℂ => ζ μ) ζ₀)
  · intro i
    simpa [baseFiberConfig_succ_apply, add_comm, add_left_comm, add_assoc] using
      ((differentiableAt_apply (𝕜 := ℂ) μ ζ₀ : DifferentiableAt ℂ
          (fun ζ : Fin (d + 1) → ℂ => ζ μ) ζ₀).add
        (differentiableAt_const
          (c := ∑ j : Fin (i.val + 1), ζtail ⟨j.val, by omega⟩ μ)))

private theorem continuous_baseFiberConfig {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    Continuous (baseFiberConfig m d ζtail) :=
  (differentiable_baseFiberConfig ζtail).continuous

theorem isOpen_baseFiber {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    IsOpen (baseFiber m d ζtail) := by
  have hPET_open : IsOpen (PermutedExtendedTube d (m + 1)) :=
    BHW_permutedExtendedTube_eq (d := d) (n := m + 1) ▸ BHW.isOpen_permutedExtendedTube
  simpa [baseFiber] using hPET_open.preimage (continuous_baseFiberConfig ζtail)

private theorem differentiableOn_baseFiberValue {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    DifferentiableOn ℂ (baseFiberValue Wfn m ζtail) (baseFiber m d ζtail) := by
  intro ζ₀ hζ₀
  have hF_holo := (W_analytic_BHW Wfn (m + 1)).property.1
  exact (hF_holo _ hζ₀).comp ζ₀
    ((differentiable_baseFiberConfig ζtail) ζ₀).differentiableWithinAt
    (fun y hy => hy)

private theorem fderiv_baseFiberValue_eq_zero {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (baseFiber m d ζtail).EqOn (fderiv ℂ (baseFiberValue Wfn m ζtail)) 0 := by
  intro ζ₀ hζ₀
  have hPET_open : IsOpen (PermutedExtendedTube d (m + 1)) :=
    BHW_permutedExtendedTube_eq (d := d) (n := m + 1) ▸ BHW.isOpen_permutedExtendedTube
  have hF_holo := (W_analytic_BHW Wfn (m + 1)).property.1
  have hval_diff :
      DifferentiableAt ℂ (baseFiberValue Wfn m ζtail) ζ₀ := by
    have hF_at :
        DifferentiableAt ℂ (W_analytic_BHW Wfn (m + 1)).val
          (baseFiberConfig m d ζtail ζ₀) :=
      (hF_holo _ hζ₀).differentiableAt (hPET_open.mem_nhds hζ₀)
    exact hF_at.comp ζ₀ ((differentiable_baseFiberConfig ζtail) ζ₀)
  ext c
  let φ : ℂ → ℂ := fun t => baseFiberValue Wfn m ζtail (ζ₀ + t • c)
  have hφ_deriv :
      HasDerivAt φ ((fderiv ℂ (baseFiberValue Wfn m ζtail) ζ₀) c) 0 := by
    have hline : HasDerivAt (fun t : ℂ => ζ₀ + t • c) c 0 := by
      simpa [one_smul] using (((hasDerivAt_id' (0 : ℂ)).smul_const c).const_add ζ₀)
    simpa [one_smul, φ] using
      hval_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  obtain ⟨ε, hε_pos, hlocal⟩ :=
    bhw_translation_local Wfn c (baseFiberConfig m d ζtail ζ₀) hζ₀
  have hφ_const :
      φ =ᶠ[nhds 0] fun _ : ℂ => baseFiberValue Wfn m ζtail ζ₀ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε_pos] with t ht
    have ht' : ‖t‖ < ε := by
      simpa [Metric.mem_ball, dist_comm] using ht
    rcases hlocal t ht' with ⟨_htPET, hEq⟩
    simpa [φ, baseFiberValue, baseFiberConfig_add, smul_eq_mul,
      add_comm, add_left_comm, add_assoc] using hEq
  have hφ_zero : HasDerivAt φ 0 0 := by
    exact (hasDerivAt_const (0 : ℂ) (baseFiberValue Wfn m ζtail ζ₀)).congr_of_eventuallyEq hφ_const
  exact hφ_deriv.unique hφ_zero

/-- On a preconnected base fiber, the BHW extension is constant as a function of
the base difference variable `ζ₀`. This packages the local translation
invariance from `bhw_translation_local` into the exact global fiber statement
needed for translation invariance. -/
theorem exists_isConst_baseFiberValue_of_isPreconnected {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hconn : IsPreconnected (baseFiber m d ζtail)) :
    ∃ a : ℂ, ∀ ζ₀ ∈ baseFiber m d ζtail, baseFiberValue Wfn m ζtail ζ₀ = a := by
  exact (isOpen_baseFiber (m := m) (d := d) ζtail).exists_is_const_of_fderiv_eq_zero
    hconn
    (differentiableOn_baseFiberValue Wfn m ζtail)
    (fderiv_baseFiberValue_eq_zero Wfn m ζtail)

/-- Conditional translation invariance from base-fiber preconnectedness.
This is the cleaner replacement surface for the old overlap-domain blocker:
once the fixed-tail base fiber is known to be preconnected, simultaneous
translation invariance follows immediately. -/
theorem bhw_translation_invariant_of_baseFiber_isPreconnected {d m : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d (m + 1))
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1))
    (hconn : IsPreconnected
      (baseFiber m d (Fin.tail (BHW.diffCoordFun (m + 1) d z)))) :
    (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn (m + 1)).val z := by
  let ζtail : Fin m → Fin (d + 1) → ℂ := Fin.tail (BHW.diffCoordFun (m + 1) d z)
  let ζ₀ : Fin (d + 1) → ℂ := BHW.diffCoordFun (m + 1) d z 0
  have hz_cfg : baseFiberConfig m d ζtail ζ₀ = z := by
    simpa [ζtail, ζ₀] using baseFiberConfig_diffCoord_tail (m := m) (d := d) z
  have hzc_cfg :
      baseFiberConfig m d ζtail (ζ₀ + c) = (fun k μ => z k μ + c μ) := by
    calc
      baseFiberConfig m d ζtail (ζ₀ + c)
          = (fun k μ => baseFiberConfig m d ζtail ζ₀ k μ + c μ) :=
              baseFiberConfig_add (m := m) (d := d) ζtail ζ₀ c
      _ = (fun k μ => z k μ + c μ) := by
            simp [hz_cfg]
  have hζ₀ : ζ₀ ∈ baseFiber m d ζtail := by
    simpa [baseFiber, hz_cfg]
      using hz
  have hζ₀c : ζ₀ + c ∈ baseFiber m d ζtail := by
    simpa [baseFiber, hzc_cfg]
      using hzc
  obtain ⟨a, ha⟩ :=
    exists_isConst_baseFiberValue_of_isPreconnected (Wfn := Wfn) (m := m)
      (ζtail := ζtail) hconn
  calc
    (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ)
        = baseFiberValue Wfn m ζtail (ζ₀ + c) := by
            simp [baseFiberValue, hzc_cfg]
    _ = a := ha _ hζ₀c
    _ = baseFiberValue Wfn m ζtail ζ₀ := (ha _ hζ₀).symm
    _ = (W_analytic_BHW Wfn (m + 1)).val z := by
          simp [baseFiberValue, hz_cfg]

/-- The permutation-sector slice of a fixed-tail base fiber. The full fiber is
the union of these slices, so proving fiber preconnectedness reduces to proving
sector-slice preconnectedness and adjacent overlaps. -/
def baseFiberSector (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d (m + 1) π ∧
      baseFiberConfig m d ζtail ζ₀ = BHW.complexLorentzAction Λ w}

/-- The fixed-tail base fiber is the union of its permutation-sector slices. -/
theorem baseFiber_eq_iUnion_baseFiberSector {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    baseFiber m d ζtail = ⋃ π : Equiv.Perm (Fin (m + 1)), baseFiberSector m d ζtail π := by
  ext ζ₀
  constructor
  · intro hζ₀
    simp only [baseFiber, Set.mem_setOf_eq, PermutedExtendedTube, Set.mem_iUnion] at hζ₀
    rcases hζ₀ with ⟨π, Λ, w, hw, hz⟩
    refine Set.mem_iUnion.mpr ⟨π, ?_⟩
    exact ⟨Λ, w, hw, by simpa [BHW.complexLorentzAction] using hz⟩
  · intro hζ₀
    simp only [Set.mem_iUnion, baseFiberSector, Set.mem_setOf_eq] at hζ₀
    rcases hζ₀ with ⟨π, Λ, w, hw, hz⟩
    simp only [baseFiber, Set.mem_setOf_eq, PermutedExtendedTube, Set.mem_iUnion]
    exact ⟨π, Λ, w, hw, by simpa [BHW.complexLorentzAction] using hz⟩

/-- Sector membership on a fixed-tail base fiber can be rewritten directly in
difference coordinates: the fixed-tail configuration `Fin.cons ζ₀ ζtail` is the
Lorentz transform of the witness difference coordinates. -/
theorem mem_baseFiberSector_iff_diffCoordWitness {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (ζ₀ : Fin (d + 1) → ℂ) :
    ζ₀ ∈ baseFiberSector m d ζtail π ↔
      ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
        w ∈ PermutedForwardTube d (m + 1) π ∧
        Fin.cons ζ₀ ζtail =
          BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) := by
  constructor
  · rintro ⟨Λ, w, hw, hz⟩
    refine ⟨Λ, w, hw, ?_⟩
    have hcfg :
        BHW.diffCoordFun (m + 1) d (baseFiberConfig m d ζtail ζ₀) =
          Fin.cons ζ₀ ζtail := by
      simpa [BHW.diffCoordEquiv_apply] using
        BHW.diffCoord_partialSum (m + 1) d (Fin.cons ζ₀ ζtail)
    calc
      Fin.cons ζ₀ ζtail
          = BHW.diffCoordFun (m + 1) d (baseFiberConfig m d ζtail ζ₀) := hcfg.symm
      _ = BHW.diffCoordFun (m + 1) d (BHW.complexLorentzAction Λ w) := by
            simp [hz]
      _ = BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) :=
            diffCoordFun_complexLorentzAction Λ w
  · rintro ⟨Λ, w, hw, hξ⟩
    refine ⟨Λ, w, hw, ?_⟩
    calc
      baseFiberConfig m d ζtail ζ₀
          = BHW.partialSumFun (m + 1) d (Fin.cons ζ₀ ζtail) := rfl
      _ = BHW.partialSumFun (m + 1) d
            (BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)) := by
              rw [hξ]
      _ = BHW.complexLorentzAction Λ
            (BHW.partialSumFun (m + 1) d (BHW.diffCoordFun (m + 1) d w)) := by
              exact partialSumFun_complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)
      _ = BHW.complexLorentzAction Λ w := by
            simp [BHW.partialSum_diffCoord]

/-- The permutation-sector geometry in difference coordinates. -/
def diffPermSector (m d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin (m + 1))) :
    Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
  {ξ | ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d (m + 1) π ∧
      ξ = BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)}

/-- A fixed-tail base-fiber sector is exactly the pullback of the corresponding
difference-coordinate sector along `Fin.cons`. -/
theorem baseFiberSector_eq_preimage_diffPermSector {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    baseFiberSector m d ζtail π =
      (fun ζ₀ => Fin.cons ζ₀ ζtail) ⁻¹' diffPermSector m d π := by
  ext ζ₀
  constructor
  · intro hζ₀
    rw [Set.mem_preimage]
    rcases (mem_baseFiberSector_iff_diffCoordWitness (m := m) (d := d) ζtail π ζ₀).mp hζ₀
      with ⟨Λ, w, hw, hξ⟩
    exact ⟨Λ, w, hw, hξ⟩
  · intro hζ₀
    rw [Set.mem_preimage] at hζ₀
    rcases hζ₀ with ⟨Λ, w, hw, hξ⟩
    exact (mem_baseFiberSector_iff_diffCoordWitness (m := m) (d := d) ζtail π ζ₀).mpr
      ⟨Λ, w, hw, hξ⟩

/-- Fixed-`Λ` slice of a base-fiber sector. -/
def baseFiberSectorSlice (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | ∃ w : Fin (m + 1) → Fin (d + 1) → ℂ,
      w ∈ PermutedForwardTube d (m + 1) π ∧
      baseFiberConfig m d ζtail ζ₀ = BHW.complexLorentzAction Λ w}

/-- A base-fiber sector is the union of its fixed-`Λ` slices. -/
theorem baseFiberSector_eq_iUnion_slice {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    baseFiberSector m d ζtail π = ⋃ Λ : ComplexLorentzGroup d, baseFiberSectorSlice m d ζtail π Λ := by
  ext ζ₀
  simp [baseFiberSector, baseFiberSectorSlice]

/-- Convex-combination formula for `baseFiberConfig` at fixed tail. -/
private theorem baseFiberConfig_convexCombo {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₁ ζ₂ : Fin (d + 1) → ℂ)
    (a b : ℝ) (hab : a + b = 1) :
    a • baseFiberConfig m d ζtail ζ₁ + b • baseFiberConfig m d ζtail ζ₂ =
      baseFiberConfig m d ζtail (a • ζ₁ + b • ζ₂) := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [baseFiberConfig_zero_apply, Pi.smul_apply]
  · intro i
    simp [baseFiberConfig_succ_apply, Pi.smul_apply, smul_add, add_assoc, add_left_comm]
    rw [← add_mul]
    have habC : (a : ℂ) + (b : ℂ) = 1 := by
      exact_mod_cast hab
    simp [habC]

/-- Real convex combinations commute with the coordinatewise complex Lorentz action. -/
private theorem complexLorentzAction_convexCombo {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (w₁ w₂ : Fin (m + 1) → Fin (d + 1) → ℂ)
    (a b : ℝ) :
    a • BHW.complexLorentzAction Λ w₁ + b • BHW.complexLorentzAction Λ w₂ =
      BHW.complexLorentzAction Λ (a • w₁ + b • w₂) := by
  ext k μ
  simp [BHW.complexLorentzAction, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem permutedForwardTube_convex_local {m d : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin (m + 1))) :
    Convex ℝ (PermutedForwardTube d (m + 1) π) := by
  simpa [BHW_permutedForwardTube_eq (d := d) (n := m + 1) π] using
    (BHW.permutedForwardTube_convex (d := d) (n := m + 1) π)

/-- Each fixed-`Λ` base-fiber sector slice is convex, hence preconnected. -/
theorem baseFiberSectorSlice_convex {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    Convex ℝ (baseFiberSectorSlice m d ζtail π Λ) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ a b ha hb hab
  rcases hζ₁ with ⟨w₁, hw₁, hz₁⟩
  rcases hζ₂ with ⟨w₂, hw₂, hz₂⟩
  refine ⟨a • w₁ + b • w₂, ?_, ?_⟩
  · exact permutedForwardTube_convex_local π hw₁ hw₂ ha hb hab
  · calc
      baseFiberConfig m d ζtail (a • ζ₁ + b • ζ₂)
          = a • baseFiberConfig m d ζtail ζ₁ + b • baseFiberConfig m d ζtail ζ₂ := by
              symm
              exact baseFiberConfig_convexCombo ζtail ζ₁ ζ₂ a b hab
      _ = a • BHW.complexLorentzAction Λ w₁ + b • BHW.complexLorentzAction Λ w₂ := by
            rw [hz₁, hz₂]
      _ = BHW.complexLorentzAction Λ (a • w₁ + b • w₂) :=
            complexLorentzAction_convexCombo Λ w₁ w₂ a b

theorem baseFiberSectorSlice_isPreconnected {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    IsPreconnected (baseFiberSectorSlice m d ζtail π Λ) :=
  (baseFiberSectorSlice_convex ζtail π Λ).isPreconnected

/-- Sector-decomposition reduction for base-fiber preconnectedness. This is the
exact analogue of `permutedExtendedTube_isPreconnected`, but on the fixed-tail
base fiber. Once sector slices are known to be preconnected and adjacent slices
overlap, the full base fiber is preconnected. -/
theorem baseFiber_isPreconnected_of_sector_geometry {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hsector : ∀ π : Equiv.Perm (Fin (m + 1)),
      IsPreconnected (baseFiberSector m d ζtail π))
    (hoverlap : ∀ (π : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1))
      (hi : i.val + 1 < m + 1),
      (baseFiberSector m d ζtail π ∩
        baseFiberSector m d ζtail (π * Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty) :
    IsPreconnected (baseFiber m d ζtail) := by
  rw [baseFiber_eq_iUnion_baseFiberSector]
  apply IsPreconnected.iUnion_of_reflTransGen
  · exact hsector
  · intro π₁ π₂
    set τ := π₁⁻¹ * π₂
    suffices h :
        ∀ σ : Equiv.Perm (Fin (m + 1)),
          Relation.ReflTransGen
            (fun i j =>
              (baseFiberSector m d ζtail i ∩ baseFiberSector m d ζtail j).Nonempty)
            π₁ (π₁ * σ) by
      have : π₂ = π₁ * τ := by simp [τ]
      rw [this]
      exact h τ
    intro σ
    induction σ using BHW.Fin.Perm.adjSwap_induction_right with
    | one =>
        simpa using Relation.ReflTransGen.refl
    | mul_adj σ₀ i₀ hi₀ ih =>
        apply Relation.ReflTransGen.tail ih
        simpa [baseFiberSector, mul_assoc] using hoverlap (π₁ * σ₀) i₀ hi₀

/-- **Preconnectedness of the fixed-tail base fiber.**

    For fixed tail difference coordinates `ζtail`, the set of base values `ζ₀`
    for which `baseFiberConfig m d ζtail ζ₀` lies in the permuted extended tube
    is preconnected.

    This is the cleaner remaining geometric blocker for BHW translation
    invariance. Once this theorem is available, the already-proved local
    translation invariance in `bhw_translation_local` upgrades to global
    constancy on the base fiber via
    `bhw_translation_invariant_of_baseFiber_isPreconnected`.

    Compared to the older overlap-domain theorem on
    `PET ∩ {z | z + c ∈ PET}`, this fiber statement matches the actual
    difference-variable geometry of translation invariance and avoids the
    false-looking 1-dimensional line-fiber route that was removed.

    **Numerical status (2026-03-14).** In the tested `d = 1`, `n = 2` regime,
    sampled base fibers remained connected even for the same shifts that split
    the one-complex-dimensional line fiber `Ω = {t | z + t c ∈ PET}`.

    Ref: Streater-Wightman §2.5; Jost, "General Theory of Quantized Fields" §III.1 -/
theorem isPreconnected_baseFiber {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    IsPreconnected (baseFiber m d ζtail) := by
  sorry

/-- **BHW extension is translation invariant on the permuted extended tube.**

    The n-point Wightman function depends only on the difference coordinates,
    so the BHW extension should be invariant under simultaneous translation
    `z_k ↦ z_k + c`.

    The formal proof here uses the fixed-tail base-fiber route:
    1. pass from absolute coordinates `z` to the cumulative difference variables
       `(ζ₀, ζtail)`;
    2. show the BHW extension has zero derivative in the base variable `ζ₀`
       by the local witness-chain theorem `bhw_translation_local`;
    3. use `isPreconnected_baseFiber` to promote local constancy to global
       constancy on the fixed-tail fiber;
    4. compare the two points `ζ₀` and `ζ₀ + c` on that fiber.

    Ref: Streater-Wightman §2.5 (translation invariance);
    Jost, "The General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hn : n = 0
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simp [hshift]
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  exact
    bhw_translation_invariant_of_baseFiber_isPreconnected (Wfn := Wfn)
      (m := m) (z := z) (c := c) hz hzc
      (isPreconnected_baseFiber
        (m := m) (d := d)
        (Fin.tail (BHW.diffCoordFun (m + 1) d z)))

/-- The smeared BHW extension equals the smeared W_analytic for approach directions
    within the forward tube cone.

    When the approach direction η has successive differences in V₊ (not just
    per-component V₊), the point x + iεη lies in the forward tube for all ε > 0.
    Since F_ext = W_analytic on the forward tube (BHW property 2), the integrals
    agree pointwise in ε, so the limits (distributional boundary values) also agree.

    This captures the forward-tube membership calculation: for z_k = x_k + iεη_k,
    the successive difference of imaginary parts is ε(η_k - η_{k-1}), which lies in
    V₊ when η has successive differences in V₊ and ε > 0 (V₊ is a cone).

    Ref: Streater-Wightman, Theorem 2-11; BHW property 2 -/
theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n).property.2.1
  -- x + iεη ∈ ForwardTube: successive differences of Im parts are ε·(η_k - η_{k-1}) ∈ V₊
  intro k
  show InOpenForwardCone d _
  -- The imaginary part of the successive difference is ε·(η_k - η_{k-1})
  have him : (fun μ => ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
      (if h : k.val = 0 then 0 else
        fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) + ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
      ε • (fun μ => η k μ - (if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
            Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
    · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      ring
  rw [him]
  exact inOpenForwardCone_smul d ε hε _ (hη_ft k)

/-- The BHW extension has the same distributional boundary values as W_n.

    The BHW extension F_ext agrees with W_analytic on the forward tube, and
    W_analytic has distributional boundary values recovering W_n by `spectrum_condition`.
    Therefore F_ext also has these boundary values: for η with each η_k ∈ V+,
    lim_{ε→0+} ∫ F_ext(x + iεη) f(x) dx = W_n(f).

    For `η : InForwardCone d n η`, the point `x + iεη` is in `ForwardTube d n` for
    every `ε > 0`. Hence `F_ext = W_analytic` pointwise on the whole integration path,
    and the claimed limit follows directly from `spectrum_condition`.

    Ref: Streater-Wightman Theorem 2-11 -/
theorem bhw_distributional_boundary_values {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  have h_sc := (Wfn.spectrum_condition n).choose_spec.2 f η hη
  refine Filter.Tendsto.congr' ?_ h_sc
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
    (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn f η hη ε hε).symm⟩

/-! #### Schwinger function construction -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the BHW extension F_ext (from `W_analytic_BHW`) composed
    with the Wick rotation map (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    where F_ext is the BHW extension of W_analytic to the permuted extended tube.
    We use F_ext rather than W_analytic because F_ext is defined and well-behaved
    on all Euclidean points (not just time-ordered ones), and carries the complex
    Lorentz invariance and permutation symmetry needed for E1b and E3.

    Important: this full-Schwartz pairing belongs to the Wightman side of the
    story. Wightman functions are tempered distributions on all of
    `SchwartzNPoint`, so there is no problem with a raw full-Schwartz pairing
    appearing here.

    What the corrected OS-I axiom surface forbids is interpreting this raw
    Euclidean Wick-rotated formula as the honest Schwinger object. The honest
    Euclidean Schwinger family of the project lives on `ZeroDiagonalSchwartz`.
    So the present definition should be read as the raw Wightman-side
    Wick-rotated boundary pairing, while `constructSchwingerFunctions` below is
    the actual zero-diagonal Euclidean Schwinger family.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def wickRotatedBoundaryPairing (Wfn : WightmanFunctions d) :
    (n : ℕ) → SchwartzNPoint d n → ℂ :=
  fun n f =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * (f x)

/-- The honest OS-I Euclidean family extracted from Wightman functions: the raw
    Wick-rotated pairing restricted to `ZeroDiagonalSchwartz`.

    This is the Euclidean Schwinger family that should appear in the OS axioms
    and in the `R -> E` direction. -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f => wickRotatedBoundaryPairing Wfn n f.1

/-- Auxiliary alias for the honest zero-diagonal Schwinger family. -/
abbrev constructZeroDiagonalSchwingerFunctions (Wfn : WightmanFunctions d) :
    ZeroDiagonalSchwingerFunctions d :=
  constructSchwingerFunctions Wfn

end
