/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

/-!
# OS to Wightman (E'→R')

This file now contains the honest theorem-facing bridge surfaces only.

- `wightman_to_os_full` takes the extra forward-tube regularity, explicit BHW
  permutation/connectedness inputs, Euclidean Wick growth, and a.e.-PET inputs
  explicitly.
- `os_to_wightman_full` takes the forward-tube boundary-value package
  together with the explicit raw transfer inputs it needs.

The older internal analytic-continuation / boundary-value construction chain and
its six file-local transfer placeholders were removed once the exported theorem
surface stopped depending on them.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Minimal bridge residue

After the cleanup of the old internal continuation chain, the only genuinely
proved transfer lemma still used in this file is the zero-point normalization
statement below. All higher Wightman-axiom transfers are currently taken as
explicit inputs by `os_to_wightman_full`.
-/

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
    (hEuclid : ∀ (f : SchwartzNPoint d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f x)) :
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
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f := (hEuclid f).symm
    _ = f 0 := lgc.normalized_zero f

/-! ### The Bridge Theorems -/

-- `IsWickRotationPair` is defined in Reconstruction.lean (available via import).

/-- **Theorem R→E**: Wightman functions with the required forward-tube regularity,
    explicit BHW permutation/connectedness inputs, and the explicit E0/E1a/E2/E4
    transport inputs produce Schwinger functions satisfying E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation). The extra regularity package is the forward-tube
    Fourier-Laplace regularity needed by the BHW/Schwinger transport chain; it is
    stronger than the bare `spectrum_condition` fields currently bundled in
    `WightmanFunctions`. The separate `hPET_ae` input makes explicit the current
    dependence on the Euclidean-to-PET measure-zero geometry. The translation,
    reflection-positive, and cluster inputs are also explicit, since the corresponding
    transport theorems are not yet formalized from the current infrastructure. -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ n : ℕ,
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 : ∀ n : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z)
    (hEuclidPoly : ∀ n : ℕ,
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖(W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))‖ ≤
            C_bd * (1 + ‖x‖) ^ N)
    (hPET_ae : ∀ n : ℕ,
      ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
        (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hTranslation : ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => x i + a)) →
      constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f =
        constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n g)
    (hReflectionPositive : ∀ (F : BorchersSequence d),
      (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
        x ∈ PositiveTimeRegion d n) →
      (OSInnerProduct d (constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1) F F).re ≥ 0)
    (hCluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
      (ε : ℝ), ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 (n + m) (f.tensorProduct g_a) -
              constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f *
              constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 m g‖ < ε) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      -- The Schwinger functions are the Wick rotation of the Wightman functions
      IsWickRotationPair OS.S Wfn.W := by
  -- Construct OS axioms from Wightman functions
  refine ⟨⟨constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1,
    fun n => constructedSchwinger_tempered Wfn hRegular hSeedConn_hd2 hExtPerm_d1
      n (hPET_ae n) (hEuclidPoly n),
    hTranslation,
    fun n R hR hdet f g hfg =>
      constructedSchwinger_rotation_invariant Wfn hRegular hSeedConn_hd2 hExtPerm_d1
        n R (hPET_ae n) hR hdet f g hfg,
    hReflectionPositive,
    fun n σ f g hfg =>
      constructedSchwinger_symmetric Wfn hRegular hSeedConn_hd2 hExtPerm_d1
        n σ f g (hPET_ae n) hfg,
    hCluster⟩, ?_⟩
  -- Prove the Wick rotation pair property
  intro n
  -- Use the BHW extension F_ext as the IsWickRotationPair witness.
  -- F_ext = BHW extension, holomorphic on PET (hence on the forward tube).
  -- Its boundary values agree with W_n since F_ext = W_analytic on the forward tube.
  refine ⟨(W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val,
    (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · -- Boundary values: use bhw_distributional_boundary_values directly.
    -- The previous approach tried to show x + iεη ∈ ForwardTube, which is false
    -- due to coordinate convention mismatch (absolute vs difference coordinates).
    intro f η hη
    exact bhw_distributional_boundary_values Wfn (hRegular n)
      (hSeedConn_hd2 n) (hExtPerm_d1 n) f η hη

/-- **Theorem E'→R'**: OS axioms with linear growth condition together with an
    explicit forward-tube boundary-value package and the corresponding raw
    transfer proofs produce Wightman functions.

    The old internal continuation / transfer chain was removed once it became
    clear that the remaining six transfer statements were not derivable from the
    bare `hBVT` package alone with currently formalized infrastructure. The
    theorem surface is therefore explicit about the additional analytic inputs it
    uses. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hBVT : ∀ n : ℕ,
      ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        Continuous W_n ∧
        IsLinearMap ℂ W_n ∧
        DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
        (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (W_n f))) ∧
        (∀ (f : SchwartzNPoint d n),
          OS.S n f = ∫ x : NPointDomain d n,
            F_analytic (fun k => wickRotatePoint (x k)) * (f x)))
    (hTranslation : ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => x i + a)) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hLorentz : ∀ (n : ℕ) (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hLocal : ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hPositive : ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (fun n => (hBVT n).choose) F F).re ≥ 0)
    (hHermitian : ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      (hBVT n).choose g = starRingEnd ℂ ((hBVT n).choose f))
    (hCluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖(hBVT (n + m)).choose (f.tensorProduct g_a) -
              (hBVT n).choose f * (hBVT m).choose g‖ < ε) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the Schwinger functions
      IsWickRotationPair OS.S Wfn.W := by
  let W : (n : ℕ) → SchwartzNPoint d n → ℂ := fun n => (hBVT n).choose
  refine ⟨{
    W := W
    linear := by
      intro n
      exact (hBVT n).choose_spec.choose_spec.2.1
    tempered := by
      intro n
      exact (hBVT n).choose_spec.choose_spec.1
    normalized := by
      intro f
      exact bv_zero_point_is_evaluation OS lgc
        (W 0)
        ((hBVT 0).choose_spec.choose)
        ((hBVT 0).choose_spec.choose_spec.2.2.2.1)
        ((hBVT 0).choose_spec.choose_spec.2.2.2.2)
        f
    translation_invariant := by
      intro n a f g hfg
      exact hTranslation n a f g hfg
    lorentz_covariant := by
      intro n Λ f g hfg
      exact hLorentz n Λ f g hfg
    spectrum_condition := by
      intro n
      have h := (hBVT n).choose_spec.choose_spec
      exact ⟨(hBVT n).choose_spec.choose, h.2.2.1, h.2.2.2.1⟩
    locally_commutative := by
      intro n i j f g hsupp hswap
      exact hLocal n i j f g hsupp hswap
    positive_definite := by
      exact hPositive
    hermitian := by
      intro n f g hfg
      exact hHermitian n f g hfg
    cluster := by
      exact hCluster
  }, fun n => ?_⟩
  have h := (hBVT n).choose_spec.choose_spec
  exact ⟨(hBVT n).choose_spec.choose, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ### Wired Corollaries

The theorem wiring to canonical names now lives in
`Wightman/Reconstruction/Main.lean`. The `_full` theorems above remain the
implementation-level results used by that wiring layer. -/

end
