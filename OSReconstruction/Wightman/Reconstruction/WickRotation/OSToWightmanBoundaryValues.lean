/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesCompactApprox
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesEuclidean
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.WightmanTwoPoint

/-!
# OS to Wightman Boundary Values and Transfers

Public frontier for the boundary-value transfer layer. The valid support
infrastructure now lives across `OSToWightmanBoundaryValuesBase.lean` and the
slimmed `OSToWightmanBoundaryValuesComparison.lean`.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

theorem bv_cluster_transfer_of_canonical_eventually (n m : ℕ)
    (W_nm : SchwartzNPoint d (n + m) → ℂ)
    (W_n : SchwartzNPoint d n → ℂ)
    (W_m : SchwartzNPoint d m → ℂ)
    (F_nm : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hBV_canonical : ∀ h : SchwartzNPoint d (n + m),
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d (n + m),
          F_nm (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (h x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_nm h)))
    (hF_cluster :
      ∀ (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (ε : ℝ), 0 < ε →
        ∃ R : ℝ, R > 0 ∧
          ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
            ∀ (g_a : SchwartzNPoint d m),
              (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
              ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
                ‖(∫ x : NPointDomain d (n + m),
                    F_nm (fun k μ =>
                      ↑(x k μ) +
                        t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I) *
                      ((f.tensorProduct g_a) x)) - W_n f * W_m g‖ < ε) :
    ∀ (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖W_nm (f.tensorProduct g_a) - W_n f * W_m g‖ < ε := by
  intro f g ε hε
  obtain ⟨R, hR, hcluster⟩ := hF_cluster f g (ε / 2) (by linarith)
  refine ⟨R, hR, ?_⟩
  intro a ha0 ha_large g_a hg_a
  have hBV_fg := hBV_canonical (f.tensorProduct g_a)
  rw [Metric.tendsto_nhds] at hBV_fg
  have hnearW :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (∫ x : NPointDomain d (n + m),
            F_nm (fun k μ =>
              ↑(x k μ) +
                t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
              ((f.tensorProduct g_a) x))
          (W_nm (f.tensorProduct g_a)) < ε / 2 :=
    hBV_fg (ε / 2) (by linarith)
  have hnearProd := hcluster a ha0 ha_large g_a hg_a
  have hboth :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
            (∫ x : NPointDomain d (n + m),
              F_nm (fun k μ =>
                ↑(x k μ) +
                  t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
                ((f.tensorProduct g_a) x))
            (W_nm (f.tensorProduct g_a)) < ε / 2 ∧
          ‖(∫ x : NPointDomain d (n + m),
              F_nm (fun k μ =>
                ↑(x k μ) +
                  t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I) *
                ((f.tensorProduct g_a) x)) - W_n f * W_m g‖ < ε / 2 :=
    hnearW.and hnearProd
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  rcases hboth.exists with ⟨t, htW, htProd⟩
  have htProd' :
      dist
        (∫ x : NPointDomain d (n + m),
          F_nm (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            ((f.tensorProduct g_a) x))
        (W_n f * W_m g) < ε / 2 := by
    simpa [dist_eq_norm] using htProd
  have hdist :
      dist (W_nm (f.tensorProduct g_a)) (W_n f * W_m g) < ε := by
    calc
      dist (W_nm (f.tensorProduct g_a)) (W_n f * W_m g)
          ≤ dist (W_nm (f.tensorProduct g_a))
              (∫ x : NPointDomain d (n + m),
                F_nm (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct g_a) x)) +
              dist
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x))
                (W_n f * W_m g) := by
            simpa [dist_comm, add_comm] using
              (dist_triangle_right
                (W_nm (f.tensorProduct g_a))
                (W_n f * W_m g)
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)))
      _ < ε / 2 + ε / 2 := by
            have hadd : dist (W_nm (f.tensorProduct g_a))
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)) +
                dist
                  (∫ x : NPointDomain d (n + m),
                    F_nm (fun k μ =>
                      ↑(x k μ) +
                        t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I) *
                      ((f.tensorProduct g_a) x))
                  (W_n f * W_m g) <
              ε / 2 + ε / 2 := by
                exact add_lt_add (by simpa [dist_comm] using htW) htProd'
            exact hadd
      _ = ε := by ring
  simpa [dist_eq_norm] using hdist

theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  have hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
    intro a x η ε _hε
    let aNeg : Fin (d + 1) → ℂ := fun μ => -(a μ : ℂ)
    have hz :
        (fun j => (fun μ => ↑(x j μ) + ε * ↑(η j μ) * Complex.I) + aNeg) =
          (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) := by
      funext j μ
      simp [aNeg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      bvt_F OS lgc n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          bvt_F OS lgc n (fun j => (fun μ => ↑(x j μ) + ε * ↑(η j μ) * Complex.I) + aNeg) := by
            rw [hz.symm]
      _ = bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
            simpa [aNeg] using
              bvt_F_translationInvariant (d := d) OS lgc n
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) aNeg
  exact bv_translation_invariance_transfer (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    hF_inv a f g hfg

private theorem bvt_F_reflectCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I))
      =
      bvt_F OS lgc n (fun k μ =>
        ↑(x (Fin.rev k) μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n x ε hε
  let η := canonicalForwardConeDirection (d := d) n
  let a : Fin (d + 1) → ℂ := fun μ =>
    if μ = 0 then (((n : ℝ) + 1) * ε : ℂ) * Complex.I else 0
  let zrev : Fin n → Fin (d + 1) → ℂ := fun k μ =>
    ↑(x k μ) + ε * ↑(η (Fin.rev k) μ) * Complex.I
  have hshift :
      bvt_F OS lgc n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) =
        bvt_F OS lgc n zrev := by
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
      bvt_F OS lgc n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I)
          =
        bvt_F OS lgc n
          (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) := by
              symm
              exact bvt_F_translationInvariant OS lgc n _ a
      _ = bvt_F OS lgc n zrev := by rw [hzrev]
  have hperm :
      bvt_F OS lgc n zrev =
        bvt_F OS lgc n (fun k μ =>
          ↑(x (Fin.rev k) μ) +
            ε * ↑(η k μ) * Complex.I) := by
    simpa [zrev] using (bvt_F_perm OS lgc n Fin.revPerm zrev).symm
  calc
    starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(η k μ) * Complex.I))
        =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) -
          ε * ↑(η k μ) * Complex.I) := bvt_F_negCanonical OS lgc n x ε hε
    _ = bvt_F OS lgc n zrev := hshift
    _ = bvt_F OS lgc n (fun k μ =>
          ↑(x (Fin.rev k) μ) +
            ε * ↑(η k μ) * Complex.I) := hperm

/-- Theorem 1 frontier: Lorentz covariance of the Wick-section pairing.

OS paper target:
- OS II Theorem 4.1, p. 288 (real analyticity from `E0`, `E1`, `E2`)
- OS II Chapter V.1, pp. 290-293, especially `(5.5)`-`(5.7)` on p. 291

This sorry is the Wick-section Lorentz-covariance step on the active OS route.
It is not a same-shell comparison between Euclidean and Minkowski functionals. -/
private theorem bvt_F_lorentz_ortho_wick
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d),
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) *
                (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) := by
  intro n Λ φ _hφ_compact hφ_tsupport
  have hφ_coeff :
      (ZeroDiagonalSchwartz.ofClassical φ).1 = φ :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
      (d := d) (n := n) φ hφ_tsupport
  let Γ := wightmanToLorentzGroup (Λ⁻¹)
  have hpoint :
      ∀ x : NPointDomain d n,
        x ∈ tsupport (φ : NPointDomain d n → ℂ) →
          bvt_F OS lgc n (fun k μ =>
            ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
    intro x hx
    have hx_ft : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n := hφ_tsupport hx
    have hF_holo_BHW :
        DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using bvt_F_holomorphic OS lgc n
    have hF_dist_BHW :
        ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
          (hdet : R.det = 1) (horth : R.transpose * R = 1)
          (ψ : SchwartzNPoint d n),
            HasCompactSupport (ψ : NPointDomain d n → ℂ) →
            tsupport (ψ : NPointDomain d n → ℂ) ⊆
              {x : NPointDomain d n |
                (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n ∧
                  BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R hdet horth)
                    (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n} →
            ∫ x : NPointDomain d n,
                bvt_F OS lgc n
                  (BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R hdet horth)
                    (fun k => wickRotatePoint (x k))) * ψ x
              =
            ∫ x : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * ψ x := by
      intro R hdet horth ψ hψ_compact hψ_tsupport
      refine bvt_F_ofEuclidean_wick_pairing (d := d) OS lgc n R hdet horth ψ hψ_compact ?_
      intro x hx
      rcases hψ_tsupport hx with ⟨hx0, hx1⟩
      constructor
      · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx0
      · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx1
    have hx_ft_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx_ft
    have hΓ :=
      BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional
        (d := d) n
        (bvt_F OS lgc n)
        hF_holo_BHW
        hF_dist_BHW
        Γ (fun k => wickRotatePoint (x k)) hx_ft_BHW
    simpa [Γ, wightmanToLorentzGroup, lorentzGroupEquiv_symm_val] using hΓ
  refine MeasureTheory.integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport (φ : NPointDomain d n → ℂ)
    · simp [hpoint x hx]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hφ0 :
          (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) = 0 := by
        simpa [hφ_coeff] using hφx
      simp [hφ0]

/-- Theorem 2 frontier: locality / swap symmetry for the reconstructed
boundary-value functional.

OS paper target:
- OS I Section 4.5 "Locality", pp. 104-105
- OS II IV.2, p. 288, which says the remaining Wightman axioms are established
  as in Sections 4.2-4.5 of OS I

This sorry is the direct boundary-distributional locality statement on the OS
route.  It should be supplied by the OS Section 4.5 branch-difference /
boundary-transfer argument, not by any finite-height canonical-shell equality.
-/
private theorem bvt_W_swap_pairing_of_spacelike
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  sorry

/-- Theorem 3 frontier: positivity of the reconstructed Wightman inner product.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II IV.2, p. 288, reducing the remaining Wightman axioms to the OS I
  arguments after continuation

Current active substep on the repo's OS route:
- OS II Theorem 4.3, p. 289, together with Chapter VI.1, pp. 297-298

This sorry is the OS-isometry / boundary-value identification step, not any
same-test-function equality `W_n(f) = S_n(f)`. -/
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  intro F
  exact
    OSReconstruction.bvt_W_positive_of_component_dense_preimage (d := d) OS lgc
      (fun n =>
        OSReconstruction.dense_section43FourierLaplace_compact_ordered_preimage_raw d n)
      F

/-- Theorem 4 frontier: cluster transfer for the canonical BV pairing.

OS paper target:
- OS I Section 4.4 "Cluster Property", p. 103
- OS II IV.2, p. 288, which delegates the remaining Wightman axioms to
  Sections 4.2-4.5 of OS I after the continuation step

This sorry is downstream of the continuation/boundary-value route and should be
proved by the OS cluster/isometry logic, not by any deleted same-shell
comparison route. -/
private theorem bvt_F_clusterCanonicalEventually_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  sorry

private theorem bvt_F_clusterCanonicalEventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
              ‖(∫ x : NPointDomain d (n + m),
                  bvt_F OS lgc (n + m) (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)) -
                bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  intro n m f g ε hε
  obtain ⟨R, hR, hcluster⟩ :=
    bvt_F_clusterCanonicalEventually_translate (d := d) OS lgc n m f g ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha0 ha_large g_a hg_a
  have hga_eq :
      ∀ x : NPointDomain d m,
        g_a x = (translateSchwartzNPoint (d := d) a g) x := by
    intro x
    simpa [translateSchwartzNPoint_apply] using hg_a x
  have hfg_eq :
      ∀ x : NPointDomain d (n + m),
        (f.tensorProduct g_a) x =
          (f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x := by
    intro x
    simp [SchwartzMap.tensorProduct_apply, hga_eq (splitLast n m x)]
  filter_upwards [hcluster a ha0 ha_large] with t ht
  have hIntEq :
      ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) *
            ((f.tensorProduct g_a) x)
        =
      ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) *
            ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => by
      exact congrArg
        (fun z : ℂ =>
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) * z)
        (hfg_eq x))
  rw [hIntEq]
  exact ht

private theorem bvt_W_cluster
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  intro n m f g ε hε
  let η0 := canonicalForwardConeDirection (d := d) (n + m)
  have hη0 : InForwardCone d (n + m) η0 := canonicalForwardConeDirection_mem (d := d) (n + m)
  exact bv_cluster_transfer_of_canonical_eventually (d := d) n m
    (bvt_W OS lgc (n + m))
    (bvt_W OS lgc n)
    (bvt_W OS lgc m)
    (bvt_F OS lgc (n + m))
    (fun h => bvt_boundary_values (d := d) OS lgc (n + m) h η0 hη0)
    (bvt_F_clusterCanonicalEventually (d := d) OS lgc n m)
    f g ε hε

private theorem bvt_F_lorentz_orthoCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d),
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ =>
          ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n Λ x ε hε
  have hΛ : LorentzGroup.IsOrthochronous Λ := LorentzGroup.zero_zero_ge_one Λ
  let η := canonicalForwardConeDirection (d := d) n
  let ΛinvC : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun μ ν => ↑((Λ⁻¹).val μ ν)
  let ΛC : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun μ ν => ↑(Λ.val μ ν)
  let FInv : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    bvt_F OS lgc n (fun k => Matrix.mulVec ΛinvC (z k))
  have hFInv_hol : DifferentiableOn ℂ FInv (ForwardTube d n) := by
    apply DifferentiableOn.comp (bvt_F_holomorphic OS lgc n)
    · intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_pi.mpr
      intro k
      apply differentiableAt_pi.mpr
      intro μ
      have hcoord : ∀ (k : Fin n) (ν : Fin (d + 1)),
          DifferentiableAt ℂ (fun w : Fin n → Fin (d + 1) → ℂ => w k ν) z :=
        fun k' ν' =>
          differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_id k') ν'
      suffices h :
          ∀ (s : Finset (Fin (d + 1))),
            DifferentiableAt ℂ
              (fun w : Fin n → Fin (d + 1) → ℂ =>
                ∑ ν ∈ s, ΛinvC μ ν * w k ν) z by
        simpa [FInv, ΛinvC, Matrix.mulVec, dotProduct] using h Finset.univ
      intro s
      induction s using Finset.induction with
      | empty =>
          simp [differentiableAt_const]
      | @insert ν s hν ih =>
          simp only [Finset.sum_insert hν]
          exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
    · intro z hz
      exact orthochronous_preserves_forward_tube (d := d) Λ⁻¹
        (LorentzGroup.IsOrthochronous.inv hΛ) z hz
  have hint_inv :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            FInv (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) := by
    intro φ hφ_compact hφ_tsupport
    simpa [FInv, ΛinvC, Matrix.mulVec, dotProduct] using
      bvt_F_lorentz_ortho_wick (d := d) OS lgc n Λ φ hφ_compact hφ_tsupport
  have hpoint :=
    forwardTube_orthochronousLorentz_point_eq_of_zeroDiagonal_distributional_wickSection_eq
      (d := d) (n := n) FInv (bvt_F OS lgc n)
      hFInv_hol (bvt_F_holomorphic OS lgc n) hint_inv
      Λ hΛ x η (canonicalForwardConeDirection_mem (d := d) n) ε hε
  have hmul : (Λ⁻¹).val * Λ.val = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmulC : ΛinvC * ΛC = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    ext μ ρ
    have hentry :
        ((Λ⁻¹).val * Λ.val) μ ρ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) μ ρ :=
      congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M μ ρ) hmul
    calc
      (ΛinvC * ΛC) μ ρ
        = ↑(((Λ⁻¹).val * Λ.val) μ ρ) := by
            simp [ΛinvC, ΛC, Matrix.mul_apply]
      _ = ↑((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) μ ρ) := by
            exact congrArg (fun r : ℝ => (r : ℂ)) hentry
      _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) μ ρ := by
            by_cases hμρ : μ = ρ <;> simp [Matrix.one_apply, hμρ]
  have hleft :
      FInv (fun k μ =>
        ∑ ν, (↑(Λ.val μ ν) : ℂ) * (↑(x k ν) + ε * ↑(η k ν) * Complex.I))
        =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
    unfold FInv
    congr 1
    ext k μ
    have hk :
        Matrix.mulVec ΛinvC
            (Matrix.mulVec ΛC (fun ν =>
              ↑(x k ν) + ε * ↑(η k ν) * Complex.I))
          =
        (fun ν => ↑(x k ν) + ε * ↑(η k ν) * Complex.I) := by
      rw [Matrix.mulVec_mulVec]
      rw [hmulC, Matrix.one_mulVec]
    simpa [ΛC, Matrix.mulVec, dotProduct] using congrFun hk μ
  exact hpoint.symm.trans hleft

theorem bvt_lorentz_covariant_restricted
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        bvt_W OS lgc n f = bvt_W OS lgc n g := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (fun Γ _hΓ => bvt_F_lorentz_orthoCanonical (d := d) OS lgc n Γ)
    Λ (LorentzGroup.zero_zero_ge_one Λ) f g hfg

private theorem bvt_F_lorentz_restricted_wick
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) * (φ x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (φ x) := by
  intro n Λ φ hφ_compact hφ_tsupport
  exact W_analytic_lorentz_wick_pairing_eq_of_restrictedCovariance
    (d := d) (n := n)
    (bvt_W OS lgc n)
    (bvt_W_linear OS lgc n)
    (bvt_W_continuous OS lgc n)
    (fun Γ f g hfg =>
      bvt_lorentz_covariant_restricted (d := d) OS lgc n Γ f g hfg)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (full_analytic_continuation_with_acr_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2.2
    (bvt_boundary_values OS lgc n)
    Λ φ hφ_compact hφ_tsupport

private theorem bvt_F_lorentz_restrictedCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ =>
          ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n Λ x ε hε
  let z : Fin n → Fin (d + 1) → ℂ := fun k μ =>
    ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I
  have hη : InForwardCone d n (canonicalForwardConeDirection (d := d) n) :=
    canonicalForwardConeDirection_mem (d := d) n
  have hz : z ∈ ForwardTube d n := by
    have hη_abs :
        canonicalForwardConeDirection (d := d) n ∈ ForwardConeAbs d n :=
      (inForwardCone_iff_mem_forwardConeAbs
        (canonicalForwardConeDirection (d := d) n)).mp hη
    have hscaled_abs :
        ε • canonicalForwardConeDirection (d := d) n ∈ ForwardConeAbs d n :=
      forwardConeAbs_smul d n ε hε (canonicalForwardConeDirection (d := d) n) hη_abs
    rw [forwardTube_eq_imPreimage, Set.mem_setOf_eq]
    convert hscaled_abs using 1
    ext k μ
    simp [z, Pi.smul_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
  exact W_analytic_lorentz_on_tube_of_restrictedCovariance
    (d := d) (n := n)
    (bvt_W OS lgc n)
    (bvt_W_linear OS lgc n)
    (bvt_W_continuous OS lgc n)
    (fun Γ f g hfg =>
      bvt_lorentz_covariant_restricted (d := d) OS lgc n Γ f g hfg)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (full_analytic_continuation_with_acr_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2.2
    (bvt_boundary_values OS lgc n)
    Λ z hz

/-- The reconstructed boundary-value witness already satisfies the abstract
absolute forward-tube input interface used by the reduced BHW route. This keeps
the connected Lorentz covariance lane theorem-based, rather than
special-casing the old spectrum-condition package. -/
noncomputable def bvt_absoluteForwardTubeInput
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (m : ℕ) :
    BHW.AbsoluteForwardTubeInput (d := d) m (bvt_W OS lgc (m + 1)) where
  toFun := bvt_F OS lgc (m + 1)
  holomorphic := by
    simpa [BHW_forwardTube_eq (d := d) (n := m + 1)] using
      (bvt_F_holomorphic OS lgc (m + 1))
  real_lorentz_invariant := by
    intro Λ z hz
    exact W_analytic_lorentz_on_tube_of_restrictedCovariance
      (d := d) (n := m + 1)
      (bvt_W OS lgc (m + 1))
      (bvt_W_linear OS lgc (m + 1))
      (bvt_W_continuous OS lgc (m + 1))
      (fun Λ f g hfg =>
        bvt_lorentz_covariant_restricted (d := d) OS lgc (m + 1) Λ f g hfg)
      (bvt_F OS lgc (m + 1))
      (bvt_F_holomorphic OS lgc (m + 1))
      (full_analytic_continuation_with_acr_symmetry_growth OS lgc (m + 1)).choose_spec.2.2.2.2.2.2
      (bvt_boundary_values OS lgc (m + 1))
      Λ z ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hz)
  translation_invariant := by
    intro z c hz hzc
    exact bvt_F_translationInvariant OS lgc (m + 1) z c
  boundary_values := by
    intro f η hη
    simpa using bvt_boundary_values OS lgc (m + 1) f η hη

theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  exact bvt_lorentz_covariant_restricted (d := d) OS lgc

theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bvt_W_swap_pairing_of_spacelike (d := d) OS lgc n i j f g hsupp hswap

theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  exact bvt_W_positive (d := d) OS lgc

theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  have hF_reflect_pairing :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
    intro n f g ε hε hfg
    exact boundary_ray_hermitian_pairing_of_F_negCanonical (d := d) n
      (bvt_F OS lgc n)
      (bvt_F_perm OS lgc n)
      (bvt_F_translationInvariant OS lgc n)
      (bvt_F_negCanonical OS lgc n)
      f g ε hε hfg
  intro n f g hfg
  exact bv_hermiticity_transfer (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (hF_reflect_pairing n)
    f g hfg

theorem bvt_positiveTime_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
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
  exact
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) (bvt_hermitian (d := d) OS lgc) F hF_compact
      hWlimit

/-- Theorem 3 restated on the chosen scalar holomorphic `singleSplit_xiShift`
trace.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current regularization / boundary-value
  substep

The OS/Schwinger side of this limit is already packaged in
`OSToWightmanBoundaryValueLimits`; the remaining content is the Wightman-side
boundary-value identification of that same scalar holomorphic function. -/
theorem bvt_positiveTime_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) (bvt_hermitian (d := d) OS lgc) F hF_compact hHlimit

theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
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
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) OS lgc (bvt_hermitian (d := d) OS lgc) F hHlimit

theorem bvt_positiveTime_self_nonneg_of_compactApprox_timeShift_eq_osInner
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
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner
      (d := d) OS lgc F hkernel

theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
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
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian
      (d := d) OS lgc (bvt_hermitian (d := d) OS lgc) F hreal

/-
Deprecated route note:

The hypothesis `hschw` below is mathematically false on the intended theorem
surface. The left-hand side is the Euclidean/OS time-shifted Schwinger pairing,
whose free-field momentum-space form carries the Laplace factor `e^{-ω_p t}`;
the right-hand side is the reconstructed Wightman boundary-value pairing
against a real Minkowski time translation, whose free-field momentum-space form
carries the oscillatory factor `e^{-i ω_p t}`.

So this theorem is a logically valid implication from a false premise. It
remains harmless compiled legacy infrastructure, but it is no longer part of
the endorsed theorem-3 route. -/
theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
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
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian
      (d := d) OS lgc (bvt_hermitian (d := d) OS lgc) F hschw

theorem bvt_cluster (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  exact bvt_W_cluster (d := d) OS lgc

def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := bvt_W_linear OS lgc
  tempered := bvt_W_continuous OS lgc
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    refine ⟨bvt_F OS lgc n, bvt_F_holomorphic OS lgc n, ?_, bvt_boundary_values OS lgc n⟩
    -- Global polynomial growth for the same ACR-selected witness used by `bvt_F`.
    exact (full_analytic_continuation_with_acr_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2.2
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc
  cluster := bvt_cluster OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    data. -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
  OSPreHilbertSpace OS

/-! ### The Bridge Theorems -/

theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  intro n
  -- Witness the analytic continuation via the TranslatedPET-extended kernel,
  -- which agrees with F_ext on ForwardTube (⊆ PET) by
  -- `F_ext_on_translatedPET_total_eq_on_PET`.
  refine ⟨F_ext_on_translatedPET_total Wfn, ?_, ?_, fun _ => rfl⟩
  · -- Differentiable on ForwardTube: transport differentiability of F_ext via
    --   F_ext_on_translatedPET_total = F_ext on PET (hence on ForwardTube ⊆ PET).
    have hFT_PET : ForwardTube d n ⊆ PermutedExtendedTube d n :=
      ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)
    have hF_diff : DifferentiableOn ℂ (W_analytic_BHW Wfn n).val (ForwardTube d n) :=
      (W_analytic_BHW Wfn n).property.1.mono hFT_PET
    refine hF_diff.congr ?_
    intro z hz
    exact F_ext_on_translatedPET_total_eq_on_PET Wfn z (hFT_PET hz)
  · -- Boundary values: the limits agree with those of F_ext on ForwardTube,
    -- where the two kernels coincide pointwise.
    intro f η hη
    have hlim := bhw_distributional_boundary_values Wfn f η hη
    refine Filter.Tendsto.congr' ?_ hlim
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε => ?_⟩
    -- At each ε > 0 the integrands agree pointwise: x + iεη ∈ ForwardTube ⊆ PET.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hpoint : (fun k μ => (↑(x k μ) + ε * ↑(η k μ) * Complex.I : ℂ)) ∈
        ForwardTube d n := by
      intro k
      show InOpenForwardCone d _
      have him :
          (fun μ =>
              ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
                (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ) else
                  fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) +
                    ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
            ε • (fun μ => η k μ -
              (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else
                η ⟨k.val - 1, by omega⟩) μ) := by
        ext μ
        by_cases hk : (k : ℕ) = 0
        · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
                Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply,
                smul_eq_mul]
        · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im,
                Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
                Pi.smul_apply, smul_eq_mul]
          ring
      rw [him]
      exact inOpenForwardCone_smul d ε (by simpa using hε) _ (hη k)
    have hFT_PET : ForwardTube d n ⊆ PermutedExtendedTube d n :=
      ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)
    have hpet := hFT_PET hpoint
    rw [F_ext_on_translatedPET_total_eq_on_PET Wfn _ hpet]

theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.schwinger Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  exact ⟨bvt_F OS lgc n,
    bvt_F_holomorphic OS lgc n,
    bvt_boundary_values OS lgc n,
    fun f => by
      simpa [OsterwalderSchraderAxioms.schwinger] using
        bvt_euclidean_restriction OS lgc n f⟩

end
