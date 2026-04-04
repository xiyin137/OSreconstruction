/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WightmanTwoPoint

/-!
# OS to Wightman Boundary Values and Transfers

Public frontier for the boundary-value transfer layer after the large support
infrastructure now lives across `OSToWightmanBoundaryValuesBase.lean` and `OSToWightmanBoundaryValuesComparison.lean`.
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
  sorry

private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  sorry

private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  sorry

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
  exact bv_local_commutativity_transfer_of_swap_pairing (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_F_swapCanonical_pairing (d := d) OS lgc n)
    i j f g hsupp hswap

theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
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
    exact ⟨bvt_F OS lgc n, bvt_F_holomorphic OS lgc n, bvt_boundary_values OS lgc n⟩
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
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

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
