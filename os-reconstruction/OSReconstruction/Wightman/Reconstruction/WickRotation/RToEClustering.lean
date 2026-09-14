import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReflectionPositivity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanClusterSection43

/-!
# R-to-E clustering through the Section 4.3 transform

The reflected positive-time pairing is a Wightman pairing of Fourier-Laplace
representatives. Spatial translation intertwines the two representations, so
R4 applies directly. This route does not use the conditional Ruelle bound or
the analytic cluster-lifting axiom. Compact support is retained explicitly
until the translation-uniform approximation step has been proved.
-/

noncomputable section

open scoped Topology
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The existing compact cross-pairing identity with arbitrary representatives
of the two transform components. No Euclidean and Minkowski test functions
are identified with one another. -/
theorem rToE_compact_pairing_eq_of_transformComponent
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hφ : section43FrequencyProjection d n φ =
      section43FourierLaplaceTransformComponent d n f.1 f.2 hf)
    (hψ : section43FrequencyProjection d m ψ =
      section43FourierLaplaceTransformComponent d m g.1 g.2 hg) :
    wickRotatedBoundaryPairing Wfn (n + m) (f.1.osConjTensorProduct g.1) =
      Wfn.W (n + m) (φ.conjTensorProduct ψ) := by
  have h :=
    compactOrderedSupport_constructSchwinger_cross_eq_section43_spectralPairing_currentAPI
      Wfn f g hf hg
  rw [← hφ, ← hψ] at h
  have hv :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f.1) (g := g.1) f.2 g.2
  simpa only [constructSchwingerFunctions,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hv,
    rToESection43SpectralPairing_apply] using h

/-- One-factor recovery from the same compact transform representative. -/
theorem rToE_compact_scalar_eq_of_transformComponent
    (Wfn : WightmanFunctions d) {n : ℕ}
    (g : euclideanPositiveTimeSubmodule (d := d) n)
    (hg : HasCompactSupport (g.1 : NPointDomain d n → ℂ))
    (ψ : SchwartzNPoint d n)
    (hψ : section43FrequencyProjection d n ψ =
      section43FourierLaplaceTransformComponent d n g.1 g.2 hg) :
    wickRotatedBoundaryPairing Wfn n g.1 = Wfn.W n ψ := by
  let e : SchwartzNPoint d 0 := (Reconstruction.vacuumSequence (d := d)).funcs 0
  have he : ∀ x, e x = 1 := fun _ => rfl
  have he_ord : tsupport (e : NPointDomain d 0 → ℂ) ⊆
      OrderedPositiveTimeRegion d 0 := by
    intro x _
    simp [OrderedPositiveTimeRegion]
  have he_compact : HasCompactSupport (e : NPointDomain d 0 → ℂ) :=
    HasCompactSupport.of_compactSpace _
  obtain ⟨φ, hφ⟩ := section43FrequencyProjection_surjective d 0
    (section43FourierLaplaceTransformComponent d 0 e he_ord he_compact)
  have hφ_eval : φ 0 = 1 := by
    simpa only [he] using
      section43TransformComponent_zero_eval_eq d φ e he_ord he_compact hφ
  have hpair := rToE_compact_pairing_eq_of_transformComponent Wfn
    ⟨e, he_ord⟩ g he_compact hg φ ψ hφ hψ
  have hleft : wickRotatedBoundaryPairing Wfn (0 + n) (e.osConjTensorProduct g.1) =
      wickRotatedBoundaryPairing Wfn n g.1 := by
    apply W_eq_of_cast (wickRotatedBoundaryPairing Wfn) (0 + n) n (Nat.zero_add n)
    intro x
    simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
      SchwartzNPoint.osConj_apply, he, map_one, one_mul]
    congr 1
    funext i
    simp [splitLast]
  have hright : Wfn.W (0 + n) (φ.conjTensorProduct ψ) = Wfn.W n ψ := by
    apply W_eq_of_cast Wfn.W (0 + n) n (Nat.zero_add n)
    intro x
    rw [SchwartzMap.conjTensorProduct_apply]
    have hfirst : (fun i : Fin 0 => splitFirst 0 n x (Fin.rev i)) =
        (0 : NPointDomain d 0) := Subsingleton.elim _ _
    rw [hfirst, hφ_eval, map_one, one_mul]
    congr 1
    funext i
    simp [splitLast]
  exact hleft.symm.trans (hpair.trans hright)

/-- Spatial clustering for compact ordered sources in the reflected OS
pairing, derived from R4. The spatial radius is uniform in direction. -/
theorem rToE_compact_reflected_cluster
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : Fin d → ℝ, (∑ i, (a i)^2) > R^2 →
      ‖wickRotatedBoundaryPairing Wfn (n + m)
          (f.1.osConjTensorProduct (translateSchwartzNPoint (Fin.cons 0 a) g.1)) -
        starRingEnd ℂ (wickRotatedBoundaryPairing Wfn n f.1) *
          wickRotatedBoundaryPairing Wfn m g.1‖ < ε := by
  obtain ⟨φ, hφ⟩ := section43FrequencyProjection_surjective d n
    (section43FourierLaplaceTransformComponent d n f.1 f.2 hf)
  obtain ⟨ψ, hψ⟩ := section43FrequencyProjection_surjective d m
    (section43FourierLaplaceTransformComponent d m g.1 g.2 hg)
  have hf_scalar := rToE_compact_scalar_eq_of_transformComponent Wfn f hf φ hφ
  have hg_scalar := rToE_compact_scalar_eq_of_transformComponent Wfn g hg ψ hψ
  have hφ_conj : Wfn.W n φ.borchersConj = starRingEnd ℂ (Wfn.W n φ) :=
    Wfn.hermitian n φ φ.borchersConj (fun _ => rfl)
  obtain ⟨R, hR, hcluster⟩ := Wfn.cluster n m φ.borchersConj ψ ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha
  have hga_ord := translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (Fin.cons 0 a) (by simp) g.1 g.2
  have hga_compact := translateSchwartzNPoint_hasCompactSupport (Fin.cons 0 a) g.1 hg
  have hψa : section43FrequencyProjection d m
        (translateSchwartzNPoint (Fin.cons 0 a) ψ) =
      section43FourierLaplaceTransformComponent d m
        (translateSchwartzNPoint (Fin.cons 0 a) g.1) hga_ord hga_compact := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have ht (u : SchwartzNPoint d 0) :
          translateSchwartzNPoint (Fin.cons 0 a) u = u := by
        ext x
        rw [translateSchwartzNPoint_apply]
        congr 1
        exact Subsingleton.elim _ _
      simpa only [ht] using hψ
    · exact section43FrequencyProjection_translate_spatial_of_transformComponent
        m hm a ψ g.1 g.2 hg hga_ord hga_compact hψ
  have hpair := rToE_compact_pairing_eq_of_transformComponent Wfn
    f ⟨_, hga_ord⟩ hf hga_compact φ
    (translateSchwartzNPoint (Fin.cons 0 a) ψ) hφ hψa
  rw [hpair, hf_scalar, hg_scalar]
  simpa only [SchwartzMap.conjTensorProduct, hφ_conj, Fin.cons_succ] using
    hcluster (Fin.cons 0 a) (by simp) (by simpa using ha)
      (translateSchwartzNPoint (Fin.cons 0 a) ψ)
      (fun x => translateSchwartzNPoint_apply _ _ x)

end OSReconstruction
