/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairSourcewiseMZ

















noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d]

/-- The Chapter V.1 logarithmic carrier across all gap/direction coordinates.

The bound is global: the imaginary widths of different chronological gaps
share one `pi / 2` budget. -/
def osiiAxisPairMultiGapLogDomain (d k : ℕ) :
    Set (Fin k → osiiAxisPairIndex d → ℂ) :=
  {r |
    ∑ i : Fin k, ∑ a : osiiAxisPairIndex d, |(r i a).im| <
      Real.pi / 2}

/-- Total imaginary `l1` width in the multi-gap coefficient space.  This is
the scalar exhaustion whose strict sublevel set is the first logarithmic
carrier. -/
def osiiAxisPairMultiGapImaginaryWidth {d k : Nat}
    (r : Fin k -> osiiAxisPairIndex d -> Complex) : Real :=
  ∑ i : Fin k, ∑ a : osiiAxisPairIndex d, |(r i a).im|

@[simp] theorem mem_osiiAxisPairMultiGapLogDomain_iff
    {r : Fin k -> osiiAxisPairIndex d -> Complex} :
    r ∈ osiiAxisPairMultiGapLogDomain d k ↔
      osiiAxisPairMultiGapImaginaryWidth r < Real.pi / 2 :=
  Iff.rfl

/-- Every simultaneous real logarithmic point belongs to the global `l1`
carrier. -/
theorem osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairSimultaneousLogRealEmbed x ∈
      osiiAxisPairMultiGapLogDomain d k := by
  change
    (∑ i : Fin k,
      ∑ a : osiiAxisPairIndex d, |(((x i a : ℝ) : ℂ)).im|) <
        Real.pi / 2
  simpa using (half_pos Real.pi_pos)

/-- The global multi-gap logarithmic carrier is open. -/
theorem isOpen_osiiAxisPairMultiGapLogDomain :
    IsOpen (osiiAxisPairMultiGapLogDomain d k) := by
  have hcont :
      Continuous
        (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
          ∑ i : Fin k, ∑ a : osiiAxisPairIndex d, |(r i a).im|) := by
    exact continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun a _ =>
        (Complex.continuous_im.comp
          ((continuous_apply a).comp (continuous_apply i))).abs
  simpa [osiiAxisPairMultiGapLogDomain] using
    isOpen_lt hcont continuous_const

/-- The global multi-gap logarithmic carrier is convex. -/
theorem convex_osiiAxisPairMultiGapLogDomain :
    Convex ℝ (osiiAxisPairMultiGapLogDomain d k) := by
  intro z hz w hw c e hc he hce
  simp only [osiiAxisPairMultiGapLogDomain, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint :
      ∀ i : Fin k, ∀ a : osiiAxisPairIndex d,
        |((c • z + e • w) i a).im| ≤
          c * |(z i a).im| + e * |(w i a).im| := by
    intro i a
    calc
      |((c • z + e • w) i a).im|
          = |c * (z i a).im + e * (w i a).im| := by
              simp [Pi.smul_apply]
      _ ≤ |c * (z i a).im| + |e * (w i a).im| := abs_add_le _ _
      _ = c * |(z i a).im| + e * |(w i a).im| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg he]
  have hsum_le :
      (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |((c • z + e • w) i a).im|) ≤
        c * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(z i a).im|) +
        e * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(w i a).im|) := by
    calc
      (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |((c • z + e • w) i a).im|)
          ≤
        ∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d,
            (c * |(z i a).im| + e * |(w i a).im|) := by
              exact Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun a _ => hpoint i a
      _ =
        c * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(z i a).im|) +
        e * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(w i a).im|) := by
            simp [Finset.mul_sum, Finset.sum_add_distrib]
  have hlt :
      c * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(z i a).im|) +
        e * (∑ i : Fin k,
          ∑ a : osiiAxisPairIndex d, |(w i a).im|) <
        Real.pi / 2 := by
    by_cases hc0 : c = 0
    · subst hc0
      have he1 : e = 1 := by linarith
      simpa [he1] using hw
    · by_cases he0 : e = 0
      · subst he0
        have hc1 : c = 1 := by linarith
        simpa [hc1] using hz
      · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
        have he_pos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
        have hzmul :
            c * (∑ i : Fin k,
              ∑ a : osiiAxisPairIndex d, |(z i a).im|) <
              c * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hz hc_pos
        have hwmul :
            e * (∑ i : Fin k,
              ∑ a : osiiAxisPairIndex d, |(w i a).im|) <
              e * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left hw he_pos
        have hcombine :
            c * (Real.pi / 2) + e * (Real.pi / 2) =
              Real.pi / 2 := by
          calc
            c * (Real.pi / 2) + e * (Real.pi / 2) =
                (c + e) * (Real.pi / 2) := by ring
            _ = Real.pi / 2 := by rw [hce]; ring
        linarith
  exact lt_of_le_of_lt hsum_le hlt

/-- The global multi-gap logarithmic carrier is nonempty and connected. -/
theorem isConnected_osiiAxisPairMultiGapLogDomain :
    IsConnected (osiiAxisPairMultiGapLogDomain d k) := by
  refine
    ⟨⟨osiiAxisPairSimultaneousLogRealEmbed (fun _ _ => 0),
      osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
        (fun _ _ => 0)⟩,
      convex_osiiAxisPairMultiGapLogDomain.isPreconnected⟩

/-- A source-parametric MZ continuation on the actual Chapter V.1 multi-gap
carrier.

`n` is the number of Schwartz source slots and `k` is the number of
chronological gaps. -/
structure OSIIAxisPairMultiGapSourcewiseMZFamily
    (d n k : ℕ) [NeZero d] where
  toFun :
    (Fin n → SchwartzSpacetime d) →
      (Fin k → osiiAxisPairIndex d → ℂ) → ℂ
  holomorphic :
    ∀ fs : Fin n → SchwartzSpacetime d,
      DifferentiableOn ℂ (toFun fs)
        (osiiAxisPairMultiGapLogDomain d k)
  realEdge :
    (Fin k → osiiAxisPairIndex d → ℝ) →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ
  realEdge_eq :
    ∀ (fs : Fin n → SchwartzSpacetime d)
      (x : Fin k → osiiAxisPairIndex d → ℝ),
      toFun fs (osiiAxisPairSimultaneousLogRealEmbed x) =
        realEdge x fs

namespace OSIIAxisPairMultiGapSourcewiseMZFamily

/-- Totally-real uniqueness forces additivity in every source slot throughout
the global multi-gap carrier. -/
theorem map_update_add
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (hdec : DecidableEq (Fin n))
    (fs : Fin n → SchwartzSpacetime d)
    (i : Fin n) (f g : SchwartzSpacetime d)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    P.toFun (Function.update fs i (f + g)) z =
      P.toFun (Function.update fs i f) z +
        P.toFun (Function.update fs i g) z := by
  letI := hdec
  let F : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
    P.toFun (Function.update fs i (f + g))
  let G : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
    fun w =>
      P.toFun (Function.update fs i f) w +
        P.toFun (Function.update fs i g) w
  have hF :
      DifferentiableOn ℂ F
        (osiiAxisPairMultiGapLogDomain d k) :=
    P.holomorphic (Function.update fs i (f + g))
  have hG :
      DifferentiableOn ℂ G
        (osiiAxisPairMultiGapLogDomain d k) :=
    (P.holomorphic (Function.update fs i f)).add
      (P.holomorphic (Function.update fs i g))
  exact
    SCV.holomorphic_eq_of_eq_on_real_of_connected_finite_product
      isOpen_osiiAxisPairMultiGapLogDomain
      isConnected_osiiAxisPairMultiGapLogDomain
      hF hG
      (x₀ := fun _ _ => 0)
      (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
        (fun _ _ => 0))
      (fun x _hx => by
        dsimp [F, G]
        change
          P.toFun (Function.update fs i (f + g))
              (osiiAxisPairSimultaneousLogRealEmbed x) =
            P.toFun (Function.update fs i f)
                (osiiAxisPairSimultaneousLogRealEmbed x) +
              P.toFun (Function.update fs i g)
                (osiiAxisPairSimultaneousLogRealEmbed x)
        rw [P.realEdge_eq, P.realEdge_eq, P.realEdge_eq]
        exact (P.realEdge x).map_update_add fs i f g)
      z hz

/-- Totally-real uniqueness forces complex homogeneity in every source slot
throughout the global multi-gap carrier. -/
theorem map_update_smul
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (hdec : DecidableEq (Fin n))
    (fs : Fin n → SchwartzSpacetime d)
    (i : Fin n) (c : ℂ) (f : SchwartzSpacetime d)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    P.toFun (Function.update fs i (c • f)) z =
      c • P.toFun (Function.update fs i f) z := by
  letI := hdec
  let F : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
    P.toFun (Function.update fs i (c • f))
  let G : (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
    fun w => c • P.toFun (Function.update fs i f) w
  have hF :
      DifferentiableOn ℂ F
        (osiiAxisPairMultiGapLogDomain d k) :=
    P.holomorphic (Function.update fs i (c • f))
  have hG :
      DifferentiableOn ℂ G
        (osiiAxisPairMultiGapLogDomain d k) :=
    (P.holomorphic (Function.update fs i f)).const_smul c
  exact
    SCV.holomorphic_eq_of_eq_on_real_of_connected_finite_product
      isOpen_osiiAxisPairMultiGapLogDomain
      isConnected_osiiAxisPairMultiGapLogDomain
      hF hG
      (x₀ := fun _ _ => 0)
      (osiiAxisPairSimultaneousLogRealEmbed_mem_multiGap
        (fun _ _ => 0))
      (fun x _hx => by
        dsimp [F, G]
        change
          P.toFun (Function.update fs i (c • f))
              (osiiAxisPairSimultaneousLogRealEmbed x) =
            c • P.toFun (Function.update fs i f)
              (osiiAxisPairSimultaneousLogRealEmbed x)
        rw [P.realEdge_eq, P.realEdge_eq]
        exact (P.realEdge x).map_update_smul fs i c f)
      z hz

/-- At every interior multi-gap logarithmic point, the branch is algebraically
multilinear in all Schwartz source slots. -/
def toMultilinearMapAt
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    MultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d) ℂ := by
  classical
  exact
    { toFun := fun fs => P.toFun fs z
      map_update_add' := by
        intro hdec fs i f g
        letI := hdec
        exact P.map_update_add hdec fs i f g z hz
      map_update_smul' := by
        intro hdec fs i c f
        letI := hdec
        exact P.map_update_smul hdec fs i c f z hz }

/-- Pointwise continuous-linear approximation in every source slot upgrades
the multi-gap MZ value to one jointly continuous multilinear map. -/
theorem exists_continuousMultilinearMapAt_of_pointwise_clm_approximants
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k)
    (happrox :
      ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
        ∃ T : ℕ → SchwartzSpacetime d →L[ℂ] ℂ,
          ∀ f : SchwartzSpacetime d,
            Filter.Tendsto (fun q => T q f) Filter.atTop
              (nhds (P.toFun (Function.update fs i f) z))) :
    ∃ PhiCont :
        ContinuousMultilinearMap ℂ
          (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        PhiCont fs = P.toFun fs z := by
  refine
    exists_continuousMultilinear_ofSeparatelyContinuous d
      (P.toMultilinearMapAt z hz) ?_
  intro i fs
  obtain ⟨T, hT⟩ := happrox i fs
  exact
    OSIIAxisPairSourcewiseMZFamily.continuous_of_pointwise_tendsto_clm
      T _ hT

/-- One pointwise-convergent sequence of continuous multilinear approximants
supplies joint source continuity at a multi-gap logarithmic point. -/
theorem exists_continuousMultilinearMapAt_of_pointwise_cmm_approximants
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k)
    (A : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ)
    (hA : ∀ fs : Fin n → SchwartzSpacetime d,
      Filter.Tendsto (fun q => A q fs) Filter.atTop
        (nhds (P.toFun fs z))) :
    ∃ PhiCont :
        ContinuousMultilinearMap ℂ
          (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        PhiCont fs = P.toFun fs z := by
  apply
    P.exists_continuousMultilinearMapAt_of_pointwise_clm_approximants
      z hz
  intro i fs
  classical
  refine ⟨fun q => (A q).toContinuousLinearMap fs i, ?_⟩
  intro f
  simpa [ContinuousMultilinearMap.toContinuousLinearMap_apply] using
    hA (Function.update fs i f)

/-- Continuous multilinear approximants produce the unique full Schwartz
distribution realizing the multi-gap MZ value on pure product tensors. -/
theorem existsUnique_schwartzDistributionAt_of_pointwise_cmm_approximants
    (P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k)
    (A : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ)
    (hA : ∀ fs : Fin n → SchwartzSpacetime d,
      Filter.Tendsto (fun q => A q fs) Filter.atTop
        (nhds (P.toFun fs z))) :
    ∃! W : SchwartzNPoint d n →L[ℂ] ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        W (SchwartzMap.productTensor fs) = P.toFun fs z := by
  obtain ⟨Phi, hPhi⟩ :=
    P.exists_continuousMultilinearMapAt_of_pointwise_cmm_approximants
      z hz A hA
  obtain ⟨W, hW, hW_unique⟩ :=
    schwartz_nuclear_extension d n Phi
  refine ⟨W, ?_, ?_⟩
  · intro fs
    exact (hW fs).trans (hPhi fs)
  · intro W' hW'
    apply hW_unique W'
    intro fs
    rw [hW' fs, hPhi fs]

end OSIIAxisPairMultiGapSourcewiseMZFamily

end OSReconstruction
