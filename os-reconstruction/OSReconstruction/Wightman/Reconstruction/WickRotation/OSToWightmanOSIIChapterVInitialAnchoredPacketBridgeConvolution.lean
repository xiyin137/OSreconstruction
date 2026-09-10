/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketTimeShell
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTotalTimePushforward













noncomputable section

open Complex Filter MeasureTheory
open scoped Classical BigOperators Convolution Pointwise Topology

namespace OSReconstruction
namespace OSIIChapterV

private theorem section43CompactPositiveTimeSource1D_ext
    {g h : Section43CompactPositiveTimeSource1D}
    (hf : g.f = h.f) :
    g = h := by
  cases g with
  | mk gf gp gc =>
      cases h with
      | mk hf hp hc =>
          simp only at hf
          subst hf
          rfl

/-- Translating both convolution factors to the right translates their
convolution by the sum of the two displacements. -/
theorem section43CompactPositiveTimeSource1D_convolution_translateRight
    (g h : Section43CompactPositiveTimeSource1D)
    (a b : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    section43CompactPositiveTimeSource1D_convolution
        (section43CompactPositiveTimeSource1D_translateRight g a ha)
        (section43CompactPositiveTimeSource1D_translateRight h b hb) =
      section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_convolution g h)
        (a + b) (add_nonneg ha hb) := by
  apply section43CompactPositiveTimeSource1D_ext
  ext t
  simp only [section43CompactPositiveTimeSource1D_convolution_apply,
    section43CompactPositiveTimeSource1D_translateRight,
    section43TranslateSchwartzReal_apply]
  calc
    (∫ s : ℝ, g.f (s + -a) * h.f (t - s + -b)) =
        ∫ u : ℝ,
          (fun s : ℝ =>
            g.f (s + -a) * h.f (t - s + -b)) (u + a) := by
      symm
      exact MeasureTheory.integral_add_right_eq_self
        (μ := (volume : Measure ℝ))
        (f := fun s : ℝ =>
          g.f (s + -a) * h.f (t - s + -b))
        a
    _ = ∫ u : ℝ, g.f u * h.f (t + -(a + b) - u) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      congr 2 <;> ring

/-- The three-factor version used by the physical bridge split. -/
theorem section43CompactPositiveTimeSource1D_totalConvolution_fin3_translateRight
    (g₀ g₁ g₂ : Section43CompactPositiveTimeSource1D)
    (a₀ a₁ a₂ : ℝ)
    (ha₀ : 0 ≤ a₀)
    (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) :
    section43CompactPositiveTimeSource1D_totalConvolution
        ![
          section43CompactPositiveTimeSource1D_translateRight g₀ a₀ ha₀,
          section43CompactPositiveTimeSource1D_translateRight g₁ a₁ ha₁,
          section43CompactPositiveTimeSource1D_translateRight g₂ a₂ ha₂] =
      section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_totalConvolution
          ![g₀, g₁, g₂])
        (a₀ + a₁ + a₂)
        (add_nonneg (add_nonneg ha₀ ha₁) ha₂) := by
  change
    section43CompactPositiveTimeSource1D_convolution
        (section43CompactPositiveTimeSource1D_translateRight g₀ a₀ ha₀)
        (section43CompactPositiveTimeSource1D_convolution
          (section43CompactPositiveTimeSource1D_translateRight g₁ a₁ ha₁)
          (section43CompactPositiveTimeSource1D_translateRight g₂ a₂ ha₂)) =
      section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_convolution g₀
          (section43CompactPositiveTimeSource1D_convolution g₁ g₂))
        (a₀ + a₁ + a₂)
        (add_nonneg (add_nonneg ha₀ ha₁) ha₂)
  rw [section43CompactPositiveTimeSource1D_convolution_translateRight
      g₁ g₂ a₁ a₂ ha₁ ha₂]
  calc
    section43CompactPositiveTimeSource1D_convolution
        (section43CompactPositiveTimeSource1D_translateRight g₀ a₀ ha₀)
        (section43CompactPositiveTimeSource1D_translateRight
          (section43CompactPositiveTimeSource1D_convolution g₁ g₂)
          (a₁ + a₂) (add_nonneg ha₁ ha₂)) =
      section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_convolution g₀
          (section43CompactPositiveTimeSource1D_convolution g₁ g₂))
        (a₀ + (a₁ + a₂))
        (add_nonneg ha₀ (add_nonneg ha₁ ha₂)) :=
      section43CompactPositiveTimeSource1D_convolution_translateRight
        g₀
        (section43CompactPositiveTimeSource1D_convolution g₁ g₂)
        a₀ (a₁ + a₂) ha₀ (add_nonneg ha₁ ha₂)
    _ = section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_convolution g₀
          (section43CompactPositiveTimeSource1D_convolution g₁ g₂))
        (a₀ + a₁ + a₂)
        (add_nonneg (add_nonneg ha₀ ha₁) ha₂) := by
      apply section43CompactPositiveTimeSource1D_ext
      ext t
      simp only [section43CompactPositiveTimeSource1D_translateRight,
        section43TranslateSchwartzReal_apply]
      congr 1
      ring

/-- Convolution preserves pointwise nonnegativity for real-valued compact
positive-time sources. -/
theorem section43CompactPositiveTimeSource1D_convolution_nonnegative
    (g h : Section43CompactPositiveTimeSource1D)
    (hg_nonnegative : ∀ x, 0 ≤ (g.f x).re)
    (hg_real : ∀ x, (g.f x).im = 0)
    (hh_nonnegative : ∀ x, 0 ≤ (h.f x).re)
    (hh_real : ∀ x, (h.f x).im = 0)
    (t : ℝ) :
    0 ≤
      ((section43CompactPositiveTimeSource1D_convolution g h).f t).re := by
  rw [section43CompactPositiveTimeSource1D_convolution_apply]
  have hint :
      Integrable (fun s : ℝ => g.f s * h.f (t - s)) := by
    exact
      (g.f.continuous.mul
        (h.f.continuous.comp
          (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        g.compact.mul_right
  have hre :
      (∫ s : ℝ, g.f s * h.f (t - s)).re =
        ∫ s : ℝ, (g.f s * h.f (t - s)).re := by
    simpa using (integral_re hint).symm
  rw [hre]
  exact MeasureTheory.integral_nonneg (fun s => by
    rw [Complex.mul_re, hg_real s, hh_real (t - s)]
    simpa using mul_nonneg (hg_nonnegative s) (hh_nonnegative (t - s)))

/-- Convolution preserves real-valuedness for compact positive-time
sources. -/
theorem section43CompactPositiveTimeSource1D_convolution_real
    (g h : Section43CompactPositiveTimeSource1D)
    (hg_real : ∀ x, (g.f x).im = 0)
    (hh_real : ∀ x, (h.f x).im = 0)
    (t : ℝ) :
    ((section43CompactPositiveTimeSource1D_convolution g h).f t).im = 0 := by
  rw [section43CompactPositiveTimeSource1D_convolution_apply]
  have hint :
      Integrable (fun s : ℝ => g.f s * h.f (t - s)) := by
    exact
      (g.f.continuous.mul
        (h.f.continuous.comp
          (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        g.compact.mul_right
  have him :
      (∫ s : ℝ, g.f s * h.f (t - s)).im =
        ∫ s : ℝ, (g.f s * h.f (t - s)).im := by
    simpa using (integral_im hint).symm
  rw [him]
  calc
    (∫ s : ℝ, (g.f s * h.f (t - s)).im) =
        ∫ _s : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [Complex.mul_im, hg_real s, hh_real (t - s)]
      ring
    _ = 0 := by simp

/-- The mass of a compact positive-time convolution is the product of the
two masses. -/
theorem section43CompactPositiveTimeSource1D_convolution_integral
    (g h : Section43CompactPositiveTimeSource1D) :
    (∫ t : ℝ,
        (section43CompactPositiveTimeSource1D_convolution g h).f t) =
      (∫ t : ℝ, g.f t) * ∫ t : ℝ, h.f t := by
  have hconv :=
    MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.mul ℝ ℂ)
      (g.f.integrable (μ := volume))
      (h.f.integrable (μ := volume))
  simpa [section43CompactPositiveTimeSource1D_convolution,
    ContinuousLinearMap.mul_apply] using hconv

/-- Ordinary support radii add under convolution. -/
theorem section43CompactPositiveTimeSource1D_convolution_support
    (g h : Section43CompactPositiveTimeSource1D)
    {r s : ℝ}
    (hg_support :
      Function.support (g.f : ℝ → ℂ) ⊆ Metric.ball 0 r)
    (hh_support :
      Function.support (h.f : ℝ → ℂ) ⊆ Metric.ball 0 s) :
    Function.support
        ((section43CompactPositiveTimeSource1D_convolution g h).f :
          ℝ → ℂ) ⊆
      Metric.ball 0 (r + s) := by
  intro x hx
  have hfun :
      ((section43CompactPositiveTimeSource1D_convolution g h).f :
        ℝ → ℂ) =
        ((g.f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          (h.f : ℝ → ℂ)) := by
    funext t
    rw [section43CompactPositiveTimeSource1D_convolution_apply]
    rfl
  have hxconv :
      x ∈ Function.support
        ((g.f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          (h.f : ℝ → ℂ)) := by
    rw [← hfun]
    exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    (MeasureTheory.support_convolution_subset
      (L := ContinuousLinearMap.mul ℝ ℂ) hxconv)
  have hu' := hg_support hu
  have hv' := hh_support hv
  rw [Metric.mem_ball, dist_zero_right] at hu' hv' ⊢
  exact (norm_add_le u v).trans_lt (add_lt_add hu' hv')

/-- A physical bridge source factored into the left positive head, the
semigroup bridge, and the right positive head. -/
structure Section43BridgeConvolutionFactorization
    (physicalBridge : Section43CompactPositiveTimeSource1D) where
  leftHead : Section43CompactPositiveTimeSource1D
  semigroupBridge : Section43CompactPositiveTimeSource1D
  rightHead : Section43CompactPositiveTimeSource1D
  physical_eq_totalConvolution :
    physicalBridge =
      section43CompactPositiveTimeSource1D_totalConvolution
        ![leftHead, semigroupBridge, rightHead]

namespace Section43BridgeConvolutionFactorization

end Section43BridgeConvolutionFactorization

namespace Section43ProductTimeApproximateIdentity

/-- A product approximate identity whose one-dimensional factors are exact
three-fold convolution powers. This is construction data, not an additional
hypothesis on an arbitrary approximate identity. -/
structure TripleConvolutionRootData
    {k : ℕ}
    (I : Section43ProductTimeApproximateIdentity k) where
  root :
    ℕ → Fin k → Section43CompactPositiveTimeSource1D
  root_nonnegative :
    ∀ N i x, 0 ≤ ((root N i).f x).re
  root_real :
    ∀ N i x, ((root N i).f x).im = 0
  root_integral_one :
    ∀ N i, ∫ x : ℝ, (root N i).f x = 1
  root_support :
    ∀ N i,
      Function.support ((root N i).f : ℝ → ℂ) ⊆
        Metric.ball 0 (I.radius N)
  factor_eq :
    ∀ N i,
      I.factors N i =
        section43CompactPositiveTimeSource1D_totalConvolution
          ![root N i, root N i, root N i]

/-- Product approximate identities with exact three-fold convolution roots
exist in every finite dimension. The roots are chosen directly at each scale,
and the product factors are defined to be their triple convolutions. -/
theorem nonempty_withTripleConvolutionRootData
    (k : ℕ) :
    ∃ I : Section43ProductTimeApproximateIdentity k,
      Nonempty (TripleConvolutionRootData I) := by
  let radius : ℕ → ℝ := fun N => 1 / (N + 1 : ℝ)
  have hradius_pos : ∀ N, 0 < radius N := by
    intro N
    dsimp [radius]
    positivity
  let root : ℕ → Section43CompactPositiveTimeSource1D := fun N =>
    Classical.choose
      (exists_section43CompactPositiveTimeSource1D_approx_identity
        (radius N / 8) (by positivity))
  have hroot :
      ∀ N,
        (∀ x : ℝ, 0 ≤ ((root N).f x).re) ∧
        (∀ x : ℝ, ((root N).f x).im = 0) ∧
        (∫ x : ℝ, (root N).f x = 1) ∧
        Function.support ((root N).f : ℝ → ℂ) ⊆
          Metric.ball (0 : ℝ) (radius N / 8) := by
    intro N
    simpa [root] using
      (Classical.choose_spec
        (exists_section43CompactPositiveTimeSource1D_approx_identity
          (radius N / 8) (by positivity)))
  let factor : ℕ → Section43CompactPositiveTimeSource1D := fun N =>
    section43CompactPositiveTimeSource1D_totalConvolution
      ![root N, root N, root N]
  have hroot_two_nonnegative :
      ∀ N x,
        0 ≤
          ((section43CompactPositiveTimeSource1D_convolution
            (root N) (root N)).f x).re := by
    intro N x
    exact
      section43CompactPositiveTimeSource1D_convolution_nonnegative
        (root N) (root N)
        (hroot N).1 (hroot N).2.1
        (hroot N).1 (hroot N).2.1 x
  have hroot_two_real :
      ∀ N x,
        ((section43CompactPositiveTimeSource1D_convolution
          (root N) (root N)).f x).im = 0 := by
    intro N x
    exact
      section43CompactPositiveTimeSource1D_convolution_real
        (root N) (root N)
        (hroot N).2.1 (hroot N).2.1 x
  have hfactor_nonnegative :
      ∀ N x, 0 ≤ ((factor N).f x).re := by
    intro N x
    exact
      section43CompactPositiveTimeSource1D_convolution_nonnegative
        (root N)
        (section43CompactPositiveTimeSource1D_convolution
          (root N) (root N))
        (hroot N).1 (hroot N).2.1
        (hroot_two_nonnegative N) (hroot_two_real N) x
  have hfactor_real :
      ∀ N x, ((factor N).f x).im = 0 := by
    intro N x
    exact
      section43CompactPositiveTimeSource1D_convolution_real
        (root N)
        (section43CompactPositiveTimeSource1D_convolution
          (root N) (root N))
        (hroot N).2.1 (hroot_two_real N) x
  have hroot_two_integral :
      ∀ N,
        ∫ x : ℝ,
          (section43CompactPositiveTimeSource1D_convolution
            (root N) (root N)).f x = 1 := by
    intro N
    rw [section43CompactPositiveTimeSource1D_convolution_integral,
      (hroot N).2.2.1]
    simp
  have hfactor_integral :
      ∀ N, ∫ x : ℝ, (factor N).f x = 1 := by
    intro N
    change
      (∫ x : ℝ,
        (section43CompactPositiveTimeSource1D_convolution
          (root N)
          (section43CompactPositiveTimeSource1D_convolution
            (root N) (root N))).f x) = 1
    rw [section43CompactPositiveTimeSource1D_convolution_integral,
      (hroot N).2.2.1, hroot_two_integral]
    simp
  have hroot_two_support :
      ∀ N,
        Function.support
            ((section43CompactPositiveTimeSource1D_convolution
              (root N) (root N)).f : ℝ → ℂ) ⊆
          Metric.ball 0 (radius N / 8 + radius N / 8) := by
    intro N
    exact
      section43CompactPositiveTimeSource1D_convolution_support
        (root N) (root N)
        (hroot N).2.2.2 (hroot N).2.2.2
  have hfactor_support_small :
      ∀ N,
        Function.support ((factor N).f : ℝ → ℂ) ⊆
          Metric.ball 0
            (radius N / 8 + (radius N / 8 + radius N / 8)) := by
    intro N
    exact
      section43CompactPositiveTimeSource1D_convolution_support
        (root N)
        (section43CompactPositiveTimeSource1D_convolution
          (root N) (root N))
        (hroot N).2.2.2 (hroot_two_support N)
  let factors :
      ℕ → Fin k → Section43CompactPositiveTimeSource1D :=
    fun N _ => factor N
  let I : Section43ProductTimeApproximateIdentity k :=
    { factors := factors
      radius := radius
      factor_nonnegative := by
        intro N i x
        exact hfactor_nonnegative N x
      factor_real := by
        intro N i x
        exact hfactor_real N x
      factor_integral_one := by
        intro N i
        exact hfactor_integral N
      factor_support := by
        intro N i x hx
        have hxsmall := hfactor_support_small N hx
        rw [Metric.mem_ball, dist_zero_right] at hxsmall ⊢
        exact hxsmall.trans (by
          have hpos := hradius_pos N
          linarith)
      nonnegative := by
        intro N x
        simp only [section43TimeProductSource, section43TimeProductTensor,
          SchwartzMap.productTensor_apply, factors]
        have hprod :
            0 ≤ (∏ i : Fin k, (factor N).f (x i)).re ∧
              (∏ i : Fin k, (factor N).f (x i)).im = 0 := by
          classical
          refine Finset.induction_on (Finset.univ : Finset (Fin k)) ?_ ?_
          · simp
          · intro a s has ih
            rw [Finset.prod_insert has]
            constructor
            · rw [Complex.mul_re, hfactor_real N (x a), ih.2]
              ring_nf
              exact mul_nonneg (hfactor_nonnegative N (x a)) ih.1
            · rw [Complex.mul_im, hfactor_real N (x a), ih.2]
              ring
        exact hprod.1
      real := by
        intro N x
        simp only [section43TimeProductSource, section43TimeProductTensor,
          SchwartzMap.productTensor_apply, factors]
        classical
        refine Finset.induction_on (Finset.univ : Finset (Fin k)) ?_ ?_
        · simp
        · intro a s has ih
          rw [Finset.prod_insert has, Complex.mul_im,
            hfactor_real N (x a), ih]
          ring
      integral_one := by
        intro N
        have hraw :=
          section43TimeProductSource_integral_eq_product_raw
            (gs := factors N) (σ := fun _ : Fin k => 0)
        calc
          (∫ x : Fin k → ℝ,
              (section43TimeProductSource (factors N)).f x) =
            ∫ x : Fin k → ℝ,
              Complex.exp
                  (-(∑ i : Fin k,
                    (x i : ℂ) * ((0 : ℝ) : ℂ))) *
                (section43TimeProductSource (factors N)).f x := by
              simp
          _ =
            ∏ i : Fin k,
              ∫ t : ℝ,
                Complex.exp
                    (-(t : ℂ) *
                      (((fun _ : Fin k => 0) i : ℝ) : ℂ)) *
                  (factors N i).f t := hraw
          _ = ∏ _i : Fin k, (1 : ℂ) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            simpa [factors] using hfactor_integral N
          _ = 1 := by simp
      support := by
        intro N x hx
        rw [Metric.mem_ball, dist_zero_right,
          pi_norm_lt_iff (hradius_pos N)]
        intro i
        have hx_prod_ne :
            (∏ j : Fin k, (factor N).f (x j)) ≠ 0 := by
          simpa [Function.mem_support, section43TimeProductSource,
            section43TimeProductTensor, SchwartzMap.productTensor_apply,
            factors] using hx
        have hxi_ne : (factor N).f (x i) ≠ 0 := by
          intro hzero
          exact hx_prod_ne
            (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
        have hxi_support :
            x i ∈ Function.support ((factor N).f : ℝ → ℂ) := by
          simpa [Function.mem_support] using hxi_ne
        have hxi_small := hfactor_support_small N hxi_support
        rw [Metric.mem_ball, dist_zero_right] at hxi_small
        exact hxi_small.trans (by
          have hpos := hradius_pos N
          linarith)
      radius_tendsto := by
        simpa [radius, Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Filter.Tendsto
              (fun N : ℕ => 1 / ((N : ℝ) + 1))
              Filter.atTop (nhds 0)) }
  refine ⟨I, ⟨?_⟩⟩
  exact
    { root := fun N _ => root N
      root_nonnegative := by
        intro N i x
        exact (hroot N).1 x
      root_real := by
        intro N i x
        exact (hroot N).2.1 x
      root_integral_one := by
        intro N i
        exact (hroot N).2.2.1
      root_support := by
        intro N i x hx
        change x ∈ Metric.ball 0 (radius N)
        have hxsmall := (hroot N).2.2.2 hx
        rw [Metric.mem_ball, dist_zero_right] at hxsmall ⊢
        have hpos := hradius_pos N
        linarith
      factor_eq := by
        intro N i
        rfl }

/-- One product approximate identity with triple-convolution roots, selected
before any later packet anchor.  The rooted recursive route needs constants
chosen before the moving anchor, so the approximate identity itself cannot be
reselected independently at each anchor. -/
noncomputable def fixedTripleConvolutionApproximateIdentity
    (k : ℕ) : Section43ProductTimeApproximateIdentity k :=
  Classical.choose (nonempty_withTripleConvolutionRootData k)

/-- Roots for `fixedTripleConvolutionApproximateIdentity`, likewise selected
before any packet anchor. -/
noncomputable def fixedTripleConvolutionRootData
    (k : ℕ) :
    TripleConvolutionRootData
      (fixedTripleConvolutionApproximateIdentity k) :=
  Classical.choice
    (Classical.choose_spec (nonempty_withTripleConvolutionRootData k))

/-- One coherent choice of a product approximate identity, exact triple
convolution roots, and the anchored packet shell built from that approximate
identity. This packages the constructive data needed by the rooted bridge
route without imposing a root hypothesis on an arbitrary packet family. -/
structure RootedAnchoredPacketTimeShellFamilyData
    {d k : ℕ} [NeZero d]
    (anchor : Fin k → ℝ) where
  approximateIdentity :
    Section43ProductTimeApproximateIdentity k
  roots :
    TripleConvolutionRootData approximateIdentity
  packet :
    AnchoredPacketTimeShellFamilyData
      (d := d) approximateIdentity anchor

namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The shrinking positive head used in the exact rooted bridge
factorization. Its center is one third of the physical bridge anchor. -/
noncomputable def rootedBridgeHead
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    Section43CompactPositiveTimeSource1D :=
  section43CompactPositiveTimeSource1D_translateRight
    (R.root (N + A.carrierData.tailStart) i.bridgeGlobalIndex)
    (anchor i.bridgeGlobalIndex / 3)
    (div_nonneg (A.anchor_positive i.bridgeGlobalIndex).le (by positivity))

/-- Rooted bridge heads remain pointwise nonnegative. -/
theorem rootedBridgeHead_nonnegative
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (t : ℝ) :
    0 ≤ ((A.rootedBridgeHead R i N).f t).re := by
  exact R.root_nonnegative
    (N + A.carrierData.tailStart) i.bridgeGlobalIndex
    (t + -(anchor i.bridgeGlobalIndex / 3))

/-- Rooted bridge heads remain real-valued. -/
theorem rootedBridgeHead_real
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (t : ℝ) :
    ((A.rootedBridgeHead R i N).f t).im = 0 := by
  exact R.root_real
    (N + A.carrierData.tailStart) i.bridgeGlobalIndex
    (t + -(anchor i.bridgeGlobalIndex / 3))

/-- Rooted bridge heads retain unit mass after translation. -/
theorem rootedBridgeHead_integral_one
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    ∫ t : ℝ, (A.rootedBridgeHead R i N).f t = 1 := by
  change
    (∫ t : ℝ,
      (R.root (N + A.carrierData.tailStart) i.bridgeGlobalIndex).f
        (t + -(anchor i.bridgeGlobalIndex / 3))) = 1
  rw [MeasureTheory.integral_add_right_eq_self]
  exact R.root_integral_one
    (N + A.carrierData.tailStart) i.bridgeGlobalIndex

/-- Split the anchored physical bridge factor into three exact positive
convolution factors by distributing its anchor equally among the three
translated roots. -/
noncomputable def rootedBridgeFactorization
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    Section43BridgeConvolutionFactorization (A.bridgeFactor i N) := by
  let j : Fin k := i.bridgeGlobalIndex
  let scale : ℕ := N + A.carrierData.tailStart
  let a : ℝ := anchor j / 3
  have ha : 0 ≤ a := by
    exact div_nonneg (A.anchor_positive j).le (by positivity)
  let root : Section43CompactPositiveTimeSource1D := R.root scale j
  let translatedRoot : Section43CompactPositiveTimeSource1D :=
    section43CompactPositiveTimeSource1D_translateRight root a ha
  refine
    { leftHead := translatedRoot
      semigroupBridge := translatedRoot
      rightHead := translatedRoot
      physical_eq_totalConvolution := ?_ }
  change
    section43CompactPositiveTimeSource1D_translateRight
        (I.factors scale j) (anchor j) (A.anchor_positive j).le =
      section43CompactPositiveTimeSource1D_totalConvolution
        ![translatedRoot, translatedRoot, translatedRoot]
  rw [R.factor_eq scale j]
  have htranslate :=
    section43CompactPositiveTimeSource1D_totalConvolution_fin3_translateRight
      root root root a a a ha ha ha
  calc
    section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_totalConvolution
          ![root, root, root])
        (anchor j) (A.anchor_positive j).le =
      section43CompactPositiveTimeSource1D_translateRight
        (section43CompactPositiveTimeSource1D_totalConvolution
          ![root, root, root])
        (a + a + a)
        (add_nonneg (add_nonneg ha ha) ha) := by
      apply section43CompactPositiveTimeSource1D_ext
      ext t
      simp only [section43CompactPositiveTimeSource1D_translateRight,
        section43TranslateSchwartzReal_apply]
      congr 1
      dsimp [a]
      ring
    _ = section43CompactPositiveTimeSource1D_totalConvolution
        ![translatedRoot, translatedRoot, translatedRoot] := htranslate.symm

@[simp]
theorem rootedBridgeFactorization_leftHead
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    (A.rootedBridgeFactorization R i N).leftHead =
      A.rootedBridgeHead R i N := rfl

@[simp]
theorem rootedBridgeFactorization_semigroupBridge
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    (A.rootedBridgeFactorization R i N).semigroupBridge =
      A.rootedBridgeHead R i N := rfl

@[simp]
theorem rootedBridgeFactorization_rightHead
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    (A.rootedBridgeFactorization R i N).rightHead =
      A.rootedBridgeHead R i N := rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
