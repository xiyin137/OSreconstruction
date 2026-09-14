/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketContinuity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapGrowthMZ
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIConfigurationTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanE0FiniteSeminorm
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import Mathlib.Data.Nat.Choose.Sum











noncomputable section

open Set
open scoped BigOperators Classical

namespace OSReconstruction

variable {d n m : ℕ} [NeZero d]

/-- Independent factor translations are one translation of the fixed full
product tensor on configuration space. -/
theorem translateSchwartzConfiguration_productTensor
    (a : NPointDomain d n)
    (fs : Fin n → SchwartzSpacetime d) :
    translateSchwartzConfiguration a
        (SchwartzMap.productTensor fs) =
      SchwartzMap.productTensor
        (fun j => SCV.translateSchwartz (a j) (fs j)) := by
  ext x
  simp [SchwartzMap.productTensor_apply]

/-- The complete finite Schwartz family is stable under independent point
translations with its exact weight order and a source-independent constant. -/
theorem osiiFiniteSchwartzSeminorm_translateSchwartzConfiguration_le
    (r : ℕ)
    (a : NPointDomain d n)
    (f : SchwartzNPoint d n) :
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)
        (translateSchwartzConfiguration a f) ≤
      (2 : ℝ) ^ r * (1 + ‖a‖) ^ r *
        (Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f := by
  let Q : ℝ :=
    (Finset.Iic (r, r)).sup
      (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f
  have hQ : 0 ≤ Q := apply_nonneg _ _
  change
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)
        (translateSchwartzConfiguration a f) ≤
      (2 : ℝ) ^ r * (1 + ‖a‖) ^ r * Q
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro ⟨p, l⟩ hpl
  have hp : p ≤ r := (Finset.mem_Iic.mp hpl).1
  have hl : l ≤ r := (Finset.mem_Iic.mp hpl).2
  apply SchwartzMap.seminorm_le_bound ℝ p l _ (by positivity)
  intro x
  rw [show
      (⇑(translateSchwartzConfiguration a f) :
        NPointDomain d n → ℂ) =
        (fun y => f (y + a)) by rfl,
    iteratedFDeriv_comp_add_right]
  have hx : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + a‖) := by
    have htriangle : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc
        ‖x‖ = ‖(x + a) - a‖ := by simp
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg a, norm_nonneg (x + a)]
  have hderivative :=
    SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (r, r)) hp hl f (x + a)
  calc
    ‖x‖ ^ p * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ ≤
        ((1 + ‖a‖) * (1 + ‖x + a‖)) ^ p *
          ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
      gcongr
    _ = (1 + ‖a‖) ^ p *
          ((1 + ‖x + a‖) ^ p *
            ‖iteratedFDeriv ℝ l f.toFun (x + a)‖) := by
      rw [mul_pow]
      ring
    _ ≤ (1 + ‖a‖) ^ p * ((2 : ℝ) ^ r * Q) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [Q] using hderivative) (by positivity)
    _ ≤ (1 + ‖a‖) ^ r * ((2 : ℝ) ^ r * Q) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by linarith [norm_nonneg a]) hp)
        (by positivity)
    _ = (2 : ℝ) ^ r * (1 + ‖a‖) ^ r * Q := by
      ring

/-- Configuration translations have polynomial growth in every Schwartz
seminorm. -/
theorem seminorm_translateSchwartzConfiguration_le
    (p l : ℕ) (f : SchwartzNPoint d n) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ a : NPointDomain d n,
        SchwartzMap.seminorm ℝ p l
            (translateSchwartzConfiguration a f) ≤
          D * (1 + ‖a‖) ^ p := by
  obtain ⟨Ck, hCk⟩ := f.decay' p l
  obtain ⟨C0, hC0⟩ := f.decay' 0 l
  have hC0' :
      ∀ y, ‖iteratedFDeriv ℝ l f.toFun y‖ ≤ C0 := by
    intro y
    have hy := hC0 y
    simpa using hy
  have hCk_nonneg : 0 ≤ Ck :=
    le_trans
      (mul_nonneg (pow_nonneg (norm_nonneg _) p) (norm_nonneg _))
      (hCk 0)
  have hC0_nonneg : 0 ≤ C0 :=
    le_trans (norm_nonneg _) (hC0' 0)
  let D : ℝ := 2 ^ (p - 1) * (Ck + C0)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD_nonneg, fun a => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ p l _
    (mul_nonneg hD_nonneg
      (pow_nonneg (by positivity) p))
  intro x
  rw [show
      (⇑(translateSchwartzConfiguration a f) :
          NPointDomain d n → ℂ) =
        fun z => f (z + a) by rfl,
    iteratedFDeriv_comp_add_right]
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by ring_nf
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have hbase : 1 ≤ 1 + ‖a‖ := by
    linarith [norm_nonneg a]
  have hconstants :
      Ck + ‖a‖ ^ p * C0 ≤
        (1 + ‖a‖) ^ p * (Ck + C0) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left hCk_nonneg
        (one_le_pow₀ hbase)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg a)
          (le_add_of_nonneg_left zero_le_one) p)
        hC0_nonneg
  calc
    ‖x‖ ^ p * ‖iteratedFDeriv ℝ l f.toFun (x + a)‖
        ≤ (‖x + a‖ + ‖a‖) ^ p *
            ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
          gcongr
    _ ≤
        (2 ^ (p - 1) * (‖x + a‖ ^ p + ‖a‖ ^ p)) *
          ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ := by
          gcongr
          exact add_pow_le (norm_nonneg _) (norm_nonneg _) p
    _ =
        2 ^ (p - 1) *
          (‖x + a‖ ^ p *
              ‖iteratedFDeriv ℝ l f.toFun (x + a)‖ +
            ‖a‖ ^ p *
              ‖iteratedFDeriv ℝ l f.toFun (x + a)‖) := by
          ring
    _ ≤ 2 ^ (p - 1) * (Ck + ‖a‖ ^ p * C0) := by
          gcongr
          · exact hCk (x + a)
          · exact hC0' (x + a)
    _ ≤ D * (1 + ‖a‖) ^ p := by
          dsimp [D]
          calc
            2 ^ (p - 1) * (Ck + ‖a‖ ^ p * C0) ≤
                2 ^ (p - 1) *
                  ((1 + ‖a‖) ^ p * (Ck + C0)) :=
              mul_le_mul_of_nonneg_left hconstants (by positivity)
            _ =
                (2 ^ (p - 1) * (Ck + C0)) *
                  (1 + ‖a‖) ^ p := by
              ring

/-- The polynomial degree in the translated-source estimate depends only on
the fixed continuous linear map and target seminorm.  The source changes only
the multiplicative constant. -/
theorem exists_uniformDegree_seminorm_clm_translateSchwartzConfiguration_le
    (L : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d m)
    (p l : ℕ) :
    ∃ N : ℕ, ∀ f : SchwartzNPoint d n,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ a : NPointDomain d n,
          SchwartzMap.seminorm ℝ p l
              (L (translateSchwartzConfiguration a f)) ≤
            C * (1 + ‖a‖) ^ N := by
  let q : Seminorm ℝ (SchwartzNPoint d n) :=
    (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ (p, l)).comp
      (L.restrictScalars ℝ).toLinearMap
  have hq_cont : Continuous q := by
    exact
      ((schwartz_withSeminorms ℝ (NPointDomain d m) ℂ).continuous_seminorm
        (p, l)).comp L.continuous
  obtain ⟨s, C₀, _hC₀, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ) q hq_cont
  refine ⟨s.sup (fun i => i.1), fun f => ?_⟩
  let D : ℕ × ℕ → ℝ :=
    fun i =>
      (seminorm_translateSchwartzConfiguration_le
        (d := d) i.1 i.2 f).choose
  have hD_nonneg : ∀ i, 0 ≤ D i :=
    fun i =>
      (seminorm_translateSchwartzConfiguration_le
        (d := d) i.1 i.2 f).choose_spec.1
  have hD_bound :
      ∀ i a,
        SchwartzMap.seminorm ℝ i.1 i.2
            (translateSchwartzConfiguration a f) ≤
          D i * (1 + ‖a‖) ^ i.1 :=
    fun i a =>
      (seminorm_translateSchwartzConfiguration_le
        (d := d) i.1 i.2 f).choose_spec.2 a
  refine
    ⟨(C₀ : ℝ) * ∑ i ∈ s, D i,
      mul_nonneg C₀.prop
        (Finset.sum_nonneg fun i _ => hD_nonneg i), fun a => ?_⟩
  have hq :
      q (translateSchwartzConfiguration a f) =
        SchwartzMap.seminorm ℝ p l
          (L (translateSchwartzConfiguration a f)) :=
    rfl
  rw [← hq]
  have h1 :
      q (translateSchwartzConfiguration a f) ≤
        (C₀ : ℝ) *
          (s.sup
            (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ))
            (translateSchwartzConfiguration a f) := by
    have h := hbound (translateSchwartzConfiguration a f)
    simpa only [Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] using h
  have h2 :
      (s.sup
          (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ))
          (translateSchwartzConfiguration a f) ≤
        ∑ i ∈ s, D i * (1 + ‖a‖) ^ i.1 := by
    apply Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hD_nonneg i) (by positivity))
    intro i hi
    exact (hD_bound i a).trans
      (Finset.single_le_sum
        (fun j _ =>
          mul_nonneg (hD_nonneg j)
            (pow_nonneg (by linarith [norm_nonneg a]) _)) hi)
  have h3 :
      ∑ i ∈ s, D i * (1 + ‖a‖) ^ i.1 ≤
        (∑ i ∈ s, D i) *
          (1 + ‖a‖) ^ s.sup (fun i => i.1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hD_nonneg i)
    exact pow_le_pow_right₀ (by linarith [norm_nonneg a])
      (Finset.le_sup (f := fun i => i.1) hi)
  calc
    q (translateSchwartzConfiguration a f)
        ≤ (C₀ : ℝ) *
            (s.sup
              (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ))
              (translateSchwartzConfiguration a f) := h1
    _ ≤ (C₀ : ℝ) *
          (∑ i ∈ s, D i * (1 + ‖a‖) ^ i.1) :=
      mul_le_mul_of_nonneg_left h2 C₀.prop
    _ ≤ (C₀ : ℝ) *
          ((∑ i ∈ s, D i) *
            (1 + ‖a‖) ^ s.sup (fun i => i.1)) :=
      mul_le_mul_of_nonneg_left h3 C₀.prop
    _ =
        ((C₀ : ℝ) * ∑ i ∈ s, D i) *
          (1 + ‖a‖) ^ s.sup (fun i => i.1) := by
      ring

/-- A finite target-seminorm family has one translated-source growth degree
uniform over the source. -/
theorem exists_uniformDegree_finsetSup_seminorm_clm_translateSchwartzConfiguration_le
    (L : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d m)
    (t : Finset (ℕ × ℕ)) :
    ∃ N : ℕ, ∀ f : SchwartzNPoint d n,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ a : NPointDomain d n,
          (t.sup
            (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ))
              (L (translateSchwartzConfiguration a f)) ≤
            C * (1 + ‖a‖) ^ N := by
  have hexists :
      ∀ i : ℕ × ℕ,
        ∃ N : ℕ, ∀ f : SchwartzNPoint d n,
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ a : NPointDomain d n,
              SchwartzMap.seminorm ℝ i.1 i.2
                  (L (translateSchwartzConfiguration a f)) ≤
                C * (1 + ‖a‖) ^ N :=
    fun i =>
      exists_uniformDegree_seminorm_clm_translateSchwartzConfiguration_le
        (d := d) L i.1 i.2
  choose N hN using hexists
  refine ⟨t.sup N, fun f => ?_⟩
  choose C hC_nonneg hbound using fun i => hN i f
  refine
    ⟨∑ i ∈ t, C i,
      Finset.sum_nonneg fun i _ => hC_nonneg i, fun a => ?_⟩
  apply Seminorm.finset_sup_apply_le
    (mul_nonneg
      (Finset.sum_nonneg fun i _ => hC_nonneg i)
      (pow_nonneg (by linarith [norm_nonneg a]) _))
  intro i hi
  calc
    SchwartzMap.seminorm ℝ i.1 i.2
        (L (translateSchwartzConfiguration a f))
        ≤ C i * (1 + ‖a‖) ^ N i :=
      hbound i a
    _ ≤ C i * (1 + ‖a‖) ^ t.sup N := by
      apply mul_le_mul_of_nonneg_left _ (hC_nonneg i)
      exact pow_le_pow_right₀ (by linarith [norm_nonneg a])
        (Finset.le_sup (f := N) hi)
    _ ≤ (∑ j ∈ t, C j) * (1 + ‖a‖) ^ t.sup N := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum
        (fun j _ => hC_nonneg j) hi

/-- Ordinary fixed-arity OS continuity controls every positive-time Hilbert
source by one finite ambient Schwartz-seminorm family. No E0' growth
hypothesis is required. -/
theorem exists_osiiPositiveTimeSingleVector_norm_sq_finsetSup_bound
    (d r : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    ∃ t : Finset (Nat × Nat), ∃ K : Real, 0 <= K ∧
      ∀ (g : SchwartzNPoint d r)
          (hg : tsupport (g : NPointDomain d r -> Complex) <=
            OrderedPositiveTimeRegion d r),
        norm (osiiPositiveTimeSingleVectorCLM OS r ⟨g, hg⟩) ^ 2 <=
          K *
            (t.sup (schwartzSeminormFamily Real
              (NPointDomain d r) Complex) g) ^ 2 := by
  let L := osiiPositiveTimeSingleVectorCLM OS r
  let p : SeminormFamily Complex
      ↥(euclideanPositiveTimeSubmodule (d := d) r) (Nat × Nat) :=
    (schwartzSeminormFamily Complex (NPointDomain d r) Complex).comp
      (euclideanPositiveTimeSubmodule (d := d) r).subtype
  let q : Seminorm Complex ↥(euclideanPositiveTimeSubmodule (d := d) r) :=
    (normSeminorm Complex (OSHilbertSpace OS)).comp L.toLinearMap
  have hp : WithSeminorms p :=
    Topology.IsInducing.withSeminorms
      (schwartz_withSeminorms
        (𝕜 := Complex) (E := NPointDomain d r) (F := Complex))
      Topology.IsInducing.subtypeVal
  have hq : Continuous q := by
    change Continuous fun g : ↥(euclideanPositiveTimeSubmodule (d := d) r) =>
      ‖L g‖
    exact continuous_norm.comp L.continuous
  obtain ⟨t, C, _hC_ne, hbound⟩ :=
    Seminorm.bound_of_continuous hp q hq
  refine ⟨t, (C : Real) ^ 2, sq_nonneg _, ?_⟩
  intro g hg
  have hnorm :
      ‖L ⟨g, hg⟩‖ <=
        (C : Real) *
          t.sup (schwartzSeminormFamily Real
            (NPointDomain d r) Complex) g := by
    calc
      ‖L ⟨g, hg⟩‖ = q ⟨g, hg⟩ := rfl
      _ <= (C • t.sup p) ⟨g, hg⟩ := hbound ⟨g, hg⟩
      _ = (C : Real) *
          t.sup (schwartzSeminormFamily Complex
            (NPointDomain d r) Complex) g := by
            change (C : Real) * (t.sup p) ⟨g, hg⟩ = _
            congr 1
            change
              (t.sup
                ((schwartzSeminormFamily Complex
                    (NPointDomain d r) Complex).comp
                  (euclideanPositiveTimeSubmodule (d := d) r).subtype)
              ) ⟨g, hg⟩ = _
            rw [← SeminormFamily.finset_sup_comp]
            rfl
      _ = (C : Real) *
          t.sup (schwartzSeminormFamily Real
            (NPointDomain d r) Complex) g := by
              rw [SCV.finsetSup_schwartzSeminormFamily_real_eq_complex]
  calc
    norm (osiiPositiveTimeSingleVectorCLM OS r ⟨g, hg⟩) ^ 2 <=
        ((C : Real) *
          t.sup (schwartzSeminormFamily Real
            (NPointDomain d r) Complex) g) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (C : Real) ^ 2 *
          (t.sup (schwartzSeminormFamily Real
            (NPointDomain d r) Complex) g) ^ 2 := by
      ring

/-- Two arbitrary Schwartz sources retain the same complete finite index
family under tensor product, with the explicit binomial constant. -/
theorem osiiFiniteSchwartzSeminorm_tensorProduct_le
    (r : ℕ)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m) :
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d (n + m)) ℂ)
        (f.tensorProduct g) ≤
      (2 : ℝ) ^ (r + r + 1) *
        ((Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f) *
        ((Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g) := by
  let t : Finset (ℕ × ℕ) := Finset.Iic (r, r)
  let Qf : ℝ :=
    t.sup (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f
  let Qg : ℝ :=
    t.sup (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g
  have hQf : 0 ≤ Qf := apply_nonneg _ _
  have hQg : 0 ≤ Qg := apply_nonneg _ _
  have hf {p l : ℕ} (hp : p ≤ r) (hl : l ≤ r) :
      SchwartzMap.seminorm ℝ p l f ≤ Qf := by
    change
      (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ (p, l)) f ≤
        t.sup (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f
    apply Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)
      (x := f)
    exact Finset.mem_Iic.mpr ⟨hp, hl⟩
  have hg {p l : ℕ} (hp : p ≤ r) (hl : l ≤ r) :
      SchwartzMap.seminorm ℝ p l g ≤ Qg := by
    change
      (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ (p, l)) g ≤
        t.sup (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g
    apply Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℝ (NPointDomain d m) ℂ)
      (x := g)
    exact Finset.mem_Iic.mpr ⟨hp, hl⟩
  change
    t.sup
        (schwartzSeminormFamily ℝ (NPointDomain d (n + m)) ℂ)
        (f.tensorProduct g) ≤
      (2 : ℝ) ^ (r + r + 1) * Qf * Qg
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro ⟨p, l⟩ hpl
  have hp : p ≤ r := (Finset.mem_Iic.mp hpl).1
  have hl : l ≤ r := (Finset.mem_Iic.mp hpl).2
  have hchoose :
      (∑ j ∈ Finset.range (l + 1), (l.choose j : ℝ)) =
        (2 : ℝ) ^ l := by
    exact_mod_cast Nat.sum_range_choose l
  calc
    SchwartzMap.seminorm ℝ p l (f.tensorProduct g) ≤
        2 ^ p *
          ∑ j ∈ Finset.range (l + 1),
            (l.choose j : ℝ) *
              (SchwartzMap.seminorm ℝ p j f *
                  SchwartzMap.seminorm ℝ 0 (l - j) g +
                SchwartzMap.seminorm ℝ 0 j f *
                  SchwartzMap.seminorm ℝ p (l - j) g) :=
      SchwartzMap.tensorProduct_seminorm_le
        (p := p) (l := l) f g
    _ ≤
        2 ^ p *
          ∑ j ∈ Finset.range (l + 1),
            (l.choose j : ℝ) * (Qf * Qg + Qf * Qg) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjr : j ≤ r := hjl.trans hl
      have hsubr : l - j ≤ r := (Nat.sub_le l j).trans hl
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact add_le_add
        (mul_le_mul (hf hp hjr) (hg (Nat.zero_le _) hsubr)
          (by positivity) hQf)
        (mul_le_mul (hf (Nat.zero_le _) hjr) (hg hp hsubr)
          (by positivity) hQf)
    _ = 2 ^ p * ((2 : ℝ) ^ l * (Qf * Qg + Qf * Qg)) := by
      rw [← Finset.sum_mul, hchoose]
    _ ≤ 2 ^ r * ((2 : ℝ) ^ r * (Qf * Qg + Qf * Qg)) := by
      exact mul_le_mul
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp)
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl)
          (by positivity))
        (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (r + r + 1) * Qf * Qg := by
      simp only [pow_add, pow_one]
      ring

/-- The complete finite Schwartz family of a reflected tensor is bounded by
the corresponding complete finite family of its source. -/
theorem osiiFiniteSchwartzSeminorm_osConjTensorProduct_le
    (r : ℕ) (g : SchwartzNPoint d m) :
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d (m + m)) ℂ)
        (g.osConjTensorProduct g) ≤
      (2 : ℝ) ^ (r + r + 1) *
        ((Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g) ^ 2 := by
  let Q : ℝ :=
    (Finset.Iic (r, r)).sup
      (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hconj :
      (Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g.osConj ≤ Q := by
    apply Seminorm.finset_sup_apply_le hQ
    intro ⟨p, l⟩ hpl
    exact
      (SchwartzNPoint.seminorm_osConj_le (d := d) p l g).trans
        (Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily ℝ (NPointDomain d m) ℂ)
          hpl)
  change
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d (m + m)) ℂ)
        (g.osConj.tensorProduct g) ≤
      (2 : ℝ) ^ (r + r + 1) * Q ^ 2
  calc
    (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d (m + m)) ℂ)
        (g.osConj.tensorProduct g) ≤
      (2 : ℝ) ^ (r + r + 1) *
        ((Finset.Iic (r, r)).sup
          (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g.osConj) * Q :=
      osiiFiniteSchwartzSeminorm_tensorProduct_le r g.osConj g
    _ ≤ (2 : ℝ) ^ (r + r + 1) * Q * Q := by
      gcongr
    _ = (2 : ℝ) ^ (r + r + 1) * Q ^ 2 := by
      ring

/-- At fixed maximum state degree, ordinary E0 controls every reflected
Hilbert-vector norm by one complete Schwartz rectangle and one coefficient. -/
theorem exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
    (d k : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    ∃ L : Nat, ∃ K : Real, 0 ≤ K ∧
      ∀ (r : Nat), r ≤ k →
        ∀ (g : SchwartzNPoint d r)
            (hg : tsupport (g : NPointDomain d r → Complex) ≤
              OrderedPositiveTimeRegion d r),
          ‖osiiPositiveTimeSingleVectorCLM OS r ⟨g, hg⟩‖ ^ 2 ≤
            K *
              ((Finset.Iic (L, L)).sup
                (schwartzSeminormFamily Real
                  (NPointDomain d r) Complex) g) ^ 2 := by
  obtain ⟨s, C, hC, hsource⟩ :=
    exists_zeroDiagonalSchwinger_evenArity_finsetSeminormBound OS k
  let L : Nat := s.sup fun i => max i.1 i.2
  have hs : s ⊆ Finset.Iic (L, L) := by
    intro i hi
    apply Finset.mem_Iic.mpr
    have hindex : max i.1 i.2 ≤ L := Finset.le_sup (f := fun j => max j.1 j.2) hi
    exact ⟨(le_max_left _ _).trans hindex, (le_max_right _ _).trans hindex⟩
  refine ⟨L, C * (2 : Real) ^ (L + L + 1), mul_nonneg hC (by positivity), ?_⟩
  intro r hr g hg
  have hzero :
      VanishesToInfiniteOrderOnCoincidence (g.osConjTensorProduct g) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := g) (g := g) hg hg
  have hE0 :
      ‖OS.S (r + r)
          (⟨g.osConjTensorProduct g, hzero⟩ :
            ZeroDiagonalSchwartz d (r + r))‖ ≤
        C * s.sup
          (schwartzSeminormFamily Complex
            (NPointDomain d (r + r)) Complex)
          (g.osConjTensorProduct g) := by
    have hsource_r := hsource r hr
    rw [two_mul] at hsource_r
    exact hsource_r
      (⟨g.osConjTensorProduct g, hzero⟩ :
        ZeroDiagonalSchwartz d (r + r))
  have hrectangle :
      s.sup
          (schwartzSeminormFamily Complex
            (NPointDomain d (r + r)) Complex)
          (g.osConjTensorProduct g) ≤
        (Finset.Iic (L, L)).sup
          (schwartzSeminormFamily Real
            (NPointDomain d (r + r)) Complex)
          (g.osConjTensorProduct g) := by
    rw [SCV.finsetSup_schwartzSeminormFamily_real_eq_complex]
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily Complex
      (NPointDomain d (r + r)) Complex) (hs hi)
  rw [osiiPositiveTimeSingleVectorCLM_norm_sq]
  calc
    (OS.S (r + r)
        (ZeroDiagonalSchwartz.ofClassical
          (g.osConjTensorProduct g))).re ≤
        ‖OS.S (r + r)
          (ZeroDiagonalSchwartz.ofClassical
            (g.osConjTensorProduct g))‖ := Complex.re_le_norm _
    _ = ‖OS.S (r + r)
          (⟨g.osConjTensorProduct g, hzero⟩ :
            ZeroDiagonalSchwartz d (r + r))‖ := by
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := g.osConjTensorProduct g) hzero]
    _ ≤ C * s.sup
          (schwartzSeminormFamily Complex
            (NPointDomain d (r + r)) Complex)
          (g.osConjTensorProduct g) := hE0
    _ ≤ C * (Finset.Iic (L, L)).sup
          (schwartzSeminormFamily Real
            (NPointDomain d (r + r)) Complex)
          (g.osConjTensorProduct g) :=
      mul_le_mul_of_nonneg_left hrectangle hC
    _ ≤ C * ((2 : Real) ^ (L + L + 1) *
          ((Finset.Iic (L, L)).sup
            (schwartzSeminormFamily Real
              (NPointDomain d r) Complex) g) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (osiiFiniteSchwartzSeminorm_osConjTensorProduct_le
          (d := d) L g) hC
    _ = (C * (2 : Real) ^ (L + L + 1)) *
          ((Finset.Iic (L, L)).sup
            (schwartzSeminormFamily Real
              (NPointDomain d r) Complex) g) ^ 2 := by
      ring

/-- Corrected OS-II arity-linear growth bounds an arity-`m` reflected
Hilbert norm using every factor seminorm through order `2 * m * s`. -/
theorem osiiPositiveTimeSingleVectorCLM_norm_sq_le_arityLinearFinsetSup
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSArityLinearGrowthCondition d OS)
    (g : SchwartzNPoint d m)
    (hg :
      tsupport (g : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    let r := (m + m) * lgc.sobolev_index
    let Q :=
      (Finset.Iic (r, r)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g
    ‖osiiPositiveTimeSingleVectorCLM OS m ⟨g, hg⟩‖ ^ 2 ≤
      (lgc.alpha * lgc.beta ^ (m + m) *
        ((m + m).factorial : ℝ) ^ lgc.gamma) *
          ((2 : ℝ) ^ (r + r + 1) * Q ^ 2) := by
  dsimp only
  let r := (m + m) * lgc.sobolev_index
  let Q : ℝ :=
    (Finset.Iic (r, r)).sup
      (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ) g
  let P : ℝ :=
    lgc.alpha * lgc.beta ^ (m + m) *
      ((m + m).factorial : ℝ) ^ lgc.gamma
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (mul_nonneg lgc.alpha_pos.le
        (pow_nonneg lgc.beta_pos.le _))
      (Real.rpow_nonneg (by positivity) _)
  have hzero :
      VanishesToInfiniteOrderOnCoincidence
        (g.osConjTensorProduct g) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := g) (g := g) hg hg
  rw [osiiPositiveTimeSingleVectorCLM_norm_sq]
  calc
    (OS.S (m + m)
        (ZeroDiagonalSchwartz.ofClassical
          (g.osConjTensorProduct g))).re ≤
        ‖OS.S (m + m)
          (ZeroDiagonalSchwartz.ofClassical
            (g.osConjTensorProduct g))‖ := Complex.re_le_norm _
    _ =
        ‖OS.S (m + m)
          (⟨g.osConjTensorProduct g, hzero⟩ :
            ZeroDiagonalSchwartz d (m + m))‖ := by
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := g.osConjTensorProduct g) hzero]
    _ ≤ P *
        osArityLinearSchwartzSeminorm d (m + m)
          lgc.sobolev_index (g.osConjTensorProduct g) := by
      simpa [P] using
        lgc.growth_estimate (m + m)
          (⟨g.osConjTensorProduct g, hzero⟩ :
            ZeroDiagonalSchwartz d (m + m))
    _ ≤ P * ((2 : ℝ) ^ (r + r + 1) * Q ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hP_nonneg
      simpa [osArityLinearSchwartzSeminorm, r, Q] using
        osiiFiniteSchwartzSeminorm_osConjTensorProduct_le
          (d := d) r g

/-- Ordinary fixed-arity E0 selects one translated-source growth degree before
the source is chosen; no arity-uniform growth hypothesis is needed. -/
theorem exists_uniformDegree_osiiPositiveTimeSingleVectorCLM_norm_sq_translate_bound
    (OS : OsterwalderSchraderAxioms d)
    (L : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d m) :
    ∃ N : ℕ, ∀ f : SchwartzNPoint d n,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ a : NPointDomain d n,
          ∀ hpositive :
            tsupport
                (L (translateSchwartzConfiguration a f) :
                  NPointDomain d m → ℂ) ⊆
              OrderedPositiveTimeRegion d m,
          ‖osiiPositiveTimeSingleVectorCLM OS m
            ⟨L (translateSchwartzConfiguration a f),
              hpositive⟩‖ ^ 2 ≤
            C * (1 + ‖a‖) ^ N := by
  obtain ⟨t, K, hK, hOS⟩ :=
    exists_osiiPositiveTimeSingleVector_norm_sq_finsetSup_bound d m OS
  obtain ⟨Nq, hq⟩ :=
    exists_uniformDegree_finsetSup_seminorm_clm_translateSchwartzConfiguration_le
      (d := d) L t
  refine ⟨Nq + Nq, fun f => ?_⟩
  obtain ⟨Cq, hCq, hqf⟩ := hq f
  refine
    ⟨K * Cq ^ 2,
      mul_nonneg hK (sq_nonneg Cq), fun a hpositive => ?_⟩
  let g := L (translateSchwartzConfiguration a f)
  let Q : ℝ :=
    (t.sup
      (schwartzSeminormFamily ℝ (NPointDomain d m) ℂ)) g
  have hQ_nonneg : 0 ≤ Q := apply_nonneg _ _
  have hQ_bound : Q ≤ Cq * (1 + ‖a‖) ^ Nq := by
    simpa [Q, g] using hqf a
  calc
    ‖osiiPositiveTimeSingleVectorCLM OS m
        ⟨g, hpositive⟩‖ ^ 2
        ≤ K * Q ^ 2 := by
      simpa [Q, g] using hOS g hpositive
    _ ≤ K * (Cq * (1 + ‖a‖) ^ Nq) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hQ_nonneg hQ_bound 2) hK
    _ =
        (K * Cq ^ 2) *
          (1 + ‖a‖) ^ (Nq + Nq) := by
      rw [pow_two, pow_add]
      ring

variable {k : ℕ} [NeZero k]

/-- Time reflection as a continuous linear endomorphism of `n`-point
Schwartz space. -/
noncomputable def schwartzNPointTimeReflectCLM :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n where
  toFun := SchwartzNPoint.timeReflect
  map_add' f g := by
    ext x
    simp [SchwartzNPoint.timeReflect_apply]
  map_smul' c f := by
    ext x
    simp [SchwartzNPoint.timeReflect_apply]
  cont := continuous_schwartzNPoint_timeReflect

@[simp]
theorem schwartzNPointTimeReflectCLM_apply
    (f : SchwartzNPoint d n) :
    schwartzNPointTimeReflectCLM f = f.timeReflect :=
  rfl

/-- A fixed proper Euclidean rotation as a continuous linear endomorphism of
`n`-point Schwartz space. -/
noncomputable def osiiEuclideanRotateSchwartzCLM
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (osiiEuclideanRotateNPointCLE (n := n) R hR)

@[simp]
theorem osiiEuclideanRotateSchwartzCLM_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzNPoint d n) :
    osiiEuclideanRotateSchwartzCLM R hR f =
      osiiEuclideanRotateSchwartz R hR f := by
  ext x
  rfl

/-- The fixed left reference tensor for one chronological gap. -/
def OSIIChronologicalCompactFactors.packetLeftReference
    (F : OSIIChronologicalCompactFactors d k)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
  SchwartzMap.productTensor
    (fun j =>
      let rj : Fin (osiiChronologicalGapLeftArity q.1) :=
        Fin.rev j
      let oi : Fin (k + 1) :=
        osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
      (F.factors oi).conj)

/-- The full tuple of independent left-source translations. -/
def OSIIChronologicalCompactFactors.packetLeftConfiguration
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    NPointDomain d (osiiChronologicalGapLeftArity q.1) :=
  fun j =>
    let rj : Fin (osiiChronologicalGapLeftArity q.1) :=
      Fin.rev j
    let oi : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
    (-F.packetCenter T hordered x q -
      osiiAxisPairChronologicalPointTranslationWithoutGap
        T x q.1 oi)

/-- The physical left packet source is one configuration translation of its
fixed reference tensor. -/
theorem OSIIChronologicalCompactFactors.packetLeftSource_eq_configurationTranslate
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetLeftSource T hordered x q =
      translateSchwartzConfiguration
        (F.packetLeftConfiguration T hordered x q)
        (F.packetLeftReference q) := by
  rw [F.packetLeftSource_eq_productTensor_translations]
  symm
  simpa [OSIIChronologicalCompactFactors.packetLeftReference,
    OSIIChronologicalCompactFactors.packetLeftConfiguration] using
    translateSchwartzConfiguration_productTensor
      (F.packetLeftConfiguration T hordered x q)
      (fun j =>
        let rj : Fin (osiiChronologicalGapLeftArity q.1) :=
          Fin.rev j
        let oi : Fin (k + 1) :=
          osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
        (F.factors oi).conj)

/-- The fixed right reference tensor for one chronological gap. -/
def OSIIChronologicalCompactFactors.packetRightReference
    (F : OSIIChronologicalCompactFactors d k)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
  SchwartzMap.productTensor
    (fun j =>
      F.factors
        (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))

/-- The full tuple of translations in the unfrozen right packet source. -/
def OSIIChronologicalCompactFactors.packetRightConfiguration
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    NPointDomain d (osiiChronologicalGapRightArity q.1) :=
  fun j =>
    -F.packetCenter T hordered x q -
      osiiAxisPairChronologicalPointTranslationWithoutGap
        T x q.1
        (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j))

/-- The unfrozen physical right source is one configuration translation of
its fixed reference tensor. -/
theorem OSIIChronologicalCompactFactors.packetRightSource_eq_configurationTranslate
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetRightSource T hordered x q =
      translateSchwartzConfiguration
        (F.packetRightConfiguration T hordered x q)
        (F.packetRightReference q) := by
  rw [OSIIChronologicalCompactFactors.packetRightSource,
    osiiAxisPairChronologicalCenteredRightSource_eq_productTensor_translations]
  symm
  simpa [OSIIChronologicalCompactFactors.packetRightReference,
    OSIIChronologicalCompactFactors.packetRightConfiguration] using
    translateSchwartzConfiguration_productTensor
      (F.packetRightConfiguration T hordered x q)
      (fun j =>
        F.factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))

/-- The fixed rotation and time reflection sending a left cone source to the
ordinary positive-time frame. -/
noncomputable def osiiPacketLeftPositiveCLM
    (T : ℝ) (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) →L[ℂ]
      SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
  schwartzNPointTimeReflectCLM.comp
    (osiiEuclideanRotateSchwartzCLM
      (osiiAxisPairRotationData T q.2).matrix
      (osiiAxisPairRotationData T q.2).orthogonal)

/-- The fixed rotation sending a frozen right cone source to the ordinary
positive-time frame. -/
noncomputable def osiiPacketRightPositiveCLM
    (T : ℝ) (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapRightArity q.1) →L[ℂ]
      SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
  osiiEuclideanRotateSchwartzCLM
    (osiiAxisPairRotationData T q.2).matrix
    (osiiAxisPairRotationData T q.2).orthogonal

/-- The left packet source in the ordinary positive-time frame. -/
def OSIIChronologicalCompactFactors.packetLeftPositiveSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
  osiiPacketLeftPositiveCLM T q
    (F.packetLeftSource T hordered x q)

/-- The unfrozen right packet source in the ordinary positive-time frame. -/
def OSIIChronologicalCompactFactors.packetRightPositiveSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
  osiiPacketRightPositiveCLM T q
    (F.packetRightSource T hordered x q)

theorem OSIIChronologicalCompactFactors.packetLeftPositiveSource_eq_configurationTranslate
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetLeftPositiveSource T hordered x q =
      osiiPacketLeftPositiveCLM T q
        (translateSchwartzConfiguration
          (F.packetLeftConfiguration T hordered x q)
          (F.packetLeftReference q)) := by
  rw [OSIIChronologicalCompactFactors.packetLeftPositiveSource,
    F.packetLeftSource_eq_configurationTranslate]

theorem OSIIChronologicalCompactFactors.packetRightPositiveSource_eq_configurationTranslate
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetRightPositiveSource T hordered x q =
      osiiPacketRightPositiveCLM T q
        (translateSchwartzConfiguration
          (F.packetRightConfiguration T hordered x q)
          (F.packetRightReference q)) := by
  rw [OSIIChronologicalCompactFactors.packetRightPositiveSource,
    F.packetRightSource_eq_configurationTranslate]

theorem OSIIChronologicalCompactFactors.packetLeftPositiveSource_support
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (F.packetLeftPositiveSource T hordered x q :
          NPointDomain d
            (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
      OrderedPositiveTimeRegion d
        (osiiChronologicalGapLeftArity q.1) := by
  apply SchwartzNPoint.timeReflect_tsupport_orderedPositive
  exact
    osiiEuclideanRotateSchwartz_tsupport_orderedNegative
      (osiiAxisPairRotationData T q.2).matrix
      (osiiAxisPairRotationData T q.2).orthogonal
      (F.packetLeftSource T hordered x q)
      (F.packetLeftSource_support T hT hordered x q)

theorem OSIIChronologicalCompactFactors.packetRightPositiveSource_support
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (F.packetRightPositiveSource T hordered x q :
          NPointDomain d
            (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
      OrderedPositiveTimeRegion d
        (osiiChronologicalGapRightArity q.1) := by
  exact
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      (osiiAxisPairRotationData T q.2).matrix
      (osiiAxisPairRotationData T q.2).orthogonal
      (F.packetRightSource T hordered x q)
      (F.packetRightSource_support T hT hordered x q)

/-- The genuine moving compensated packet is bounded by the two original-OS
source norms, with no arity-growth hypothesis or spurious semigroup factor. -/
theorem OSIIChronologicalCompactFactors.norm_compensatedMovingPacket_branchOfOS_le
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : ℂ) (hz : 0 < z.re) :
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (F.packetLeftSource T hordered x q)
        (F.packetLeftSource_support T hT hordered x q)
        (F.packetRightSource T hordered x q)
        (F.packetRightSource_support T hT hordered x q)).branchOfOS
          OS z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 +
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 := by
  let A : ℝ :=
    ‖osiiPositiveTimeSingleVectorCLM OS
      (osiiChronologicalGapLeftArity q.1)
      ⟨F.packetLeftPositiveSource T hordered x q,
        F.packetLeftPositiveSource_support
          T hT hordered x q⟩‖
  let B : ℝ :=
    ‖osiiPositiveTimeSingleVectorCLM OS
      (osiiChronologicalGapRightArity q.1)
      ⟨F.packetRightPositiveSource T hordered x q,
        F.packetRightPositiveSource_support
          T hT hordered x q⟩‖
  have hpacket :=
    OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branchOfOS_le
      OS T hT
      (osiiAxisPairPositiveCoefficients (x q.1))
      (fun b =>
        le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
      q.2
      (F.packetLeftSource T hordered x q)
      (F.packetLeftSource_support T hT hordered x q)
      (F.packetRightSource T hordered x q)
      (F.packetRightSource_support T hT hordered x q)
      z hz
  have hpacket' :
      ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          T hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b =>
            le_of_lt
              (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2
          (F.packetLeftSource T hordered x q)
          (F.packetLeftSource_support T hT hordered x q)
          (F.packetRightSource T hordered x q)
          (F.packetRightSource_support T hT hordered x q)).branchOfOS
            OS z‖ ≤
        A * B := by
    simpa [A, B,
      OSIIChronologicalCompactFactors.packetLeftPositiveSource,
      OSIIChronologicalCompactFactors.packetRightPositiveSource,
      osiiPacketLeftPositiveCLM,
      osiiPacketRightPositiveCLM] using hpacket
  calc
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (F.packetLeftSource T hordered x q)
        (F.packetLeftSource_support T hT hordered x q)
        (F.packetRightSource T hordered x q)
        (F.packetRightSource_support T hT hordered x q)).branchOfOS
          OS z‖
        ≤ A * B := hpacket'
    _ ≤ A ^ 2 + B ^ 2 := by
      have hA : 0 ≤ A := norm_nonneg _
      have hB : 0 ≤ B := norm_nonneg _
      nlinarith [sq_nonneg (A - B), mul_nonneg hA hB]

/-- The old growth-indexed moving packet estimate is only a compatibility
wrapper over the genuine original-OS physical source estimate. -/
theorem OSIIChronologicalCompactFactors.norm_compensatedMovingPacket_branch_le
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : ℂ) (hz : 0 < z.re) :
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (F.packetLeftSource T hordered x q)
        (F.packetLeftSource_support T hT hordered x q)
        (F.packetRightSource T hordered x q)
        (F.packetRightSource_support T hT hordered x q)).branch
          OS lgc z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 +
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support
              T hT hordered x q⟩‖ ^ 2 := by
  rw [OSIIAxisPairRotatedSourcePacket.branch_eq_branchOfOS _ OS lgc z hz]
  exact F.norm_compensatedMovingPacket_branchOfOS_le
    OS T hT hordered x q z hz

/-- Cancellation-free majorant for all physical chronological translations. -/
def osiiAxisPairChronologicalTranslationMajorant
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    ℝ :=
  ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
    Real.exp (x i a) * ‖osiiAxisPairDir (d := d) T a‖

theorem osiiAxisPairChronologicalTranslationMajorant_nonneg
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    0 ≤ osiiAxisPairChronologicalTranslationMajorant T x := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

/-- One full chronological gap is bounded by the global translation
majorant, first in its local summand. -/
theorem norm_osiiAxisPairChronologicalGapTranslation_le_localMajorant
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) :
    ‖osiiAxisPairChronologicalGapTranslation T x i‖ ≤
      ∑ a : osiiAxisPairIndex d,
        Real.exp (x i a) *
          ‖osiiAxisPairDir (d := d) T a‖ := by
  rw [osiiAxisPairChronologicalGapTranslation]
  calc
    ‖∑ a : osiiAxisPairIndex d,
        osiiAxisPairPositiveCoefficients (x i) a •
          osiiAxisPairDir (d := d) T a‖
        ≤ ∑ a : osiiAxisPairIndex d,
            ‖osiiAxisPairPositiveCoefficients (x i) a •
              osiiAxisPairDir (d := d) T a‖ :=
      norm_sum_le _ _
    _ =
        ∑ a : osiiAxisPairIndex d,
          Real.exp (x i a) *
            ‖osiiAxisPairDir (d := d) T a‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [osiiAxisPairPositiveCoefficients, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- One full chronological gap is bounded by the global translation
majorant. -/
theorem norm_osiiAxisPairChronologicalGapTranslation_le_majorant
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) :
    ‖osiiAxisPairChronologicalGapTranslation T x i‖ ≤
      osiiAxisPairChronologicalTranslationMajorant T x := by
  exact
    (norm_osiiAxisPairChronologicalGapTranslation_le_localMajorant
      T x i).trans
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin k)))
        (f := fun j =>
          ∑ a : osiiAxisPairIndex d,
            Real.exp (x j a) *
              ‖osiiAxisPairDir (d := d) T a‖)
        (fun j _ =>
          Finset.sum_nonneg fun a _ =>
            mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (Finset.mem_univ i))

/-- Every omitted-gap point displacement is bounded by the same global
majorant. -/
theorem norm_osiiAxisPairChronologicalPointTranslationWithoutGap_le_majorant
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (j : Fin (k + 1)) :
    ‖osiiAxisPairChronologicalPointTranslationWithoutGap
        T x selected j‖ ≤
      osiiAxisPairChronologicalTranslationMajorant T x := by
  rw [osiiAxisPairChronologicalPointTranslationWithoutGap]
  calc
    ‖∑ i ∈ (Finset.univ : Finset (Fin k)).erase selected,
        if i.val < j.val then
          osiiAxisPairChronologicalGapTranslation T x i
        else 0‖
        ≤
      ∑ i ∈ (Finset.univ : Finset (Fin k)).erase selected,
        ‖if i.val < j.val then
          osiiAxisPairChronologicalGapTranslation T x i
        else 0‖ :=
      norm_sum_le _ _
    _ ≤
      ∑ i ∈ (Finset.univ : Finset (Fin k)).erase selected,
        ∑ a : osiiAxisPairIndex d,
          Real.exp (x i a) *
            ‖osiiAxisPairDir (d := d) T a‖ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hij : i.val < j.val
      · simp only [if_pos hij]
        exact
          norm_osiiAxisPairChronologicalGapTranslation_le_localMajorant
            T x i
      · simp only [if_neg hij, norm_zero]
        exact Finset.sum_nonneg fun a _ =>
          mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    _ ≤
      ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp (x i a) *
          ‖osiiAxisPairDir (d := d) T a‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset selected Finset.univ)
        (fun i hi hnot =>
          Finset.sum_nonneg fun a _ =>
            mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

omit [NeZero d] [NeZero k] in
@[simp]
theorem osiiAxisPairMultiGapFlatten_apply_flattenIndex
    {α : Type*}
    (x : Fin k → osiiAxisPairIndex d → α)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiAxisPairMultiGapFlatten x
        (osiiAxisPairMultiGapFlattenIndex q) =
      x q.1 q.2 := by
  rcases q with ⟨i, a, b⟩
  simp [osiiAxisPairMultiGapFlatten,
    osiiAxisPairMultiGapFlattenIndex]

/-- Fixed directional coefficient in the cosh bound for the translation
majorant. -/
def osiiAxisPairChronologicalTranslationMajorantConstant
    (T : ℝ) :
    ℝ :=
  ∑ _i : Fin k, ∑ a : osiiAxisPairIndex d,
    ‖osiiAxisPairDir (d := d) T a‖

theorem osiiAxisPairChronologicalTranslationMajorantConstant_nonneg
    (T : ℝ) :
    0 ≤
      osiiAxisPairChronologicalTranslationMajorantConstant
        (d := d) (k := k) T := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun a _ => norm_nonneg _

/-- The translation majorant has one common cosh-gauge exponential bound. -/
theorem osiiAxisPairChronologicalTranslationMajorant_le_cosh
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairChronologicalTranslationMajorant T x ≤
      osiiAxisPairChronologicalTranslationMajorantConstant
          (d := d) (k := k) T *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten x)) := by
  let E : ℝ :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten x))
  have hcoef :
      ∀ i : Fin k, ∀ a : osiiAxisPairIndex d,
        Real.exp (x i a) ≤ E := by
    intro i a
    simpa [E] using
      (SCV.exp_coord_le_exp_four_mul_logCoshGauge
        (osiiAxisPairMultiGapFlatten x)
        (osiiAxisPairMultiGapFlattenIndex (i, a)))
  calc
    osiiAxisPairChronologicalTranslationMajorant T x
        ≤ ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            E * ‖osiiAxisPairDir (d := d) T a‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right
        (hcoef i a) (norm_nonneg _)
    _ =
        osiiAxisPairChronologicalTranslationMajorantConstant
            (d := d) (k := k) T * E := by
      dsimp [osiiAxisPairChronologicalTranslationMajorantConstant]
      simp_rw [mul_comm E]
      calc
        (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            ‖osiiAxisPairDir (d := d) T a‖ * E) =
            ∑ i : Fin k,
              (∑ a : osiiAxisPairIndex d,
                ‖osiiAxisPairDir (d := d) T a‖) * E := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
        _ =
            (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
              ‖osiiAxisPairDir (d := d) T a‖) * E := by
          conv_rhs => rw [Finset.sum_mul]
    _ =
        osiiAxisPairChronologicalTranslationMajorantConstant
            (d := d) (k := k) T *
          Real.exp
            (4 *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten x)) := by
      rfl

/-- Fixed affine center vector used by one packet split and frame. -/
def OSIIChronologicalCompactFactors.packetCenterOffsetVector
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    SpacetimeDim d :=
  (F.axisPairCenterOffset T hordered q.1 q.2 /
      osiiAxisPairRadius T) •
    osiiAxisPairDir (d := d) T q.2

/-- A common rotated-time support bound controls the fixed affine part of the
actual packet center. -/
theorem
    OSIIChronologicalCompactFactors.norm_packetCenterOffsetVector_le_of_factor_bound
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k)
    (B : ℝ) (hB : 0 ≤ B)
    (hfactor_bound :
      ∀ i : Fin (k + 1), ∀ y ∈ tsupport
          ((F.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        |((osiiAxisPairRotationData T q.2).matrix.mulVec y) 0| ≤ B) :
    ‖F.packetCenterOffsetVector T hordered q‖ ≤ 2 * B + 1 := by
  let r := osiiAxisPairRadius T
  have hr : 0 < r := osiiAxisPairRadius_pos T
  have hdir :
      ‖osiiAxisPairDir (d := d) T q.2‖ ≤ r := by
    exact norm_osiiAxisPairDir_le_radius T q.2
  have hoff :=
    F.abs_axisPairCenterOffset_le_of_factor_bound
      T hordered q.1 q.2 B hB hfactor_bound
  rw [OSIIChronologicalCompactFactors.packetCenterOffsetVector, norm_smul,
    Real.norm_eq_abs, abs_div, abs_of_pos hr]
  calc
    |F.axisPairCenterOffset T hordered q.1 q.2| / r *
          ‖osiiAxisPairDir (d := d) T q.2‖
        ≤
      |F.axisPairCenterOffset T hordered q.1 q.2| / r * r := by
        exact mul_le_mul_of_nonneg_left hdir
          (div_nonneg (abs_nonneg _) hr.le)
    _ = |F.axisPairCenterOffset T hordered q.1 q.2| := by
      exact div_mul_cancel₀ _ (ne_of_gt hr)
    _ ≤ 2 * B + 1 := hoff

theorem OSIIChronologicalCompactFactors.packetCenter_eq
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetCenter T hordered x q =
      -osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1 (Fin.succ q.1) +
        F.packetCenterOffsetVector T hordered q :=
  rfl

theorem OSIIChronologicalCompactFactors.norm_packetCenter_le_majorant
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    ‖F.packetCenter T hordered x q‖ ≤
      osiiAxisPairChronologicalTranslationMajorant T x +
        ‖F.packetCenterOffsetVector T hordered q‖ := by
  rw [F.packetCenter_eq]
  calc
    ‖-osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1 (Fin.succ q.1) +
        F.packetCenterOffsetVector T hordered q‖
        ≤
      ‖-osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1 (Fin.succ q.1)‖ +
        ‖F.packetCenterOffsetVector T hordered q‖ :=
      norm_add_le _ _
    _ =
      ‖osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1 (Fin.succ q.1)‖ +
        ‖F.packetCenterOffsetVector T hordered q‖ := by
      rw [norm_neg]
    _ ≤
      osiiAxisPairChronologicalTranslationMajorant T x +
        ‖F.packetCenterOffsetVector T hordered q‖ := by
      gcongr
      exact
        norm_osiiAxisPairChronologicalPointTranslationWithoutGap_le_majorant
          T x q.1 (Fin.succ q.1)

theorem OSIIChronologicalCompactFactors.norm_packetLeftConfiguration_le_majorant
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    ‖F.packetLeftConfiguration T hordered x q‖ ≤
      2 * osiiAxisPairChronologicalTranslationMajorant T x +
        ‖F.packetCenterOffsetVector T hordered q‖ := by
  refine
    (pi_norm_le_iff_of_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (osiiAxisPairChronologicalTranslationMajorant_nonneg T x))
        (norm_nonneg _))).2 ?_
  intro j
  dsimp [OSIIChronologicalCompactFactors.packetLeftConfiguration]
  calc
    ‖-F.packetCenter T hordered x q -
        osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1
          (osiiChronologicalGapSplitEquiv q.1
            (Sum.inl (Fin.rev j)))‖
        ≤ ‖F.packetCenter T hordered x q‖ +
          ‖osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1
              (Sum.inl (Fin.rev j)))‖ := by
      simpa [norm_neg] using
        norm_sub_le
          (-F.packetCenter T hordered x q)
          (osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1
              (Sum.inl (Fin.rev j))))
    _ ≤
        (osiiAxisPairChronologicalTranslationMajorant T x +
          ‖F.packetCenterOffsetVector T hordered q‖) +
        osiiAxisPairChronologicalTranslationMajorant T x := by
      gcongr
      · exact F.norm_packetCenter_le_majorant
          T hordered x q
      · exact
          norm_osiiAxisPairChronologicalPointTranslationWithoutGap_le_majorant
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1
              (Sum.inl (Fin.rev j)))
    _ =
        2 * osiiAxisPairChronologicalTranslationMajorant T x +
          ‖F.packetCenterOffsetVector T hordered q‖ := by
      ring

theorem OSIIChronologicalCompactFactors.norm_packetRightConfiguration_le_majorant
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    ‖F.packetRightConfiguration T hordered x q‖ ≤
      2 * osiiAxisPairChronologicalTranslationMajorant T x +
        ‖F.packetCenterOffsetVector T hordered q‖ := by
  refine
    (pi_norm_le_iff_of_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (osiiAxisPairChronologicalTranslationMajorant_nonneg T x))
        (norm_nonneg _))).2 ?_
  intro j
  dsimp [OSIIChronologicalCompactFactors.packetRightConfiguration]
  calc
    ‖-F.packetCenter T hordered x q -
        osiiAxisPairChronologicalPointTranslationWithoutGap
          T x q.1
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j))‖
        ≤ ‖F.packetCenter T hordered x q‖ +
          ‖osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j))‖ := by
      simpa [norm_neg] using
        norm_sub_le
          (-F.packetCenter T hordered x q)
          (osiiAxisPairChronologicalPointTranslationWithoutGap
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))
    _ ≤
        (osiiAxisPairChronologicalTranslationMajorant T x +
          ‖F.packetCenterOffsetVector T hordered q‖) +
        osiiAxisPairChronologicalTranslationMajorant T x := by
      gcongr
      · exact F.norm_packetCenter_le_majorant
          T hordered x q
      · exact
          norm_osiiAxisPairChronologicalPointTranslationWithoutGap_le_majorant
            T x q.1
            (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j))
    _ =
        2 * osiiAxisPairChronologicalTranslationMajorant T x +
          ‖F.packetCenterOffsetVector T hordered q‖ := by
      ring

/-- Positive affine coefficient controlling the moving left and unfrozen
right configuration tuples. -/
def OSIIChronologicalCompactFactors.packetConfigurationCoshConstant
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ℝ :=
  1 +
    2 *
      osiiAxisPairChronologicalTranslationMajorantConstant
        (d := d) (k := k) T +
    ‖F.packetCenterOffsetVector T hordered q‖

theorem OSIIChronologicalCompactFactors.packetConfigurationCoshConstant_pos
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    0 < F.packetConfigurationCoshConstant T hordered q := by
  dsimp [OSIIChronologicalCompactFactors.packetConfigurationCoshConstant]
  nlinarith
    [osiiAxisPairChronologicalTranslationMajorantConstant_nonneg
      (d := d) (k := k) T,
     norm_nonneg (F.packetCenterOffsetVector T hordered q)]

private theorem one_le_packetGaugeExp
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    1 ≤
      Real.exp
        (4 *
          SCV.logCoshGauge
            (osiiAxisPairMultiGapFlatten x)) := by
  exact Real.one_le_exp
    (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun i _ =>
        (Real.cosh_pos _).le))

theorem OSIIChronologicalCompactFactors.one_add_norm_packetLeftConfiguration_le_cosh
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    1 + ‖F.packetLeftConfiguration T hordered x q‖ ≤
      F.packetConfigurationCoshConstant T hordered q *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten x)) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K :=
    osiiAxisPairChronologicalTranslationMajorantConstant
      (d := d) (k := k) T
  let B := ‖F.packetCenterOffsetVector T hordered q‖
  let E :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten x))
  have hconfig :
      ‖F.packetLeftConfiguration T hordered x q‖ ≤
        2 * M + B := by
    simpa [M, B] using
      F.norm_packetLeftConfiguration_le_majorant
        T hordered x q
  have hM : M ≤ K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_cosh
        (d := d) (k := k) T x
  have hK : 0 ≤ K := by
    exact
      osiiAxisPairChronologicalTranslationMajorantConstant_nonneg
        (d := d) (k := k) T
  have hB : 0 ≤ B := norm_nonneg _
  have hE : 1 ≤ E := by
    simpa [E] using one_le_packetGaugeExp (d := d) (k := k) x
  dsimp
    [OSIIChronologicalCompactFactors.packetConfigurationCoshConstant]
  change 1 + ‖F.packetLeftConfiguration T hordered x q‖ ≤
    (1 + 2 * K + B) * E
  nlinarith

theorem OSIIChronologicalCompactFactors.one_add_norm_packetRightConfiguration_le_cosh
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    1 + ‖F.packetRightConfiguration T hordered x q‖ ≤
      F.packetConfigurationCoshConstant T hordered q *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten x)) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K :=
    osiiAxisPairChronologicalTranslationMajorantConstant
      (d := d) (k := k) T
  let B := ‖F.packetCenterOffsetVector T hordered q‖
  let E :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten x))
  have hconfig :
      ‖F.packetRightConfiguration T hordered x q‖ ≤
        2 * M + B := by
    simpa [M, B] using
      F.norm_packetRightConfiguration_le_majorant
        T hordered x q
  have hM : M ≤ K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_cosh
        (d := d) (k := k) T x
  have hK : 0 ≤ K := by
    exact
      osiiAxisPairChronologicalTranslationMajorantConstant_nonneg
        (d := d) (k := k) T
  have hB : 0 ≤ B := norm_nonneg _
  have hE : 1 ≤ E := by
    simpa [E] using one_le_packetGaugeExp (d := d) (k := k) x
  dsimp
    [OSIIChronologicalCompactFactors.packetConfigurationCoshConstant]
  change 1 + ‖F.packetRightConfiguration T hordered x q‖ ≤
    (1 + 2 * K + B) * E
  nlinarith

/-- Real logarithmic base naturally associated to a one-coordinate complex
chart.  The selected coordinate is replaced by the real part of the chart
parameter; all frozen coordinates retain their original real values. -/
def osiiAxisPairMultiGapChartRealPart
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : ℂ) :
    Fin k → osiiAxisPairIndex d → ℝ :=
  fun i a =>
    ((osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w) i a).re

theorem osiiAxisPairMultiGapChartRealPart_eq_of_ne
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q p : osiiAxisPairMultiGapIndex d k)
    (w : ℂ)
    (hpq : p ≠ q) :
    osiiAxisPairMultiGapChartRealPart x q w p.1 p.2 =
      x p.1 p.2 := by
  by_cases hi : p.1 = q.1
  · have ha : p.2 ≠ q.2 := by
      intro ha
      exact hpq (Prod.ext hi ha)
    rw [hi]
    simp [osiiAxisPairMultiGapChartRealPart,
      osiiAxisPairMultiGapUpdate, ha,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed]
  · simp [osiiAxisPairMultiGapChartRealPart,
      osiiAxisPairMultiGapUpdate, hi,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed]

/-- Re-inserting a real selected coordinate leaves the nested logarithmic real
embedding unchanged. -/
theorem osiiAxisPairMultiGapUpdate_realEmbed_selected
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiAxisPairMultiGapUpdate
        (osiiAxisPairSimultaneousLogRealEmbed x) q
        (x q.1 q.2 : ℂ) =
      osiiAxisPairSimultaneousLogRealEmbed x := by
  funext i a
  by_cases hi : i = q.1
  · subst i
    by_cases ha : a = q.2
    · subst a
      simp [osiiAxisPairMultiGapUpdate,
        osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed]
    · simp [osiiAxisPairMultiGapUpdate, ha,
        osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed]
  · simp [osiiAxisPairMultiGapUpdate, hi,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed]

/-- The chart real part also returns the original real base when its selected
coordinate is re-inserted. -/
theorem osiiAxisPairMultiGapChartRealPart_selected_real
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiAxisPairMultiGapChartRealPart x q (x q.1 q.2 : ℂ) = x := by
  funext i a
  change
    ((osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q
      (x q.1 q.2 : ℂ)) i a).re = x i a
  rw [osiiAxisPairMultiGapUpdate_realEmbed_selected x q]
  simp [osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed]

/-- Flattening the nested chart real part gives the real part of the ordinary
flattened one-coordinate update. -/
theorem osiiAxisPairMultiGapFlatten_chartRealPart_unflatten
    (x : osiiAxisPairIndex (k * d) → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : ℂ) :
    osiiAxisPairMultiGapFlatten
        (osiiAxisPairMultiGapChartRealPart
          (osiiAxisPairMultiGapUnflatten x) q w) =
      fun b =>
        (Function.update
          (fun c => (x c : ℂ))
          (osiiAxisPairMultiGapFlattenIndex q) w b).re := by
  have hbase :
      osiiAxisPairMultiGapFlatten
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiAxisPairMultiGapUnflatten x)) =
        fun b => (x b : ℂ) := by
    rw [osiiAxisPairMultiGapFlatten_realEmbed]
    rw [osiiAxisPairMultiGapFlatten_unflatten]
    rfl
  have hunflatten :
      osiiAxisPairMultiGapUnflatten
          (Function.update
            (fun c => (x c : ℂ))
            (osiiAxisPairMultiGapFlattenIndex q) w) =
        osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiAxisPairMultiGapUnflatten x)) q w := by
    rw [← hbase]
    exact
      osiiAxisPairMultiGapUnflatten_update_flatten
        (osiiAxisPairSimultaneousLogRealEmbed
          (osiiAxisPairMultiGapUnflatten x)) q w
  funext b
  let p := osiiAxisPairMultiGapUnflattenIndex b
  have hp :=
    congrArg (fun z => (z p.1 p.2).re) hunflatten
  change
    ((osiiAxisPairMultiGapUnflatten
      (Function.update
        (fun c => (x c : ℂ))
        (osiiAxisPairMultiGapFlattenIndex q) w)) p.1 p.2).re =
      ((osiiAxisPairMultiGapUpdate
        (osiiAxisPairSimultaneousLogRealEmbed
          (osiiAxisPairMultiGapUnflatten x)) q w) p.1 p.2).re at hp
  change
    ((osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed
        (osiiAxisPairMultiGapUnflatten x)) q w) p.1 p.2).re =
      (Function.update
        (fun c => (x c : ℂ))
        (osiiAxisPairMultiGapFlattenIndex q) w b).re
  rw [← hp]
  change
    (Function.update
      (fun c => (x c : ℂ))
      (osiiAxisPairMultiGapFlattenIndex q) w
      (osiiAxisPairMultiGapFlattenIndex p)).re =
        (Function.update
          (fun c => (x c : ℂ))
          (osiiAxisPairMultiGapFlattenIndex q) w b).re
  rw [show osiiAxisPairMultiGapFlattenIndex p = b by simp [p]]

end OSReconstruction
