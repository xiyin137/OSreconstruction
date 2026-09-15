/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.ForwardTubeDomain

noncomputable section

open Complex Topology

variable {d n : ℕ} [NeZero d]

/-- Complexified Wick map on configuration space: multiply the time component by `I`
and leave the spatial components unchanged. On real configurations this is the usual
Euclidean Wick rotation. -/
def wickRotateComplexPoint
    (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * z 0 else z μ

def wickRotateComplexConfig
    (z : Fin n → Fin (d + 1) → ℂ) : Fin n → Fin (d + 1) → ℂ :=
  fun k => wickRotateComplexPoint (z k)

/-- Inverse complexified Wick map on configuration space. -/
def wickUnrotateComplexConfig
    (z : Fin n → Fin (d + 1) → ℂ) : Fin n → Fin (d + 1) → ℂ :=
  fun k μ => if μ = 0 then (-Complex.I) * z k 0 else z k μ

@[simp] theorem wickRotateComplexConfig_realToComplexProduct
    (x : Fin n → Fin (d + 1) → ℝ) :
    wickRotateComplexConfig (SCV.realToComplexProduct x) = fun k => wickRotatePoint (x k) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [wickRotateComplexConfig, wickRotateComplexPoint, SCV.realToComplexProduct, wickRotatePoint]
  · rw [wickRotateComplexConfig, wickRotateComplexPoint, SCV.realToComplexProduct, wickRotatePoint]
    rfl

@[simp] theorem wickRotateComplexConfig_wickUnrotateComplexConfig
    (z : Fin n → Fin (d + 1) → ℂ) :
    wickRotateComplexConfig (wickUnrotateComplexConfig z) = z := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [wickRotateComplexConfig, wickRotateComplexPoint, wickUnrotateComplexConfig]
    calc
      Complex.I * (-Complex.I * z k 0) = (Complex.I * -Complex.I) * z k 0 := by ring
      _ = z k 0 := by simp
  · simp [wickRotateComplexConfig, wickRotateComplexPoint, wickUnrotateComplexConfig, hμ]

@[simp] theorem wickUnrotateComplexConfig_wickRotateComplexConfig
    (z : Fin n → Fin (d + 1) → ℂ) :
    wickUnrotateComplexConfig (wickRotateComplexConfig z) = z := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [wickUnrotateComplexConfig, wickRotateComplexConfig, wickRotateComplexPoint]
    calc
      (-Complex.I) * (Complex.I * z k 0) = ((-Complex.I) * Complex.I) * z k 0 := by ring
      _ = z k 0 := by simp
  · simp [wickRotateComplexConfig, wickRotateComplexPoint, wickUnrotateComplexConfig, hμ]

private theorem continuous_wickRotateComplexPoint :
    Continuous (wickRotateComplexPoint (d := d)) := by
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    change Continuous (fun z : Fin (d + 1) → ℂ => Complex.I * z 0)
    exact continuous_const.mul (continuous_apply 0)
  · simpa [wickRotateComplexPoint, hμ] using
      (continuous_apply μ)

private theorem differentiable_wickRotateComplexPoint :
    Differentiable ℂ (wickRotateComplexPoint (d := d)) := by
  apply differentiable_pi.mpr
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord : Differentiable ℂ (fun z : Fin (d + 1) → ℂ => z 0) := differentiable_apply 0
    simpa [wickRotateComplexPoint] using hcoord.const_mul Complex.I
  · have hcoord : Differentiable ℂ (fun z : Fin (d + 1) → ℂ => z μ) := differentiable_apply μ
    simpa [wickRotateComplexPoint, hμ] using hcoord

private theorem continuous_wickRotateComplexConfig :
    Continuous (wickRotateComplexConfig (n := n) (d := d)) := by
  apply continuous_pi
  intro k
  exact continuous_wickRotateComplexPoint.comp (continuous_apply k)

private theorem differentiable_wickRotateComplexConfig :
    Differentiable ℂ (wickRotateComplexConfig (n := n) (d := d)) := by
  apply differentiable_pi.mpr
  intro k
  exact differentiable_wickRotateComplexPoint.comp (differentiable_apply k)

private theorem continuous_wickUnrotateComplexConfig :
    Continuous (wickUnrotateComplexConfig (n := n) (d := d)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord : Continuous (fun z : Fin n → Fin (d + 1) → ℂ => z k 0) :=
      (continuous_apply 0).comp (continuous_apply k)
    have hmul : Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
        (-Complex.I) * z k 0) :=
      continuous_const.mul hcoord
    simpa [wickUnrotateComplexConfig, neg_mul] using hmul
  · simp only [wickUnrotateComplexConfig, hμ, if_false]
    fun_prop

private theorem continuous_wickRotateRealConfig :
    Continuous (fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord : Continuous (fun x : NPointDomain d n => x k 0) :=
      (continuous_apply 0).comp (continuous_apply k)
    change Continuous (fun x : NPointDomain d n => Complex.I * (x k 0 : ℂ))
    exact continuous_const.mul (Complex.continuous_ofReal.comp hcoord)
  · simp only [wickRotatePoint, hμ, if_false]
    fun_prop

@[simp] theorem wickRotatePoint_add
    (x a : Fin (d + 1) → ℝ) :
    wickRotatePoint (fun μ => x μ + a μ) =
      fun μ => wickRotatePoint x μ + wickRotatePoint a μ := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [wickRotatePoint]
    ring
  · simp [wickRotatePoint, hμ]

@[simp] theorem wickRotatePoint_timeReflection_eq_lorentzTimeReversal
    (x : Fin (d + 1) → ℝ) :
    wickRotatePoint (timeReflection d x) =
      fun μ => ∑ ν, (↑((LorentzGroup.timeReversal (d := d)).val μ ν) : ℂ) * wickRotatePoint x ν := by
  ext μ
  have hsum :
      (∑ ν, (↑((LorentzGroup.timeReversal (d := d)).val μ ν) : ℂ) * wickRotatePoint x ν) =
        if μ = 0 then -wickRotatePoint x 0 else wickRotatePoint x μ := by
    by_cases hμ : μ = 0
    · subst hμ
      rw [Finset.sum_eq_single 0]
      · simp [LorentzGroup.timeReversal, FullLorentzGroup.timeReversal]
      · intro ν hν
        intro hν0
        have hentry :
            ((LorentzGroup.timeReversal (d := d)).val 0 ν) = 0 := by
          change Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) 0 ν = 0
          by_cases h0ν : 0 = ν
          · exact False.elim (hν0 h0ν.symm)
          · simp [Matrix.diagonal, h0ν]
        simp [hentry]
      · simp [LorentzGroup.timeReversal, FullLorentzGroup.timeReversal]
    · rw [Finset.sum_eq_single μ]
      · simp [LorentzGroup.timeReversal, FullLorentzGroup.timeReversal, hμ]
      · intro ν hν
        intro hνμ
        have hentry :
            ((LorentzGroup.timeReversal (d := d)).val μ ν) = 0 := by
          change Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) μ ν = 0
          by_cases hμν' : μ = ν
          · exact False.elim (hνμ hμν'.symm)
          · simp [Matrix.diagonal, hμν']
        simp [hentry]
      · simp [LorentzGroup.timeReversal, hμ]
  calc
    wickRotatePoint (timeReflection d x) μ
        = starRingEnd ℂ (wickRotatePoint x μ) :=
          wickRotatePoint_timeReflection (d := d) (x := x) μ
    _ = if μ = 0 then -wickRotatePoint x 0 else wickRotatePoint x μ := by
          by_cases hμ : μ = 0 <;> simp [wickRotatePoint, hμ]
    _ = ∑ ν, (↑((LorentzGroup.timeReversal (d := d)).val μ ν) : ℂ) * wickRotatePoint x ν := by
          simpa using hsum.symm

private theorem wickRotateComplexConfig_real_smul
    (a b : ℝ) (z w : Fin n → Fin (d + 1) → ℂ) :
    wickRotateComplexConfig (a • z + b • w) =
      a • wickRotateComplexConfig z + b • wickRotateComplexConfig w := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [wickRotateComplexConfig, wickRotateComplexPoint, Pi.add_apply, Pi.smul_apply]
    ring
  · simp [wickRotateComplexConfig, wickRotateComplexPoint, hμ, Pi.add_apply, Pi.smul_apply]

private theorem euclidean_forwardTube_section_nonempty :
    ({x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}).Nonempty := by
  let x0 : NPointDomain d n :=
    fun k μ => if μ = 0 then (k : ℝ) + 1 else 0
  refine ⟨x0, ?_⟩
  apply euclidean_ordered_in_forwardTube (d := d) (n := n) x0
  · intro i j hij
    simp [x0, hij]
  · intro i
    have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    simpa [x0] using this

omit [NeZero d] in
/-- Each coincident-time hyperplane is Haar-null. -/
theorem measure_timeCoord_eq_zero (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.volume {x : NPointDomain d n | x i 0 = x j 0} = 0 := by
  let L : NPointDomain d n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i 0 - x j 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp
        ring }
  have hset :
      {x : NPointDomain d n | x i 0 = x j 0} =
        (LinearMap.ker L : Set (NPointDomain d n)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have hji : j ≠ i := by
      intro h
      exact hij h.symm
    have : (1 : ℝ) = 0 := by
      simp [L, hji] at hval
    norm_num at this
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L) hker_ne_top

omit [NeZero d] in
/-- Almost every configuration has pairwise distinct Euclidean time coordinates. -/
theorem ae_pairwise_distinct_timeCoords :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0 := by
  have hall : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, x p.1.1 0 ≠ x p.1.2 0 := by
    have hall' : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
        ∀ p ∈ (Set.univ : Set {p : Fin n × Fin n // p.1 ≠ p.2}),
          x p.1.1 0 ≠ x p.1.2 0 := by
      refine
      ((Set.toFinite (Set.univ : Set {p : Fin n × Fin n // p.1 ≠ p.2})).eventually_all
        (l := MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
        (p := fun p => fun x : NPointDomain d n => x p.1.1 0 ≠ x p.1.2 0)).2 ?_
      intro p _
      let s : Set (NPointDomain d n) := {x | x p.1.1 0 = x p.1.2 0}
      have hs0 : MeasureTheory.volume s = 0 := by
        simpa [s] using measure_timeCoord_eq_zero (d := d) (n := n) p.1.1 p.1.2 p.2
      have hsae :
          sᶜ ∈ MeasureTheory.ae
            (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
        MeasureTheory.compl_mem_ae_iff.mpr hs0
      change sᶜ ∈ MeasureTheory.ae
        (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n))
      exact hsae
    simpa only [Set.mem_univ, forall_const] using hall'
  filter_upwards [hall] with x hx i j hij
  exact hx ⟨⟨i, j⟩, hij⟩

/-- On the Wick-rotated real section of the forward tube, Euclidean times are
strictly increasing. -/
private theorem strictMono_time_of_wickRotate_mem_forwardTube
    {m : ℕ} {x : NPointDomain d (m + 1)}
    (hx : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d (m + 1)) :
    StrictMono (fun k : Fin (m + 1) => x k 0) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro k
  have hk := (hx k.succ).1
  norm_num [wickRotatePoint, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Fin.succ_ne_zero] at hk
  have hindex : (⟨k.val, by omega⟩ : Fin (m + 1)) = k.castSucc := by
    apply Fin.ext
    rfl
  rw [← hindex]
  linarith

/-- Real configurations whose Wick rotation lies in the forward tube have
strictly positive, strictly increasing Euclidean times. -/
theorem mem_orderedPositiveTimeRegion_of_wickRotate_mem_forwardTube
    {x : NPointDomain d n}
    (hx : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n) :
    x ∈ OrderedPositiveTimeRegion d n := by
  intro i
  constructor
  · cases n with
    | zero =>
        exact Fin.elim0 i
    | succ m =>
        have hmono :
            StrictMono (fun k : Fin (m + 1) => x k 0) :=
          strictMono_time_of_wickRotate_mem_forwardTube (d := d) hx
        have h0 : 0 < x 0 0 := by
          simpa [wickRotatePoint, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] using (hx 0).1
        exact lt_of_lt_of_le h0 (hmono.monotone (Fin.zero_le i))
  · intro j hij
    cases n with
    | zero =>
        exact Fin.elim0 i
    | succ m =>
        exact strictMono_time_of_wickRotate_mem_forwardTube (d := d) hx hij

/-- Compactly supported Schwartz tests supported on the Wick-rotated real
section inside the forward tube are automatically zero-diagonal. -/
theorem VanishesToInfiniteOrderOnCoincidence_of_tsupport_subset_wickForwardTubeSection
    (f : SchwartzNPoint d n)
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆
      {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}) :
    VanishesToInfiniteOrderOnCoincidence f := by
  apply VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
  intro x hx
  exact mem_orderedPositiveTimeRegion_of_wickRotate_mem_forwardTube (hsupp hx)

/-- On the Wick-rotated real section inside the forward tube, the classical
promotion into `ZeroDiagonalSchwartz` is the intended branch. -/
theorem ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
    (f : SchwartzNPoint d n)
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆
      {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}) :
    (ZeroDiagonalSchwartz.ofClassical f).1 = f := by
  exact ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes f
    (VanishesToInfiniteOrderOnCoincidence_of_tsupport_subset_wickForwardTubeSection
      (d := d) f hsupp)

/-- If two holomorphic functions on the forward tube agree on all Wick-rotated real
configurations whose Wick image lies in the forward tube, then they agree everywhere on
the forward tube. -/
theorem forwardTube_eq_of_eq_on_wickRealSection
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hG : DifferentiableOn ℂ G (ForwardTube d n))
    (hFG_euclid :
      ∀ x : NPointDomain d n,
        (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n →
          F (fun k => wickRotatePoint (x k)) = G (fun k => wickRotatePoint (x k))) :
    ∀ z ∈ ForwardTube d n, F z = G z := by
  let U : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | wickRotateComplexConfig z ∈ ForwardTube d n}
  have hU_open : IsOpen U := by
    have hFT_open : IsOpen (ForwardTube d n) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using
        (BHW.isOpen_forwardTube (d := d) (n := n))
    change IsOpen (wickRotateComplexConfig ⁻¹' ForwardTube d n)
    exact hFT_open.preimage (continuous_wickRotateComplexConfig (d := d) (n := n))
  have hU_convex : Convex ℝ U := by
    intro z hz w hw a b ha hb hab
    change wickRotateComplexConfig z ∈ ForwardTube d n at hz
    change wickRotateComplexConfig w ∈ ForwardTube d n at hw
    have hzFT : wickRotateComplexConfig z ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz
    have hwFT : wickRotateComplexConfig w ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hw
    have hconv :
        a • wickRotateComplexConfig z + b • wickRotateComplexConfig w ∈ ForwardTube d n := by
      have hconv' := BHW.forwardTube_convex hzFT hwFT ha hb hab
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hconv'
    simpa [U, wickRotateComplexConfig_real_smul (d := d) (n := n) a b z w] using hconv
  have hU_conn : IsConnected U := hU_convex.isConnected <| by
    obtain ⟨x0, hx0⟩ := euclidean_forwardTube_section_nonempty (d := d) (n := n)
    refine ⟨SCV.realToComplexProduct x0, ?_⟩
    simpa [U, wickRotateComplexConfig_realToComplexProduct] using hx0
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    F (wickRotateComplexConfig z) - G (wickRotateComplexConfig z)
  have hH_holo : DifferentiableOn ℂ H U := by
    intro z hz
    have hcompF :
        DifferentiableWithinAt ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => F (wickRotateComplexConfig z)) U z :=
      (hF _ hz).comp z differentiable_wickRotateComplexConfig.differentiableAt.differentiableWithinAt
        (by
          intro y hy
          exact hy)
    have hcompG :
        DifferentiableWithinAt ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => G (wickRotateComplexConfig z)) U z :=
      (hG _ hz).comp z differentiable_wickRotateComplexConfig.differentiableAt.differentiableWithinAt
        (by
          intro y hy
          exact hy)
    exact hcompF.sub hcompG
  let V : Set (NPointDomain d n) := {x | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}
  have hV_open : IsOpen V := by
    have hFT_open : IsOpen (ForwardTube d n) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using
        (BHW.isOpen_forwardTube (d := d) (n := n))
    change IsOpen ((fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) ⁻¹'
      ForwardTube d n)
    exact hFT_open.preimage (continuous_wickRotateRealConfig (d := d) (n := n))
  have hV_ne : V.Nonempty := euclidean_forwardTube_section_nonempty (d := d) (n := n)
  have hV_sub :
      ∀ x ∈ V, SCV.realToComplexProduct x ∈ U := by
    intro x hx
    simpa [U, V, wickRotateComplexConfig_realToComplexProduct] using hx
  have hH_zero :
      ∀ x ∈ V, H (SCV.realToComplexProduct x) = 0 := by
    intro x hx
    simp [H, wickRotateComplexConfig_realToComplexProduct, hFG_euclid x hx]
  have hzero_on_U :=
    SCV.identity_theorem_totally_real_product
      (hD_open := hU_open) (hD_conn := hU_conn) (f := H) hH_holo
      (V := V) hV_open hV_ne hV_sub hH_zero
  intro z hz
  have hw : wickUnrotateComplexConfig z ∈ U := by
    simpa [U, wickRotateComplexConfig_wickUnrotateComplexConfig] using hz
  have hHzero : H (wickUnrotateComplexConfig z) = 0 := hzero_on_U _ hw
  have : F z - G z = 0 := by
    simpa [H, wickRotateComplexConfig_wickUnrotateComplexConfig] using hHzero
  exact sub_eq_zero.mp this

/-- If two holomorphic functions agree on the Wick-rotated real section inside
an open connected domain, then they agree on the whole domain.

This is the subdomain form of `forwardTube_eq_of_eq_on_wickRealSection`, used
on the intersection domain where both `z` and a transformed point stay inside
the forward tube. -/
theorem eqOn_openConnected_of_eqOn_wickRealSection
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_wick_nonempty :
      ∃ x : NPointDomain d n, (fun k => wickRotatePoint (x k)) ∈ U)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U)
    (hFG_euclid :
      ∀ x : NPointDomain d n,
        (fun k => wickRotatePoint (x k)) ∈ U →
          F (fun k => wickRotatePoint (x k)) = G (fun k => wickRotatePoint (x k))) :
    Set.EqOn F G U := by
  let U' : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | wickRotateComplexConfig z ∈ U}
  have hU'_open : IsOpen U' := by
    change IsOpen (wickRotateComplexConfig ⁻¹' U)
    exact hU_open.preimage continuous_wickRotateComplexConfig
  have himage :
      wickUnrotateComplexConfig '' U = U' := by
    ext z
    constructor
    · rintro ⟨w, hwU, rfl⟩
      simpa [U', wickRotateComplexConfig_wickUnrotateComplexConfig] using hwU
    · intro hz
      refine ⟨wickRotateComplexConfig z, ?_, ?_⟩
      · simpa [U'] using hz
      · simpa [wickUnrotateComplexConfig_wickRotateComplexConfig]
  have hU'_conn : IsConnected U' := by
    rw [← himage]
    exact hU_conn.image
      (wickUnrotateComplexConfig (n := n) (d := d))
      continuous_wickUnrotateComplexConfig.continuousOn
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    F (wickRotateComplexConfig z) - G (wickRotateComplexConfig z)
  have hH_holo : DifferentiableOn ℂ H U' := by
    intro z hz
    have hwick_diff :
        DifferentiableWithinAt ℂ
          (wickRotateComplexConfig (n := n) (d := d)) U' z := by
      have htmp : DifferentiableAt ℂ (wickRotateComplexConfig (n := n) (d := d)) z :=
        (differentiable_wickRotateComplexConfig (d := d) (n := n)).differentiableAt
      exact htmp.differentiableWithinAt
    have hwick_maps :
        Set.MapsTo (wickRotateComplexConfig (n := n) (d := d)) U' U := by
      intro y hy
      simpa [U'] using hy
    have hcompF :
        DifferentiableWithinAt ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => F (wickRotateComplexConfig z)) U' z :=
      (hF _ (by simpa [U'] using hz)).comp z hwick_diff hwick_maps
    have hcompG :
        DifferentiableWithinAt ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => G (wickRotateComplexConfig z)) U' z :=
      (hG _ (by simpa [U'] using hz)).comp z hwick_diff hwick_maps
    exact hcompF.sub hcompG
  let V : Set (NPointDomain d n) := {x | (fun k => wickRotatePoint (x k)) ∈ U}
  have hV_open : IsOpen V := by
    change IsOpen ((fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) ⁻¹' U)
    exact hU_open.preimage (continuous_wickRotateRealConfig (d := d) (n := n))
  obtain ⟨x0, hx0⟩ := hU_wick_nonempty
  have hV_ne : V.Nonempty := ⟨x0, hx0⟩
  have hV_sub : ∀ x ∈ V, SCV.realToComplexProduct x ∈ U' := by
    intro x hx
    simpa [U', V, wickRotateComplexConfig_realToComplexProduct] using hx
  have hH_zero : ∀ x ∈ V, H (SCV.realToComplexProduct x) = 0 := by
    intro x hx
    simp [H, wickRotateComplexConfig_realToComplexProduct, hFG_euclid x hx]
  have hzero_on_U' :=
    SCV.identity_theorem_totally_real_product
      (hD_open := hU'_open) (hD_conn := hU'_conn) (f := H) hH_holo
      (V := V) hV_open hV_ne hV_sub hH_zero
  intro z hz
  have hw : wickUnrotateComplexConfig z ∈ U' := by
    simpa [U', wickRotateComplexConfig_wickUnrotateComplexConfig] using hz
  have hHzero : H (wickUnrotateComplexConfig z) = 0 := hzero_on_U' _ hw
  have : F z - G z = 0 := by
    simpa [H, wickRotateComplexConfig_wickUnrotateComplexConfig] using hHzero
  exact sub_eq_zero.mp this

/-- Distributional equality on compactly supported Wick-rotated Euclidean tests upgrades
to equality of the holomorphic witnesses on the full forward tube. -/
theorem forwardTube_eq_of_distributional_wickSection_eq
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hG : DifferentiableOn ℂ G (ForwardTube d n))
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n, F (fun k => wickRotatePoint (x k)) * φ x =
          ∫ x : NPointDomain d n, G (fun k => wickRotatePoint (x k)) * φ x) :
    ∀ z ∈ ForwardTube d n, F z = G z := by
  let V : Set (NPointDomain d n) := {x | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}
  have hFT_open : IsOpen (ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      (BHW.isOpen_forwardTube (d := d) (n := n))
  have hV_open : IsOpen V := by
    change IsOpen ((fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) ⁻¹'
      ForwardTube d n)
    exact hFT_open.preimage (continuous_wickRotateRealConfig (d := d) (n := n))
  have hF_cont : ContinuousOn F (ForwardTube d n) := by
    intro z hz
    exact (hF z hz).continuousWithinAt
  have hG_cont : ContinuousOn G (ForwardTube d n) := by
    intro z hz
    exact (hG z hz).continuousWithinAt
  have hg_cont : ContinuousOn (fun x : NPointDomain d n => F (fun k => wickRotatePoint (x k))) V := by
    refine hF_cont.comp (continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact hx
  have hh_cont : ContinuousOn (fun x : NPointDomain d n => G (fun k => wickRotatePoint (x k))) V := by
    refine hG_cont.comp (continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact hx
  have hEqOn :
      Set.EqOn
        (fun x : NPointDomain d n => F (fun k => wickRotatePoint (x k)))
        (fun x : NPointDomain d n => G (fun k => wickRotatePoint (x k)))
        V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hg_cont hh_cont ?_
    intro φ hφ_compact hφ_tsupport
    exact hint φ hφ_compact hφ_tsupport
  exact forwardTube_eq_of_eq_on_wickRealSection (d := d) (n := n) F G hF hG
    (fun x hx => hEqOn hx)

/-- Distributional Wick-section equality on an open connected Wick subdomain
upgrades to pointwise equality on that whole subdomain. -/
theorem eqOn_openConnected_of_distributional_wickSection_eq
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_wick_nonempty :
      ∃ x : NPointDomain d n, (fun k => wickRotatePoint (x k)) ∈ U)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U)
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ U} →
        ∫ x : NPointDomain d n, F (fun k => wickRotatePoint (x k)) * φ x =
          ∫ x : NPointDomain d n, G (fun k => wickRotatePoint (x k)) * φ x) :
    Set.EqOn F G U := by
  let V : Set (NPointDomain d n) := {x | (fun k => wickRotatePoint (x k)) ∈ U}
  have hV_open : IsOpen V := by
    change IsOpen ((fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) ⁻¹' U)
    exact hU_open.preimage (continuous_wickRotateRealConfig (d := d) (n := n))
  have hF_cont : ContinuousOn F U := by
    intro z hz
    exact (hF z hz).continuousWithinAt
  have hG_cont : ContinuousOn G U := by
    intro z hz
    exact (hG z hz).continuousWithinAt
  have hF_wick_cont :
      ContinuousOn (fun x : NPointDomain d n => F (fun k => wickRotatePoint (x k))) V := by
    refine hF_cont.comp (continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact hx
  have hG_wick_cont :
      ContinuousOn (fun x : NPointDomain d n => G (fun k => wickRotatePoint (x k))) V := by
    refine hG_cont.comp (continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    exact hx
  have hEqOn_wick :
      Set.EqOn
        (fun x : NPointDomain d n => F (fun k => wickRotatePoint (x k)))
        (fun x : NPointDomain d n => G (fun k => wickRotatePoint (x k)))
        V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hF_wick_cont hG_wick_cont ?_
    intro φ hφ_compact hφ_tsupport
    exact hint φ hφ_compact hφ_tsupport
  exact eqOn_openConnected_of_eqOn_wickRealSection
    (d := d) (n := n) U hU_open hU_conn hU_wick_nonempty F G hF hG
    (fun x hx => hEqOn_wick hx)

/-- Intersection-domain specialization of the subdomain Wick-section identity
theorem. This is the domain shape needed for the theorem-1 Lorentz lane: the
common region where both `z` and `Λ · z` stay in the forward tube. -/
theorem eqOn_d_lambda_of_distributional_wickSection_eq
    (Λ : ComplexLorentzGroup d)
    (hD_wick_nonempty :
      ∃ x : NPointDomain d n,
        (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
          BHW.complexLorentzAction Λ (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF :
      DifferentiableOn ℂ F
        {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n})
    (hG :
      DifferentiableOn ℂ G
        {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n})
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction Λ (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n, F (fun k => wickRotatePoint (x k)) * φ x =
          ∫ x : NPointDomain d n, G (fun k => wickRotatePoint (x k)) * φ x) :
    Set.EqOn F G
      {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n} := by
  have hD_conn :
      IsConnected {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n} := by
    rcases hD_wick_nonempty with ⟨x, hxFT, hxΛFT⟩
    refine ⟨⟨(fun k => wickRotatePoint (x k)), ⟨hxFT, hxΛFT⟩⟩, ?_⟩
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      (BHW.d_lambda_isPreconnected (d := d) (n := n) Λ)
  have hD_open :
      IsOpen {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n} := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      (BHW.isOpen_d_lambda (d := d) (n := n) Λ)
  exact eqOn_openConnected_of_distributional_wickSection_eq
    (d := d) (n := n)
    {z | z ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ z ∈ ForwardTube d n}
    hD_open hD_conn
    (by
      rcases hD_wick_nonempty with ⟨x, hxFT, hxΛFT⟩
      exact ⟨x, ⟨hxFT, hxΛFT⟩⟩)
    F G hF hG hint

/-- Distributional equality on compactly supported Wick-section tests may be
checked on the `ZeroDiagonalSchwartz` branch when the support stays inside the
forward-tube Wick section. -/
theorem forwardTube_eq_of_zeroDiagonal_distributional_wickSection_eq
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hG : DifferentiableOn ℂ G (ForwardTube d n))
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) =
          ∫ x : NPointDomain d n,
            G (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x)) :
    ∀ z ∈ ForwardTube d n, F z = G z := by
  refine forwardTube_eq_of_distributional_wickSection_eq (d := d) (n := n) F G hF hG ?_
  intro φ hφ_compact hφ_tsupport
  have hcoeff :
      (ZeroDiagonalSchwartz.ofClassical φ).1 = φ :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
      (d := d) (n := n) φ hφ_tsupport
  simpa [hcoeff] using hint φ hφ_compact hφ_tsupport

/-- To prove pointwise equality of two forward-tube holomorphic witnesses along a
positive imaginary ray, it suffices to prove equality of their compactly supported
Wick-section pairings on the zero-diagonal branch. -/
theorem forwardTube_point_eq_of_zeroDiagonal_distributional_wickSection_eq
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hG : DifferentiableOn ℂ G (ForwardTube d n))
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) =
          ∫ x : NPointDomain d n,
            G (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x))
    (x : NPointDomain d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : 0 < ε) :
    F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) =
      G (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs η).mp hη
  have hscaled_abs : ε • η ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n ε hε η hη_abs
  have hz :
      (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) ∈ ForwardTube d n := by
    rw [forwardTube_eq_imPreimage, Set.mem_setOf_eq]
    convert hscaled_abs using 1
    ext k μ
    simp [Pi.smul_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
  exact forwardTube_eq_of_zeroDiagonal_distributional_wickSection_eq
    (d := d) (n := n) F G hF hG hint _ hz
