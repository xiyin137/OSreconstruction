import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45TraceMembership

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ}

/-- The real embedding of `n`-point configurations is continuous. -/
theorem continuous_realEmbedNPoint :
    Continuous
      (BHW.realEmbed :
        NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact Complex.continuous_ofReal.comp
    ((continuous_apply μ).comp (continuous_apply k))

/-- Permuting the point labels of a real `n`-point configuration is
continuous. -/
theorem continuous_permNPoint (τ : Equiv.Perm (Fin n)) :
    Continuous (fun x : NPointDomain d n => fun k => x (τ k)) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (τ k))

/-- The OS45 horizontal common-edge real map is continuous. -/
theorem continuous_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n)) :
    Continuous
      (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [BHW.os45CommonEdgeRealPoint] using
      (((continuous_apply (0 : Fin (d + 1))).comp
        (continuous_apply (σ k))).div_const 2)
  · simpa [BHW.os45CommonEdgeRealPoint, hμ] using
      ((continuous_apply μ).comp (continuous_apply (σ k)))

/-- The embedded OS45 horizontal common-edge real map is continuous. -/
theorem continuous_realEmbed_os45CommonEdgeRealPoint
    (σ : Equiv.Perm (Fin n)) :
    Continuous
      (fun x : NPointDomain d n =>
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) σ x)) :=
  BHW.continuous_realEmbedNPoint.comp
    (BHW.continuous_os45CommonEdgeRealPoint
      (d := d) (n := n) σ)

/-- Compact-parameter tube lemma: if a continuous family is inside an open set
along `{x0} × Y` and `Y` is compact, then a single open neighborhood of `x0`
works for all parameters. -/
theorem exists_open_nhds_forall_mem_of_compact_parameter
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace Y]
    {f : X × Y → Z} (hf : Continuous f)
    {x0 : X} {U : Set Z} (hU_open : IsOpen U)
    (hx0 : ∀ y : Y, f (x0, y) ∈ U) :
    ∃ V : Set X,
      IsOpen V ∧ x0 ∈ V ∧
        ∀ x ∈ V, ∀ y : Y, f (x, y) ∈ U := by
  have hP : ∀ y ∈ (Set.univ : Set Y),
      ∀ᶠ z : X × Y in 𝓝 (x0, y), f z ∈ U := by
    intro y _hy
    exact hf.continuousAt.preimage_mem_nhds
      (hU_open.mem_nhds (hx0 y))
  have hEventually :
      ∀ᶠ x in 𝓝 x0,
        ∀ y ∈ (Set.univ : Set Y), f (x, y) ∈ U :=
    (isCompact_univ : IsCompact (Set.univ : Set Y)).eventually_forall_of_forall_eventually
      hP
  rcases mem_nhds_iff.mp hEventually with
    ⟨V, hV_sub, hV_open, hx0V⟩
  refine ⟨V, hV_open, hx0V, ?_⟩
  intro x hx y
  exact hV_sub hx y trivial

/-- Time coefficient for the identity branch in the Streater-Wightman
Figure-2-4 path.  It interpolates from Wick time `I * τ` to the inverse OS45
quarter-turn time `(1 + I) * τ / 2`. -/
def os45Figure24TimeCoeff (t : unitInterval) : ℂ :=
  (((t : ℝ) / 2 : ℝ) : ℂ) +
    (((1 : ℝ) - (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I

theorem os45Figure24TimeCoeff_zero :
    os45Figure24TimeCoeff (0 : unitInterval) = Complex.I := by
  norm_num [os45Figure24TimeCoeff]

theorem os45Figure24TimeCoeff_one :
    os45Figure24TimeCoeff (1 : unitInterval) =
      ((1 : ℂ) + Complex.I) / 2 := by
  norm_num [os45Figure24TimeCoeff]
  ring

theorem continuous_os45Figure24TimeCoeff :
    Continuous BHW.os45Figure24TimeCoeff := by
  have ht : Continuous (fun t : unitInterval => (t : ℝ)) :=
    continuous_subtype_val
  have hhalf : Continuous (fun t : unitInterval => ((t : ℝ) / 2)) :=
    ht.div_const 2
  have hleft :
      Continuous (fun t : unitInterval => (((t : ℝ) / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hhalf
  have hrightCoeff :
      Continuous
        (fun t : unitInterval =>
          ((((1 : ℝ) - (t : ℝ) / 2 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub hhalf)
  have hI : Continuous (fun _ : unitInterval => Complex.I) :=
    continuous_const
  change Continuous
    (fun t : unitInterval =>
      (((t : ℝ) / 2 : ℝ) : ℂ) +
        ((((1 : ℝ) - (t : ℝ) / 2 : ℝ)) : ℂ) * Complex.I)
  exact hleft.add (hrightCoeff.mul hI)

/-- The identity-side Figure-2-4 path from the Wick configuration to the
inverse OS45 quarter-turn of the horizontal common edge. -/
def os45Figure24IdentityPath
    (x : NPointDomain d n)
    (t : unitInterval) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    if μ = 0 then os45Figure24TimeCoeff t * (x k 0 : ℂ)
    else (x k μ : ℂ)

theorem os45Figure24IdentityPath_zero
    (x : NPointDomain d n) :
    os45Figure24IdentityPath (d := d) (n := n) x (0 : unitInterval) =
      (fun k => wickRotatePoint (x k)) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45Figure24IdentityPath, os45Figure24TimeCoeff_zero,
      wickRotatePoint]
  · simp [os45Figure24IdentityPath, wickRotatePoint, hμ]

theorem os45Figure24IdentityPath_one
    (x : NPointDomain d n) :
    let Q := BHW.os45QuarterTurnCLE (d := d) (n := n)
    let y := BHW.os45CommonEdgeRealPoint (d := d) (n := n)
      (1 : Equiv.Perm (Fin n)) x
    os45Figure24IdentityPath (d := d) (n := n) x (1 : unitInterval) =
      Q.symm (BHW.realEmbed y) := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [os45Figure24IdentityPath, os45Figure24TimeCoeff_one,
      BHW.os45QuarterTurnCLE_symm_apply, BHW.os45CommonEdgeRealPoint,
      BHW.realEmbed]
    ring
  · simp [os45Figure24IdentityPath, BHW.os45QuarterTurnCLE_symm_apply,
      BHW.os45CommonEdgeRealPoint, BHW.realEmbed, hμ]

theorem continuous_os45Figure24IdentityPath
    (x : NPointDomain d n) :
    Continuous (BHW.os45Figure24IdentityPath (d := d) (n := n) x) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [os45Figure24IdentityPath] using
      (BHW.continuous_os45Figure24TimeCoeff.mul continuous_const)
  · simpa [os45Figure24IdentityPath, hμ] using
      (continuous_const : Continuous
        (fun _ : unitInterval => (x k μ : ℂ)))

/-- If the real configuration has zero Euclidean time coordinates, the
Figure-2-4 identity path is constant and equal to its real embedding. -/
theorem os45Figure24IdentityPath_of_time_zero
    (x : NPointDomain d n)
    (hx_time0 : ∀ k : Fin n, x k 0 = 0)
    (t : unitInterval) :
    BHW.os45Figure24IdentityPath (d := d) (n := n) x t =
      BHW.realEmbed x := by
  ext k μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [BHW.os45Figure24IdentityPath, BHW.realEmbed, hx_time0 k]
  · simp [BHW.os45Figure24IdentityPath, BHW.realEmbed, hμ]

/-- Joint continuity of the Figure-2-4 identity path in the real point and the
path parameter. -/
theorem continuous_os45Figure24IdentityPath_joint :
    Continuous
      (fun p : NPointDomain d n × unitInterval =>
        BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hcoord : Continuous
      (fun p : NPointDomain d n × unitInterval => (p.1 k μ : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp ((continuous_apply k).comp continuous_fst))
  by_cases hμ : μ = 0
  · subst hμ
    have htime :
        Continuous
          (fun p : NPointDomain d n × unitInterval =>
            BHW.os45Figure24TimeCoeff p.2) :=
      BHW.continuous_os45Figure24TimeCoeff.comp continuous_snd
    have htimeCoord : Continuous
        (fun p : NPointDomain d n × unitInterval => (p.1 k 0 : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ((continuous_apply (0 : Fin (d + 1))).comp
          ((continuous_apply k).comp continuous_fst))
    simpa [BHW.os45Figure24IdentityPath] using htime.mul htimeCoord
  · simpa [BHW.os45Figure24IdentityPath, hμ] using hcoord

/-- Along the identity ordered sector, the Figure-2-4 identity path stays in
the ordinary forward tube.  The imaginary time gaps are the positive scalar
`1 - t / 2` times the Euclidean ordered time gaps, and the spatial imaginary
gaps vanish. -/
theorem os45Figure24IdentityPath_mem_forwardTube
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))) :
    ∀ t,
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t ∈
        BHW.ForwardTube d n := by
  intro t k
  let coeff : ℝ := 1 - (t : ℝ) / 2
  let gap : ℝ :=
    if (k : ℕ) = 0 then x k 0
    else x k 0 - x ⟨(k : ℕ) - 1, by omega⟩ 0
  let η : Fin (d + 1) → ℝ := fun μ =>
    (BHW.os45Figure24IdentityPath (d := d) (n := n) x t k μ).im -
      ((if (k : ℕ) = 0 then 0 else
        BHW.os45Figure24IdentityPath (d := d) (n := n) x t
          ⟨(k : ℕ) - 1, by omega⟩) μ).im
  have hcoeff_pos : 0 < coeff := by
    have ht_le : (t : ℝ) ≤ 1 := t.property.2
    dsimp [coeff]
    nlinarith
  have hx_ord : x ∈ OrderedPositiveTimeRegion d n := by
    simpa [EuclideanOrderedPositiveTimeSector] using hx_ordered
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    by_cases hk : (k : ℕ) = 0
    · have hbase : 0 < x k 0 := (hx_ord k).1
      simpa [hk] using hbase
    · let j : Fin n := ⟨(k : ℕ) - 1, by omega⟩
      have hj_lt_k : j < k := Fin.lt_def.mpr (by
        dsimp [j]
        omega)
      have hlt : x j 0 < x k 0 := (hx_ord j).2 k hj_lt_k
      have hgap : 0 < x k 0 - x j 0 := sub_pos.mpr hlt
      simpa [hk, j] using hgap
  have hη0 : η 0 = coeff * gap := by
    dsimp [η, coeff, gap]
    by_cases hk : (k : ℕ) = 0
    · simp [BHW.os45Figure24IdentityPath, BHW.os45Figure24TimeCoeff, hk,
        Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
    · simp [BHW.os45Figure24IdentityPath, BHW.os45Figure24TimeCoeff, hk,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      ring
  have hη0_pos : 0 < η 0 := by
    rw [hη0]
    exact mul_pos hcoeff_pos hgap_pos
  have hspatial_zero : ∀ i : Fin d, η i.succ = 0 := by
    intro i
    dsimp [η]
    by_cases hk : (k : ℕ) = 0
    · simp [BHW.os45Figure24IdentityPath, hk]
    · simp [BHW.os45Figure24IdentityPath, hk]
  dsimp [BHW.ForwardTube, BHW.InOpenForwardCone]
  change η 0 > 0 ∧
    (∑ μ, LorentzLieGroup.minkowskiSignature d μ * η μ ^ 2) < 0
  constructor
  · exact hη0_pos
  · rw [BHW.minkowski_sum_decomp (d := d) (η := η)]
    have hsum_zero : (∑ i : Fin d, η i.succ ^ 2) = 0 := by
      simp [hspatial_zero]
    rw [hsum_zero]
    nlinarith [sq_pos_of_pos hη0_pos]

theorem continuous_figure24RotateAdjacentConfig
    (hd : 2 ≤ d) :
    Continuous (BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  have hcoord : ∀ ν : Fin (d + 1), Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ => z k ν) := by
    intro ν
    exact (continuous_apply ν).comp (continuous_apply k)
  by_cases h0 : μ = 0
  · simpa [figure24RotateAdjacentConfig, h0] using hcoord μ
  · by_cases h1 : μ = BHW.figure24Axis1 (d := d) hd
    · simpa [figure24RotateAdjacentConfig, h1] using
        (continuous_const.mul
          (hcoord (BHW.figure24Axis1 (d := d) hd))).sub
          (continuous_const.mul
            (hcoord (BHW.figure24Axis2 (d := d) hd)))
    · by_cases h2 : μ = BHW.figure24Axis2 (d := d) hd
      · simpa [figure24RotateAdjacentConfig, h1, h2] using
          (continuous_const.mul
            (hcoord (BHW.figure24Axis1 (d := d) hd))).add
            (continuous_const.mul
              (hcoord (BHW.figure24Axis2 (d := d) hd)))
      · simpa [figure24RotateAdjacentConfig, h0, h1, h2] using hcoord μ

/-- Complex Lorentz transformations preserve the source Minkowski Gram
matrix. -/
theorem sourceMinkowskiGram_complexLorentzAction
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    BHW.sourceMinkowskiGram d n (BHW.complexLorentzAction Λ z) =
      BHW.sourceMinkowskiGram d n z := by
  ext i j
  simp only [BHW.sourceMinkowskiGram, BHW.complexLorentzAction]
  have hmetric : ∀ μ ν : Fin (d + 1),
      (∑ x, ↑(MinkowskiSpace.metricSignature d x) *
        Λ.val x μ * Λ.val x ν) =
        if μ = ν then (MinkowskiSpace.metricSignature d μ : ℂ) else 0 := by
    intro μ ν
    simpa [MinkowskiSpace.metricSignature,
      LorentzLieGroup.minkowskiSignature] using
      Λ.metric_preserving μ ν
  calc
    ∑ x, (↑(MinkowskiSpace.metricSignature d x) * ∑ ν, Λ.val x ν * z i ν) *
        ∑ ν, Λ.val x ν * z j ν
        = ∑ μ, ∑ ν,
            (∑ x, (↑(MinkowskiSpace.metricSignature d x) *
              Λ.val x μ * Λ.val x ν)) * z i ν * z j μ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ν _
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ μ, ∑ ν,
          (if μ = ν then
            (MinkowskiSpace.metricSignature d μ : ℂ) else 0) *
            z i ν * z j μ := by
          simp [hmetric]
    _ = ∑ μ, (↑(MinkowskiSpace.metricSignature d μ) * z i μ * z j μ) := by
          simp
    _ = ∑ μ, ↑(MinkowskiSpace.metricSignature d μ) * z i μ * z j μ := by
          rfl

/-- Continuity of the rotated adjacent Figure-2-4 path in the real point and
path parameter. -/
theorem continuous_figure24RotatedIdentityPath
    (hd : 2 ≤ d)
    (τ : Equiv.Perm (Fin n)) :
    Continuous
      (fun p : NPointDomain d n × unitInterval =>
        BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
          (BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2))) := by
  have hperm : Continuous
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.permAct (d := d) τ z) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (τ k))
  exact (BHW.continuous_figure24RotateAdjacentConfig (d := d) (n := n) hd).comp
    (hperm.comp BHW.continuous_os45Figure24IdentityPath_joint)

/-- Figure-2-4 path-stability neighborhood around the equal-time adjacent
support witness.  The adjacent path is the rotated two-plane realization, not
the bare adjacent relabelling of the identity path. -/
theorem swFigure24_adjacentPathStableNeighborhood_exists
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Upath : Set (NPointDomain d n))
      (xfig : NPointDomain d n),
      IsOpen Upath ∧ xfig ∈ Upath ∧
      (∀ k : Fin n, xfig k 0 = 0) ∧
      xfig ∈ BHW.JostSet d n ∧
      BHW.realEmbed xfig ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed (fun k => xfig (τ k)) ∈
        BHW.ExtendedTube d n ∧
      (∀ x ∈ Upath,
        ∃ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ,
          Continuous Δ ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n
                  (BHW.os45Figure24IdentityPath
                    (d := d) (n := n) x t)))) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.figure24_adjacentTwoPlaneRotationSupport
      (d := d) (n := n) hd i hi with
    ⟨xfig, xrot, Λfig, hxfig_time0, hxfig_J, hxfig_ET,
      hrot_formula, hxrot_FJ, hΛfig⟩
  have hd1 : 1 ≤ d :=
    Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hd)
  have hxrot_ET : BHW.realEmbed xrot ∈ BHW.ExtendedTube d n :=
    BHW.forwardJostSet_subset_extendedTube (d := d) (n := n) hd1 xrot hxrot_FJ
  have hxfig_swapET :
      BHW.realEmbed (fun k => xfig (τ k)) ∈ BHW.ExtendedTube d n := by
    have hact :
        BHW.complexLorentzAction Λfig (BHW.realEmbed xrot) ∈
          BHW.ExtendedTube d n :=
      BHW.complexLorentzAction_mem_extendedTube (d := d) n
        (z := BHW.realEmbed xrot) Λfig hxrot_ET
    exact hΛfig ▸ hact
  let H : NPointDomain d n × unitInterval → Fin n → Fin (d + 1) → ℂ :=
    fun p =>
      BHW.figure24RotateAdjacentConfig (d := d) (n := n) hd
        (BHW.permAct (d := d) τ
          (BHW.os45Figure24IdentityPath (d := d) (n := n) p.1 p.2))
  have hH_cont : Continuous H := by
    simpa [H] using
      (BHW.continuous_figure24RotatedIdentityPath
        (d := d) (n := n) hd τ)
  have hH_base : ∀ t : unitInterval, H (xfig, t) ∈ BHW.ExtendedTube d n := by
    intro t
    have hpath_zero :
        BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t =
          BHW.realEmbed xfig :=
      BHW.os45Figure24IdentityPath_of_time_zero
        (d := d) (n := n) xfig hxfig_time0 t
    have hperm :
        BHW.permAct (d := d) τ
            (BHW.os45Figure24IdentityPath (d := d) (n := n) xfig t) =
          BHW.realEmbed (fun k => xfig (τ k)) := by
      ext k μ
      simp [BHW.permAct, hpath_zero, BHW.realEmbed]
    have hH_eq : H (xfig, t) = BHW.realEmbed xrot := by
      dsimp [H]
      rw [hperm]
      exact hrot_formula.symm
    simpa [hH_eq] using hxrot_ET
  rcases BHW.exists_open_nhds_forall_mem_of_compact_parameter
      (X := NPointDomain d n) (Y := unitInterval)
      (Z := Fin n → Fin (d + 1) → ℂ)
      (f := H) hH_cont BHW.isOpen_extendedTube hH_base with
    ⟨Upath, hUpath_open, hxfig_Upath, hUpath_path⟩
  refine ⟨Upath, xfig, hUpath_open, hxfig_Upath, hxfig_time0, hxfig_J,
    hxfig_ET, hxfig_swapET, ?_⟩
  intro x hxUpath
  let Δ : unitInterval → Fin n → Fin (d + 1) → ℂ := fun t => H (x, t)
  refine ⟨Δ, ?_, ?_, ?_⟩
  · exact hH_cont.comp (continuous_const.prodMk continuous_id)
  · intro t
    exact hUpath_path x hxUpath t
  · intro t
    let Γ : Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x t
    rcases BHW.figure24RotateAdjacentConfig_lorentz_inverse
        (d := d) (n := n) hd with
      ⟨Λinv, hΛinv⟩
    have hInv :
        BHW.complexLorentzAction Λinv (Δ t) =
          BHW.permAct (d := d) τ Γ := by
      simpa [Δ, H, Γ] using
        hΛinv (BHW.permAct (d := d) τ Γ)
    have hLor :
        BHW.sourceMinkowskiGram d n
            (BHW.complexLorentzAction Λinv (Δ t)) =
          BHW.sourceMinkowskiGram d n (Δ t) :=
      BHW.sourceMinkowskiGram_complexLorentzAction
        (d := d) (n := n) Λinv (Δ t)
    calc
      BHW.sourceMinkowskiGram d n (Δ t)
          = BHW.sourceMinkowskiGram d n
              (BHW.complexLorentzAction Λinv (Δ t)) := hLor.symm
      _ = BHW.sourceMinkowskiGram d n (BHW.permAct (d := d) τ Γ) := by
            rw [hInv]
      _ = BHW.sourcePermuteComplexGram n τ
            (BHW.sourceMinkowskiGram d n Γ) := by
            simpa [BHW.permAct] using
              BHW.sourceMinkowskiGram_perm d n τ Γ

/-- Anchored Figure-2-4 source environment with the compact-open
path-stability field.  The same equal-time witness supplies both the source
domain and the path-stability neighborhood. -/
theorem swFigure24_adjacentHorizontalEnvironmentWithPathStability
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∃ (Ufig Upath : Set (NPointDomain d n))
      (x0 : NPointDomain d n),
      IsOpen Ufig ∧ IsOpen Upath ∧
      x0 ∈ Ufig ∧ x0 ∈ Upath ∧
      (∀ k : Fin n, x0 k 0 = 0) ∧
      (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
      (∀ x ∈ Ufig,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
      (∀ x ∈ Upath,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) →
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t)))) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentPathStableNeighborhood_exists
      (d := d) (n := n) hd i hi with
    ⟨Upath, x0, hUpath_open, hx0Upath, hx0_time0, hx0J, hx0ET,
      hx0SwapET, hUpath_path⟩
  let Ufig : Set (NPointDomain d n) :=
    BHW.JostSet d n ∩
      {x | BHW.realEmbed x ∈ BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n)
            (1 : Equiv.Perm (Fin n))} ∩
      {x |
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ}
  have hswapReal_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed (fun k => x (τ k))) :=
    BHW.continuous_realEmbedNPoint.comp
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hcommon_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) :=
    BHW.continuous_realEmbed_os45CommonEdgeRealPoint
      (d := d) (n := n) (1 : Equiv.Perm (Fin n))
  have hUfig_open : IsOpen Ufig := by
    dsimp [Ufig]
    exact (((BHW.isOpen_jostSet (d := d) (n := n)).inter
      (BHW.isOpen_extendedTube.preimage
        (BHW.continuous_realEmbedNPoint (d := d) (n := n)))).inter
      (BHW.isOpen_extendedTube.preimage hswapReal_cont)).inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))).preimage hcommon_cont) |>.inter
      ((BHW.isOpen_os45PulledRealBranchDomain (d := d) (n := n) τ).preimage
        hcommon_cont)
  have hx0_common :
      BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x0 = x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45CommonEdgeRealPoint, hx0_time0 k]
    · simp [BHW.os45CommonEdgeRealPoint, hμ]
  have hQsymm_x0 :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed x0) =
        BHW.realEmbed x0 := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hx0_time0 k]
    · simp [BHW.os45QuarterTurnCLE_symm_apply, BHW.realEmbed, hμ]
  have hx0_pulled_id :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    change
      BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    simpa [BHW.permAct] using hx0ET
  have hx0_pulled_tau :
      BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x0) ∈
        BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    change
      BHW.permAct (d := d) τ.symm
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x0))) ∈
        BHW.ExtendedTube d n
    rw [hx0_common, hQsymm_x0]
    have hperm :
        BHW.permAct (d := d) τ.symm (BHW.realEmbed x0) =
          BHW.realEmbed (fun k => x0 (τ k)) := by
      ext k μ
      simp [BHW.permAct, BHW.realEmbed, τ]
    simpa [hperm] using hx0SwapET
  have hx0Ufig : x0 ∈ Ufig := by
    exact ⟨⟨⟨⟨hx0J, hx0ET⟩, hx0SwapET⟩, hx0_pulled_id⟩,
      hx0_pulled_tau⟩
  refine ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
    hx0_time0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1.1.1.1
  · intro x hx
    exact hx.1.1.1.2
  · intro x hx
    exact hx.1.1.2
  · intro x hx
    exact hx.1.2
  · intro x hx
    exact hx.2
  · intro x hxUpath hx_ordered
    let Γ : unitInterval → Fin n → Fin (d + 1) → ℂ :=
      BHW.os45Figure24IdentityPath (d := d) (n := n) x
    rcases hUpath_path x hxUpath with
      ⟨Δ, hΔ_cont, hΔ_ET, hΔ_gram⟩
    refine ⟨Γ, Δ, ?_, hΔ_cont, ?_, ?_, ?_, hΔ_ET, ?_⟩
    · exact BHW.continuous_os45Figure24IdentityPath (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_zero (d := d) (n := n) x
    · simpa [Γ] using
        BHW.os45Figure24IdentityPath_one (d := d) (n := n) x
    · intro t
      exact BHW.forwardTube_subset_extendedTube
        (BHW.os45Figure24IdentityPath_mem_forwardTube
          (d := d) (n := n) hx_ordered t)
    · intro t
      simpa [Γ, τ] using hΔ_gram t

/-- Source patch for the identity-order adjacent OS45 horizontal edge.  The
selected connected patch has compact closure inside the anchored Figure-2-4
source environment and carries the closure-level horizontal edge and
path-stability fields needed by the branchwise boundary-value step. -/
theorem os45_adjacent_identity_horizontalEdge_sourcePatch
    [NeZero d]
    (hd : 2 ≤ d)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (Ufig V : Set (NPointDomain d n)) (xseed : NPointDomain d n),
      IsOpen Ufig ∧
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧ xseed ∈ V ∧
      IsCompact (closure V) ∧
      closure V ⊆ Ufig ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ Ufig, x ∈ BHW.JostSet d n) ∧
       (∀ x ∈ Ufig, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed (fun k => x (τ k)) ∈
           BHW.ExtendedTube d n) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ Ufig,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ)) ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            (Equiv.swap i ⟨i.val + 1, hi⟩)) ∧
      (∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n))) ∧
      (∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x) ∧
      (∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ∧
      (let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
           (1 : Equiv.Perm (Fin n))) ∧
       (∀ x ∈ closure V,
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) 1) ∧
       (∀ x ∈ closure V,
         BHW.realEmbed
           (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
           BHW.os45PulledRealBranchDomain (d := d) (n := n) τ) ∧
       (∀ x ∈ closure V,
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t))))) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability
      (d := d) (n := n) hd i hi with
    ⟨Ufig, Upath, x0, hUfig_open, hUpath_open, hx0Ufig, hx0Upath,
      hx0_time0, hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau, hUpath_path⟩
  let Ubase : Set (NPointDomain d n) := Ufig ∩ Upath
  have hUbase_open : IsOpen Ubase := hUfig_open.inter hUpath_open
  have hx0Ubase : x0 ∈ Ubase := ⟨hx0Ufig, hx0Upath⟩
  rcases BHW.exists_ordered_small_time_perturb_in_adjacent_overlap_of_lt
      (d := d) (n := n) hd i hi Ubase hUbase_open x0 hx0Ubase
      hx0_time0 (by norm_num : (0 : ℝ) < 1) with
    ⟨ε, _hε_pos, _hε_lt, hxseed_Ubase, hxseed_ordered,
      hxseed_swap_ordered⟩
  let xseed : NPointDomain d n :=
    BHW.adjacentTimePerturb (d := d) (n := n) x0 ε
  let ordered : Set (NPointDomain d n) :=
    EuclideanOrderedPositiveTimeSector (d := d) (n := n)
      (1 : Equiv.Perm (Fin n))
  let swappedOrdered : Set (NPointDomain d n) :=
    {x |
      (fun k => x (τ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ}
  let Ufinal : Set (NPointDomain d n) :=
    Ufig ∩ Upath ∩ ordered ∩ swappedOrdered
  have hswappedOrdered_open : IsOpen swappedOrdered := by
    dsimp [swappedOrdered]
    exact (BHW.isOpen_euclideanOrderedPositiveTimeSector
      (d := d) (n := n) τ).preimage
      (BHW.continuous_permNPoint (d := d) (n := n) τ)
  have hUfinal_open : IsOpen Ufinal := by
    dsimp [Ufinal, ordered]
    exact (((hUfig_open.inter hUpath_open).inter
      (BHW.isOpen_euclideanOrderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)))).inter
      hswappedOrdered_open)
  have hxseedUfinal : xseed ∈ Ufinal := by
    exact ⟨⟨⟨hxseed_Ubase.1, hxseed_Ubase.2⟩, hxseed_ordered⟩,
      by simpa [swappedOrdered, τ] using hxseed_swap_ordered⟩
  rcases BHW.exists_connected_open_precompact_subset
      (d := d) (n := n) (x0 := xseed) (U := Ufinal)
      hUfinal_open hxseedUfinal with
    ⟨V, hV_open, hV_connected, hxseedV, hV_compact, hclosureV_Ufinal⟩
  have hV_nonempty : V.Nonempty := ⟨xseed, hxseedV⟩
  have hclosureV_Ufig : closure V ⊆ Ufig := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.1
  have hclosureV_Upath : closure V ⊆ Upath := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.1.2
  have hclosureV_ordered :
      ∀ x ∈ closure V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact (hclosureV_Ufinal hx).1.2
  have hclosureV_swap_ordered :
      ∀ x ∈ closure V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact (hclosureV_Ufinal hx).2
  have hV_Ufig : ∀ x ∈ V, x ∈ Ufig := by
    intro x hx
    exact hclosureV_Ufig (subset_closure hx)
  have hV_ordered :
      ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact hclosureV_ordered x (subset_closure hx)
  have hV_swap_ordered :
      ∀ x ∈ V,
        (fun k => x (τ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ := by
    intro x hx
    exact hclosureV_swap_ordered x (subset_closure hx)
  have hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n := by
    intro x hx
    exact hUfig_jost x (hV_Ufig x hx)
  have hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_ET x (hV_Ufig x hx)
  have hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (τ k)) ∈
          BHW.ExtendedTube d n := by
    intro x hx
    exact hUfig_swapET x (hV_Ufig x hx)
  have hV_wick :
      ∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi
            (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    exact BHW.wickRotate_mem_adjacentOS45WickSeedDomain_of_ordered
      (d := d) (n := n) i hi x (1 : Equiv.Perm (Fin n))
      (hV_ordered x hx) (by simpa [τ] using hV_swap_ordered x hx)
  have hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi := by
    intro x hx
    exact BHW.realEmbed_mem_adjacentOS45RealEdgeDomain_of_ET
      (d := d) (n := n) i hi x (hV_ET x hx)
      (by simpa [τ] using hV_swapET x hx)
  have hV_geom_id :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) x
      (hV_ordered x hx)
  have hV_geom_tau :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) τ
          (fun k => x (τ k)) := by
    intro x hx
    exact BHW.os45OppositeTubeBranchGeometry_of_ordered
      (d := d) (n := n) τ (fun k => x (τ k))
      (hV_swap_ordered x hx)
  have hV_pulled_id :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hV_Ufig x hx)
  have hV_pulled_tau :
      ∀ x ∈ V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hV_Ufig x hx)
  have hclosureV_pulled_id :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) 1 := by
    intro x hx
    exact hUfig_pulled_id x (hclosureV_Ufig hx)
  have hclosureV_pulled_tau :
      ∀ x ∈ closure V,
        BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n) 1 x) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) τ := by
    intro x hx
    exact hUfig_pulled_tau x (hclosureV_Ufig hx)
  have hclosureV_path :
      ∀ x ∈ closure V,
        ∃ (Γ Δ : unitInterval → Fin n → Fin (d + 1) → ℂ),
          Continuous Γ ∧
          Continuous Δ ∧
          Γ (0 : unitInterval) = (fun k => wickRotatePoint (x k)) ∧
          Γ (1 : unitInterval) =
            (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) x)) ∧
          (∀ t, Γ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t, Δ t ∈ BHW.ExtendedTube d n) ∧
          (∀ t,
            BHW.sourceMinkowskiGram d n (Δ t) =
              BHW.sourcePermuteComplexGram n τ
                (BHW.sourceMinkowskiGram d n (Γ t))) := by
    intro x hx
    exact hUpath_path x (hclosureV_Upath hx) (hclosureV_ordered x hx)
  refine ⟨Ufig, V, xseed, hUfig_open, hV_open, hV_connected,
    hV_nonempty, hxseedV, hV_compact, hclosureV_Ufig, ?_, hV_jost,
    hV_ET, ?_, hV_ordered, ?_, hV_wick, hV_real, hV_geom_id, ?_, ?_⟩
  · exact ⟨hUfig_jost, hUfig_ET, hUfig_swapET, hUfig_pulled_id,
      hUfig_pulled_tau⟩
  · intro x hx
    simpa [τ] using hV_swapET x hx
  · intro x hx
    simpa [τ] using hV_swap_ordered x hx
  · intro x hx
    simpa [τ] using hV_geom_tau x hx
  · exact ⟨hV_pulled_id, hV_pulled_tau, hclosureV_ordered,
      (by intro x hx; simpa [τ] using hclosureV_swap_ordered x hx),
      hclosureV_pulled_id, hclosureV_pulled_tau, hclosureV_path⟩

end BHW
