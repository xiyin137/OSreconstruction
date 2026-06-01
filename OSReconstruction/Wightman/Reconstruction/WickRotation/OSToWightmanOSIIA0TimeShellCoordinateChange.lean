import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge
import OSReconstruction.SCV.DistributionalRepresentationGluing
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# OS-II A0 Time-Shell Coordinate Change

This file contains the measure-preserving coordinate transport from a local
coordinate-space A0 representative to the Section 4.3 right-time-shell surface.
It is the concrete change of variables used before the scalar partial-Fubini
step in OS II V.1--V.2.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Pure partial-Fubini identity for the scalar time-shell representative. -/
theorem osiiA0_partialFubini_scalar_timeShell
    {E T : Type*} [MeasurableSpace E] [MeasurableSpace T]
    {μ : Measure E} {ν : Measure T} [SFinite μ] [SFinite ν]
    (K : E → T → ℂ) (a : E → ℂ) (φ : T → ℂ)
    (hint :
      Integrable (fun p : E × T => K p.1 p.2 * a p.1 * φ p.2)
        (μ.prod ν)) :
    (∫ p : E × T, K p.1 p.2 * a p.1 * φ p.2 ∂(μ.prod ν)) =
      ∫ τ : T, (∫ e : E, K e τ * a e ∂μ) * φ τ ∂ν := by
  calc
    (∫ p : E × T, K p.1 p.2 * a p.1 * φ p.2 ∂(μ.prod ν))
        = ∫ τ : T, ∫ e : E, K e τ * a e * φ τ ∂μ ∂ν := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_prod_symm
              (μ := μ) (ν := ν)
              (f := fun p : E × T => K p.1 p.2 * a p.1 * φ p.2) hint)
    _ = ∫ τ : T, (∫ e : E, K e τ * a e ∂μ) * φ τ ∂ν := by
          apply integral_congr_ae
          filter_upwards with τ
          simpa [mul_assoc] using
            (MeasureTheory.integral_mul_const
              (μ := μ) (r := φ τ) (f := fun e : E => K e τ * a e))

/-- The concrete scalar time-shell representative obtained by partially
integrating a local coordinate representative against the frozen reflected-left
and right-spatial weights. -/
noncomputable def osiiA0_timeShellScalarFromCoordinateRepresentative
    {n m : ℕ}
    (H : NPointDomain d n → (Fin m → ℝ) → Section43SpatialSpace d m → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m) :
    (Fin m → ℝ) → ℂ :=
  fun τ =>
    ∫ e : NPointDomain d n × Section43SpatialSpace d m,
      H e.1 τ e.2 * (fLeft.osConj e.1 * κ.1 e.2)

/-- The A0 time-shell scalar only depends on the coordinate representative on
the support of the frozen reflected-left and right-spatial integration weight.

This is the carrier step used after local MZ gluing: a branch representative
does not have to be globally identified with the full-coordinate A0
representative, only on the part of the slice where the fixed integral weight
is nonzero. -/
theorem osiiA0_timeShellScalar_congr_on_weight_support
    {n m : ℕ}
    (H H' : NPointDomain d n → (Fin m → ℝ) → Section43SpatialSpace d m → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (τ : Fin m → ℝ)
    (hEq :
      ∀ e : NPointDomain d n × Section43SpatialSpace d m,
        e.1 ∈ tsupport ((fLeft.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) →
        e.2 ∈ tsupport (κ.1 : Section43SpatialSpace d m → ℂ) →
          H e.1 τ e.2 = H' e.1 τ e.2) :
    osiiA0_timeShellScalarFromCoordinateRepresentative H fLeft κ τ =
      osiiA0_timeShellScalarFromCoordinateRepresentative H' fLeft κ τ := by
  apply integral_congr_ae
  filter_upwards with e
  by_cases heLeft :
      e.1 ∈ tsupport ((fLeft.osConj : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)
  · by_cases heSpatial :
        e.2 ∈ tsupport (κ.1 : Section43SpatialSpace d m → ℂ)
    · rw [hEq e heLeft heSpatial]
    · have hκ_zero : κ.1 e.2 = 0 :=
        image_eq_zero_of_notMem_tsupport heSpatial
      simp [hκ_zero]
  · have hf_zero : (fLeft.osConj : SchwartzNPoint d n) e.1 = 0 :=
      image_eq_zero_of_notMem_tsupport heLeft
    simp [hf_zero]

/-- Right block reconstructed from Section 4.3 time/spatial coordinates through
the difference-coordinate chart. -/
noncomputable def osiiA0_rightFromTimeSpatial (d m : ℕ) [NeZero d]
    (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    NPointDomain d m :=
  (section43DiffCoordRealCLE d m).symm
    ((nPointTimeSpatialCLE (d := d) m).symm (τ, η))

@[simp] theorem osiiA0_section43QTime_nPointTimeSpatialCLE_symm
    {m : ℕ} (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    section43QTime (d := d) (n := m)
        ((nPointTimeSpatialCLE (d := d) m).symm (τ, η)) =
      τ := by
  have h := (nPointTimeSpatialCLE (d := d) m).apply_symm_apply (τ, η)
  exact congrArg Prod.fst h

@[simp] theorem osiiA0_section43QSpatial_nPointTimeSpatialCLE_symm
    {m : ℕ} (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    section43QSpatial (d := d) (n := m)
        ((nPointTimeSpatialCLE (d := d) m).symm (τ, η)) =
      η := by
  have h := (nPointTimeSpatialCLE (d := d) m).apply_symm_apply (τ, η)
  exact congrArg Prod.snd h

/-- Support-local branch equality inside the A0 time-shell integral gives the
compact-carrier Schwinger-shell equality required by the compact BVT handoff. -/
theorem osiiA0_glued_timeShellScalar_schwinger_of_weight_support
    {n m : ℕ} {ι : Type*}
    (N : ι → Set (NPointDomain d (n + m)))
    (D : ι → NPointDomain d (n + m) → ℂ)
    (Hsch : NPointDomain d n → (Fin m → ℝ) → Section43SpatialSpace d m → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (K : Set (Fin m → ℝ))
    (Sch : (Fin m → ℝ) → ℂ)
    (hBranch :
      ∀ τ ∈ K, ∀ e : NPointDomain d n × Section43SpatialSpace d m,
        e.1 ∈ tsupport ((fLeft.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) →
        e.2 ∈ tsupport (κ.1 : Section43SpatialSpace d m → ℂ) →
          SCV.glued_iUnion N D
              (Fin.append e.1 (osiiA0_rightFromTimeSpatial d m τ e.2)) =
            Hsch e.1 τ e.2)
    (hSch :
      Set.EqOn
        (osiiA0_timeShellScalarFromCoordinateRepresentative Hsch fLeft κ)
        Sch K) :
    Set.EqOn
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      Sch K := by
  intro τ hτ
  calc
    osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ τ =
      osiiA0_timeShellScalarFromCoordinateRepresentative Hsch fLeft κ τ := by
        exact
          osiiA0_timeShellScalar_congr_on_weight_support
            (d := d)
            (fun xL τ η =>
              SCV.glued_iUnion N D
                (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
            Hsch fLeft κ τ
            (fun e heLeft heSpatial => hBranch τ hτ e heLeft heSpatial)
    _ = Sch τ := hSch hτ

/-- Local-branch form of the support-local scalar Schwinger equality.

In the local MZ/A0 construction the branch identified on the frozen
left/spatial weight support may be given by a local chart representative
`D i`, rather than a globally named full-coordinate function.  The glued branch
has the same time-shell scalar as soon as one such local representative covers
each weighted slice point and agrees there with the Schwinger-normalized
coordinate slice. -/
theorem osiiA0_glued_timeShellScalar_schwinger_of_local_weight_support
    {n m : ℕ} {ι : Type*}
    (N : ι → Set (NPointDomain d (n + m)))
    (D : ι → NPointDomain d (n + m) → ℂ)
    (Hsch : NPointDomain d n → (Fin m → ℝ) → Section43SpatialSpace d m → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (K : Set (Fin m → ℝ))
    (Sch : (Fin m → ℝ) → ℂ)
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j))
    (hBranch :
      ∀ τ ∈ K, ∀ e : NPointDomain d n × Section43SpatialSpace d m,
        e.1 ∈ tsupport ((fLeft.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) →
        e.2 ∈ tsupport (κ.1 : Section43SpatialSpace d m → ℂ) →
          ∃ i : ι,
            Fin.append e.1 (osiiA0_rightFromTimeSpatial d m τ e.2) ∈ N i ∧
              D i (Fin.append e.1
                (osiiA0_rightFromTimeSpatial d m τ e.2)) =
                Hsch e.1 τ e.2)
    (hSch :
      Set.EqOn
        (osiiA0_timeShellScalarFromCoordinateRepresentative Hsch fLeft κ)
        Sch K) :
    Set.EqOn
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      Sch K := by
  intro τ hτ
  calc
    osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ τ =
      osiiA0_timeShellScalarFromCoordinateRepresentative Hsch fLeft κ τ := by
        apply osiiA0_timeShellScalar_congr_on_weight_support
        intro e heLeft heSpatial
        rcases hBranch τ hτ e heLeft heSpatial with ⟨i, hxi, hDi⟩
        exact (SCV.glued_iUnion_eqOn (N := N) (D := D) hEq i hxi).trans hDi
    _ = Sch τ := hSch hτ

/-- Continuity of the scalar time-shell representative obtained from a full
local A0 coordinate representative.

This is the concrete OS-II V.2 continuity input for the positive-time
delta-smearing step: the full representative is continuous on the natural
right-time cylinder, and the fixed left/spatial weights have one compact
support in the integration variables. -/
theorem osiiA0_timeShellScalarFromCoordinateRepresentative_continuousOn_rightTimeCylinder
    {n m : ℕ}
    (H_full : NPointDomain d (n + m) → ℂ)
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (U : Set (Fin m → ℝ))
    (hH_cont :
      ContinuousOn H_full
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }) :
    ContinuousOn
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  let K : Set (NPointDomain d n × Section43SpatialSpace d m) :=
    tsupport ((fLeft.osConj : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ×ˢ
      tsupport (κ.1 : Section43SpatialSpace d m → ℂ)
  have hfLeft_os_comp :
      HasCompactSupport
        ((fLeft.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
    osiiA0_osConj_hasCompactSupport (d := d) fLeft hfLeft_comp
  have hK : IsCompact K := by
    exact hfLeft_os_comp.prod κ.2
  let f : (Fin m → ℝ) →
      (NPointDomain d n × Section43SpatialSpace d m) → ℂ :=
    fun τ e =>
      H_full (Fin.append e.1 (osiiA0_rightFromTimeSpatial d m τ e.2)) *
        (fLeft.osConj e.1 * κ.1 e.2)
  have hmap_cont :
      Continuous
        (fun q : (Fin m → ℝ) ×
            (NPointDomain d n × Section43SpatialSpace d m) =>
          Fin.append q.2.1 (osiiA0_rightFromTimeSpatial d m q.1 q.2.2)) := by
    refine continuous_pi fun i => continuous_pi fun μ => ?_
    by_cases hi : i.val < n
    · have hidx : i = Fin.castAdd m ⟨i.val, hi⟩ := by
        ext
        simp
      rw [hidx]
      simpa only [Fin.append_left] using
        (by
          fun_prop :
          Continuous fun q : (Fin m → ℝ) ×
              (NPointDomain d n × Section43SpatialSpace d m) =>
            q.2.1 ⟨i.val, hi⟩ μ)
    · have hm : i.val - n < m := by omega
      have hidx : i = Fin.natAdd n ⟨i.val - n, hm⟩ := by
        ext
        simp [Fin.natAdd, Nat.add_sub_of_le (Nat.le_of_not_gt hi)]
      rw [hidx]
      simpa only [Fin.append_right] using
        (by
          have hright_cont :
              Continuous fun q : (Fin m → ℝ) ×
                  (NPointDomain d n × Section43SpatialSpace d m) =>
                osiiA0_rightFromTimeSpatial d m q.1 q.2.2 := by
            dsimp [osiiA0_rightFromTimeSpatial]
            fun_prop
          simpa [osiiA0_rightFromTimeSpatial] using
            (continuous_apply μ).comp
              ((continuous_apply ⟨i.val - n, hm⟩).comp hright_cont))
  have hmap_maps :
      Set.MapsTo
        (fun q : (Fin m → ℝ) ×
            (NPointDomain d n × Section43SpatialSpace d m) =>
          Fin.append q.2.1 (osiiA0_rightFromTimeSpatial d m q.1 q.2.2))
        (U ×ˢ Set.univ)
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U } := by
    intro q hq
    rcases q with ⟨τ, xL, η⟩
    change section43QTime (d := d) (n := m)
      (section43DiffCoordRealCLE d m (splitLast n m
        (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)))) ∈ U
    simpa [osiiA0_rightFromTimeSpatial] using hq.1
  have hH_comp :
      ContinuousOn
        (fun q : (Fin m → ℝ) ×
            (NPointDomain d n × Section43SpatialSpace d m) =>
          H_full
            (Fin.append q.2.1
              (osiiA0_rightFromTimeSpatial d m q.1 q.2.2)))
        (U ×ˢ Set.univ) :=
    hH_cont.comp hmap_cont.continuousOn hmap_maps
  have hweight_cont :
      Continuous
        (fun q : (Fin m → ℝ) ×
            (NPointDomain d n × Section43SpatialSpace d m) =>
          fLeft.osConj q.2.1 * κ.1 q.2.2) := by
    fun_prop
  have hfcont : ContinuousOn f.uncurry (U ×ˢ Set.univ) := by
    dsimp [f]
    exact hH_comp.mul hweight_cont.continuousOn
  have hfs : ∀ p, ∀ x, p ∈ U → x ∉ K → f p x = 0 := by
    intro τ e _hτ heK
    dsimp [f, K] at heK ⊢
    by_cases hleft :
        e.1 ∈ tsupport
          ((fLeft.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)
    · have hright :
          e.2 ∉ tsupport (κ.1 : Section43SpatialSpace d m → ℂ) := by
        intro hright
        exact heK ⟨hleft, hright⟩
      have hκ_zero : κ.1 e.2 = 0 :=
        image_eq_zero_of_notMem_tsupport hright
      simp [hκ_zero]
    · have hf_zero : fLeft.osConj e.1 = 0 :=
        image_eq_zero_of_notMem_tsupport hleft
      have hf_zero' :
          starRingEnd ℂ (fLeft (timeReflectionN d e.1)) = 0 := by
        simpa [SchwartzNPoint.osConj_apply] using hf_zero
      rw [hf_zero', zero_mul, mul_zero]
  simpa [osiiA0_timeShellScalarFromCoordinateRepresentative, f] using
    (continuousOn_integral_of_compact_support
      (μ := (volume :
        Measure (NPointDomain d n × Section43SpatialSpace d m)))
      hK hfcont hfs)

/-- Section 4.3 partial-Fubini identity with the concrete time-shell scalar. -/
theorem osiiA0_section43_partialFubini_timeShellScalar
    {n m : ℕ}
    (H : NPointDomain d n → (Fin m → ℝ) → Section43SpatialSpace d m → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hint :
      Integrable
        (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
            (Fin m → ℝ) =>
          H p.1.1 p.2 p.1.2 * (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
        ((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume)) :
    (∫ p : (NPointDomain d n × Section43SpatialSpace d m) ×
        (Fin m → ℝ),
        H p.1.1 p.2 p.1.2 * (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2
        ∂((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume)) =
      ∫ τ : Fin m → ℝ,
        osiiA0_timeShellScalarFromCoordinateRepresentative H fLeft κ τ *
          φ τ := by
  simpa [osiiA0_timeShellScalarFromCoordinateRepresentative] using
    osiiA0_partialFubini_scalar_timeShell
      (μ := (volume :
        Measure (NPointDomain d n × Section43SpatialSpace d m)))
      (ν := (volume : Measure (Fin m → ℝ)))
      (K := fun e τ => H e.1 τ e.2)
      (a := fun e => fLeft.osConj e.1 * κ.1 e.2)
      (φ := fun τ => φ τ)
      hint

/-- The right-block measurable coordinate chart used in OS II Section 4.3. -/
noncomputable def osiiA0_rightTimeSpatialMeasurableEquiv
    (d m : ℕ) [NeZero d] :
    NPointDomain d m ≃ᵐ (Fin m → ℝ) × Section43SpatialSpace d m :=
  (section43DiffCoordRealMeasurableEquiv d m).trans
    (section43NPointTimeSpatialMeasurableEquiv d m)

/-- The right-block Section 4.3 coordinate chart preserves Lebesgue measure. -/
theorem osiiA0_rightTimeSpatialMeasurableEquiv_measurePreserving
    (d m : ℕ) [NeZero d] :
    MeasurePreserving
      (osiiA0_rightTimeSpatialMeasurableEquiv d m)
      (volume : Measure (NPointDomain d m))
      (volume : Measure ((Fin m → ℝ) × Section43SpatialSpace d m)) := by
  exact
    (section43DiffCoordRealCLE_measurePreserving d m).trans
      (section43NPointTimeSpatialCLE_measurePreserving d m)

/-- The inverse right-block chart is the concrete reconstruction used by the
integrand. -/
theorem osiiA0_rightTimeSpatialMeasurableEquiv_symm_apply
    {m : ℕ} (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    (osiiA0_rightTimeSpatialMeasurableEquiv d m).symm (τ, η) =
      osiiA0_rightFromTimeSpatial d m τ η := by
  have hts :
      (section43NPointTimeSpatialMeasurableEquiv d m).symm (τ, η) =
        (nPointTimeSpatialCLE (d := d) m).symm (τ, η) := by
    ext k μ
    refine Fin.cases ?_ ?_ μ
    · simp [nPointTimeSpatialCLE]
    · intro j
      simpa [nPointTimeSpatialCLE, EuclideanSpace.equiv] using
        section43NPointTimeSpatialMeasurableEquiv_symm_apply_spatial
          d m (τ, η) (k, j)
  change
    (section43DiffCoordRealMeasurableEquiv d m).symm
        ((section43NPointTimeSpatialMeasurableEquiv d m).symm (τ, η)) =
      osiiA0_rightFromTimeSpatial d m τ η
  rw [hts]
  simp [osiiA0_rightFromTimeSpatial, section43DiffCoordRealMeasurableEquiv]

/-- Full product/time-spatial coordinate chart for the OS-II A0 pairing. -/
noncomputable def osiiA0_fullProductTimeSpatialMeasurableEquiv
    (d n m : ℕ) [NeZero d] :
    NPointDomain d (n + m) ≃ᵐ
      (NPointDomain d n × Section43SpatialSpace d m) × (Fin m → ℝ) :=
  (MeasurableEquiv.finAddProd n m (SpacetimeDim d)).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (NPointDomain d n))
      ((osiiA0_rightTimeSpatialMeasurableEquiv d m).trans
        (MeasurableEquiv.prodComm))).trans
      (MeasurableEquiv.prodAssoc
        (α := NPointDomain d n)
        (β := Section43SpatialSpace d m)
        (γ := Fin m → ℝ)).symm)

/-- The full product/time-spatial chart preserves the product Lebesgue measure
used by the scalar time-shell Fubini theorem. -/
theorem osiiA0_fullProductTimeSpatialMeasurableEquiv_measurePreserving
    (d n m : ℕ) [NeZero d] :
    MeasurePreserving
      (osiiA0_fullProductTimeSpatialMeasurableEquiv d n m)
      (volume : Measure (NPointDomain d (n + m)))
      ((volume : Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
        (volume : Measure (Fin m → ℝ))) := by
  let eSplit := MeasurableEquiv.finAddProd n m (SpacetimeDim d)
  let eRight := osiiA0_rightTimeSpatialMeasurableEquiv d m
  have hsplit :
      MeasurePreserving eSplit
        (volume : Measure (NPointDomain d (n + m)))
        ((volume : Measure (NPointDomain d n)).prod
          (volume : Measure (NPointDomain d m))) := by
    simpa [eSplit, NPointDomain] using
      (MeasureTheory.volume_preserving_finAddProd n m (SpacetimeDim d))
  have hright :
      MeasurePreserving eRight
        (volume : Measure (NPointDomain d m))
        (volume : Measure ((Fin m → ℝ) × Section43SpatialSpace d m)) :=
    osiiA0_rightTimeSpatialMeasurableEquiv_measurePreserving d m
  have hswap :
      MeasurePreserving
        (MeasurableEquiv.prodComm :
          (Fin m → ℝ) × Section43SpatialSpace d m ≃ᵐ
            Section43SpatialSpace d m × (Fin m → ℝ))
        (volume : Measure ((Fin m → ℝ) × Section43SpatialSpace d m))
        ((volume : Measure (Section43SpatialSpace d m)).prod
          (volume : Measure (Fin m → ℝ))) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure (Fin m → ℝ)))
        (ν := (volume : Measure (Section43SpatialSpace d m))))
  have hrightSwap :
      MeasurePreserving (eRight.trans MeasurableEquiv.prodComm)
        (volume : Measure (NPointDomain d m))
        ((volume : Measure (Section43SpatialSpace d m)).prod
          (volume : Measure (Fin m → ℝ))) :=
    hright.trans hswap
  have hprod :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (NPointDomain d n))
          (eRight.trans MeasurableEquiv.prodComm))
        ((volume : Measure (NPointDomain d n)).prod
          (volume : Measure (NPointDomain d m)))
        ((volume : Measure (NPointDomain d n)).prod
          ((volume : Measure (Section43SpatialSpace d m)).prod
            (volume : Measure (Fin m → ℝ)))) := by
    simpa using
      (MeasurePreserving.prod
        (MeasurePreserving.id (volume : Measure (NPointDomain d n)))
        hrightSwap)
  have hassoc :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc
          (α := NPointDomain d n)
          (β := Section43SpatialSpace d m)
          (γ := Fin m → ℝ)).symm
        ((volume : Measure (NPointDomain d n)).prod
          ((volume : Measure (Section43SpatialSpace d m)).prod
            (volume : Measure (Fin m → ℝ))))
        (((volume : Measure (NPointDomain d n)).prod
            (volume : Measure (Section43SpatialSpace d m))).prod
          (volume : Measure (Fin m → ℝ))) := by
    exact
      (measurePreserving_prodAssoc
        (volume : Measure (NPointDomain d n))
        (volume : Measure (Section43SpatialSpace d m))
        (volume : Measure (Fin m → ℝ))).symm
          (MeasurableEquiv.prodAssoc
            (α := NPointDomain d n)
            (β := Section43SpatialSpace d m)
            (γ := Fin m → ℝ))
  simpa [osiiA0_fullProductTimeSpatialMeasurableEquiv, eSplit, eRight] using
    hsplit.trans (hprod.trans hassoc)

/-- The inverse full chart is `Fin.append left (rightFromTimeSpatial time spatial)`. -/
theorem osiiA0_fullProductTimeSpatialMeasurableEquiv_symm_apply
    {n m : ℕ} (xL : NPointDomain d n)
    (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    (osiiA0_fullProductTimeSpatialMeasurableEquiv d n m).symm
        ((xL, η), τ) =
      Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η) := by
  change
    (MeasurableEquiv.finAddProd n m (SpacetimeDim d)).symm
      (xL,
        ((osiiA0_rightTimeSpatialMeasurableEquiv d m).trans
          (MeasurableEquiv.prodComm)).symm (η, τ)) =
      Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)
  rw [MeasurableEquiv.finAddProd_symm_apply]
  change
    Fin.append xL
      ((osiiA0_rightTimeSpatialMeasurableEquiv d m).symm (τ, η)) =
    Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)
  rw [osiiA0_rightTimeSpatialMeasurableEquiv_symm_apply]

/-- Pointwise full two-block tensor integrand after the right block has been
written in Section 4.3 time/spatial coordinates. -/
theorem osiiA0_fullIntegrand_rightFromTimeSpatial_eq
    {n m : ℕ}
    (H_full : NPointDomain d (n + m) → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (xL : NPointDomain d n)
    (τ : Fin m → ℝ) (η : Section43SpatialSpace d m) :
    H_full (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)) *
        (fLeft.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))
            (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)) =
      H_full (Fin.append xL (osiiA0_rightFromTimeSpatial d m τ η)) *
        (fLeft.osConj xL * κ.1 η) * φ τ := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    osiiA0_rightFromTimeSpatial]
  ring

/-- Full A0 pairing transported to the product/time-shell measure surface. -/
theorem osiiA0_fullCoordinateChange_to_productTimeShell
    {n m : ℕ}
    (H_full : NPointDomain d (n + m) → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    (∫ x : NPointDomain d (n + m),
        H_full x *
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x) =
      ∫ p : (NPointDomain d n × Section43SpatialSpace d m) ×
          (Fin m → ℝ),
        H_full
            (Fin.append p.1.1
              (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
          (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2
        ∂((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume) := by
  let e := osiiA0_fullProductTimeSpatialMeasurableEquiv d n m
  let Φ : NPointDomain d (n + m) → ℂ := fun x =>
    H_full x *
      (fLeft.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x
  have hmp :
      MeasurePreserving e
        (volume : Measure (NPointDomain d (n + m)))
        ((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            (volume : Measure (Fin m → ℝ))) :=
    osiiA0_fullProductTimeSpatialMeasurableEquiv_measurePreserving d n m
  calc
    (∫ x : NPointDomain d (n + m),
        H_full x *
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x)
        =
      ∫ p : (NPointDomain d n × Section43SpatialSpace d m) ×
          (Fin m → ℝ),
        Φ (e.symm p)
        ∂((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume) := by
          simpa [Φ] using (hmp.symm.integral_comp' (g := Φ)).symm
    _ =
      ∫ p : (NPointDomain d n × Section43SpatialSpace d m) ×
          (Fin m → ℝ),
        H_full
            (Fin.append p.1.1
              (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
          (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2
        ∂((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume) := by
        apply integral_congr_ae
        filter_upwards with p
        rcases p with ⟨⟨xL, η⟩, τ⟩
        change
          Φ (e.symm ((xL, η), τ)) =
            H_full
                (Fin.append xL
                  (osiiA0_rightFromTimeSpatial d m τ η)) *
              (fLeft.osConj xL * κ.1 η) * φ τ
        rw [osiiA0_fullProductTimeSpatialMeasurableEquiv_symm_apply]
        dsimp [Φ]
        exact
          osiiA0_fullIntegrand_rightFromTimeSpatial_eq
            (d := d) H_full fLeft κ φ xL τ η

/-- Full-carrier continuity and support give the product-coordinate integrability
needed by the A0 time-shell Fubini bridge.

This is the analytic bookkeeping in OS-II V.2: once the full local A0
representative is continuous on the carrier containing the fixed tensor current,
the measure-preserving Section 4.3 coordinate change preserves integrability of
the full compactly supported integrand. -/
theorem osiiA0_productTimeShell_integrable_of_full_supportsInOpen
    {n m : ℕ}
    (H_full : NPointDomain d (n + m) → ℂ)
    (V : Set (NPointDomain d (n + m)))
    (hV_open : IsOpen V)
    (hH_cont : ContinuousOn H_full V)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hsupport :
      SCV.SupportsInOpen
        ((fLeft.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ) :
            SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ) V) :
    Integrable
      (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
          (Fin m → ℝ) =>
        H_full
            (Fin.append p.1.1
              (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
          (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
      ((volume :
        Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
          volume) := by
  let e := osiiA0_fullProductTimeSpatialMeasurableEquiv d n m
  let Φ : NPointDomain d (n + m) → ℂ := fun x =>
    H_full x *
      (fLeft.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x
  have hΦ_int : Integrable Φ := by
    exact
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        hV_open hH_cont hsupport
  have hmp :
      MeasurePreserving e
        (volume : Measure (NPointDomain d (n + m)))
        ((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            (volume : Measure (Fin m → ℝ))) :=
    osiiA0_fullProductTimeSpatialMeasurableEquiv_measurePreserving d n m
  have hcomp :
      Integrable
        (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
            (Fin m → ℝ) => Φ (e.symm p))
        ((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            (volume : Measure (Fin m → ℝ))) := by
    simpa [e] using hmp.symm.integrable_comp_of_integrable hΦ_int
  exact hcomp.congr (by
    filter_upwards with p
    rcases p with ⟨⟨xL, η⟩, τ⟩
    change
      Φ (e.symm ((xL, η), τ)) =
        H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)) *
          (fLeft.osConj xL * κ.1 η) * φ τ
    rw [osiiA0_fullProductTimeSpatialMeasurableEquiv_symm_apply]
    dsimp [Φ]
    exact
      osiiA0_fullIntegrand_rightFromTimeSpatial_eq
        (d := d) H_full fLeft κ φ xL τ η)

/-- The full A0 pairing equals the scalar time-shell pairing once the
product-coordinate integrand is integrable. -/
theorem osiiA0_fullA0_timeShellScalar_identity_of_product_integrable
    {n m : ℕ}
    (H_full : NPointDomain d (n + m) → ℂ)
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hint :
      Integrable
        (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
            (Fin m → ℝ) =>
          H_full
              (Fin.append p.1.1
                (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
            (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
        ((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume)) :
    (∫ x : NPointDomain d (n + m),
        H_full x *
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x) =
      ∫ τ : Fin m → ℝ,
        osiiA0_timeShellScalarFromCoordinateRepresentative
          (fun xL τ η =>
            H_full
              (Fin.append xL
                (osiiA0_rightFromTimeSpatial d m τ η)))
          fLeft κ τ * φ τ := by
  calc
    (∫ x : NPointDomain d (n + m),
        H_full x *
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x)
        =
      ∫ p : (NPointDomain d n × Section43SpatialSpace d m) ×
          (Fin m → ℝ),
        H_full
            (Fin.append p.1.1
              (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
          (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2
        ∂((volume :
          Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
            volume) :=
          osiiA0_fullCoordinateChange_to_productTimeShell
            (d := d) H_full fLeft κ φ
    _ =
      ∫ τ : Fin m → ℝ,
        osiiA0_timeShellScalarFromCoordinateRepresentative
          (fun xL τ η =>
            H_full
              (Fin.append xL
                (osiiA0_rightFromTimeSpatial d m τ η)))
          fLeft κ τ * φ τ := by
        simpa using
          osiiA0_section43_partialFubini_timeShellScalar
            (d := d)
            (H := fun xL τ η =>
              H_full
                (Fin.append xL
                  (osiiA0_rightFromTimeSpatial d m τ η)))
            fLeft κ φ hint

/-- A full local coordinate-space representative for the cutoff Schwinger
distribution induces the right-time-shell representative after the fixed left
source and right spatial source are inserted.

This is the OS-II V.1 to V.2 transport step after the coordinate change above:
the full local A0 representative is evaluated on the concrete two-block test,
the pairing is rewritten in Section 4.3 product/time-shell coordinates, and
partial Fubini gives the scalar time-shell distribution. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (V : Set (NPointDomain d (n + m)))
    (U : Set (Fin m → ℝ))
    (hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V)
    (hsupport :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          SCV.SupportsInOpen
            ((fLeft.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ) :
                SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ) V)
    (hint :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          Integrable
            (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
                (Fin m → ℝ) =>
              H_full
                  (Fin.append p.1.1
                    (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
                (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
            ((volume :
              Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
                volume)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  intro φ hφ
  have hΦ_support := hsupport φ hφ
  have hfull_φ :=
    hfull
      (fLeft.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))
      hΦ_support
  calc
    osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ φ
        =
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
        (fLeft.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) := by
        rfl
    _ =
      ∫ x : NPointDomain d (n + m),
        H_full x *
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) x :=
        hfull_φ
    _ =
      ∫ τ : Fin m → ℝ,
        osiiA0_timeShellScalarFromCoordinateRepresentative
          (fun xL τ η =>
            H_full
              (Fin.append xL
                (osiiA0_rightFromTimeSpatial d m τ η)))
          fLeft κ τ * φ τ :=
        osiiA0_fullA0_timeShellScalar_identity_of_product_integrable
      (d := d) H_full fLeft κ φ (hint φ hφ)

/-- Concrete right-time-cylinder version of the OS-II V.1 to V.2 transport.

The abstract support hypothesis in
`osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep` is
discharged by the ordered-pullback support theorem: a time test supported in
`U` produces a full two-block current supported exactly over the corresponding
right-time cylinder. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U })
    (hint :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          Integrable
            (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
                (Fin m → ℝ) =>
              H_full
                  (Fin.append p.1.1
                    (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
                (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
            ((volume :
              Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
                volume)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep
      (d := d) OS χ hχ_disj fLeft κ H_full
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }
      U hfull
      (fun φ hφ =>
        osiiA0_osConjTensorProduct_orderedPullback_supportsInOpen_rightTimeCylinder
          (d := d) fLeft hfLeft_comp κ φ U hφ)
      hint

/-- The natural full right-time cylinder over an open time carrier is open. -/
theorem isOpen_osiiA0_rightTimeCylinder
    {n m : ℕ}
    {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) :
    IsOpen
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U } := by
  have htime_cont :
      Continuous fun y : NPointDomain d m =>
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m y) := by
    have hq_cont :
        Continuous (section43QTime (d := d) (n := m)) := by
      simpa [section43QTimeCLM_apply] using
        (section43QTimeCLM d m).continuous
    exact
      hq_cont.comp
        (section43DiffCoordRealCLE d m).continuous
  exact hU.preimage
    (htime_cont.comp (splitLast_continuousLinear n m))

private theorem continuousOn_of_local_continuousOn_open
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {H : E → F} {V : Set E}
    (hlocal :
      ∀ x ∈ V, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ContinuousOn H U) :
    ContinuousOn H V := by
  intro x hx
  rcases hlocal x hx with ⟨U, hU_open, hxU, hH_U⟩
  have hH_at : ContinuousAt H x :=
    (hH_U x hxU).continuousAt (hU_open.mem_nhds hxU)
  exact hH_at.continuousWithinAt

/-- Right-time-cylinder transport with the Fubini integrability discharged from
full-carrier continuity.

This is the directly usable OS-II `(A0)` time-shell bridge once the local
coordinate representative is continuous on the cylinder and represents the
cutoff Schwinger distribution there. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder_of_continuousOn
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hH_cont :
      ContinuousOn H_full
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U })
    (hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ H_full U hfull
      (fun φ hφ =>
        osiiA0_productTimeShell_integrable_of_full_supportsInOpen
          (d := d) H_full
          { x : NPointDomain d (n + m) |
            section43QTime (d := d) (n := m)
              (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }
          (isOpen_osiiA0_rightTimeCylinder (d := d) (n := n) (m := m) hU_open)
          hH_cont fLeft κ φ
          (osiiA0_osConjTensorProduct_orderedPullback_supportsInOpen_rightTimeCylinder
            (d := d) fLeft hfLeft_comp κ φ U hφ))

/-- Pointwise local A0 representatives on every point of an open carrier
assemble to one `RepresentsDistributionOn` statement on that carrier.  This is
the partition-of-unity bridge between OS-II Lemma 5.1 local polydiscs and the
open-carrier representative consumed by the time-shell theorem above. -/
theorem osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_pointwise_local_reps
    {n : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ))
        (CoincidenceLocus d n))
    (H_full : NPointDomain d n → ℂ)
    (V : Set (NPointDomain d n))
    (hlocal :
      ∀ x ∈ V,
        ∃ U : Set (NPointDomain d n), IsOpen U ∧ x ∈ U ∧
          ContinuousOn H_full U ∧
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full U) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V := by
  intro φ hφ
  exact
    SCV.distribution_representation_of_local_representations_for_test
      (T := osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj)
      (H := H_full)
      (φ := φ)
      hφ.1
      (by
        intro x hx
        exact hlocal x (hφ.2 hx))

/-- A cutoff Schwinger distribution only requires local representatives on the
cutoff support.  Away from `tsupport chi`, the localized distribution is zero;
if the chosen representative also vanishes there, the zero neighborhood supplies
the missing local representation.

This is the support-local form of the OS-II `(A0)` local-representative
assembly: Lemma 5.1/Malgrange-Zerner has to be applied only on the cutoff
support, not on the whole ambient carrier. -/
theorem osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_tsupport_local_reps
    {n : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ))
        (CoincidenceLocus d n))
    (H_full : NPointDomain d n → ℂ)
    (V : Set (NPointDomain d n))
    (hH_zero_off :
      ∀ x : NPointDomain d n,
        x ∉ tsupport (χ : NPointDomain d n → ℂ) → H_full x = 0)
    (hlocal :
      ∀ x ∈ V,
        x ∈ tsupport (χ : NPointDomain d n → ℂ) →
          ∃ Ux : Set (NPointDomain d n), IsOpen Ux ∧ x ∈ Ux ∧
            ContinuousOn H_full Ux ∧
              SCV.RepresentsDistributionOn
                (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V := by
  intro φ hφ
  refine
    SCV.distribution_representation_of_local_representations_for_test
      (T := osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj)
      (H := H_full)
      (φ := φ)
      hφ.1 ?_
  intro x hxφ
  have hxV : x ∈ V := hφ.2 hxφ
  by_cases hxχ : x ∈ tsupport (χ : NPointDomain d n → ℂ)
  · exact hlocal x hxV hxχ
  · let Ux : Set (NPointDomain d n) :=
      (tsupport (χ : NPointDomain d n → ℂ))ᶜ
    have hUx_open : IsOpen Ux :=
      (isClosed_tsupport (χ : NPointDomain d n → ℂ)).isOpen_compl
    have hxUx : x ∈ Ux := hxχ
    have hH_cont : ContinuousOn H_full Ux := by
      refine
        (continuousOn_const :
          ContinuousOn (fun _ : NPointDomain d n => (0 : ℂ)) Ux).congr ?_
      intro y hy
      exact hH_zero_off y hy
    have hrep_Ux :
        SCV.RepresentsDistributionOn
          (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux := by
      intro ψ hψ
      have hsmul_zero :
          SchwartzMap.smulLeftCLM ℂ (χ : NPointDomain d n → ℂ) ψ = 0 := by
        ext y
        rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
        by_cases hyψ : y ∈ tsupport (ψ : NPointDomain d n → ℂ)
        · have hy_notχ : y ∉ tsupport (χ : NPointDomain d n → ℂ) := hψ.2 hyψ
          have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport hy_notχ
          simp [smul_eq_mul, hχy]
        · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hyψ
          simp [smul_eq_mul, hψy]
      have hzeroCLM :
          osiiA0LocalCutoffZeroCLM χ hχ_disj ψ = 0 := by
        apply SetCoe.ext
        simpa [osiiA0LocalCutoffZeroCLM_coe] using hsmul_zero
      have hT_zero :
          osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj ψ = 0 := by
        change OS.S n (osiiA0LocalCutoffZeroCLM χ hχ_disj ψ) = 0
        rw [hzeroCLM]
        simpa [OsterwalderSchraderAxioms.schwingerCLM] using
          (OS.E0_linear n).map_zero
      have hintegral_zero :
          (∫ y : NPointDomain d n, H_full y * ψ y) = 0 := by
        rw [← integral_zero (α := NPointDomain d n) (G := ℂ) (μ := volume)]
        refine integral_congr_ae ?_
        filter_upwards with y
        by_cases hyψ : y ∈ tsupport (ψ : NPointDomain d n → ℂ)
        · have hy_notχ : y ∉ tsupport (χ : NPointDomain d n → ℂ) := hψ.2 hyψ
          simp [hH_zero_off y hy_notχ]
        · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hyψ
          simp [hψy]
      exact hT_zero.trans hintegral_zero.symm
    exact ⟨Ux, hUx_open, hxUx, hH_cont, hrep_Ux⟩

/-- Fully local OS-II V.1 to V.2 transport: pointwise Lemma 5.1 local
representatives on the full A0 carrier assemble to the represented
right-time-shell distribution, provided the concrete tensor tests stay in the
carrier and the local representative gives the product-coordinate
integrability. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_pointwise_full_local_rep
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (V : Set (NPointDomain d (n + m)))
    (U : Set (Fin m → ℝ))
    (hlocal :
      ∀ x ∈ V,
        ∃ Ux : Set (NPointDomain d (n + m)), IsOpen Ux ∧ x ∈ Ux ∧
          ContinuousOn H_full Ux ∧
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux)
    (hsupport :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          SCV.SupportsInOpen
            ((fLeft.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ) :
                SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ) V)
    (hint :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          Integrable
            (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
                (Fin m → ℝ) =>
              H_full
                  (Fin.append p.1.1
                    (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
                (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
            ((volume :
              Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
                volume)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  have hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V :=
    osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_pointwise_local_reps
      (d := d) OS χ hχ_disj H_full V hlocal
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep
      (d := d) OS χ hχ_disj fLeft κ H_full V U hfull hsupport hint

/-- Fully local OS-II V.1 to V.2 transport on the natural right-time
cylinder.

This is the form that plugs Lemma 5.1 local full-coordinate representatives
directly into the time-shell distribution: pointwise local representatives are
only required over the cylinder determined by the right time support `U`, and
the support of every concrete ordered-pullback current is supplied by
`osiiA0_osConjTensorProduct_orderedPullback_supportsInOpen_rightTimeCylinder`. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_pointwise_full_local_rep_rightTimeCylinder
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hlocal :
      ∀ x ∈
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U },
        ∃ Ux : Set (NPointDomain d (n + m)), IsOpen Ux ∧ x ∈ Ux ∧
          ContinuousOn H_full Ux ∧
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux)
    (hint :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U →
          Integrable
            (fun p : (NPointDomain d n × Section43SpatialSpace d m) ×
                (Fin m → ℝ) =>
              H_full
                  (Fin.append p.1.1
                    (osiiA0_rightFromTimeSpatial d m p.2 p.1.2)) *
                (fLeft.osConj p.1.1 * κ.1 p.1.2) * φ p.2)
            ((volume :
              Measure (NPointDomain d n × Section43SpatialSpace d m)).prod
                volume)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  have hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U } :=
    osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_pointwise_local_reps
      (d := d) OS χ hχ_disj H_full
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }
      hlocal
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ H_full U hfull hint

/-- Pointwise local A0 representatives on the right-time cylinder give the
represented time-shell distribution, with support, openness, and Fubini
integrability all discharged.

This is the cleaned OS-II `(A0)` handoff for the next producer: Lemma
5.1/Malgrange-Zerner only has to supply local continuity and local
`RepresentsDistributionOn` around every point of the cylinder. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_pointwise_full_local_rep_rightTimeCylinder_open
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hlocal :
      ∀ x ∈
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U },
        ∃ Ux : Set (NPointDomain d (n + m)), IsOpen Ux ∧ x ∈ Ux ∧
          ContinuousOn H_full Ux ∧
            SCV.RepresentsDistributionOn
              (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  let V : Set (NPointDomain d (n + m)) :=
    { x : NPointDomain d (n + m) |
      section43QTime (d := d) (n := m)
        (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }
  have hH_cont : ContinuousOn H_full V := by
    apply continuousOn_of_local_continuousOn_open
    intro x hx
    rcases hlocal x hx with ⟨Ux, hUx_open, hxUx, hH_Ux, _hrep_Ux⟩
    exact ⟨Ux, hUx_open, hxUx, hH_Ux⟩
  have hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V :=
    osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_pointwise_local_reps
      (d := d) OS χ hχ_disj H_full V hlocal
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder_of_continuousOn
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ H_full U hU_open
      hH_cont hfull

/-- Cutoff-support-local version of the right-time-cylinder A0 handoff.

The local Lemma 5.1/MZ representative is only needed where the cutoff actually
lives.  Outside `tsupport chi`, the representative is assumed to vanish and the
localized Schwinger distribution is zero by construction. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_full_local_rep_rightTimeCylinder_open
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (H_full : NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hH_zero_off :
      ∀ x : NPointDomain d (n + m),
        x ∉ tsupport (χ : NPointDomain d (n + m) → ℂ) → H_full x = 0)
    (hlocal :
      ∀ x ∈
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U },
        x ∈ tsupport (χ : NPointDomain d (n + m) → ℂ) →
          ∃ Ux : Set (NPointDomain d (n + m)), IsOpen Ux ∧ x ∈ Ux ∧
            ContinuousOn H_full Ux ∧
              SCV.RepresentsDistributionOn
                (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          H_full
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  let V : Set (NPointDomain d (n + m)) :=
    { x : NPointDomain d (n + m) |
      section43QTime (d := d) (n := m)
        (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U }
  have hH_cont : ContinuousOn H_full V := by
    apply continuousOn_of_local_continuousOn_open
    intro x hxV
    by_cases hxχ : x ∈ tsupport (χ : NPointDomain d (n + m) → ℂ)
    · rcases hlocal x hxV hxχ with ⟨Ux, hUx_open, hxUx, hH_Ux, _hrep_Ux⟩
      exact ⟨Ux, hUx_open, hxUx, hH_Ux⟩
    · let Ux : Set (NPointDomain d (n + m)) :=
        (tsupport (χ : NPointDomain d (n + m) → ℂ))ᶜ
      have hUx_open : IsOpen Ux :=
        (isClosed_tsupport (χ : NPointDomain d (n + m) → ℂ)).isOpen_compl
      have hxUx : x ∈ Ux := hxχ
      have hH_Ux : ContinuousOn H_full Ux := by
        refine
          (continuousOn_const :
            ContinuousOn (fun _ : NPointDomain d (n + m) => (0 : ℂ)) Ux).congr ?_
        intro y hy
        exact hH_zero_off y hy
      exact ⟨Ux, hUx_open, hxUx, hH_Ux⟩
  have hfull :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full V :=
    osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_tsupport_local_reps
      (d := d) OS χ hχ_disj H_full V hH_zero_off hlocal
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder_of_continuousOn
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ H_full U hU_open
      hH_cont hfull

/-- Branch-family form of the cutoff-support-local right-time-cylinder A0
handoff.

This is the distributional Malgrange-Zerner gluing step in the exact shape used
by OS-II `(A0)`: local branches that represent the cutoff Schwinger
distribution and agree on overlaps define a glued full-coordinate
representative, which then feeds the time-shell transport theorem above.  The
remaining OS-specific leaf is to prove the branch representation hypotheses
from the semigroup construction. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_full_local_reps_rightTimeCylinder_open
    {n m : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (N : ι → Set (NPointDomain d (n + m)))
    (D : ι → NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hH_zero_off :
      ∀ x : NPointDomain d (n + m),
        x ∉ tsupport (χ : NPointDomain d (n + m) → ℂ) →
          SCV.glued_iUnion N D x = 0)
    (hcover :
      ∀ x ∈
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U },
        x ∈ tsupport (χ : NPointDomain d (n + m) → ℂ) →
          x ∈ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD_cont : ∀ i, ContinuousOn (D i) (N i))
    (hD_rep : ∀ i,
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  exact
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_full_local_rep_rightTimeCylinder_open
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ
      (SCV.glued_iUnion N D) U hU_open hH_zero_off
      (by
        intro x hxV hxχ
        rcases Set.mem_iUnion.mp (hcover x hxV hxχ) with ⟨i, hxi⟩
        refine ⟨N i, hN_open i, hxi, ?_, ?_⟩
        · exact (hD_cont i).congr fun y hy =>
            SCV.glued_iUnion_eqOn (N := N) (D := D) hEq i hy
        · exact
            SCV.representsDistributionOn_glued_iUnion
              (T := osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj)
              (N := N) (D := D) (U := N i)
              (by
                intro y hy
                exact Set.mem_iUnion.2 ⟨i, hy⟩)
              hN_open hD_cont hD_rep hEq)

/-- Local-cutoff branch-family form of the cutoff-support-local
right-time-cylinder A0 handoff.

This version is the same gluing/time-shell transport as
`osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_full_local_reps_rightTimeCylinder_open`,
but each local branch may first be represented using a local cutoff `χloc i`
that agrees with the global cutoff `χ` on the corresponding carrier `N i`.
The cutoff agreement transports each local distributional representative to the
global cutoff before the genuine Malgrange-Zerner gluing step is applied. -/
theorem osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_local_cutoff_reps_rightTimeCylinder_open
    {n m : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (χloc : ι → SchwartzNPoint d (n + m))
    (hχloc_disj : ∀ i : ι,
      Disjoint (tsupport (χloc i : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (hfLeft_comp : HasCompactSupport (fLeft : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (N : ι → Set (NPointDomain d (n + m)))
    (D : ι → NPointDomain d (n + m) → ℂ)
    (U : Set (Fin m → ℝ))
    (hU_open : IsOpen U)
    (hH_zero_off :
      ∀ x : NPointDomain d (n + m),
        x ∉ tsupport (χ : NPointDomain d (n + m) → ℂ) →
          SCV.glued_iUnion N D x = 0)
    (hcover :
      ∀ x ∈
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U },
        x ∈ tsupport (χ : NPointDomain d (n + m) → ℂ) →
          x ∈ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD_cont : ∀ i, ContinuousOn (D i) (N i))
    (hχ_eq : ∀ i : ι,
      Set.EqOn (χloc i : NPointDomain d (n + m) → ℂ)
        (χ : NPointDomain d (n + m) → ℂ) (N i))
    (hD_rep_local : ∀ i,
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS (χloc i) (hχloc_disj i))
        (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      (osiiA0_timeShellScalarFromCoordinateRepresentative
        (fun xL τ η =>
          SCV.glued_iUnion N D
            (Fin.append xL
              (osiiA0_rightFromTimeSpatial d m τ η)))
        fLeft κ)
      U := by
  refine
    osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_full_local_reps_rightTimeCylinder_open
      (d := d) OS χ hχ_disj fLeft hfLeft_comp κ N D U hU_open
      hH_zero_off hcover hN_open hD_cont ?_ hEq
  intro i
  exact
    osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_cutoff_eqOn
      (d := d) OS (χloc i) χ (hχloc_disj i) hχ_disj (D i) (N i)
      (hχ_eq i) (hD_rep_local i)

end OSReconstruction
