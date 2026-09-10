/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneSidedTaylorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge












noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Family form of the cutoff-data Hilbert real-edge theorem. A common scalar
edge, cutoff germ, source-translation germ, norm identity, and Cauchy radius
produce one real neighborhood on which every field in the family is the
honest translated positive-time vector. -/
theorem eventually_holomorphicField_eq_localPositiveTimeParameterTranslate_family_of_cutoffData
    {d n q : ℕ} [NeZero d]
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin (q + 1) → NPointDomain d n)
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (R : ℝ)
    (hR : 0 < R)
    (hradius : ∀ a, (D a).radius = R)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU :
      ∀ a,
        SCV.closedPolydisc (D a).center (fun _ => (D a).radius) ⊆ U)
    (hscalar : ∀ a, DifferentiableOn ℂ (D a).scalar U)
    (hreal :
      ∀ᶠ x : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice (D a).scalar (D a).center x =
            OS.S (n + n)
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM directions x)
                  ((f a).1.osConjTensorProduct (f a).1))))
    (Ψ : ι → (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      ∀ a,
        TendstoLocallyUniformlyOn
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            (f a) directions).partialSum OS)
          (Ψ a) atTop
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius)))
    (χ : NPointDomain d (n + n) → ℂ)
    (T : SchwartzNPoint d (n + n) →L[ℂ] ℂ)
    (hlocal_one :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a y, y ∈ tsupport
          ((translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions u)
            ((f a).1.osConjTensorProduct (f a).1) :
              SchwartzNPoint d (n + n)) :
                NPointDomain d (n + n) → ℂ) →
          χ y = 1)
    (hlocal_eval :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions u)
            ((f a).1.osConjTensorProduct (f a).1)) =
            OS.S (n + n)
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM directions u)
                  ((f a).1.osConjTensorProduct (f a).1))))
    (hsource :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ∀ a,
          (localPositiveTimeParameterTranslate (f a) directions x).1 =
            translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) (f a).1)
    (hnorm :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ∀ a,
          ‖Ψ a (fun i => (x i : ℂ))‖ ^ 2 =
            ‖osiiPositiveTimeSingleVectorCLM OS n
              (localPositiveTimeParameterTranslate
                (f a) directions x)‖ ^ 2)
    (hhomogeneous :
      ∀ a (g : euclideanPositiveTimeSubmodule (d := d) n)
        (_hχ_one :
          ∀ y ∈ tsupport
            (((g.1.osConjTensorProduct (f a).1 :
              SchwartzNPoint d (n + n)) :
                NPointDomain d (n + n) → ℂ)),
            χ y = 1)
        (_hgf_disj :
          Disjoint
            (tsupport
              (((g.1.osConjTensorProduct (f a).1 :
                SchwartzNPoint d (n + n)) :
                  NPointDomain d (n + n) → ℂ)))
            (CoincidenceLocus d (n + n)))
        (z : Fin (q + 1) → ℂ) (p : ℕ),
        T (g.1.osConjTensorProduct
            ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
              (f a) directions).homogeneousSource z p).1) =
          OS.S (n + n)
            (ZeroDiagonalSchwartz.ofClassical
              (g.1.osConjTensorProduct
                ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
                  (f a) directions).homogeneousSource z p).1))) :
    ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
      ∀ a,
        Ψ a (fun i => (x i : ℂ)) =
          osiiPositiveTimeSingleVectorCLM OS n
            (localPositiveTimeParameterTranslate
              (f a) directions x) := by
  let m := q + 1
  let φ : ι → SchwartzNPoint d (n + n) :=
    fun a => (f a).1.osConjTensorProduct (f a).1
  let L := reflectedSourceParameterDisplacementCLM directions
  have hlocal' :
      ∀ᶠ u : Fin (m + m) → ℝ in 𝓝 0,
        ∀ a,
          (∀ y ∈ tsupport
              ((translateSchwartzConfiguration (L u) (φ a) :
                SchwartzNPoint d (n + n)) : NPointDomain d (n + n) → ℂ),
              χ y = 1) ∧
            T (translateSchwartzConfiguration (L u) (φ a)) =
              OS.S (n + n)
                (ZeroDiagonalSchwartz.ofClassical
                  (translateSchwartzConfiguration (L u) (φ a))) := by
    filter_upwards [hlocal_one, hlocal_eval] with u huOne huEval
    intro a
    constructor
    · simpa [m, L, φ] using huOne a
    · simpa [m, L, φ] using huEval a
  have hjoint := hreal.and hlocal'
  let appendR :
      ((Fin m → ℝ) × (Fin m → ℝ)) → Fin (m + m) → ℝ :=
    fun p => Fin.append p.1 p.2
  have happend_cont : Continuous appendR := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [appendR, Fin.append_left]
      fun_prop
    · simp only [appendR, Fin.append_right]
      fun_prop
  have happend_zero :
      appendR (0, 0) = (0 : Fin (m + m) → ℝ) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [appendR]
    · change
        Fin.append (0 : Fin m → ℝ) 0 (Fin.natAdd m i) = 0
      rw [Fin.append_right]
      rfl
  have happend_tendsto :
      Tendsto appendR
        (𝓝 ((0 : Fin m → ℝ), (0 : Fin m → ℝ)))
        (𝓝 (0 : Fin (m + m) → ℝ)) := by
    have ht :
        Tendsto appendR
          (𝓝 ((0 : Fin m → ℝ), (0 : Fin m → ℝ)))
          (𝓝 (appendR
            ((0 : Fin m → ℝ), (0 : Fin m → ℝ)))) :=
      happend_cont.continuousAt
    rw [happend_zero] at ht
    exact ht
  have hjoint_prod := happend_tendsto.eventually hjoint
  rw [nhds_prod_eq] at hjoint_prod
  obtain ⟨pl, hpl, pr, hpr, hjoint_lr⟩ :=
    Filter.eventually_prod_iff.mp hjoint_prod
  let leftOnly : (Fin m → ℝ) → Fin (m + m) → ℝ :=
    fun x => Fin.append x 0
  have hleftOnly_cont : Continuous leftOnly := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [leftOnly, Fin.append_left]
      fun_prop
    · simp only [leftOnly, Fin.append_right]
      fun_prop
  have hleftOnly_zero :
      leftOnly 0 = (0 : Fin (m + m) → ℝ) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [leftOnly]
    · change
        Fin.append (0 : Fin m → ℝ) 0 (Fin.natAdd m i) = 0
      rw [Fin.append_right]
      rfl
  have hleftOnly_tendsto :
      Tendsto leftOnly (𝓝 (0 : Fin m → ℝ))
        (𝓝 (0 : Fin (m + m) → ℝ)) := by
    have ht :
        Tendsto leftOnly (𝓝 (0 : Fin m → ℝ))
          (𝓝 (leftOnly (0 : Fin m → ℝ))) :=
      hleftOnly_cont.continuousAt
    rw [hleftOnly_zero] at ht
    exact ht
  have hlocal_left := hleftOnly_tendsto.eventually hlocal'
  let Rc : ℝ := R / 3
  let Rw : ℝ := 2 * R / 3
  have hRc : 0 < Rc := by
    dsimp [Rc]
    linarith
  have hRw : Rc < Rw := by
    dsimp [Rc, Rw]
    linarith
  have hRwR : Rw < R := by
    dsimp [Rw]
    linarith
  let bound : ℝ := Rc / (2 * ((q : ℝ) + 2))
  have hdenom : 0 < 2 * ((q : ℝ) + 2) := by positivity
  have hbound : 0 < bound := div_pos hRc hdenom
  have hboundRc : bound < Rc := by
    dsimp [bound]
    rw [div_lt_iff₀ hdenom]
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith
  have hembed_cont :
      Continuous
        (fun x : Fin m → ℝ => fun i => (x i : ℂ)) := by
    fun_prop
  have hsmall :
      ∀ᶠ x : Fin m → ℝ in 𝓝 0,
        ‖(fun i => (x i : ℂ))‖ < bound := by
    have hball :
        Metric.ball (0 : Fin m → ℂ) bound ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ hbound
    have hevent := hembed_cont.continuousAt.eventually hball
    simpa [Metric.mem_ball, dist_zero_right] using hevent
  have hrightP :
      ∀ᶠ x : Fin m → ℝ in 𝓝 0,
        (fun i => (x i : ℂ)) ∈
          SCV.Polydisc (0 : Fin m → ℂ) (fun _ => Rw) := by
    filter_upwards [hsmall] with x hx
    intro i
    change dist (x i : ℂ) 0 < Rw
    rw [dist_zero_right]
    exact (norm_le_pi_norm (fun i => (x i : ℂ)) i).trans_lt
      (hx.trans (hboundRc.trans hRw))
  filter_upwards [hpl, hpr, hlocal_left, hsource, hnorm, hsmall, hrightP]
      with x hxpl hxpr hxlocalLeft hxsource hxnorm hxsmall hxP
  intro a
  let fa := f a
  let Da := D a
  let Ψa := Ψ a
  let g := localPositiveTimeParameterTranslate fa directions x
  let zx : Fin m → ℂ := fun i => (x i : ℂ)
  let sliceMap : (Fin m → ℂ) → Fin (m + m) → ℂ :=
    fun z => Da.center + Fin.append zx z
  let scalarx : (Fin m → ℂ) → ℂ := fun z => Da.scalar (sliceMap z)
  let Ux : Set (Fin m → ℂ) := sliceMap ⁻¹' U
  have hslice_cont : Continuous sliceMap := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [sliceMap, Pi.add_apply, Fin.append_left]
      fun_prop
    · simp only [sliceMap, Pi.add_apply, Fin.append_right]
      fun_prop
  have hUx : IsOpen Ux := hU.preimage hslice_cont
  have hxcoordRc : ∀ i, ‖zx i‖ < Rc := by
    intro i
    change ‖zx‖ < bound at hxsmall
    exact (norm_le_pi_norm zx i).trans_lt
      (hxsmall.trans hboundRc)
  have hRwDa : Rw < Da.radius := by
    simpa [Da, hradius a] using hRwR
  have hRwUx :
      SCV.closedPolydisc (0 : Fin m → ℂ) (fun _ => Rw) ⊆ Ux := by
    intro z hz
    apply hRU a
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [sliceMap, Pi.add_apply]
      rw [Fin.append_left]
      simpa [Da] using
        (le_of_lt ((hxcoordRc i).trans (hRw.trans hRwDa)))
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [sliceMap, Pi.add_apply]
      rw [Fin.append_right]
      simpa [Da] using
        (hz i).trans (le_of_lt hRwDa)
  have hscalarx : DifferentiableOn ℂ scalarx Ux := by
    apply DifferentiableOn.comp (hscalar a)
    · have hslice_diff : Differentiable ℂ sliceMap := by
        apply differentiable_pi.mpr
        intro j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [sliceMap, Pi.add_apply, Fin.append_left]
          fun_prop
        · simp only [sliceMap, Pi.add_apply, Fin.append_right]
          fun_prop
      exact hslice_diff.differentiableOn
    · intro z hz
      exact hz
  have hΨRw :
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          fa directions).partialSum OS)
        Ψa atTop
        (SCV.Polydisc (0 : Fin m → ℂ) (fun _ => Rw)) := by
    apply (hΨ a).mono
    intro z hz i
    exact (hz i).trans hRwDa
  have hleftDisp :
      L (leftOnly x) =
        Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM directions x))
          (sourceParameterDisplacementCLM directions 0) := by
    change
      Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM directions
              (fun i => leftOnly x (Fin.castAdd m i))))
          (sourceParameterDisplacementCLM directions
            (fun i => leftOnly x (Fin.natAdd m i))) =
        _
    congr 2
    · congr 1
      funext i
      simp [leftOnly]
    · funext i
      change leftOnly x (Fin.natAdd m i) = 0
      rw [show leftOnly x = Fin.append x 0 by rfl, Fin.append_right]
      rfl
  have hχgf :
      ∀ y ∈ tsupport
          (((g.1.osConjTensorProduct fa.1 :
            SchwartzNPoint d (n + n)) :
            NPointDomain d (n + n) → ℂ)),
        χ y = 1 := by
    intro y hy
    apply (hxlocalLeft a).1 y
    have hprod :
        g.1.osConjTensorProduct fa.1 =
          translateSchwartzConfiguration (L (leftOnly x)) (φ a) := by
      have hleftDisp0 :
          L (leftOnly x) =
            Fin.append
              (timeReflectionN d
                (sourceParameterDisplacementCLM directions x)) 0 := by
        simpa using hleftDisp
      calc
        g.1.osConjTensorProduct fa.1 =
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) fa.1
            ).osConjTensorProduct fa.1 := by rw [hxsource a]
        _ =
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) fa.1
            ).osConjTensorProduct
              (translateSchwartzConfiguration 0 fa.1) := by
          congr 1
          ext z
          simp [translateSchwartzConfiguration_apply]
        _ =
            translateSchwartzConfiguration
              (Fin.append
                (timeReflectionN d
                  (sourceParameterDisplacementCLM directions x)) 0)
              (fa.1.osConjTensorProduct fa.1) :=
          osConjTensorProduct_translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) 0 fa.1 fa.1
        _ = translateSchwartzConfiguration (L (leftOnly x)) (φ a) := by
          rw [hleftDisp0]
    rwa [← hprod]
  have hgf_disj :
      Disjoint
        (tsupport
          (((g.1.osConjTensorProduct fa.1 :
            SchwartzNPoint d (n + n)) :
            NPointDomain d (n + n) → ℂ)))
        (CoincidenceLocus d (n + n)) :=
    osiiA0_osConjTensorProduct_tsupport_disjoint_coincidence_of_ordered
      g.1 fa.1 g.2 fa.2
  have hT :
      ∀ z p,
        T (g.1.osConjTensorProduct
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            fa directions).homogeneousSource z p).1) =
        OS.S (n + n)
          (ZeroDiagonalSchwartz.ofClassical
            (g.1.osConjTensorProduct
              ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
                fa directions).homogeneousSource z p).1)) :=
    fun z p => hhomogeneous a g hχgf hgf_disj z p
  have hslice_real :
      ∀ y, pr y →
        scalarx (fun i => (y i : ℂ)) =
          T (g.1.osConjTensorProduct
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions y) fa.1)) := by
    intro y hypr
    have hxy := hjoint_lr hxpl hypr
    have hdisp :
        L (Fin.append x y) =
          Fin.append
            (timeReflectionN d
              (sourceParameterDisplacementCLM directions x))
            (sourceParameterDisplacementCLM directions y) := by
      change
        Fin.append
            (timeReflectionN d
              (sourceParameterDisplacementCLM directions
                (fun i => Fin.append x y (Fin.castAdd m i))))
            (sourceParameterDisplacementCLM directions
              (fun i => Fin.append x y (Fin.natAdd m i))) =
          _
      congr 2
      · congr 1
        funext i
        simp
      · funext i
        exact Fin.append_right x y i
    calc
      scalarx (fun i => (y i : ℂ)) =
          realAffineSlice Da.scalar Da.center (Fin.append x y) := by
        change
          Da.scalar (Da.center + Fin.append zx (fun i => (y i : ℂ))) =
            Da.scalar
              (Da.center +
                realCoordinateEmbeddingCLM (m + m) (Fin.append x y))
        apply congrArg Da.scalar
        congr 1
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zx]
        · rw [realCoordinateEmbeddingCLM_apply]
          rw [Fin.append_right zx (fun i => (y i : ℂ)) i]
          exact_mod_cast (Fin.append_right x y i).symm
      _ = OS.S (n + n)
          (ZeroDiagonalSchwartz.ofClassical
            (translateSchwartzConfiguration
              (L (Fin.append x y)) (φ a))) := (hxy.1 a)
      _ = T (translateSchwartzConfiguration
          (L (Fin.append x y)) (φ a)) := (hxy.2 a).2.symm
      _ = T (g.1.osConjTensorProduct
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions y) fa.1)) := by
        rw [show g.1 =
            translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions x) fa.1 by
          exact hxsource a]
        rw [osConjTensorProduct_translateSchwartzConfiguration]
        rw [← hdisp]
  have hrealx :
      (fun y : Fin m → ℝ =>
        scalarx (fun i => (y i : ℂ))) =ᶠ[𝓝 0]
        (fun y =>
          T (g.1.osConjTensorProduct
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM directions y) fa.1))) :=
    hpr.mono fun y hy => hslice_real y hy
  have hpair :
      @inner ℂ (OSHilbertSpace OS) _
          (osiiPositiveTimeSingleVectorCLM OS n g)
          (Ψa zx) =
        scalarx zx := by
    exact
      inner_holomorphicField_eq_localRightScalar_of_norm_lt
        hTowerC (by infer_instance) OS T g fa directions hRc hRw
        hUx hRwUx hscalarx hrealx Ψa hΨRw hT zx
        (by simpa [zx, bound] using hxsmall) hxP
  have hdiag := hslice_real x hxpr
  have hself :
      scalarx zx =
        @inner ℂ (OSHilbertSpace OS) _
          (osiiPositiveTimeSingleVectorCLM OS n g)
          (osiiPositiveTimeSingleVectorCLM OS n g) := by
    rw [hdiag]
    rw [show
        translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) fa.1 =
          g.1 by
      exact (hxsource a).symm]
    rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
    have hxy := hjoint_lr hxpl hxpr
    have hdisp :
        L (Fin.append x x) =
          Fin.append
            (timeReflectionN d
              (sourceParameterDisplacementCLM directions x))
            (sourceParameterDisplacementCLM directions x) := by
      change
        Fin.append
            (timeReflectionN d
              (sourceParameterDisplacementCLM directions
                (fun i => Fin.append x x (Fin.castAdd m i))))
            (sourceParameterDisplacementCLM directions
              (fun i => Fin.append x x (Fin.natAdd m i))) =
          _
      congr 2
      · congr 1
        funext i
        exact Fin.append_left x x i
      · funext i
        exact Fin.append_right x x i
    rw [show
        g.1.osConjTensorProduct g.1 =
          translateSchwartzConfiguration
            (L (Fin.append x x)) (φ a) by
      rw [show g.1 =
          translateSchwartzConfiguration
            (sourceParameterDisplacementCLM directions x) fa.1 by
        exact hxsource a]
      rw [osConjTensorProduct_translateSchwartzConfiguration]
      rw [hdisp]]
    exact (hxy.2 a).2
  exact
    eq_of_norm_sq_eq_and_inner_eq_inner_self OS
      (osiiPositiveTimeSingleVectorCLM OS n g) (Ψa zx)
      (hxnorm a) (hpair.trans hself)

end OSIIChapterV
end OSReconstruction
