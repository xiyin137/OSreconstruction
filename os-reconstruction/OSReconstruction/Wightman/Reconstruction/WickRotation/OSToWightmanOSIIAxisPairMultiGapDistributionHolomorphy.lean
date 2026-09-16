/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionRealEdge
import OSReconstruction.Mathlib429Compat
import Mathlib.Topology.ContinuousMap.Bounded.Normed















noncomputable section

open Filter GaussianField Topology
open scoped BoundedContinuousFunction Classical

namespace OSReconstruction

variable {K E G : Type*}
  [NontriviallyNormedField K]
  [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]
  [BaireSpace E] [FirstCountableTopology E]
  [NormedAddCommGroup G] [NormedSpace K G]

/-- The separately-continuous multilinear theorem with a normed target. -/
theorem multilinear_continuous_of_separatelyContinuous_normedTarget
    {n : Nat}
    (Phi : MultilinearMap K (fun _ : Fin n => E) G)
    (hPhi : forall (i : Fin n) (fs : Fin n -> E),
      Continuous (fun f => Phi (Function.update fs i f))) :
    Continuous Phi := by
  induction n with
  | zero =>
      have heq : forall fs : Fin 0 -> E, fs = Fin.elim0 := by
        intro fs
        ext i
        exact Fin.elim0 i
      have hconst : forall fs : Fin 0 -> E, Phi fs = Phi Fin.elim0 := by
        intro fs
        congr 1
        exact heq fs
      show Continuous (fun fs => Phi fs)
      simp_rw [hconst]
      exact continuous_const
  | succ n ih =>
      have hcurry_sep : forall (x0 : E) (j : Fin n) (gs : Fin n -> E),
          Continuous (fun g =>
            Phi.curryLeft x0 (Function.update gs j g)) := by
        intro x0 j gs
        have key : forall g : E,
            Phi.curryLeft x0 (Function.update gs j g) =
              Phi (Function.update (Fin.cons x0 gs) j.succ g) := by
          intro g
          simp only [MultilinearMap.curryLeft_apply, Fin.cons_update]
        simp_rw [key]
        exact hPhi j.succ (Fin.cons x0 gs)
      have hcurry_cont : forall x0 : E, Continuous (Phi.curryLeft x0) :=
        fun x0 => ih (Phi.curryLeft x0) (hcurry_sep x0)
      have hcont_h : forall gs : Fin n -> E,
          Continuous (fun h : E => Phi.curryLeft h gs) := by
        intro gs
        have heq :
            (fun h => Phi.curryLeft h gs) =
              (fun h => Phi (Function.update (Fin.cons 0 gs) 0 h)) := by
          ext h
          simp [MultilinearMap.curryLeft_apply]
        rw [heq]
        exact hPhi 0 (Fin.cons 0 gs)
      apply continuous_iff_continuousAt.mpr
      intro fs0
      have hPhi_eq : forall m : Fin (n + 1) -> E,
          Phi m = Phi.curryLeft (m 0) (Fin.tail m) := by
        intro m
        simp [MultilinearMap.curryLeft_apply, Fin.cons_self_tail]
      have hPhi_eq' :
          (fun fs => Phi fs) =
            (fun fs => Phi.curryLeft (fs 0) (Fin.tail fs)) := by
        ext fs
        exact hPhi_eq fs
      rw [ContinuousAt]
      change Tendsto (fun fs => Phi fs) (nhds fs0) (nhds (Phi fs0))
      rw [hPhi_eq']
      have hdecomp : forall fs : Fin (n + 1) -> E,
          Phi.curryLeft (fs 0) (Fin.tail fs) =
            Phi.curryLeft (fs 0 - fs0 0) (Fin.tail fs) +
              Phi.curryLeft (fs0 0) (Fin.tail fs) := by
        intro fs
        have hmap :
            Phi.curryLeft (fs 0) =
              Phi.curryLeft (fs 0 - fs0 0) +
                Phi.curryLeft (fs0 0) := by
          rw [← Phi.curryLeft.map_add, sub_add_cancel]
        rw [hmap]
        rfl
      simp_rw [hdecomp]
      rw [← zero_add (Phi fs0)]
      apply Tendsto.add
      · set gs0 := Fin.tail fs0
        rw [tendsto_def]
        intro U hU
        rw [Metric.mem_nhds_iff] at hU
        obtain ⟨epsilon, hepsilon, hepsilonU⟩ := hU
        suffices
            ∃ V, V ∈ nhds fs0 ∧
              ∀ fs, fs ∈ V →
                norm (Phi.curryLeft (fs 0 - fs0 0) (Fin.tail fs)) <
                  epsilon by
          obtain ⟨V, hV, hVe⟩ := this
          exact Filter.mem_of_superset hV (fun fs hfs =>
            hepsilonU (Metric.mem_ball.mpr (by
              rw [dist_zero_right]
              exact hVe fs hfs)))
        by_contra h
        push_neg at h
        obtain ⟨Vbasis, hVbasis⟩ := (nhds fs0).exists_antitone_basis
        choose fsSeq hfsSeqMem hfsSeqBound using
          fun m => h (Vbasis m) (hVbasis.mem m)
        have hfsSeqLim : Tendsto fsSeq atTop (nhds fs0) :=
          hVbasis.tendsto hfsSeqMem
        have hhLim :
            Tendsto (fun m => fsSeq m 0 - fs0 0) atTop (nhds 0) := by
          have h1 : Tendsto (fun m => fsSeq m 0) atTop (nhds (fs0 0)) :=
            (continuous_apply (0 : Fin (n + 1))).continuousAt.tendsto.comp
              hfsSeqLim
          have h2 :
              Tendsto (fun m => fsSeq m 0 - fs0 0) atTop
                (nhds (fs0 0 - fs0 0)) :=
            h1.sub tendsto_const_nhds
          rwa [sub_self] at h2
        have hgsLim :
            Tendsto (fun m => Fin.tail (fsSeq m)) atTop (nhds gs0) :=
          (continuous_pi (fun i =>
            continuous_apply (Fin.succ i))).continuousAt.tendsto.comp
              hfsSeqLim
        let phi : Nat → E →L[K] G := fun m =>
          { toLinearMap :=
              { toFun := fun x =>
                  Phi.curryLeft x (Fin.tail (fsSeq m))
                map_add' := by
                  intro x y
                  simp [map_add, MultilinearMap.add_apply]
                map_smul' := by
                  intro c x
                  simp [map_smul, MultilinearMap.smul_apply] }
            cont := hcont_h (Fin.tail (fsSeq m)) }
        let p : Nat → Seminorm K E := fun m =>
          (normSeminorm K G).comp (phi m).toLinearMap
        have hpCont : forall m, Continuous (p m) :=
          fun m => (phi m).continuous.norm
        have hpBdd : BddAbove (Set.range p) := by
          rw [Seminorm.bddAbove_range_iff]
          intro x
          have hconv :
              Tendsto (fun m => phi m x) atTop
                (nhds (Phi.curryLeft x gs0)) :=
            (hcurry_cont x).continuousAt.tendsto.comp hgsLim
          exact hconv.norm.bddAbove_range
        letI : BarrelledSpace K E := BaireSpace.instBarrelledSpace
        have hpSupCont : Continuous (⨆ m, p m) :=
          Seminorm.continuous_iSup p hpCont hpBdd
        let pSup : Seminorm K E := ⨆ m, p m
        have hpSupZero : pSup (0 : E) = 0 := map_zero _
        have hpSupCont' : Continuous pSup := by
          have hcoe : (pSup : E → Real) = ⨆ m, (p m : E → Real) := by
            exact Seminorm.coe_iSup_eq hpBdd
          rw [hcoe]
          exact hpSupCont
        have hV0 :
            pSup ⁻¹' Metric.ball 0 epsilon ∈ nhds (0 : E) :=
          hpSupCont'.continuousAt.preimage_mem_nhds (by
            rw [hpSupZero]
            exact Metric.ball_mem_nhds 0 hepsilon)
        have hhIn :
            ∀ᶠ m in atTop,
              fsSeq m 0 - fs0 0 ∈ pSup ⁻¹' Metric.ball 0 epsilon :=
          hhLim hV0
        obtain ⟨m0, hm0⟩ := hhIn.exists
        have hle :
            p m0 (fsSeq m0 0 - fs0 0) ≤
              pSup (fsSeq m0 0 - fs0 0) := by
          exact (le_ciSup hpBdd m0) _
        have hlt :
            pSup (fsSeq m0 0 - fs0 0) < epsilon := by
          simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq,
            sub_zero] at hm0
          rwa [abs_of_nonneg (apply_nonneg pSup _)] at hm0
        have hpEq :
            p m0 (fsSeq m0 0 - fs0 0) =
              norm
                (Phi.curryLeft (fsSeq m0 0 - fs0 0)
                  (Fin.tail (fsSeq m0))) := by
          rfl
        linarith [hfsSeqBound m0]
      · rw [hPhi_eq fs0]
        exact (hcurry_cont (fs0 0)).continuousAt.comp
          (continuous_pi (fun i =>
            continuous_apply (Fin.succ i))).continuousAt

variable {d n : Nat} {J : Type*} [NeZero d]

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

set_option backward.isDefEq.respectTransparency false in
/-- A pointwise-bounded family of continuous multilinear Schwartz
maps into a complete complex normed target has one polynomial Hermite bound,
uniform over the family. -/
theorem pointwiseBounded_cmm_encodedHermite_polyBounded
    {D : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [FiniteDimensional Real D] [Nontrivial D]
    [MeasurableSpace D] [BorelSpace D]
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace Complex G]
    [NormedSpace Real G] [IsScalarTower Real Complex G]
    [CompleteSpace G]
    (T : J →
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => SchwartzMap D Complex) G)
    (βs : Nat → Fin n → Nat)
    (hβ : ∃ D_enc > 0, ∃ q : Nat, ∀ m i,
      (βs m i : Real) ≤ D_enc * (1 + (m : Real)) ^ q)
    (hT : forall fs : Fin n -> SchwartzMap D Complex,
      exists C : Real, forall i, norm (T i fs) ≤ C) :
    exists C : Real, 0 < C ∧ exists p : Nat,
      forall i m,
        norm (T i (fun a =>
          complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (E := SchwartzMap D Real)
              (βs m a)))) ≤
          C * (1 + (m : Real)) ^ p := by
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  let sourceBound : (Fin n -> SchwartzMap D Complex) -> Real :=
    fun fs => Classical.choose (hT fs)
  have source_bound :
      forall fs i, norm (T i fs) ≤ sourceBound fs := by
    intro fs i
    exact Classical.choose_spec (hT fs) i
  let familyValue :
      (Fin n -> SchwartzMap D Complex) -> (J →ᵇ G) :=
    fun fs =>
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun i : J => T i fs) (sourceBound fs) (source_bound fs)
  let Phi :
      MultilinearMap Complex
        (fun _ : Fin n => SchwartzMap D Complex) (J →ᵇ G) :=
    { toFun := familyValue
      map_update_add' := by
        intro hdec fs j f g
        letI := hdec
        ext i
        simp [familyValue]
      map_update_smul' := by
        intro hdec fs j c f
        letI := hdec
        ext i
        simp [familyValue] }
  have hPhi_sep :
      forall (j : Fin n) (fs : Fin n -> SchwartzMap D Complex),
        Continuous (fun f => Phi (Function.update fs j f)) := by
    intro j fs
    let L : J -> SchwartzMap D Complex →L[Complex] G :=
      fun i => (T i).toContinuousLinearMap fs j
    have hL_pointwise :
        forall f : SchwartzMap D Complex,
          exists C : Real, forall i, norm (L i f) ≤ C := by
      intro f
      obtain ⟨C, hC⟩ := hT (Function.update fs j f)
      refine ⟨C, fun i => ?_⟩
      simpa [L, ContinuousMultilinearMap.toContinuousLinearMap_apply] using
        hC i
    have hL_equicont :
        Equicontinuous
          (fun i f => (L i).restrictScalars Real f) := by
      simpa only [Function.comp_apply] using
        (SchwartzMap.tempered_equicontinuous
          (E := D) (F := Complex) (G := G)
          (T := fun i => (L i).restrictScalars Real)
          (by
            intro f
            obtain ⟨C, hC⟩ := hL_pointwise f
            exact ⟨C, fun i => by simpa using hC i⟩)).equicontinuous
    rw [continuous_iff_continuousAt]
    intro f0
    change Tendsto
      (fun f => Phi (Function.update fs j f))
      (nhds f0)
      (nhds (Phi (Function.update fs j f0)))
    refine Metric.tendsto_nhds.2 ?_
    intro epsilon hepsilon
    have hhalf : 0 < epsilon / 2 := half_pos hepsilon
    filter_upwards
        [Metric.equicontinuousAt_iff_right.mp
          (hL_equicont f0) (epsilon / 2) hhalf] with f hf
    rw [dist_eq_norm]
    apply lt_of_le_of_lt
      ((BoundedContinuousFunction.norm_le hhalf.le).2
        (fun i => ?_))
      (half_lt_self hepsilon)
    change
      norm
        (Phi (Function.update fs j f) i -
          Phi (Function.update fs j f0) i) ≤
        epsilon / 2
    rw [← dist_eq_norm]
    simpa [Phi, familyValue, L,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, dist_comm] using
      (hf i).le
  let PhiCont :
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => SchwartzMap D Complex) (J →ᵇ G) :=
    { Phi with
      cont := by
        letI :
            (uniformity (SchwartzMap D Complex)).IsCountablyGenerated := by
          set_option backward.isDefEq.respectTransparency false in
            exact IsUniformAddGroup.uniformity_countably_generated
        let hcomplete :
            TopologicalSpace.IsCompletelyPseudoMetrizableSpace
              (SchwartzMap D Complex) :=
          TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
        letI := hcomplete
        letI : BaireSpace (SchwartzMap D Complex) :=
          @BaireSpace.of_completelyPseudoMetrizable
            (SchwartzMap D Complex) inferInstance hcomplete
        exact
          multilinear_continuous_of_separatelyContinuous_normedTarget
            Phi hPhi_sep }
  let PhiReal :
      ContinuousMultilinearMap Real
        (fun _ : Fin n =>
          SchwartzMap D Real) (J →ᵇ G) :=
    { toFun := fun fs => PhiCont (fun i => complexifyRealSchwartz (fs i))
      map_update_add' := by
        intro hdec fs i f g
        letI := hdec
        have hupdate :
            forall h,
              (fun j => complexifyRealSchwartz
                (Function.update fs i h j)) =
              Function.update
                (fun j => complexifyRealSchwartz (fs j))
                i (complexifyRealSchwartz h) := by
          intro h
          ext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [Function.update, hji]
        rw [hupdate (f + g), hupdate f, hupdate g]
        simpa using
          PhiCont.map_update_add
            (fun j => complexifyRealSchwartz (fs j))
            i (complexifyRealSchwartz f) (complexifyRealSchwartz g)
      map_update_smul' := by
        intro hdec fs i c f
        letI := hdec
        have hupdate :
            forall h,
              (fun j => complexifyRealSchwartz
                (Function.update fs i h j)) =
              Function.update
                (fun j => complexifyRealSchwartz (fs j))
                i (complexifyRealSchwartz h) := by
          intro h
          ext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [Function.update, hji]
        rw [hupdate (c • f), hupdate f]
        have hc :
            complexifyRealSchwartz (c • f) =
              (c : Complex) • complexifyRealSchwartz f := by
          exact map_smul complexifyRealSchwartz c f
        rw [hc]
        rw [PhiCont.map_update_smul]
        exact IsScalarTower.algebraMap_smul Complex c _
      cont := PhiCont.cont.comp
        (continuous_pi fun i =>
          (complexifyRealSchwartz.continuous.comp
            (continuous_apply i))) }
  obtain ⟨C, hC, p, hp⟩ :=
    norm_multilinear_on_basis_polyBounded n PhiReal
      βs hβ
  refine ⟨C, hC, p, fun i m => ?_⟩
  calc
    norm (T i (fun a =>
        complexifyRealSchwartz
          (GaussianField.DyninMityaginSpace.basis
            (E := SchwartzMap D Real)
            (βs m a)))) =
        norm (PhiCont (fun a =>
          complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (E := SchwartzMap D Real)
              (βs m a))) i) := by
      rfl
    _ ≤ norm (PhiCont (fun a =>
          complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (E := SchwartzMap D Real)
              (βs m a)))) :=
      BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ C * (1 + (m : Real)) ^ p := by
      change norm (PhiReal (fun a =>
        GaussianField.DyninMityaginSpace.basis
          (E := SchwartzMap D Real) (βs m a))) ≤
        C * (1 + (m : Real)) ^ p
      exact hp m

set_option backward.isDefEq.respectTransparency false in
/-- Product-aware specialization of
`pointwiseBounded_cmm_encodedHermite_polyBounded`. -/
theorem pointwiseBounded_cmm_productBasis_polyBounded
    {D : Type*}
    [NormedAddCommGroup D] [NormedSpace Real D]
    [FiniteDimensional Real D] [Nontrivial D]
    [MeasurableSpace D] [BorelSpace D]
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace Complex G]
    [NormedSpace Real G] [IsScalarTower Real Complex G]
    [CompleteSpace G]
    (T : J →
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => SchwartzMap D Complex) G)
    (hn : 0 < n)
    (hT : forall fs : Fin n -> SchwartzMap D Complex,
      exists C : Real, forall i, norm (T i fs) ≤ C) :
    exists C : Real, 0 < C ∧ exists p : Nat,
      forall i m,
        norm (T i (fun a =>
          complexifyRealSchwartz
            (GaussianField.DyninMityaginSpace.basis
              (E := SchwartzMap D Real)
              (GaussianField.productBasisIndices
                (D := D) n hn m a)))) ≤
          C * (1 + (m : Real)) ^ p := by
  exact
    pointwiseBounded_cmm_encodedHermite_polyBounded T
      (GaussianField.productBasisIndices (D := D) n hn)
      (GaussianField.productBasisIndices_polyGrowth (D := D) n hn)
      hT

set_option backward.isDefEq.respectTransparency false in
/-- Spacetime specialization of
`pointwiseBounded_cmm_productBasis_polyBounded`. -/
theorem pointwiseBounded_cmm_productHermite_polyBounded
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace Complex G]
    [NormedSpace Real G] [IsScalarTower Real Complex G]
    [CompleteSpace G]
    (T : J →
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => SchwartzSpacetime d) G)
    (hn : 0 < n)
    (hT : forall fs : Fin n -> SchwartzSpacetime d,
      exists C : Real, forall i, norm (T i fs) ≤ C) :
    exists C : Real, 0 < C ∧ exists p : Nat,
      forall i m,
        norm (T i (productHermiteFactor (d := d) hn m)) ≤
          C * (1 + (m : Real)) ^ p := by
  unfold productHermiteFactor
  exact pointwiseBounded_cmm_productBasis_polyBounded
    (D := SpacetimeDim d) T hn hT

/-- A polynomial product-Hermite bound for one full Schwartz distribution
controls its action on every complexified real Schwartz test. -/
theorem norm_schwartzDistribution_complexifyRealSchwartz_le_of_productHermite
    {d n : Nat}
    [NeZero d]
    (W : SchwartzNPoint d n →L[Complex] Complex)
    (hn : 0 < n)
    (C : Real) (p : Nat)
    (hbound : forall m,
      norm (W
        (SchwartzMap.productTensor
          (productHermiteFactor (d := d) hn m))) ≤
        C * (1 + (m : Real)) ^ p)
    (g : SchwartzMap (Fin n -> Fin (d + 1) -> Real) Real) :
    norm (W (complexifyRealSchwartz g)) ≤
      C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p
        (GaussianField.productRapidDecayEquiv n hn g) := by
  letI : NeZero d := inferInstance
  let e := GaussianField.productRapidDecayEquiv
    (D := Fin (d + 1) -> Real) n hn
  let L : GaussianField.RapidDecaySeq →L[Real] Complex :=
    (W.restrictScalars Real).comp
      (complexifyRealSchwartz.comp e.symm.toContinuousLinearMap)
  let a : GaussianField.RapidDecaySeq := e g
  have hsum :
      HasSum
        (fun m => L
          (a.val m • GaussianField.RapidDecaySeq.basisVec m))
        (L a) :=
    (GaussianField.RapidDecaySeq.hasSum_basisVec a).mapL L
  have hmajor :
      Summable (fun m => C * (abs (a.val m) * (1 + (m : Real)) ^ p)) :=
    ((a.rapid_decay p).mul_left C).congr (fun m => by ring)
  have hnorm_summable :
      Summable (fun m =>
        norm (L (a.val m • GaussianField.RapidDecaySeq.basisVec m))) := by
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [map_smul, norm_smul]
      change
        norm (a.val m : Real) *
            norm (W (complexifyRealSchwartz
              (e.symm (GaussianField.RapidDecaySeq.basisVec m)))) ≤
          C * (abs (a.val m) * (1 + (m : Real)) ^ p)
      rw [Real.norm_eq_abs]
      calc
        abs (a.val m) *
              norm (W (complexifyRealSchwartz
                (e.symm (GaussianField.RapidDecaySeq.basisVec m))))
            ≤ abs (a.val m) * (C * (1 + (m : Real)) ^ p) := by
              apply mul_le_mul_of_nonneg_left
              · change
                  norm (W (complexifyRealSchwartz
                    (realProductHermite (d := d) hn m))) ≤
                    C * (1 + (m : Real)) ^ p
                rw [complexifyRealSchwartz_realProductHermite
                  (d := d) hn m]
                exact hbound m
              · exact abs_nonneg _
        _ = C * (abs (a.val m) * (1 + (m : Real)) ^ p) := by
          ring) hmajor
  calc
    norm (W (complexifyRealSchwartz g)) = norm (L a) := by
      simp [L, a, e, complexifyRealSchwartz]
    _ = norm (∑' m, L
        (a.val m • GaussianField.RapidDecaySeq.basisVec m)) := by
      rw [hsum.tsum_eq]
    _ ≤ ∑' m,
        norm (L (a.val m • GaussianField.RapidDecaySeq.basisVec m)) :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' m, C * (abs (a.val m) * (1 + (m : Real)) ^ p) := by
      apply hnorm_summable.tsum_le_tsum
      · intro m
        rw [map_smul, norm_smul]
        change
          norm (a.val m : Real) *
              norm (W (complexifyRealSchwartz
                (e.symm (GaussianField.RapidDecaySeq.basisVec m)))) ≤
            C * (abs (a.val m) * (1 + (m : Real)) ^ p)
        rw [Real.norm_eq_abs]
        calc
          abs (a.val m) *
                norm (W (complexifyRealSchwartz
                  (e.symm (GaussianField.RapidDecaySeq.basisVec m))))
              ≤ abs (a.val m) * (C * (1 + (m : Real)) ^ p) := by
                apply mul_le_mul_of_nonneg_left
                · change
                    norm (W (complexifyRealSchwartz
                      (realProductHermite (d := d) hn m))) ≤
                      C * (1 + (m : Real)) ^ p
                  rw [complexifyRealSchwartz_realProductHermite
                    (d := d) hn m]
                  exact hbound m
                · exact abs_nonneg _
          _ = C * (abs (a.val m) * (1 + (m : Real)) ^ p) := by
            ring
      · exact hmajor
    _ = C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p a := by
      rw [GaussianField.RapidDecaySeq.rapidDecaySeminorm]
      exact tsum_mul_left
    _ = C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p
        (GaussianField.productRapidDecayEquiv n hn g) := rfl

namespace OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily

variable {d n k : Nat} [NeZero d]
  {P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k}

/-- Restriction of one full Schwartz distribution to pure product tensors. -/
noncomputable def productCMM
    (A : P.SchwartzDistributionFamily)
    (z : {z : Fin k -> osiiAxisPairIndex d -> Complex //
      z ∈ osiiAxisPairMultiGapLogDomain d k}) :
    ContinuousMultilinearMap Complex
      (fun _ : Fin n => SchwartzSpacetime d) Complex :=
  (A.distribution z).compContinuousMultilinearMap
    (SchwartzMap.productTensorMLM (E := SpacetimeDim d) n)

@[simp] theorem productCMM_apply
    (A : P.SchwartzDistributionFamily)
    (z : {z : Fin k -> osiiAxisPairIndex d -> Complex //
      z ∈ osiiAxisPairMultiGapLogDomain d k})
    (fs : Fin n -> SchwartzSpacetime d) :
    A.productCMM z fs = P.toFun fs z.1 := by
  exact A.productTensor z fs

/-- A polynomial product-Hermite bound for a full Schwartz distribution
controls its action on every complexified real Schwartz test. -/
theorem norm_complexifyRealSchwartz_le_of_productHermite
    (A : P.SchwartzDistributionFamily)
    (z : {z : Fin k -> osiiAxisPairIndex d -> Complex //
      z ∈ osiiAxisPairMultiGapLogDomain d k})
    (hn : 0 < n)
    (C : Real) (p : Nat)
    (hbound : forall m,
      norm (A.distribution z
        (SchwartzMap.productTensor
          (productHermiteFactor (d := d) hn m))) ≤
        C * (1 + (m : Real)) ^ p)
    (g : SchwartzMap (Fin n -> Fin (d + 1) -> Real) Real) :
    norm (A.distribution z (complexifyRealSchwartz g)) ≤
      C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p
        (GaussianField.productRapidDecayEquiv n hn g) := by
  exact
    norm_schwartzDistribution_complexifyRealSchwartz_le_of_productHermite
      (A.distribution z) hn C p hbound g

/-- Compact scalar holomorphy on product tensors already forces compact
pointwise boundedness of the canonical full Schwartz distributions. -/
theorem locallyPointwiseBounded_of_productTensor_holomorphic
    (A : P.SchwartzDistributionFamily)
    (hn : 0 < n) :
    A.LocallyPointwiseBounded := by
  intro K hK_compact hK_domain f
  let T : K ->
      ContinuousMultilinearMap Complex
        (fun _ : Fin n => SchwartzSpacetime d) Complex :=
    fun z => A.productCMM ⟨z.1, hK_domain z.2⟩
  have hT_pointwise :
      forall fs : Fin n -> SchwartzSpacetime d,
        exists C : Real, forall z : K, norm (T z fs) ≤ C := by
    intro fs
    obtain ⟨C, hC⟩ :=
      hK_compact.exists_bound_of_continuousOn
        ((P.holomorphic fs).continuousOn.mono hK_domain)
    refine ⟨C, fun z => ?_⟩
    simpa [T, productCMM_apply] using hC z.1 z.2
  have hpoly := by
    set_option backward.isDefEq.respectTransparency false in
      exact pointwiseBounded_cmm_productHermite_polyBounded T hn hT_pointwise
  obtain ⟨C, hC, p, hp⟩ := hpoly
  let fRe := realPartSchwartz f
  let fIm := imaginaryPartSchwartz f
  let e := GaussianField.productRapidDecayEquiv
    (D := Fin (d + 1) -> Real) n hn
  refine
    ⟨C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) +
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm), ?_⟩
  intro z hz
  let zs : {z : Fin k -> osiiAxisPairIndex d -> Complex //
      z ∈ osiiAxisPairMultiGapLogDomain d k} :=
    ⟨z, hK_domain hz⟩
  have hRe :
      norm (A.distribution zs (complexifyRealSchwartz fRe)) ≤
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) := by
    apply A.norm_complexifyRealSchwartz_le_of_productHermite
      zs hn C p
    intro m
    simpa [T, zs, productCMM] using hp ⟨z, hz⟩ m
  have hIm :
      norm (A.distribution zs (complexifyRealSchwartz fIm)) ≤
        C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm) := by
    apply A.norm_complexifyRealSchwartz_le_of_productHermite
      zs hn C p
    intro m
    simpa [T, zs, productCMM] using hp ⟨z, hz⟩ m
  rw [A.pairing_of_mem f z (hK_domain hz)]
  rw [← complexifyRealSchwartz_realPart_add_I_imaginaryPart f]
  rw [map_add, map_smul]
  calc
    norm
        (A.distribution zs (complexifyRealSchwartz fRe) +
          Complex.I •
            A.distribution zs (complexifyRealSchwartz fIm))
        ≤ norm (A.distribution zs (complexifyRealSchwartz fRe)) +
            norm (Complex.I •
              A.distribution zs (complexifyRealSchwartz fIm)) :=
      norm_add_le _ _
    _ = norm (A.distribution zs (complexifyRealSchwartz fRe)) +
          norm (A.distribution zs (complexifyRealSchwartz fIm)) := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fRe) +
          C * GaussianField.RapidDecaySeq.rapidDecaySeminorm p (e fIm) :=
      add_le_add hRe hIm

/-- Product-tensor holomorphy therefore extends to every full Schwartz test
without an additional compact-boundedness hypothesis. -/
theorem differentiableOn_pairing_of_productTensor_holomorphic
    (A : P.SchwartzDistributionFamily)
    (hn : 0 < n)
    (f : SchwartzNPoint d n) :
    DifferentiableOn Complex
      (A.pairing f)
      (osiiAxisPairMultiGapLogDomain d k) :=
  A.differentiableOn_pairing
    (A.locallyPointwiseBounded_of_productTensor_holomorphic hn)
    f

/-- Compact equicontinuity and weak holomorphy give joint continuity when
the full Schwartz test varies continuously with an auxiliary parameter. -/
theorem continuous_distribution_joint_apply_on_compact
    (A : P.SchwartzDistributionFamily)
    (hA : A.LocallyPointwiseBounded)
    (K : Set (Fin k → osiiAxisPairIndex d → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ osiiAxisPairMultiGapLogDomain d k)
    {X : Type*} [TopologicalSpace X]
    (f : X → SchwartzNPoint d n)
    (hf : Continuous f) :
    Continuous
      (fun p : K × X =>
        A.distribution
          ⟨p.1.1, hK_domain p.1.2⟩
          (f p.2)) := by
  let T : K → SchwartzNPoint d n → ℂ :=
    fun z f => A.distribution ⟨z.1, hK_domain z.2⟩ f
  have hT_equi : UniformEquicontinuous T := by
    simpa [T] using
      A.uniformEquicontinuous_distribution_on_compact
        hA K hK_compact hK_domain
  have hT_fixed :
      ∀ e : SchwartzNPoint d n, Continuous (fun z : K => T z e) := by
    intro e
    have hcont :
        ContinuousOn
          (A.pairing e)
          K :=
      (A.differentiableOn_pairing hA e).continuousOn.mono hK_domain
    have hrestrict :
        Continuous (fun z : K => A.pairing e z.1) := by
      exact (continuousOn_iff_continuous_restrict.mp hcont).congr
        (fun z => rfl)
    apply hrestrict.congr
    intro z
    exact A.pairing_of_mem e z.1 (hK_domain z.2)
  exact
    continuous_joint_apply_of_uniformEquicontinuous
      T f hT_equi hT_fixed hf

/-- Joint compact evaluation on the honest multi-gap carrier is
unconditional for positive source arity. -/
theorem continuous_distribution_joint_apply_on_compact_of_pos
    (A : P.SchwartzDistributionFamily)
    (hn : 0 < n)
    (K : Set (Fin k → osiiAxisPairIndex d → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ osiiAxisPairMultiGapLogDomain d k)
    {X : Type*} [TopologicalSpace X]
    (f : X → SchwartzNPoint d n)
    (hf : Continuous f) :
    Continuous
      (fun p : K × X =>
        A.distribution
          ⟨p.1.1, hK_domain p.1.2⟩
          (f p.2)) :=
  A.continuous_distribution_joint_apply_on_compact
    (A.locallyPointwiseBounded_of_productTensor_holomorphic hn)
    K hK_compact hK_domain f hf

end OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily

namespace OSIIChronologicalCompactFactors

variable {d k : Nat} [NeZero d] [NeZero k]

section OriginalOSSourceFamily

variable (F : OSIIChronologicalCompactFactors d k)
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

end OriginalOSSourceFamily

end OSIIChronologicalCompactFactors

namespace OSIIChronologicalSourcewisePacketData

variable {d n k : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {lgc : OSLinearGrowthCondition d OS}

/-- The canonical chronological multi-gap family is weakly holomorphic
against every full Schwartz test. -/
theorem schwartzDistributionFamily_differentiableOn_pairing
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc)
    (hn : 0 < n)
    (f : SchwartzNPoint d n) :
    DifferentiableOn Complex
      (D.schwartzDistributionFamily.pairing f)
      (osiiAxisPairMultiGapLogDomain d k) :=
  OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.differentiableOn_pairing_of_productTensor_holomorphic
    D.schwartzDistributionFamily hn f

end OSIIChronologicalSourcewisePacketData

end OSReconstruction
