import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity

/-!
# Section 4.3 spatial Fourier density support

This companion file starts Layer 3 of the Section 4.3 OS-route density proof.
It keeps the finite-time compact-Laplace density file frozen and introduces the
spatial-frequency compact-source interface needed for the next tensor-density
step.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

/-- The spatial block appearing after the standard time/spatial splitting. -/
abbrev Section43SpatialSpace (d n : ℕ) :=
  EuclideanSpace ℝ (Fin n × Fin d)

/-- Flatten the spatial Euclidean block to ordinary finite real coordinates.
This is the bridge to `SchwartzMap.dense_hasCompactSupport`, which is stated on
`Fin m → ℝ`. -/
noncomputable def section43SpatialFlatCLE (d n : ℕ) :
    Section43SpatialSpace d n ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)).trans
    ((LinearEquiv.funCongrLeft ℝ ℝ finProdFinEquiv.symm).toContinuousLinearEquiv)

@[simp] theorem section43SpatialFlatCLE_apply
    (d n : ℕ) (η : Section43SpatialSpace d n) (k : Fin (n * d)) :
    section43SpatialFlatCLE d n η k =
      (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) η)
        (finProdFinEquiv.symm k) := rfl

@[simp] theorem section43SpatialFlatCLE_symm_apply
    (d n : ℕ) (x : Fin (n * d) → ℝ) (p : Fin n × Fin d) :
    (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
      ((section43SpatialFlatCLE d n).symm x)) p =
      x (finProdFinEquiv p) := rfl

/-- The Schwartz-space lift of `section43SpatialFlatCLE`. -/
noncomputable def section43SpatialFlatSchwartzCLE (d n : ℕ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ ≃L[ℂ]
      SchwartzMap (Fin (n * d) → ℝ) ℂ := by
  let e := section43SpatialFlatCLE d n
  let toFwd :
      SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
        SchwartzMap (Fin (n * d) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap (Fin (n * d) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d n) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext η
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

@[simp] theorem section43SpatialFlatSchwartzCLE_apply
    (d n : ℕ) (κ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (x : Fin (n * d) → ℝ) :
    section43SpatialFlatSchwartzCLE d n κ x =
      κ ((section43SpatialFlatCLE d n).symm x) := by
  simp [section43SpatialFlatSchwartzCLE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp] theorem section43SpatialFlatSchwartzCLE_symm_apply
    (d n : ℕ) (κ : SchwartzMap (Fin (n * d) → ℝ) ℂ)
    (η : Section43SpatialSpace d n) :
    (section43SpatialFlatSchwartzCLE d n).symm κ η =
      κ (section43SpatialFlatCLE d n η) := by
  change
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43SpatialFlatCLE d n) κ) η =
      κ (section43SpatialFlatCLE d n η)
  rfl

/-- Compactly supported spatial Schwartz sources in the spatial block. -/
def Section43SpatialCompactSource (d n : ℕ) :=
  {κ : SchwartzMap (Section43SpatialSpace d n) ℂ //
    HasCompactSupport (κ : Section43SpatialSpace d n → ℂ)}

/-- Compactly supported Schwartz functions are dense on the Section 4.3 spatial
block.  This transports `SchwartzMap.dense_hasCompactSupport` from
`Fin (n*d) → ℝ` through `section43SpatialFlatCLE`. -/
theorem dense_section43Spatial_hasCompactSupport (d n : ℕ) :
    Dense
      {κ : SchwartzMap (Section43SpatialSpace d n) ℂ |
        HasCompactSupport (κ : Section43SpatialSpace d n → ℂ)} := by
  let E := Section43SpatialSpace d n
  let P := Fin (n * d) → ℝ
  let e := section43SpatialFlatCLE d n
  let T := (section43SpatialFlatSchwartzCLE d n).symm
  let Sflat : Set (SchwartzMap P ℂ) :=
    {κ | HasCompactSupport (κ : P → ℂ)}
  let Ssp : Set (SchwartzMap E ℂ) :=
    {κ | HasCompactSupport (κ : E → ℂ)}
  have hflat : Dense Sflat := by
    simpa [Sflat, P] using
      (SchwartzMap.dense_hasCompactSupport (m := n * d))
  have hT_denseRange :
      DenseRange (T : SchwartzMap P ℂ → SchwartzMap E ℂ) :=
    (section43SpatialFlatSchwartzCLE d n).symm.surjective.denseRange
  have himage_dense : Dense ((fun κ : SchwartzMap P ℂ => T κ) '' Sflat) :=
    hT_denseRange.dense_image
      ((section43SpatialFlatSchwartzCLE d n).symm.continuous) hflat
  have hsubset :
      ((fun κ : SchwartzMap P ℂ => T κ) '' Sflat) ⊆ Ssp := by
    rintro _ ⟨κ, hκ, rfl⟩
    have htsupport :
        tsupport ((T κ : SchwartzMap E ℂ) : E → ℂ) =
          e.toHomeomorph ⁻¹' tsupport (κ : P → ℂ) := by
      simpa [T, E, P, e, section43SpatialFlatSchwartzCLE,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        (tsupport_comp_eq_preimage (g := (κ : P → ℂ)) e.toHomeomorph)
    have hpre_eq :
        e.toHomeomorph ⁻¹' tsupport (κ : P → ℂ) =
          e.symm '' tsupport (κ : P → ℂ) := by
      ext η
      constructor
      · intro hη
        refine ⟨e η, hη, ?_⟩
        simp [e]
      · rintro ⟨x, hx, rfl⟩
        simpa [e] using hx
    have hcompact :
        IsCompact (e.symm '' tsupport (κ : P → ℂ)) :=
      hκ.isCompact.image e.symm.continuous
    change HasCompactSupport ((T κ : SchwartzMap E ℂ) : E → ℂ)
    rw [HasCompactSupport, htsupport, hpre_eq]
    exact hcompact
  exact Dense.mono hsubset himage_dense

/-- Spatial-frequency functions obtained by Fourier-transforming compactly
supported spatial Schwartz sources. -/
noncomputable def section43SpatialFourierCompactRange (d n : ℕ) :
    Set (SchwartzMap (Section43SpatialSpace d n) ℂ) :=
  Set.range fun κ : Section43SpatialCompactSource d n =>
    SchwartzMap.fourierTransformCLM ℂ κ.1

/-- Fourier transforms of compactly supported spatial Schwartz sources are
dense in the spatial-frequency Schwartz space. -/
theorem dense_section43SpatialFourierCompactRange (d n : ℕ) :
    Dense (section43SpatialFourierCompactRange d n) := by
  let E := Section43SpatialSpace d n
  let FT : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
    SchwartzMap.fourierTransformCLM ℂ
  let Ssp : Set (SchwartzMap E ℂ) :=
    {κ | HasCompactSupport (κ : E → ℂ)}
  have hcompact_dense : Dense Ssp := by
    simpa [Ssp, E] using dense_section43Spatial_hasCompactSupport d n
  have hFT_denseRange : DenseRange (FT : SchwartzMap E ℂ → SchwartzMap E ℂ) := by
    have hsurj : Function.Surjective (FT : SchwartzMap E ℂ → SchwartzMap E ℂ) := by
      intro χ
      refine ⟨FourierTransform.fourierInv χ, ?_⟩
      simp [FT]
    exact hsurj.denseRange
  have himage_dense : Dense ((fun κ : SchwartzMap E ℂ => FT κ) '' Ssp) :=
    hFT_denseRange.dense_image FT.continuous hcompact_dense
  have hset :
      section43SpatialFourierCompactRange d n =
        (fun κ : SchwartzMap E ℂ => FT κ) '' Ssp := by
    ext χ
    constructor
    · rintro ⟨κ, rfl⟩
      exact ⟨κ.1, κ.2, rfl⟩
    · rintro ⟨κ, hκ, rfl⟩
      exact ⟨⟨κ, hκ⟩, rfl⟩
  simpa [hset] using himage_dense

/-- The product of the ordinary finite-time block and the Section 4.3 spatial
block. -/
abbrev Section43TimeSpatialSpace (d n : ℕ) :=
  (Fin n → ℝ) × Section43SpatialSpace d n

/-- Flatten the time/spatial product block to ordinary finite real coordinates:
first the `n` time coordinates, then the `n*d` flattened spatial coordinates. -/
noncomputable def section43TimeSpatialFlatCLE (d n : ℕ) :
    Section43TimeSpatialSpace d n ≃L[ℝ] (Fin (n + n * d) → ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).prodCongr
      (section43SpatialFlatCLE d n)).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ
        (Fin n) (Fin (n * d)) (fun _ => ℝ)).symm.trans
      (ContinuousLinearEquiv.piCongrLeft ℝ
        (fun _ : Fin (n + n * d) => ℝ) finSumFinEquiv))

@[simp] theorem section43TimeSpatialFlatCLE_splitFirst
    (d n : ℕ) (τ : Fin n → ℝ) (η : Section43SpatialSpace d n) :
    splitFirst n (n * d) (section43TimeSpatialFlatCLE d n (τ, η)) = τ := by
  ext i
  change (Equiv.piCongrLeft (fun _ : Fin (n + n * d) => ℝ) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin (n * d) => ℝ)).symm
        (τ, (section43SpatialFlatCLE d n) η))
      (Fin.castAdd (n * d) i) = τ i
  rw [show Fin.castAdd (n * d) i = finSumFinEquiv (Sum.inl i) from
    finSumFinEquiv_apply_left i]
  exact Equiv.piCongrLeft_sumInl (fun _ : Fin (n + n * d) => ℝ)
    finSumFinEquiv τ ((section43SpatialFlatCLE d n) η) i

@[simp] theorem section43TimeSpatialFlatCLE_splitLast
    (d n : ℕ) (τ : Fin n → ℝ) (η : Section43SpatialSpace d n) :
    splitLast n (n * d) (section43TimeSpatialFlatCLE d n (τ, η)) =
      section43SpatialFlatCLE d n η := by
  ext i
  change (Equiv.piCongrLeft (fun _ : Fin (n + n * d) => ℝ) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin (n * d) => ℝ)).symm
        (τ, (section43SpatialFlatCLE d n) η))
      (Fin.natAdd n i) = section43SpatialFlatCLE d n η i
  rw [show Fin.natAdd n i = finSumFinEquiv (Sum.inr i) from
    finSumFinEquiv_apply_right i]
  exact Equiv.piCongrLeft_sumInr (fun _ : Fin (n + n * d) => ℝ)
    finSumFinEquiv τ ((section43SpatialFlatCLE d n) η) i

/-- Tensor a finite-time Schwartz function with a spatial-frequency Schwartz
function, after flattening the spatial block.  Pointwise this is just
`φ τ * χ η`, but the definition is phrased through `SchwartzMap.tensorProduct`
so it participates in the existing dense-product machinery. -/
noncomputable def section43TimeSpatialTensor (d n : ℕ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzMap (Section43TimeSpatialSpace d n) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43TimeSpatialFlatCLE d n)
    (SchwartzMap.tensorProduct φ (section43SpatialFlatSchwartzCLE d n χ))

@[simp] theorem section43TimeSpatialTensor_apply
    (d n : ℕ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (τ : Fin n → ℝ) (η : Section43SpatialSpace d n) :
    section43TimeSpatialTensor d n φ χ (τ, η) = φ τ * χ η := by
  simp [section43TimeSpatialTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.tensorProduct_apply]

/-- Block tensors between `Fin n` and `Fin m` are dense in the flat
`Fin (n+m)` Schwartz space.  This follows because coordinatewise product
tensors are a subset of the block-tensor span. -/
theorem dense_section43_flatBlockTensor_span (n m : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Fin (n + m) → ℝ) ℂ |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          ∃ ψ : SchwartzMap (Fin m → ℝ) ℂ,
            F = SchwartzMap.tensorProduct φ ψ}) :
        Submodule ℂ (SchwartzMap (Fin (n + m) → ℝ) ℂ)) :
        Set (SchwartzMap (Fin (n + m) → ℝ) ℂ)) := by
  let A := SchwartzMap (Fin (n + m) → ℝ) ℂ
  let Pblock : Set A :=
    {F : A | ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
      ∃ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        F = SchwartzMap.tensorProduct φ ψ}
  let Mblock : Submodule ℂ A := Submodule.span ℂ Pblock
  let Pall : Set A :=
    {F : A | ∃ fs : Fin (n + m) → SchwartzMap ℝ ℂ,
      F = section43TimeProductTensor fs}
  let Mall : Submodule ℂ A := Submodule.span ℂ Pall
  change Dense (Mblock : Set A)
  have hMall_dense : Dense (Mall : Set A) := by
    simpa [Mall, Pall, A] using section43_timeProductTensor_span_dense (n + m)
  have hMall_le_Mblock : Mall ≤ Mblock := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨fs, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨section43TimeProductTensor (fun i : Fin n => fs (Fin.castAdd m i)),
      section43TimeProductTensor (fun j : Fin m => fs (Fin.natAdd n j)), ?_⟩
    ext x
    rw [SchwartzMap.tensorProduct_apply]
    simp [section43TimeProductTensor, splitFirst, splitLast, Fin.prod_univ_add]
  exact Dense.mono (fun F hF => hMall_le_Mblock hF) hMall_dense

/-- Unrestricted time/spatial block tensors are dense in the time/spatial
Schwartz space. -/
theorem dense_section43TimeSpatialTensor_span (d n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Section43TimeSpatialSpace d n) ℂ |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
            F = section43TimeSpatialTensor d n φ χ}) :
        Submodule ℂ (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) :
        Set (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) := by
  let A := SchwartzMap (Section43TimeSpatialSpace d n) ℂ
  let B := SchwartzMap (Fin (n + n * d) → ℝ) ℂ
  let e := section43TimeSpatialFlatCLE d n
  let toA : B →L[ℂ] A := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let toB : A →L[ℂ] B := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let PA : Set A :=
    {F : A | ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
      ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
        F = section43TimeSpatialTensor d n φ χ}
  let MA : Submodule ℂ A := Submodule.span ℂ PA
  let PB : Set B :=
    {F : B | ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
      ∃ ψ : SchwartzMap (Fin (n * d) → ℝ) ℂ,
        F = SchwartzMap.tensorProduct φ ψ}
  let MB : Submodule ℂ B := Submodule.span ℂ PB
  change Dense (MA : Set A)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  let preM : Submodule ℂ B := MA.topologicalClosure.comap toA.toLinearMap
  have hMB_dense : Dense (MB : Set B) := by
    simpa [MB, PB, B] using dense_section43_flatBlockTensor_span n (n * d)
  have hMB_le_preM : MB ≤ preM := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨φ, ψ, rfl⟩
    change toA (SchwartzMap.tensorProduct φ ψ) ∈ MA.topologicalClosure
    refine MA.le_topologicalClosure (Submodule.subset_span ?_)
    refine ⟨φ, (section43SpatialFlatSchwartzCLE d n).symm ψ, ?_⟩
    ext p
    rcases p with ⟨τ, η⟩
    change (φ.tensorProduct ψ) (e (τ, η)) =
      section43TimeSpatialTensor d n φ
        ((section43SpatialFlatSchwartzCLE d n).symm ψ) (τ, η)
    rw [SchwartzMap.tensorProduct_apply]
    simp [e, section43TimeSpatialTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hpre_closed : IsClosed (preM : Set B) := by
    change IsClosed {y : B | toA y ∈ (MA.topologicalClosure : Set A)}
    exact MA.isClosed_topologicalClosure.preimage toA.continuous
  have htop_le_pre : (⊤ : Submodule ℂ B) ≤ preM := by
    have hclosure : MB.topologicalClosure ≤ preM :=
      MB.topologicalClosure_minimal hMB_le_preM hpre_closed
    rwa [(Submodule.dense_iff_topologicalClosure_eq_top).mp hMB_dense] at hclosure
  have hxpre : toB x ∈ preM := htop_le_pre trivial
  change toA (toB x) ∈ MA.topologicalClosure at hxpre
  have hcomp : toA (toB x) = x := by
    ext p
    change x (e.symm (e p)) = x p
    simp
  simpa [hcomp] using hxpre

/-- If the time factors and spatial factors are dense, then finite sums of
time/spatial block tensors with factors in those dense sets are dense. -/
theorem dense_section43TimeSpatialTensor_span_of_factor_dense
    {d n : ℕ}
    {St : Set (SchwartzMap (Fin n → ℝ) ℂ)}
    {Sx : Set (SchwartzMap (Section43SpatialSpace d n) ℂ)}
    (hSt : Dense St) (hSx : Dense Sx) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Section43TimeSpatialSpace d n) ℂ |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          φ ∈ St ∧
          ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
          χ ∈ Sx ∧
            F = section43TimeSpatialTensor d n φ χ}) :
        Submodule ℂ (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) :
        Set (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) := by
  let At := SchwartzMap (Fin n → ℝ) ℂ
  let Ax := SchwartzMap (Section43SpatialSpace d n) ℂ
  let A := SchwartzMap (Section43TimeSpatialSpace d n) ℂ
  let PS : Set A :=
    {F : A | ∃ φ : At, φ ∈ St ∧ ∃ χ : Ax, χ ∈ Sx ∧
      F = section43TimeSpatialTensor d n φ χ}
  let MS : Submodule ℂ A := Submodule.span ℂ PS
  let Pall : Set A :=
    {F : A | ∃ φ : At, ∃ χ : Ax,
      F = section43TimeSpatialTensor d n φ χ}
  let Mall : Submodule ℂ A := Submodule.span ℂ Pall
  change Dense (MS : Set A)
  let D : Set (At × Ax) := St ×ˢ Sx
  let T : At × Ax → A := fun p => section43TimeSpatialTensor d n p.1 p.2
  have hD : Dense D := hSt.prod hSx
  have hTcont : Continuous T := by
    let e := section43TimeSpatialFlatCLE d n
    let toA : SchwartzMap (Fin (n + n * d) → ℝ) ℂ →L[ℂ] A :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    let Tflat : At × SchwartzMap (Fin (n * d) → ℝ) ℂ →
        SchwartzMap (Fin (n + n * d) → ℝ) ℂ :=
      fun p => SchwartzMap.tensorProduct p.1 p.2
    have hpair :
        Continuous (fun p : At × Ax =>
          (p.1, section43SpatialFlatSchwartzCLE d n p.2)) :=
      Continuous.prodMk continuous_fst
        ((section43SpatialFlatSchwartzCLE d n).continuous.comp continuous_snd)
    have hflat : Continuous Tflat := by
      simpa [Tflat] using
        (SchwartzMap.tensorProduct_continuous (E := ℝ) (m := n) (k := n * d))
    change Continuous
      (fun p : At × Ax =>
        toA (Tflat (p.1, section43SpatialFlatSchwartzCLE d n p.2)))
    exact toA.continuous.comp (hflat.comp hpair)
  have hMall_le_MSclosure : Mall ≤ MS.topologicalClosure := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨φ, χ, rfl⟩
    have himage_subset : T '' D ⊆ (MS : Set A) := by
      rintro _ ⟨p, hp, rfl⟩
      rcases hp with ⟨hpSt, hpSx⟩
      exact Submodule.subset_span ⟨p.1, hpSt, p.2, hpSx, rfl⟩
    have hmem_image_closure :
        section43TimeSpatialTensor d n φ χ ∈ closure (T '' D) := by
      exact hTcont.range_subset_closure_image_dense hD ⟨(φ, χ), rfl⟩
    change section43TimeSpatialTensor d n φ χ ∈ closure (MS : Set A)
    exact closure_mono himage_subset hmem_image_closure
  have hMall_dense : Dense (Mall : Set A) := by
    simpa [Mall, Pall, A, At, Ax] using dense_section43TimeSpatialTensor_span d n
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hxMall : x ∈ Mall.topologicalClosure := by
    rw [(Submodule.dense_iff_topologicalClosure_eq_top).mp hMall_dense]
    trivial
  have hclosure_le : Mall.topologicalClosure ≤ MS.topologicalClosure :=
    Mall.topologicalClosure_minimal hMall_le_MSclosure MS.isClosed_topologicalClosure
  exact hclosure_le hxMall

/-- The route-relevant dense family: time factors whose positive-time quotient
comes from a compact strict-positive Laplace source, paired with spatial
Fourier transforms of compact spatial sources. -/
theorem dense_section43TimeSpatialTensor_span_compactLaplace_spatialFourier
    (d n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Section43TimeSpatialSpace d n) ℂ |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          φ ∈
            ((section43TimePositiveQuotientMap n) ⁻¹'
              Set.range (section43IteratedLaplaceCompactTransform n)) ∧
          ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
          χ ∈ section43SpatialFourierCompactRange d n ∧
            F = section43TimeSpatialTensor d n φ χ}) :
        Submodule ℂ (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) :
        Set (SchwartzMap (Section43TimeSpatialSpace d n) ℂ)) :=
  dense_section43TimeSpatialTensor_span_of_factor_dense
    (d := d) (n := n)
    (hSt := dense_section43IteratedLaplaceCompactTransform_preimage n)
    (hSx := dense_section43SpatialFourierCompactRange d n)

/-- The time/spatial tensor transported back to the `n`-point Schwartz space. -/
noncomputable def section43NPointTimeSpatialTensor (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzNPoint d n :=
  (nPointTimeSpatialSchwartzCLE (d := d) (n := n)).symm
    (section43TimeSpatialTensor d n φ χ)

@[simp] theorem section43NPointTimeSpatialTensor_apply
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (q : NPointDomain d n) :
    section43NPointTimeSpatialTensor d n φ χ q =
      φ (section43QTime (d := d) (n := n) q) *
        χ (section43QSpatial (d := d) (n := n) q) := by
  change section43TimeSpatialTensor d n φ χ ((nPointTimeSpatialCLE (d := d) n) q) = _
  rw [show ((nPointTimeSpatialCLE (d := d) n) q) =
      (section43QTime (d := d) (n := n) q,
        section43QSpatial (d := d) (n := n) q) by
    simp [section43QTime, section43QSpatial]]
  simp

/-- The restricted time/spatial tensor-density theorem transported to
`SchwartzNPoint d n`. -/
theorem dense_section43NPointTimeSpatialTensor_span_of_factor_dense
    {d n : ℕ} [NeZero d]
    {St : Set (SchwartzMap (Fin n → ℝ) ℂ)}
    {Sx : Set (SchwartzMap (Section43SpatialSpace d n) ℂ)}
    (hSt : Dense St) (hSx : Dense Sx) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzNPoint d n |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          φ ∈ St ∧
          ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
          χ ∈ Sx ∧
            F = section43NPointTimeSpatialTensor d n φ χ}) :
        Submodule ℂ (SchwartzNPoint d n)) :
        Set (SchwartzNPoint d n)) := by
  let E := SchwartzNPoint d n
  let A := SchwartzMap (Section43TimeSpatialSpace d n) ℂ
  let e := nPointTimeSpatialSchwartzCLE (d := d) (n := n)
  let PN : Set E :=
    {F : E | ∃ φ : SchwartzMap (Fin n → ℝ) ℂ, φ ∈ St ∧
      ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ, χ ∈ Sx ∧
        F = section43NPointTimeSpatialTensor d n φ χ}
  let MN : Submodule ℂ E := Submodule.span ℂ PN
  let PP : Set A :=
    {F : A | ∃ φ : SchwartzMap (Fin n → ℝ) ℂ, φ ∈ St ∧
      ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ, χ ∈ Sx ∧
        F = section43TimeSpatialTensor d n φ χ}
  let MP : Submodule ℂ A := Submodule.span ℂ PP
  change Dense (MN : Set E)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  let preM : Submodule ℂ A := MN.topologicalClosure.comap e.symm.toLinearMap
  have hMP_dense : Dense (MP : Set A) := by
    simpa [MP, PP, A] using
      dense_section43TimeSpatialTensor_span_of_factor_dense
        (d := d) (n := n) (St := St) (Sx := Sx) hSt hSx
  have hMP_le_preM : MP ≤ preM := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨φ, hφ, χ, hχ, rfl⟩
    change e.symm (section43TimeSpatialTensor d n φ χ) ∈ MN.topologicalClosure
    refine MN.le_topologicalClosure (Submodule.subset_span ?_)
    exact ⟨φ, hφ, χ, hχ, rfl⟩
  have hpre_closed : IsClosed (preM : Set A) := by
    change IsClosed {y : A | e.symm y ∈ (MN.topologicalClosure : Set E)}
    exact MN.isClosed_topologicalClosure.preimage e.symm.continuous
  have htop_le_pre : (⊤ : Submodule ℂ A) ≤ preM := by
    have hclosure : MP.topologicalClosure ≤ preM :=
      MP.topologicalClosure_minimal hMP_le_preM hpre_closed
    rwa [(Submodule.dense_iff_topologicalClosure_eq_top).mp hMP_dense] at hclosure
  have hxpre : e x ∈ preM := htop_le_pre trivial
  change e.symm (e x) ∈ MN.topologicalClosure at hxpre
  simpa using hxpre

/-- Route-relevant `SchwartzNPoint` density after transporting the product-space
Layer-3 packet through the time/spatial split. -/
theorem dense_section43NPointTimeSpatialTensor_span_compactLaplace_spatialFourier
    (d n : ℕ) [NeZero d] :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzNPoint d n |
          ∃ φ : SchwartzMap (Fin n → ℝ) ℂ,
          φ ∈
            ((section43TimePositiveQuotientMap n) ⁻¹'
              Set.range (section43IteratedLaplaceCompactTransform n)) ∧
          ∃ χ : SchwartzMap (Section43SpatialSpace d n) ℂ,
          χ ∈ section43SpatialFourierCompactRange d n ∧
            F = section43NPointTimeSpatialTensor d n φ χ}) :
        Submodule ℂ (SchwartzNPoint d n)) :
        Set (SchwartzNPoint d n)) :=
  dense_section43NPointTimeSpatialTensor_span_of_factor_dense
    (d := d) (n := n)
    (hSt := dense_section43IteratedLaplaceCompactTransform_preimage n)
    (hSx := dense_section43SpatialFourierCompactRange d n)

/-- The topological support of a transported time/spatial tensor is controlled
by the topological support of its time factor. -/
theorem tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    tsupport
      ((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ⊆
    (section43QTime (d := d) (n := n)) ⁻¹'
      tsupport (φ : (Fin n → ℝ) → ℂ) := by
  intro q hq
  have hfun :
      (((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        fun q : NPointDomain d n =>
          φ (section43QTime (d := d) (n := n) q) *
            χ (section43QSpatial (d := d) (n := n) q) := by
    funext q
    simp
  have hprod :
      q ∈ tsupport
        (fun q : NPointDomain d n =>
          φ (section43QTime (d := d) (n := n) q) *
            χ (section43QSpatial (d := d) (n := n) q)) := by
    simpa [hfun] using hq
  have ht_pullback :
      q ∈ tsupport
        (fun q : NPointDomain d n =>
          φ (section43QTime (d := d) (n := n) q)) :=
    (tsupport_mul_subset_left
      (f := fun q : NPointDomain d n =>
        φ (section43QTime (d := d) (n := n) q))
      (g := fun q : NPointDomain d n =>
        χ (section43QSpatial (d := d) (n := n) q))) hprod
  exact
    (tsupport_comp_subset_preimage
      (φ : (Fin n → ℝ) → ℂ)
      (f := section43QTime (d := d) (n := n))
      (by
        simpa [section43QTimeCLM_apply] using
          (section43QTimeCLM d n).continuous)) ht_pullback

/-- A transported time/spatial tensor is compactly supported if both factors
are compactly supported. -/
theorem hasCompactSupport_section43NPointTimeSpatialTensor
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hφ : HasCompactSupport (φ : (Fin n → ℝ) → ℂ))
    (hχ : HasCompactSupport (χ : Section43SpatialSpace d n → ℂ)) :
    HasCompactSupport
      ((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  let e := nPointTimeSpatialCLE (d := d) n
  let K : Set (NPointDomain d n) :=
    e.symm '' (tsupport (φ : (Fin n → ℝ) → ℂ) ×ˢ
      tsupport (χ : Section43SpatialSpace d n → ℂ))
  have hKcompact : IsCompact K := by
    exact (hφ.isCompact.prod hχ.isCompact).image e.symm.continuous
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro q hq
  rw [Function.mem_support] at hq
  have hφq : φ (section43QTime (d := d) (n := n) q) ≠ 0 := by
    intro hzero
    apply hq
    simp [section43NPointTimeSpatialTensor_apply, hzero]
  have hχq : χ (section43QSpatial (d := d) (n := n) q) ≠ 0 := by
    intro hzero
    apply hq
    simp [section43NPointTimeSpatialTensor_apply, hzero]
  refine ⟨(section43QTime (d := d) (n := n) q,
      section43QSpatial (d := d) (n := n) q), ?_, ?_⟩
  · exact ⟨subset_tsupport _ (Function.mem_support.mpr hφq),
      subset_tsupport _ (Function.mem_support.mpr hχq)⟩
  · simp [e, section43QTime, section43QSpatial]

/-- Compact time/spatial sources in difference variables, supported in the
strict positive time orthant. -/
structure Section43CompactStrictPositiveTimeSpatialSource
    (d n : ℕ) [NeZero d] where
  f : SchwartzNPoint d n
  positive :
    tsupport (f : NPointDomain d n → ℂ) ⊆
      {q | ∀ i : Fin n, 0 < section43QTime (d := d) (n := n) q i}
  compact : HasCompactSupport (f : NPointDomain d n → ℂ)

/-- Product a compact strict-positive time source with a compact spatial source,
then transport it to the `n`-point difference-coordinate Schwartz space. -/
noncomputable def section43TimeSpatialProductSource
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n) :
    Section43CompactStrictPositiveTimeSpatialSource d n where
  f := section43NPointTimeSpatialTensor d n g.f κ.1
  positive := by
    intro q hq i
    exact g.positive
      (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d n g.f κ.1 hq) i
  compact :=
    hasCompactSupport_section43NPointTimeSpatialTensor
      d n g.f κ.1 g.compact κ.2

/-- The fixed-time spatial slice of a product source is scalar multiplication
of the spatial source by the time-source value. -/
theorem partialEval₂_section43TimeSpatialProductSource
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n)
    (τ : Fin n → ℝ) :
    SchwartzMap.partialEval₂
      (nPointSpatialTimeSchwartzCLE (d := d) (n := n)
        (section43TimeSpatialProductSource d n g κ).f) τ =
    g.f τ • κ.1 := by
  ext η
  change
    nPointSpatialTimeSchwartzCLE (d := d) (n := n)
      (section43TimeSpatialProductSource d n g κ).f (η, τ) =
    (g.f τ • κ.1) η
  rw [nPointSpatialTimeSchwartzCLE_apply]
  change
    nPointTimeSpatialSchwartzCLE (d := d) (n := n)
      (section43NPointTimeSpatialTensor d n g.f κ.1) (τ, η) =
    (g.f τ • κ.1) η
  change section43TimeSpatialTensor d n g.f κ.1 (τ, η) = (g.f τ • κ.1) η
  simp [smul_eq_mul]

/-- The partial spatial Fourier transform of a product source factorizes into
the time source times the full spatial Fourier transform of the spatial
source. -/
theorem partialFourierSpatial_fun_section43TimeSpatialProductSource
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n)
    (τ : Fin n → ℝ) (ξ : Section43SpatialSpace d n) :
    partialFourierSpatial_fun
      (d := d) (n := n)
      (section43TimeSpatialProductSource d n g κ).f
      (τ, ξ) =
    g.f τ * (SchwartzMap.fourierTransformCLM ℂ κ.1) ξ := by
  rw [partialFourierSpatial_fun]
  change
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.partialEval₂
        (nPointSpatialTimeSchwartzCLE (d := d) (n := n)
          (section43TimeSpatialProductSource d n g κ).f) τ)) ξ =
      g.f τ * (SchwartzMap.fourierTransformCLM ℂ κ.1) ξ
  rw [partialEval₂_section43TimeSpatialProductSource]
  rw [(SchwartzMap.fourierTransformCLM ℂ).map_smul]
  simp [smul_eq_mul]

/-- A difference-coordinate source `g` represents a time-Laplace /
spatial-Fourier transform `Φ` on the Section 4.3 positive-energy surface. -/
def section43TimeLaplaceSpatialFourierRepresentative
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSpatialSource d n)
    (Φ : SchwartzNPoint d n) : Prop :=
  ∀ q : NPointDomain d n, q ∈ section43PositiveEnergyRegion d n →
    Φ q =
      ∫ τ : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
          partialFourierSpatial_fun
            (d := d) (n := n) g.f
            (τ, section43QSpatial (d := d) (n := n) q)

/-- Product sources represent the tensor product of the finite-time Laplace
representative and the spatial Fourier transform of the compact spatial
source. -/
theorem section43TimeLaplaceSpatialFourierRepresentative_productSource
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n) :
    section43TimeLaplaceSpatialFourierRepresentative d n
      (section43TimeSpatialProductSource d n g κ)
      (section43NPointTimeSpatialTensor d n
        (section43IteratedLaplaceSchwartzRepresentative n g)
        (SchwartzMap.fourierTransformCLM ℂ κ.1)) := by
  intro q hq
  have hσ :
      section43QTime (d := d) (n := n) q ∈
        section43TimePositiveRegion n := by
    intro i
    simpa [section43PositiveEnergyRegion, section43QTime, nPointTimeSpatialCLE] using hq i
  rw [section43NPointTimeSpatialTensor_apply]
  rw [section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ]
  unfold section43IteratedLaplaceRaw
  rw [show
      (∫ τ : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
          partialFourierSpatial_fun
            (d := d) (n := n)
            (section43TimeSpatialProductSource d n g κ).f
            (τ, section43QSpatial (d := d) (n := n) q)) =
      (∫ τ : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
          g.f τ) *
        (SchwartzMap.fourierTransformCLM ℂ κ.1)
          (section43QSpatial (d := d) (n := n) q) by
    calc
      (∫ τ : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
          partialFourierSpatial_fun
            (d := d) (n := n)
            (section43TimeSpatialProductSource d n g κ).f
            (τ, section43QSpatial (d := d) (n := n) q))
          =
        ∫ τ : Fin n → ℝ,
          (Complex.exp
            (-(∑ i : Fin n,
              (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
            g.f τ) *
          (SchwartzMap.fourierTransformCLM ℂ κ.1)
            (section43QSpatial (d := d) (n := n) q) := by
            congr with τ
            rw [partialFourierSpatial_fun_section43TimeSpatialProductSource]
            ring
      _ =
        (∫ τ : Fin n → ℝ,
          Complex.exp
            (-(∑ i : Fin n,
              (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
            g.f τ) *
          (SchwartzMap.fourierTransformCLM ℂ κ.1)
            (section43QSpatial (d := d) (n := n) q) :=
            MeasureTheory.integral_mul_const
              ((SchwartzMap.fourierTransformCLM ℂ κ.1)
                (section43QSpatial (d := d) (n := n) q))
              (fun τ : Fin n → ℝ =>
                Complex.exp
                  (-(∑ i : Fin n,
                    (τ i : ℂ) *
                      (section43QTime (d := d) (n := n) q i : ℂ))) *
                  g.f τ)]

/-- If two time factors agree in the finite-time positive quotient, then their
transported time/spatial tensors agree in the Section 4.3 positive-energy
quotient after pairing with any fixed spatial factor. -/
theorem section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
    (d n : ℕ) [NeZero d]
    {φ ψ : SchwartzMap (Fin n → ℝ) ℂ}
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hφψ :
      section43TimePositiveQuotientMap n φ =
        section43TimePositiveQuotientMap n ψ) :
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n φ χ) =
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n ψ χ) := by
  apply section43PositiveEnergyQuotientMap_eq_of_eqOn_region (d := d)
  intro q hq
  have hσ :
      section43QTime (d := d) (n := n) q ∈
        section43TimePositiveRegion n := by
    intro i
    simpa [section43PositiveEnergyRegion, section43QTime, nPointTimeSpatialCLE] using hq i
  have hφψ_point :
      φ (section43QTime (d := d) (n := n) q) =
        ψ (section43QTime (d := d) (n := n) q) :=
    eqOn_region_of_section43TimePositiveQuotientMap_eq hφψ hσ
  simp [section43NPointTimeSpatialTensor_apply, hφψ_point]

/-- Each restricted time/spatial tensor generator has an explicit compact
time/spatial source representative after passing to the positive-energy
quotient. -/
theorem section43NPointTimeSpatialTensor_mem_timeLaplaceSpatialFourierTarget
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hφ :
      φ ∈ ((section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n)))
    (hχ : χ ∈ section43SpatialFourierCompactRange d n) :
    ∃ (G : Section43CompactStrictPositiveTimeSpatialSource d n)
      (Ψ : SchwartzNPoint d n),
      section43TimeLaplaceSpatialFourierRepresentative d n G Ψ ∧
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n φ χ) =
      section43PositiveEnergyQuotientMap (d := d) n Ψ := by
  rcases hφ with ⟨g, hg⟩
  rcases hχ with ⟨κ, rfl⟩
  let Ψt := section43IteratedLaplaceSchwartzRepresentative n g
  let Ψ : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n Ψt
      (SchwartzMap.fourierTransformCLM ℂ κ.1)
  refine ⟨section43TimeSpatialProductSource d n g κ, Ψ, ?_, ?_⟩
  · exact section43TimeLaplaceSpatialFourierRepresentative_productSource d n g κ
  · have hΨt_rep : section43IteratedLaplaceRepresentative n g Ψt := by
      intro σ hσ
      exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
    have hcompact :
        section43IteratedLaplaceCompactTransform n g =
          section43TimePositiveQuotientMap n Ψt :=
      section43IteratedLaplaceCompactTransform_eq_quotient n g Ψt hΨt_rep
    change section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n φ
          (SchwartzMap.fourierTransformCLM ℂ κ.1)) =
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n Ψt
          (SchwartzMap.fourierTransformCLM ℂ κ.1))
    exact
      section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
        d n (SchwartzMap.fourierTransformCLM ℂ κ.1)
        (hg.symm.trans hcompact)

end OSReconstruction
