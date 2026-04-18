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

end OSReconstruction
