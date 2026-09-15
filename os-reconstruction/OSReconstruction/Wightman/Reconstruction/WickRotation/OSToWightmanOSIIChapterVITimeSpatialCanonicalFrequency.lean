/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullFrequencyTemporalSupport











noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

private def osiiFlatProductSplitMeasurableEquiv (a b : Nat) :
    (Fin (a + b) -> Real) ≃ᵐ
      ((Fin a -> Real) × (Fin b -> Real)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (a + b) => Real)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin a ⊕ Fin b => Real))

private theorem osiiFlatProductSplitMeasurableEquiv_measurePreserving
    (a b : Nat) :
    MeasurePreserving
      (osiiFlatProductSplitMeasurableEquiv a b)
      (volume : Measure (Fin (a + b) -> Real))
      ((volume : Measure (Fin a -> Real)).prod
        (volume : Measure (Fin b -> Real))) := by
  let e1 := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (a + b) => Real)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
  have he1 : MeasurePreserving e1 volume volume := by
    simpa [e1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin (a + b) => Real)
        (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  have he2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin a ⊕ Fin b => Real))
      volume
      ((volume : Measure (Fin a -> Real)).prod
        (volume : Measure (Fin b -> Real))) := by
    have h := MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin a ⊕ Fin b => Real)
    rw [Measure.volume_eq_prod] at h
    exact h
  refine (he2.comp (he1.symm e1)).congr
    (osiiFlatProductSplitMeasurableEquiv a b).measurable ?_
  filter_upwards with x
  rfl

private theorem osiiFlatProductSplitMeasurableEquiv_fst_eq_splitFirst
    (a b : Nat) (x : Fin (a + b) -> Real) :
    (osiiFlatProductSplitMeasurableEquiv a b x).1 =
      splitFirst a b x := by
  ext i
  rw [osiiFlatProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (a + b) => Real)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
        (Sum.inl i) =
    x (Fin.castAdd b i)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (a + b) => Real)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
    ((Equiv.piCongrLeft (fun _ : Fin (a + b) => Real)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
    (Sum.inl i)
  rw [← h]
  simp [finSumFinEquiv_apply_left]

private theorem osiiFlatProductSplitMeasurableEquiv_snd_eq_splitLast
    (a b : Nat) (x : Fin (a + b) -> Real) :
    (osiiFlatProductSplitMeasurableEquiv a b x).2 =
      splitLast a b x := by
  ext j
  rw [osiiFlatProductSplitMeasurableEquiv]
  simp only [MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi]
  change ((Equiv.piCongrLeft (fun _ : Fin (a + b) => Real)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
        (Sum.inr j) =
    x (Fin.natAdd a j)
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (a + b) => Real)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
    ((Equiv.piCongrLeft (fun _ : Fin (a + b) => Real)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm x)
    (Sum.inr j)
  rw [← h]
  simp [finSumFinEquiv_apply_right]

private theorem osiiFlat_pair_eq_split_pair
    (a b : Nat) (x xi : Fin (a + b) -> Real) :
    (∑ i : Fin (a + b), (x i : Complex) * (xi i : Complex)) =
      (∑ i : Fin a,
        (splitFirst (E := Real) a b x i : Complex) *
          (splitFirst (E := Real) a b xi i : Complex)) +
      (∑ j : Fin b,
        (splitLast (E := Real) a b x j : Complex) *
          (splitLast (E := Real) a b xi j : Complex)) := by
  rw [Fin.sum_univ_add]
  rfl

/-- The flat physics Fourier transform factors over the standard first/last
coordinate tensor product. -/
theorem physicsFourierFlatCLM_tensorProduct_apply
    (a b : Nat)
    (F : SchwartzMap (Fin a -> Real) Complex)
    (G : SchwartzMap (Fin b -> Real) Complex)
    (xi : Fin (a + b) -> Real) :
    physicsFourierFlatCLM (F.tensorProduct G) xi =
      physicsFourierFlatCLM F (splitFirst a b xi) *
        physicsFourierFlatCLM G (splitLast a b xi) := by
  rw [← physicsFourierFlatCLM_integral,
    ← physicsFourierFlatCLM_integral,
    ← physicsFourierFlatCLM_integral]
  let e := osiiFlatProductSplitMeasurableEquiv a b
  let xiL := splitFirst a b xi
  let xiR := splitLast a b xi
  let g : ((Fin a -> Real) × (Fin b -> Real)) -> Complex := fun p =>
    Complex.exp (Complex.I *
      ((∑ i, (p.1 i : Complex) * (xiL i : Complex)) +
       (∑ j, (p.2 j : Complex) * (xiR j : Complex)))) *
      (F p.1 * G p.2)
  have he := osiiFlatProductSplitMeasurableEquiv_measurePreserving a b
  calc
    (∫ x : Fin (a + b) -> Real,
      Complex.exp (Complex.I * ∑ i,
        (x i : Complex) * (xi i : Complex)) *
        (F.tensorProduct G) x)
        = ∫ x : Fin (a + b) -> Real, g (e x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [g]
          rw [osiiFlatProductSplitMeasurableEquiv_fst_eq_splitFirst,
            osiiFlatProductSplitMeasurableEquiv_snd_eq_splitLast,
            osiiFlat_pair_eq_split_pair]
    _ = ∫ p : (Fin a -> Real) × (Fin b -> Real), g p := by
          exact he.integral_comp' (g := g)
    _ = ∫ p : (Fin a -> Real) × (Fin b -> Real),
          (Complex.exp (Complex.I * ∑ i,
            (p.1 i : Complex) * (xiL i : Complex)) * F p.1) *
          (Complex.exp (Complex.I * ∑ j,
            (p.2 j : Complex) * (xiR j : Complex)) * G p.2) := by
          apply integral_congr_ae
          filter_upwards with p
          dsimp [g]
          rw [mul_add, Complex.exp_add]
          ring
    _ = (∫ x : Fin a -> Real,
          Complex.exp (Complex.I * ∑ i,
            (x i : Complex) * (xiL i : Complex)) * F x) *
        (∫ y : Fin b -> Real,
          Complex.exp (Complex.I * ∑ j,
            (y j : Complex) * (xiR j : Complex)) * G y) := by
          rw [Measure.volume_eq_prod
            (Fin a -> Real) (Fin b -> Real)]
          simpa [mul_assoc] using
            (MeasureTheory.integral_prod_mul
              (μ := (volume : Measure (Fin a -> Real)))
              (ν := (volume : Measure (Fin b -> Real)))
              (f := fun x : Fin a -> Real =>
                Complex.exp (Complex.I * ∑ i,
                  (x i : Complex) * (xiL i : Complex)) * F x)
              (g := fun y : Fin b -> Real =>
                Complex.exp (Complex.I * ∑ j,
                  (y j : Complex) * (xiR j : Complex)) * G y))

/-- The explicit inverse physics Fourier transform factors over flat tensor
products. -/
theorem physicsFourierFlatInvCLM_tensorProduct
    (a b : Nat)
    (F : SchwartzMap (Fin a -> Real) Complex)
    (G : SchwartzMap (Fin b -> Real) Complex) :
    physicsFourierFlatInvCLM (F.tensorProduct G) =
      (physicsFourierFlatInvCLM F).tensorProduct
        (physicsFourierFlatInvCLM G) := by
  apply (Function.LeftInverse.injective
    (fun H : SchwartzMap (Fin (a + b) -> Real) Complex =>
      physicsFourierFlatInvCLM_left H))
  ext xi
  calc
    physicsFourierFlatCLM
        (physicsFourierFlatInvCLM (F.tensorProduct G)) xi =
        (F.tensorProduct G) xi := by
          rw [physicsFourierFlatCLM_inv_right]
    _ = F (splitFirst a b xi) * G (splitLast a b xi) := by
          rw [SchwartzMap.tensorProduct_apply]
    _ = physicsFourierFlatCLM (physicsFourierFlatInvCLM F)
          (splitFirst a b xi) *
        physicsFourierFlatCLM (physicsFourierFlatInvCLM G)
          (splitLast a b xi) := by
          rw [physicsFourierFlatCLM_inv_right,
            physicsFourierFlatCLM_inv_right]
    _ = physicsFourierFlatCLM
          ((physicsFourierFlatInvCLM F).tensorProduct
            (physicsFourierFlatInvCLM G)) xi := by
          rw [physicsFourierFlatCLM_tensorProduct_apply]

variable {d k : Nat} [NeZero d]

/-- Flatten a Section 4.3 time/spatial Schwartz test with time coordinates
first. -/
noncomputable def section43TimeSpatialFlatSchwartzCLM (d k : Nat) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Fin (k + k * d) -> Real) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (section43TimeSpatialFlatCLE d k).symm

/-- Unflatten a time-first flat Schwartz test back to Section 4.3 product
coordinates. -/
noncomputable def section43TimeSpatialUnflatSchwartzCLM (d k : Nat) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (section43TimeSpatialFlatCLE d k)

@[simp] theorem section43TimeSpatialFlatSchwartzCLM_timeSpatialTensor
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    section43TimeSpatialFlatSchwartzCLM d k
        (section43TimeSpatialTensor d k phi chi) =
      SchwartzMap.tensorProduct phi
        (section43SpatialFlatSchwartzCLE d k chi) := by
  ext x
  simp [section43TimeSpatialFlatSchwartzCLM, section43TimeSpatialTensor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp] theorem section43TimeSpatialUnflatSchwartzCLM_tensorProduct
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Fin (k * d) -> Real) Complex) :
    section43TimeSpatialUnflatSchwartzCLM d k
        (SchwartzMap.tensorProduct phi chi) =
      section43TimeSpatialTensor d k phi
        ((section43SpatialFlatSchwartzCLE d k).symm chi) := by
  ext p
  rcases p with ⟨tau, eta⟩
  simp [section43TimeSpatialUnflatSchwartzCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Reduced boundary distribution expressed on Section 4.3 product
coordinates. -/
def section43TimeSpatialBoundaryDistribution
    (W : SchwartzNPoint d k →L[Complex] Complex) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  W.comp
    (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).symm.toContinuousLinearMap

/-- Reduced boundary distribution expressed on the time-first flat block. -/
def section43FlatTimeSpatialBoundaryDistribution
    (W : SchwartzNPoint d k →L[Complex] Complex) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex] Complex :=
  (section43TimeSpatialBoundaryDistribution W).comp
    (section43TimeSpatialUnflatSchwartzCLM d k)

/-- Canonical physics Fourier representative of a reduced boundary, in
time-first Section 4.3 product coordinates. -/
def section43CanonicalTimeSpatialFrequencyBoundary
    (W : SchwartzNPoint d k →L[Complex] Complex) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  (section43FlatTimeSpatialBoundaryDistribution W).comp
    ((physicsFourierFlatInvCLM (m := k + k * d)).comp
      (section43TimeSpatialFlatSchwartzCLM d k))

theorem section43CanonicalTimeSpatialFrequencyBoundary_timeSpatialTensor
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    section43CanonicalTimeSpatialFrequencyBoundary W
        (section43TimeSpatialTensor d k phi chi) =
      W (section43NPointTimeSpatialTensor d k
        (physicsFourierFlatInvCLM phi)
        (section43SpatialPhysicsFourierFlatInvCLM d k chi)) := by
  change W ((nPointTimeSpatialSchwartzCLE (d := d) (n := k)).symm
    (section43TimeSpatialUnflatSchwartzCLM d k
      (physicsFourierFlatInvCLM
        (section43TimeSpatialFlatSchwartzCLM d k
          (section43TimeSpatialTensor d k phi chi))))) = _
  rw [section43TimeSpatialFlatSchwartzCLM_timeSpatialTensor,
    physicsFourierFlatInvCLM_tensorProduct,
    section43TimeSpatialUnflatSchwartzCLM_tensorProduct]
  rfl

namespace OSIIFullTimeStageVladimirovGrowthData

variable {A : OSIITimeContinuationStage d k}

/-- The assembled full-frequency boundary is exactly the canonical Fourier
representative of the reduced Chapter VI boundary in time-first coordinates. -/
theorem section43CanonicalTimeSpatialFrequencyBoundary_eq_fullFrequencyMixedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    section43CanonicalTimeSpatialFrequencyBoundary
        G.toTemperedBoundaryData.reducedBoundary =
      G.fullFrequencyMixedBoundary := by
  apply G.fullFrequencyMixedBoundary_unique
  intro phi chi
  rw [section43CanonicalTimeSpatialFrequencyBoundary_timeSpatialTensor,
    G.toTemperedBoundaryData_reducedBoundary_timeSpatialTensor]
  rfl

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
