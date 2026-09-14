import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanDensity

/-!
# Convex complex charts with Euclidean overlap points

Complexify the existing proper-rotation/order charts before Wick rotation.
Each domain is an open convex preimage of the physical product tube. Taking
real parts preserves membership: it keeps the rotated imaginary time gaps
and removes all rotated imaginary spatial components. Consequently every
nonempty overlap meets the totally real Euclidean slice.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

variable {d k : Nat}

def osiiComplexEuclideanOrderCLM (i : OSIIEuclideanOrderIndex d k) :
    (Fin (k + 1) -> Fin (d + 1) -> Complex) →L[Complex]
      (Fin (k + 1) -> Fin (d + 1) -> Complex) :=
  ContinuousLinearMap.pi fun j =>
    (Matrix.toLin' (i.1.val.map Complex.ofReal)).toContinuousLinearMap.comp
      (ContinuousLinearMap.proj (i.2 j))

@[simp] theorem osiiComplexEuclideanOrderCLM_apply
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (j : Fin (k + 1)) :
    osiiComplexEuclideanOrderCLM i z j =
      (i.1.val.map Complex.ofReal).mulVec (z (i.2 j)) := rfl

theorem osiiComplexEuclideanOrderCLM_realToComplex
    (i : OSIIEuclideanOrderIndex d k) (x : NPointDomain d (k + 1)) :
    osiiComplexEuclideanOrderCLM i (SCV.realToComplexProduct x) =
      SCV.realToComplexProduct (osiiEuclideanOrderAction i x) := by
  ext j mu
  simp [osiiComplexEuclideanOrderCLM_apply, osiiEuclideanOrderAction,
    SCV.realToComplexProduct, Matrix.mulVec, dotProduct, Complex.ofReal_sum]

theorem osiiComplexEuclideanOrderCLM_re
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    (fun j mu => (osiiComplexEuclideanOrderCLM i z j mu).re) =
      osiiEuclideanOrderAction i (fun j mu => (z j mu).re) := by
  ext j mu
  simp [osiiComplexEuclideanOrderCLM_apply, osiiEuclideanOrderAction,
    Matrix.mulVec, dotProduct]

variable [NeZero d]

def osiiEuclideanOrderComplexTubeMap (i : OSIIEuclideanOrderIndex d k) :
    (Fin (k + 1) -> Fin (d + 1) -> Complex) →L[Complex]
      (Fin k -> Fin (d + 1) -> Complex) :=
  (ContinuousLinearMap.pi fun j =>
    (osiiAxisPairWickBlockCLE (d := d)).toContinuousLinearMap.comp
      (ContinuousLinearMap.proj j)).comp
    ((BHW.reducedDiffMap (k + 1) d).comp (osiiComplexEuclideanOrderCLM i))

@[simp] theorem osiiEuclideanOrderComplexTubeMap_apply
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (j : Fin k) :
    osiiEuclideanOrderComplexTubeMap i z j =
      osiiAxisPairWickBlock
        (BHW.reducedDiffMap (k + 1) d (osiiComplexEuclideanOrderCLM i z) j) := by
  exact osiiAxisPairWickBlockCLE_apply _

theorem osiiEuclideanOrderComplexTubeMap_realToComplex
    (i : OSIIEuclideanOrderIndex d k) (x : NPointDomain d (k + 1)) :
    osiiEuclideanOrderComplexTubeMap i (SCV.realToComplexProduct x) =
      fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d (osiiEuclideanOrderAction i x) j) := by
  ext j mu
  rw [osiiEuclideanOrderComplexTubeMap_apply, osiiComplexEuclideanOrderCLM_realToComplex]
  have hdiff : BHW.reducedDiffMap (k + 1) d
      (SCV.realToComplexProduct (osiiEuclideanOrderAction i x)) j =
      fun nu => (BHW.reducedDiffMapReal (k + 1) d (osiiEuclideanOrderAction i x) j nu : Complex) := by
    ext nu
    rw [BHW.reducedDiffMap_eq_successive_differences]
    change ((osiiEuclideanOrderAction i x) j.succ nu : Complex) -
      ((osiiEuclideanOrderAction i x) j.castSucc nu : Complex) =
      (((osiiEuclideanOrderAction i x) j.succ nu -
        (osiiEuclideanOrderAction i x) j.castSucc nu : Real) : Complex)
    simp
  rw [hdiff]
  refine Fin.cases ?_ (fun a => ?_) mu
  · simp [osiiAxisPairWickBlock, wickRotatePoint]
  · simp [osiiAxisPairWickBlock, wickRotatePoint]

theorem osiiEuclideanOrderComplexTubeMap_time_im
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (j : Fin k) :
    (osiiEuclideanOrderComplexTubeMap i z j 0).im =
      BHW.reducedDiffMapReal (k + 1) d
        (osiiEuclideanOrderAction i (fun a mu => (z a mu).re)) j 0 := by
  rw [osiiEuclideanOrderComplexTubeMap_apply]
  change (I * BHW.reducedDiffMap (k + 1) d (osiiComplexEuclideanOrderCLM i z) j 0).im = _
  rw [BHW.reducedDiffMap_eq_successive_differences]
  have h := osiiComplexEuclideanOrderCLM_re i z
  have ha := congrFun (congrFun h j.succ) 0
  have hb := congrFun (congrFun h j.castSucc) 0
  change _ = (osiiEuclideanOrderAction i (fun a mu => (z a mu).re)) j.succ 0 -
    (osiiEuclideanOrderAction i (fun a mu => (z a mu).re)) j.castSucc 0
  simpa using congrArg₂ (fun a b : Real => a - b) ha hb

def osiiEuclideanOrderComplexRegion (i : OSIIEuclideanOrderIndex d k) :
    Set (Fin (k + 1) -> Fin (d + 1) -> Complex) :=
  osiiEuclideanOrderComplexTubeMap i ⁻¹' TubeDomainSetPi (BHW.ProductForwardConeReal d k)

theorem isOpen_osiiEuclideanOrderComplexRegion (i : OSIIEuclideanOrderIndex d k) :
    IsOpen (osiiEuclideanOrderComplexRegion i) :=
  (BHW.isOpen_productForwardCone (n := k) (d := d)).preimage
    (osiiEuclideanOrderComplexTubeMap i).continuous

omit [NeZero d] in
theorem convex_osiiEuclideanOrderComplexRegion (i : OSIIEuclideanOrderIndex d k) :
    Convex Real (osiiEuclideanOrderComplexRegion i) :=
  (BHW.productForwardCone_convex (n := k) (d := d)).linear_preimage
    ((osiiEuclideanOrderComplexTubeMap i).restrictScalars Real).toLinearMap

theorem osiiEuclideanOrderComplexRegion_realToComplex_iff
    (i : OSIIEuclideanOrderIndex d k) (x : NPointDomain d (k + 1)) :
    SCV.realToComplexProduct x ∈ osiiEuclideanOrderComplexRegion i ↔
      x ∈ osiiEuclideanOrderRegion i := by
  change osiiEuclideanOrderComplexTubeMap i (SCV.realToComplexProduct x) ∈
    TubeDomainSetPi (BHW.ProductForwardConeReal d k) ↔ x ∈ osiiEuclideanOrderRegion i
  rw [osiiEuclideanOrderComplexTubeMap_realToComplex]
  constructor
  · intro hx j
    simpa [wickRotatePoint] using (hx j).1
  · exact fun hx => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive _ hx

theorem osiiEuclideanOrderComplexRegion_realPart_mem
    (i : OSIIEuclideanOrderIndex d k) {z : Fin (k + 1) -> Fin (d + 1) -> Complex}
    (hz : z ∈ osiiEuclideanOrderComplexRegion i) :
    SCV.realToComplexProduct (fun j mu => (z j mu).re) ∈ osiiEuclideanOrderComplexRegion i := by
  apply (osiiEuclideanOrderComplexRegion_realToComplex_iff i _).mpr
  intro j
  change 0 < BHW.reducedDiffMapReal (k + 1) d
    (osiiEuclideanOrderAction i (fun a mu => (z a mu).re)) j 0
  rw [← osiiEuclideanOrderComplexTubeMap_time_im]
  exact (hz j).1

theorem osiiEuclideanOrderComplexTubeMap_perm
    (i : OSIIEuclideanOrderIndex d k) (sigma : Equiv.Perm (Fin (k + 1)))
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    osiiEuclideanOrderComplexTubeMap i (fun j => z (sigma j)) =
      osiiEuclideanOrderComplexTubeMap (i.1, i.2.trans sigma) z := by
  have h : osiiComplexEuclideanOrderCLM i (fun j => z (sigma j)) =
      osiiComplexEuclideanOrderCLM (i.1, i.2.trans sigma) z := by
    ext j mu
    rfl
  ext j mu
  simp only [osiiEuclideanOrderComplexTubeMap_apply, h]

theorem osiiEuclideanOrderComplexTubeMap_translate
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (a : Fin (d + 1) -> Complex) :
    osiiEuclideanOrderComplexTubeMap i (fun j => z j + a) = osiiEuclideanOrderComplexTubeMap i z := by
  have h : osiiComplexEuclideanOrderCLM i (fun j => z j + a) =
      fun j mu => osiiComplexEuclideanOrderCLM i z j mu +
        (i.1.val.map Complex.ofReal).mulVec a mu := by
    ext j mu
    simp [osiiComplexEuclideanOrderCLM_apply, Matrix.mulVec_add]
  ext j mu
  rw [osiiEuclideanOrderComplexTubeMap_apply, osiiEuclideanOrderComplexTubeMap_apply, h,
    BHW.reducedDiffMap_translate_uniform_eq]

theorem osiiEuclideanOrderComplexRegion_translate_iff
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (a : Fin (d + 1) -> Complex) :
    (fun j => z j + a) ∈ osiiEuclideanOrderComplexRegion i ↔ z ∈ osiiEuclideanOrderComplexRegion i := by
  change osiiEuclideanOrderComplexTubeMap i (fun j => z j + a) ∈
    TubeDomainSetPi (BHW.ProductForwardConeReal d k) ↔
      osiiEuclideanOrderComplexTubeMap i z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)
  rw [osiiEuclideanOrderComplexTubeMap_translate]

def osiiEuclideanComplexDomain (d k : Nat) [NeZero d] :
    Set (Fin (k + 1) -> Fin (d + 1) -> Complex) :=
  ⋃ i : OSIIEuclideanOrderIndex d k, osiiEuclideanOrderComplexRegion i

theorem isOpen_osiiEuclideanComplexDomain : IsOpen (osiiEuclideanComplexDomain d k) :=
  isOpen_iUnion isOpen_osiiEuclideanOrderComplexRegion

theorem osiiEuclideanComplexDomain_realToComplex_iff (x : NPointDomain d (k + 1)) :
    SCV.realToComplexProduct x ∈ osiiEuclideanComplexDomain d k ↔
      x ∉ CoincidenceLocus d (k + 1) := by
  rw [osiiEuclideanComplexDomain, Set.mem_iUnion]
  simp_rw [osiiEuclideanOrderComplexRegion_realToComplex_iff]
  simpa only [Set.mem_iUnion] using
    (Set.ext_iff.mp (iUnion_osiiEuclideanOrderRegion (d := d) (k := k)) x)

theorem osiiEuclideanComplexDomain_perm_iff
    (sigma : Equiv.Perm (Fin (k + 1))) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    (fun j => z (sigma j)) ∈ osiiEuclideanComplexDomain d k ↔
      z ∈ osiiEuclideanComplexDomain d k := by
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_iUnion.mpr ⟨(i.1, i.2.trans sigma), ?_⟩
    change osiiEuclideanOrderComplexTubeMap (i.1, i.2.trans sigma) z ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k)
    rw [← osiiEuclideanOrderComplexTubeMap_perm]
    exact hi
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_iUnion.mpr ⟨(i.1, i.2.trans sigma.symm), ?_⟩
    change osiiEuclideanOrderComplexTubeMap (i.1, i.2.trans sigma.symm) (fun j => z (sigma j)) ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k)
    rw [osiiEuclideanOrderComplexTubeMap_perm]
    have hsigma : (i.2.trans sigma.symm).trans sigma = i.2 := by ext a; simp
    rw [hsigma]
    exact hi

theorem osiiEuclideanComplexDomain_translate_iff
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) (a : Fin (d + 1) -> Complex) :
    (fun j => z j + a) ∈ osiiEuclideanComplexDomain d k ↔ z ∈ osiiEuclideanComplexDomain d k := by
  simp only [osiiEuclideanComplexDomain, Set.mem_iUnion, osiiEuclideanOrderComplexRegion_translate_iff]

def osiiIdentityEuclideanOrderIndex (d k : Nat) : OSIIEuclideanOrderIndex d k :=
  (⟨1, by simp, by simp⟩, Equiv.refl _)

theorem osiiEuclideanOrderComplexTubeMap_identity_inverseWick
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    osiiEuclideanOrderComplexTubeMap (osiiIdentityEuclideanOrderIndex d k)
        (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j)) =
      BHW.reducedDiffMap (k + 1) d z := by
  have hact : osiiComplexEuclideanOrderCLM (osiiIdentityEuclideanOrderIndex d k)
        (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j)) =
      fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j) := by
    ext j mu
    simp [osiiComplexEuclideanOrderCLM_apply, osiiIdentityEuclideanOrderIndex]
  ext j mu
  rw [osiiEuclideanOrderComplexTubeMap_apply, hact, ← osiiAxisPairWickBlockCLE_apply]
  change (osiiAxisPairWickBlockCLE
    ((osiiAxisPairWickBlockCLE (d := d)).symm (z j.succ) -
      (osiiAxisPairWickBlockCLE (d := d)).symm (z j.castSucc))) mu =
    (z j.succ - z j.castSucc) mu
  rw [← map_sub, ContinuousLinearEquiv.apply_symm_apply]

end OSReconstruction
