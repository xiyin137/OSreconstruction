import OSBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation

noncomputable section
open MeasureTheory Complex Filter Set Topology Matrix
namespace OSReconstructionAudit

def ComplexLorentz.toProduction {d : ℕ} (L : ComplexLorentz d) : ComplexLorentzGroup d :=
  ⟨L.val, L.metric_preserving, L.proper⟩

def ComplexLorentz.ofProduction {d : ℕ} (L : ComplexLorentzGroup d) : ComplexLorentz d :=
  ⟨L.val, L.metric_preserving, L.proper⟩

theorem permutedExtendedTube_eq (d n : ℕ) [NeZero d] :
    permutedExtendedTube d n = PermutedExtendedTube d n := by
  ext z
  simp only [permutedExtendedTube, PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨π, L, w, hw, hz⟩
    exact ⟨π, L.toProduction, w, hw, hz⟩
  · rintro ⟨π, L, w, hw, hz⟩
    exact ⟨π, ComplexLorentz.ofProduction L, w, hw, hz⟩

theorem translatedPET_eq (d n : ℕ) [NeZero d] :
    translatedPET d n = TranslatedPET d n := by
  simp only [translatedPET, TranslatedPET, permutedExtendedTube_eq]

/-- Existence of the independently specified extension, with no additional
hypothesis on the Wightman family. -/
theorem extensionProperty_exists {d : ℕ} [NeZero d] (A : Wightman d) (n : ℕ) :
    ∃ F, extensionProperty A n F := by
  refine ⟨(W_analytic_BHW A.toProduction n).val, ?_, ?_⟩
  · simpa only [permutedExtendedTube_eq] using
      (W_analytic_BHW A.toProduction n).property.1
  · exact (W_analytic_BHW A.toProduction n).property.2.1

/-- BHW uniqueness identifies the independently selected extension wherever
its values enter the translated constructor. -/
theorem extendedKernel_eq {d n : ℕ} [NeZero d] (A : Wightman d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ permutedExtendedTube d n) :
    extendedKernel A n z = (W_analytic_BHW A.toProduction n).val z := by
  classical
  have hex := extensionProperty_exists A n
  rw [extendedKernel, dif_pos hex]
  apply W_analytic_BHW_unique A.toProduction n hex.choose
  · simpa only [permutedExtendedTube_eq] using hex.choose_spec.1
  · exact hex.choose_spec.2
  · simpa only [permutedExtendedTube_eq] using hz

/-- The total translated kernels agree pointwise, including their zero branch. -/
theorem translatedKernel_eq {d n : ℕ} [NeZero d] (A : Wightman d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    translatedKernel A z = F_ext_on_translatedPET_total A.toProduction z := by
  classical
  by_cases hz : z ∈ translatedPET d n
  · have hz' : z ∈ TranslatedPET d n := by
      simpa only [translatedPET_eq] using hz
    rw [translatedKernel, dif_pos hz, F_ext_on_translatedPET_total, dif_pos hz']
    rw [extendedKernel_eq A _ hz.choose_spec]
    exact F_ext_value_on_translatedPET A.toProduction z hz.choose hz'.choose
      (by simpa only [permutedExtendedTube_eq] using hz.choose_spec) hz'.choose_spec
  · have hz' : z ∉ TranslatedPET d n := by
      simpa only [translatedPET_eq] using hz
    rw [translatedKernel, dif_neg hz, F_ext_on_translatedPET_total, dif_neg hz']

/-- The independent fixed constructor is exactly the production constructor,
not merely some Schwinger family with a Wick pairing. -/
theorem constructSchwinger_eq {d : ℕ} [NeZero d] (A : Wightman d) :
    constructSchwinger A = constructSchwingerFunctions A.toProduction := by
  funext n f
  unfold constructSchwinger constructSchwingerFunctions wickRotatedBoundaryPairing
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [translatedKernel_eq]
  rfl

end OSReconstructionAudit
