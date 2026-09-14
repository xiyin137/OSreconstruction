import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeReconstruction

/-!
# Public OS Reconstruction

The public E-to-R output uses the native OS-built full-Schwartz family.
Assembly lives downstream of the native proof to avoid importing it back
through the legacy analytic utilities on which that proof still depends.
-/

noncomputable section

variable {d : ℕ} [NeZero d]

/-- OS reconstruction with all distributional Wightman axioms, including
locality and clustering, from the original zero-diagonal Euclidean input. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ Wfn : WightmanFunctions d, IsWickRotationPair OS.schwinger Wfn.W := by
  obtain ⟨W, hpair, hnorm, htrans, hlor, hspec, htube, hlocal, hpos,
    hherm, _hreal, hcluster, _hunique⟩ :=
      OSReconstruction.exists_osii_native_reconstruction OS lgc
  exact ⟨{
    W := fun n f => W n f
    linear := fun n => ⟨(W n).map_add, (W n).map_smul⟩
    tempered := fun n => (W n).continuous
    normalized := hnorm
    translation_invariant := htrans
    lorentz_covariant := hlor
    spectrum_condition := htube
    spectral_support := hspec
    locally_commutative := hlocal
    positive_definite := hpos
    hermitian := hherm
    cluster := hcluster }, hpair⟩

/-- The full native reconstruction; locality and clustering are proved, not inputs. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : WightmanFunctions d :=
  (os_to_wightman_full OS lgc).choose

theorem constructWightmanFunctions_isWickRotationPair
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    IsWickRotationPair OS.schwinger (constructWightmanFunctions OS lgc).W :=
  (os_to_wightman_full OS lgc).choose_spec

/-- Forget locality and clustering from the same native full reconstruction. -/
def constructWightmanFunctionsCore (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : WightmanFunctionsCore d where
  W := (constructWightmanFunctions OS lgc).W
  linear := (constructWightmanFunctions OS lgc).linear
  tempered := (constructWightmanFunctions OS lgc).tempered
  normalized := (constructWightmanFunctions OS lgc).normalized
  translation_invariant := (constructWightmanFunctions OS lgc).translation_invariant
  lorentz_covariant := (constructWightmanFunctions OS lgc).lorentz_covariant
  spectrum_condition := (constructWightmanFunctions OS lgc).spectrum_condition
  spectral_support := (constructWightmanFunctions OS lgc).spectral_support
  positive_definite := (constructWightmanFunctions OS lgc).positive_definite
  hermitian := (constructWightmanFunctions OS lgc).hermitian

end
