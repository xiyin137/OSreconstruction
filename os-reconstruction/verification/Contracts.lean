import OSReconstruction
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Exact targets and standard-axiom guards for the distributable OS package. -/

noncomputable section
open OSReconstruction

-- Equality checks reject weakened target propositions, not just unproved ones.
example {d : Nat} [NeZero d] : EToRStatement d =
    (∀ (OS : OsterwalderSchraderAxioms d), OSLinearGrowthCondition d OS →
      ∃ Wfn : WightmanFunctions d, IsWickRotationPair OS.schwinger Wfn.W) := rfl

example {d : Nat} [NeZero d] : EToROSIIStatement d =
    (∀ (OS : OsterwalderSchraderAxioms d), OSIIOriginalLinearGrowthCondition d OS →
      ∃ Wfn : WightmanFunctions d,
        IsWickRotationPair OS.schwinger Wfn.W ∧
        OSIIWightmanGrowthCondition d Wfn.W ∧
        ∀ V : (n : Nat) → SchwartzNPoint d n → Complex,
          IsWickRotationPair OS.schwinger V → V = Wfn.W) := rfl

example {d : Nat} [NeZero d] : RToEStatement d constructSchwingerFunctions =
    (∀ Wfn : WightmanFunctions d, ∃ OS : OsterwalderSchraderAxioms d,
      OS.S = constructSchwingerFunctions Wfn ∧ IsWickRotationPair OS.S Wfn.W) := rfl

example {d : Nat} [NeZero d] : EToRStatement d := e_to_r_specification
example {d : Nat} [NeZero d] : EToROSIIStatement d := e_to_r_osii_specification
example {d : Nat} [NeZero d] : RToEStatement d constructSchwingerFunctions :=
  r_to_e_specification

example (OS : OsterwalderSchraderAxioms 1)
    (growth : OSIIOriginalLinearGrowthCondition 1 OS) :
    ∃ Wfn : WightmanFunctions 1,
      IsWickRotationPair OS.schwinger Wfn.W ∧
      OSIIWightmanGrowthCondition 1 Wfn.W ∧
      ∀ V : (n : Nat) → SchwartzNPoint 1 n → Complex,
        IsWickRotationPair OS.schwinger V → V = Wfn.W :=
  os_to_wightman_osii_original OS growth

example (Wfn : WightmanFunctions 1) :
    (constructOsterwalderSchraderAxioms Wfn).S = constructSchwingerFunctions Wfn := rfl

example (Wfn : WightmanFunctions 1) (f : ZeroDiagonalSchwartz 1 0)
    (g : ZeroDiagonalSchwartz 1 2) :=
  (constructOsterwalderSchraderAxioms Wfn).E4_cluster 0 2 f g

open Lean in
run_cmd do
  let env ← getEnv
  let mut localModules : Nat := 0
  for name in env.header.moduleNames do
    if (`OSReconstruction).isPrefixOf name then
      let path := System.FilePath.mk (name.toString.replace "." "/" ++ ".lean")
      unless ← path.pathExists do
        throwError "Loaded local module has no retained source: {name}"
      localModules := localModules + 1
  logInfo m!"PASS: all {localModules} loaded local modules have retained source files"
  let mut localDeclarations : Nat := 0
  let mut localNames : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if (`OSReconstruction).isPrefixOf env.header.moduleNames[index]! then
        localDeclarations := localDeclarations + 1
        localNames := localNames.push name
        if info.isAxiom then
          throwError "Project axiom in loaded package: {name}"
        if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
          throwError "Admission in loaded package: {name}"
  logInfo m!"PASS: all {localDeclarations} loaded project declarations are admission-free and contain no project axioms"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  -- `Lean.collectAxioms` is the public entry point of `Lean.Util.CollectAxioms`
  -- (the monad `CollectAxioms.M` and `collect` are module-private since Lean 4.30).
  let mut unexpected : Array Name := #[]
  for name in localNames do
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax || unexpected.contains ax do
        unexpected := unexpected.push ax
  unless unexpected.isEmpty do
    throwError "Nonstandard transitive axioms in the package: {unexpected}"
  logInfo m!"PASS: every loaded project declaration transitively uses only standard axioms"
  for decl in #[``os_to_wightman, ``os_to_wightman_full,
      ``os_to_wightman_osii, ``os_to_wightman_osii_original,
      ``constructWightmanFunctions, ``constructWightmanFunctionsCore,
      ``constructWightmanFunctions_isWickRotationPair,
      ``constructWightmanFunctions_osii_growth,
      ``OSReconstruction.osiiOriginalLinearGrowth_iff,
      ``OSReconstruction.wightman_to_os_axioms,
      ``OSReconstruction.constructOsterwalderSchraderAxioms,
      ``OSReconstruction.constructSchwingerFunctions_isWickRotationPair,
      ``OSReconstruction.e_to_r_specification,
      ``OSReconstruction.e_to_r_osii_specification,
      ``OSReconstruction.r_to_e_specification] do
    unless localNames.contains decl do
      throwError "Expected checked production root is absent: {decl}"
    logInfo m!"PASS: {decl} uses only standard axioms"

end
