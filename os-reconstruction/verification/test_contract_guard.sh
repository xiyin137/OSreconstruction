#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

project_dir="$PWD"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/os-contract-guard.XXXXXX")"
trap 'rm -rf "$scratch_dir"' EXIT
mkdir -p "$scratch_dir/lib"

# Compile the actual audit once; the fixtures invoke it rather than a copy.
lake env lean -R "$project_dir/verification" \
  -o "$scratch_dir/lib/Contracts.olean" verification/Contracts.lean
lean_binary="$(lake env sh -c 'command -v lean')"
lean_path="$(lake env ruby -e 'puts ENV.fetch("LEAN_PATH").split(File::PATH_SEPARATOR).map { |p| File.expand_path(p) }.join(File::PATH_SEPARATOR)')"

prepare_case() {
  mkdir -p "$scratch_dir/$1"
  cat > "$scratch_dir/$1/Run.lean" <<'LEAN'
import Contracts
import AuditFixture

-- The legacy runner loads full proof bodies, as the standalone audit does.
open Lean Elab Command in
run_cmd liftCoreM <| OSReconstructionVerification.auditContracts `AuditFixture #[]
LEAN
}

prepare_case good
cat > "$scratch_dir/good/AuditFixture.lean" <<'LEAN'
module

public theorem witness : True := True.intro
LEAN
cat > "$scratch_dir/good/ExportedView.lean" <<'LEAN'
module
import AuditFixture
import Lean

-- Reproduce the representation that caused the original false positive.
open Lean in
run_cmd do
  unless (← getConstInfo `witness).isAxiom do
    throwError "Fixture must expose the proved theorem as an axiom placeholder"
LEAN

prepare_case project_axiom
cat > "$scratch_dir/project_axiom/AuditFixture.lean" <<'LEAN'
module

public axiom unjustified : True
public theorem witness : True := True.intro
LEAN

prepare_case direct_sorry
cat > "$scratch_dir/direct_sorry/AuditFixture.lean" <<'LEAN'
module

public theorem witness : True := by sorry
LEAN

prepare_case private_foreign
cat > "$scratch_dir/private_foreign/AuditFixture.lean" <<'LEAN'
module

import ForeignSupport

-- Unused by the public witness: a roots-only audit would miss this dependency.
private theorem helper : True := ForeignSupport.unjustified
public theorem witness : True := True.intro
LEAN

prepare_case generated_foreign
cat > "$scratch_dir/generated_foreign/AuditFixture.lean" <<'LEAN'
module

public import ForeignSupport

@[expose] public section

-- The exposed definition lifts this proof into witness._proof_1.
def witness : { n : Nat // n = 0 } :=
  ⟨0, by exact Eq.trans ForeignSupport.equality (Eq.refl 0)⟩
LEAN

for name in private_foreign generated_foreign; do
  cat > "$scratch_dir/$name/ForeignSupport.lean" <<'LEAN'
module

namespace ForeignSupport
public axiom unjustified : True
public axiom equality : (0 : Nat) = 0
end ForeignSupport
LEAN
done

run_case() {
  local name="$1" expected="$2" case_dir="$scratch_dir/$1" status
  for module in ForeignSupport AuditFixture; do
    if [[ -f "$case_dir/$module.lean" ]]; then
      LEAN_PATH="$case_dir:$lean_path" "$lean_binary" -R "$case_dir" \
        -o "$case_dir/$module.olean" "$case_dir/$module.lean" \
        > "$case_dir/$module.log" 2>&1 || {
          cat "$case_dir/$module.log"
          return 1
        }
    fi
  done
  if [[ -f "$case_dir/ExportedView.lean" ]]; then
    LEAN_PATH="$case_dir:$lean_path" "$lean_binary" -R "$case_dir" \
      "$case_dir/ExportedView.lean"
  fi
  if (cd "$case_dir" && LEAN_PATH="$scratch_dir/lib:$case_dir:$lean_path" \
      "$lean_binary" Run.lean > guard.log 2>&1); then
    status=0
  else
    status=$?
  fi
  if [[ -z "$expected" ]]; then
    if [[ "$status" -ne 0 ]]; then
      cat "$case_dir/guard.log"
      echo "FAIL: $name should pass" >&2
      return 1
    fi
  elif [[ "$status" -eq 0 ]] || ! ruby -e \
      'exit(File.read(ARGV[0]).include?(ARGV[1]) ? 0 : 1)' \
      "$case_dir/guard.log" "$expected"; then
    cat "$case_dir/guard.log"
    echo "FAIL: $name should reject with: $expected" >&2
    return 1
  fi
  echo "PASS: contract guard fixture $name"
}

run_case good ''
run_case project_axiom 'Project axiom in loaded package: unjustified'
run_case direct_sorry 'Admission in loaded package: witness'
run_case private_foreign 'Nonstandard transitive axioms in the package: [ForeignSupport.unjustified]'
run_case generated_foreign 'Nonstandard transitive axioms in the package: [ForeignSupport.equality]'
