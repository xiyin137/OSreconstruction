#!/usr/bin/env bash
set -euo pipefail

comparator_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
project_dir="$(cd "$comparator_dir/../.." && pwd -P)"
source "$comparator_dir/tool-versions.sh"
source "$comparator_dir/paths.sh"
tools_dir="${OS_COMPARATOR_TOOLS_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/osreconstruction-comparator}"

case "${1:-}" in
  ""|--development) ;;
  *) echo "Usage: bash verification/comparator/run.sh [--development]" >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  echo "Usage: bash verification/comparator/run.sh [--development]" >&2
  exit 2
fi
if [[ "${1:-}" != --development ]]; then
  if [[ "$(uname -s)" != Linux ]]; then
    echo "Sandboxed verification requires Linux. For a local macOS check, pass --development." >&2
    exit 1
  fi
  if [[ "$(id -u)" == 0 ]]; then
    echo "Run sandboxed comparator verification as an unprivileged user." >&2
    exit 1
  fi
  command -v systemd-run >/dev/null || {
    echo "Sandboxed verification requires systemd-run with a user service manager." >&2
    exit 1
  }
fi

cd "$project_dir"
ruby verification/source_check.rb
bash "$comparator_dir/setup.sh" "$@"
lake_directory="$(comparator_resolve_directory "$project_dir/.lake")"
tools_dir="$(comparator_resolve_tool_directory "$tools_dir" "$lake_directory")"
comparator_checkout="$(comparator_resolve_tool_directory "$tools_dir/comparator-$comparator_revision" "$lake_directory")"
exporter_checkout="$(comparator_resolve_tool_directory "$tools_dir/lean4export-$exporter_revision" "$lake_directory")"
comparator_binary_directory="$(comparator_resolve_tool_directory "$comparator_checkout/.lake/build/bin" "$lake_directory")"
exporter_binary_directory="$(comparator_resolve_tool_directory "$exporter_checkout/.lake/build/bin" "$lake_directory")"
comparator_binary="$comparator_binary_directory/comparator"
export COMPARATOR_LEAN4EXPORT="$exporter_binary_directory/lean4export"

if [[ "${1:-}" == --development ]]; then
  echo "DEVELOPMENT MODE: builds and exports are unsandboxed; only statement comparison," >&2
  echo "the axiom whitelist, and Lean kernel replay are checked. No isolation claim." >&2
  export COMPARATOR_LANDRUN="$comparator_checkout/scripts/fake-landrun.sh"
  exec lake env "$comparator_binary" verification/comparator/comparator.json
fi

landrun_checkout="$(comparator_resolve_tool_directory "$tools_dir/landrun-$landrun_revision" "$lake_directory")"
export OS_COMPARATOR_LANDRUN="$landrun_checkout/landrun"
export COMPARATOR_LANDRUN="$comparator_dir/landrun-strict.sh"
exec systemd-run --user --pipe --wait --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$project_dir" \
  -E "PATH=$PATH" -E "HOME=$HOME" \
  -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
  -E "OS_COMPARATOR_LANDRUN=$OS_COMPARATOR_LANDRUN" \
  -- lake env "$comparator_binary" verification/comparator/comparator.json
