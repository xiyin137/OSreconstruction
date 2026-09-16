#!/usr/bin/env bash
set -euo pipefail

comparator_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
project_dir="$(cd "$comparator_dir/../.." && pwd -P)"
source "$comparator_dir/tool-versions.sh"
source "$comparator_dir/paths.sh"
tools_dir="${OS_COMPARATOR_TOOLS_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/osreconstruction-comparator}"
case "$tools_dir" in
  /*) ;;
  *) echo "OS_COMPARATOR_TOOLS_DIR must be an absolute path." >&2; exit 2 ;;
esac

if [[ "$(cat "$project_dir/lean-toolchain")" != "$project_lean_toolchain" ]]; then
  echo "The project's Lean version changed; update the pinned exporter first." >&2
  exit 1
fi

checkout() {
  local repository="$1" revision="$2" destination="$3"
  if [[ -e "$destination" || -L "$destination" ]]; then
    destination="$(comparator_resolve_tool_directory "$destination" "$lake_directory")" || return 1
  else
    git clone --no-checkout "$repository" "$destination"
    git -C "$destination" checkout --detach "$revision"
  fi
  if [[ "$(git -C "$destination" rev-parse HEAD)" != "$revision" ]] ||
      [[ -n "$(git -C "$destination" status --porcelain --untracked-files=no)" ]]; then
    echo "Expected a clean pinned tool checkout: $destination" >&2
    exit 1
  fi
}

mkdir -p "$project_dir/.lake" "$tools_dir"
lake_directory="$(comparator_resolve_directory "$project_dir/.lake")"
tools_dir="$(comparator_resolve_tool_directory "$tools_dir" "$lake_directory")"
checkout https://github.com/leanprover/comparator.git "$comparator_revision" \
  "$tools_dir/comparator-$comparator_revision"
checkout https://github.com/leanprover/lean4export.git "$exporter_revision" \
  "$tools_dir/lean4export-$exporter_revision"
comparator_checkout="$(comparator_resolve_tool_directory "$tools_dir/comparator-$comparator_revision" "$lake_directory")"
exporter_checkout="$(comparator_resolve_tool_directory "$tools_dir/lean4export-$exporter_revision" "$lake_directory")"
(cd "$comparator_checkout" && lake build comparator)
(cd "$exporter_checkout" && lake build lean4export)

if [[ "${1:-}" != --development ]]; then
  if [[ "$(uname -s)" != Linux ]]; then
    echo "Sandboxed verification requires Linux. Use --development explicitly on macOS." >&2
    exit 1
  fi
  command -v go >/dev/null || {
    echo "Install Go 1.24 or newer to build the pinned Landrun sandbox." >&2
    exit 1
  }
  checkout https://github.com/Zouuup/landrun.git "$landrun_revision" \
    "$tools_dir/landrun-$landrun_revision"
  landrun_checkout="$(comparator_resolve_tool_directory "$tools_dir/landrun-$landrun_revision" "$lake_directory")"
  (cd "$landrun_checkout" && go build -o landrun ./cmd/landrun)
fi
