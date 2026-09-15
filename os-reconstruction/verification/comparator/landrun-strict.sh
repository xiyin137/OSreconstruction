#!/usr/bin/env bash
# Comparator requests --best-effort by default. Refuse silent sandbox downgrade:
# the pinned Landrun must support its complete requested Landlock policy.
set -euo pipefail
: "${OS_COMPARATOR_LANDRUN:?The runner must supply the pinned Landrun binary}"
landrun_args=()
for argument in "$@"; do
  [[ "$argument" == --best-effort ]] || landrun_args+=("$argument")
done
exec "$OS_COMPARATOR_LANDRUN" "${landrun_args[@]}"
