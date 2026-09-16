#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

case "${1:-full}" in
  quick)
    ruby verification/source_check.rb
    ;;
  contracts)
    ruby verification/source_check.rb
    lake build OSReconstruction.Wightman.Reconstruction.Main Challenge Solution
    lake env lean verification/Contracts.lean
    ;;
  comparator)
    shift
    exec bash verification/comparator/run.sh "$@"
    ;;
  full)
    ruby verification/source_check.rb
    lake build
    lake build Challenge Solution
    lake env lean verification/Contracts.lean
    ;;
  *)
    printf 'Usage: bash verification/check.sh quick|contracts|full|comparator [--development]\n' >&2
    exit 2
    ;;
esac
