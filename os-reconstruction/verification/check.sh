#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

case "${1:-full}" in
  quick)
    ruby verification/source_check.rb
    ;;
  contracts)
    lake build OSReconstruction.Wightman.Reconstruction.Main
    lake env lean verification/Contracts.lean
    ;;
  full)
    ruby verification/source_check.rb
    lake build
    lake env lean verification/Contracts.lean
    ;;
  *)
    printf 'Usage: bash verification/check.sh quick|contracts|full\n' >&2
    exit 2
    ;;
esac
