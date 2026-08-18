#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

if [[ "${LUFFS_VERIFY_EXPORTED_CHECKOUT:-0}" != 1 ]]; then
  verify_root="$(mktemp -d)"
  trap 'rm -rf "$verify_root"' EXIT
  git -C "$repo_root" archive HEAD | tar -x -C "$verify_root"
  LUFFS_VERIFY_EXPORTED_CHECKOUT=1 "$verify_root/scripts/verify-clean.sh"
  exit
fi

cd "$repo_root"

cargo test --all-targets
lake_bin="$(command -v lake || true)"
if [[ -z "$lake_bin" ]]; then
  elan_root="${ELAN_HOME:-${HOME}/.elan}"
  lake_bin="$elan_root/bin/lake"
fi
if [[ ! -x "$lake_bin" ]]; then
  echo 'lake was not found; install the pinned Lean toolchain with elan' >&2
  exit 1
fi
"$lake_bin" build

for source in examples/*.luffs stdlib/*.luffs; do
  stem="$(basename "$source" .luffs)"
  cargo run --quiet -- emit "$source"
  "$lake_bin" env lean "build/$stem.lean"
  if [[ "$source" == examples/* ]]; then
    output="build/$stem"
    rustc --edition=2024 -O "build/$stem.rs" -o "$output"
  else
    output="build/lib$stem.rlib"
    rustc --edition=2024 -O --crate-type=lib "build/$stem.rs" -o "$output"
  fi
done

if grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
    lean src stdlib examples; then
  echo 'verification placeholders are forbidden' >&2
  exit 1
fi
