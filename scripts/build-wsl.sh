#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.toml || ! -f lean-toolchain ]]; then
  echo "Run this script from the SimonDCP repository root." >&2
  exit 1
fi

export PATH="$HOME/.elan/bin:$PATH"

# The dependencies are pinned by lake-manifest.json.  Suppressing mathlib's
# update hook avoids an unnecessary full cache download during `lake update`.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get
lake build
