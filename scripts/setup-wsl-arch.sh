#!/usr/bin/env bash
set -euo pipefail

# Reproducible Arch Linux setup for this Lean project.
# Run this script inside the Arch WSL distribution as a normal interactive user.

LEAN_TOOLCHAIN="leanprover/lean4:v4.31.0"

if ! command -v curl >/dev/null || ! command -v git >/dev/null; then
  if [[ "$EUID" -eq 0 ]]; then
    pacman --needed --noconfirm -S curl git base-devel
  else
    sudo pacman --needed --noconfirm -S curl git base-devel
  fi
fi

if ! command -v elan >/dev/null; then
  curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$LEAN_TOOLCHAIN"
fi

export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$LEAN_TOOLCHAIN"
elan default "$LEAN_TOOLCHAIN"

printf 'Elan: '
elan --version
printf 'Lean: '
lean --version
printf 'Lake: '
lake --version

echo "WSL Lean toolchain is ready. Run scripts/build-wsl.sh from the repository root."
