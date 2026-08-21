#!/usr/bin/env bash
# Runs once, when a Codespace (or dev container) is first created.
#
# The point of this file is the guard in the middle: if the prebuilt Mathlib
# cache cannot be downloaded, `lake build` would fall back to compiling Mathlib
# from source, which takes hours and looks, from the student's side, exactly
# like a Codespace that is merely slow. Better to fail loudly and early.
set -euo pipefail

echo "==> Downloading prebuilt Mathlib (the slow step; a few minutes)"
downloaded=0
for attempt in 1 2 3; do
  if lake exe cache get; then
    downloaded=1
    break
  fi
  echo "==> Cache download failed (attempt ${attempt}/3); retrying in 15s..."
  sleep 15
done

if [ "${downloaded}" -ne 1 ]; then
  echo ""
  echo "!!  Could not download the prebuilt Mathlib cache after 3 attempts."
  echo "!!  Stopping here on purpose: continuing would compile Mathlib from"
  echo "!!  source, which takes hours."
  echo "!!"
  echo "!!  To retry by hand once the network settles:"
  echo "!!      lake exe cache get && lake build"
  exit 1
fi

echo "==> Building the tutorial"
lake build

echo ""
echo "==> Ready. Open LeanTutorial/Part1_WhatIsLean.lean to begin."
