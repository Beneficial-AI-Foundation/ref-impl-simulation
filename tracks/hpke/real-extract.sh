#!/usr/bin/env bash
# Charon + Aeneas on hpke-rs (generic over HpkeCrypto), all pub items.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd)
AE=$T/../../.aeneas
mkdir -p "$T/logs"
export CARGO_TARGET_DIR=$T/target
cd $T/real-work
touch src/lib.rs
$AE/charon cargo --preset=aeneas --hide-marker-traits ${REAL_START:---start-from-pub} --opaque hpke_rs::util::xor_bytes ${REAL_EXTRA:-} \
  --dest-file $T/logs/real.llbc > $T/logs/charon-real.log 2>&1
rm -rf $T/lean/Real
$AE/aeneas -backend lean -split-files -dest $T/lean -subdir Real -namespace Real -no-progress-bar $T/logs/real.llbc > $T/logs/aeneas-real.log 2>&1 || true
