#!/usr/bin/env bash
# Charon + Aeneas on the hacspec HPKE spec (shimmed), starting from KeySchedule.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd)
AE=$T/../../.aeneas
mkdir -p "$T/logs"
OPQ=""
for f in hkdf_extract hkdf_expand ecdh secret_to_public valid_private_key parse_public_key aead_encrypt aead_decrypt; do
  OPQ="$OPQ --opaque hacspec_cryptolib::$f"
done
cd $T/ref-shim/hpke
touch src/hpke.rs
RUSTFLAGS="-Zalways-encode-mir -Zmir-opt-level=0" $AE/charon cargo --preset=aeneas --hide-marker-traits \
  $OPQ --include hpke_kdf --include hpke_aead --include hpke_kem --include hacspec_lib --include hacspec_cryptolib \
  --start-from hpke::KeySchedule ${EXTRA_START:-} \
  --dest-file $T/logs/ref.llbc > $T/logs/charon-ref.log 2>&1
rm -rf $T/lean/Ref
$AE/aeneas -backend lean -split-files -dest $T/lean -subdir Ref -namespace Ref -no-progress-bar $T/logs/ref.llbc > $T/logs/aeneas-ref.log 2>&1
# Tweak: the `discriminant` attribute names its instance from the short type name at the root
# namespace, so Ref.hpke_errors.HpkeError and Real.HpkeError both define
# `instDiscriminantHpkeErrorIsize`. Ref never reads that discriminant: drop the attribute.
sed -i 's/@\[discriminant isize, rust_type "hpke_errors::HpkeError"\]/@[rust_type "hpke_errors::HpkeError"]/' $T/lean/Ref/Types.lean
