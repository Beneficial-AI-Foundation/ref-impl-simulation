#!/usr/bin/env bash
# Regression tests for check-short-names.py. Run from any directory.
set -u
here=$(cd "$(dirname "$0")" && pwd)
fail() { echo "FAIL: $1"; exit 1; }

out=$("$here/../check-short-names.py" "$here/short-names-multiline.lean" 2>/dev/null)
code=$?
[ "$code" -eq 1 ] || fail "multiline: exit $code, expected 1"
for expected in \
  "short-names-multiline.lean:7: in foo.A.B.g: \`t\` binds to foo.A.t (intended foo.t)" \
  "short-names-multiline.lean:11: in foo.A.C.h: \`t\` binds to foo.A.t (intended foo.t)"; do
  [[ "$out" == *"$expected"* ]] || fail "multiline: missing \"$expected\" in: $out"
done

if "$here/../check-short-names.py" "$here/short-names-unreadable.lean" >/dev/null 2>&1; then
  fail "unreadable: exit 0, expected an error"
fi
echo "ok"
