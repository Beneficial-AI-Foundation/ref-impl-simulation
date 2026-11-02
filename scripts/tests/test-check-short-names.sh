#!/usr/bin/env bash
# Regression test for check-short-names.py. Run from any directory.
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$("$here/../check-short-names.py" "$here/short-names-multiline.lean" 2>/dev/null)
code=$?
expected="short-names-multiline.lean:7: in foo.A.B.g: \`t\` binds to foo.A.t (intended foo.t)"
if [ "$code" -ne 1 ] || [[ "$out" != *"$expected"* ]]; then
  echo "FAIL: exit $code, output: $out"
  exit 1
fi
echo "ok"
