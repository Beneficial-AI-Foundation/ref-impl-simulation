#!/usr/bin/env bash
# usage: run.sh <tag> <crate-dir-rel-to-track> <llbc-name> [charon args...]
set -u
T=$(cd "$(dirname "$0")" && pwd)
A=$T/../../.aeneas
tag=$1; dir=$2; name=$3; shift 3
AEARGS=${AEARGS:-}
export CARGO_TARGET_DIR=$T/target
mkdir -p $T/out/$tag $T/logs
(cd $T/$dir && $A/charon cargo --preset=aeneas "$@" --dest $T/out/$tag > $T/logs/$tag-charon.log 2>&1); echo "charon rc=$?"
grep -E "^error" $T/logs/$tag-charon.log | sort | uniq -c | head -20
rm -rf $T/out/$tag-lean
(cd $T && $A/aeneas -backend lean -split-files -loops-to-rec -no-progress-bar $AEARGS -dest out/$tag-lean out/$tag/$name.llbc 2>&1 | sed 's/\x1b\[[0-9;]*m//g' > logs/$tag-aeneas.log); echo "aeneas rc=$?"
grep -E "^\[Error\]" -A2 $T/logs/$tag-aeneas.log | head -40
ls $T/out/$tag-lean 2>/dev/null && grep -c "^axiom" $T/out/$tag-lean/FunsExternal_Template.lean
