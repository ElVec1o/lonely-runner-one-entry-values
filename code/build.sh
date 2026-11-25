#!/bin/bash
# usage: bash code/build.sh [outdir-suffix-ignored]
# Compiles every program of code/ in place: rustc -O (edition 2021 as fallback) for .rs, cc -O2 for .c.
# A source in a directory named src or src2 is built into ../bin/NAME; any other source is built next to itself.
# Library fragments (multi_entry/src/mm2_lib.rs) and the Cargo project linear_count/l2 are handled separately.
# No network access, no external crates. Nothing is run.
cd "$(dirname "$0")" || exit 1
fail=0; n=0
for f in $(find . -type f \( -name '*.rs' -o -name '*.c' \) | LC_ALL=C sort); do
  case $f in ./linear_count/l2/*|*/mm2_lib.rs) continue;; esac
  d=$(dirname "$f"); b=$(basename "${f%.*}"); ext=${f##*.}
  case $(basename "$d") in src|src2) bd="$d/../bin";; *) bd="$d";; esac
  mkdir -p "$bd"; n=$((n+1))
  if [ "$ext" = rs ]; then
    rustc -O -o "$bd/$b" "$f" 2>/dev/null || rustc -O --edition 2021 -o "$bd/$b" "$f" || { echo "FAIL $f"; fail=$((fail+1)); }
  else
    cc -O2 -o "$bd/$b" "$f" -lm || { echo "FAIL $f"; fail=$((fail+1)); }
  fi
done
if [ -f linear_count/l2/Cargo.toml ]; then
  (cd linear_count/l2 && cargo build --release --offline) || { echo "FAIL linear_count/l2"; fail=$((fail+1)); }
fi
echo "built $n programs, $fail failures"
exit $fail
