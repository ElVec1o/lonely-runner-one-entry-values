#!/bin/bash
# usage: run.sh NAME args...  -> launch_lite.sh, 300 MB ceiling
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" ${CEIL:-300} $D/logs $NAME $D/bin/${BIN:-oe} "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; cat $D/logs/$NAME.out | cut -c1-${CUT:-1200}; cat $D/logs/$NAME.err | head -5
