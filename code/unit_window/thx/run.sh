#!/bin/bash
# usage: run.sh NAME args...  -> launch_lite.sh ceiling 300 MB
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 300 $D/logs $NAME $D/bin/thx "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -2 $D/logs/$NAME.watch | tr '\n' ' ')"; cut -c1-260 $D/logs/$NAME.out | head -${LINES_OUT:-70}
