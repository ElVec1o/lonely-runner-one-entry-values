#!/bin/bash
# usage: run.sh NAME args... -> launch_lite.sh ceiling ${CEIL:-300} MB
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CEIL=${CEIL:-300}
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/n02 "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -2 $D/logs/$NAME.watch | tr '\n' ' ')"; cut -c1-300 $D/logs/$NAME.out | tail -${LINES_OUT:-40}
