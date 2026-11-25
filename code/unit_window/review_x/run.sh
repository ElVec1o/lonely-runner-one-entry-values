#!/bin/bash
# usage: run.sh NAME args...  ; ceiling 300 MB
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 300 $D/logs $NAME $D/bin/revx "$@" >$D/logs/$NAME.launch 2>&1
cat $D/logs/$NAME.launch | head -3; echo "== $NAME: $(tail -2 $D/logs/$NAME.watch | tr '\n' ' ')"; cut -c1-250 $D/logs/$NAME.out | head -${LINES_OUT:-60}; head -5 $D/logs/$NAME.err
