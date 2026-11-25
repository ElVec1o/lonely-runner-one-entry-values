#!/bin/bash
# usage: run.sh NAME args...  -> launch_lite.sh, 400 MB ceiling
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 400 $D/logs $NAME $D/gl "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; tail -40 $D/logs/$NAME.out
