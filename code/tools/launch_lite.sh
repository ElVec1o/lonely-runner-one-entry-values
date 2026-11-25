#!/bin/bash
# usage: launch_lite.sh CEILING_MB LOGDIR NAME cmd args...
# Minimal stand-in for the author's job launcher. It runs the command, writes stdout to LOGDIR/NAME.out and stderr to
# LOGDIR/NAME.err, and records the start and the exit status in LOGDIR/NAME.watch (the run scripts of this directory read
# the last line of that file). CEILING_MB is only recorded: the author's launcher also enforced a memory ceiling and
# a disk floor with a watchdog; this script does not. The programs of this directory are small (see code/README.md).
CEIL=${1:?}; LOGDIR=${2:?}; NAME=${3:?}; shift 3
mkdir -p "$LOGDIR"
echo "launched $NAME ceiling=${CEIL}MB (not enforced) $(date +%T)" >> "$LOGDIR/$NAME.watch"
"$@" > "$LOGDIR/$NAME.out" 2> "$LOGDIR/$NAME.err"
echo "exit=$? $(date +%T)" >> "$LOGDIR/$NAME.watch"
