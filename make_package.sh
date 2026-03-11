#! /usr/bin/env bash

set -eou pipefail

package="$1"
shift

rocqfile="_RocqProject.$package"
makefile="Makefile.$package"

rm -f "$rocqfile"
grep -E "^-arg" _RocqProject >> "$rocqfile"
awk "/^#END ${package}$/{b=0} b; /^#BEGIN ${package}$/{b=1}" _RocqProject >> "$rocqfile"

coq_makefile -f "$rocqfile" -o "$makefile"

make -f "$makefile" "$@"

rm -f "$rocqfile" ".$makefile.d" "$makefile"*
