#! /usr/bin/env bash

set -eou pipefail

package="$1"
shift

coqfile="_CoqProject.$package"
makefile="Makefile.$package"

rm -f "$coqfile"
grep -E "^-arg" _CoqProject >> "$coqfile"
echo "-Q theories/$(echo $package | sed -e 's:^zoo::' -e 's:^-::') ${package//-/.}" >> "$coqfile"
awk "/^#END ${package}$/{b=0} b; /^#BEGIN ${package}$/{b=1}" _CoqProject >> "$coqfile"

coq_makefile -f "$coqfile" -o "$makefile"

make -f "$makefile" "$@"

rm -f "$coqfile" ".$makefile.d" "$makefile"*
