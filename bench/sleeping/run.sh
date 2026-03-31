#! /bin/bash

set -eou pipefail

dune build bench/sleeping/run.exe

echo "This benchmark exercises the logic to put inactive workers to sleep."

for impl in sequential domainslib parabs-main parabs
do
    echo
    echo -n "implementation $impl:"
    time _build/default/bench/sleeping/run.exe $impl 2_000
done
