#! /bin/bash

set -eou pipefail

dune build bench/sleeping/run.exe

echo "This benchmark exercises the logic to put inactive workers to sleep."

for impl in sequential moonpool-ws domainslib parabs
do
    echo
    echo -n "implementation $impl:"
    time _build/default/bench/sleeping/run.exe $impl 10_000
done
