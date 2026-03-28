#! /bin/bash

set -eou pipefail

dune build bench/waiting/run.exe

echo "This benchmark measures busy-waiting behavior on futures. Compare the 'user' (or CPU) time between implementations, which all take about the same 'real' time."

for impl in sequential moonpool-ws domainslib parabs
do
    echo
    echo -n "implementation $impl:"
    time _build/default/bench/waiting/run.exe $impl 20
done
