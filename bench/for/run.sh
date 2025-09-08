#! /bin/bash

set -eou pipefail

impls="sequential,parabs,domainslib,moonpool-fifo,moonpool-ws"
inputs="500_000"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method $impls \
    -L cutoff 1,10,100,1000,default \
    --command-name "method:{method} cutoff:{cutoff} input:$input" \
    "CUTOFF={cutoff} ./_build/default/bench/for/run.exe {method} $input"
done
