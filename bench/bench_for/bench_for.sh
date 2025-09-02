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
    -L cutoff 1,10,100,1000 \
    --command-name "method:{method} cutoff:{cutoff} input:$input" \
    "./_build/default/bench/bench_for/bench_for.exe {method} {cutoff} $input"
done
