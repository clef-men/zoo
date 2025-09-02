#! /bin/bash

set -eou pipefail

impls="sequential,parabs,domainslib,moonpool-fifo,moonpool-ws"
inputs="100000 1000000 10000000"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method $impls \
    -L cutoff 20,50,100 \
    --command-name "method:{method} cutoff:{cutoff} input:$input" \
    "./_build/default/bench/bench_for/bench_for.exe {method} {cutoff} $input"
done
