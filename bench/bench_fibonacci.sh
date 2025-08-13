#! /bin/bash

set -eou pipefail

inputs="30 40 42"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method parabs,domainslib,moonpool-fifo,moonpool-ws \
    -L cutoff 20,25,30 \
    --command-name "method:{method} cutoff:{cutoff} input:$input" \
    "./_build/default/bench/bench_fibonacci.exe {method} {cutoff} $input"
done
