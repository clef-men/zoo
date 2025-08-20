#! /bin/bash

set -eou pipefail

inputs="800 1000"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method parabs,domainslib \
    --command-name "method:{method} size:$input" \
    "./_build/default/bench/bench_lu/bench_lu.exe {method} $input"
done
