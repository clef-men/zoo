#! /bin/bash

set -eou pipefail

inputs="1000000 2000000 3000000"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method parabs,domainslib \
    --command-name "method:{method} size:$input" \
    "./_build/default/bench/bench_iota/bench_iota.exe {method} $input"
done
