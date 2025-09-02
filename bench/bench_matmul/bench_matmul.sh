#! /bin/bash

set -eou pipefail

inputs="500"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method parabs,domainslib,moonpool-fifo,moonpool-ws \
    --command-name "method:{method} size:$input" \
    "./_build/default/bench/bench_matmul/bench_matmul.exe {method} $input"
done
