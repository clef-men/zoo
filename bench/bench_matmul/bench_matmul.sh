#! /bin/bash

set -eou pipefail

impls="sequential,parabs,domainslib,moonpool-fifo,moonpool-ws"
inputs="500"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method $impls \
    --command-name "method:{method} size:$input" \
    "./_build/default/bench/bench_matmul/bench_matmul.exe {method} $input"
done
