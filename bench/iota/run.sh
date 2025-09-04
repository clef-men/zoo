#! /bin/bash

set -eou pipefail

impls="sequential,parabs,domainslib,moonpool-fifo,moonpool-ws"
inputs="1000000 2000000 3000000"

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 20 \
    -L method $impls \
    --command-name "method:{method} size:$input" \
    "./_build/default/bench/iota/run.exe {method} $input"
done
