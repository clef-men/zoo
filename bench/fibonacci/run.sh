#! /bin/bash

set -eou pipefail

impls="parabs,domainslib,parabs-main"

#inputs="30 40 42"
#cutoffs="20,25,30"

inputs=40
cutoffs=8

for input in $inputs; do
  hyperfine \
    "$@" \
    --warmup 10 \
    --runs 40 \
    -L method $impls \
    -L cutoff $cutoffs \
    --command-name "method:{method} cutoff:{cutoff} input:$input" \
    "CUTOFF={cutoff} ./_build/default/bench/fibonacci/run.exe {method} $input"
done
