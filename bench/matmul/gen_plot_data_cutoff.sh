#! /bin/bash

set -eou pipefail

benchname="matmul"
input="500"
cutoffs="1 5 10 50 100 200 400"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="EXTRA_DOMAINS=6 ./_build/default/bench/$benchname/run.exe"

dune build bench/$benchname/run.exe

outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

