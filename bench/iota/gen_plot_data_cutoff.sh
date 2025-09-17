#! /bin/bash

set -eou pipefail

benchname="iota"
input="400_000"
cutoffs="10 100 1000 10000 100000"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="EXTRA_DOMAINS=6 ./_build/default/bench/$benchname/run.exe"

dune build bench/$benchname/run.exe

outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

