#! /bin/bash

set -eou pipefail

benchname="fibonacci"
input="35"
cutoffs="5 7 10 12 15 17 20 22 25 27 30 32 35"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="./_build/default/bench/$benchname/run.exe"

dune build bench/$benchname/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

