#! /bin/bash

set -eou pipefail

benchname="for_irregular"
input="100"
cutoffs="1 2 3 4 6 8 12 16 24 32"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="LIMIT=36 ./_build/default/bench/$benchname/run.exe"

dune build bench/$benchname/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

