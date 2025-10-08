#! /bin/bash

set -eou pipefail

benchname="for_irregular"
input="100"
cutoff="1"
extra_domains="0 1 2 3 4 5 6 7 8 9 10 11 12 13 14"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="CUTOFF=$cutoff LIMIT=38 ./_build/default/bench/$benchname/run.exe"

dune build bench/$benchname/run.exe

outfile=bench/$benchname/data/plot_domains.data

source bench/lib/plot/gen_plot_data_domains.sh
