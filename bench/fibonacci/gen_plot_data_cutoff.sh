#! /bin/bash

set -eou pipefail

EXTRA_DOMAINS=6
benchname="fibonacci"
input="42"
cutoffs="6 8 10 12 15 17 20 22 25"
impls="sequential parabs domainslib moonpool-ws moonpool-fifo"
prog="EXTRA_DOMAINS=$EXTRA_DOMAINS timeout 10 ./_build/default/bench/$benchname/run.exe"

if [ -f /tmp/fibonacci-taskflow.exe ]
then
  impls="$impls taskflow"
fi

dune build bench/$benchname/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

