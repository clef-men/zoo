#! /bin/bash

set -eou pipefail

EXTRA_DOMAINS=6
benchname="fibonacci"
input="42"
cutoffs="27 30 32 35"
impls="sequential parabs domainslib moonpool-ws moonpool-fifo"
hyperfine_args="--ignore-failure"

prog="EXTRA_DOMAINS=$EXTRA_DOMAINS timeout 8 ./_build/default/bench/$benchname/run.exe"

if [ -f /tmp/fibonacci-taskflow.exe ]
then
  impls="$impls taskflow"
fi

dune build bench/$benchname/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/$benchname/data/plot_cutoff.data

source bench/lib/plot/gen_plot_data_cutoff.sh

