#! /bin/bash

set -eou pipefail

input="35"
cutoffs="5 7 10 12 15 17 20 22 25 27 30 32 35"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="./_build/default/bench/fibonacci/run.exe"

dune build bench/fibonacci/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/fibonacci/data/plot_cutoff.data

rm -f $outfile

printf "# fibonacci, with varying cutoff\n" >> $outfile
printf "# input=%s\n" $input >> $outfile
printf "# domains=%s\n" $DOMAINS >> $outfile

printf "# columns: cutoff" >> $outfile
for impl in $impls
do
    printf ", %s" $impl >> $outfile
done
printf "\n" >> $outfile

for cutoff in $cutoffs
do
    printf "%d " $cutoff >> $outfile
    for impl in $impls
    do
        hyperfine --runs 10 "CUTOFF=$cutoff $prog $impl $input" --export-json /tmp/out.json
        printf "%g " $(cat /tmp/out.json | jq .results[0].mean) >> $outfile
    done
    printf "\n" >> $outfile
done

echo "Data written to: $outfile"
