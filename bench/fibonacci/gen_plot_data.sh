#! /bin/bash

set -eou pipefail

input="35"
cutoffs="5 7 10 12 15 17 20 22 25 27 30 32 35"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="./_build/default/bench/fibonacci/run.exe"

dune build bench/fibonacci/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/fibonacci/data/plot_$DOMAINS.data

rm -f $outfile

printf "%s" "# cutoff" >> $outfile
for impl in $impls
do
    printf ", %s" $impl >> $outfile
done
echo >> $outfile

for cutoff in $cutoffs
do
    printf "%d " $cutoff >> $outfile
    for impl in $impls
    do
        hyperfine --runs 10 "$prog $impl $cutoff $input" --export-json /tmp/out.json
        printf "%g " $(cat /tmp/out.json | jq .results[0].mean) >> $outfile
    done
    echo >> $outfile
done

echo "Data written to: $outfile"
