#! /bin/bash

set -eou pipefail

input="500"
cutoffs="1 2 4 8 16 32 64"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="./_build/default/bench/for_irregular/run.exe"

dune build bench/for_irregular/run.exe

DOMAINS=$(($EXTRA_DOMAINS + 1))
outfile=bench/for_irregular/data/plot_$DOMAINS.data

rm -f $outfile

printf "%s" "# cutoff" >> $outfile
for impl in $impls
do
    printf ", %s" $impl >> $outfile
done
echo >> $outfile

for cutoff in $cutoffs
do
    printf "%s " $cutoff >> $outfile
    for impl in $impls
    do
        hyperfine --runs 10 "CUTOFF=$cutoff $prog $impl $input" --export-json /tmp/out.json
        printf "%g " $(cat /tmp/out.json | jq .results[0].mean) >> $outfile
    done
    echo >> $outfile
done

echo "Data written to: $outfile"
