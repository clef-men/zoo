#! /bin/bash

set -eou pipefail

input="1_000_000"
cutoff="10_000"
extra_domains="0 1 2 3 4 5 6 7 8 9 10 11 12 13 14"
impls="sequential parabs domainslib moonpool-fifo moonpool-ws"
prog="./_build/default/bench/iota/run.exe"

dune build bench/iota/run.exe

outfile=bench/iota/data/plot.data

rm -f $outfile

printf "# input=%s" $input >> $outfile
printf "# cutoff=%s" $cutoff >> $outfile
printf "# domains" >> outfile
for impl in $impls
do
    printf ", %s" $impl >> $outfile
done
echo >> $outfile

for extra in $extra_domains
do
    printf "%s " $(( $extra + 1 )) >> $outfile
    for impl in $impls
    do
        hyperfine --runs 10 "EXTRA_DOMAINS=$extra CUTOFF=$cutoff $prog $impl $input" --export-json /tmp/out.json
        printf "%g " $(cat /tmp/out.json | jq .results[0].mean) >> $outfile
    done
    echo >> $outfile
done

echo "Data written to: $outfile"
