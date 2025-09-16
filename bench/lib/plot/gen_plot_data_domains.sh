# Expected variables:
# $benchname: the name of the benchmark
# $outfile: a path where to write the plot data
# $prog: a path to the binary to run
#   expected calling convention for $prog:
#     EXTRA_DOMAINS=$extra_domains $prog $impl $input
#     EXTRA_DOMAINS=3 $prog sequential 500
# $input: the input to provide to prog

rm -f $outfile

printf "# %s, with varying domains\n" "$benchname" >> $outfile
printf "# prog: EXTRA_DOMAINS={doms} %s {impl} %s\n" "$prog" "$input" >> $outfile

printf "# columns: domains" >> $outfile
for impl in $impls
do
    printf ", %s" $impl >> $outfile
done
printf "\n" >> $outfile

for extra in $extra_domains
do
    printf "%s " $(( $extra + 1 )) >> $outfile
    for impl in $impls
    do
        hyperfine --runs 10 "EXTRA_DOMAINS=$extra $prog $impl $input" --export-json /tmp/out.json
        printf "%g " $(cat /tmp/out.json | jq .results[0].mean) >> $outfile
    done
    printf "\n" >> $outfile
done

echo "Data written to: $outfile"
