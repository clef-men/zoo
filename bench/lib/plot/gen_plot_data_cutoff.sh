# Expected variables:
# $benchname: the name of the benchmark
# $outfile: a path where to write the plot data
# $prog: a path to the binary to run
#   expected calling convention for $prog:
#     CUTOFF=$cutoff $prog $impl $input
#     CUTOFF=52 $prog sequential 500
# $input: the input to provide to prog

rm -f $outfile

printf "# %s, with varying cutoff\n" "$benchname" >> $outfile
printf "# prog: CUTOFF={cutoff} %s {impl} %s\n" "$prog" "$input" >> $outfile

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
