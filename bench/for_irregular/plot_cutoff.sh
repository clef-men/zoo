gnuplot -p -e "libdir='bench/lib/plot'" -e "datafile='$1'" \
  -c ./bench/for_irregular/graph_cutoff.plot
