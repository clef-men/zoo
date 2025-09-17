gnuplot -p \
  -e "libdir='bench/lib/plot'" -e "datafile='$1'" \
  -c ./bench/fibonacci/graph_cutoff.plot
