gnuplot -p -e "libdir='bench/lib/plot'" -e "datafile='$1'" \
  -c ./bench/matmul/graph_cutoff.plot
