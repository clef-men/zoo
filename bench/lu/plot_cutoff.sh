gnuplot -p -e "libdir='bench/lib/plot'" -e "datafile='$1'" \
  -c ./bench/lu/graph_cutoff.plot
