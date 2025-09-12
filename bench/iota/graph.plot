set xlabel 'domains'
set ylabel 'seconds'
# set logscale x
set xrange [0:16]
set xtics (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
plot \
  datafile using 1:2 with linespoints title 'sequential', \
  datafile using 1:3 with linespoints title 'parabs', \
  datafile using 1:4 with linespoints title 'domainslib', \
  datafile using 1:5 with linespoints title 'moonpool-fifo', \
  datafile using 1:6 with linespoints title 'moonpool-ws'
