set xlabel 'cutoff'
set ylabel 'seconds'
set logscale x
set xtics (1, 2, 4, 8, 16, 32, 64)
plot \
  datafile using 1:2 with linespoints title 'sequential', \
  datafile using 1:3 with linespoints title 'parabs', \
  datafile using 1:4 with linespoints title 'domainslib', \
  datafile using 1:5 with linespoints title 'moonpool-fifo', \
  datafile using 1:6 with linespoints title 'moonpool-ws'
