plot \
  datafile using 1:2 with linespoints title 'sequential', \
  datafile using 1:3 with linespoints title 'parabs', \
  datafile using 1:4 with linespoints title 'domainslib', \
  datafile using 1:5 with linespoints title 'moonpool-fifo', \
  datafile using 1:6 with linespoints title 'moonpool-ws'
