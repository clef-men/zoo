load libdir.'/output.plot'
load libdir.'/axes_cutoff.plot'
set ytics (0.01, 0.02, 0.04, 0.08, 0.16, 0.32, 0.64, 1.28, 2.56, 5.12, 10.24, 20.48, 40.96)
set yrange [0.08:40.96]

plot \
  datafile using 1:2 with linespoints title 'sequential', \
  datafile using 1:3 with linespoints title 'parabs', \
  datafile using 1:4 with linespoints title 'domainslib', \
  datafile using 1:5 with linespoints title 'taskflow'

