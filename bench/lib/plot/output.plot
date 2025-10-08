# Pass SVG=1 to the plot scripts to get SVG output
if (system("echo $SVG")) {
  set term svg size 1024,768 dynamic enhanced background rgb 'white'
  set output datafile.'.svg'
  print 'SVG output written to '.datafile.'.svg'
}
