#!/usr/bin/bash
set -x

if [ ! -d bench ]
then
    echo "this program is meant to be run from the root directory of the zoo project"
    exit 2
fi

for bench in fibonacci for_irregular iota lu matmul
do
    for kind in cutoff domains
    do
	SVG=1 sh bench/$bench/plot_$kind.sh bench/$bench/data/plot_$kind.data
	inkscape bench/$bench/data/plot_$kind.data.svg -o bench/$bench/data/plot_$kind.data.svg.pdf
    done
done
