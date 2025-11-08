
if [ ! -d bench ]
then
    echo "this program is meant to be run from the root directory of the zoo project"
    exit 2
fi

for bench in fibonacci for_irregular iota lu matmul
do
    sh bench/$bench/gen_plot_data_cutoff.sh
    sh bench/$bench/gen_plot_data_domains.sh
done
