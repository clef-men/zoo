The commands in this file are meant to be run from the root directory
of the 'zoo' repository.

## Running benchmarks

```
EXTRA_DOMAINS=3 sh bench/fibonacci/run.sh
```

Note: the EXTRA_DOMAINS=3 variable is interpreted by the Pool
implementation, and it creates 3 *extra* domains in addition to the
main domain, so in practice this is a 4-domains configuration.

## Plotting data

```
# generates data/fibonacci/data/plot_cutoff.data, for 4 domains (1+3)
EXTRA_DOMAINS=3 sh bench/fibonacci/gen_plot_data_cutoff.sh

# plot the data
sh bench/fibonacci/plot_cutoff.sh bench/fibonacci/data/plot_cutoff.data

# produce SVG output
SVG=1 sh bench/fibonacci/plot_cutoff.sh bench/fibonacci/data/plot_cutoff.data

# convert SVG output to a PDF
inkscape bench/fibonacci/data/plot_cutoff.data.svg -o bench/fibonacci/data/plot_cutoff.data.pdf
```
