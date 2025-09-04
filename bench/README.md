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
# generates data/fibonacci_plot_4.data, the 4-domains results
EXTRA_DOMAINS=3 sh bench/fibonacci/gen_plot_data.sh

# plot the data
sh bench/fibonacci/plot.sh bench/fibonacci/data/plot_4.data
```
