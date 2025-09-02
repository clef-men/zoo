The commands in this file are meant to be run from the root directory
of the 'zoo' repository.

## Running benchmarks

```
EXTRA_DOMAINS=3 sh bench/bench_fibonacci/bench_fibonacci.sh
```

Note: the EXTRA_DOMAINS=3 variable is interpreted by the Pool
implementation, and it creates 3 *extra* domains in addition to the
main domain, so in practice this is a 4-domains configuration.

## Plotting data

```
# generates data/fibonacci_plot_4.data, the 4-domains results
EXTRA_DOMAINS=3 sh bench/bench_fibonacci/gen_plot_data.sh

# plot the data
sh bench/bench_fibonacci/plot.sh bench/bench_fibonacci/data/fibonacci_plot_4.data
```
