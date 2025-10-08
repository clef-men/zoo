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


# Preliminary analysis of benchmark results

The analysis is based on the benchmark output data currently stored in the repository.

## Benchmarks

Each benchmark is evaluated across different schedulers.

- `domainslib`: [domainslib](https://github.com/ocaml-multicore/domainslib/), the standard library for CPU-bound concurrent tasks in Multicore OCaml
- `parabs`: the (verified) code from this repository
- `moonpool-fifo`: the [moonpool](https://github.com/c-cube/moonpool/) scheduler, which started as a simpler-yet-efficient scheduler
- `moonpool-ws`: a variant of `moonpool` that uses a work-stealing structure in its scheduler,
  and is described as better at optimizing throughput
- `sequential`: a default baseline where no parallelism actually happens, all tasks are run on the main domain


## Benchmark setting

Those benchmark results were produced on Gabriel's 12-cores AMD Ryzen
5 7640U machine, set at a fixed frequency of 2GHz.

The benchmarks were *not* run in an isolated environment, so at least
one or two cores were busy with other programs. It is fair to assume
that workloads running with more than 10 domains suffered from CPU
contention. (Note: the multicore OCaml runtime is known to behave
badly under CPU contention, due to the stop-the-world design being
sensitive to OS-imposed pauses.)

## Benchmark parameters

Our benchmarks typically used a fixed input that determines a large-enough compute time (typically between 200ms and 2s; `hyperfine` is used to repeat computations to reduce noise).

They can vary the number of domains (DOMAINS), or the cutoff value (CUTOFF) under which a sequential implementation is used.

We perform two kinds of measurements for each benchmark:

- a "per-cutoff" benchmark, which evaluates the performance of the
  benchmark with varying CUTOFF values, using a fixed number of
  domains, typically DOMAINS=6 -- large enough to observe concurrency
  effects and data contention, but small enough to avoid CPU/domain
  contention.

- a "per-domain" benchmark, which evaluates the performance with
  varying DOMAINS value, using a CUTOFF value that has been observed
  to deliver reasonable performance across all implementations.


## Pre-benchmarking expectations

Our expectation before running the benchmark is that `parabs` has the
same performance as `domainslib`, and that they are both more
efficient than `moonpool` (which uses a central pool of jobs instead
of per-domain deques).

Because `moonpool` has a less optimized scheduler, we expect
scheduling overhead to be an issue for small CUTOFF values. On all
schedulers, the performance for larger CUTOFF values should be good if
the benchmark has homogeneous/regular tasks, and it should be bad if
the benchmark has heterogeneous/irregular tasks.

## Overall results

We observe that `moonpool` works better than either `parabs` and
`domainslib` under CPU contention -- starting around 10 domains.

The parallel-for implementation of `moonpool` uses one less domain
than `domainslib` or `parabs` for compute -- the main domain simply
blocks until the worker domains complete. This shows as one-domain
shift in the results, for example the DOMAINS=2 performance of
moonpool will be comparable to the DOMAINS=1 performance of `parabs`
or `domainslib`.

TODO

## Per-benchmark results

TODO
