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

## Scheduler implementations

Each benchmark is evaluated across different schedulers.

- `domainslib`: [domainslib](https://github.com/ocaml-multicore/domainslib/), the standard library for CPU-bound concurrent tasks in Multicore OCaml
- `parabs`: the (verified) code from this repository
- `moonpool-fifo`: the [moonpool](https://github.com/c-cube/moonpool/) scheduler, which started as a simpler-yet-efficient scheduler
- `moonpool-ws`: a variant of `moonpool` that uses a work-stealing structure in its scheduler,
  and is described as better at optimizing throughput
- `sequential`: a default baseline where no parallelism actually happens, all tasks are run on the main domain

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


## Benchmarks

### `fibonacci`

A concurrent implementation of `fibonacci` running `fibo (n - 1)` and
`fibo (n - 2)` in separate tasks, forcing and summing them. Below the
cutoff, a sequential implementation is used.

### `iota`

This benchmark uses a parallel-for to write a default value in each element of an array. In pseudo-code:

```ocaml
parallel-for i = 1 to N do
  t.(i) <- 42
done
```

This measures the performance of the parallel-for implementation with
neglectible per-element work (but some memory traffic). We expect
significant variations due to the CUTOFF parameter.

### `for-irregular`

`for-irregular` computes the following pseudo-code:

```
parallel-for i = 1 to N do
  i' = 10 + ((i-10) mod 30)
  ignore (fibo i')
done
```

In other words, this is a parallel-for loop with a very irregular workload: `fibo` has exponential runtime, `fibo(i+1)` is roughly 1.6x slower than `fibo(i)`, so the majority of compute time is concentrated for the indices 35 to 40. In particular, our parallel-for implementations try to amortize scheduling costs by having each task work on a chunk of CUTOFF consecutive indices, and shoudl behave badly for larger CUTOFF values.

TODO: use a larger LIMIT value

### `lu`

This benchmark performs a LU factorization for a randomly-initialized matrix. It performs O(N) parallel loops with O(N) iterations, where each parallel iteration is itself an O(N) sequential loop:

```ocaml
for k = 0 to N-2 do
  parallel-for i = k+1 to N-1 do
    for j = k+1 to N-1 do
      (two reads, one write)
    done
  done
done
```

### `matmul`

This benchmark computes the multiplication of two matrices, with only a toplevel parallel loop of O(N) iteration, that each perform O(N^2) sequential work:

```ocaml
parallel-for i = 0 to N-1 do
  for j = 0 to N-1 do
    for k = 0 to N-1 do
      (three reads, one write)
    done
  done
done
```

## Benchmark setting

Those benchmark results were produced on Gabriel's 12-cores AMD Ryzen
5 7640U machine, set at a fixed frequency of 2GHz.

The benchmarks were *not* run in an isolated environment, so at least
one or two cores were busy with other programs. It is fair to assume
that workloads running with more than 10 domains suffered from CPU
contention. (Note: the multicore OCaml runtime is known to behave
badly under CPU contention, due to the stop-the-world design being
sensitive to OS-imposed pauses.)


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

The benchmarks `fibonacci` and `iota` validate our pre-benchmarking
expectations. In fact `parabs` seems to perform slightly better than
`domainslib` (sometimes 10-20% better).

The benchmark `lu` shows surprisingly poor performance of `parabs` on
larger CUTOFF value, whose cause is not yet understood.

`for_irregular`, `matmul`: TODO

The parallel-for implementation of `moonpool` uses one less domain
than `domainslib` or `parabs` for compute -- the main domain simply
blocks until the worker domains complete. This shows as "one-domain
shift" in the results, for example the DOMAINS=3 performance of
moonpool will be comparable to the DOMAINS=2 performance of `parabs`
or `domainslib`.

We observe that `moonpool` works better than either `parabs` and
`domainslib` under CPU contention -- starting around 10 domains. The
cause for this difference is not yet understood. (One plausible
explanation is that the centralized design means that domains wait
more, and that having several domains waiting on a lock actually helps
in CPU-contended situations.)


## Per-benchmark results

### `fibonacci`

Per-cutoff results: All schedulers start behave badly when the CUTOFF becomes small enough, with exponentially-decreasing performance after a certain drop point. For `moonpool`, performance drops around CUTOFF=22. For `parabs` and `domainslib`, performance drops around CUTOFF=15. In fact, even for the sequential scheduler we observe a small performance drop: the task-using version creates closures and performs indirect calls, so it is noticeably slower (by a constant factor) than the version used below the sequential cutoff.

Note: we observe very large memory usage with `moonpool` at smaller cutoff values -- for N=40, we had to stop computing from CUTOFF=5 due to benchmarks failing with out-of-memory errors on machine with 32Gio of RAM. This seems to come from the `fifo` architecture which runs the oldest and thus biggest task first, and thus stores an expontential number of smaller tasks in the queue.

Per-domain results: `parabs` behaves slightly better than `domainslib`, and they both behave better than `moonpool` due to the one-domain shift. Performance becomes very close for larger number of domains (DOMAINS >= 7).

Representative results for DOMAINS=4.

```
Summary
  method:parabs cutoff:30 input:40 ran
    1.13 ± 0.02 times faster than method:domainslib cutoff:30 input:40
    1.49 ± 0.02 times faster than method:moonpool-ws cutoff:30 input:40
    1.49 ± 0.02 times faster than method:moonpool-fifo cutoff:30 input:40
    3.86 ± 0.05 times faster than method:sequential cutoff:30 input:40
```

If we give one extra domain to `moonpool` to control against the one-domain shift,
it has the same performance as `domainslib`.

Representative results for DOMAINS=10.

```
Summary
  method:parabs cutoff:30 input:40 ran
    1.01 ± 0.04 times faster than method:domainslib cutoff:30 input:40
    1.03 ± 0.04 times faster than method:moonpool-fifo cutoff:30 input:40
    1.04 ± 0.05 times faster than method:moonpool-ws cutoff:30 input:40
    5.74 ± 0.23 times faster than method:sequential cutoff:30 input:40
```

### `for_irregular`

TODO: re-run the benchmarks with larger LIMIT values

### `iota`

In the per-domain plot, we observe three performance regimes:

- 1 <= DOMAINS <= 5: `moonpool` is much slower than other schedulers
  due to the one-domain shift, but if we correct for this all schedulers
  perform similarly

- 5 <= DOMAINS <= 11: all schedulers perform similarly

- 12 <= DOMAINS: moonpool is noticeably faster than other schedulers
  in CPU-contention scenarios, with a slower degradation of performance
  (even accounting for the one-domain shift)

### `lu`

Per-cutoff results: most schedulers tend to behave relatively well for any cutoff value, except for `parabs` which only performs well with CUTOFF=1.

SURPRISE: `parabs` does very badly with larger cutoff values, this is not explained.

I computed two set of per-domain results, one with CUTOFF=10 which seems to be around the sweet spot for `moonpool`, and one with CUTOFF=1 where `parabs` performs much better than for other CUTOFF values.

Per-domain results (CUTOFF=1): `parabs` and `domainslib` perform similarly, `moonpool` is much worse (around 30% slower in the best cases). `moonpool` does better in CPU-contended scenarios (DOMAINS >= 12).

Per-domain results (CUTOFF=10): `domainslib` does better than `moonpool`, `parabs` is much much worse. For example for DOMAINS=6, `moonpool` is 27% slower than `domainslib` and `parabs` is 290% slower than `domainslib`.


## `matmul`

TODO
