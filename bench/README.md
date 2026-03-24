The commands in this file are meant to be run from the root directory
of the 'zoo' repository.

Software dependencies:
- you need to build the `Parabs` library of the present directory
  (so you need `opam`, OCaml, but not Rocq; see the root README)
- the benchmarking tool [hyperfine](https://github.com/sharkdp/hyperfine)
- to produce plots: [gnuplot](http://www.gnuplot.info/)
- to convert SVG plots in PDF: [inkscape](https://en.wikipedia.org/wiki/Inkscape)
  (this is optional, you can also look at the SVG results directly)

Running the benchmarks should work on all operating systems.

## How to run individual benchmarks

The `run.sh` scripts only run the benchmark and print results in the
terminal, they do not save any plotting data or any other output.

```
# from the _root_ directory of the project, not from bench/

EXTRA_DOMAINS=3 sh bench/fibonacci/run.sh
```

Note: the EXTRA_DOMAINS=3 variable is interpreted by the Pool
implementation, and it creates 3 *extra* domains in addition to the
main domain, so in practice this is a 4-domains configuration.

## How to run a benchmark and plot the results

The `gen_plot_data_*.sh` scripts run benchmarks _and_ write the
benchmark data in files. (If you are in a git-versioned repository you
will see which benchmark data has been updated with `git status`.)
Then the `plot_*.sh` scripts will plot the data in a viewer or,
depending on the options, write `.svg` and `.pdf` files.


For a single benchmark:
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


For all benchmarks:

```
# run all benchmarks one after the other
sh bench/gen_all_data.sh

# render all plots into .svg and .pdf files
sh bench/render_all_plots.sh

# find all the plots (you can also use the SVG format directly)
find . -name '*.pdf'
```

On one test machine, running all the benchmarks took 70 minutes.


## [for artifact reviewers] how to review the results

In our Parabs paper we have specific plots from a test machine, we try
our best to interpret the quantitative results shown in the plot, and
then we extract qualitative claims from these interpretations.

If you have produced your own plots on a different benchmark machine,
we would recommend reviewing them as follows:

- for each benchmark, compare our plots and your plots;

- if you notice any significant difference, read our interpretation of
  our plots and see if your results agree with it, or if they suggest
  other significant phenomenons which the interpretation should also
  take into account;

- if the quantitative results different significantly, check that the
  qualitative claims we made are still valid.

The rest of this document explains our benchmarks, and provides an
analysis of the benchmark results that is up-to-date with the version
of the benchmarks in this directory. It should be very close to the
analysis of the benchmarks in the Parabs paper (which was extracted
and summarized from an earlier version of the present README) --
comparing your results to the discussion here or in the paper should
be the same.


# Preliminary analysis of benchmark results

The analysis is based on the benchmark output data currently stored in the repository.

## Benchmark setting

Those benchmark results were produced on Gabriel's 12-cores AMD Ryzen
5 7640U machine, set at a fixed frequency of 2GHz, running GNU/Linux.

Note: the multicore OCaml runtime is known to behave badly under CPU
contention, due to the stop-the-world design being sensitive to
OS-imposed pauses. In particular, if you run the benchmarks on
a machine that is already busy with other things (or in
performance-saving mode, etc.), you are likely to observe sharp
performance degradation above the number of mostly-free cores
available -- on one busy test machine with 12 cores, asking for 12
domains runs 3x slower than 8 domains. This issue affects all
benchmarks, is mostly unrelated to the scheduler implementations under
test (sometimes we observe that `moonpool` does a bit better than the
others, possibly due to the use of native threads for tasks which
might improve OS scheduling decisions), and will invalidate our
qualitative analysis on higher domain counts on busy machines.


## Scheduler implementations

Each benchmark is evaluated across different schedulers.

- `domainslib`: [domainslib](https://github.com/ocaml-multicore/domainslib/), the standard library for CPU-bound concurrent tasks in Multicore OCaml
- `parabs`: the (verified) code from this repository
- `moonpool-fifo`: the [moonpool](https://github.com/c-cube/moonpool/) scheduler (version 0.9), which started as a simpler-yet-efficient scheduler
- `moonpool-ws`: a variant of `moonpool` that uses a work-stealing structure in its scheduler, and is described as better at optimizing throughput
- `sequential`: a default baseline where no parallelism actually happens, all tasks are run on the main domain

Software versions: our results below use OCaml 5.4.0 (`ocamlc --version`),
Domainslib 0.5.2 and Moonpool 0.11 (`opam show domainslib moonpool`).


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

The benchmarks validate our pre-benchmarking expectations.  In fact
`parabs` seems to perform slightly better than `domainslib` on
benchmarks `fibonacci` and `for_irregular` with irregular task
(sometimes 10-20% better).

We observe that `moonpool` sometimes works better than either `parabs`
and `domainslib` under CPU contention. The cause for this difference
is not fully understood; it may come from the fact that `moonpool`
creates native threads (`pthreads`) for each task, which may have
a positive influence on how the OS schedules the program under
contention.


## Per-benchmark results

### `fibonacci`

Note: as a control we also measure a C++ version of this benchmark using the [TaskFlow](https://github.com/taskflow/taskflow/) library. We expect this version to be faster than the others by a constant factor.

Per-cutoff results: All schedulers start behave badly when the CUTOFF becomes small enough, with exponentially-decreasing performance after a certain drop point. For `moonpool`, performance drops around CUTOFF=22. For `parabs`, `domainslib` and `taskflow`, performance drops around CUTOFF=15. In fact, even for the sequential scheduler we observe a small performance drop around CUTOFF=8: the task-using version creates closures and performs indirect calls, so it is noticeably slower (by a constant factor) than the version used below the sequential cutoff.

For any `cutoff` value it appears that `parabs` is slightly faster than `domainslib` on this benchmark, and `moonpool-ws` is slightly faster than `moonpool-fifo`. The `moonpool` versions become *very* slow for smaller cutoff values, so we had to set a timeout at 8s and their results are clamped.

Note: we observe very large memory usage with `moonpool-fifo` at smaller cutoff values -- for N=40, we had to stop computing from CUTOFF=5 due to benchmarks failing with out-of-memory errors on machine with 32Gio of RAM. This seems to come from the `fifo` architecture which runs the oldest and thus biggest task first, and thus stores an expontential number of smaller tasks in the queue.

Per-domain results: `domainslib` and `moonpool-*` have very similar performance, and `parabs` is slightly faster. Performance becomes very close for larger number of domains (DOMAINS >= 7).

Representative results for cutoff=30, DOMAINS=4.

```
Summary
  method:taskflow cutoff:30 input:40 ran
    1.32 ± 0.03 times faster than method:parabs cutoff:30 input:40
    1.40 ± 0.03 times faster than method:domainslib cutoff:30 input:40
    1.45 ± 0.04 times faster than method:moonpool-fifo cutoff:30 input:40
    1.47 ± 0.04 times faster than method:moonpool-ws cutoff:30 input:40
    5.43 ± 0.11 times faster than method:sequential cutoff:30 input:40
```

### `for_irregular`

Per-cutoff results: `for_irregular` is designed to be a worst-case for large CUTOFF values. We indeed observe better noticeably performance with CUTOFF=1 than with larger values, across all schedulers -- for example `domainslib` is 45% slower with CUTOFF=8.

We observe that `parabs` is slightly faster than the other schedulers, and that `domainslib` is slightly faster than `moonpool-*` for CUTOFF<=6 and they behave similarly afterwards.

The per-domain results show that `parabs` is slightly faster than `domainslib` and `moonpool`. Representative results for DOMAINS=4:

```
Summary
  method:parabs cutoff:1 input:100 ran
    1.11 ± 0.04 times faster than method:domainslib cutoff:1 input:100
    1.14 ± 0.04 times faster than method:moonpool-ws cutoff:1 input:100
    1.14 ± 0.04 times faster than method:moonpool-fifo cutoff:1 input:100
    3.77 ± 0.11 times faster than method:sequential cutoff:1 input:100
```

### `iota`

In the per-cutoff plot we see that `moonpool` performance degrade rapidely for not-so-small cutoff values, with `moonpool-ws` behaving noticeably better than `moonpool-fifo`.

In the per-domain plot, we see that `parabs` and `domainslib` have the same performance, and `moonpool` (both implementations) is slower. For example for DOMAINS=4:

```
Summary
  method:parabs size:1_000_000 ran
    1.02 ± 0.05 times faster than method:domainslib size:1_000_000
    1.14 ± 0.07 times faster than method:moonpool-ws size:1_000_000
    1.15 ± 0.07 times faster than method:moonpool-fifo size:1_000_000
    3.33 ± 0.13 times faster than method:sequential size:1_000_000
```

### `lu`

Per-cutoff results: most schedulers tend to behave relatively well for any cutoff value.

Per-domain results (CUTOFF=10): `domainslib` and `parabs` have similar performance and `moonpool` is slower. On (DOMAINS >= 12) `moonpool` behaves much better as it suffers much less from CPU contention.

For example for DOMAINS=4:

```
Summary
  method:domainslib size:700 ran
    1.04 ± 0.05 times faster than method:parabs size:700
    1.17 ± 0.04 times faster than method:moonpool-ws size:700
    1.20 ± 0.05 times faster than method:moonpool-fifo size:700
    3.52 ± 0.12 times faster than method:sequential size:700
```

## `matmul`

Per-cutoff results: the performance is stable across a wide range of CUTOFF value: almost constant between CUTOFF=1 and CUTOFF=10, decreases slightly until CUTOFF=100. The input uses N=500, so larger cutoff values prevent parallelization and bring performance closer to the sequential scheduler.

Per-domain results: for DOMAINS<=12, all scheduler perform similarly. In CPU-contended settings (DOMAINS > 12), `moonpool` performs noticeably better than the other schedulers.
