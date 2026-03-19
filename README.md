## Building

### Rocq proofs only

First, you need to install [`opam`](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

Then, create a new local `opam` switch and install dependencies with:

```
opam switch create . --empty --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
opam install ./rocq-*.opam --deps-only --yes
eval $(opam env --switch=. --set-switch)
```

Finally, to compile Rocq proofs, run:

```
make -j
```

### OCaml libraries and Rocq proofs

First, you need to install [`opam`](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

Then, you need to install [this custom version of the OCaml compiler](https://github.com/clef-men/ocaml/tree/generative_constructors) featuring atomic record fields, atomic arrays and generative constructors.
Hopefully, it should be merged into the OCaml compiler one day.

The following commands take care of this:

```
opam switch create . --empty --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
opam pin add ocaml-variants git+https://github.com/clef-men/ocaml#generative_constructors --yes
```

Then, install dependencies including [`ocaml2zoo`](https://github.com/clef-men/ocaml2zoo) with:

```
opam pin add ocaml2zoo git+https://github.com/clef-men/ocaml2zoo#main --yes
opam install . --with-dev-setup --deps-only --yes
```

To compile OCaml libraries (see [`lib/`](lib/)), run:

```
make lib
```

To compile benchmarks, run:

```
make bench
```

To translate OCaml libraries into [Zoo](https://github.com/clef-men/zoo) (Rocq files are generated in [`theories/`](theories/)), run:

```
make ocaml2zoo
```

Finally, to compile Rocq proofs, run:

```
make -j
```

### OCaml libraries only

First, you need to install [`opam`](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

Then, you need to install [this custom version of the OCaml compiler](https://github.com/clef-men/ocaml/tree/generative_constructors) featuring atomic record fields, atomic arrays and generative constructors.
Hopefully, it should be merged into the OCaml compiler one day.

The following commands take care of this:

```
opam switch create . --empty --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
opam pin add ocaml-variants git+https://github.com/clef-men/ocaml#generative_constructors --yes
```

Then, install dependencies with:

```
opam install $(find . -depth 1 -name '*.opam' ! -name 'rocq-*') --deps-only --yes
```

To compile benchmarks, you also need to install benchmark-only dependencies with:

```
opam install $(find . -depth 1 -name '*.opam' ! -name 'rocq-*') --with-dev-setup --deps-only --yes
```

To compile OCaml libraries (see [`lib/`](lib/)), run:

```
make lib
```

To compile benchmarks, run:

```
make bench
```

## Installation

Zoo is not available on `opam` yet, but you can already use it in your Rocq developments by adding the following `opam` dependency:

```
pin-depends: [
  ["rocq-zoo.dev" "git+https://github.com/clef-men/zoo.git#main"]
]
depends: [
  "rocq-zoo"
]
```

To also install the standard library, add:

```
pin-depends: [
  ["rocq-zoo.dev" "git+https://github.com/clef-men/zoo.git#main"]
  ["rocq-zoo-std.dev" "git+https://github.com/clef-men/zoo.git#main"]
]
depends: [
  "rocq-zoo-std"
]
```

See also [this example](https://github.com/clef-men/zoo-demo).

## Architecture

### OCaml libraries

The [`lib/`](lib/) directory contains the OCaml libraries, some of which are inherited from Zoo.

- [`lib/zoo/`](lib/zoo/) is inherited from Zoo.
  It provides support for prophecy variables.

- [`lib/zoo_std/`](lib/zoo_std/) is inherited from Zoo.
  It provides standard sequential and concurrent data structures.

- [`lib/zoo_saturn/`](lib/zoo_saturn/) is partly inherited from Zoo.
  It provides lock-free data structures, including the Chase-Lev work-stealing deque presented in the paper.

- [`lib/zoo_parabs/`](lib/zoo_parabs/) contains the source code of the `Parabs` library presented in the paper.

- [`lib/examples/`](lib/examples/) contains examples for the `Parabs` library.

### Rocq proofs

The [`theories/`](theories/) directory contains the correctness proofs for the OCaml libraries, some of which are also inherited from Zoo.
It mirrors the [`lib/`](lib/) directory.

- [`theories/zoo/`](theories/zoo/) is largely inherited from Zoo.
  It defines the ZooLang language (presented in the POPL 2026 paper) along with an Iris-based program logic.
  The theories for reasoning about prophecy variables described in the paper are located in [`theories/zoo/program_logic/`](theories/zoo/program_logic/).

- [`theories/zoo_std/`](theories/zoo_std/) is inherited from Zoo.
  It contains the correctness proofs for the data structures of [`lib/zoo_std/`](lib/zoo_std).

- [`theories/zoo_saturn/`](theories/zoo_saturn/) is partly inherited from Zoo.
  It contains the correctness proofs for the data structures of [`lib/zoo_saturn/`](lib/zoo_saturn).

- [`lib/zoo_parabs/`](lib/zoo_parabs/) contains the correctness proofs for the `Parabs` library.

- [`theories/examples/`](theories/examples/) contains the correctness proofs for the examples.

### Benchmarks

The [`bench/`](bench/) directory contains the benchmarks mentioned in the paper and presented in the appendix.
See [`bench/README.md`](bench/README.md).

## Paper coverage

The mapping between our claims and this development is provided in the paper.
