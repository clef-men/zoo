## Synopsis

This project is part of the [Iris Masterplan](https://julesjacobs.com/slides/iris-masterplan.pdf).
It aims at verifying OCaml 5 programs, including lockfree algorithms from [Saturn](https://github.com/ocaml-multicore/saturn) and a [work-stealing scheduler](https://github.com/clef-men/parabs) based on [Domainslib](https://github.com/ocaml-multicore/domainslib).

## Building

First, you need to install [`opam`](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

Then, create a new local `opam` switch and install dependencies with:

```
opam switch create . --deps-only --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
```

Finally, to compile Coq proofs, run:

```
make -j
```

## Installation

Zoo is not available on `opam` yet, but you can already use it in your Coq developments by adding the following `opam` dependency:

```
pin-depends: [
  ["coq-zoo.dev" "git+https://github.com/clef-men/zoo.git#main"]
]
depends: [
  "coq-zoo"
]
```

To also install the standard library, add:

```
pin-depends: [
  ["coq-zoo.dev" "git+https://github.com/clef-men/zoo.git#main"]
  ["coq-zoo-std.dev" "git+https://github.com/clef-men/zoo.git#main"]
]
depends: [
  "coq-zoo-std"
]
```

See also [this example](https://github.com/clef-men/zoo-demo).
