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
