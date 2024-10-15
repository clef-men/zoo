## Synopsis

This project is part of the [Iris Masterplan](https://julesjacobs.com/slides/iris-masterplan.pdf).
It aims at verifying OCaml 5 programs, including lockfree algorithms from [Saturn](https://github.com/ocaml-multicore/saturn) and a [work-stealing scheduler](https://github.com/clef-men/parabs) based on [Domainslib](https://github.com/ocaml-multicore/domainslib).

## Building

First, you need to install [opam](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

### Coq proofs only

To compile Coq proofs, run the following commands:

```
opam switch create . --deps-only --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
make -j
```

### Coq proofs and `ocaml2zoo`

To compile Coq proofs and `ocaml2zoo` in the same opam switch, you need to install [this custom version of the OCaml compiler](https://github.com/clef-men/ocaml/tree/atomic_fields_11) featuring atomic record fields.
Hopefully, the corresponding PR should be merged one day.

The following commands take care of this:

```
opam switch create . --empty --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git
eval $(opam env --switch=. --set-switch)
opam pin add ocaml-variants git+https://github.com/clef-men/ocaml#atomic_fields_11 --yes
```

To compile Coq proofs, run:

```
opam install ./coq-zoo.opam --deps-only --yes
make -j
```

To compile `ocaml2zoo`, run:

```
cd ocaml2zoo
opam install . --deps-only --yes
make
```
