This artifact is available online at:

- TODO (github + Zenodo)

## Building and installation

See [README.md](./README.md).

## Architecture

The Zoo source code is split across `lib/` and `theories/`, which have the same organization: `lib/` contains OCaml source modules whose implementation fits in the Zoo fragment, and `theories/` contains Rocq proofs about those modules. Some of those modules are grouped in libraries that can be installed as standard OCaml libraries, and can depend on each other.

For example, `lib/examples/fibonacci.ml` is an implementation of a fibonacci function using the `Parabs` scheduler, and `theories/examples/` contains a correctness proof for this function in Rocq. The proof refers to a deep embedding of the `fibonacci` code, that is produced by the build system by calling the `ocaml2zoo` translator.

Finally, the `bench/` directory contains preliminary benchmark scripts and some benchmark data.

The libraries are organized as follows (in both `lib/` and `theories/`, they share the same organization):

- `examples/`: a simple example (fibonacci function)
- `zoo/`: core definitions of the ZooLang language ;

  in `lib/`, this contains only a few definitions around prophecy variables, but in `theories/` there is a whole infrastructure to define the syntax and semantics of ZooLang, instantiate it as an Iris language, etc.

  + `theories/zoo/{common,ltac2}`: common utilities
  + `theories/zoo/diaframe`: support for Diaframe proof automation
  + `theories/zoo/iris`: non-Zoo-specific extensions to the Iris standard library
  + `theories/zoo/language`: ZooLang definition, in particular
    * syntax in `syntax.v`
    * operational semantics in `semantics.v`
    * syntactic sugar in `notations.v`
  + `theories/zoo/program_logic`: the Zoo program logic (see `wp.v`)

- `zoo_std/`: basic librariries for ZooLang programs, mostly a subset of the OCaml standard library, but also some Zoo-specific libraries (`ivar`, `inf_array`, etc.)
- `zoo_eio/`: the Rcfd module from the EIO library, with proofs
- `zoo_persistent/`: persistent data structures
  + a persistent queue (pair of lists) in `pqueue.v`
  + (sequential) persistent arrays in `parray_{1,2}.{ml,v}` in Conchon-Filliatre style
    (version 1 implicitly restores old version on access, version 2 has an explicit capture/restore interface)
  + a heterogeneous (sequential) persistent store in `pstore_{1,2}.{ml,v}`, generalizing the persistent-array data structure, following the [Store] paper
    (both versions have the same interface, version 2 adds generations and thus the record-elision optimization)
- `zoo_saturn/`: concurrent data structures, many variants

- other libraries that are not covered by the POPL'26 publication (and may be work-in-progress): `boxroot`, `kcas`, `parabs`, `partition`.

In addition, `theories/unix` provides an axiomatization of a couple file-descriptor operations of the `Unix` module, which are used in `Rcfd`.

[Store]: https://inria.hal.science/hal-04887939
