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


## Paper coverage

Our POPL'26 publication is available at TODO.

(TODO: consider including the current version of the PDF within the artifact repository?)

In this section we detail the mapping between the claims in the paper and our mechanized development.

### Section 2: Zoo in practice

Figure 1 (Treiber stack example): see `lib/zoo_saturn/mpmc_stack_1.ml` and `theories/zoo_saturn/mpmc_stack_1.v`

Figure 2 (full syntax of ZooLang): see `theories/zoo/language/syntax.v` for the Rocq AST definitions, and `notations.v` for the syntactic sugar.

> ZooLang comes with a program logic based on Iris, proved correct with respect to its small-step
> operational semantics.

The operational semantics are defined in `theories/zoo/language/semantics.v`. More precisely, this file defines basic building blocks (base steps, evaluation contexts), and then the Iris framework can automatically instantiate a full operational semantics on top of this, and this is done in `language.v`.

The program logic is in `theories/zoo/program_logic/wp.v`. The proof of correctness with respect to the semantics is in `adequacy.v`. The definition of the `safe` predicate occurring in the statement of adequacy is in `theories/zoo/iris/program_logic/language.v`.

The proof of the `stack_push_spec` specificatino shown in Section 2.3 can be found in `theories/zoo_saturn/mpmc_stack_1.v`, at the full name `mpmc_stack_1_push_spec`.

### Section 3: Zoo features

Basically all verified implementations (see `lib/...`) contain algebraic data types.

Mutually-recursive functions can be found for example in `lib/zoo_saturn/mpmc_bstack.ml`, a "bounded" variant of the Treiber stack where `push` and `push_aux` are mutually-recursive.

The translation of atomic operations mentioned in 3.3 is in the `ocaml2zoo` tool (which is hosted in a separate source repository), in `ocaml2zoo/lib/zoo/implementation_of_cmt.ml`.

The definition of `Zoo.proph` and `Zoo.resolve` are in `lib/zoo/zoo.{ml,mli}`. (Prophecies are represented at runtime by `dummy` value that is a freshly allocated reference, guaranteed to be distinct from any other value.)


### Section 4: OCaml extensions

These parts of the paper describe experimental variants of the OCaml compiler, which lie outside the Zoo repository.


### Section 5: Physical equality

#### HeapLang

The definition of physical equality in HeapLang can be found in the `iris` repository:

- the semantics of equality are defined in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/c5014d246b2cc5d1bf79d3ba362501dd7b447f74/iris_heap_lang/lang.v#L569-574
  where you can see that they are undefined unless `vals_compare_safe v1 v2` holds

- `vals_compare_safe` is defined in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/c5014d246b2cc5d1bf79d3ba362501dd7b447f74/iris_heap_lang/lang.v#L197
  and it uses the `val_is_unboxed` predicate defined in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/c5014d246b2cc5d1bf79d3ba362501dd7b447f74/iris_heap_lang/lang.v#L180

- to understand the definition of `val_is_unboxed`, see the definition of the HeapLang value representation in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/c5014d246b2cc5d1bf79d3ba362501dd7b447f74/iris_heap_lang/lang.v#L148


For an example of the extra indirections added in HeapLang implementations to satisfy this `val_is_unboxed` constraint, see the `iris-examples` directory

  https://gitlab.mpi-sws.org/iris/examples/-/blob/426893b7d67cd4456f89337d9163b3b4a91734d0/theories/concurrent_stacks/concurrent_stack1.v#L9

In the `push` code for example, `("v", "tail")` allocates a boxed pair, then `ref` boxes this with an extra indirection (on the other hand `SOME` which is `InjL` does not result in extra boxing).


#### ZooLang

ZooLang values are formally defined in `theories/zoo/language/syntax.v` (see `with val :=`). The `gen` argument of `ValBlock`, of type `generativity`, is omitted from 5.2 as this concept has not been introduced in the paper yet.

The key definitions for physical equality in the mechanized development are `val_similar` and `val_nonsimilar` in `theories/zoo/language/physical_equality.v`, which are defined via a translation to low-level values (`val_to_low`) and then `lowval_simliar` and `lowval_nonsimilar`, all in the same file.

Note: the notations `≈` and `≉` are used for `val_similar` and `val_nonsimilar` throughout the development, overloaded via the type-classes `Similar` and `Nonsimilar` defined in `theories/zoo/common/typeclasses.v`.

Finally, the specification `physeq_spec` in the paper in fact corresponds to the WP rule `wp_equal_nobranch` in `theories/zoo/program_logic/wp.v`.

_Generative constructors_: The type `'a glist` in the paper is defined in `lib/zoo_std/glst.ml`, and this `Glst` module is used in the Treiber stack implementation `lib/zoo_saturn/mpmc_stack_1.ml`; you can also find the `[@generative]` annotations on the constructors of the `Rcfd.state` datatype in `lib/zoo_eio/rcfd.ml`.

### Section 6: Structural equality

The definition of structural equality as a recursive function is in `theories/zoo/program_logic/structural_equality.v`; this (simple) code looks like a `ocaml2zoo`-translated program, but it was in fact written by hand. The lemmas `structeq_spec` and `structeq_spec_abstract` are to be found in this same file, under the same name. (In the statement of `struct_eq_abstract` we use `val_physeq` in the paper but it is `val_similar` in the Rocq development, via the infix notation.)

### Section 7: Standard data structures

Sequential data structures:

- array: `{lib,theories}/zoo_std/array.{ml,mli,v}`

- dynamic arrays: `{lib,theories}/zoo_std/dynarray_{1,2}.{ml,mli,v}`
  (Version 1 does not preserve memory safety under concurrent usage,
   so it is only safe sequentially. Version 2 corresponds to
   the Dynarray module discussed in Section 11.1.)

- list: `{lib,theories}/zoo_std/lst.{ml,mli,v}`
- stack: `{lib,theories}/zoo_std/stack.{ml,mli,v}`
- unbounded queues: `{lib,theories}/zoo_std/queue_{1,2,3}.{ml,mli,v}`
- bounded queue: `{lib,theories}/zoo_std/bqueue.{ml,mli,v}`
- double-ended queue: `{lib,theories}/zoo_std/deque.{ml,mli,v}`

> we developed an extensive collection of flexible specifications for the iterators of the Array and List modules

See `array_iteri_slice_{spec,spec',spec_atomic,spec_disentangled,spec_disentangled'}` for example.
(In `theories/zoo_std/array.v`.)

> our formalization of Array features different (fractional) predicates to express the ownership of either an entire array, a slice or even a circular slice

See `array_slice` and `array_cslice`.

Concurrent data structures:

- domain: `{lib,theories}/zoo_std/domain.{ml,mli,v}`; including domain-local storage: see `local_{new,get,set}`
- mutex: `{lib,theories}/zoo_std/mutex.{ml,mli,v}`
- (counting) semaphore: `{lib,theories}/zoo_std/semaphore.{ml,mli,v}`
- condition variable: `{lib,theories}/zoo_std/condition.{ml,mli,v}`
- write-once variable: `{lib,theories}/zoo_std/ivar_{1,2,3}.{ml,mli,v}`
  + version 1: does not support waiting, only `try_get`
  + version 2: waiting on a condition variable
  + version 3: a lock-free waiting mechanism
- atomic array: `{lib,theories}/zoo_std/atomic_array.{ml,mli}`
  This module is defined in terms of Stdlib.Atomic_array in the standard library
  of our experimental OCaml compiler (atomic arrays are not yet merged upstream),
  but get rewritten into calls to `Zoo_std.Array` by the ocaml2zoo translation layer,
  because in our sequentially-consistent model atomic and non-atomic arrays have
  exactly the same specifications.

### Section 8: Persistent data structures

> we verified a collection of persistent data structures.  This includes purely functional data structures such as persistent stack and queue, but also efficient imperative implementations of persistent array from Conchon and Filliâtre [2007], store and union-find from Allain, Clément, Moine and Scherer [2024]

Persistent stack and queue: `{lib,theories}/zoo_persistent/{pstack,pqueue}.{ml,mli,v}`

Persistent arrays from Conchon and Filliâtre: `{lib,theories}/zoo_persistent/parray_{1,2}.{ml,mli,v}`
+ version 1 implicitly restores old version on access (as in the Conchon-Filliâtre API)
+ version 2 has an explicit capture/restore interface (as in the Store API)

Store: `{lib,theories}/zoo_persistent/pstore_{1,2}.{ml,mli,v}`
+ version 1 does not perform record elision
+ version 2 adds generations and thus the record elision optimization

Persistent union-find on top of Store references: `{lib,theories}/zoo_persistent/puf.{ml,mli,v}`
This implementation does rank-based path compression, so it has the optimal inverse-Ackermann complexity. It is modeled in the correctness proof by a map from each element to its canonical representative.

### Section 9: RCFD

The fragment of Eio.Rcfd that we verified can be found in `lib/zoo_eio/rcfd.ml`, with the proofs in `theories/zoo_eio/rcfd.v`. In particular the per-FD logical state is defined by the `lstate` datatype and the `lstep` predicates in `rcfd.v`.

### Section 10: Saturn

> We verified three variants of the Treiber stack [Treiber 1986]: 1) unbounded MPMC (the standard one), 2) bounded MPMC, 3) closable unbounded MPMC.

1. `lib/zoo_saturn/mpmc_stack_1.ml`:
2. `lib/zoo_saturn/mpmc_stack_2.ml`:
3. `lib/zoo_saturn/mpmc_bstack.ml`:

> We verified four variants of the Michael-Scott queue [Michael and Scott 1996]: 1) unbounded MPMC (the standard one), 2) bounded MPMC, 3) unbounded MPSC and 4) unbounded SPMC.

1. `lib/zoo_saturn/mpmc_queue_1.ml`
2. `lib/zoo_saturn/mpmc_bqueue.ml`
3. `lib/zoo_saturn/mpsc_queue_1.ml`
4. `lib/zoo_saturn/spmc_queue.ml`

> Using atomic record fields, we can represent the list more efficiently, without the extra indirection. However, there is one subtlety: in this new representation, we need to clear the outdated nodes so that their value is no longer reachable and can be garbage-collected, in other words to prevent a memory leak.

In `mpmc_queue_1.ml`, clearing is done in `pop` by

```ocaml
new_front_r.data <- Obj.magic () ;
```

This uses unsafe language features, but we prove that it is correct (in a SC model).

> we introduce the notion of explicit chain that allows decoupling the chain structure formed by the nodes and the content of the nodes

See `theories/zoo_std/xchain.v`.


> [...] this is called an external linearization point. To handle this in the proof, we introduced a mechanism in the invariant to transfer the Iris resource materializing the linearization point from is_empty to push and vice versa.

The external linearlization point in the invariant is the `waiter_au` proposition mentioned in `waiter_model`.

> A standard way to implement a sequential queue is to use two stacks: producers push onto the back stack while consumers pop from the front stack, stealing and reversing the back stack when needed. Based on this simple idea, Vesa Karvonen developed a new lock-free concurrent queue. We verified (1) the MPMC variant used in Picos and (2) the closable MPSC variant used in Eio.

1. `lib/zoo_saturn/mpmc_queue_2.ml`
2. `lib/zoo_saturn/mpsc_queue_3.ml`

Note: mpsc_queue_3.ml is based on a MPSC implementation in Saturn. Eio includes its own version of this queue, itself inspired by the Saturn implementation: https://github.com/ocaml-multicore/eio/blob/7695d22387af7dc98214d66ad003dfad7b2a38f8/lib_eio/utils/lf_queue.ml#L5

> Essentially, the concurrent protocol — and therefore the Iris invariant — includes a destabilization phase during which a new back stack pointing to the former one awaits to be stabilized

See `theories/zoo_saturn/mpmc_queue_2.v`, in particular the `status` inductive (`Stable` or `Unstable`) and the `step_destabilize` and `step_stabilize` constructors of the `step` relation.

### Section 11: memory safety

> We verified (a representative fragment of) the proposed Dynarray implementation in ZooLang...

`lib/zoo_std/dynarray_2.{ml,mli}` implements the following functions: `create`, `make`, `init`, `size`, `capacity`, `is_empty`, `get`, `set`, `reserve`, `reserve_extra`, `grow`, `push`, `pop`, `fit_capacity`, `reset`, `iteri` and `iter`.

> ...proving that it is functionally correct under sequential usage, ...

`theories/zoo_std/dynarray_2.v`: the sequential-usage specs are the `dynarray_2_<operation>_spec` lemmas, which assume unique ownership of `dynarray_2_model t vs`, which corresponds to the "strong invariant" mentioned in the paper.

> ...and that it does preserve memory-safety even under concurrent usage.

The concurrent-usage specs are the `dynarray_2_<operation>_type` lemmas, which provide specifications for the same operations but only require the persistent `itype_dynarray_2 t` predicate, which corresponds to the "weak invariant" mentioned in the paper.

> [Saturn] This erasure is performed by writing a non-type-safe dummy value, Obj.magic ().

See our references about Section 10 above.
