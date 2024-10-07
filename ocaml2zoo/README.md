## Building

In order to build and use `ocaml2zoo`, you need to install [this custom version of the OCaml compiler](https://github.com/clef-men/ocaml/tree/atomic_fields_11) featuring atomic record fields.
Hopefully, the corresponding PR should be merged one day.

The following commands take care of this:

```
opam switch create . --empty
eval $(opam env --switch=. --set-switch)
opam pin add ocaml-variants git+https://github.com/clef-men/ocaml#atomic_fields_11 --yes
opam install . --deps-only --yes
```

Then you can build `ocaml2zoo`:
```
make
```
