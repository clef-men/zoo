(lang dune 3.0)

(name zoo)

(generate_opam_files)

(authors
 "Clément Allain"
)
(maintainers
 "clement.allain@cs.au.dk"
)

(source (github clef-men/zoo))
(license ISC)

(package
 (name zoo)
 (synopsis "Zoo")
)

(package
 (name zoo-std)
 (synopsis "Zoo standard library")
 (depends
  zoo
 )
)

(package
 (name zoo-data)
 (synopsis "Collection of data structures")
 (depends
  zoo-std
 )
)

(package
 (name zoo-saturn)
 (synopsis "Saturn")
 (depends
  backoff
  zoo
  zoo-std
 )
)

(package
 (name zoo-parabs)
 (synopsis "Parabs")
 (depends
  zoo
  zoo-std
  zoo-saturn
  ; benchmark dependencies
  (domainslib :with-dev-setup)
  (moonpool :with-dev-setup)
 )
)

(package
 (name zoo-eio)
 (synopsis "Eio")
 (depends
  zoo-std
 )
)

(package
 (name zoo-mcas)
 (synopsis "Multi-word compare-and-set")
 (depends
  zoo
  zoo-std
 )
)

(package
 (name rocq-zoo)
 (synopsis "Zoo")
 (allow_empty)
)

(package
 (name rocq-zoo-std)
 (synopsis "Zoo standard library")
 (allow_empty)
)
