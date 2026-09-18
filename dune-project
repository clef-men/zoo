(lang dune 3.21)

(using rocq 0.11)

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
 (depends
  (rocq-core (= 9.2.0))
  (rocq-stdlib (= 9.2.0))
  rocq-stdpp
  rocq-please
  (rocq-iris (= dev.2026-07-19.0.5b67fadf))
  (rocq-diaframe (= dev.2026-08-13.0.c7a7406d))
 )
)

(package
 (name rocq-zoo-std)
 (synopsis "zoo-std verification")
 (depends
  rocq-zoo
 )
)

(package
 (name rocq-zoo-data)
 (synopsis "zoo-data verification")
 (depends
  rocq-zoo-std
 )
)

(package
 (name rocq-zoo-backoff)
 (synopsis "backoff specification")
 (depends
  rocq-zoo
 )
)

(package
 (name rocq-zoo-unix)
 (synopsis "unix specification")
 (depends
  rocq-zoo
 )
)

(package
 (name rocq-zoo-saturn)
 (synopsis "zoo-saturn verification")
 (depends
  rocq-zoo-std
  rocq-zoo-backoff
 )
)

(package
 (name rocq-zoo-parabs)
 (synopsis "zoo-parabs verification")
 (depends
  rocq-zoo-std
  rocq-zoo-saturn
 )
)

(package
 (name rocq-zoo-eio)
 (synopsis "zoo-eio verification")
 (depends
  rocq-zoo-std
  rocq-zoo-unix
 )
)

(package
 (name rocq-zoo-mcas)
 (synopsis "zoo-mcas verification")
 (depends
  rocq-zoo-std
 )
)

(package
 (name rocq-zoo-examples)
 (synopsis "examples verification")
 (depends
  rocq-zoo-parabs
 )
)
