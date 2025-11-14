(lang dune 3.0)

(name zoo)

(generate_opam_files)

(authors
  "Clément Allain"
)
(maintainers
  "clement.allain@inria.fr"
)

(source (github clef-men/zoo))
(license ISC)

(package
  (name zoo)
  (synopsis "Zoo")
)

(package
  (name zoo_std)
  (synopsis "Zoo standard library")
  (depends
    zoo
  )
)

(package
  (name zoo_persistent)
  (synopsis "Persistent and semi-persistent data structures")
  (depends
    zoo_std
  )
)

(package
  (name zoo_saturn)
  (synopsis "Saturn")
  (depends
    zoo
    zoo_std
  )
)

(package
  (name zoo_parabs)
  (synopsis "Parabs")
  (depends
    zoo
    zoo_std
    zoo_saturn
    ; benchmark dependencies
    (domainslib :with-dev-setup)
    (moonpool :with-dev-setup)
  )
)

(package
  (name zoo_eio)
  (synopsis "Eio")
  (depends
    zoo_std
  )
)

(package
  (name coq-zoo)
  (synopsis "Zoo")
  (allow_empty)
)

(package
  (name coq-zoo-std)
  (synopsis "Zoo standard library")
  (allow_empty)
)
