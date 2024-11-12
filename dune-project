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
)

(package
  (name zoo_persistent)
  (synopsis "Persistent and semi-persistent data structures")
  (depends
    zoo_std
  )
)

(package
  (name saturn)
  (synopsis "Saturn")
  (depends
    zoo
    zoo_std
  )
)

(package
  (name eio)
  (synopsis "Eio")
  (depends
    zoo_std
  )
)

(package
  (name kcas)
  (synopsis "Kcas")
  (depends
    zoo
    zoo_std
  )
)

(package
  (name partition)
  (synopsis "Partition")
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
