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
  (name zoo_mcas)
  (synopsis "Multi-word compare-and-set")
  (depends
    zoo
    zoo_std
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
