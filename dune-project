(lang dune 3.12)
(using coq 0.8)
(version 0.1)
(name coq-debr-lvl)

(package
 (name coq-debr-lvl)
 (synopsis "Helper for using De Bruijn level representation.")
 (description "Representation of binders or arbitrary names can be annoying and use of representation is common. We develop a collection of modules and module types for simply defined Types or Sets that use De Bruijn levels as a representation.")
 (depends
  (coq (= 8.18.0))
  (coq-mmaps (>= 1.1))
 )
 (authors "Ischard Jordan")
 (maintainers "Ischard Jordan")
 (source (github JordanIschard/DeBrLevel)))

(generate_opam_files)
