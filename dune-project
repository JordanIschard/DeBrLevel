(lang dune 3.12)
(using coq 0.8)

(package
 (name Level-DeBr)
 (synopsis "Helper for using De Bruijn level representation.")
 (description "Representation of binders or arbitrary names can be annoying and use of representation is common. We develop a collection of modules and module types for simply defined Types or Sets that use De Bruijn levels as a representation.")
 (depends (coq-mmaps (= "dev")))
 (authors "Ischard Jordan")
 (maintainers "Ischard Jordan"))

(generate_opam_files)