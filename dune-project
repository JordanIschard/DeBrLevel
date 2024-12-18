(lang dune 3.12)
(using coq 0.8)
(version 1.0.2)

(name coq-debr-lvl)

(package

  (name coq-debr-lvl)

  (synopsis "Collection of interfaces and implementations for a modular using of De Bruijn level")

  (description 
    "Formalization of a language often implies variables or equivalent. A specific representation of them is required in order 
    to avoid capture issues. Consequently, we define here a collection of interfaces and implementations for using De Bruijn level.
    In addition to the definition of a level and its minimal set of functions/properties, we propose a modular way to define a
    'leveled' elements and provide numerous predefined data types and data structures such as option, pair, list, map, etc."
  )


  (license GPL-3.0-or-later)

  (depends
    (coq (= 8.18.0))
    (coq-mmaps (>= 1.1))
  )

  (authors "Ischard Jordan")

  (maintainers "Ischard Jordan")

  (source (github JordanIschard/DeBrLevel))
)

(generate_opam_files)
