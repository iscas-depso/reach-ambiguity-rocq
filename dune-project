(lang dune 3.14)

(name position-automata)

(generate_opam_files true)

(using coq 0.8)

(authors "reach-ambiguity contributors")

(package
 (name position-automata)
 (synopsis "Rocq formalization of position automata and reach ambiguity")
 (depends
  (rocq-prover (>= 9.0))
  (rocq-stdlib (>= 9.0))))
