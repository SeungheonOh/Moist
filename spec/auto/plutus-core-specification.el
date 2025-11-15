;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "plutus-core-specification"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("report" "a4paper")))
   (TeX-run-style-hooks
    "latex2e"
    "header"
    "introduction"
    "notation"
    "untyped-grammar"
    "builtins"
    "untyped-reduction"
    "untyped-cek-machine"
    "cardano/cardano"
    "formal-verification"
    "data-cbor"
    "flat-serialisation"
    "report"
    "rep10")
   (LaTeX-add-bibliographies))
 :latex)

