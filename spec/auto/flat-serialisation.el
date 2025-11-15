;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "flat-serialisation"
 (lambda ()
   (TeX-add-symbols
    "etype"
    "dtype"
    "arrow")
   (LaTeX-add-labels
    "appendix:flat-serialisation"
    "sec:encoding-and-decoding"
    "sec:basic-flat-encodings"
    "sec:flat-term-encodings"
    "table:term-tags"
    "table:type-tags"
    "sec:flat-constants"
    "table:builtin-tags-batch-1"
    "table:builtin-tags-batch-2"
    "table:builtin-tags-batch-4"
    "table:builtin-tags-batch-5"
    "table:builtin-tags-batch-6"
    "sec:cardano-issues"
    "fig:index-bytestring-example"))
 :latex)

