(TeX-add-style-hook
 "natproof"
 (lambda ()
   (TeX-run-style-hooks
    "latex/nproof")
   (LaTeX-add-labels
    "npf"
    "assoc"))
 :latex)

