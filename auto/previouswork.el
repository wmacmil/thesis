(TeX-add-style-hook
 "previouswork"
 (lambda ()
   (TeX-run-style-hooks
    "latex/ContrClean")
   (LaTeX-add-labels
    "fig:M1"
    "fig:M2"
    "fig:M3"))
 :latex)

