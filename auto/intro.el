(TeX-add-style-hook
 "intro"
 (lambda ()
   (TeX-run-style-hooks
    "perspectives")
   (LaTeX-add-labels
    "sec:intro"
    "fig:M1"
    "fig:M2"
    "fig:M3"))
 :latex)

