(TeX-add-style-hook
 "intro"
 (lambda ()
   (TeX-run-style-hooks
    "latex/monoid")
   (LaTeX-add-labels
    "sec:intro"))
 :latex)

