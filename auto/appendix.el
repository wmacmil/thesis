(TeX-add-style-hook
 "appendix"
 (lambda ()
   (TeX-run-style-hooks
    "latex/monoid"
    "latex/twinsigma"
    "latex/compare"
    "latex/Id")
   (LaTeX-add-labels
    "judge"
    "homo"
    "def:def3"
    "def:def4"
    "hottproofs"))
 :latex)

