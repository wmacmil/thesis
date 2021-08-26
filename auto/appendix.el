(TeX-add-style-hook
 "appendix"
 (lambda ()
   (TeX-run-style-hooks
    "latex/compare")
   (LaTeX-add-labels
    "cubicaltt"
    "hottproofs"))
 :latex)

