(TeX-add-style-hook
 "hottgrammars"
 (lambda ()
   (TeX-run-style-hooks
    "latex/ContrClean")
   (LaTeX-add-labels
    "rantaHott"
    "cubic"))
 :latex)

