(TeX-add-style-hook
 "mlt-thesis-2015"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "margin=2.5cm")))
   (TeX-run-style-hooks
    "fontspec"
    "natbib"
    "geometry")
   (TeX-add-symbols
    '("subtitle" 1)
    "numberline")
   (LaTeX-add-fontspec-newfontcmds
    "csffamily"))
 :latex)

