(TeX-add-style-hook
 "roadmap.lagda"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("babel" "english")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "perspectives"
    "previouswork"
    "mltt"
    "gfintro"
    "article"
    "art11"
    "mlt-thesis-2015"
    "babel"
    "graphicx"
    "setspace"
    "fontspec"
    "fullpage"
    "hyperref"
    "agda"
    "unicode-math"
    "amsfonts"
    "mathtools"
    "xspace"
    "enumitem"
    "newunicodechar")
   (TeX-add-symbols
    '("id" ["argument"] 2)
    '("opp" 1)
    '("indid" 1)
    '("ind" 1)
    '("define" 1)
    '("refl" 1)
    "jdeq"
    "defeq"
    "blank"
    "UU"
    "rev"
    "bbU"
    "type")
   (LaTeX-add-labels
    "sec:intro"
    "eq:Jconv"
    "lem:opp")
   (LaTeX-add-environments
    "definition"
    "lem"
    "proof"
    "thm")
   (LaTeX-add-bibliographies
    "example_bibliography")
   (LaTeX-add-index-entries
    "loop space"
    "loop space!iterated"
    "iterated loop space"))
 :latex)

