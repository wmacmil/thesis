(TeX-add-style-hook
 "roadmap.lagda"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("babel" "english")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "grammar"
    "article"
    "art11"
    "mlt-thesis-2015"
    "multicol"
    "csquotes"
    "float"
    "babel"
    "graphicx"
    "setspace"
    "tikz-cd"
    "dsfont"
    "fontspec"
    "fullpage"
    "hyperref"
    "agda"
    "unicode-math"
    "stmaryrd"
    "amsfonts"
    "mathtools"
    "xspace"
    "enumitem"
    "newunicodechar"
    "xcolor"
    "listings"
    "xparse"
    "ebproof")
   (TeX-add-symbols
    '("equivalenceH" 2)
    '("appH" 2)
    '("arrowH" 2)
    '("comprehensionH" 3)
    '("equalH" 2)
    '("define" 1)
    '("refl" 1)
    "jdeq"
    "defeq"
    "UU"
    "bbU"
    "type")
   (LaTeX-add-environments
    "definition"
    "lem"
    "proof"
    "thm")
   (LaTeX-add-bibliographies
    "example_bibliography")
   (LaTeX-add-xparse-macros
    '("codeword" "v")
    '("term" "v")
    '("keyword" "v")))
 :latex)

