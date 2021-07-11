(TeX-add-style-hook
 "screport.tex"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("scrreprt" "fontsize=11pt" "")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("fontenc" "T1") ("ulem" "normalem") ("agda" "bw") ("dot2texi" "debug")))
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
    "scrreprt"
    "scrreprt10"
    "fontenc"
    "graphicx"
    "grffile"
    "longtable"
    "wrapfig"
    "rotating"
    "ulem"
    "amsmath"
    "textcomp"
    "amssymb"
    "capt-of"
    "hyperref"
    "agda"
    "dot2texi"
    "tikz-cd"
    "tikz"
    "tabularx"
    "enumitem"
    "comment"
    "quiver"
    "xeCJK"
    "geometry"
    "amsthm"
    "thmtools"
    "fontspec"
    "newunicodechar")
   (TeX-add-symbols
    '("AB" 1)
    '("AK" 1)
    '("AR" 1)
    '("AFd" 1)
    '("AF" 1)
    '("AIC" 1)
    '("AD" 1)
    "lBrace"
    "rBrace")
   (LaTeX-add-environments
    "mywrapper")
   (LaTeX-add-thmtools-declaretheoremstyles
    "mystyle")
   (LaTeX-add-thmtools-declaretheorems
    "theorem"
    "lemma"
    "corollary"
    "definition"
    "example"
    "remark"
    "notation"))
 :latex)

