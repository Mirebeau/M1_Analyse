# Lean pages

`build.py` builds `index.html`: the statements of the course notes `M1_Analyse.tex`, each with its
Lean formalization (docstring, statement and complete proof), the Mathlib notions of the statement
and the Mathlib lemmas used by the proof (with links to the Mathlib documentation). Adapted from
`LeanHJB_Autoformalisation/scripts/proof_map/`.

A Lean declaration formalizes the course labels cited between backticks in the bold lead of its
docstring, e.g. `/-- **Déf. `def:topo` (Espace topologique).** ... -/`; a Lean module covers the
section label cited in the title of its module docstring.

To regenerate, after `lake build`, from the project directory:

    python3 scripts/lean_pages/build.py            # local page only (scripts/lean_pages/index.html)
    python3 scripts/lean_pages/build.py --publish  # also update the public website
    python3 scripts/lean_pages/leancheck.py        # rewrite leananchors.tex (no Lean needed)

`--publish` copies the page to the clone `../lean-proof-maps` of the public repository
`github.com/Mirebeau/lean-proof-maps` (folder `M1Analyse/`), commits and pushes (SSH); GitHub Pages
serves it at <https://mirebeau.github.io/lean-proof-maps/M1Analyse/>.

## Links from the course

`leancheck.py` writes `leananchors.tex` next to `M1_Analyse.tex`, defining `\leancheck{<label>}`: a
small "Lean✓" mark linking to `<site>#label=<label>`, or nothing and a LaTeX warning if no Lean
declaration cites the label. It is loaded by `\input{leananchors}` after `hyperref`; the marks are
placed on their own line right after the `\label` (after `\end{equation}` for an equation).
Rerun it after formalizing new statements.
To compile the course without Lean links, put `\newcommand\leancheck[1]{}` before
`\input{leananchors}` (or on the command line); `leananchors.tex` then does nothing.

`paper.py` compiles a copy of the course in `build/paper` (when the sources changed) and reads the
`.aux` (printed numbers, pages, section titles); it converts each statement to HTML, the math being
typeset by KaTeX in the browser with the macros of the preamble.
