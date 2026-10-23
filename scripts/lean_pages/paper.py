"""Adapted from LeanHJB_Autoformalisation/scripts/proof_map/paper.py for the course notes
M1_Analyse (French theorem names, sections down to subsubsections, `\\IeC` accents in the .aux).

The paper side of the proof map: printed numbers, section titles and statements (as HTML with
the math left for KaTeX), read from the LaTeX sources and from the `.aux` file of a compilation.

`paper_data(paper_dir, build_dir)` compiles a copy of the paper in `build_dir` (pdflatex, twice)
when the `.aux` there is older than the sources, then returns a JSON-ready dict:
  macros:   KaTeX macros from the preamble (`\\def`, `\\newcommand`, `\\DeclareMathOperator`)
  sections: [{num, title, page}] (numbered sections, in order)
  labels:   {label: {kind, num, page, ref, env, title, html}}, where `ref` is the printed reference
            ("Lemma 2.21", "(11)", ...), `env` the label of the enclosing statement (for items and
            equations inside a statement), `title` its optional name, `html` its text.
Unknown text-mode commands are reported on stderr, so that the conversion can be completed.
"""
import html
import re
import shutil
import subprocess
import sys
from pathlib import Path

THEOREMS = ("theorem", "lemma", "proposition", "corollary", "remark", "definition", "assumption",
            "exemple", "notation", "exo")
KINDS = {"theorem": "Théorème", "lemma": "Lemme", "proposition": "Proposition",
         "corollary": "Corollaire", "remark": "Remarque", "definition": "Définition",
         "assumption": "Hypothèse", "exemple": "Exemple", "notation": "Notation",
         "exo": "Exercice", "section": "Section", "subsection": "Section",
         "subsubsection": "Section", "figure": "Figure", "table": "Table"}
MATH_ENVS = ("equation", "equation*", "align", "align*", "gather", "gather*", "multline",
             "multline*", "eqnarray", "eqnarray*")
# KaTeX equivalents of macros it does not know
KATEX_OVERRIDES = {r"\mathbbm": r"\mathbb", r"\bbone": r"\mathbb{1}",
                   r"\overpar": r"\overgroup{#1}"}  # \aoverbrace (abraces) is unknown to KaTeX
TEXT_MACROS = {r"\ve": "ε", r"\eg": "e.g.", r"\ie": "i.e.", r"\facultatif": "✈",
               r"\loc": "loc", r"\cdots": "⋯"}
WRAPPERS = {"emph": ("<em>", "</em>"), "textit": ("<em>", "</em>"), "textsl": ("<em>", "</em>"),
            "textbf": ("<strong>", "</strong>"), "texttt": ("<code>", "</code>"),
            "textrm": ("", ""), "text": ("", ""), "mbox": ("", ""), "textup": ("", ""),
            "textnormal": ("", ""), "footnote": (' <span class="fn">(', ")</span>")}
IGNORED = ("label", "leancheck", "leancheckdef", "claudereport", "formalizationInstruction",
           "todo", "todoi", "notei", "hiddenproof", "inventaire", "index", "phantom", "vspace",
           "hspace")


# ---------------------------------------------------------------------------- LaTeX scanning

def strip_comments(s):
    return re.sub(r"(?<!\\)%[^\n]*", "", s)


def group(s, i, open_="{", close="}"):
    """The balanced group starting at `s[i] == open_`: (content, index after the group)."""
    assert s[i] == open_, (s[i:i + 30])
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == open_:
            depth += 1
        elif c == close:
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ValueError("unbalanced group: " + s[i:i + 60])


def skip_ws(s, i):
    while i < len(s) and s[i] in " \t\n":
        i += 1
    return i


def remove_commands(s, names):
    """Remove `\\name[opt]{arg}` (and `\\name*`) for the given command names."""
    pat = re.compile(r"\\(" + "|".join(map(re.escape, names)) + r")\*?(?![A-Za-z@])")
    out, i = [], 0
    while (m := pat.search(s, i)):
        out.append(s[i:m.start()])
        j = skip_ws(s, m.end())
        if j < len(s) and s[j] == "[":
            _, j = group(s, j, "[", "]")
            j = skip_ws(s, j)
        if j < len(s) and s[j] == "{":
            _, j = group(s, j)
        i = j
    return "".join(out) + s[i:]


# ---------------------------------------------------------------------------- macros

def katex_macros(main_tex):
    pre = strip_comments(main_tex.split("\\begin{document}")[0])
    macros = {}
    for m in re.finditer(r"\\def\s*(\\[A-Za-z]+|\\.)\s*\{", pre):
        body, _ = group(pre, m.end() - 1)
        macros[m.group(1)] = body
    for m in re.finditer(r"\\(?:re)?newcommand\s*\{?(\\[A-Za-z]+)\}?\s*(?:\[(\d)\])?\s*\{", pre):
        body, _ = group(pre, m.end() - 1)
        if "todo" not in body and "Users" not in body:
            macros[m.group(1)] = body
    for m in re.finditer(r"\\DeclareMathOperator\s*\{?(\\[A-Za-z]+)\}?\s*\{([^}]*)\}", pre):
        macros[m.group(1)] = r"\operatorname{" + m.group(2) + "}"
    macros.update(KATEX_OVERRIDES)
    return {k: v for k, v in macros.items() if "todo" not in k and "claudereport" not in k
            and "formalization" not in k and "pathPic" not in k}


# ---------------------------------------------------------------------------- .aux

def compile_aux(paper_dir, build_dir, main="M1_Analyse"):
    build_dir = Path(build_dir)
    aux = build_dir / (main + ".aux")
    sources = [Path(paper_dir) / (main + ".tex")] + list(Path(paper_dir).glob("Include/*.tex"))
    if aux.exists() and all(aux.stat().st_mtime > f.stat().st_mtime for f in sources):
        return aux
    if build_dir.exists():
        shutil.rmtree(build_dir)
    shutil.copytree(paper_dir, build_dir, ignore=shutil.ignore_patterns(
        ".texpadtmp", "*.pdf", ".git", ".lake", "scripts", "M1Analyse", "Old"))
    for cmd in (["pdflatex"], ["bibtex"], ["pdflatex"], ["pdflatex"]):
        arg = main if cmd == ["bibtex"] else main + ".tex"
        subprocess.run(cmd + (["-interaction=nonstopmode"] if cmd != ["bibtex"] else []) + [arg],
                       cwd=build_dir, capture_output=True)
    if not aux.exists():
        sys.exit("paper.py: the compilation of the paper produced no .aux")
    return aux


ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "c": "\u0327", "~": "\u0303"}


def decode_ieC(s):
    """`\\IeC {\\'e}` (utf8x/ucs in the .aux) to `é`."""
    import unicodedata
    s = re.sub(r"\\IeC\s*\{\\(['`^\"~]|c\s)\s*\{?(\w)\}?\}",
               lambda m: unicodedata.normalize("NFC", m.group(2) + ACCENTS[m.group(1).strip()]), s)
    return re.sub(r"\\IeC\s*\{([^{}]*)\}", r"\1", s)


def read_aux(aux):
    s = decode_ieC(Path(aux).read_text(errors="replace"))
    labels, cites, sections = {}, {}, []
    for m in re.finditer(r"\\newlabel\{([^}]+)@cref\}\{\{\[([^\]]*)\]\[[^\]]*\]\[[^\]]*\]([^}]*)\}"
                         r"\{\[[^\]]*\]\[([^\]]*)\]", s):
        labels[m.group(1)] = dict(kind=m.group(2), num=m.group(3), page=int(m.group(4) or 0))
    for m in re.finditer(r"\\newlabel\{([^}@]+)\}\{\{([^}]*)\}\{[^}]*\}\{((?:[^{}]|\{[^{}]*\})*)\}", s):
        if m.group(1) in labels:
            labels[m.group(1)]["plain"] = m.group(2)  # what \ref prints (a line number, ...)
            labels[m.group(1)]["title"] = m.group(3)  # what \nameref prints
    for m in re.finditer(r"\\bibcite\{([^}]+)\}\{([^}]+)\}", s):
        cites[m.group(1)] = m.group(2)
    for m in re.finditer(r"\\contentsline \{((?:sub)*section)\}\{\\numberline \{([^}]+)\}(.*?)\}"
                         r"\{(\d+)\}\{((?:sub)*section)\.", s):
        sections.append(dict(level=m.group(1).count("sub"), num=m.group(2), title=m.group(3),
                             page=int(m.group(4))))
    return labels, cites, sections


def ref_text(info):
    k = info["kind"]
    if k == "equation":
        return f"({info['num']})"
    if k == "enumi":
        return f"point {info['num']}"
    if k == "algorithm" and info.get("plain", info["num"]) != info["num"]:
        return f"line {info['plain']} of Algorithm {info['num']}"
    return f"{KINDS.get(k, k.capitalize())} {info['num']}"


# ---------------------------------------------------------------------------- statements

def environments(tex):
    """Theorem-like environments, displayed equations and algorithms of a chapter, with labels."""
    s = strip_comments(tex)
    found = []
    pat = re.compile(r"\\begin\{(" + "|".join(map(re.escape, THEOREMS + MATH_ENVS
                                                    + ("algorithm",))) + r")\}")
    for m in pat.finditer(s):
        env = m.group(1)
        end = s.find("\\end{" + env + "}", m.end())
        if end < 0:
            continue
        i, title = m.end(), ""
        if env in THEOREMS:
            j = skip_ws(s, i)
            if j < len(s) and s[j] == "[":
                title, i = group(s, j, "[", "]")
        body = s[i:end]
        found.append(dict(env=env, start=m.start(), end=end, title=title, body=body,
                          labels=re.findall(r"\\label\{([^}]+)\}", body)))
    return found


class Converter:
    """LaTeX text to HTML, the math being kept for KaTeX."""

    def __init__(self, labels, cites):
        self.labels, self.cites, self.unknown = labels, cites, set()

    def ref(self, keys, eq=False, plain=False):
        out = []
        for k in keys.split(","):
            k = k.strip()
            info = self.labels.get(k)
            if not info:
                out.append("??")
                continue
            t = (f"({info['num']})" if eq else info.get("plain", info["num"]) if plain
                 else ref_text(info))
            out.append(f'<a class="pref" href="#label={html.escape(k)}">{t}</a>')
        return " et ".join(out) if len(out) <= 2 else ", ".join(out[:-1]) + " et " + out[-1]

    def cite(self, opt, keys):
        ks = ", ".join(self.cites.get(k.strip(), k.strip()) for k in keys.split(","))
        return f"[{ks}{', ' + self.text(opt) if opt else ''}]"

    def math(self, m):
        m = remove_commands(m, ("label", "leancheck", "claudereport"))
        m = re.sub(r"\\(nonumber|notag)\b", "", m)
        m = re.sub(r"\\eqref\{([^}]+)\}", lambda x: r"\text{(" + ", ".join(
            self.labels.get(k.strip(), {}).get("num", "?") for k in x.group(1).split(",")) + ")}", m)
        return html.escape(m)

    def text(self, s):
        """Convert text mode, splitting off the math."""
        s = remove_commands(s, IGNORED)  # before splitting: their arguments may contain math
        out, i = [], 0
        mpat = re.compile(r"\$\$|\$|\\\[|\\\(|\\begin\{(" + "|".join(map(re.escape, MATH_ENVS))
                          + r"|cases)\}|\\(" + "|".join(WRAPPERS) + r")(?![A-Za-z])")
        while (m := mpat.search(s, i)):
            out.append(self.plain(s[i:m.start()]))
            tok = m.group(0)
            if m.group(2):  # a text command whose argument may contain math
                a, i = group(s, skip_ws(s, m.end()))
                o, c = WRAPPERS[m.group(2)]
                out.append(o + self.text(a) + c)
                continue
            if tok.startswith("\\begin"):
                env = m.group(1)
                j = s.find("\\end{" + env + "}", m.end())
                j = len(s) if j < 0 else j + len("\\end{" + env + "}")
                body = s[m.start():j]
                inner = body[len("\\begin{" + env + "}"):-len("\\end{" + env + "}")]
                if env == "cases":
                    out.append(self.math(body))
                else:  # KaTeX numbers nothing: a plain display (`align` becomes `aligned`, ...)
                    out.append(display(self, dict(env=env, body=inner)))
                i = j
                continue
            close = {"$$": "$$", "$": "$", "\\[": "\\]", "\\(": "\\)"}[tok]
            j = m.end()
            while True:
                j = s.find(close, j)
                if j < 0 or s[j - 1] != "\\":
                    break
                j += 1
            j = len(s) if j < 0 else j
            inner = s[m.end():j]
            if tok in ("$$", "\\["):
                out.append("\\[" + self.math(inner) + "\\]")
            else:
                out.append("$" + self.math(inner) + "$")
            i = j + len(close)
        out.append(self.plain(s[i:]))
        return "".join(out)

    def plain(self, s):
        s = remove_commands(s, IGNORED)
        res, i = [], 0
        while i < len(s):
            c = s[i]
            if c == "\\":
                m = re.match(r"\\([A-Za-z]+\*?|.)", s[i:], re.S)
                if not m:  # a lone backslash at the end
                    i += 1
                    continue
                name, j = m.group(1), i + m.end()
                if name in ("Nref", "nref", "nameref"):
                    j = skip_ws(s, j)
                    keys, j = group(s, j)
                    t = self.labels.get(keys.strip(), {}).get("title", "")
                    if name == "nameref":
                        res.append(html.escape(t))
                    else:
                        res.append(self.ref(keys) + (f" ({html.escape(t)})" if t else ""))
                elif name in ("cref", "Cref", "ref", "eqref", "autoref"):
                    j = skip_ws(s, j)
                    keys, j = group(s, j)
                    res.append(self.ref(keys, eq=name == "eqref", plain=name == "ref"))
                elif name in ("cite", "citep", "citet"):
                    j = skip_ws(s, j)
                    opt = ""
                    if s[j] == "[":
                        opt, j = group(s, j, "[", "]")
                        j = skip_ws(s, j)
                    keys, j = group(s, j)
                    res.append(self.cite(opt, keys))
                elif name in ("emph", "textit", "textsl"):
                    a, j = group(s, skip_ws(s, j))
                    res.append("<em>" + self.text(a) + "</em>")
                elif name in ("textbf",):
                    a, j = group(s, skip_ws(s, j))
                    res.append("<strong>" + self.text(a) + "</strong>")
                elif name in ("texttt",):
                    a, j = group(s, skip_ws(s, j))
                    res.append("<code>" + self.text(a) + "</code>")
                elif name in ("textrm", "text", "mbox", "textup", "textnormal"):
                    a, j = group(s, skip_ws(s, j))
                    res.append(self.text(a))
                elif name == "footnote":
                    a, j = group(s, skip_ws(s, j))
                    res.append(' <span class="fn">(' + self.text(a) + ")</span>")
                elif name in ("url",):
                    a, j = group(s, skip_ws(s, j))
                    res.append(f'<a href="{html.escape(a)}">{html.escape(a)}</a>')
                elif name == "begin":
                    env, j = group(s, skip_ws(s, j))
                    res.append({"itemize": "<ul>", "enumerate": "<ol>", "description": "<ul>",
                                "algorithmic": '<ol class="alg">'}.get(env, ""))
                    if env in ("enumerate", "algorithmic") and s[skip_ws(s, j):skip_ws(s, j) + 1] == "[":
                        _, j = group(s, skip_ws(s, j), "[", "]")
                elif name == "end":
                    env, j = group(s, skip_ws(s, j))
                    res.append({"itemize": "</li></ul>", "enumerate": "</li></ol>",
                                "description": "</li></ul>", "algorithmic": "</li></ol>"}.get(env, ""))
                elif name == "setcounter":  # the first line number of an algorithmic block
                    c, j = group(s, skip_ws(s, j))
                    n, j = group(s, skip_ws(s, j))
                    if c == "ALG@line":
                        res.append(f"<!--start={int(n) + 1}-->")
                elif name == "State":
                    res.append("</li><li>")
                elif name == "-":
                    pass
                elif name == "item":
                    k = skip_ws(s, j)
                    lab = ""
                    if k < len(s) and s[k] == "[":
                        lab, j = group(s, k, "[", "]")
                        lab = "<strong>" + self.text(lab) + "</strong> "
                    res.append("</li><li>" + lab)
                elif name in ("\\", "newline", "par"):
                    res.append("<br>")
                elif name in (" ", ",", ";", "quad", "qquad", "/", "noindent", "smallskip",
                              "medskip", "bigskip", "centering", "protect"):
                    res.append(" " if name in (" ", "quad", "qquad") else "")
                elif name in ("%", "&", "#", "_", "{", "}", "$"):
                    res.append(html.escape(name))
                elif name == '"':
                    v = s[j] if j < len(s) and s[j] != "{" else s[j + 1]
                    res.append({"o": "ö", "u": "ü", "a": "ä", "O": "Ö", "U": "Ü", "A": "Ä"}.get(v, v))
                    j += 1 if s[j] != "{" else 3
                elif name in ("'", "`", "^", "~", "v", "c"):
                    v = s[j] if j < len(s) and s[j] != "{" else s[j + 1]
                    res.append(v)
                    j += 1 if s[j] != "{" else 3
                elif "\\" + name in TEXT_MACROS:
                    res.append(TEXT_MACROS["\\" + name])
                elif name in ("ldots", "dots"):
                    res.append("…")
                else:
                    self.unknown.add(name)
                    res.append(html.escape("\\" + name))
                i = j
            elif c in "{}":
                i += 1
            elif c == "~":
                res.append("&nbsp;")
                i += 1
            elif s.startswith("---", i):
                res.append("—")
                i += 3
            elif s.startswith("--", i):
                res.append("–")
                i += 2
            elif s.startswith("``", i) or s.startswith("''", i):
                res.append("“" if c == "`" else "”")
                i += 2
            else:
                res.append(html.escape(c))
                i += 1
        out = "".join(res)
        out = re.sub(r'<ol class="alg">\s*<!--start=(\d+)-->', r'<ol class="alg" start="\1">', out)
        out = re.sub(r"<(ul|ol)([^>]*)>\s*</li>", r"<\1\2>", out)
        out = re.sub(r"(\s|<br>)+</li>", "</li>", out)
        return re.sub(r"\n\s*\n", "<br><br>", out)


def display(conv, e):
    """A displayed equation environment, for KaTeX (`align` becomes `aligned`, ...)."""
    env = e["env"].rstrip("*")
    inner = {"align": "aligned", "eqnarray": "aligned", "gather": "gathered",
             "multline": "gathered"}.get(env)
    body = conv.math(e["body"])
    return "\\[" + (f"\\begin{{{inner}}}{body}\\end{{{inner}}}" if inner else body) + "\\]"


def paper_data(paper_dir, build_dir, main="M1_Analyse"):
    paper_dir = Path(paper_dir)
    aux = compile_aux(paper_dir, build_dir, main)
    labels, cites, sections = read_aux(aux)
    conv = Converter(labels, cites)
    for sec in sections:
        sec["title"] = conv.text(sec["title"]).strip()
    out = {}
    main_tex = (paper_dir / (main + ".tex")).read_text(errors="replace")
    chapters = [paper_dir / (c + ("" if c.endswith(".tex") else ".tex")) for c in
                re.findall(r"^\\input\{(Include/[^}]+)\}", main_tex, re.M)]
    for f in chapters:
        envs = environments(f.read_text(errors="replace"))
        thms = [e for e in envs if e["env"] in THEOREMS and e["labels"]]
        for e in envs:
            if not e["labels"]:
                continue
            main_label = e["labels"][0]
            if e["env"] in THEOREMS:
                body = e["body"]
                for l in e["labels"]:
                    if l in labels:
                        out[l] = dict(labels[l], ref=ref_text(labels[l]), env=main_label,
                                      title=conv.text(e["title"]).strip(" ."), html="")
                out[main_label]["html"] = re.sub(r"^(\s|<br>)+|(\s|<br>)+$", "", conv.text(body))
            elif e["env"] == "algorithm":
                cap = re.search(r"\\caption\{", e["body"])
                title = group(e["body"], cap.end() - 1)[0] if cap else ""
                title = conv.text(title.split("\\newline")[0]).strip(" .")
                algo = next((l for l in e["labels"] if labels.get(l, {}).get("kind") == "algorithm"
                             and labels[l].get("plain", "") == labels[l]["num"]), None)
                for l in e["labels"]:
                    if l in labels and algo:  # the algorithm, and its lines
                        out[l] = dict(labels[l], ref=ref_text(labels[l]), env=algo,
                                      title=title if l == algo else "", html="")
            else:  # a displayed equation outside a statement
                inside = any(t["start"] < e["start"] < t["end"] for t in thms)
                for l in e["labels"]:
                    if l in labels and l not in out:
                        out[l] = dict(labels[l], ref=ref_text(labels[l]), env="" if not inside
                                      else "", title="", html="" if inside else
                                      display(conv, e))
    # equations inside statements: point to the statement
    for t_file in chapters:
        for e in environments(t_file.read_text(errors="replace")):
            if e["env"] in THEOREMS and e["labels"]:
                for l in e["labels"][1:]:
                    if l in out:
                        out[l]["env"] = e["labels"][0]
    for l, info in labels.items():  # sectioning labels (`subsubsec:...`)
        if info["kind"].endswith("section") and l not in out:
            out[l] = dict(info, ref=ref_text(info), env="", html="",
                          title=conv.text(info.get("title", "")).strip())
    conv.unknown.discard("")
    if conv.unknown:
        print("paper.py: text commands left as is: " + ", ".join(sorted(conv.unknown)),
              file=sys.stderr)
    order = [l for l in labels if l in out]  # the order of the document
    return dict(macros=katex_macros(main_tex), sections=sections, labels=out, order=order)
