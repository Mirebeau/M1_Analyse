#!/usr/bin/env python3
"""Build the Lean pages of the course: an HTML page showing, for each statement of the course
notes `M1_Analyse.tex`, its Lean formalization (docstring, statement and proof).

Run from anywhere (the project must have been built with `lake build`):

    python3 scripts/lean_pages/build.py [output.html] [--publish]

With `--publish`, the page is also copied to the public website repository (default: the clone
`../lean-proof-maps` of `github.com/Mirebeau/lean-proof-maps`, folder `M1Analyse/`), committed and
pushed; GitHub Pages serves it at `https://mirebeau.github.io/lean-proof-maps/M1Analyse/`.

Steps: read the declarations of `M1Analyse/**/*.lean` (a declaration formalizes the course labels
cited between backticks in its docstring, e.g. `def:topo`); ask Lean (`build/Mathlib.lean`, run
with `lake env lean`) for the Mathlib declarations that each one uses directly; read the course
statements (`paper.py`); fill `template.html`. Default output: `scripts/lean_pages/index.html`.
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

from paper import paper_data

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent  # the Lake project, which is also the directory of the course notes
SRC = ROOT / "M1Analyse"
BUILD = HERE / "build"
SITE = ROOT.parent / "lean-proof-maps"  # clone of the public website repository
SITE_DIR = "M1Analyse"
NAMESPACE = "M1Analyse"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?"
                  r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s(\[{:]+)")


def course_labels(paper):
    return set(paper["labels"])


def lean_files():
    """The modules in the order of the root file `M1Analyse.lean` (then any other)."""
    root = (ROOT / "M1Analyse.lean").read_text()
    mods = re.findall(r"^import (M1Analyse\.\S+)", root, re.M)
    files = [ROOT / (m.replace(".", "/") + ".lean") for m in mods]
    return files + sorted(set(SRC.glob("**/*.lean")) - set(files))


def read_decls(labels):
    """The documented declarations of the project, with the course labels their docstrings cite."""
    decls, modules = [], []
    for f in lean_files():
        text = f.read_text()
        lines = text.split("\n")
        rel = f.relative_to(ROOT).as_posix()
        mod = rel[:-5].replace("/", ".")
        m = re.search(r"/-!\s*\n# ([^\n]*)\n(.*?)-/", text, re.S)
        title = m.group(1).strip() if m else mod
        mdoc = m.group(2).strip() if m else ""
        modules.append(dict(module=mod, file=rel, title=title, doc=mdoc,
                            labels=[l for l in re.findall(r"`([A-Za-z]+:[A-Za-z0-9_]+)`", title)
                                    if l in labels]))
        ns = []
        i = 0
        while i < len(lines):
            line = lines[i]
            if (mm := re.match(r"namespace (\S+)", line)):
                ns.append(mm.group(1))
            elif re.match(r"end (\S+)", line) and ns and line.split()[1] == ns[-1]:
                ns.pop()
            if not line.startswith("/--"):
                i += 1
                continue
            j = i
            while not lines[j].rstrip().endswith("-/"):
                j += 1
            doc = "\n".join(lines[i:j + 1])
            doc = re.sub(r"^/--\s*|\s*-/$", "", doc.strip()).strip()
            k = j + 1  # the declaration ends at a blank line followed by a line at column 0
            while k < len(lines) and not (lines[k].strip() == "" and (
                    k + 1 >= len(lines) or (lines[k + 1][:1] not in (" ", "\t", "")))):
                k += 1
            code = "\n".join(lines[j + 1:k]).rstrip()
            dm = DECL.match(code)
            if dm:
                name = ".".join(ns + [dm.group(2)])
                # the labels formalized: those of the bold lead `**...**` of the docstring (the
                # others are mere cross-references). Without a bold lead: all the labels cited by a
                # definition (course notions), none for a theorem (helper lemma)
                lead = re.match(r"\*\*(.*?)\*\*", doc, re.S)
                cited = re.findall(r"`([A-Za-z]+:[A-Za-z0-9_]+)`", lead.group(1) if lead else
                                   "" if dm.group(1) in ("theorem", "lemma") else doc)
                decls.append(dict(
                    name=name, short=dm.group(2), kind=dm.group(1), module=mod, file=rel,
                    line=j + 2, doc=doc, code=code,
                    labels=list(dict.fromkeys(l for l in cited if l in labels))))
            i = k
    return decls, modules


def mathlib_uses(decls):
    """For each declaration, the Mathlib declarations used directly by its statement and proof,
    with their modules (for the links to the Mathlib documentation)."""
    BUILD.mkdir(exist_ok=True)
    out = BUILD / "mathlib.json"
    names = ",\n".join(f"  `{d['name']}" for d in decls)
    (BUILD / "Mathlib.lean").write_text(f'''import M1Analyse
open Lean Elab Command

def names : List Name := [
{names}
]

/-- Too basic to be worth a link. -/
def tooBasic : List Name := [`Set, `Set.ofPred, `Set.Elem]

/-- Shown: Mathlib declarations, except instances and auxiliary declarations. -/
def shown (env : Environment) (n : Name) : Option String := do
  let i ← env.getModuleIdxFor? n
  let mod := env.header.moduleNames[i.toNat]!
  guard ((`Mathlib).isPrefixOf mod && !n.isInternal && !Meta.isInstanceCore env n &&
    !tooBasic.contains n)
  return "[\\"" ++ n.toString ++ "\\", \\"" ++ mod.toString ++ "\\"]"

-- The Mathlib notions of the statement, and the Mathlib theorems used by the proof.
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for n in names do
    let some ci := env.find? n | logWarning m!"missing {{n}}"
    let notions := ci.type.getUsedConstants.filterMap (shown env)
    let lemmas := ci.getUsedConstantsAsSet.toArray.filter
      (fun m => (env.find? m).any (·.isThm)) |>.filterMap (shown env)
    out := out.push ("\\"" ++ n.toString ++ "\\": {{\\"notions\\": [" ++ ", ".intercalate
      notions.toList.eraseDups ++ "], \\"lemmas\\": [" ++ ", ".intercalate lemmas.toList.eraseDups ++ "]}}")
  IO.FS.writeFile "{out}" ("{{" ++ ",\\n".intercalate out.toList ++ "}}")
''')
    out.unlink(missing_ok=True)
    res = subprocess.run(["lake", "env", "lean", str(BUILD / "Mathlib.lean")], cwd=ROOT,
                         capture_output=True, text=True)
    if res.returncode != 0:
        sys.exit("lake env lean failed:\n" + res.stdout + res.stderr)
    if res.stdout.strip():
        print(res.stdout)
    data = json.loads(out.read_text())
    url = "https://leanprover-community.github.io/mathlib4_docs/{}.html#{}"
    for d in decls:
        for key in ("notions", "lemmas"):
            d[key] = sorted(({"name": n, "url": url.format(m.replace(".", "/"), n)}
                             for n, m in data.get(d["name"], {}).get(key, [])),
                            key=lambda x: x["name"])
    return decls


def publish(page, site):
    """Copy the page to `site/SITE_DIR/index.html`, commit and push (website repository)."""
    git = lambda *a: subprocess.run(["git", "-C", str(site), *a], check=True)
    git("pull", "--ff-only", "--quiet")
    (site / SITE_DIR).mkdir(exist_ok=True)
    (site / SITE_DIR / "index.html").write_text(page.read_text())
    git("add", f"{SITE_DIR}/index.html")
    if subprocess.run(["git", "-C", str(site), "diff", "--cached", "--quiet"]).returncode == 0:
        print("website: no change")
        return
    git("commit", "--quiet", "-m", f"Update the {SITE_DIR} Lean pages")
    git("push", "--quiet")
    print(f"website: pushed {SITE_DIR}/index.html")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("output", nargs="?", default=str(HERE / "index.html"))
    ap.add_argument("--publish", action="store_true", help="copy to the website and push")
    ap.add_argument("--site", default=str(SITE), help="clone of the website repository")
    args = ap.parse_args()
    out = Path(args.output)
    paper = paper_data(ROOT, BUILD / "paper")
    decls, modules = read_decls(course_labels(paper))
    decls = mathlib_uses(decls)
    data = json.dumps(dict(decls=decls, modules=modules, paper=paper),
                      ensure_ascii=False).replace("</", "<\\/")
    out.write_text((HERE / "template.html").read_text().replace("__DATA__", data))
    covered = {l for d in decls for l in d["labels"]}
    print(f"{out}: {len(decls)} Lean declarations, {len(covered)} course labels formalized")
    if args.publish:
        publish(out, Path(args.site))


if __name__ == "__main__":
    main()
