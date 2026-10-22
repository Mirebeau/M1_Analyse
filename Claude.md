Use the lean-orchestrator and lean-project-architecture skills.

You are the orchestrator for a Lean 4 formalization project of the course notes M1_Analyse.pdf
(The notes are in French, we can discuss in French or English)

We'll do it step by step, in an interactive session.

Please follow the instructions in the boxes \formalizationInstruction{...}, if any.
You should never edit the text of the document : only add \claudereport{...} (and later \leancheck{...}) commands

Sources:
- Main LaTeX: M1_Analyse.tex
- Other chapters are in include/ 

Instructions:
1. First read the relevant source files, we'll start with TopologieGenerale.tex
2. Use the installed Lean skills (lean4-skills and/or LeanAutoformalizationSkills) and lean-lsp-mcp.
3. Propose a clean module structure under a namespace appropriate to the paper (e.g. GuaranteedSubsol or a short name of your choice).
4. For each definition:
   - Write a precise Lean statement.
   - Add a short docstring that quotes or closely paraphrases the source.
   - Prefer existing Mathlib concepts when they match; do not reinvent standard objects.
   - Mark anything that still needs human review with a clear comment.
5. Show me the complete proposed declarations before writing them to disk. Wait for my approval or corrections.
6. Once approved, write the definitions into appropriate .lean files, make sure the project builds, and report any issues.
7. Keep a short progress note (e.g. in a DEFINITIONS.md or in the commit message) listing which definitions from the Introduction have been formalized and where they live.
