# Formalisation Lean de M1_Analyse — état d'avancement

Lean `v4.34.1`, Mathlib `v4.34.1`. Espace de noms `M1Analyse`. Un fichier Lean par
`\subsubsection` du cours. Les noms Lean suivent les labels LaTeX (`def:topo` → `def_topo_…`).
Les objets du cours sont ceux de Mathlib ; chaque énoncé établit la correspondance avec
la définition du cours ou la propriété annoncée. Tous les énoncés sont démontrés (pas de `sorry`).

## §1.1.1 Ouverts et fermés — `M1Analyse/TopologieGenerale/OuvertsFermes.lean`

| Label | Lean | Objet Mathlib |
|---|---|---|
| `def:topo` | `def_topo_axioms`, `def_topo_of_axioms` | `TopologicalSpace`, `IsOpen` |
| `def:topo` (topologie induite) | `def_topo_induite` | `instTopologicalSpaceSubtype` |
| `eq:finter_open` | `eq_finter_open` (sans l'hypothèse `I ≥ 1`) | `isOpen_iInter_of_finite` |
| `rem:unionVide` | `rem_unionVide` | `sUnion_empty`, `sInter_empty` |
| `rem:fermes` | `rem_fermes` | `IsClosed` |
| `def:interieur`, `eqdef:int_adh` | `def_interieur`, `def_adherence` | `interior`, `closure` |
| `eq:int_adh_compl` | `eq_int_adh_compl` | `interior_compl`, `closure_compl` |
| `eq:int_inter_adh_cup` | `eq_int_inter_adh_cup` | `interior_inter`, `closure_union` |
| `def:dense` | `def_dense`, `def_separable` | `Dense`, `SeparableSpace` |

Non formalisé : la définition d'une topologie par ses fermés (`TopologicalSpace.ofClosed`),
prévue avec `ex:T1nonT2`.

## Pages web et marques `\leancheck`

Chaque énoncé formalisé porte dans le cours une marque `\leancheck{<label>}` (« Lean✓ ») qui pointe
vers sa page : énoncé du cours, version Lean avec démonstration complète, notions et lemmes Mathlib
utilisés. Voir `scripts/lean_pages/README.md` pour régénérer `leananchors.tex` et la page.

## À venir

§1.1.2 `subsubsec:compTopo`, §1.1.3 `subsubsec:Vois`, §1.1.4 `subsubsec:separation`,
§1.1.5 `subsubsec:continuite`, §1.2–1.4.
