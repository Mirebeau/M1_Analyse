# Rapport d'élaboration — M1Analyse — 2026-11-02

Campagne de nettoyage en quatre étapes : élimination du code mort, test d'élaboration n°1,
passe d'amélioration de l'élaboration (A/B par intervention), test d'élaboration n°2.
Méthode : skills `lean-elaboration-test` et `lean-elaboration`.

## 1. Mise en place et provenance

| | Test 1 (avant) | Test 2 (après) |
|---|---|---|
| Fenêtre (UTC) | 2026-11-02 21:56:24 → 21:58:08 | 2026-11-02 22:13:03 → 22:14:44 |
| Commit | `0317830` (après élimination du code mort) | `aab5590` (après passe d'élaboration) |

- **Machine :** Apple M1 Pro, 10 cœurs, 32 Go, macOS (Darwin 24.6.0).
- **Chaîne d'outils :** Lean `v4.34.1`, Mathlib `v4.34.1` (8548 oleans présents, aucun recompilé).
- **Outil de mesure :** `/usr/bin/time -l` (BSD/macOS ; pas de `%CPU` direct, le parallélisme est calculé).
- **Cible :** `lake build M1Analyse`, cible par défaut. Le facade `M1Analyse.lean` importe les 53 fichiers suivis par git (directement, ou via `Brouwer` pour `Compacite.Lax`).
- **Invalidation :** uniquement les artefacts du projet, `.lake/build/lib/lean/M1Analyse{,.olean,.ilean,.trace,*.hash}` et `.lake/build/ir/M1Analyse*`. Jamais de `lake clean` ni de `lake update`.
- **Charge concurrente :** deux workers LSP inactifs (un dans un autre projet, un serveur MCP de ce projet). Aucune compilation amont n'a été observée (0 ligne `Mathlib.` dans les deux journaux).

## 2. Taille (`count_lean_lines.py`, depuis git)

| | Avant (`0317830`) | Après (`aab5590`) |
|---|---|---|
| Fichiers `.lean` | 53 | 53 |
| Lignes totales | 21 891 | 21 887 |
| Lignes de code (hors commentaires) | 16 682 | 16 680 |
| Fichiers uniquement commentaires | 0 | 0 |
| Fichiers non-module | 53 | 53 |

Le projet n'utilise pas le système de modules Lean, ce qui est cohérent avec sa configuration. Ce n'est pas un défaut au sens de ce projet.

## 3. Tableau de synthèse

| Mesure | Test 1 | Test 2 | Δ |
|---|---|---|---|
| Temps réel | 103,84 s | 100,62 s | −3,2 s (−3,1 %) |
| CPU utilisateur | 395,42 s | 383,46 s | −12,0 s (−3,0 %) |
| CPU système | 168,79 s | 165,43 s | −3,4 s |
| CPU journalisée (Σ « Built ») | 396,0 s | 386,6 s | −9,4 s (−2,4 %) |
| Parallélisme implicite (journalisée / réel) | 3,81 | 3,84 | comparable |
| Coût par ligne | 23,7 ms | 23,2 ms | −0,5 ms |
| RSS max | 3,28 Go | 3,27 Go | ≈ |
| Jobs | 3357 (53 du projet) | 3357 (53 du projet) | = |

Le parallélisme est apparié (3,81 contre 3,84), avec le même outil et la même machine. La comparaison des temps réels est donc légitime, mais l'écart reste de l'ordre du bruit d'un seul run.

## 4. Santé du build

- **Statut :** sortie 0 pour les deux tests, 0 erreur, 0 avertissement.
- **`sorry` :** 0.
- **Axiomes du projet :** `th_unifCvxReflex` (Milman–Pettis) et `th_YoungFaible_lintegral` (Young faible), conformes aux décisions de l'auteur.
- **Règles respectées :** aucun `set_option maxHeartbeats` et aucune commande `#…` dans les sources.

## 5. Queue lourde

| Palier (durée de build par fichier) | Avant | Après |
|---|---|---|
| ≥ 5 s | 44 | 44 |
| ≥ 10 s | 12 | 8 |
| ≥ 20 s | 0 | 0 |

**Attention :** Lake arrondit à la seconde les durées de 10 s et plus. Un écart de ±1 s sur ces fichiers n'est donc pas significatif.

Les 16 fichiers les plus lourds (durée de build) :

| Fichier | Avant | Après | Δ |
|---|---|---|---|
| Sobolev.W1p | 14 | 14 | 0 |
| Sobolev.NoyauGreen | 14 | 13 | −1 (bruit, non modifié) |
| Sobolev.InjSurCritique | 11 | 10 | −1 (bruit, non modifié) |
| **Sobolev.InjSousCritiqueW1p** | 11 | **8,6** | **−2,4** (modifié) |
| Hilbert.Hilbert | 11 | 11 | 0 |
| Dualite.Reflexivite | 11 | 11 | 0 |
| **Sobolev.Rellich** | 10 | **9,2** | **−0,8** (modifié) |
| Sobolev.MinNonLinH1 | 10 | 10 | 0 |
| Sobolev.ConvolDistrib | 10 | 10 | 0 |
| LegendreFenchel | 10 | 10 | 0 |
| Dualite.DualiteLebesgue | 10 | 9,0 | −1 (bruit) |
| Compacite.Lax | 10 | 9,6 | −0,4 |
| TopologieGenerale.EspacesFonctionnels | 9,6 | 9,5 | −0,1 |
| Compacite.OperateursCompacts | 9,4 | 9,8 | +0,4 |
| Compacite.Brouwer | 9,3 | 9,5 | +0,2 |
| TopologieGenerale.TopologieFaible | 9,1 | 8,1 | −1,0 (bruit) |

Le plancher d'import est d'environ 4,2 s par fichier : c'est la durée de build du facade `M1Analyse`, qui ne fait qu'importer.

## 6. CPU par répertoire (s, CPU journalisée)

| Répertoire | Avant | Après | Δ |
|---|---|---|---|
| Sobolev | 151,9 | 148,5 | −3,4 |
| Compacite | 66,0 | 65,2 | −0,8 |
| TopologieGenerale | 60,3 | 57,9 | −2,4 |
| Completude | 40,8 | 39,7 | −1,1 |
| Dualite | 40,0 | 38,1 | −1,9 |
| Hilbert | 11,0 | 11,0 | 0 |
| LegendreFenchel | 10,0 | 10,0 | 0 |
| Outils | 6,0 | 6,3 | +0,3 |
| Bosse | 5,7 | 5,7 | 0 |
| facade `M1Analyse` | 4,3 | 4,2 | −0,1 |

Seul `Sobolev` a été modifié. Les variations hors `Sobolev` (−0,8 à −2,4 s) sont du bruit de run et d'arrondi : elles mesurent l'amplitude du bruit.

## 7. Profils individuels (en série, à chaud : `lake env lean --profile`)

Temps réel du processus ; phases cumulées. Les preuves s'élaborent en parallèle, donc les phases peuvent dépasser le temps réel.

| Fichier | Réel avant | Réel après | import | inférence de classes (avant → après) | interprétation (avant → après) | exécution de tactiques (avant → après) | Phase dominante |
|---|---|---|---|---|---|---|---|
| Sobolev.W1p | 13,89 | 14,00 | 3,45 | 12,1 → 12,3 | 1,44 → 1,46 | 10,1 → 10,2 | classes (diffus) |
| Sobolev.Rellich | 12,67 | **11,10** | 3,39 | 11,6 → 11,0 | **4,40 → 3,30** | **15,1 → 11,2** | classes / tactiques |
| Sobolev.MinNonLinH1 | 12,23 | 12,21 | 3,40 | 4,77 → 4,66 | 2,92 → 2,91 | 8,62 → 8,54 | tactiques |
| Sobolev.ConvolDistrib | 11,37 | 11,41 | 3,40 | 10,7 → 10,7 | 1,31 → 1,30 | 6,03 → 5,99 | classes (diffus) |
| Sobolev.InjSousCritiqueW1p | 11,20 | **8,24** | 3,45 | 1,98 → 1,94 | **4,71 → 0,90** | **2,80 → 1,37** | import (après) |
| Sobolev.InjSurCritique | 10,60 | 10,58 | 3,38 | 6,71 → 6,71 | 2,95 → 2,95 | 6,25 → 6,27 | tactiques / classes |
| Dualite.DualiteLebesgue | 10,25 | 10,29 | 3,20 | 6,60 → 6,53 | 2,98 → 2,96 | 3,41 → 3,37 | classes |
| Sobolev.NoyauGreen | 9,91 | 9,90 | 3,08 | 4,21 → 4,23 | 2,24 → 2,23 | 2,01 → 2,02 | classes |
| Dualite.Reflexivite | 8,03 | 8,00 | 2,84 | 3,39 → 3,39 | 1,45 → 1,43 | 1,58 → 1,58 | import |
| LegendreFenchel | 7,79 | 7,81 | 2,57 | 4,14 → 4,10 | 3,48 → 3,46 | 2,03 → 2,05 | classes / interprétation |
| Compacite.Lax | 7,79 | 7,82 | 3,26 | 2,63 → 2,58 | 0,78 → 0,79 | 1,39 → 1,35 | import |
| Hilbert.Hilbert | 7,76 | 7,77 | 3,21 | 2,06 → 2,06 | 0,80 → 0,79 | 0,43 → 0,42 | import |

- **Fichiers non modifiés :** stables à ±0,05 s près. Ce sont les témoins, et le bruit des profils est faible.
- **Inférence de classes :** 1 à 3 événements de plus de 100 ms par fichier (`InnerProductSpace` 0,33 s, `ContinuousConstSMul` 0,29 s, `Norm` 0,15 s, `NormedSpace` 0,47 s), pour 11 à 12 s cumulées. Elle est donc diffuse. D'après le skill, c'est un plancher structurel : pas de cache de classe de tête possible.

## 8. Constats et interventions, par ordre d'actionnabilité

### Élimination du code mort (étape 1)

- **Méthode :** graphe des usages calculé dans l'environnement Lean (types et corps de toutes les constantes du projet, y compris les privées et les auxiliaires), croisé avec une recherche textuelle. Le croisement est nécessaire parce que les lemmes `rfl` utilisés par `simp` ne laissent aucune trace dans les termes de preuve.
- **Supprimé (commit `0317830`) :**
  - `nonReflexMkC0_apply` (`Dualite/DualiteLebesgue.lean`) ;
  - `rellich_fst_le` (`Sobolev/Rellich.lean`).
  Ce sont deux lemmes privés jamais utilisés.
- **Faux positif écarté :** `nonReflexDelta_apply`, un lemme `rfl` utilisé par `simp`.
- **Gardé :** 302 déclarations publiques à en-tête de label jamais référencées. Ce sont les énoncés du cours (des feuilles), donc pas du code mort.
- **Gardé, à arbitrer par l'auteur :** 16 déclarations publiques sans en-tête de label et non référencées. Ce sont des ponts vers Mathlib ou des lemmes d'API documentés :
  - `fixedPoint_of_retract`, `normeHolder_eq_normeModule` ;
  - `ConvexeFerme.coe_conePolaire`, `conePolaire_eq_neg_innerDual` ;
  - `biconjuguee_apply`, `prop_Jensen_reel` ;
  - `restrGrad_fst`, `restrGrad_snd` ;
  - `continuous_of_mem_espaceHolder`, `toReal_normeSup` ;
  - `estSuiteExhaustive_compactExhaustion`, `distCvSimple_max` ;
  - `estModuleCont_iff`, `rem_distInfinie_axioms` ;
  - les `…_def` de `Sobolev1`/`H10`.

### Passe d'élaboration (étape 3, commit `aab5590`)

Chaque intervention a été testée seule en A/B, sur une copie hors projet, avec le profil `--profile` en série (B, A, B). Règle d'acceptation : la phase visée baisse de 2 s ou de 10 % au moins, sans transfert de coût ailleurs.

1. **`injSousCrit_test` (`InjSousCritiqueW1p`) : `calc` remplacé par `h1.trans (hle.trans (le_of_le_of_eq … (by gcongr) ?_))`.**
   - Diagnostic : le `calc` coûtait 5,3 s. Le terme initial `eLpNorm f pstar` y était élaboré avec une mesure en métavariable, et le raccord au but déclenchait des dizaines d'échecs `isDefEq` (environ 0,2 s chacun) et une recherche de coercion.
   - Variante testée et rejetée : annoter `volume` en tête de `calc`. Elle provoque un dépassement de heartbeats (`whnf`).
   - Mesure : interprétation 4,72 → 0,90 s ; temps réel du fichier 10,95 → 8,6 s. **Gardé.**
2. **`corol_injSousCritOm` : `rw [enorm_eq_nnnorm u, ← ENNReal.coe_mul, ENNReal.coe_le_coe]; exact P.le_opNNNorm u` remplacé par `exact P.le_opENorm u`.**
   - Mesure : exécution de tactiques 2,71 → 1,37 s (−50 %). **Gardé.**
3. **`rellich_surCrit_rep` (cas `d = 0`) : `rw [one_mul, Subsingleton.elim (0 : EuclideanSpace ℝ (Fin 0)) x]` remplacé par un `congrArg` nommé (levier 9), puis `rw [one_mul, h0]`.**
   - Diagnostic : le `rw` coûtait 4,7 s (calcul du motif).
   - Mesure : exécution de tactiques 15,1 → 11,6 s cumulés. Le temps réel ne bouge pas, car d'autres preuves parallèles dominent. **Gardé** (gain de CPU).
4. **`W1p_inclusion_of_le` : deux `nlinarith` remplacés par `ring` et des lemmes de monotonie (`le_add_of_nonneg_left/right`) (levier 2).**
   - Mesure : interprétation 4,37 → 3,33 s ; temps réel du fichier 12,27 → 10,82 s. **Gardé.**

**Rejeté :** dans `corol_testDenseWspO` (`W1p`), remplacer `rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hPu'` par une annotation définitionnelle ne fait gagner que −0,9 s d'exécution de tactiques (−9 %). C'est sous le seuil, donc non appliqué.

**Non tenté, faute de levier :**
- l'inférence de classes diffuse de `W1p`, `Rellich` et `ConvolDistrib` (plancher structurel) ;
- les commandes `local notation` à 1,6–1,9 s (`NoyauGreen`, `DualiteLebesgue`), dont le coût est la reconstruction de la table du parseur (`term_parser`) et n'est pas corrigeable localement ;
- le `nlinarith` de 1,2 s de `ex_nonLinMinH1_hypMinFctCvxRefl`, qui demanderait de restructurer l'argument : coût d'auteur supérieur au gain.

## 9. Ce qui n'est pas établi

- **Gain global :** −3,2 s de temps réel et −9,4 s de CPU journalisée, mesurés sur un seul run de chaque côté. Le bruit observé sur les fichiers non modifiés est de ±1 s par fichier (arrondi de Lake). Le gain global est donc de l'ordre du bruit. En revanche, les gains par fichier (§7 et A/B) sont robustes : 3 runs, témoins stables à ±0,05 s.
- **Borne du temps réel :** elle est probablement fixée par la chaîne critique `W1p → … → Rellich → RellichCorollaire → MinNonLinH1`, plutôt que par le travail total (396 s / 10 cœurs ≈ 40 s, contre 100 s mesurées). Le chemin critique pondéré n'a pas été calculé.
- **Import :** il représente environ 3,3 s par fichier, soit environ 44 % de la CPU totale. Il n'a pas été traité : réduire les imports Mathlib fichier par fichier comporte environ 50 % de faux positifs d'après le skill, et exige une vérification symbole par symbole.
- **Fichiers hors du top 12 :** non profilés.

## 10. Méthodologie (commandes exactes)

```bash
python3 ~/.claude/skills/lean-elaboration-test/scripts/count_lean_lines.py HEAD
rm -rf .lake/build/lib/lean/M1Analyse .lake/build/ir/M1Analyse
rm -f .lake/build/lib/lean/M1Analyse.{olean,ilean,trace,olean.hash,ilean.hash} \
      .lake/build/ir/M1Analyse.{c,c.hash,setup.json}
/usr/bin/time -l lake build M1Analyse > elabN.log 2>&1
grep -oE "Built M1Analyse[^ ]* \(([0-9.]+)(m?s)\)" elabN.log      # par fichier (LC_ALL=C)
lake env lean --profile M1Analyse/<Chemin>/Fichier.lean           # en série, top 12
lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=700 <fichier>   # attribution par déclaration
```

Code mort : script Lean (hors projet) qui parcourt `env.constants`, calcule les constantes utilisées par le type et la valeur (`value? (allowOpaque := true)`) de chaque constante du projet, rattache les auxiliaires à leur déclaration propriétaire, puis croise le résultat avec `grep`.

## 11. Pointeurs

Aucun rapport antérieur : ce rapport sert de première référence (baseline) pour les mesures futures.
