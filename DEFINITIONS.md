# Formalisation Lean de M1_Analyse — état d'avancement

Lean `v4.34.1`, Mathlib `v4.34.1`. Espace de noms `M1Analyse`. Un fichier Lean par sous-section
(ou sous-sous-section) du cours. Les noms Lean suivent les labels LaTeX (`def:topo` → `def_topo_…`).
Les objets du cours sont ceux de Mathlib ; chaque énoncé établit la correspondance avec la
définition du cours ou démontre le résultat annoncé. **Tous les énoncés sont démontrés** (aucun
`sorry`, aucun axiome ajouté) ; le projet compile sans avertissement.

- §1.1.1 (`OuvertsFermes.lean`) a été relu et approuvé par l'auteur.
- **Tout le reste est un brouillon à relire** (branche `formalisation-nuit`, nuit du 23 au 24 octobre
  2026) : énoncés écrits par des agents IA à partir du texte, puis relus par l'orchestrateur.
  Voir « Points à relire » ci-dessous.

Chaque énoncé formalisé porte dans le cours une marque `\leancheck{<label>}` (« Lean✓ ») qui
pointe vers sa page web (énoncé du cours, version Lean, démonstration repliée, notions et lemmes
Mathlib utilisés). Voir `scripts/lean_pages/README.md`.

## Couverture


**Bilan : 217 énoncés du cours formalisés (465 déclarations Lean), dans 37 fichiers.**


### §1.1.1 Ouverts et fermés — `M1Analyse/TopologieGenerale/OuvertsFermes.lean`

8 énoncés du cours, 12 déclarations Lean : `def:topo`, `eq:finter_open`, `rem:unionVide`, `rem:fermes`, `def:interieur`, `eq:int_adh_compl`, `eq:int_inter_adh_cup`, `def:dense`

### §1.1.2 Comparaison de topologies — `M1Analyse/TopologieGenerale/ComparaisonTopologies.lean`

6 énoncés du cours, 12 déclarations Lean : `def:finesseTopo`, `def:topoEngendree`, `prop:baseOuverts`, `corol:baseOuverts`, `ex:topoOrdre`, `ex:topoProduit`

### §1.1.3 Voisinages — `M1Analyse/TopologieGenerale/Voisinages.lean`

11 énoncés du cours, 15 déclarations Lean : `def:filtre_vois`, `eqdef:Vx`, `prop:adh_vois`, `def:base_vois`, `rem:topoVois`, `def:denVois`, `def:cvSuite`, `prop:adhSuite`, `eqdef:adherence_suite`, `prop:adhSousSuite`, `rem:axiomFiltre`

### §1.1.4 Séparation — `M1Analyse/TopologieGenerale/Separation.lean`

4 énoncés du cours, 11 déclarations Lean : `def:separe`, `rem:uniqueLim`, `rem:T1`, `ex:T1nonT2`

### §1.1.5 Continuité — `M1Analyse/TopologieGenerale/Continuite.lean`

6 énoncés du cours, 18 déclarations Lean : `def:continuite`, `eq:cont_at_x_direct`, `prop:caract_cont`, `rem:topoFunc`, `def:semiContinuite`, `prop:surGrapheSCI`

### §1.2 Espaces métriques — `M1Analyse/TopologieGenerale/Metrique.lean`

11 énoncés du cours, 37 déclarations Lean : `def:distance`, `def:boule`, `rem:distInfinie`, `prop:baseVoisMetric`, `def:moduleCont`, `rem:dist_of_mod_cont`, `lem:contDistance`, `def:unifContinu`, `prop:distCvSimple`, `def:dist_unif`, `rem:equicont`

### §1.3 Espaces vectoriels normés — `M1Analyse/TopologieGenerale/EVN.lean`

5 énoncés du cours, 25 déclarations Lean : `def:norme`, `def:normeOperateur`, `def:normeHolder`, `def:normeCnb`, `def:normeLp`

### §1.4 Espaces vectoriels topologiques localement convexes — `M1Analyse/TopologieGenerale/EVTLC.lean`

13 énoncés du cours, 25 déclarations Lean : `def:evtlc`, `eq:evtlc_vois`, `lem:evtlc_separe`, `lem:evtlcLinCont`, `eq:cont_lin_evtlc`, `eq:cont_lin_evtlc_evn`, `rem:sommeMaxEvtlc`, `rem:evtlcGradue`, `eqdef:boule_graduee`, `eqdef:evtlc_dist`, `eq:boule_evtlc`, `prop:distanceEvtlcs`, `def:lineairBorne`

### §1.4 Exemples d'espaces fonctionnels — `M1Analyse/TopologieGenerale/EspacesFonctionnels.lean`

8 énoncés du cours, 21 déclarations Lean : `eqdef:exhaustive_compacts`, `prop:exhaustComp`, `def:lploc`, `def:classeSchwartz`, `def:cont_nonbornee`, `def:cinf_bornee`, `def:distribution`, `lem:omegaNmuN`

### §1.4 La topologie faible — `M1Analyse/TopologieGenerale/TopologieFaible.lean`

4 énoncés du cours, 10 déclarations Lean : `def:topoFaible`, `prop:bouleMetrisable`, `eqdef:met_faible_boule`, `eq:vois_faible_boule_evtlc`

### §2.1 Critère de Cauchy — `M1Analyse/Completude/Cauchy.lean`

6 énoncés du cours, 11 déclarations Lean : `def:suiteCauchy`, `eqdef:suiteCauchyMin`, `def:complet`, `lem:serie_Banach`, `prop:fermeComplet`, `prop:LEFcomplet`

### §2.2 Espaces fonctionnels complets — `M1Analyse/Completude/FonctionnelsComplets.lean`

3 énoncés du cours, 9 déclarations Lean : `ex:cont_bornee_Banach`, `ex:Holder_Banach`, `ex:LpBanach`

### §2.3 Prolongements — `M1Analyse/Completude/Prolongements.lean`

3 énoncés du cours, 5 déclarations Lean : `prop:prolongement_complet`, `prop:espaceComplete`, `ex:extUnifCont`

### §2.4 Point fixe de Picard — `M1Analyse/Completude/Picard.lean`

5 énoncés du cours, 5 déclarations Lean : `th:fixe_Picard`, `lem:Gronwall`, `th:Cauchy_Lipschitz`, `ex:EDretard`, `ex:eqFunctIntegr`

### §2.5 Théorème de Baire — `M1Analyse/Completude/Baire.lean`

6 énoncés du cours, 10 déclarations Lean : `lem:fermeEmboite`, `th:BaireOuvert`, `corol:BaireFerme`, `rem:terminologieBaire`, `ex:GrasQ`, `ex:grasNonDen`

### §2.6 Applications de Baire aux opérateurs linéaires continus — `M1Analyse/Completude/BaireLineaire.lean`

7 énoncés du cours, 8 déclarations Lean : `th:BanachSteinhaus`, `corol:limSimpleLin`, `corol:BanachSteinhausK`, `th:appliOuverte`, `corol:isomBanach`, `corol:equivNormes`, `th:grapheFerme`

### §3.1 Axiome de Borel-Lebesgue — `M1Analyse/Compacite/BorelLebesgue.lean`

8 énoncés du cours, 13 déclarations Lean : `def:compact`, `rem:fermeBorelLeb`, `lem:compImplFerme`, `corol:compSsiFerme`, `prop:compactImage`, `corol:homeoCompact`, `def:locCompact`, `def:compactAlex`

### §3.2 Compacts métriques — `M1Analyse/Compacite/CompactsMetriques.lean`

5 énoncés du cours, 9 déclarations Lean : `def:precompact`, `rem:precompact_separable`, `th:BolzanoWeierstrass`, `th:Heine`, `prop:noAdhCv`

### §3.3 Compacité en dimension finie — `M1Analyse/Compacite/DimensionFinie.lean`

5 énoncés du cours, 6 déclarations Lean : `prop:compSsiFermeBorne`, `corol:bornesAtteintes`, `corol:normesEquivRd`, `lem:normaleRiesz`, `th:bouleCompRiesz`

### §3.4 Produits de compacts — `M1Analyse/Compacite/Produits.lean`

7 énoncés du cours, 10 déclarations Lean : `th:compProdTycho`, `ex:formuleLogique`, `th:BanachAlaoglu`, `th:AscoliLip`, `corol:AscoliEquicont`, `prop:hullCompact`, `th:Caratheodory`

### §3.5 Point fixe de Brouwer — `M1Analyse/Compacite/Brouwer.lean`

1 énoncés du cours, 3 déclarations Lean : `th:chgVarIntegr`

### §3.6 Point fixe de Schauder — `M1Analyse/Compacite/Schauder.lean`

0 énoncés du cours, 3 déclarations Lean : 

### §3.7 Théorème de Stone-Weierstrass — `M1Analyse/Compacite/StoneWeierstrass.lean`

7 énoncés du cours, 9 déclarations Lean : `th:StoneWeierstrass`, `lem:StoneUnite`, `lem:StoneSqrt`, `corol:StoneMinMax`, `lem:StoneDirac`, `corol:StoneComplexe`, `rem:polDens`

### §3.8 Opérateurs linéaires compacts — `M1Analyse/Compacite/OperateursCompacts.lean`

7 énoncés du cours, 14 déclarations Lean : `def:linCompact`, `prop:opCompactComposition`, `prop:opCompactLimite`, `def:linSpectre`, `th:Fredholm`, `corol:FredholmPrecise`, `prop:opCompactComplCont`

### §3.1 Théorème de Hahn-Banach — `M1Analyse/Dualite/HahnBanach.lean`

9 énoncés du cours, 11 déclarations Lean : `def:inductif`, `lem:Zorn`, `def:axiomChoix`, `def:sousLin`, `th:HahnBanach`, `corol:prol_forme_evn`, `corol:dens_banach`, `ex:dualSeparable`, `corol:projDimFinie`

### §3.2 Réflexivité — `M1Analyse/Dualite/Reflexivite.lean`

7 énoncés du cours, 10 déclarations Lean : `def:reflexif`, `prop:conjugueDual`, `corol:faibleSepare`, `corol:faibleFortBorne`, `corol:bidualComplete`, `rem:unifCvxHilbert`, `th:HolderIneq`

### §3.3 Formes géométriques de Hahn-Banach — `M1Analyse/Dualite/HahnBanachGeometrique.lean`

5 énoncés du cours, 12 déclarations Lean : `prop:jaugeCvx`, `lem:jaugeOuvertCvx`, `th:separOuvertPt`, `corol:separOuvertPt`, `th:separFermeComp`

### §3.3 (suite) Polarité, compacité faible et optimisation — `M1Analyse/Dualite/CompaciteFaible.lean`

4 énoncés du cours, 9 déclarations Lean : `def:convexePolaire`, `prop:cvxFaibleFerme`, `corol:cvxFermeBdComp`, `corol:minFctCvxRefl`

### §5.1 Convolution dans les espaces `L^p` — `M1Analyse/Sobolev/ConvolutionLp.lean`

8 énoncés du cours, 20 déclarations Lean : `prop:densC0Lp`, `prop:Jensen`, `corol:lpInclusLq`, `prop:convolLp`, `lem:convolTranslat`, `prop:convolDeriv`, `corol:testDenseLp`, `prop:convolApprox`

### §5.2 Convolution de distributions et espaces de Sobolev — `M1Analyse/Sobolev/ConvolutionSobolev.lean`

1 énoncés du cours, 3 déclarations Lean : `prop:distribL1Loc`

### §5.1 Théorème de Fréchet-Kolmogorov — `M1Analyse/Sobolev/FrechetKolmogorov.lean`

1 énoncés du cours, 8 déclarations Lean : `th:FrechetKolmogorov`

### §5.3 Injections de Sobolev - cas sous-critique — `M1Analyse/Sobolev/InjSousCritique.lean`

5 énoncés du cours, 12 déclarations Lean : `subsec:injSousCrit`, `eq:powLpw`, `eq:homog_lp`, `rem:homogSobolev`, `th:Young`

### §5.3 Injections de Sobolev, cas sous-critique : noyau de Green — `M1Analyse/Sobolev/NoyauGreen.lean`

2 énoncés du cours, 9 déclarations Lean : `prop:convolPow`, `corol:noyauGreen`

### §5.5 Injection compacte de Sobolev - théorème de Rellich — `M1Analyse/Sobolev/Rellich.lean`

1 énoncés du cours, 1 déclarations Lean : `prop:interpLp`

### §A Fonctions bosse `C^∞` — `M1Analyse/Bosse/Bosse.lean`

6 énoncés du cours, 7 déclarations Lean : `lem:cinfExpInv`, `prop:cinfHeaviside`, `prop:cinfBosse`, `prop:cinfSupport`, `prop:cinfPartition`, `prop:cinfExhaust`

### §B Espaces Hilbertiens — `M1Analyse/Hilbert/Hilbert.lean`

12 énoncés du cours, 26 déclarations Lean : `def:prehilbert`, `prop:CauchySchwarz`, `def:Hilbert`, `th:projConvexe`, `eq:proj_obtus`, `eq:proj_moyennee`, `th:reprRiesz`, `ex:l2Hilbert`, `prop:decompOrth`, `prop:decompCone`, `ex:coneSdp`, `th:baseHilbert`

### §C Dualité de Legendre-Fenchel — `M1Analyse/LegendreFenchel/LegendreFenchel.lean`

10 énoncés du cours, 36 déclarations Lean : `def:legendre_fenchel`, `def:domaineFct`, `lem:FenchelPropre`, `lem:minorantCvxSci`, `th:LegendreFenchel`, `lem:cvxImplLip`, `lem:cvxImplBorne`, `th:ssGrad`, `lem:cvxSciAlt`, `th:FenchelRockafellar`

## Points à relire (choix d'interprétation, définitions ajoutées, écarts au texte)

### EVN (§1.3)
- Nouvelles définitions (Mathlib n'a pas ces normes) : seminormeHolder, constLip, normeHolder, espaceHolder, normeCnb, espaceCnb, espaceCnbAdherence, deriveePartielle.
- Les sup sont des `Real.iSup` (valent 0 si non borné) : n'ont de sens que sur l'espace ; à relire.
- C^n_b(Ω) : fonctions définies sur ℝ^d dont seules les valeurs sur Ω comptent (sous-module de (ℝ^d → 𝕜), pas un quotient) ; séparation énoncée « f non nulle sur Ω ⇒ ‖f‖ > 0 ».
- Hölder énoncé pour tout α ≥ 0 (le cours : α ∈ ]0,1[).
- Norme C^n_b : somme sur les multi-indices comme dans le cours (Mathlib utiliserait ‖iteratedFDeriv‖, équivalente).
### Comparaison de topologies (§1.1.2)
- Ordre de Mathlib inversé : « t₁ plus fine que t₂ » ⇔ t₁ ≤ t₂ ; fine = ⊥, grossière = ⊤ ; intersection de topologies = sSup.
- prop:baseOuverts scindée en deux : lien avec IsTopologicalBasis (prop_baseOuverts_iff) et l'énoncé (prop_baseOuverts).
- Description explicite de la topologie engendrée : j parcourt Fin (J i), J i > 0, I : Type u.
- ex:topoOrdre : la topologie de l'ordre de Mathlib (engendrée par ]a,∞[, ]−∞,b[) admet les trois familles d'intervalles comme base — accord avec la définition du cours.
### Voisinages (§1.1.3)
- rem:topoVois scindée (premier / second point) ; l'hypothèse « chaque W ∈ 𝒲_x contient x » est inutile pour le premier point.
- prop:adhSuite, prop:adhSousSuite : en plus, le sens sans dénombrabilité (_supset).
- Adh((x_n)) écrit ⋂ N, closure (x '' Ici N), égal à {a | MapClusterPt a atTop x}.
### Séparation, Continuité (§1.1.4–1.1.5)
- Zariski : construit directement sur ℂ^d (type `Zariski d`) à partir de ses fermés (Mathlib ne l'a que sur PrimeSpectrum) ; non séparé seulement pour d ≥ 1.
- s.c.i./s.c.s. : à valeurs dans EReal ; définition du cours (sous-niveaux fermés) prouvée équivalente à celle de Mathlib.
- Somme de fonctions s.c.i. : à valeurs dans ]−∞,∞] codé par EReal + f x ≠ ⊥ ; l'identité eq:somme_sci elle-même n'est pas formalisée.
- prop:surGrapheSCI : l'hypothèse f > −∞ est inutile (gardée, non utilisée).
- rem:topoFunc : la convergence des suites formalisée sous la forme corrigée (x_n → a ⇔ f_i(x_n) → f_i(a) ∀ i).
### EVTLC (§1.4, partie générale)
- Cadre : famille de semi-normes `p : SeminormFamily 𝕜 E ι` avec `WithSeminorms p` ; max sur I₀ fini = `(I₀.sup p) x` (0 si I₀ vide).
- Définition propre au cours : `evtlcDist p x y := ⨆ n, min (2⁻ⁿ) (p n (x−y))` ; prouvé que le sup est atteint (max).
- Hypothèse de séparation retirée là où elle est inutile (signalé dans les docstrings) ; gardée pour prop:distanceEvtlcs.
- eq:boule_evtlc énoncé avec ≤ (correction du cours, voir les \claudereport).
- Non formalisé : la variante « somme » de la distance (rem:sommeMaxEvtlc).
### Complétude §2.1–2.3
- Module de continuité : chaque fichier le traite comme une fonction avec hypothèses explicites (ω : ℝ≥0 → ℝ≥0∞ ou ℝ≥0, « ω(s) → 0 » = Tendsto ω (𝓝 0) (𝓝 0), donc ω(0) = 0) ; à unifier avec la définition de Metrique.lean (def:moduleCont).
- ex:Holder_Banach : nouvel espace C^ω_b (sous-module de X →ᵇ E) ; « Banach » énoncé par la norme + critère de Cauchy, sans nouvelle instance ; non relié à seminormeHolder de EVN.lean.
- def:complet (Fréchet) : via evtlcDist ; hypothèse de séparation inutile.
- Non formalisés (absents de Mathlib) : C^k_b Banach, C^k(Ω) Fréchet, C^∞_b et 𝒟_K Fréchet, Schwartz Fréchet (pas d'instance CompleteSpace pour SchwartzMap), L^p_loc.
### Espaces métriques (§1.2)
- DÉCISION : module de continuité `EstModuleCont ω := Tendsto ω (𝓝 0) (𝓝 0)` avec ω : ℝ≥0 → ℝ≥0∞ ; la limite inclut s = 0 (convention française), ce qui impose ω(0) = 0 (prouvé équivalent à ω(0) = 0 ∧ limite en 0⁺). Alternative : limite épointée.
- Nouvelles distances (rem:distInfinie, rem:dist_of_mod_cont, prop:distCvSimple, def:dist_unif) énoncées comme « EstDistance d ∧ les boules de d forment une base de voisinages de la topologie existante ».
- def:dist_unif seulement pour Y^I (Mathlib n'a pas la convergence uniforme sur un produit dépendant).
- Contractante : ∃ K < 1, LipschitzWith K f (ContractingWith de Mathlib ne couvre que X → X).
- Helpers : EstDistance, metricSpaceOfIsDistance.
- Non formalisé : lem:regModuleCont (construction longue, absente de Mathlib).
### Espaces fonctionnels, topologie faible (fin du §1.4)
- Les deux sous-sous-sections n'ont pas de label : modules rattachés à `subsec:evtlc` (suggestion : ajouter des \label).
- Dérivées partielles indexées par des mots (j, w : Fin j → Fin d) plutôt que des multi-indices (équivalent par Schwarz, non prouvé).
- Classe de Schwartz, L^p_loc, C^k(Ω) : seule l'appartenance est formalisée, pas la topologie (Mathlib n'a pas L^p_loc ni C^k(Ω) comme espaces topologiques).
- Distributions : via `TestFunction` de Mathlib (topologie LF) ; « continue ⇔ estimation locale ».
- lem:omegaNmuN énoncé dans [0,∞] (+ corollaire réel).
- prop:bouleMetrisable : distance du cours (⨆ ; atteinte non prouvée) ; hypothèse « E séparable » redondante, gardée.
- Non formalisés : C^∞_b(Ω), prop:distribCont (facultatif), ordre d'une distribution.
### Complétude §2.4–2.6
- th:fixe_Picard : hypothèse [Nonempty X] ajoutée.
- Cauchy–Lipschitz : preuve via Picard–Lindelöf de Mathlib (contraction itérée) ; stabilité sous hypothèse plus faible (dérivable, pas C¹).
- Maigre : IsMeagre de Mathlib = définition du cours seulement dans un espace de Baire (énoncé dans un métrique complet).
- corol:equivNormes : la seconde norme modélisée par un second espace E' et un isomorphisme linéaire e (‖x‖' = ‖e x‖).
- Corollaire sur les projections (sans label) : nommé corol_projectionContinue_iff.
- Non formalisés : corol:CauchyLipAuton (solutions maximales absentes de Mathlib), ex:FourierDiverge, th:BanachSteinhausFrechet (facultatif).
### Compacité §3.1–3.4
- « Compact » au sens du cours = CompactSpace ∧ T2Space (Mathlib ne suppose pas séparé) ; les énoncés portent [CompactSpace X] [T2Space X] même quand la séparation est inutile.
- Compactifié d'Alexandrov = OnePoint X de Mathlib (accord grâce à la séparation).
- Bolzano–Weierstrass (ii) via valeurs d'adhérence ; version sous-suite à part.
- Diamètre ≤ ε écrit ∀ x y, dist x y ≤ ε (Metric.diam vaut 0 si non borné).
- Équivalence des normes : preuve par une base (pas par compacité de la sphère).
- Ascoli : C⁰(X,Y) représenté par X →ᵇ Y.
- Non formalisés : corol:AscoliCk, corol:AscoliCkNonBorne (facultatif), remarques sans label.
### Fonctions bosse (annexe)
- Bosse explicite (comme dans le cours) : la ContDiffBump de Mathlib n'est pas radiale de façon prouvable.
- exists_bosse_const_pos : version renforcée (constante > 0), utilisée par la suite.
- prop:cinfSupport, prop:cinfPartition : preuves via Urysohn lisse et partitions de l'unité de Mathlib (énoncés inchangés).
- Partition indexée par Fin I (0..I−1).
### Dualité
- Définitions propres au cours : Inductif, SousLineaire, Reflexif (Φ bijective ; équivalent à surjective), jauge (valeurs dans [0,∞], inf ∅ = ∞ ; égale à gauge de Mathlib si C absorbant), polaire (unilatérale φ(x) ≤ 1 ; égale à celle de Mathlib si C symétrique).
- Hölder : inégalité seulement (cas d'égalité non formalisé).
- corol:minFctCvxRefl : convexité de f : E → ]−∞,∞] exprimée par la convexité de l'épigraphe (ConvexOn ne s'applique pas à EReal) ; « faiblement continue sur les bornés » interprété via WeakSpace.
- Les items après le \subsection commenté (lignes 546–631) sont dans CompaciteFaible.lean, rattaché à `sec:dual`.
- Non formalisés : th:unifCvxReflex (Milman–Pettis), prop:ClarksonIneq, th:lpDualLq (dual de L^p absent de Mathlib), ex:nonReflex.
### Compacité §3.5–3.8
- Brouwer absent de Mathlib : seuls le changement de variables (th:chgVarIntegr), le cas d = 1, le transfert par rétraction et la projection de Schauder sont formalisés ; th:Brouwer, th:Schauder, Cauchy–Peano non formalisés.
- Stone–Weierstrass : énoncé pour [CompactSpace X] (sans séparation) ; preuve via le théorème unitaire de Mathlib, pas celle du cours ; lem:StoneSqrt et corol:StoneMinMax déduits du théorème (énoncés vrais, mais pas comme étapes de la preuve).
- Fredholm : alternative de Mathlib ; corol:FredholmPrecise (i)–(iv) prouvés.
- Non formalisés : second point de prop:opCompactComplCont, lem:convK_compact, corol:eqFuncNoyau, prop:StoneCtrEx (facultatif).
### Hilbert
- Convention sesquilinéaire du cours (antilinéaire à gauche) = celle de Mathlib ; texte actuel cohérent.
- DÉFINITION À RELIRE : projConvexe K x = un minimiseur choisi s'il existe, x sinon (valeur arbitraire hors du cas convexe fermé non vide) ; égal à starProjection pour un sous-espace fermé.
- Convexité énoncée sur ℝ (Convex ℝ K) même si 𝕜 = ℂ.
- prop:decompCone : hypothèse K non vide ajoutée.
- ℓ² = lp (fun _ => 𝕜) 2 de Mathlib.
- Non formalisé : partie S_d⁺ de ex:coneSdp (facultatif).
### Legendre–Fenchel
- Définitions propres au cours : conjuguee, biconjuguee (via l'injection canonique E → E**), domaine, Propre, sousDiff, enveloppeSci, ConvexeEtendue (convexité de l'épigraphe : Mathlib n'a pas de convexité pour des fonctions à valeurs dans EReal).
- ]−∞,∞] codé par EReal + f x ≠ ⊥.
- lem:cvxImplLip : hypothèse f(x) < ∞ ajoutée.
- Preuves différentes du cours pour lem:cvxImplBorne (Baire sur des fermés recouvrant E), th:ssGrad, th:FenchelRockafellar (s.c.i. de f et complétude de E inutiles, gardées).
- Fenchel–Rockafellar : signes vérifiés, corrects dans le texte actuel.
### Sobolev (début)
- Inégalité de Young L¹ × L^p (prop:convolLp) : absente de Mathlib, démontrée ici.
- prop:Jensen : seulement pour g réelle convexe, avec Integrable (g∘f) (l'intégrale de Bochner vaut 0 hors intégrabilité) ; le cas g à valeurs dans ]−∞,∞] n'est pas couvert.
- Hypothèses inutiles retirées : 1 ≤ p (prop:densC0Lp, corol:lpInclusLq), « A mesurable » (lem:convolTranslat).
- Définitions propres au cours : noyauEps (ρ_ε), moduleTransl (ω_p).
- ARRÊT à def:Sobolev (W^{s,p}(Ω) absent de Mathlib, qui n'a que H^{s,p}(ℝ^d) via Fourier). Non formalisés : lem:intDerivIter, prop:testFunSeparab, corol:convolTestFun (topologie limite inductive de 𝓓(Ω)), ex:operCompactL2, corol:distribLp (dual de L^p), et tout ce qui fait intervenir W^{s,p} (injections de Sobolev, Rellich), ainsi que th:YoungFaible (admis).
### Sobolev (24 octobre : résultats indépendants des espaces de Sobolev)
- th:FrechetKolmogorov : 𝓕 ⊆ Lp ℝ p (volume.restrict Ω), conclusion TotallyBounded (et adhérence compacte). La condition |h| ≤ d(K, ℝ^d∖Ω) est écrite K + B'(0,|h|) ⊆ Ω (pour K compact : |h| < d(K, ℝ^d∖Ω), hypothèse très légèrement plus faible ; la formulation littérale dégénère pour Ω = ℝ^d car infDist x ∅ = 0). ω_K : EstModuleCont (convention à trancher). Preuve sans fonction plateau lisse (indicatrice de K₀ + B'(0,η)).
- th:Young : trilinéaire (fonctions positives, et réelles L^p) et convolution ‖f⋆g‖_{r'} ≤ ‖f‖_p‖g‖_q ; preuve dans l'ordre inverse du cours (convolution d'abord, Hölder à trois facteurs + Fubini). Convolution de Mathlib (intégrale p.p.), et non prolongement continu depuis C⁰_c.
- Nouvelle définition normeFaible (‖·‖_{p,w}, formule littérale ; L^{p,w} faible absent de Mathlib) ; ‖f‖_{p,w} ≤ ‖f‖_p ; eq:powLpw.
- eq:homog_lp : première identité seulement, pour toute fonction u (pas seulement u ∈ 𝒟).
- prop:interpLp : hypothèse p₀, p₁ ≥ 1 inutile, retirée.
- prop:convolPow, corol:noyauGreen : hypothèse d ≥ 1 explicite ; |𝕊_{d-1}| = mesure de Mathlib volume.toSphere (= d·|B(0,1)|, pont avec la définition du cours toSphere_eq_cone_Ioc). −ΔG = δ₀ sous deux formes (∫ G(−Δφ) = φ(0), et distributions de Mathlib) ; preuve par régularisation G_ε(x) = c(d)k(|x|²+ε²) au lieu de Stokes. φ = −Δ(G⋆φ) avec la convolution de fonctions (G ∈ L¹_loc), pas celle des distributions.
- Nouvelles définitions : constGreen (c(d)), noyauGreen (G, valeur en 0 sans importance).

## Erreurs ou imprécisions du cours relevées pendant la formalisation

Chacune fait l'objet d'un \claudereport dans le texte.

- TopologieGenerale ex:T1nonT2 (cofinite): "les fermés sont les parties finies" -> "les parties finies et N lui-même".
- TopologieGenerale ex:T1nonT2 (Zariski): non séparé seulement pour d >= 1 (C^0 est un point).
- TopologieGenerale rem:topoFunc: "(x_n) converge ssi (f_i(x_n)) converge pour tout i" faux tel quel (X=]0,1], inclusion dans R, x_n=1/n) ; correct : x_n -> a ssi f_i(x_n) -> f_i(a) pour tout i.
- TopologieGenerale prop:surGrapheSCI: hypothèse f > -inf inutile (info, pas une erreur).
- TopologieGenerale eq:boule_evtlc: "n < -log_2 eta" -> "n <= -log_2 eta" (cas n = -log_2 eta : min{2^{-n},a} < eta ssi a < eta) ; dans la preuve, "toujours satisfait si n >= -log_2 eta" -> "n > -log_2 eta". Contre-exemple eta=1/2, |y-x|_0=0, |y-x|_1=1.
- Completude ex:extUnifCont (preuve) : les deux inégalités du type ω(d(x,z)) ≤ ω(d(x,y)) + ω(d(y,z)) utilisent l'inégalité triangulaire, la croissance ET la sous-additivité de ω (pas seulement « par sous-additivité »).
- Completude th:fixe_Picard : supposer X non vide (sinon pas de point fixe) — détail.
- Bosse prop:cinfBosse : "constante sur B(0,1/3)" -> "constante strictement positive sur B(0,1/3)" ; la preuve de prop:cinfSupport utilise phi > 0 sur B(0,1/3) (contre-exemple à l énoncé seul : bosse radiale portée par la couronne 1/3 <= |x| <= 2/3).
- Hilbert prop:decompCone : supposer K non vide (la définition de cône convexe autorise K = ∅, et P_∅ n'est pas défini).
- LegendreFenchel lem:cvxImplBorne (preuve) : l'union des {f ≤ n} est Dom(f), pas E, donc le \cref{corol:BaireFerme} ne s'applique pas tel quel ; appliquer Baire dans la boule fermée (complète) B'(0,ε) ⊂ Dom(f), recouverte par les {f ≤ n} ∩ B'(0,ε) ; on obtient alors x_0 ∈ B'(0,ε), ce qui assure aussi -εx_0 ∈ Dom(f) (sinon f(-εx_0) peut valoir +∞).
- LegendreFenchel lem:cvxImplLip : supposer f(x) < ∞ (sinon l'hypothèse f ≤ f(x)+M est vide).

## Non formalisé (absent de Mathlib, ou trop long)

Voir les lignes « Non formalisé(s) » ci-dessus. En résumé : théorèmes de Brouwer et de Schauder, Cauchy–Peano, solutions maximales (Cauchy–Lipschitz autonome), dual de L^p, Milman–Pettis et Clarkson, espaces de Sobolev W^{s,p}(Ω) et les injections de Sobolev (sauf Young, interpolation et noyau de Green), espaces C^k_b / C^∞_b / C^k(Ω) comme espaces topologiques, lem:regModuleCont, divergence des séries de Fourier.
