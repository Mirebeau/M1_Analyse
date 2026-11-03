# Notes du cours M1 Analyse Fonctionnelle, ENS Paris-Saclay

Ce dépôt contient les fichiers source des notes du cours de M1 d'Analyse Fonctionnelle de l'ENS Paris-Saclay, enseignant Jean-Marie Mirebeau. 
Sources Latex : Fichier `M1_Analyse.tex` et dossier `include/`

[PDF à jour du cours](https://www.dropbox.com/scl/fi/inkckohpt8dqlcb2ys76f/M1_Analyse_Shared.pdf?rlkey=0yh1c9c06i1413ve901lqrhsu&dl=1)

En octobre 2026, le cours a été auto-formalisé en Lean, via l'IA Claude et les [skills de Scott Armstrong](https://www.scottnarmstrong.com/2026/10/autoformalization-is-now-very-easy/). 
Sources Lean : dossier `M1Analyse/`. Pour recompiler (nécessite [elan](https://github.com/leanprover/elan)) :

    git clone https://github.com/Mirebeau/M1_Analyse && cd M1_Analyse
    lake exe cache get   # télécharge Mathlib précompilé (sinon plusieurs heures de compilation)
    lake build           # cible par défaut M1Analyse

Une recompilation complète du projet prend environ 2 minutes (Apple M1 Pro, 10 cœurs, ~3,3 Go de RAM).