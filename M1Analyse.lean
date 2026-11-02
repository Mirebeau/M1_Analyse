/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Outils.Schwarz
import M1Analyse.TopologieGenerale.OuvertsFermes
import M1Analyse.TopologieGenerale.ComparaisonTopologies
import M1Analyse.TopologieGenerale.Voisinages
import M1Analyse.TopologieGenerale.Separation
import M1Analyse.TopologieGenerale.Continuite
import M1Analyse.TopologieGenerale.Metrique
import M1Analyse.TopologieGenerale.EVN
import M1Analyse.TopologieGenerale.EVTLC
import M1Analyse.TopologieGenerale.EspacesFonctionnels
import M1Analyse.TopologieGenerale.TopologieFaible
import M1Analyse.Completude.Cauchy
import M1Analyse.Completude.FonctionnelsComplets
import M1Analyse.Completude.Prolongements
import M1Analyse.Completude.Picard
import M1Analyse.Completude.Baire
import M1Analyse.Completude.BaireLineaire
import M1Analyse.Compacite.BorelLebesgue
import M1Analyse.Compacite.CompactsMetriques
import M1Analyse.Compacite.DimensionFinie
import M1Analyse.Compacite.Produits
import M1Analyse.Compacite.Brouwer
import M1Analyse.Compacite.Schauder
import M1Analyse.Compacite.SchauderPeano
import M1Analyse.Compacite.StoneWeierstrass
import M1Analyse.Compacite.OperateursCompacts
import M1Analyse.Dualite.HahnBanach
import M1Analyse.Dualite.Reflexivite
import M1Analyse.Dualite.DualiteLebesgue
import M1Analyse.Dualite.HahnBanachGeometrique
import M1Analyse.Dualite.CompaciteFaible
import M1Analyse.Sobolev.FonctionsTest
import M1Analyse.Sobolev.ConvolutionLp
import M1Analyse.Sobolev.ConvolutionSobolev
import M1Analyse.Sobolev.W1p
import M1Analyse.Sobolev.W1p0Separable
import M1Analyse.Sobolev.W1infLip
import M1Analyse.Sobolev.ConvolDistrib
import M1Analyse.Sobolev.FrechetKolmogorov
import M1Analyse.Sobolev.InjSousCritique
import M1Analyse.Sobolev.InjSousCritiqueW1p
import M1Analyse.Sobolev.InjSurCritique
import M1Analyse.Sobolev.NoyauGreen
import M1Analyse.Sobolev.Rellich
import M1Analyse.Sobolev.RellichCorollaire
import M1Analyse.Sobolev.MinNonLinH1
import M1Analyse.Sobolev.BouleW1pFerme
import M1Analyse.Bosse.Bosse
import M1Analyse.Hilbert.Hilbert
import M1Analyse.LegendreFenchel.LegendreFenchel

/-!
# M1Analyse

Formalisation Lean 4 / Mathlib des notes de cours `M1_Analyse.tex`.
Chaque module correspond à une sous-sous-section du cours ; voir `DEFINITIONS.md`.
-/
