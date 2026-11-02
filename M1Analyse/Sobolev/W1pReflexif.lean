/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Dualite.DualiteLebesgue
import M1Analyse.Sobolev.W1p
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Réflexivité et séparabilité de `W^{1,p}(Ω)` (`eq:W1p_sev_Lp`)

`W^{1,p}(Ω)` s'identifie à un s.e.v. fermé de `L^p(Ω) × L^p(Ω)^d` (`eq:W1p_sev_Lp`) ; il est donc
réflexif pour `1 < p < ∞` (`prop:reflex_sev`, `th:lpDualLq`) et séparable pour `p < ∞`
(`rem:separable_partie`).
-/

open MeasureTheory NormedSpace TopologicalSpace
open scoped ENNReal

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Éq. `eq:W1p_sev_Lp`, réflexivité.** Pour `1 < p < ∞`, `W^{1,p}(Ω)` est réflexif : c'est
un s.e.v. fermé (`prop_SobolevBanach_isClosed`) de `L^p(Ω) × L^p(Ω)^d`, réflexif comme produit
fini (`reflexif_prod`, `reflexif_pi`) d'espaces `L^p` réflexifs (`th:lpDualLq`), donc réflexif
(`prop:reflex_sev`). Dépend de l'axiome de Milman–Pettis (via `reflexif_Lp`). -/
theorem W1p_reflexif (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) : Reflexif (Sobolev1 Ω p) := by
  have hL := reflexif_Lp (μ := volume.restrict (Ω : Set ℝᵈ)) hp hp'
  have hG : Reflexif (LpGrad Ω p) :=
    Reflexif.of_continuousLinearEquiv (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm
      (reflexif_prod hL (Reflexif.of_continuousLinearEquiv
        (PiLp.continuousLinearEquiv p ℝ _).symm (reflexif_pi fun _ => hL)))
  exact prop_reflex_sev hG _ (prop_SobolevBanach_isClosed Ω p)

/-- **Éq. `eq:W1p_sev_Lp`, séparabilité.** Pour `1 ≤ p < ∞`, `W^{1,p}(Ω)` est séparable : partie
(`rem:separable_partie`) de `L^p(Ω) × L^p(Ω)^d`, séparable. -/
theorem W1p_separable (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : SeparableSpace (Sobolev1 Ω p) := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  let L := Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))
  have h1 : SecondCountableTopology (PiLp p fun _ : Fin d => L) :=
    (PiLp.continuousLinearEquiv p ℝ fun _ : Fin d => L).toHomeomorph.secondCountableTopology
  have h2 : SecondCountableTopology (LpGrad Ω p) :=
    (WithLp.prodContinuousLinearEquiv p ℝ L
      (PiLp p fun _ : Fin d => L)).toHomeomorph.secondCountableTopology
  infer_instance

end M1Analyse
