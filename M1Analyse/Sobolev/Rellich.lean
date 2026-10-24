/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# §5.5 Injection compacte de Sobolev - théorème de Rellich (`subsec:injCompacte`)

Source : `Include/Sobolev.tex`, sous-section `subsec:injCompacte`.

Seule l'inégalité d'interpolation `L^p` (`prop:interpLp`) est formalisée, avec les objets
`eLpNorm` de Mathlib. Les autres énoncés (`prop:trans_grad_lp`, `th:Rellich`,
`corol:Rellich`, ...) portent sur les espaces de Sobolev `W^{1,p}(Ω)`, absents de Mathlib.
-/

open MeasureTheory
open scoped ENNReal

namespace M1Analyse

/-- **Prop. `prop:interpLp` (Inégalité d'interpolation `L^p`).** Soient `(X, μ)` un espace
mesuré, `f : X → ℝ` mesurable, `p₀, p₁ ∈ [1, ∞]` et `θ ∈ ]0, 1[`. Alors
`‖f‖_{p_θ} ≤ ‖f‖_{p₀}^{1-θ} ‖f‖_{p₁}^θ`, où `1/p_θ := (1-θ)/p₀ + θ/p₁`.
Remarque : l'hypothèse `p₀, p₁ ≥ 1` du cours est superflue (l'énoncé vaut pour
`p₀, p₁ ∈ [0, ∞]`). -/
theorem prop_interpLp {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) {p₀ p₁ pθ : ℝ≥0∞} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / pθ = ENNReal.ofReal (1 - θ) / p₀ + ENNReal.ofReal θ / p₁) :
    eLpNorm f pθ μ ≤ eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
  have h1θ : 0 < 1 - θ := by linarith
  set a := p₀ * ENNReal.ofReal (1 / (1 - θ)) with ha
  set b := p₁ * ENNReal.ofReal (1 / θ) with hb
  have hinv : ∀ (q : ℝ≥0∞) (s : ℝ), 0 < s →
      (q * ENNReal.ofReal (1 / s))⁻¹ = ENNReal.ofReal s / q := by
    intro q s hs
    rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (by simp [hs])),
      ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv, div_eq_mul_inv, mul_comm]
  have hT : ENNReal.HolderTriple a b pθ := by
    constructor
    rw [ha, hb, hinv _ _ h1θ, hinv _ _ hθ₀, ← hpθ, one_div]
  have hn : ∀ x, ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ = ‖f x‖ := by
    intro x
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
  calc eLpNorm f pθ μ = eLpNorm (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ) pθ μ := by
        simp only [hn]; exact (eLpNorm_norm f hf).symm
    _ ≤ eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) a μ * eLpNorm (fun x => ‖f x‖ ^ θ) b μ :=
        eLpNorm_smul_le_mul_eLpNorm (φ := fun x => ‖f x‖ ^ (1 - θ)) (f := fun x => ‖f x‖ ^ θ)
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
    _ = eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
        rw [eLpNorm_norm_rpow f hf h1θ, eLpNorm_norm_rpow f hf hθ₀, ha, hb, mul_assoc, mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          one_div_mul_cancel h1θ.ne', one_div_mul_cancel hθ₀.ne', ENNReal.ofReal_one, mul_one,
          mul_one]

end M1Analyse
