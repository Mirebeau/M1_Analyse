/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# §5.2 Convolution de distributions et espaces de Sobolev (`subsec:convolSobolev`)

Source : `Include/Sobolev.tex`, sous-section `subsec:convolSobolev` (début seulement).

La distribution `U_f` associée à `f ∈ L^1_loc(Ω)` est `Distribution.ofFun Ω f volume ⊤` de
Mathlib, de formule `⟨U_f, φ⟩ = ∫ φ f`. Les espaces de Sobolev `W^{s,p}(Ω)` (définis par
dérivées faibles) ne sont pas dans Mathlib (qui ne contient que les espaces de potentiel de
Bessel `H^{s,p}(ℝ^d)`, définis par transformée de Fourier) : la suite de la sous-section n'est
pas formalisée.
-/

open Set Filter Topology MeasureTheory
open scoped Distributions

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Prop. `prop:distribL1Loc` (Distribution associée à une fonction), définition.**
Pour `f ∈ L^1_loc(Ω)` et `φ ∈ 𝓓(Ω)`, `⟨U_f, φ⟩ = ∫_Ω f φ`, où `U_f` est la distribution
Mathlib `Distribution.ofFun Ω f volume ⊤` (l'intégrale peut être prise sur `ℝ^d`, `φ` étant
nulle hors de `Ω`). -/
theorem prop_distribL1Loc_apply (Ω : TopologicalSpace.Opens ℝᵈ) {f : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) (φ : 𝓓(Ω, ℝ)) :
    Distribution.ofFun Ω f volume ⊤ φ = ∫ x, f x * φ x := by
  rw [Distribution.ofFun_apply hf]
  simp only [smul_eq_mul, mul_comm]

/-- **Prop. `prop:distribL1Loc`, ordre `0`.** Pour `K ⊂⊂ Ω` compact et `φ ∈ 𝓓_K(Ω)` avec
`|φ| ≤ C`, on a `|⟨U_f, φ⟩| ≤ C ‖f‖_{L^1(K)}` : `U_f` est d'ordre `0`. -/
theorem prop_distribL1Loc_ordre (Ω : TopologicalSpace.Opens ℝᵈ) {f : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) {K : Set ℝᵈ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (φ : 𝓓(Ω, ℝ)) (hφK : tsupport φ ⊆ K) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) :
    |Distribution.ofFun Ω f volume ⊤ φ| ≤ C * ∫ x in K, |f x| := by
  have hfK : IntegrableOn f K := hf.integrableOn_compact_subset hKΩ hK
  rw [prop_distribL1Loc_apply Ω hf φ, ← integral_const_mul,
    ← integral_indicator hK.measurableSet, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (IntegrableOn.integrable_indicator
    (hfK.norm.const_mul C) hK.measurableSet) (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφK h)
    simp [indicator_of_notMem hx, this]

/-- **Prop. `prop:distribL1Loc`, injectivité.** Si `f, g ∈ L^1_loc(Ω)` vérifient `U_f = U_g`,
alors `f = g` presque partout sur `Ω`.
Remarque : la continuité de `f ↦ U_f` (de `L^1_loc(Ω)` dans `𝓓'(Ω)`) n'est pas formalisée. -/
theorem prop_distribL1Loc_injective (Ω : TopologicalSpace.Opens ℝᵈ) {f g : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω)
    (h : Distribution.ofFun Ω f volume ⊤ = Distribution.ofFun Ω g volume ⊤) :
    f =ᵐ[volume.restrict (Ω : Set ℝᵈ)] g :=
  Distribution.ofFun_injective hf hg h

end M1Analyse
