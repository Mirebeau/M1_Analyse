/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.Basic

/-!
# §3.6 Point fixe de Schauder (`subsec:Schauder`)

Source : `Include/Compacite.tex`, sous-section `subsec:Schauder`.

Le théorème de point fixe de Schauder (`th:Schauder`) et le théorème de Cauchy-Arzelà-Peano
(`th:CauchyPeano`) sont dans `M1Analyse/Compacite/SchauderPeano.lean` (ils reposent sur
`th:Brouwer`).

On formalise ici l'étape élémentaire de la preuve du `th:Schauder` : la « projection de
Schauder » `g_ε`, définie à partir d'un recouvrement `K ⊆ ⋃ᵢ B(xᵢ, ε)`, est continue sur `K`,
à valeurs dans l'enveloppe convexe `K_ε := Hull{xᵢ}`, et vérifie `‖g_ε(x) - x‖ ≤ ε`.
-/

open Set Metric

namespace M1Analyse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Projection de Schauder (étape de la preuve du théorème de Schauder) : pour des points
`x₀, …, x_I` et `ε > 0`, `g_ε(x) := (∑ᵢ φᵢ(x) xᵢ) / (∑ᵢ φᵢ(x))`, où `φᵢ(x) := max {0, ε - ‖x - xᵢ‖}`
(barycentre `Finset.centerMass` des `xᵢ` pour les poids `φᵢ(x)`). -/
noncomputable def schauderProj {n : ℕ} (ε : ℝ) (xs : Fin n → X) (x : X) : X :=
  Finset.univ.centerMass (fun i => max 0 (ε - ‖x - xs i‖)) xs

omit [NormedSpace ℝ X] in
/-- Sur le recouvrement `⋃ᵢ B(xᵢ, ε)`, la somme des poids `∑ᵢ φᵢ(x)` est strictement positive :
`g_ε` est bien définie (preuve du `th:Schauder`). -/
theorem schauderProj_sum_pos {n : ℕ} {ε : ℝ} {xs : Fin n → X} {x : X}
    (hx : x ∈ ⋃ i, ball (xs i) ε) : 0 < ∑ i, max 0 (ε - ‖x - xs i‖) := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  rw [mem_ball, dist_eq_norm] at hi
  exact Finset.sum_pos' (fun j _ => le_max_left _ _)
    ⟨i, Finset.mem_univ _, lt_max_of_lt_right (by linarith)⟩

/-- **Projection de Schauder** (étape de la preuve du `th:Schauder`). Soit `K ⊆ ⋃ᵢ B(xᵢ, ε)`.
Alors `g_ε` est continue sur `K`, à valeurs dans `K_ε := Hull{xᵢ}`, et `‖g_ε(x) - x‖ ≤ ε`
pour tout `x ∈ K`. -/
theorem schauderProj_spec {n : ℕ} {ε : ℝ} (xs : Fin n → X) (K : Set X)
    (hK : K ⊆ ⋃ i, ball (xs i) ε) :
    ContinuousOn (schauderProj ε xs) K ∧
      (∀ x ∈ K, schauderProj ε xs x ∈ convexHull ℝ (range xs)) ∧
      ∀ x ∈ K, ‖schauderProj ε xs x - x‖ ≤ ε := by
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- continuité : quotient de fonctions continues, à dénominateur non nul sur `K`
    have hcont : ∀ i, Continuous fun x : X => max 0 (ε - ‖x - xs i‖) := fun i => by fun_prop
    unfold schauderProj Finset.centerMass
    refine ContinuousOn.smul ?_ (Continuous.continuousOn (by fun_prop))
    exact (Continuous.continuousOn (by fun_prop)).inv₀ fun x hx =>
      (schauderProj_sum_pos (hK hx)).ne'
  · exact Finset.centerMass_mem_convexHull _ (fun i _ => le_max_left _ _)
      (schauderProj_sum_pos (hK hx)) fun i _ => mem_range_self i
  · -- barycentre de points de la boule `B(x, ε)` (ceux de poids non nul)
    classical
    have hmem : schauderProj ε xs x ∈ ball x ε := by
      unfold schauderProj
      rw [← Finset.centerMass_filter_ne_zero]
      refine (convex_ball x ε).centerMass_mem (fun i _ => le_max_left _ _) ?_ ?_
      · rw [Finset.sum_filter_ne_zero]
        exact schauderProj_sum_pos (hK hx)
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [mem_ball, dist_comm, dist_eq_norm]
        by_contra h
        exact hi.2 (max_eq_left (by linarith))
    rw [mem_ball, dist_eq_norm] at hmem
    exact hmem.le

end M1Analyse
