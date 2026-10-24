/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

/-!
# §3.5 Point fixe de Brouwer (`subsec:Brouwer`)

Source : `Include/Compacite.tex`, sous-section `subsec:Brouwer`.

Le théorème de point fixe de Brouwer (`th:Brouwer`) est absent de Mathlib, de même que les
outils de la preuve de Lax suivie par le cours (`lem:chgVarLax`, `lem:noretractSmooth`,
`corol:noretract`, équivalents en substance au théorème de Brouwer) : ces énoncés ne sont pas
formalisés.

On formalise :
* la formule de changement de variable `th:chgVarIntegr`, citée sans preuve par le cours, et
  présente dans Mathlib (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) ;
* le cas `d = 1` du théorème de Brouwer, par le théorème des valeurs intermédiaires ;
* l'argument de rétraction du corollaire (non numéroté) suivant `th:Brouwer` : si une boule `B`
  a la propriété du point fixe et se rétracte sur `K`, alors `K` a la propriété du point fixe.
-/

open Set MeasureTheory

namespace M1Analyse

/-- **Thm. `th:chgVarIntegr` (Changement de variable dans une intégrale).** Soient
`U, V ⊆ ℝ^d` ouverts, `φ ∈ C¹(U, V)` un difféomorphisme, et `f : V → ℝ` intégrable. Alors
`∫_V f(x) dx = ∫_U f(φ(x)) |det J(x)| dx`, où `det J(x)` est le jacobien de `φ`
(déterminant de la différentielle `fderiv ℝ φ x`).
Remarque : l'énoncé Mathlib ne requiert que l'injectivité et la différentiabilité de `φ` sur
`U` ; les hypothèses de difféomorphisme (inverse `C¹`) et d'intégrabilité du cours sont gardées
pour la fidélité mais ne servent pas.
Preuve (absente du cours) : formule de Mathlib
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem th_chgVarIntegr {d : ℕ} (U V : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (_hV : IsOpen V) (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hφ : ContDiffOn ℝ 1 φ U) (hinj : InjOn φ U) (himg : φ '' U = V)
    (_hinv : ContDiffOn ℝ 1 (Function.invFunOn φ U) V)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (_hf : IntegrableOn f V) :
    ∫ x in V, f x = ∫ x in U, f (φ x) * |(fderiv ℝ φ x).det| := by
  have hder : ∀ x ∈ U, HasFDerivWithinAt φ (fderiv ℝ φ x) U x := fun x hx =>
    (((hφ.differentiableOn one_ne_zero) x hx).differentiableAt
      (hU.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  subst himg
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hder hinj f]
  simp only [smul_eq_mul, mul_comm]

/-- **Cas `d = 1` du théorème de Brouwer** (`th:Brouwer`). Toute fonction continue
`f : [-1, 1] → [-1, 1]` admet un point fixe (la boule unité fermée de `ℝ` est `[-1, 1]`).
Preuve : théorème des valeurs intermédiaires appliqué à `x ↦ f(x) - x`. -/
theorem brouwer_dim_one (f : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1)) : ∃ x, f x = x := by
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  set g : ℝ → ℝ := fun y => (f (projIcc (-1) 1 hab y) : ℝ) - y
  have hg : Continuous g := by
    have : Continuous fun y => (f (projIcc (-1) 1 hab y) : ℝ) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
    exact this.sub continuous_id
  have h0 : (0 : ℝ) ∈ Icc (g 1) (g (-1)) := by
    constructor
    · have := (f (projIcc (-1) 1 hab 1)).2.2
      simp only [g]; linarith
    · have := (f (projIcc (-1) 1 hab (-1))).2.1
      simp only [g]; linarith
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc' hab hg.continuousOn h0
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  have : projIcc (-1) 1 hab y = ⟨y, hy⟩ := projIcc_of_mem hab hy
  simp only [g, this] at hgy
  linarith

/-- Argument de rétraction (corollaire suivant `th:Brouwer`, premier point). Soit `K ⊆ B`, et
`P ∈ C⁰(B, K)` une rétraction (`P|_K = Id`). Si toute `g ∈ C⁰(B, B)` admet un point fixe, alors
toute `f ∈ C⁰(K, K)` admet un point fixe.
Remarque : le cours applique ceci avec `B` la boule unité de `ℝ^d` et le `th:Brouwer` (non
formalisé), qui est ici une hypothèse. -/
theorem fixedPoint_of_retract {X : Type*} [TopologicalSpace X] {B K : Set X} (hKB : K ⊆ B)
    (hB : ∀ g : C(B, B), ∃ x, g x = x) (P : C(B, K)) (hP : ∀ x : K, P ⟨x, hKB x.2⟩ = x)
    (f : C(K, K)) : ∃ x, f x = x := by
  -- `x` point fixe de `f ∘ P` (vue dans `B`) ; alors `x ∈ K` et `P x = x`
  set ι : C(K, B) := ⟨fun x => ⟨x, hKB x.2⟩, by fun_prop⟩
  obtain ⟨x, hx⟩ := hB (ι.comp (f.comp P))
  have hxK : (x : X) ∈ K := by
    rw [← hx]; exact (f (P x)).2
  have hPx : P x = ⟨x, hxK⟩ := by
    have := hP ⟨x, hxK⟩
    simpa using this
  refine ⟨⟨x, hxK⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hx
  simp only [ContinuousMap.comp_apply, hPx] at this
  exact this

end M1Analyse
