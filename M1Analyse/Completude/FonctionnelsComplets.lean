/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# §2.2 Espaces fonctionnels complets (`subsec:fctsComplets`)

Source : `Include/Completude.tex`, sous-section `subsec:fctsComplets`.

Les objets du cours sont ceux de Mathlib : `C⁰_b(X,E)` = `X →ᵇ E`, `L^p(X,μ)` =
`MeasureTheory.Lp 𝕜 p μ` ; la complétude de ces espaces est une instance Mathlib.

L'espace `C^ω_b(X,E)` des fonctions continues bornées admettant le module de continuité `ω`
(à une constante multiplicative près) n'existe pas dans Mathlib pour un module `ω` général :
on introduit la semi-norme `|f|_ω` (`seminormeModule`, à valeurs dans `[0, ∞]`), l'espace
`C^ω_b(X,E)` (`espaceModule`, sous-module de `X →ᵇ E`) et la norme `‖f‖_ω`
(`normeModule`), et l'on démontre que `‖·‖_ω` est une norme sur `C^ω_b(X,E)`, pour laquelle cet
espace est complet (critère de Cauchy, `def:suiteCauchy`/`def:complet`).
-/

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace M1Analyse

/-! ### Espaces de Banach -/

/-- **Ex. `ex:cont_bornee_Banach`.** Soient `X` un espace topologique et `E` un Banach. Alors
`C⁰_b(X,E)` (muni de la norme uniforme) est un Banach. -/
theorem ex_cont_bornee_Banach {𝕜 X E : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    CompleteSpace (X →ᵇ E) :=
  inferInstance

section Module

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]

/-- Semi-norme `|f|_ω := sup_{x ≠ y} ‖f(x) - f(y)‖ / ω(d(x,y)) ∈ [0, ∞]` de l'exemple
`ex:Holder_Banach`, associée à un module de continuité `ω : ℝ₊ → ℝ₊`. -/
noncomputable def seminormeModule (ω : ℝ≥0 → ℝ≥0) (f : X → E) : ℝ≥0∞ :=
  ⨆ (x : X) (y : X) (_ : x ≠ y), ‖f x - f y‖ₑ / (ω (nndist x y) : ℝ≥0∞)

/-- Norme `‖f‖_ω := ‖f‖_∞ + |f|_ω` de l'exemple `ex:Holder_Banach` (la semi-norme `|f|_ω` est
convertie en réel, ce qui n'a de sens que si `|f|_ω < ∞`). -/
noncomputable def normeModule (ω : ℝ≥0 → ℝ≥0) (f : X →ᵇ E) : ℝ :=
  ‖f‖ + (seminormeModule ω f).toReal

variable {ω : ℝ≥0 → ℝ≥0}

lemma seminormeModule_le_iff {f : X → E} {C : ℝ≥0∞} :
    seminormeModule ω f ≤ C ↔ ∀ x y, x ≠ y → ‖f x - f y‖ₑ / (ω (nndist x y) : ℝ≥0∞) ≤ C := by
  simp only [seminormeModule, iSup_le_iff]

lemma le_seminormeModule (f : X → E) {x y : X} (h : x ≠ y) :
    ‖f x - f y‖ₑ / (ω (nndist x y) : ℝ≥0∞) ≤ seminormeModule ω f :=
  seminormeModule_le_iff.1 le_rfl x y h

/-- Si `ω > 0` hors de `0`, la condition `|f|_ω ≤ C` s'écrit
`‖f(x) - f(y)‖ ≤ C ω(d(x,y))` pour tous `x ≠ y`. -/
lemma seminormeModule_le_iff' (hω : ∀ s, 0 < s → 0 < ω s) {f : X → E} {C : ℝ≥0∞} :
    seminormeModule ω f ≤ C ↔ ∀ x y, x ≠ y → ‖f x - f y‖ₑ ≤ C * ω (nndist x y) := by
  rw [seminormeModule_le_iff]
  refine forall₂_congr fun x y => imp_congr_right fun h => ?_
  have h0 : (ω (nndist x y) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (hω _ (NNReal.coe_pos.1 (by rw [coe_nndist]; exact dist_pos.2 h))).ne'
  exact ENNReal.div_le_iff h0 ENNReal.coe_ne_top

lemma seminormeModule_add_le (f g : X → E) :
    seminormeModule ω (f + g) ≤ seminormeModule ω f + seminormeModule ω g := by
  refine seminormeModule_le_iff.2 fun x y h => ?_
  calc ‖(f + g) x - (f + g) y‖ₑ / (ω (nndist x y) : ℝ≥0∞)
      ≤ (‖f x - f y‖ₑ + ‖g x - g y‖ₑ) / (ω (nndist x y) : ℝ≥0∞) := by
        gcongr
        simp only [Pi.add_apply, add_sub_add_comm]
        exact enorm_add_le _ _
    _ = _ := ENNReal.add_div
    _ ≤ _ := add_le_add (le_seminormeModule f h) (le_seminormeModule g h)

lemma seminormeModule_neg (f : X → E) : seminormeModule ω (-f) = seminormeModule ω f := by
  refine iSup_congr fun x => iSup_congr fun y => iSup_congr fun _ => ?_
  rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, enorm_sub_rev]

lemma seminormeModule_sub_le (f g : X → E) :
    seminormeModule ω (f - g) ≤ seminormeModule ω f + seminormeModule ω g := by
  rw [sub_eq_add_neg, ← seminormeModule_neg (ω := ω) g]
  exact seminormeModule_add_le f (-g)

lemma seminormeModule_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (f : X → E) :
    seminormeModule ω (c • f) = ‖c‖ₑ * seminormeModule ω f := by
  simp only [seminormeModule, Pi.smul_apply, ← smul_sub, enorm_smul, ENNReal.mul_iSup,
    mul_div_assoc]

/-- L'espace `C^ω_b(X,E) := {f ∈ C⁰_b(X,E) | |f|_ω < ∞}` de l'exemple `ex:Holder_Banach`,
sous-espace vectoriel de `C⁰_b(X,E)`. -/
def espaceModule (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 E] (ω : ℝ≥0 → ℝ≥0) :
    Submodule 𝕜 (X →ᵇ E) where
  carrier := {f | seminormeModule ω f < ∞}
  zero_mem' := by
    change seminormeModule ω (0 : X → E) < ∞
    refine lt_of_le_of_lt (seminormeModule_le_iff.2 fun x y _ => ?_) ENNReal.zero_lt_top
    simp
  add_mem' := by
    intro f g hf hg
    change seminormeModule ω (⇑f + ⇑g) < ∞
    exact (seminormeModule_add_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)
  smul_mem' := by
    intro c f hf
    change seminormeModule ω (c • ⇑f) < ∞
    rw [seminormeModule_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hf

/-- **Ex. `ex:Holder_Banach` (Complétude des espaces de Lipschitz et Hölder), norme.**
Soient `(X,d)` un espace métrique, `E` un evn et `ω : ℝ₊ → ℝ₊` un module de continuité
strictement positif hors de `0`. Alors `‖·‖_ω = ‖·‖_∞ + |·|_ω` est une norme sur `C^ω_b(X,E)`
(axiomes de `def:norme`). -/
theorem ex_Holder_Banach_norme {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    (_hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (_hω : ∀ s, 0 < s → 0 < ω s) :
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), 0 ≤ normeModule ω f) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), f ≠ 0 → 0 < normeModule ω f) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), ∀ c : 𝕜,
      normeModule ω (c • f) = ‖c‖ * normeModule ω f) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), ∀ g ∈ espaceModule 𝕜 ω (X := X) (E := E),
      normeModule ω (f + g) ≤ normeModule ω f + normeModule ω g) := by
  refine ⟨fun f _ => add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    fun f _ hf => add_pos_of_pos_of_nonneg (norm_pos_iff.2 hf) ENNReal.toReal_nonneg,
    fun f _ c => ?_, fun f hf g hg => ?_⟩
  · have hc : ⇑(c • f) = c • ⇑f := rfl
    rw [normeModule, normeModule, hc, seminormeModule_smul,
      norm_smul, ENNReal.toReal_mul, toReal_enorm, mul_add]
  · rw [normeModule, normeModule, normeModule, BoundedContinuousFunction.coe_add]
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.ne, hg.ne⟩)
      (seminormeModule_add_le (ω := ω) ⇑f ⇑g)
    rw [ENNReal.toReal_add hf.ne hg.ne] at h
    linarith [norm_add_le f g]

/-- **Ex. `ex:Holder_Banach` (Complétude des espaces de Lipschitz et Hölder), complétude.**
Soient `(X,d)` un espace métrique, `E` un Banach et `ω : ℝ₊ → ℝ₊` un module de continuité
strictement positif hors de `0`. Alors `C^ω_b(X,E)` est complet pour la norme
`‖·‖_ω = ‖·‖_∞ + |·|_ω` : toute suite de `C^ω_b(X,E)` de Cauchy pour `‖·‖_ω` converge pour
`‖·‖_ω` vers un élément de `C^ω_b(X,E)`. -/
theorem ex_Holder_Banach {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (_hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (hω : ∀ s, 0 < s → 0 < ω s)
    (f : ℕ → X →ᵇ E) (hf : ∀ n, f n ∈ espaceModule 𝕜 ω)
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, normeModule ω (f p - f q) ≤ ε) :
    ∃ g ∈ espaceModule 𝕜 ω, Tendsto (fun n => normeModule ω (f n - g)) atTop (𝓝 0) := by
  have hfin : ∀ p q, seminormeModule ω ⇑(f p - f q) ≠ ∞ := fun p q => by
    rw [BoundedContinuousFunction.coe_sub]
    exact ((seminormeModule_sub_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hf p, hf q⟩)).ne
  -- La suite est de Cauchy pour la norme uniforme, donc converge vers `g ∈ C⁰_b(X,E)`.
  have hcauchy : CauchySeq f := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    rw [dist_eq_norm]
    have := hN p hp q hq
    rw [normeModule] at this
    linarith [ENNReal.toReal_nonneg (a := seminormeModule ω ⇑(f p - f q))]
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hgx : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (g x)) := fun x =>
    ((continuous_eval_const x).tendsto g).comp hg
  -- Contrôle de `|f_n - g|_ω` par passage à la limite.
  have hkey : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, seminormeModule ω ⇑(f n - g) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn => (seminormeModule_le_iff' hω).2 fun x y hxy => ?_⟩
    have hlim : Tendsto (fun m => ‖(f n - f m) x - (f n - f m) y‖) atTop
        (𝓝 ‖(f n - g) x - (f n - g) y‖) := by
      simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
      exact (((tendsto_const_nhds.sub (hgx x)).sub (tendsto_const_nhds.sub (hgx y)))).norm
    have hbound : ∀ m ≥ N, ‖(f n - f m) x - (f n - f m) y‖ ≤ ε * ω (nndist x y) := by
      intro m hm
      have h1 : (seminormeModule ω ⇑(f n - f m)).toReal ≤ ε := by
        have := hN n hn m hm
        rw [normeModule] at this
        linarith [norm_nonneg (f n - f m)]
      have h2 := (seminormeModule_le_iff' hω).1
        (le_of_eq (ENNReal.ofReal_toReal (hfin n m)).symm) x y hxy
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul
        ENNReal.toReal_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right h1 (NNReal.coe_nonneg _))
    have := le_of_tendsto hlim (eventually_atTop.2 ⟨N, hbound⟩)
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hε.le]
    exact ENNReal.ofReal_le_ofReal this
  obtain ⟨N₁, hN₁⟩ := hkey 1 one_pos
  have hgmem : g ∈ espaceModule 𝕜 ω := by
    change seminormeModule ω ⇑g < ∞
    have hg' : ⇑g = ⇑(f N₁) - ⇑(f N₁ - g) := by
      rw [BoundedContinuousFunction.coe_sub, sub_sub_cancel]
    rw [hg']
    exact (seminormeModule_sub_le _ _).trans_lt (ENNReal.add_lt_top.2
      ⟨hf N₁, (hN₁ N₁ le_rfl).trans_lt ENNReal.ofReal_lt_top⟩)
  refine ⟨g, hgmem, ?_⟩
  have h1 : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hg
  have h2 : Tendsto (fun n => (seminormeModule ω ⇑(f n - g)).toReal) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hkey (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le (hN n hn)).trans_lt
      (half_lt_self hε)
  simpa [normeModule] using h1.add h2

/-- **Ex. `ex:Holder_Banach`, espaces de Hölder et de Lipschitz.** Cas particulier
`ω(s) := s^α` : pour `0 < α ≤ 1`, l'espace de Hölder `C^α_b(X,E)` (`α < 1`), resp. l'espace
`Lip_b(X,E)` (`α = 1`), est complet pour la norme `‖·‖_∞ + |·|_{C^α}`. -/
theorem ex_Holder_Banach_holder {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    {α : ℝ} (hα : 0 < α) (_hα1 : α ≤ 1) (f : ℕ → X →ᵇ E)
    (hf : ∀ n, f n ∈ espaceModule 𝕜 (fun s => s ^ α))
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      normeModule (fun s => s ^ α) (f p - f q) ≤ ε) :
    ∃ g ∈ espaceModule 𝕜 (fun s => s ^ α),
      Tendsto (fun n => normeModule (fun s => s ^ α) (f n - g)) atTop (𝓝 0) := by
  refine ex_Holder_Banach ?_ (fun s hs => NNReal.rpow_pos hs) f hf hC
  have := (NNReal.continuous_rpow_const hα.le).tendsto 0
  rwa [NNReal.zero_rpow hα.ne'] at this

end Module

/-- **Ex. `ex:LpBanach`.** Soit `(X,μ)` un espace mesuré. Alors `L^p(X,μ)` est un Banach, pour
tout `p ∈ [1, ∞]`. -/
theorem ex_LpBanach {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (Lp 𝕜 p μ) :=
  inferInstance

end M1Analyse
