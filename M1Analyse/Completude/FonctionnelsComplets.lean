/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import M1Analyse.TopologieGenerale.EVN

/-!
# §2.2 Espaces fonctionnels complets (`subsec:fctsComplets`)

Source : `Include/Completude.tex`, sous-section `subsec:fctsComplets`.

Les objets du cours sont ceux de Mathlib : `C⁰_b(X,E)` = `X →ᵇ E`, `L^p(X,μ)` =
`MeasureTheory.Lp 𝕜 p μ` ; la complétude de ces espaces est une instance Mathlib.

L'espace `C^ω_b(X,E)` des fonctions continues bornées admettant le module de continuité `ω`
(à une constante multiplicative près) n'existe pas dans Mathlib pour un module `ω` général :
avec la semi-norme `|f|_ω` (`seminormeModule`, à valeurs dans `[0, ∞]`, introduite dans
`M1Analyse.TopologieGenerale.EVN`), on introduit l'espace `C^ω_b(X,E)` (`espaceModule`,
sous-module de `X →ᵇ E`) et la norme `‖f‖_ω ∈ [0, ∞]` (`normeModule`), et l'on démontre que
`‖·‖_ω` est une norme sur `C^ω_b(X,E)`, pour laquelle cet espace est complet (critère de Cauchy,
`def:suiteCauchy`/`def:complet`).
-/

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace M1Analyse

/-! ### Espaces de Banach -/

/-- **Ex. `ex:cont_bornee_Banach`.** Soient `X` un espace topologique et `E` un Banach. Alors
`C⁰_b(X,E)` (muni de la norme uniforme) est un Banach.
Preuve (via Mathlib, même stratégie que le cours) : instance de complétude de Mathlib (limite
simple, approchée uniformément, donc continue et bornée). -/
theorem ex_cont_bornee_Banach {𝕜 X E : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    CompleteSpace (X →ᵇ E) :=
  inferInstance

section Module

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]

/-- Norme `‖f‖_ω := ‖f‖_∞ + |f|_ω ∈ [0, ∞]` de l'exemple `ex:Holder_Banach`, définie pour toute
fonction `f : X → E` (`normeSup`, `seminormeModule`). Pour `ω(s) = s^α`, c'est la norme de
Hölder `normeHolder α` (`normeHolder_eq_normeModule`).
Pont Mathlib : pour `f : X →ᵇ E`, `‖f‖_ω = ‖f‖ₑ + |f|_ω`, où `‖f‖` est la norme de
`BoundedContinuousFunction` (`normeModule_coe`). -/
noncomputable def normeModule (ω : ℝ≥0 → ℝ≥0) (f : X → E) : ℝ≥0∞ :=
  normeSup f + seminormeModule ω f

variable {ω : ℝ≥0 → ℝ≥0}

theorem normeModule_coe (f : X →ᵇ E) : normeModule ω f = ‖f‖ₑ + seminormeModule ω f := by
  rw [normeModule, normeSup_eq_enorm]

theorem normeHolder_eq_normeModule (α : ℝ≥0) (f : X → E) :
    normeHolder α f = normeModule (fun s => s ^ (α : ℝ)) f :=
  rfl

lemma normeModule_eq_zero_iff {f : X → E} : normeModule ω f = 0 ↔ f = 0 := by
  refine ⟨fun h => normeSup_eq_zero_iff.1 (add_eq_zero.1 h).1, ?_⟩
  rintro rfl
  rw [normeModule, normeSup_eq_zero_iff.2 rfl, seminormeModule_zero, add_zero]

lemma normeModule_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (f : X → E) :
    normeModule ω (c • f) = ‖c‖ₑ * normeModule ω f := by
  rw [normeModule, normeModule, normeSup_smul, seminormeModule_smul, mul_add]

lemma normeModule_add_le (f g : X → E) :
    normeModule ω (f + g) ≤ normeModule ω f + normeModule ω g := by
  rw [normeModule, normeModule, normeModule, add_add_add_comm]
  exact add_le_add (normeSup_add_le f g) (seminormeModule_add_le f g)

/-- L'espace `C^ω_b(X,E) := {f ∈ C⁰_b(X,E) | |f|_ω < ∞}` de l'exemple `ex:Holder_Banach`,
sous-espace vectoriel de `C⁰_b(X,E)` (`X →ᵇ E`). Ses éléments sont exactement les `f ∈ C⁰_b`
telles que `‖f‖_ω < ∞` (`mem_espaceModule_iff`). -/
def espaceModule (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 E] (ω : ℝ≥0 → ℝ≥0) :
    Submodule 𝕜 (X →ᵇ E) where
  carrier := {f | seminormeModule ω f < ∞}
  zero_mem' := by
    change seminormeModule ω (0 : X → E) < ∞
    rw [seminormeModule_zero]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro f g hf hg
    change seminormeModule ω (⇑f + ⇑g) < ∞
    exact (seminormeModule_add_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)
  smul_mem' := by
    intro c f hf
    change seminormeModule ω (c • ⇑f) < ∞
    rw [seminormeModule_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hf

theorem mem_espaceModule_iff {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] {f : X →ᵇ E} :
    f ∈ espaceModule 𝕜 ω ↔ normeModule ω f < ∞ := by
  rw [normeModule_coe, ENNReal.add_lt_top, and_iff_right enorm_lt_top]
  rfl

/-- **Ex. `ex:Holder_Banach` (Complétude des espaces de Lipschitz et Hölder), norme.**
Soient `(X,d)` un espace métrique, `E` un evn et `ω : ℝ₊ → ℝ₊` un module de continuité
strictement positif hors de `0`. Alors `‖·‖_ω = ‖·‖_∞ + |·|_ω ∈ [0, ∞]` satisfait les axiomes
de norme (`def:norme`) : séparation, homogénéité, inégalité triangulaire, pour toutes fonctions
`f, g : X → E` ; c'est donc une norme sur `C^ω_b(X,E)`, où elle est finie (cf.
`ex_Holder_Banach_norme_toReal` pour la norme réelle). -/
theorem ex_Holder_Banach_norme {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    (_hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (_hω : ∀ s, 0 < s → 0 < ω s) :
    (∀ f : X → E, normeModule ω f = 0 ↔ f = 0) ∧
    (∀ (c : 𝕜) (f : X → E), normeModule ω (c • f) = ‖c‖ₑ * normeModule ω f) ∧
    (∀ f g : X → E, normeModule ω (f + g) ≤ normeModule ω f + normeModule ω g) :=
  ⟨fun _ => normeModule_eq_zero_iff, normeModule_smul, normeModule_add_le⟩

/-- **Ex. `ex:Holder_Banach`, norme réelle.** Sur `C^ω_b(X,E)`, la norme réelle (finie)
`‖f‖_ω = ‖f‖_∞ + |f|_ω` satisfait les axiomes de norme du cours (`def:norme`). -/
theorem ex_Holder_Banach_norme_toReal {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    (_hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (_hω : ∀ s, 0 < s → 0 < ω s) :
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), 0 ≤ (normeModule ω f).toReal) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), f ≠ 0 → 0 < (normeModule ω f).toReal) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), ∀ c : 𝕜,
      (normeModule ω ⇑(c • f)).toReal = ‖c‖ * (normeModule ω f).toReal) ∧
    (∀ f ∈ espaceModule 𝕜 ω (X := X) (E := E), ∀ g ∈ espaceModule 𝕜 ω (X := X) (E := E),
      (normeModule ω ⇑(f + g)).toReal ≤
        (normeModule ω f).toReal + (normeModule ω g).toReal) :=
  axiomesNorme_toReal (fun f : X →ᵇ E => normeModule ω f) _
    (fun _ hf => mem_espaceModule_iff.1 hf)
    (fun _ => normeModule_eq_zero_iff.trans
      ⟨fun h => DFunLike.coe_injective h, fun h => by rw [h]; rfl⟩)
    (fun c f => normeModule_smul c f) (fun f g => normeModule_add_le f g)

/-- **Ex. `ex:Holder_Banach` (Complétude des espaces de Lipschitz et Hölder), complétude.**
Soient `(X,d)` un espace métrique, `E` un Banach et `ω : ℝ₊ → ℝ₊` un module de continuité
strictement positif hors de `0`. Alors `C^ω_b(X,E)` est complet pour la norme
`‖·‖_ω = ‖·‖_∞ + |·|_ω` : toute suite de `C^ω_b(X,E)` de Cauchy pour `‖·‖_ω` converge pour
`‖·‖_ω` vers un élément de `C^ω_b(X,E)` (critère énoncé dans `[0, ∞]`). -/
theorem ex_Holder_Banach {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (_hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (hω : ∀ s, 0 < s → 0 < ω s)
    (f : ℕ → X →ᵇ E) (hf : ∀ n, f n ∈ espaceModule 𝕜 ω)
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, normeModule ω ⇑(f p - f q) ≤ ε) :
    ∃ g ∈ espaceModule 𝕜 ω, Tendsto (fun n => normeModule ω ⇑(f n - g : X →ᵇ E)) atTop (𝓝 0) := by
  -- La suite est de Cauchy pour la norme uniforme, donc converge vers `g ∈ C⁰_b(X,E)`.
  have hcauchy : CauchySeq f := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC (ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    have h1 : edist (f p) (f q) ≤ ENNReal.ofReal (ε / 2) := by
      rw [edist_eq_enorm_sub, ← normeSup_eq_enorm]
      exact le_self_add.trans (hN p hp q hq)
    exact ((edist_le_ofReal (half_pos hε).le).1 h1).trans_lt (half_lt_self hε)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hgx : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (g x)) := fun x =>
    ((continuous_eval_const x).tendsto g).comp hg
  -- Contrôle de `|f_n - g|_ω` par passage à la limite.
  have hkey : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, seminormeModule ω ⇑(f n - g) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn => (seminormeModule_le_iff' hω).2 fun x y hxy => ?_⟩
    have hlim : Tendsto (fun m => ‖(f n - f m) x - (f n - f m) y‖ₑ) atTop
        (𝓝 ‖(f n - g) x - (f n - g) y‖ₑ) := by
      simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
      exact (((tendsto_const_nhds.sub (hgx x)).sub (tendsto_const_nhds.sub (hgx y)))).enorm
    have hbound : ∀ m ≥ N, ‖(f n - f m) x - (f n - f m) y‖ₑ ≤ ε * ω (nndist x y) :=
      fun m hm => (seminormeModule_le_iff' hω).1 (le_add_self.trans (hN n hn m hm)) x y hxy
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, hbound⟩)
  obtain ⟨N₁, hN₁⟩ := hkey 1 one_pos
  have hgmem : g ∈ espaceModule 𝕜 ω := by
    change seminormeModule ω ⇑g < ∞
    have hg' : ⇑g = ⇑(f N₁) - ⇑(f N₁ - g) := by
      rw [BoundedContinuousFunction.coe_sub, sub_sub_cancel]
    rw [hg']
    exact (seminormeModule_sub_le _ _).trans_lt (ENNReal.add_lt_top.2
      ⟨hf N₁, (hN₁ N₁ le_rfl).trans_lt ENNReal.one_lt_top⟩)
  refine ⟨g, hgmem, ?_⟩
  have h1 : Tendsto (fun n => ‖f n - g‖ₑ) atTop (𝓝 0) := by
    simpa using (hg.sub_const g).enorm
  have h2 : Tendsto (fun n => seminormeModule ω ⇑(f n - g : X →ᵇ E)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero.2 hkey
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr fun n => (normeModule_coe _).symm

/-- **Ex. `ex:Holder_Banach`, espaces de Hölder et de Lipschitz.** Cas particulier
`ω(s) := s^α` : pour `0 < α ≤ 1`, l'espace de Hölder `C^α_b(X,E)` (`α < 1`), resp. l'espace
`Lip_b(X,E)` (`α = 1`), est complet pour la norme `‖·‖_∞ + |·|_{C^α}`. -/
theorem ex_Holder_Banach_holder {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    {α : ℝ} (hα : 0 < α) (_hα1 : α ≤ 1) (f : ℕ → X →ᵇ E)
    (hf : ∀ n, f n ∈ espaceModule 𝕜 (fun s => s ^ α))
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      normeModule (fun s => s ^ α) ⇑(f p - f q) ≤ ε) :
    ∃ g ∈ espaceModule 𝕜 (fun s => s ^ α),
      Tendsto (fun n => normeModule (fun s => s ^ α) ⇑(f n - g : X →ᵇ E)) atTop (𝓝 0) := by
  refine ex_Holder_Banach ?_ (fun s hs => NNReal.rpow_pos hs) f hf hC
  have := (NNReal.continuous_rpow_const hα.le).tendsto 0
  rwa [NNReal.zero_rpow hα.ne'] at this

end Module

/-- **Ex. `ex:LpBanach`.** Soit `(X,μ)` un espace mesuré. Alors `L^p(X,μ)` est un Banach, pour
tout `p ∈ [1, ∞]`.
Preuve (via Mathlib, proche du cours) : instance de Mathlib (aussi pour `p = ∞`) : une suite de
Cauchy à incréments sommables vérifie `∑ |f_{n+1} - f_n| ∈ L^p` (Minkowski, Fatou), donc converge
p.p., puis dans `L^p` (Fatou). -/
theorem ex_LpBanach {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (Lp 𝕜 p μ) :=
  inferInstance

end M1Analyse
