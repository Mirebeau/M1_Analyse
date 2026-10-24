/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.Sort
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Perm.Sign
import M1Analyse.Outils.Schwarz

/-!
# §1.3 Espaces vectoriels normés (`subsec:evn`)

Source : `Include/TopologieGenerale.tex`, sous-section `subsec:evn` (y compris la
sous-sous-section « Exemples d'espaces fonctionnels »).

Les objets du cours sont ceux de Mathlib : evn = `NormedAddCommGroup` + `NormedSpace 𝕜`,
semi-norme = `Seminorm 𝕜 E`, `L(E,F)` = `E →L[𝕜] F` (norme d'opérateur `‖u‖`),
dual = `StrongDual 𝕜 E`, `C⁰_b(X,𝕂)` = `X →ᵇ 𝕜`, Hölder/Lipschitz = `HolderWith`, `MemHolder`,
`LipschitzWith`, `L^p(X,μ)` = `MeasureTheory.Lp 𝕜 p μ`.

Les formules « sup » du cours pour la norme uniforme, la semi-norme de Hölder et la constante de
Lipschitz ne figurent pas telles quelles dans Mathlib (qui définit `eHolderNorm` comme un inf de
constantes) : on les introduit à valeurs dans `[0, ∞]` (`normeSup`, `seminormeModule`,
`seminormeHolder`, `constLip`, `normeHolder`), ce qui les rend définies pour toute fonction, et
on montre qu'elles coïncident avec les objets de Mathlib (`eHolderNorm`, `HolderWith`,
`LipschitzWith`, norme de `X →ᵇ E`).

Les dérivées partielles `∂_α f` (`deriveePartielle`), pour un multi-indice `α ∈ ℕ^d` et
`f : ℝ^d → F` (`ℝ^d = EuclideanSpace ℝ (Fin d)`), sont définies à partir de la différentielle
itérée `iteratedFDeriv` de Mathlib ; on utilise le lemme de Schwarz itéré
(`iteratedFDeriv_comp_perm_of_contDiff`, absent de Mathlib pour les fonctions `C^n`), démontré
dans le fichier utilitaire `M1Analyse.Outils.Schwarz`.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace M1Analyse

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Normes et semi-normes -/

/-- **Déf. `def:norme` (Norme), sens direct.** La norme d'un `𝕜`-evn de Mathlib est à valeurs
dans `ℝ₊` et satisfait la séparation, l'homogénéité (`|λ|` s'écrit `‖λ‖`) et l'inégalité
triangulaire. -/
theorem def_norme {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (∀ x : E, 0 ≤ ‖x‖) ∧ (∀ x : E, x ≠ 0 → 0 < ‖x‖) ∧
    (∀ (x : E) (c : 𝕜), ‖c • x‖ = ‖c‖ * ‖x‖) ∧ (∀ x y : E, ‖x + y‖ ≤ ‖x‖ + ‖y‖) :=
  ⟨norm_nonneg, fun _ => norm_pos_iff.mpr, fun x c => norm_smul c x, norm_add_le⟩

/-- **Déf. `def:norme` (Norme), sens réciproque.** Une application `‖·‖ : E → ℝ₊` satisfaisant
les trois axiomes du cours fournit les données `NormedSpace.Core` de Mathlib, à partir
desquelles `NormedAddCommGroup.ofCore` et `NormedSpace.ofCore` construisent un evn. -/
theorem def_norme_of_axioms {E : Type*} [AddCommGroup E] [Module 𝕜 E] [Norm E]
    (h₀ : ∀ x : E, 0 ≤ ‖x‖) (hsep : ∀ x : E, x ≠ 0 → 0 < ‖x‖)
    (hhom : ∀ (x : E) (c : 𝕜), ‖c • x‖ = ‖c‖ * ‖x‖)
    (htri : ∀ x y : E, ‖x + y‖ ≤ ‖x‖ + ‖y‖) : NormedSpace.Core 𝕜 E where
  norm_nonneg := h₀
  norm_smul c x := hhom x c
  norm_triangle := htri
  norm_eq_zero_iff x := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_contra hx
      exact (hsep x hx).ne' h
    · simpa [h] using hhom 0 0

/-- **Déf. `def:norme` (Semi-norme).** Les semi-normes de Mathlib (`Seminorm 𝕜 E`) sont
exactement les applications `E → ℝ₊` homogènes et sous-additives. -/
theorem def_norme_seminorme {E : Type*} [AddCommGroup E] [Module 𝕜 E] (N : E → ℝ) :
    (∃ p : Seminorm 𝕜 E, ⇑p = N) ↔
    ((∀ x, 0 ≤ N x) ∧ (∀ (x : E) (c : 𝕜), N (c • x) = ‖c‖ * N x) ∧
      (∀ x y, N (x + y) ≤ N x + N y)) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨apply_nonneg p, fun x c => map_smul_eq_mul p c x, map_add_le_add p⟩
  · rintro ⟨-, hhom, htri⟩
    exact ⟨Seminorm.of N htri (fun c x => hhom x c), rfl⟩

/-- **Déf. `def:norme`, distance associée.** Un evn est muni de la distance
`d(x,y) := ‖x - y‖`. -/
theorem def_norme_dist {E : Type*} [NormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖ :=
  dist_eq_norm x y

/-! ### Norme d'opérateur -/

section Operateur

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Déf. `def:normeOperateur` (Evn des applications linéaires continues).** La norme
d'opérateur de `u ∈ L(E,F)` (`E →L[𝕜] F` dans Mathlib) est
`|||u||| = sup {‖u x‖_F | ‖x‖_E ≤ 1}`. -/
theorem def_normeOperateur (u : E →L[𝕜] F) :
    ‖u‖ = sSup ((fun x => ‖u x‖) '' {x : E | ‖x‖ ≤ 1}) := by
  rw [← u.sSup_unitClosedBall_eq_norm]
  congr 2
  ext x
  simp

/-- **Déf. `def:normeOperateur`, constante de Lipschitz.** La norme d'opérateur `|||u|||` est
aussi la (plus petite) constante de Lipschitz de `u`. -/
theorem def_normeOperateur_lipschitz (u : E →L[𝕜] F) :
    IsLeast {K : ℝ≥0 | LipschitzWith K u} ‖u‖₊ := by
  refine ⟨u.lipschitzWith, fun K hK => ?_⟩
  refine u.opNNNorm_le_bound K fun x => ?_
  simpa using hK.nndist_le x 0

/-- **Déf. `def:normeOperateur`, dual.** Le dual `E* := L(E,𝕜)` (`StrongDual 𝕜 E` dans Mathlib)
est l'evn des formes linéaires continues sur `E`. -/
theorem def_normeOperateur_dual : StrongDual 𝕜 E = (E →L[𝕜] 𝕜) :=
  rfl

end Operateur

/-! ### Fonctions continues bornées, Hölderiennes, Lipschitziennes -/

section Holder

/-- **Déf. `def:normeHolder`, espace `C⁰_b(X,𝕂)`.** La norme de `X →ᵇ 𝕜` (fonctions continues
bornées) est la norme uniforme `‖f‖_∞ = sup_{x ∈ X} |f(x)|`. -/
theorem def_normeHolder_infty {X : Type*} [TopologicalSpace X] (f : X →ᵇ 𝕜) :
    ‖f‖ = ⨆ x, ‖f x‖ :=
  f.norm_eq_iSup_norm

/-- Norme uniforme du cours, `‖f‖_∞ := sup_{x ∈ X} ‖f(x)‖`, à valeurs dans `[0, ∞]`
(`def:normeHolder`) : elle est définie pour toute fonction, et finie exactement pour les
fonctions bornées (`normeSup_lt_top_iff`).
Pont Mathlib : pour `f ∈ C⁰_b(X,E)` (`X →ᵇ E`), `normeSup f = ‖f‖ₑ`, i.e. c'est la norme de
`BoundedContinuousFunction` (`normeSup_eq_enorm`, `toReal_normeSup`). -/
noncomputable def normeSup {X E : Type*} [NormedAddCommGroup E] (f : X → E) : ℝ≥0∞ :=
  ⨆ x, ‖f x‖ₑ

section NormeSup

variable {X E : Type*} [NormedAddCommGroup E]

lemma enorm_le_normeSup (f : X → E) (x : X) : ‖f x‖ₑ ≤ normeSup f :=
  le_iSup (fun x => ‖f x‖ₑ) x

lemma normeSup_add_le (f g : X → E) : normeSup (f + g) ≤ normeSup f + normeSup g :=
  iSup_le fun x => (enorm_add_le _ _).trans
    (add_le_add (enorm_le_normeSup f x) (enorm_le_normeSup g x))

lemma normeSup_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : X → E) :
    normeSup (c • f) = ‖c‖ₑ * normeSup f := by
  simp only [normeSup, Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]

lemma normeSup_eq_zero_iff {f : X → E} : normeSup f = 0 ↔ f = 0 := by
  simp only [normeSup, ENNReal.iSup_eq_zero, enorm_eq_zero, funext_iff, Pi.zero_apply]

/-- `‖f‖_∞ < ∞` si et seulement si `f` est bornée. -/
theorem normeSup_lt_top_iff {f : X → E} :
    normeSup f < ∞ ↔ BddAbove (range fun x => ‖f x‖) := by
  constructor
  · intro h
    refine ⟨(normeSup f).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    have := (ENNReal.toReal_le_toReal enorm_ne_top h.ne).2 (enorm_le_normeSup f x)
    rwa [toReal_enorm] at this
  · rintro ⟨C, hC⟩
    refine lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := C))
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC ⟨x, rfl⟩)

/-- Pont Mathlib : sur `C⁰_b(X,E)`, `‖f‖_∞` est la norme de `X →ᵇ E`. -/
theorem normeSup_eq_enorm [TopologicalSpace X] (f : X →ᵇ E) : normeSup f = ‖f‖ₑ := by
  have hb : BddAbove (range fun x => ‖f x‖₊) := by
    refine ⟨‖f‖₊, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact f.norm_coe_le_norm x
  rw [enorm_eq_nnnorm, f.nnnorm_eq_iSup_nnnorm, ENNReal.coe_iSup hb]
  rfl

theorem toReal_normeSup [TopologicalSpace X] (f : X →ᵇ E) : (normeSup f).toReal = ‖f‖ := by
  rw [normeSup_eq_enorm, toReal_enorm]

end NormeSup

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]

/-- Semi-norme `|f|_ω := sup_{x ≠ y} ‖f(x) - f(y)‖ / ω(d(x,y)) ∈ [0, ∞]` associée à un module de
continuité `ω : ℝ₊ → ℝ₊` (exemple `ex:Holder_Banach`) ; le cas `ω(s) = s^α` est la
semi-norme de Hölder (`seminormeHolder`), le cas `ω = id` la constante de Lipschitz
(`constLip`) de `def:normeHolder`. -/
noncomputable def seminormeModule (ω : ℝ≥0 → ℝ≥0) (f : X → E) : ℝ≥0∞ :=
  ⨆ (x : X) (y : X) (_ : x ≠ y), ‖f x - f y‖ₑ / (ω (nndist x y) : ℝ≥0∞)

section SeminormeModule

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

lemma seminormeModule_zero : seminormeModule ω (0 : X → E) = 0 :=
  le_antisymm (seminormeModule_le_iff.2 fun _ _ _ => by simp) bot_le

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

lemma seminormeModule_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : X → E) :
    seminormeModule ω (c • f) = ‖c‖ₑ * seminormeModule ω f := by
  simp only [seminormeModule, Pi.smul_apply, ← smul_sub, enorm_smul, ENNReal.mul_iSup,
    mul_div_assoc]

end SeminormeModule

/-- Semi-norme de Hölder du cours, `|f|_{C^α} := sup_{x ≠ y} ‖f(x) - f(y)‖ / d(x,y)^α ∈ [0, ∞]`
(`def:normeHolder`), i.e. `|f|_ω` pour `ω(s) = s^α`.
Pont Mathlib : `seminormeHolder α f = eHolderNorm α f` (`seminormeHolder_eq_eHolderNorm`) ;
`|f|_{C^α} ≤ C ↔ HolderWith C α f` (`seminormeHolder_le_iff_holderWith`) ;
`|f|_{C^α} < ∞ ↔ MemHolder α f` (`seminormeHolder_lt_top_iff`). -/
noncomputable def seminormeHolder (α : ℝ≥0) (f : X → E) : ℝ≥0∞ :=
  seminormeModule (fun s => s ^ (α : ℝ)) f

/-- Constante de Lipschitz du cours, `Lip(f) := sup_{x ≠ y} ‖f(x) - f(y)‖ / d(x,y) ∈ [0, ∞]`
(`def:normeHolder`), i.e. `|f|_ω` pour `ω = id` ; c'est `|f|_{C^1}`
(`constLip_eq_seminormeHolder_one`).
Pont Mathlib : `Lip(f) ≤ K ↔ LipschitzWith K f` (`constLip_le_iff_lipschitzWith`) ;
`Lip(f) < ∞ ↔ ∃ K, LipschitzWith K f` (`constLip_lt_top_iff`). -/
noncomputable def constLip (f : X → E) : ℝ≥0∞ :=
  seminormeModule id f

/-- Norme de Hölder du cours, `‖f‖_{C^α} := ‖f‖_∞ + |f|_{C^α} ∈ [0, ∞]` (`def:normeHolder`).
Pour `α = 1`, c'est la norme `‖f‖_∞ + Lip(f)` des fonctions Lipschitziennes bornées.
Pont Mathlib : `‖f‖_{C^α} < ∞ ↔ (f bornée ∧ MemHolder α f)` (`normeHolder_lt_top_iff`). -/
noncomputable def normeHolder (α : ℝ≥0) (f : X → E) : ℝ≥0∞ :=
  normeSup f + seminormeHolder α f

variable {α : ℝ≥0}

lemma constLip_eq_seminormeHolder_one (f : X → E) : constLip f = seminormeHolder 1 f := by
  simp only [constLip, seminormeHolder, NNReal.coe_one, NNReal.rpow_one]
  rfl

/-- `|f|_{C^α} ≤ C` si et seulement si `‖f(x) - f(y)‖ ≤ C d(x,y)^α` pour tous `x, y`. -/
theorem seminormeHolder_le_iff {f : X → E} {C : ℝ≥0∞} :
    seminormeHolder α f ≤ C ↔ ∀ x y, ‖f x - f y‖ₑ ≤ C * edist x y ^ (α : ℝ) := by
  have hc : ∀ x y : X, ((nndist x y ^ (α : ℝ) : ℝ≥0) : ℝ≥0∞) = edist x y ^ (α : ℝ) :=
    fun x y => by rw [edist_nndist, ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg]
  rw [seminormeHolder, seminormeModule_le_iff' fun s hs => NNReal.rpow_pos hs]
  refine ⟨fun h x y => ?_, fun h x y _ => ?_⟩
  · rcases eq_or_ne x y with rfl | hxy
    · simp
    · rw [← hc]; exact h x y hxy
  · rw [hc]; exact h x y

/-- Pont Mathlib : `|f|_{C^α} ≤ C ↔ HolderWith C α f`. -/
theorem seminormeHolder_le_iff_holderWith {f : X → E} (C : ℝ≥0) :
    seminormeHolder α f ≤ C ↔ HolderWith C α f := by
  rw [seminormeHolder_le_iff]
  simp only [HolderWith, edist_eq_enorm_sub]

/-- Pont Mathlib : la semi-norme de Hölder du cours est `eHolderNorm` de Mathlib (défini comme
l'inf des constantes de Hölder). -/
theorem seminormeHolder_eq_eHolderNorm (f : X → E) :
    seminormeHolder α f = eHolderNorm α f := by
  refine le_antisymm (le_iInf₂ fun C hC => (seminormeHolder_le_iff_holderWith C).2 hC) ?_
  rcases eq_top_or_lt_top (seminormeHolder α f) with h | h
  · rw [h]; exact le_top
  · have hC := (seminormeHolder_le_iff_holderWith (f := f) (seminormeHolder α f).toNNReal).1
      (ENNReal.coe_toNNReal h.ne).ge
    exact hC.eHolderNorm_le.trans (ENNReal.coe_toNNReal h.ne).le

/-- Pont Mathlib : `|f|_{C^α} < ∞ ↔ MemHolder α f`. -/
theorem seminormeHolder_lt_top_iff {f : X → E} : seminormeHolder α f < ∞ ↔ MemHolder α f := by
  rw [seminormeHolder_eq_eHolderNorm, eHolderNorm_lt_top]

/-- Pont Mathlib : `Lip(f) ≤ K ↔ LipschitzWith K f`. -/
theorem constLip_le_iff_lipschitzWith {f : X → E} (K : ℝ≥0) :
    constLip f ≤ K ↔ LipschitzWith K f := by
  rw [constLip_eq_seminormeHolder_one, seminormeHolder_le_iff_holderWith, holderWith_one]

/-- Pont Mathlib : `Lip(f) < ∞ ↔ ∃ K, LipschitzWith K f`. -/
theorem constLip_lt_top_iff {f : X → E} : constLip f < ∞ ↔ ∃ K, LipschitzWith K f := by
  refine ⟨fun h => ⟨(constLip f).toNNReal, ?_⟩, fun ⟨K, hK⟩ => ?_⟩
  · exact (constLip_le_iff_lipschitzWith _).1 (ENNReal.coe_toNNReal h.ne).ge
  · exact ((constLip_le_iff_lipschitzWith K).2 hK).trans_lt ENNReal.coe_lt_top

/-- Pont Mathlib : `‖f‖_{C^α} < ∞` si et seulement si `f` est bornée et `α`-Hölderienne. -/
theorem normeHolder_lt_top_iff {f : X → E} :
    normeHolder α f < ∞ ↔ BddAbove (range fun x => ‖f x‖) ∧ MemHolder α f := by
  rw [normeHolder, ENNReal.add_lt_top, normeSup_lt_top_iff, seminormeHolder_lt_top_iff]

lemma normeHolder_eq_zero_iff {f : X → E} : normeHolder α f = 0 ↔ f = 0 := by
  refine ⟨fun h => normeSup_eq_zero_iff.1 (add_eq_zero.1 h).1, ?_⟩
  rintro rfl
  rw [normeHolder, normeSup_eq_zero_iff.2 rfl, seminormeHolder, seminormeModule_zero, add_zero]

lemma normeHolder_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : X → E) :
    normeHolder α (c • f) = ‖c‖ₑ * normeHolder α f := by
  rw [normeHolder, normeHolder, seminormeHolder, seminormeHolder, normeSup_smul,
    seminormeModule_smul, mul_add]

lemma normeHolder_add_le (f g : X → E) :
    normeHolder α (f + g) ≤ normeHolder α f + normeHolder α g := by
  rw [normeHolder, normeHolder, normeHolder, add_add_add_comm]
  exact add_le_add (normeSup_add_le f g) (seminormeModule_add_le f g)

/-- L'espace `C^α_b(X,E)` (`def:normeHolder`) des fonctions `f : X → E` de norme
`‖f‖_{C^α} = ‖f‖_∞ + |f|_{C^α}` finie, vu comme sous-espace vectoriel de `X → E`. Pour `α = 1`,
ce sont les fonctions Lipschitziennes bornées.
Pont Mathlib : `f ∈ C^α_b(X,E) ↔ (f bornée ∧ MemHolder α f)` (`mem_espaceHolder_iff`).
L'exposant est supposé `α > 0` (hypothèse `hα`), conformément à la décision de l'auteur : `C^0_b`
ne peut pas être formé (pour `α = 0`, on obtiendrait toutes les fonctions bornées, sans
intérêt ici).
Remarques : (1) le cours prend `𝕂 = ℝ, ℂ` comme espace d'arrivée et `α ∈ ]0,1[` ; on autorise un
evn `E` quelconque et tout `α > 0`. (2) Le cours se place dans `C⁰_b(X,𝕂)` ; comme `α > 0`, les
éléments de `C^α_b(X,E)` sont automatiquement continus (`continuous_of_mem_espaceHolder`). -/
@[nolint unusedArguments]
def espaceHolder (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 E] (α : ℝ≥0) (_hα : 0 < α) :
    Submodule 𝕜 (X → E) where
  carrier := {f | normeHolder α f < ∞}
  zero_mem' := by
    change normeHolder α (0 : X → E) < ∞
    rw [normeHolder_eq_zero_iff.2 rfl]
    exact ENNReal.zero_lt_top
  add_mem' {f g} hf hg :=
    (normeHolder_add_le f g).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)
  smul_mem' c f hf := by
    change normeHolder α (c • f) < ∞
    rw [normeHolder_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hf

/-- Pont Mathlib : `f ∈ C^α_b(X,E)` si et seulement si `f` est bornée et `MemHolder α f`. -/
theorem mem_espaceHolder_iff [NormedSpace 𝕜 E] (hα : 0 < α) {f : X → E} :
    f ∈ espaceHolder 𝕜 α hα ↔ BddAbove (range fun x => ‖f x‖) ∧ MemHolder α f :=
  normeHolder_lt_top_iff

/-- Les éléments de `C^α_b(X,E)` (`α > 0`) sont continus : `C^α_b(X,E)` est bien inclus dans
`C⁰_b(X,E)`, comme dans le cours (`def:normeHolder`). -/
theorem continuous_of_mem_espaceHolder [NormedSpace 𝕜 E] (hα : 0 < α) {f : X → E}
    (hf : f ∈ espaceHolder 𝕜 α hα) : Continuous f := by
  obtain ⟨C, hC⟩ := ((mem_espaceHolder_iff hα).1 hf).2
  exact hC.continuous hα

/-- **Déf. `def:normeHolder` (semi-norme de Hölder).** La semi-norme du cours
`|f|_{C^α} = sup_{x ≠ y} |f(x)-f(y)|/d(x,y)^α ∈ [0, ∞]` est la plus petite constante
`C ∈ [0, ∞]` telle que `|f(x) - f(y)| ≤ C d(x,y)^α` pour tous `x, y`, et coïncide avec
`eHolderNorm α f` de Mathlib ; pour `f` `α`-Hölderienne, elle est finie et vaut
`nnHolderNorm α f`. -/
theorem def_normeHolder_seminorme (α : ℝ≥0) (f : X → E) :
    IsLeast {C : ℝ≥0∞ | ∀ x y, ‖f x - f y‖ₑ ≤ C * edist x y ^ (α : ℝ)} (seminormeHolder α f) ∧
    seminormeHolder α f = eHolderNorm α f ∧
    (MemHolder α f → seminormeHolder α f = nnHolderNorm α f) := by
  refine ⟨⟨seminormeHolder_le_iff.1 le_rfl, fun C hC => seminormeHolder_le_iff.2 hC⟩,
    seminormeHolder_eq_eHolderNorm f, fun hf => ?_⟩
  rw [seminormeHolder_eq_eHolderNorm, hf.coe_nnHolderNorm_eq_eHolderNorm]

/-- **Déf. `def:normeHolder` (constante de Lipschitz).** `Lip(f)` est la semi-norme de Hölder
d'exposant `1`, les fonctions Lipschitziennes sont les fonctions `1`-Hölderiennes, `Lip(f)` est
la plus petite constante `K ∈ [0, ∞]` telle que `d(f(x), f(y)) ≤ K d(x,y)`, et pour `f`
Lipschitzienne, `Lip(f)` est finie et est la plus petite constante de Lipschitz de `f`. -/
theorem def_normeHolder_lip (f : X → E) :
    constLip f = seminormeHolder 1 f ∧ (MemHolder 1 f ↔ ∃ K, LipschitzWith K f) ∧
    IsLeast {K : ℝ≥0∞ | ∀ x y, edist (f x) (f y) ≤ K * edist x y} (constLip f) ∧
    ((∃ K, LipschitzWith K f) →
      constLip f < ∞ ∧ IsLeast {K : ℝ≥0 | LipschitzWith K f} (constLip f).toNNReal) := by
  have h1 := constLip_eq_seminormeHolder_one f
  have hle : ∀ C : ℝ≥0∞, constLip f ≤ C ↔ ∀ x y, edist (f x) (f y) ≤ C * edist x y := by
    intro C
    rw [h1, seminormeHolder_le_iff]
    simp [edist_eq_enorm_sub]
  refine ⟨h1, by simp [MemHolder, holderWith_one], ⟨(hle _).1 le_rfl, fun C hC => (hle C).2 hC⟩,
    fun hK => ?_⟩
  have hfin := constLip_lt_top_iff.2 hK
  refine ⟨hfin, (constLip_le_iff_lipschitzWith _).1 (ENNReal.coe_toNNReal hfin.ne).ge,
    fun K hK' => ?_⟩
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin.ne]
  exact (constLip_le_iff_lipschitzWith K).2 hK'

/-- Une fonction `N : V → [0, ∞]` satisfaisant les axiomes de norme (séparation, homogénéité,
inégalité triangulaire) induit, sur un sous-espace où elle est finie, une norme réelle
`(N ·).toReal` au sens de `def:norme`. -/
theorem axiomesNorme_toReal {V : Type*} [AddCommGroup V] [Module 𝕜 V] (N : V → ℝ≥0∞)
    (S : Submodule 𝕜 V) (hS : ∀ f ∈ S, N f < ∞) (h0 : ∀ f, N f = 0 ↔ f = 0)
    (hsmul : ∀ (c : 𝕜) f, N (c • f) = ‖c‖ₑ * N f) (hadd : ∀ f g, N (f + g) ≤ N f + N g) :
    (∀ f ∈ S, 0 ≤ (N f).toReal) ∧ (∀ f ∈ S, f ≠ 0 → 0 < (N f).toReal) ∧
    (∀ f ∈ S, ∀ c : 𝕜, (N (c • f)).toReal = ‖c‖ * (N f).toReal) ∧
    (∀ f ∈ S, ∀ g ∈ S, (N (f + g)).toReal ≤ (N f).toReal + (N g).toReal) := by
  refine ⟨fun _ _ => ENNReal.toReal_nonneg,
    fun f hf hf0 => ENNReal.toReal_pos (mt (h0 f).1 hf0) (hS f hf).ne,
    fun f _ c => by rw [hsmul, ENNReal.toReal_mul, toReal_enorm], fun f hf g hg => ?_⟩
  rw [← ENNReal.toReal_add (hS f hf).ne (hS g hg).ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(hS f hf).ne, (hS g hg).ne⟩) (hadd f g)

/-- **Déf. `def:normeHolder` (evn `C^α_b(X,𝕂)`).** `‖f‖_{C^α} = ‖f‖_∞ + |f|_{C^α} ∈ [0, ∞]`
satisfait, pour toutes fonctions `f, g : X → E` et sans autre hypothèse, les axiomes de norme du
cours (`def:norme`) : séparation, homogénéité, inégalité triangulaire. Elle est donc une norme
sur `C^α_b(X,E)`, l'ensemble des fonctions pour lesquelles elle est finie (`espaceHolder`,
cf. `def_normeHolder_espace`). Pour `α = 1`, c'est l'evn des fonctions Lipschitziennes
bornées. -/
theorem def_normeHolder [NormedSpace 𝕜 E] (α : ℝ≥0) :
    (∀ f : X → E, normeHolder α f = 0 ↔ f = 0) ∧
    (∀ (c : 𝕜) (f : X → E), normeHolder α (c • f) = ‖c‖ₑ * normeHolder α f) ∧
    (∀ f g : X → E, normeHolder α (f + g) ≤ normeHolder α f + normeHolder α g) :=
  ⟨fun _ => normeHolder_eq_zero_iff, normeHolder_smul, normeHolder_add_le⟩

/-- **Déf. `def:normeHolder` (evn `C^α_b(X,𝕂)`), version réelle.** Sur `C^α_b(X,E)`, la norme
réelle `‖f‖_{C^α}` (finie) satisfait les axiomes de norme du cours (`def:norme`). -/
theorem def_normeHolder_espace [NormedSpace 𝕜 E] (α : ℝ≥0) (hα : 0 < α) :
    (∀ f ∈ espaceHolder 𝕜 α hα (X := X) (E := E), 0 ≤ (normeHolder α f).toReal) ∧
    (∀ f ∈ espaceHolder 𝕜 α hα (X := X) (E := E), f ≠ 0 → 0 < (normeHolder α f).toReal) ∧
    (∀ f ∈ espaceHolder 𝕜 α hα (X := X) (E := E), ∀ c : 𝕜,
      (normeHolder α (c • f)).toReal = ‖c‖ * (normeHolder α f).toReal) ∧
    (∀ f ∈ espaceHolder 𝕜 α hα (X := X) (E := E), ∀ g ∈ espaceHolder 𝕜 α hα (X := X) (E := E),
      (normeHolder α (f + g)).toReal ≤ (normeHolder α f).toReal + (normeHolder α g).toReal) :=
  axiomesNorme_toReal _ _ (fun _ hf => hf) (fun _ => normeHolder_eq_zero_iff) normeHolder_smul
    normeHolder_add_le

end Holder

/-! ### Dérivées partielles et espaces `C^n_b(Ω)` -/

section Cnb

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Liste des directions de dérivation associée au multi-indice `α ∈ ℕ^d` : chaque
`i ∈ {0, …, d-1}` y figure `α_i` fois, dans l'ordre croissant. -/
def directions (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun i => List.replicate (α i) i

lemma length_directions (α : Fin d → ℕ) : (directions α).length = ∑ i, α i := by
  simp [directions, List.length_flatMap, Fin.sum_univ_def]

lemma count_directions (α : Fin d → ℕ) (i : Fin d) : (directions α).count i = α i := by
  rw [directions, List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate]

lemma sortedLE_directions (α : Fin d → ℕ) : (directions α).SortedLE := by
  rw [List.sortedLE_iff_pairwise, directions, List.pairwise_flatMap]
  refine ⟨fun i _ => List.pairwise_replicate_of_refl, ?_⟩
  refine (List.pairwise_lt_finRange d).imp fun {a b} hab x hx y hy => ?_
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  exact hab.le

/-- Dérivée partielle `∂_α f(x)` du cours (`def:normeCnb`), pour `f : ℝ^d → F`
(`ℝ^d = EuclideanSpace ℝ (Fin d)`) et un multi-indice `α ∈ ℕ^d` : la différentielle itérée
`D^{|α|₁} f(x)` (`iteratedFDeriv` de Mathlib) appliquée aux vecteurs de base `e_i`, chacun
répété `α_i` fois. Les fonctions sont définies sur `ℝ^d` tout entier.
Pont Mathlib : pour `Ω` ouvert et `x ∈ Ω`, c'est aussi la différentielle itérée relative à `Ω`
(`iteratedFDerivWithin`), cf. `deriveePartielle_eq_iteratedFDerivWithin` ; elle ne dépend donc
que des valeurs de `f` sur `Ω`. Pour `f` de classe `C^j`, une dérivée itérée `D^j f(x)` dans
des directions de base quelconques `e_{w_1}, …, e_{w_j}` est une dérivée partielle `∂_α f(x)`
(lemme de Schwarz, `iteratedFDeriv_eq_deriveePartielle_multiIndice`). -/
noncomputable def deriveePartielle (α : Fin d → ℕ) (f : EuclideanSpace ℝ (Fin d) → F)
    (x : EuclideanSpace ℝ (Fin d)) : F :=
  iteratedFDeriv ℝ (directions α).length f x
    (fun j => EuclideanSpace.single ((directions α).get j) (1 : ℝ))

/-- Pont Mathlib : sur un ouvert `Ω`, `∂_α f` coïncide avec la dérivée relative à `Ω`. -/
theorem deriveePartielle_eq_iteratedFDerivWithin {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (α : Fin d → ℕ) (f : EuclideanSpace ℝ (Fin d) → F)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    deriveePartielle α f x = iteratedFDerivWithin ℝ (directions α).length f Ω x
      (fun j => EuclideanSpace.single ((directions α).get j) (1 : ℝ)) := by
  rw [deriveePartielle, iteratedFDerivWithin_of_isOpen _ hΩ hx]

lemma deriveePartielle_zero (f : EuclideanSpace ℝ (Fin d) → F) (x : EuclideanSpace ℝ (Fin d)) :
    deriveePartielle 0 f x = f x := by
  have h : directions (0 : Fin d → ℕ) = [] := by simp [directions]
  unfold deriveePartielle
  generalize directions 0 = l at h ⊢
  subst h
  rfl

/-- Une dérivée partielle est contrôlée par la norme de la différentielle itérée. -/
theorem norm_deriveePartielle_le (α : Fin d → ℕ) (f : EuclideanSpace ℝ (Fin d) → F)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖deriveePartielle α f x‖ ≤ ‖iteratedFDeriv ℝ (directions α).length f x‖ := by
  refine ((iteratedFDeriv ℝ _ f x).le_opNorm _).trans ?_
  simp

/-- Multi-indice `α(w) ∈ ℕ^d` associé à un mot `w = (w_1, …, w_j)` : `α(w)_i` est le nombre
d'occurrences de `i` dans `w`. -/
def multiIndice {j : ℕ} (w : Fin j → Fin d) : Fin d → ℕ := fun i => (List.ofFn w).count i

lemma directions_multiIndice {j : ℕ} (w : Fin j → Fin d) :
    directions (multiIndice w) = List.ofFn (w ∘ Tuple.sort w) := by
  refine List.Perm.eq_of_sortedLE (sortedLE_directions _)
    (List.sortedLE_ofFn_iff.2 (Tuple.monotone_sort w)) ?_
  rw [List.perm_iff_count]
  intro i
  rw [count_directions, multiIndice, ((Tuple.sort w).ofFn_comp_perm w).count_eq]

lemma sum_multiIndice {j : ℕ} (w : Fin j → Fin d) : ∑ i, multiIndice w i = j := by
  rw [← length_directions, directions_multiIndice, List.length_ofFn]

lemma iteratedFDeriv_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ}
    (h : m = n) (f : E → F) (x : E) (u : Fin n → E) :
    iteratedFDeriv ℝ m f x (fun k => u (Fin.cast h k)) = iteratedFDeriv ℝ n f x u := by
  subst h
  rfl

/-- Pour `f` de classe `C^j`, la dérivée itérée `D^j f(x)(e_{w_1}, …, e_{w_j})` dans des
directions de base quelconques est la dérivée partielle `∂_{α(w)} f(x)`, où `α(w)` compte les
occurrences de chaque direction (lemme de Schwarz). -/
theorem iteratedFDeriv_eq_deriveePartielle_multiIndice {j : ℕ} {f : EuclideanSpace ℝ (Fin d) → F}
    (hf : ContDiff ℝ j f) (x : EuclideanSpace ℝ (Fin d)) (w : Fin j → Fin d) :
    iteratedFDeriv ℝ j f x (fun k => EuclideanSpace.single (w k) (1 : ℝ)) =
      deriveePartielle (multiIndice w) f x := by
  rw [deriveePartielle, directions_multiIndice]
  simp only [List.get_ofFn, Function.comp_apply]
  rw [iteratedFDeriv_cast (List.length_ofFn (f := w ∘ Tuple.sort w)) f x
    (fun k => EuclideanSpace.single (w (Tuple.sort w k)) (1 : ℝ))]
  exact (iteratedFDeriv_comp_perm_of_contDiff j hf x
    (fun k => EuclideanSpace.single (w k) (1 : ℝ)) (Tuple.sort w)).symm

/-- L'espace `C^n_b(Ω)` du cours (`def:normeCnb`) : fonctions `n` fois continûment
différentiables sur `Ω`, dont les dérivées partielles `∂_α f`, `|α|₁ ≤ n`, sont bornées sur `Ω`.
Les fonctions sont représentées par des fonctions sur `ℝ^d` tout entier, dont seules les
valeurs sur `Ω` interviennent (`deriveePartielle_eq_iteratedFDerivWithin`). -/
def espaceCnb (𝕜 : Type*) [RCLike 𝕜] (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω)
    (n : ℕ) : Submodule 𝕜 (EuclideanSpace ℝ (Fin d) → 𝕜) where
  carrier := {f | ContDiffOn ℝ n f Ω ∧
    ∀ α : Fin d → ℕ, ∑ i, α i ≤ n → BddAbove (range fun x : Ω => ‖deriveePartielle α f x‖)}
  zero_mem' := by
    refine ⟨contDiffOn_const, fun α _ => ⟨0, ?_⟩⟩
    rintro _ ⟨x, rfl⟩
    simp [deriveePartielle]
  add_mem' := by
    rintro f g ⟨hf, hbf⟩ ⟨hg, hbg⟩
    refine ⟨hf.add hg, fun α hα => ?_⟩
    obtain ⟨a, ha⟩ := hbf α hα
    obtain ⟨b, hb⟩ := hbg α hα
    refine ⟨a + b, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hk : ((directions α).length : WithTop ℕ∞) ≤ n := by
      rw [length_directions]; exact_mod_cast hα
    have ha' := ha ⟨x, rfl⟩
    have hb' := hb ⟨x, rfl⟩
    simp only [deriveePartielle_eq_iteratedFDerivWithin hΩ _ _ x.2] at ha' hb' ⊢
    rw [iteratedFDerivWithin_add_apply ((hf x x.2).of_le hk) ((hg x x.2).of_le hk)
      hΩ.uniqueDiffOn x.2]
    exact (norm_add_le _ _).trans (add_le_add ha' hb')
  smul_mem' := by
    rintro c f ⟨hf, hbf⟩
    refine ⟨hf.const_smul c, fun α hα => ?_⟩
    obtain ⟨a, ha⟩ := hbf α hα
    refine ⟨‖c‖ * a, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hk : ((directions α).length : WithTop ℕ∞) ≤ n := by
      rw [length_directions]; exact_mod_cast hα
    have ha' := ha ⟨x, rfl⟩
    simp only [deriveePartielle_eq_iteratedFDerivWithin hΩ _ _ x.2] at ha' ⊢
    rw [iteratedFDerivWithin_const_smul_apply ((hf x x.2).of_le hk) hΩ.uniqueDiffOn x.2]
    simp only [smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left ha' (norm_nonneg c)

/-- Norme du cours sur `C^n_b(Ω)` (`def:normeCnb`) :
`‖f‖_{C^n_b} := ∑_{|α|₁ ≤ n} ‖∂_α f‖_∞`, avec `‖g‖_∞ = sup_{x ∈ Ω} |g(x)|` (à valeurs réelles ;
elle n'a de sens que sur `C^n_b(Ω)`, où les suprema sont finis). -/
noncomputable def normeCnb {𝕜 : Type*} [RCLike 𝕜] (Ω : Set (EuclideanSpace ℝ (Fin d))) (n : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → 𝕜) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
    ⨆ x : Ω, ‖deriveePartielle α f x‖

/-- **Déf. `def:normeCnb` (Espace `C^n_b(Ω)`).** Pour `Ω ⊆ ℝ^d` ouvert et `n ∈ ℕ`,
`‖f‖_{C^n_b} = ∑_{|α|₁ ≤ n} ‖∂_α f‖_∞` satisfait sur `C^n_b(Ω)` les axiomes de norme du cours
(`def:norme`).
Remarque : les fonctions étant représentées sur `ℝ^d`, la séparation s'énonce
« `f` non identiquement nulle sur `Ω` ⇒ `‖f‖_{C^n_b} > 0` ». -/
theorem def_normeCnb (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (n : ℕ) :
    (∀ f ∈ espaceCnb 𝕜 Ω hΩ n, 0 ≤ normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb 𝕜 Ω hΩ n, (∃ x ∈ Ω, f x ≠ 0) → 0 < normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb 𝕜 Ω hΩ n, ∀ c : 𝕜, normeCnb Ω n (c • f) = ‖c‖ * normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb 𝕜 Ω hΩ n, ∀ g ∈ espaceCnb 𝕜 Ω hΩ n,
      normeCnb Ω n (f + g) ≤ normeCnb Ω n f + normeCnb Ω n g) := by
  have hsup0 : ∀ (α : Fin d → ℕ) (f : EuclideanSpace ℝ (Fin d) → 𝕜),
      0 ≤ ⨆ x : Ω, ‖deriveePartielle α f x‖ :=
    fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hnn : ∀ f : EuclideanSpace ℝ (Fin d) → 𝕜, 0 ≤ normeCnb Ω n f := fun f =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun α _ => hsup0 α f
  have hmem : ∀ k ∈ Finset.range (n + 1), ∀ α ∈ Finset.Nat.antidiagonalTuple d k,
      ((directions α).length : WithTop ℕ∞) ≤ n ∧ ∑ i, α i ≤ n := by
    intro k hk α hα
    rw [Finset.Nat.mem_antidiagonalTuple] at hα
    rw [Finset.mem_range] at hk
    have : ∑ i, α i ≤ n := by omega
    refine ⟨?_, this⟩
    rw [length_directions]; exact_mod_cast this
  refine ⟨fun f _ => hnn f, ?_, ?_, ?_⟩
  · rintro f ⟨-, hb⟩ ⟨x, hx, hfx⟩
    have h0 : (0 : ℝ) < ⨆ y : Ω, ‖deriveePartielle 0 f y‖ := by
      refine (norm_pos_iff.mpr ?_).trans_le (le_ciSup (hb 0 (by simp)) ⟨x, hx⟩)
      rwa [deriveePartielle_zero]
    refine h0.trans_le ?_
    have h1 : ⨆ y : Ω, ‖deriveePartielle 0 f y‖ =
        ∑ α ∈ Finset.Nat.antidiagonalTuple d 0, ⨆ y : Ω, ‖deriveePartielle α f y‖ := by
      simp [Finset.Nat.antidiagonalTuple_zero_right]
    rw [h1, normeCnb]
    exact Finset.single_le_sum (f := fun k => ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      ⨆ y : Ω, ‖deriveePartielle α f y‖)
      (fun k _ => Finset.sum_nonneg fun α _ => hsup0 α f) (by simp)
  · rintro f ⟨hf, -⟩ c
    rw [normeCnb, normeCnb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
    refine iSup_congr fun x => ?_
    simp only [deriveePartielle_eq_iteratedFDerivWithin hΩ _ _ x.2]
    rw [iteratedFDerivWithin_const_smul_apply ((hf x x.2).of_le (hmem k hk α hα).1)
      hΩ.uniqueDiffOn x.2]
    simp only [smul_apply, smul_eq_mul, norm_mul]
  · rintro f ⟨hf, hbf⟩ g ⟨hg, hbg⟩
    rw [normeCnb, normeCnb, normeCnb, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun α hα => ?_
    rcases isEmpty_or_nonempty Ω with hΩe | hΩe
    · simp
    refine ciSup_le fun x => ?_
    have := iteratedFDerivWithin_add_apply ((hf x x.2).of_le (hmem k hk α hα).1)
      ((hg x x.2).of_le (hmem k hk α hα).1) hΩ.uniqueDiffOn x.2
    have hfx := le_ciSup (hbf α (hmem k hk α hα).2) x
    have hgx := le_ciSup (hbg α (hmem k hk α hα).2) x
    simp only [deriveePartielle_eq_iteratedFDerivWithin hΩ _ _ x.2] at hfx hgx ⊢
    rw [this, add_apply]
    exact (norm_add_le _ _).trans (add_le_add hfx hgx)

/-- **Déf. `def:normeCnb`, espace `C^n_b(Ω̄)`.** Le sous-ensemble de `C^n_b(Ω)` formé des
fonctions dont les dérivées partielles jusqu'à l'ordre `n` s'étendent continûment à `Ω̄`. -/
def espaceCnbAdherence (𝕜 : Type*) [RCLike 𝕜] (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩ : IsOpen Ω) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d) → 𝕜) :=
  {f | f ∈ espaceCnb 𝕜 Ω hΩ n ∧ ∀ α : Fin d → ℕ, ∑ i, α i ≤ n →
    ∃ g : EuclideanSpace ℝ (Fin d) → 𝕜, ContinuousOn g (closure Ω) ∧
      EqOn g (deriveePartielle α f) Ω}

end Cnb

/-! ### Espaces de Lebesgue -/

section Lebesgue

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Déf. `def:normeLp` (Espaces de Lebesgue), espace.** `L^p(X,μ)` est l'ensemble des
classes (modulo l'égalité `μ`-p.p.) de fonctions mesurables `f : X → 𝕜` telles que
`‖f‖_p < ∞` : dans Mathlib, `Lp 𝕜 p μ` est le sous-groupe de `X →ₘ[μ] 𝕜` défini par
`eLpNorm f p μ < ∞`.
Remarque : Mathlib utilise des classes de fonctions p.p. fortement mesurables, ce qui pour
`𝕜 = ℝ, ℂ` revient aux classes de fonctions mesurables. -/
theorem def_normeLp_espace (p : ℝ≥0∞) (f : X →ₘ[μ] 𝕜) :
    f ∈ Lp 𝕜 p μ ↔ eLpNorm f p μ < ∞ :=
  Lp.mem_Lp_iff_eLpNorm_lt_top

/-- **Déf. `def:normeLp`, norme `‖f‖_p` pour `p ∈ [1, ∞[`.**
`‖f‖_p = (∫_X |f|^p dμ)^{1/p}` (intégrale de Lebesgue d'une fonction positive). -/
theorem def_normeLp_fini {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (f : Lp 𝕜 p μ) :
    ‖f‖ = ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)).toReal := by
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (zero_lt_one.trans_le hp).ne' hp' (Lp.aestronglyMeasurable f)]

/-- **Déf. `def:normeLp`, norme `‖f‖_∞`.**
`‖f‖_∞ = inf {λ ≥ 0 | |f| ≤ λ μ-p.p.}`. -/
theorem def_normeLp_infty (f : Lp 𝕜 ∞ μ) :
    ‖f‖ = sInf {l : ℝ | 0 ≤ l ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ l} := by
  have hfin : eLpNorm f ∞ μ ≠ ∞ := Lp.eLpNorm_ne_top f
  have hE : eLpNorm f ∞ μ = eLpNormEssSup f μ := eLpNorm_exponent_top (Lp.aestronglyMeasurable f)
  have hl : IsLeast {l : ℝ | 0 ≤ l ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ l} ‖f‖ := ⟨⟨norm_nonneg _, ?_⟩, ?_⟩
  · exact hl.csInf_eq.symm
  · filter_upwards [ae_le_eLpNormEssSup (f := (f : X → 𝕜)) (μ := μ)] with x hx
    rw [Lp.norm_def, hE]
    rw [hE] at hfin
    rw [← ofReal_norm] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hx
  · rintro l ⟨hl0, hl⟩
    rw [Lp.norm_def, hE]
    exact ENNReal.toReal_le_of_le_ofReal hl0 (eLpNormEssSup_le_of_ae_bound hl)

/-- **Déf. `def:normeLp`, structure d'evn.** Pour `p ∈ [1, ∞]`, `L^p(X,μ)` est un evn : sa norme
satisfait les axiomes du cours (`def:norme`) ; l'inégalité triangulaire est l'inégalité de
Minkowski.
Preuve (différente du cours) : structure d'evn de `Lp` dans Mathlib, où l'inégalité de
Minkowski (`ENNReal.lintegral_Lp_add_le`) découle de l'inégalité de Hölder, et non de la
convexité de `s ↦ s^p`. -/
theorem def_normeLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (∀ f : Lp 𝕜 p μ, 0 ≤ ‖f‖) ∧ (∀ f : Lp 𝕜 p μ, f ≠ 0 → 0 < ‖f‖) ∧
    (∀ (f : Lp 𝕜 p μ) (c : 𝕜), ‖c • f‖ = ‖c‖ * ‖f‖) ∧
    (∀ f g : Lp 𝕜 p μ, ‖f + g‖ ≤ ‖f‖ + ‖g‖) :=
  def_norme

end Lebesgue

end M1Analyse
