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

/-!
# §1.3 Espaces vectoriels normés (`subsec:evn`)

Source : `Include/TopologieGenerale.tex`, sous-section `subsec:evn` (y compris la
sous-sous-section « Exemples d'espaces fonctionnels »).

Les objets du cours sont ceux de Mathlib : evn = `NormedAddCommGroup` + `NormedSpace 𝕜`,
semi-norme = `Seminorm 𝕜 E`, `L(E,F)` = `E →L[𝕜] F` (norme d'opérateur `‖u‖`),
dual = `StrongDual 𝕜 E`, `C⁰_b(X,𝕂)` = `X →ᵇ 𝕜`, Hölder/Lipschitz = `HolderWith`, `MemHolder`,
`LipschitzWith`, `L^p(X,μ)` = `MeasureTheory.Lp 𝕜 p μ`.

Les formules « sup » du cours pour la semi-norme de Hölder et la constante de Lipschitz ne
figurent pas telles quelles dans Mathlib (qui définit `nnHolderNorm` comme un inf de constantes) :
on les introduit (`seminormeHolder`, `constLip`, `normeHolder`) et on montre qu'elles coïncident
avec les objets de Mathlib.
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

variable {X : Type*} [MetricSpace X]

/-- Semi-norme de Hölder du cours, `|f|_{C^α} := sup_{x ≠ y} |f(x) - f(y)| / d(x,y)^α`
(`def:normeHolder`). Valeur `0` par convention si le sup n'est pas fini. -/
noncomputable def seminormeHolder (α : ℝ≥0) (f : X → 𝕜) : ℝ :=
  ⨆ p : {p : X × X // p.1 ≠ p.2}, ‖f p.1.1 - f p.1.2‖ / dist p.1.1 p.1.2 ^ (α : ℝ)

/-- Constante de Lipschitz du cours, `Lip(f) := sup_{x ≠ y} |f(x) - f(y)| / d(x,y)`
(`def:normeHolder`). -/
noncomputable def constLip (f : X → 𝕜) : ℝ :=
  ⨆ p : {p : X × X // p.1 ≠ p.2}, ‖f p.1.1 - f p.1.2‖ / dist p.1.1 p.1.2

/-- Norme de Hölder du cours, `‖f‖_{C^α} := ‖f‖_∞ + |f|_{C^α}` (`def:normeHolder`). Pour
`α = 1`, c'est la norme `‖f‖_∞ + Lip(f)` des fonctions Lipschitziennes bornées. -/
noncomputable def normeHolder (α : ℝ≥0) (f : X → 𝕜) : ℝ :=
  (⨆ x, ‖f x‖) + seminormeHolder α f

/-- L'espace `C^α_b(X,𝕂)` des fonctions bornées et `α`-Hölderiennes (`def:normeHolder`), vu
comme sous-espace vectoriel de `X → 𝕜`. Pour `α = 1`, ce sont les fonctions Lipschitziennes
bornées. -/
def espaceHolder (α : ℝ≥0) : Submodule 𝕜 (X → 𝕜) where
  carrier := {f | BddAbove (range fun x => ‖f x‖) ∧ MemHolder α f}
  zero_mem' := ⟨⟨0, by rintro _ ⟨x, rfl⟩; simp⟩, memHolder_zero⟩
  add_mem' := by
    rintro f g ⟨⟨a, ha⟩, hf⟩ ⟨⟨b, hb⟩, hg⟩
    refine ⟨⟨a + b, ?_⟩, hf.add hg⟩
    rintro _ ⟨x, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (ha ⟨x, rfl⟩) (hb ⟨x, rfl⟩))
  smul_mem' := by
    rintro c f ⟨⟨a, ha⟩, hf⟩
    refine ⟨⟨‖c‖ * a, ?_⟩, hf.smul⟩
    rintro _ ⟨x, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha ⟨x, rfl⟩) (norm_nonneg c)

lemma holderWith_of_dist_le {C α : ℝ≥0} {f : X → 𝕜}
    (h : ∀ x y, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) : HolderWith C α f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg α),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x y)

lemma ratio_le_of_holderWith {α C : ℝ≥0} {f : X → 𝕜} (hf : HolderWith C α f) {x y : X}
    (hxy : x ≠ y) : ‖f x - f y‖ / dist x y ^ (α : ℝ) ≤ C := by
  have hd : 0 < dist x y ^ (α : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  rw [div_le_iff₀ hd, ← dist_eq_norm]
  exact hf.dist_le x y

lemma seminormeHolder_nonneg (α : ℝ≥0) (f : X → 𝕜) : 0 ≤ seminormeHolder α f :=
  Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)

lemma holderWith_seminormeHolder {α : ℝ≥0} {f : X → 𝕜} (hf : MemHolder α f) :
    HolderWith ⟨seminormeHolder α f, seminormeHolder_nonneg α f⟩ α f := by
  obtain ⟨C, hC⟩ := hf
  have hbdd : BddAbove (range fun p : {p : X × X // p.1 ≠ p.2} =>
      ‖f p.1.1 - f p.1.2‖ / dist p.1.1 p.1.2 ^ (α : ℝ)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact ratio_le_of_holderWith hC p.2
  refine holderWith_of_dist_le fun x y => ?_
  rcases eq_or_ne x y with rfl | hxy
  · simp only [dist_self]
    exact mul_nonneg (seminormeHolder_nonneg α f) (Real.rpow_nonneg le_rfl _)
  · have hd : 0 < dist x y ^ (α : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
    have := le_ciSup hbdd ⟨(x, y), hxy⟩
    rw [div_le_iff₀ hd, ← dist_eq_norm] at this
    exact this

/-- **Déf. `def:normeHolder` (semi-norme de Hölder).** Pour `f` `α`-Hölderienne, la semi-norme
du cours `|f|_{C^α} = sup_{x ≠ y} |f(x)-f(y)|/d(x,y)^α` est la plus petite constante `C ≥ 0`
telle que `|f(x) - f(y)| ≤ C d(x,y)^α`, et coïncide avec `nnHolderNorm α f` de Mathlib. -/
theorem def_normeHolder_seminorme {α : ℝ≥0} {f : X → 𝕜} (hf : MemHolder α f) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (α : ℝ)}
      (seminormeHolder α f) ∧
    seminormeHolder α f = nnHolderNorm α f := by
  refine ⟨⟨⟨seminormeHolder_nonneg α f, fun x y => ?_⟩, ?_⟩, le_antisymm ?_ ?_⟩
  · rw [← dist_eq_norm]; exact (holderWith_seminormeHolder hf).dist_le x y
  · rintro C ⟨hC0, hC⟩
    refine Real.iSup_le (fun p => ?_) hC0
    have hd : 0 < dist p.1.1 p.1.2 ^ (α : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr p.2) _
    rw [div_le_iff₀ hd]
    exact hC _ _
  · refine Real.iSup_le (fun p => ratio_le_of_holderWith hf.holderWith p.2) (by positivity)
  · exact_mod_cast (holderWith_seminormeHolder hf).nnholderNorm_le

/-- **Déf. `def:normeHolder` (constante de Lipschitz).** `Lip(f)` est la semi-norme de Hölder
d'exposant `1`, les fonctions Lipschitziennes sont les fonctions `1`-Hölderiennes, et pour `f`
Lipschitzienne, `Lip(f)` est la plus petite constante de Lipschitz de `f`. -/
theorem def_normeHolder_lip (f : X → 𝕜) :
    constLip f = seminormeHolder 1 f ∧ (MemHolder 1 f ↔ ∃ K, LipschitzWith K f) ∧
    ((∃ K, LipschitzWith K f) →
      IsLeast {K : ℝ≥0 | LipschitzWith K f} ⟨constLip f, by
        rw [show constLip f = seminormeHolder 1 f by simp [constLip, seminormeHolder]]
        exact seminormeHolder_nonneg 1 f⟩) := by
  have h1 : constLip f = seminormeHolder 1 f := by simp [constLip, seminormeHolder]
  refine ⟨h1, by simp [MemHolder, holderWith_one], fun hK => ?_⟩
  have hf : MemHolder 1 f := by simpa [MemHolder, holderWith_one] using hK
  obtain ⟨⟨-, hle⟩, hleast⟩ := (def_normeHolder_seminorme hf).1
  refine ⟨?_, fun K hK' => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hle x y
    simp only [NNReal.coe_one, Real.rpow_one] at this
    rw [← h1] at this
    rw [dist_eq_norm]
    exact this
  · have := hleast ⟨K.2, fun x y => by simpa [dist_eq_norm] using hK'.dist_le_mul x y⟩
    rw [← h1] at this
    exact_mod_cast this

/-- **Déf. `def:normeHolder` (evn `C^α_b(X,𝕂)`).** Sur l'espace `C^α_b(X,𝕂)` des fonctions
bornées `α`-Hölderiennes (fonctions Lipschitziennes bornées pour `α = 1`),
`‖f‖_{C^α} = ‖f‖_∞ + |f|_{C^α}` satisfait les axiomes de norme du cours (`def:norme`). -/
theorem def_normeHolder (α : ℝ≥0) :
    (∀ f ∈ espaceHolder (X := X) (𝕜 := 𝕜) α, 0 ≤ normeHolder α f) ∧
    (∀ f ∈ espaceHolder (X := X) (𝕜 := 𝕜) α, f ≠ 0 → 0 < normeHolder α f) ∧
    (∀ f ∈ espaceHolder (X := X) (𝕜 := 𝕜) α, ∀ c : 𝕜,
      normeHolder α (c • f) = ‖c‖ * normeHolder α f) ∧
    (∀ f ∈ espaceHolder (X := X) (𝕜 := 𝕜) α, ∀ g ∈ espaceHolder (X := X) (𝕜 := 𝕜) α,
      normeHolder α (f + g) ≤ normeHolder α f + normeHolder α g) := by
  have hsup0 : ∀ f : X → 𝕜, 0 ≤ ⨆ x, ‖f x‖ := fun f => Real.iSup_nonneg fun _ => norm_nonneg _
  have hnn : ∀ f : X → 𝕜, 0 ≤ normeHolder α f := fun f =>
    add_nonneg (hsup0 f) (seminormeHolder_nonneg α f)
  refine ⟨fun f _ => hnn f, ?_, ?_, ?_⟩
  · rintro f ⟨hb, -⟩ hf0
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hf0 (funext h)
    have : 0 < ⨆ x, ‖f x‖ := (norm_pos_iff.mpr hx).trans_le (le_ciSup hb x)
    exact add_pos_of_pos_of_nonneg this (seminormeHolder_nonneg α f)
  · rintro f ⟨-, hf⟩ c
    have hs := (def_normeHolder_seminorme (hf.smul (c := c))).2
    rw [normeHolder, normeHolder, hs, hf.nnHolderNorm_smul c, (def_normeHolder_seminorme hf).2,
      mul_add]
    congr 1
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm
  · rintro f ⟨hbf, hf⟩ g ⟨hbg, hg⟩
    rw [normeHolder, normeHolder, normeHolder, (def_normeHolder_seminorme (hf.add hg)).2,
      (def_normeHolder_seminorme hf).2, (def_normeHolder_seminorme hg).2,
      add_add_add_comm]
    refine add_le_add ?_ (by exact_mod_cast hf.nnHolderNorm_add_le hg)
    rcases isEmpty_or_nonempty X with hX | hX
    · simp
    · exact ciSup_le fun x => (norm_add_le _ _).trans
        (add_le_add (le_ciSup hbf x) (le_ciSup hbg x))

end Holder

/-! ### Espaces `C^n_b(Ω)` -/

section Cnb

variable {d : ℕ}

/-- Liste des directions de dérivation associée au multi-indice `α ∈ ℕ^d` : chaque
`i ∈ {0, …, d-1}` y figure `α_i` fois (l'ordre est sans importance pour une fonction `C^n`,
par le lemme de Schwarz). -/
def directions (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun i => List.replicate (α i) i

lemma length_directions (α : Fin d → ℕ) : (directions α).length = ∑ i, α i := by
  simp [directions, List.length_flatMap, Fin.sum_univ_def]

/-- Dérivée partielle `∂_α f(x)` du cours (`def:normeCnb`), pour `f` définie sur `ℝ^d`
(représenté par `Fin d → ℝ`) et un ouvert `Ω` : la différentielle itérée d'ordre `|α|₁`
de `f` (relative à `Ω`) appliquée aux vecteurs de base `e_i`, chacun répété `α_i` fois. -/
noncomputable def deriveePartielle (Ω : Set (Fin d → ℝ)) (α : Fin d → ℕ)
    (f : (Fin d → ℝ) → 𝕜) (x : Fin d → ℝ) : 𝕜 :=
  iteratedFDerivWithin ℝ (directions α).length f Ω x
    (fun j => Pi.single ((directions α).get j) 1)

lemma deriveePartielle_zero (Ω : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → 𝕜) (x : Fin d → ℝ) :
    deriveePartielle Ω 0 f x = f x := by
  have h : directions (0 : Fin d → ℕ) = [] := by simp [directions]
  unfold deriveePartielle
  generalize directions 0 = l at h ⊢
  subst h
  rfl

/-- L'espace `C^n_b(Ω)` du cours (`def:normeCnb`) : fonctions `n` fois continûment
différentiables sur `Ω`, dont les dérivées partielles `∂_α f`, `|α|₁ ≤ n`, sont bornées sur `Ω`.
Les fonctions sont représentées par des fonctions sur `ℝ^d` tout entier, dont seules les
valeurs sur `Ω` interviennent. -/
def espaceCnb (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω) (n : ℕ) :
    Submodule 𝕜 ((Fin d → ℝ) → 𝕜) where
  carrier := {f | ContDiffOn ℝ n f Ω ∧
    ∀ α : Fin d → ℕ, ∑ i, α i ≤ n → BddAbove (range fun x : Ω => ‖deriveePartielle Ω α f x‖)}
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
    simp only [deriveePartielle]
    rw [iteratedFDerivWithin_add_apply ((hf x x.2).of_le hk) ((hg x x.2).of_le hk)
      hΩ.uniqueDiffOn x.2]
    exact (norm_add_le _ _).trans (add_le_add (ha ⟨x, rfl⟩) (hb ⟨x, rfl⟩))
  smul_mem' := by
    rintro c f ⟨hf, hbf⟩
    refine ⟨hf.const_smul c, fun α hα => ?_⟩
    obtain ⟨a, ha⟩ := hbf α hα
    refine ⟨‖c‖ * a, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hk : ((directions α).length : WithTop ℕ∞) ≤ n := by
      rw [length_directions]; exact_mod_cast hα
    simp only [deriveePartielle]
    rw [iteratedFDerivWithin_const_smul_apply ((hf x x.2).of_le hk) hΩ.uniqueDiffOn x.2]
    simp only [smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha ⟨x, rfl⟩) (norm_nonneg c)

/-- Norme du cours sur `C^n_b(Ω)` (`def:normeCnb`) :
`‖f‖_{C^n_b} := ∑_{|α|₁ ≤ n} ‖∂_α f‖_∞`, avec `‖g‖_∞ = sup_{x ∈ Ω} |g(x)|`. -/
noncomputable def normeCnb (Ω : Set (Fin d → ℝ)) (n : ℕ) (f : (Fin d → ℝ) → 𝕜) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
    ⨆ x : Ω, ‖deriveePartielle Ω α f x‖

/-- **Déf. `def:normeCnb` (Espace `C^n_b(Ω)`).** Pour `Ω ⊆ ℝ^d` ouvert et `n ∈ ℕ`,
`‖f‖_{C^n_b} = ∑_{|α|₁ ≤ n} ‖∂_α f‖_∞` satisfait sur `C^n_b(Ω)` les axiomes de norme du cours
(`def:norme`).
Remarque : les fonctions étant représentées sur `ℝ^d`, la séparation s'énonce
« `f` non identiquement nulle sur `Ω` ⇒ `‖f‖_{C^n_b} > 0` ». -/
theorem def_normeCnb (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω) (n : ℕ) :
    (∀ f ∈ espaceCnb (𝕜 := 𝕜) Ω hΩ n, 0 ≤ normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb (𝕜 := 𝕜) Ω hΩ n, (∃ x ∈ Ω, f x ≠ 0) → 0 < normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb (𝕜 := 𝕜) Ω hΩ n, ∀ c : 𝕜,
      normeCnb Ω n (c • f) = ‖c‖ * normeCnb Ω n f) ∧
    (∀ f ∈ espaceCnb (𝕜 := 𝕜) Ω hΩ n, ∀ g ∈ espaceCnb (𝕜 := 𝕜) Ω hΩ n,
      normeCnb Ω n (f + g) ≤ normeCnb Ω n f + normeCnb Ω n g) := by
  have hsup0 : ∀ (α : Fin d → ℕ) (f : (Fin d → ℝ) → 𝕜),
      0 ≤ ⨆ x : Ω, ‖deriveePartielle Ω α f x‖ :=
    fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hnn : ∀ f : (Fin d → ℝ) → 𝕜, 0 ≤ normeCnb Ω n f := fun f =>
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
    have h0 : (0 : ℝ) < ⨆ y : Ω, ‖deriveePartielle Ω 0 f y‖ := by
      refine (norm_pos_iff.mpr ?_).trans_le (le_ciSup (hb 0 (by simp)) ⟨x, hx⟩)
      rwa [deriveePartielle_zero]
    refine h0.trans_le ?_
    have h1 : ⨆ y : Ω, ‖deriveePartielle Ω 0 f y‖ =
        ∑ α ∈ Finset.Nat.antidiagonalTuple d 0, ⨆ y : Ω, ‖deriveePartielle Ω α f y‖ := by
      simp [Finset.Nat.antidiagonalTuple_zero_right]
    rw [h1, normeCnb]
    exact Finset.single_le_sum (f := fun k => ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      ⨆ y : Ω, ‖deriveePartielle Ω α f y‖)
      (fun k _ => Finset.sum_nonneg fun α _ => hsup0 α f) (by simp)
  · rintro f ⟨hf, -⟩ c
    rw [normeCnb, normeCnb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
    refine iSup_congr fun x => ?_
    simp only [deriveePartielle]
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
    simp only [deriveePartielle, this, add_apply]
    exact (norm_add_le _ _).trans (add_le_add (le_ciSup (hbf α (hmem k hk α hα).2) x)
      (le_ciSup (hbg α (hmem k hk α hα).2) x))

/-- **Déf. `def:normeCnb`, espace `C^n_b(Ω̄)`.** Le sous-ensemble de `C^n_b(Ω)` formé des
fonctions dont les dérivées partielles jusqu'à l'ordre `n` s'étendent continûment à `Ω̄`. -/
def espaceCnbAdherence (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω) (n : ℕ) :
    Set ((Fin d → ℝ) → 𝕜) :=
  {f | f ∈ espaceCnb Ω hΩ n ∧ ∀ α : Fin d → ℕ, ∑ i, α i ≤ n →
    ∃ g : (Fin d → ℝ) → 𝕜, ContinuousOn g (closure Ω) ∧ EqOn g (deriveePartielle Ω α f) Ω}

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
Minkowski. -/
theorem def_normeLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (∀ f : Lp 𝕜 p μ, 0 ≤ ‖f‖) ∧ (∀ f : Lp 𝕜 p μ, f ≠ 0 → 0 < ‖f‖) ∧
    (∀ (f : Lp 𝕜 p μ) (c : 𝕜), ‖c • f‖ = ‖c‖ * ‖f‖) ∧
    (∀ f g : Lp 𝕜 p μ, ‖f + g‖ ≤ ‖f‖ + ‖g‖) :=
  def_norme

end Lebesgue

end M1Analyse
