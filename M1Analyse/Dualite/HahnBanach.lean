/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Order.Zorn
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Basic

/-!
# §3.1 Théorème de Hahn-Banach (`subsec:HahnBanach`)

Source : `Include/Dualite.tex`, sous-section `subsec:HahnBanach` (l'introduction du chapitre
`sec:dual` ne contient pas d'énoncé numéroté).

Les objets du cours sont ceux de Mathlib : dual topologique `E^* = StrongDual ℝ E`, sous-espace
vectoriel = `Submodule ℝ E`, lemme de Zorn = `zorn_le`. La notion d'ensemble inductif, absente
de Mathlib sous ce nom, est introduite (`M1Analyse.Inductif`) et reliée à la formulation de
Mathlib (`IsChain`, `BddAbove`). Le théorème de Hahn-Banach (forme analytique) est déduit de
`exists_extension_of_le_sublinear`.
-/

open Set Topology

namespace M1Analyse

section Zorn

variable (α : Type*) [PartialOrder α]

/-- **Déf. `def:inductif` (Ensemble inductif).** Un ensemble partiellement ordonné est inductif
si toute partie totalement ordonnée `F` admet un majorant. -/
def Inductif : Prop :=
  ∀ F : Set α, (∀ y ∈ F, ∀ z ∈ F, y ≤ z ∨ z ≤ y) → ∃ x, ∀ y ∈ F, y ≤ x

/-- **Déf. `def:inductif`, lien avec Mathlib.** Être inductif équivaut à : toute chaîne
(`IsChain`) est majorée (`BddAbove`), hypothèse du lemme de Zorn `zorn_le` de Mathlib. -/
theorem def_inductif_iff :
    Inductif α ↔ ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c := by
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h c fun y hy z hz => hc.total hy hz
    exact ⟨x, hx⟩
  · intro h F hF
    obtain ⟨x, hx⟩ := h F fun y hy z hz _ => hF y hy z hz
    exact ⟨x, hx⟩

/-- **Lemme `lem:Zorn` (Zorn).** Tout ensemble non vide et inductif admet un élément maximal
`m` (i.e. `m ≤ y → y = m`).
Remarque : l'hypothèse de non-vacuité est en fait conséquence du caractère inductif (la partie
vide admet un majorant). -/
theorem lem_Zorn [Nonempty α] (h : Inductif α) : ∃ m : α, ∀ y, m ≤ y → y = m := by
  obtain ⟨m, hm⟩ := zorn_le ((def_inductif_iff α).1 h)
  exact ⟨m, fun y hy => le_antisymm (hm hy) hy⟩

/-- **Déf. `def:axiomChoix` (Axiome du choix).** Pour tout ensemble `𝒜` d'ensembles non vides,
il existe une fonction de choix `f : 𝒜 → ⋃ 𝒜` telle que `f(a) ∈ a` pour tout `a ∈ 𝒜`. -/
theorem def_axiomChoix {β : Type*} (𝒜 : Set (Set β)) (h𝒜 : ∀ a ∈ 𝒜, a.Nonempty) :
    ∃ f : 𝒜 → ⋃₀ 𝒜, ∀ a : 𝒜, (f a : β) ∈ (a : Set β) :=
  ⟨fun a => ⟨(h𝒜 a a.2).some, mem_sUnion_of_mem (h𝒜 a a.2).some_mem a.2⟩,
    fun a => (h𝒜 a a.2).some_mem⟩

end Zorn

section SousLineaire

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- La propriété de sous-linéarité du cours (`def:sousLin`) : positive homogénéité (pour
`λ ≥ 0`) et sous-additivité. -/
def SousLineaire (ρ : E → ℝ) : Prop :=
  (∀ (c : ℝ), 0 ≤ c → ∀ x, ρ (c • x) = c * ρ x) ∧ ∀ x y, ρ (x + y) ≤ ρ x + ρ y

/-- **Déf. `def:sousLin` (Fonction sous-linéaire).** Une fonction `ρ : E → ℝ` est sous-linéaire
(positivement homogène et sous-additive) si et seulement si elle est positivement `1`-homogène et
convexe. -/
theorem def_sousLin (ρ : E → ℝ) :
    SousLineaire ρ ↔
      (∀ (c : ℝ), 0 ≤ c → ∀ x, ρ (c • x) = c * ρ x) ∧ ConvexOn ℝ univ ρ := by
  constructor
  · rintro ⟨hhom, hadd⟩
    refine ⟨hhom, convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    calc ρ (a • x + b • y) ≤ ρ (a • x) + ρ (b • y) := hadd _ _
      _ = a • ρ x + b • ρ y := by rw [hhom a ha, hhom b hb, smul_eq_mul, smul_eq_mul]
  · rintro ⟨hhom, hcvx⟩
    refine ⟨hhom, fun x y => ?_⟩
    have h := hcvx.2 (mem_univ (2 • x)) (mem_univ (2 • y))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e1 : ((1 : ℝ) / 2) • ((2 : ℕ) • x) = x := by
      rw [two_nsmul, ← two_smul ℝ x, smul_smul]; norm_num
    have e2 : ((1 : ℝ) / 2) • ((2 : ℕ) • y) = y := by
      rw [two_nsmul, ← two_smul ℝ y, smul_smul]; norm_num
    have h2x : ρ ((2 : ℕ) • x) = 2 * ρ x := by
      rw [two_nsmul, ← two_smul ℝ x, hhom 2 (by norm_num)]
    have h2y : ρ ((2 : ℕ) • y) = 2 * ρ y := by
      rw [two_nsmul, ← two_smul ℝ y, hhom 2 (by norm_num)]
    rw [e1, e2, h2x, h2y, smul_eq_mul, smul_eq_mul] at h
    linarith

/-- **Th. `th:HahnBanach` (Hahn-Banach).** Soient `E` un `ℝ`-espace vectoriel, `F` un
sous-espace, `ρ : E → ℝ` sous-linéaire et `φ_F : F → ℝ` linéaire avec `φ_F ≤ ρ` sur `F`. Alors il
existe `φ : E → ℝ` linéaire avec `φ ≤ ρ` sur `E` et `φ|_F = φ_F`. -/
theorem th_HahnBanach (F : Submodule ℝ E) (ρ : E → ℝ) (hρ : SousLineaire ρ)
    (φF : F →ₗ[ℝ] ℝ) (hφF : ∀ x : F, φF x ≤ ρ x) :
    ∃ φ : E →ₗ[ℝ] ℝ, (∀ x, φ x ≤ ρ x) ∧ ∀ x : F, φ x = φF x := by
  obtain ⟨g, hg, hgρ⟩ := exists_extension_of_le_sublinear ⟨F, φF⟩ ρ
    (fun c hc x => hρ.1 c hc.le x) hρ.2 hφF
  exact ⟨g, hgρ, hg⟩

end SousLineaire

section EVN

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Cor. `corol:prol_forme_evn` (Prolongement de même norme d'une forme linéaire).** Soient `E`
un evn, `F ⊆ E` un sous-espace et `φ_F ∈ F^*`. Il existe `φ ∈ E^*` prolongeant `φ_F` et de même
norme. -/
theorem corol_prol_forme_evn (F : Submodule ℝ E) (φF : StrongDual ℝ F) :
    ∃ φ : StrongDual ℝ E, (∀ x : F, φ x = φF x) ∧ ‖φ‖ = ‖φF‖ :=
  exists_extension_norm_eq F φF

/-- **Cor. `corol:dens_banach` (Critère de densité).** Un sous-espace `F` d'un `ℝ`-evn `E` est
dense si et seulement si la seule forme linéaire continue s'annulant sur `F` est `0`. -/
theorem corol_dens_banach (F : Submodule ℝ E) :
    Dense (F : Set E) ↔ ∀ φ : StrongDual ℝ E, (∀ x ∈ F, φ x = 0) → φ = 0 := by
  constructor
  · intro hF φ hφ
    ext x
    have hcl : IsClosed {y : E | φ y = 0} := isClosed_eq φ.continuous continuous_const
    exact closure_minimal (fun y hy => hφ y hy) hcl (hF x)
  · intro h
    by_contra hd
    obtain ⟨x, hx⟩ : ∃ x, x ∉ closure (F : Set E) := by
      by_contra hc
      push Not at hc
      exact hd fun x => hc x
    have hconv : Convex ℝ (closure (F : Set E)) := (F.convex).closure
    obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hconv isClosed_closure hx
    have h0 : (0 : E) ∈ closure (F : Set E) := subset_closure F.zero_mem
    have hu : u < 0 := by simpa using hfb 0 h0
    have hzero : ∀ y ∈ F, f y = 0 := by
      intro y hy
      by_contra hne
      have hmem : ((u - 1) / f y) • y ∈ closure (F : Set E) :=
        subset_closure (F.smul_mem _ hy)
      have := hfb _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have := h f hzero
    subst this
    simp at hfx
    linarith

/-- **Ex. `ex:dualSeparable`.** Soit `E` un evn. Si `E^*` est séparable, alors `E` est
séparable. -/
theorem ex_dualSeparable [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.SeparableSpace E := by
  obtain ⟨φs, hφs⟩ := TopologicalSpace.exists_dense_seq (StrongDual ℝ E)
  -- choix de `x_n` avec `‖x_n‖ ≤ 1` et `φ_n(x_n) ≥ ‖φ_n‖/2`
  have hx : ∀ n, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖φs n‖ / 2 ≤ φs n x := by
    intro n
    rcases eq_or_ne (φs n) 0 with h0 | h0
    · exact ⟨0, by simp, by simp [h0]⟩
    · have hpos : 0 < ‖φs n‖ := norm_pos_iff.2 h0
      obtain ⟨x, hx1, hx2'⟩ := (φs n).exists_lt_apply_of_lt_opNorm
        (r := ‖φs n‖ / 2) (by linarith)
      have hx1' : ‖x‖ ≤ 1 := hx1.le
      rw [Real.norm_eq_abs] at hx2'
      rcases le_or_gt 0 (φs n x) with hs | hs
      · exact ⟨x, hx1', by rw [abs_of_nonneg hs] at hx2'; exact hx2'.le⟩
      · refine ⟨-x, by simpa using hx1', ?_⟩
        rw [abs_of_neg hs] at hx2'
        simp only [map_neg]
        exact hx2'.le
  choose x hx1 hx2 using hx
  let F : Submodule ℝ E := Submodule.span ℝ (range x)
  have hFsep : TopologicalSpace.IsSeparable (F : Set E) :=
    (countable_range x).isSeparable.span
  have hdense : Dense (F : Set E) := by
    rw [corol_dens_banach]
    intro φ hφ
    by_contra hne
    have hpos : 0 < ‖φ‖ := norm_pos_iff.2 hne
    obtain ⟨n, hn⟩ : ∃ n, dist φ (φs n) < ‖φ‖ / 4 :=
      hφs.exists_dist_lt φ (by positivity)
    rw [dist_eq_norm] at hn
    have hxn : φ (x n) = 0 := hφ _ (Submodule.subset_span (mem_range_self n))
    have h1 : φs n (x n) ≤ ‖φ - φs n‖ := by
      have : φs n (x n) = (φs n - φ) (x n) := by simp [hxn]
      rw [this]
      calc (φs n - φ) (x n) ≤ ‖(φs n - φ) (x n)‖ := Real.le_norm_self _
        _ ≤ ‖φs n - φ‖ * ‖x n‖ := (φs n - φ).le_opNorm _
        _ ≤ ‖φs n - φ‖ * 1 := by gcongr; exact hx1 n
        _ = ‖φ - φs n‖ := by rw [mul_one, norm_sub_rev]
    have h2 : ‖φ‖ ≤ ‖φs n‖ + ‖φ - φs n‖ := by
      calc ‖φ‖ = ‖φs n + (φ - φs n)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h3 := hx2 n
    linarith
  have : TopologicalSpace.IsSeparable (univ : Set E) := by
    rw [← hdense.closure_eq]
    exact hFsep.closure
  exact TopologicalSpace.isSeparable_univ_iff.1 this

/-- **Cor. `corol:projDimFinie` (Projection sur un sous-espace de dimension finie).** Pour tout
sous-espace de dimension finie `F` d'un evn `E`, il existe une projection linéaire continue
`P_F : E → F` (i.e. `P_F x = x` pour `x ∈ F`). -/
theorem corol_projDimFinie (F : Submodule ℝ E) [FiniteDimensional ℝ F] :
    ∃ P : E →L[ℝ] F, ∀ x : F, P x = x :=
  Submodule.ClosedComplemented.of_finiteDimensional F

end EVN

end M1Analyse
