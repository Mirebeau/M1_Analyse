/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.RCLike.Basic

/-!
# §2.6 Applications de Baire aux opérateurs linéaires continus (`subsec:BaireLin`)

Source : `Include/Completude.tex`, sous-section `subsec:BaireLin`.

Le corps de base `𝕂 = ℝ` ou `ℂ` du cours est modélisé par `[RCLike 𝕜]`. Un Banach est un
`NormedAddCommGroup` + `NormedSpace 𝕜` + `CompleteSpace` ; `L(E,F)` est `E →L[𝕜] F` et la norme
d'opérateur `|||L|||` est `‖L‖`. Les théorèmes de Banach-Steinhaus, de l'application ouverte et
du graphe fermé sont ceux de Mathlib (`banach_steinhaus`, `ContinuousLinearMap.isOpenMap`,
`LinearMap.continuous_of_isClosed_graph`).
-/

open Set Filter Topology Metric Function

namespace M1Analyse

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Th. `th:BanachSteinhaus` (Banach-Steinhaus).** Soit `E` un Banach, `F` un evn et
`𝒜 ⊆ L(E,F)` simplement bornée : `∀ x, sup_{L ∈ 𝒜} ‖Lx‖ < ∞`. Alors `𝒜` est uniformément
bornée : `sup_{L ∈ 𝒜} |||L||| < ∞`.
Preuve (différente du cours) : appel direct au théorème `banach_steinhaus` de Mathlib, sans
l'argument de Baire sur les fermés `E_k` du cours. -/
theorem th_BanachSteinhaus [CompleteSpace E] (𝒜 : Set (E →L[𝕜] F))
    (h : ∀ x : E, ∃ C, ∀ L ∈ 𝒜, ‖L x‖ ≤ C) : ∃ C, ∀ L ∈ 𝒜, ‖L‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun L : 𝒜 => (L : E →L[𝕜] F))
    fun x => (h x).imp fun C hC L => hC L L.2
  exact ⟨C, fun L hL => hC ⟨L, hL⟩⟩

/-- **Cor. `corol:limSimpleLin`.** Soient `E` un Banach, `F` un evn et `L_n ∈ L(E,F)` telles que
`Lx := lim L_n x` existe pour tout `x ∈ E`. Alors `L ∈ L(E,F)` est linéaire continue. -/
theorem corol_limSimpleLin [CompleteSpace E] (L : ℕ → E →L[𝕜] F) (Lim : E → F)
    (h : ∀ x, Tendsto (fun n => L n x) atTop (𝓝 (Lim x))) :
    ∃ M : E →L[𝕜] F, ⇑M = Lim :=
  ⟨continuousLinearMapOfTendsto L (tendsto_pi_nhds.2 h), rfl⟩

/-- **Cor. `corol:BanachSteinhausK` (Banach-Steinhaus, pour les formes linéaires).** Soient `E`
un Banach et `𝒜 ⊆ E^*`. Alors `𝒜` est *faiblement borné (`∀ x, {l(x) | l ∈ 𝒜}` est borné)
ssi `𝒜` est borné. -/
theorem corol_BanachSteinhausK [CompleteSpace E] (𝒜 : Set (E →L[𝕜] 𝕜)) :
    (∀ x : E, Bornology.IsBounded ((fun l : E →L[𝕜] 𝕜 => l x) '' 𝒜)) ↔
      Bornology.IsBounded 𝒜 := by
  simp only [isBounded_iff_forall_norm_le, forall_mem_image]
  constructor
  · exact th_BanachSteinhaus 𝒜
  · rintro ⟨C, hC⟩ x
    exact ⟨C * ‖x‖, fun l hl =>
      (l.le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC l hl) (norm_nonneg x))⟩

/-- **Th. `th:appliOuverte` (Application ouverte).** Soient `E, F` des Banach et `L ∈ L(E,F)`
surjective. Alors `∃ δ > 0, B_F(0,δ) ⊆ L(B_E(0,1))`, et l'image par `L` de tout ouvert est un
ouvert.
Preuve (différente du cours) : l'ouverture de `L` est le théorème de Mathlib
`ContinuousLinearMap.isOpenMap` ; l'inclusion de boules s'en déduit (ordre inverse du cours). -/
theorem th_appliOuverte [CompleteSpace E] [CompleteSpace F] (L : E →L[𝕜] F)
    (hL : Surjective L) :
    (∃ δ > 0, ball (0 : F) δ ⊆ L '' ball 0 1) ∧ IsOpenMap L := by
  have ho : IsOpenMap L := L.isOpenMap hL
  refine ⟨?_, ho⟩
  have h0 : (0 : F) ∈ L '' ball 0 1 := ⟨0, mem_ball_self one_pos, map_zero L⟩
  exact Metric.isOpen_iff.1 (ho _ isOpen_ball) 0 h0

/-- **Cor. `corol:isomBanach` (Isomorphisme de Banach).** Soient `E, F` des Banach et
`L ∈ L(E,F)` bijective. Alors `L⁻¹ ∈ L(F,E)` est continue. -/
theorem corol_isomBanach [CompleteSpace E] [CompleteSpace F] (L : E →L[𝕜] F)
    (hL : Bijective L) :
    ∃ M : F →L[𝕜] E, (∀ x, M (L x) = x) ∧ ∀ y, L (M y) = y := by
  let e := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.2 hL.1)
    (LinearMap.range_eq_top.2 hL.2)
  exact ⟨e.symm, fun x => e.symm_apply_apply x, fun y => e.apply_symm_apply y⟩

/-- **Cor. `corol:equivNormes` (Équivalence des normes).** Soit `E` un espace vectoriel complet
pour deux normes `‖·‖` et `‖·‖'`. S'il existe `C` tel que `‖x‖' ≤ C ‖x‖`, alors il existe
`c > 0` tel que `‖x‖' ≥ c ‖x‖`.
Remarque : on modélise `(E, ‖·‖')` par un second espace `E'` et l'identité par un isomorphisme
linéaire `e : E ≃ₗ[𝕜] E'` (de sorte que `‖x‖' = ‖e x‖`), Lean ne permettant pas commodément
deux structures normées sur un même type. -/
theorem corol_equivNormes {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [CompleteSpace E] [CompleteSpace E'] (e : E ≃ₗ[𝕜] E')
    (hC : ∃ C, ∀ x, ‖e x‖ ≤ C * ‖x‖) : ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖e x‖ := by
  obtain ⟨C, hC⟩ := hC
  have hcont : Continuous e := AddMonoidHomClass.continuous_of_bound e C hC
  let M : E' →L[𝕜] E := ⟨(e.symm : E' →ₗ[𝕜] E), e.continuous_symm hcont⟩
  refine ⟨(‖M‖ + 1)⁻¹, by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ ‖M‖ * ‖e x‖ := by
    have := M.le_opNorm (e x)
    simpa [M] using this
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (e x)]

/-- **Th. `th:grapheFerme` (Graphe fermé).** Soient `E, F` des Banach et `L : E → F` linéaire.
Alors `L` est continue ssi son graphe `G := {(x, Lx) | x ∈ E}` est fermé dans `E × F`.
Preuve (différente du cours) : le sens réciproque est le théorème de Mathlib
`LinearMap.continuous_of_isClosed_graph`, sans passer par `corol:isomBanach`. -/
theorem th_grapheFerme [CompleteSpace E] [CompleteSpace F] (L : E →ₗ[𝕜] F) :
    Continuous L ↔ IsClosed (range fun x => (x, L x)) := by
  have hG : range (fun x => (x, L x)) = {p : E × F | p.2 = L p.1} := by
    ext ⟨x, y⟩
    simp only [mem_range, Prod.mk.injEq, mem_ofPred_eq]
    exact ⟨fun ⟨z, hz, hz'⟩ => hz ▸ hz'.symm, fun h => ⟨x, rfl, h.symm⟩⟩
  rw [hG]
  constructor
  · intro hL
    exact isClosed_eq continuous_snd (hL.comp continuous_fst)
  · intro hc
    exact L.continuous_of_isClosed_graph (by
      convert hc using 1
      ext p
      exact LinearMap.mem_graph_iff L p)

/-- **Corollaire (sans label) du `th:grapheFerme` : projection sur un supplémentaire.** Soit `E`
un Banach et `E = V ⊕ W` une décomposition en sev supplémentaires. La projection `P : E → V`
parallèlement à `W` (Mathlib : `Submodule.projectionOnto`) est continue ssi `V` et `W` sont
fermés.
Preuve (différente du cours) : la réciproque utilise `IsTopCompl.continuous_projectionOnto`
de Mathlib, et non le théorème du graphe fermé. -/
theorem corol_projectionContinue_iff [CompleteSpace E] (V W : Submodule 𝕜 E)
    (h : IsCompl V W) :
    Continuous (V.projectionOnto W h) ↔ IsClosed (V : Set E) ∧ IsClosed (W : Set E) := by
  constructor
  · intro hP
    let P : E →L[𝕜] V := ⟨V.projectionOnto W h, hP⟩
    refine ⟨?_, ?_⟩
    · have hV : (V : Set E) = {x | ((P x : V) : E) = x} := by
        ext x
        refine ⟨fun hx => ?_, fun hx => hx ▸ (P x).2⟩
        simpa [P] using hx
      rw [hV]
      exact isClosed_eq (continuous_subtype_val.comp P.continuous) continuous_id
    · have hW : (W : Set E) = P ⁻¹' {0} := by
        ext x
        simp only [SetLike.mem_coe, mem_preimage, mem_singleton_iff]
        change x ∈ W ↔ V.projectionOnto W h x = 0
        rw [← LinearMap.mem_ker, Submodule.ker_projectionOnto]
      rw [hW]
      exact isClosed_singleton.preimage P.continuous
  · rintro ⟨hV, hW⟩
    exact (Submodule.IsCompl.isTopCompl_of_isClosed h hV hW).continuous_projectionOnto

end M1Analyse
