/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# §3.3 Compacité en dimension finie (`subsec:compactRd`)

Source : `Include/Compacite.tex`, sous-section `subsec:compactRd`.

Les objets du cours sont ceux de Mathlib : `ℝ^d` est `EuclideanSpace ℝ (Fin d)`, un evn sur
`𝕂 ∈ {ℝ, ℂ}` est `[NormedAddCommGroup E] [NormedSpace 𝕜 E]` avec `[RCLike 𝕜]`, la dimension
finie est `FiniteDimensional 𝕜 E`, `B'_E(0,1)` est `closedBall (0 : E) 1`, `B_E(x,1)` est
`ball x 1`, et `d(x, F)` est `Metric.infDist x F`. Pour l'équivalence des normes, `E` est un
simple espace vectoriel de dimension finie et les deux normes sont des fonctions `E → ℝ`
satisfaisant les axiomes de `def:norme` (comme dans `def_norme_of_axioms`).
-/

open Set Filter Topology Metric

namespace M1Analyse

/-- **Prop. `prop:compSsiFermeBorne`.** Une partie de `ℝ^d` est compacte ssi elle est fermée et
bornée. -/
theorem prop_compSsiFermeBorne {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

/-- **Cor. `corol:bornesAtteintes` (Bornes atteintes).** Une application continue d'un compact
non vide `X` dans `ℝ` est bornée et atteint ses bornes. -/
theorem corol_bornesAtteintes {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Nonempty X] {f : X → ℝ} (hf : Continuous f) :
    BddBelow (range f) ∧ BddAbove (range f) ∧
      (∃ x, ∀ y, f x ≤ f y) ∧ (∃ x, ∀ y, f y ≤ f x) := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨(isCompact_range hf).bddBelow, (isCompact_range hf).bddAbove,
    ⟨a, fun y => ha (mem_univ y)⟩, ⟨b, fun y => hb (mem_univ y)⟩⟩

section NormesEquiv

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Lemme auxiliaire pour `corol:normesEquivRd` : en dimension finie, une semi-norme `M` est
majorée par un multiple de toute norme `N`. -/
private theorem majoration_seminorme (N M : E → ℝ) (h₀ : ∀ x, 0 ≤ N x)
    (hsep : ∀ x, x ≠ 0 → 0 < N x) (hhom : ∀ (x : E) (c : 𝕜), N (c • x) = ‖c‖ * N x)
    (htri : ∀ x y, N (x + y) ≤ N x + N y)
    (hMhom : ∀ (x : E) (c : 𝕜), M (c • x) = ‖c‖ * M x)
    (hMtri : ∀ x y, M (x + y) ≤ M x + M y) :
    ∃ C > 0, ∀ x, M x ≤ C * N x := by
  let _ : Norm E := ⟨N⟩
  have core : NormedSpace.Core 𝕜 E :=
    { norm_nonneg := h₀
      norm_smul := fun c x => hhom x c
      norm_triangle := htri
      norm_eq_zero_iff := fun x => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · by_contra hx
          exact (hsep x hx).ne' h
        · subst h
          have := hhom 0 0
          simp only [smul_zero, norm_zero, zero_mul] at this
          exact this }
  let _ : NormedAddCommGroup E := NormedAddCommGroup.ofCore core
  let _ : NormedSpace 𝕜 E := NormedSpace.ofCore core
  have hM0 : M 0 = 0 := by simpa using hMhom 0 0
  have hM : ∀ y, 0 ≤ M y := fun y => by
    have h1 := hMtri y (-y)
    have h2 : M (-y) = M y := by simpa using hMhom y (-1)
    rw [add_neg_cancel, hM0, h2] at h1
    linarith
  let b := Module.finBasis 𝕜 E
  let L : Fin (Module.finrank 𝕜 E) → E →L[𝕜] 𝕜 :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hS : 0 ≤ ∑ i, ‖L i‖ * M (b i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hM _)
  refine ⟨∑ i, ‖L i‖ * M (b i) + 1, by linarith, fun x => ?_⟩
  calc M x = M (∑ i, b.repr x i • b i) := by rw [b.sum_repr x]
    _ ≤ ∑ i, M (b.repr x i • b i) := Finset.le_sum_of_subadditive M hM0.le hMtri _ _
    _ = ∑ i, ‖L i x‖ * M (b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hMhom]
        rfl
    _ ≤ ∑ i, ‖L i‖ * N x * M (b i) := by
        gcongr with i
        · exact hM _
        · exact (L i).le_opNorm x
    _ ≤ (∑ i, ‖L i‖ * M (b i) + 1) * N x := by
        rw [add_mul, Finset.sum_mul, one_mul]
        have : ∑ i, ‖L i‖ * N x * M (b i) = ∑ i, ‖L i‖ * M (b i) * N x :=
          Finset.sum_congr rfl fun i _ => by ring
        linarith [h₀ x]

/-- **Cor. `corol:normesEquivRd` (Équivalence des normes en dimension finie).** Soit `E` un
espace vectoriel de dimension finie, muni de deux normes `N₁ = ‖·‖` et `N₂ = ‖·‖'` (au sens
de `def:norme`). Alors il existe `C, c > 0` tels que `c ‖x‖ ≤ ‖x‖' ≤ C ‖x‖` pour tout `x`. -/
theorem corol_normesEquivRd (N₁ N₂ : E → ℝ)
    (h₁₀ : ∀ x, 0 ≤ N₁ x) (h₁sep : ∀ x, x ≠ 0 → 0 < N₁ x)
    (h₁hom : ∀ (x : E) (c : 𝕜), N₁ (c • x) = ‖c‖ * N₁ x)
    (h₁tri : ∀ x y, N₁ (x + y) ≤ N₁ x + N₁ y)
    (h₂₀ : ∀ x, 0 ≤ N₂ x) (h₂sep : ∀ x, x ≠ 0 → 0 < N₂ x)
    (h₂hom : ∀ (x : E) (c : 𝕜), N₂ (c • x) = ‖c‖ * N₂ x)
    (h₂tri : ∀ x y, N₂ (x + y) ≤ N₂ x + N₂ y) :
    ∃ c > 0, ∃ C > 0, ∀ x, c * N₁ x ≤ N₂ x ∧ N₂ x ≤ C * N₁ x := by
  obtain ⟨C, hC, hC'⟩ := majoration_seminorme N₁ N₂ h₁₀ h₁sep h₁hom h₁tri h₂hom h₂tri
  obtain ⟨D, hD, hD'⟩ := majoration_seminorme N₂ N₁ h₂₀ h₂sep h₂hom h₂tri h₁hom h₁tri
  refine ⟨D⁻¹, inv_pos.2 hD, C, hC, fun x => ⟨?_, hC' x⟩⟩
  rw [inv_mul_le_iff₀ hD]
  exact hD' x

end NormesEquiv

section Riesz

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Lemme `lem:normaleRiesz` (Riesz).** Soit `E` un evn et `F ⊊ E` un sous-espace vectoriel
strict fermé. Pour tout `ρ < 1`, il existe `x ∈ B'_E(0,1)` tel que `d(x, F) ≥ ρ`. -/
theorem lem_normaleRiesz {F : Submodule 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : F ≠ ⊤)
    {ρ : ℝ} (hρ : ρ < 1) : ∃ x ∈ closedBall (0 : E) 1, ρ ≤ infDist x F := by
  obtain ⟨x, -, hx, h⟩ := riesz_lemma_of_lt_one hFc (by
    by_contra h'
    push Not at h'
    exact hF (Submodule.eq_top_iff'.2 h')) hρ
  refine ⟨x, by simp [hx], (le_infDist ⟨0, F.zero_mem⟩).2 fun y hy => ?_⟩
  rw [dist_eq_norm]
  exact h y hy

/-- **Lemme `lem:normaleRiesz`, cas de la dimension finie.** Si de plus `F` est de dimension
finie, alors il existe `x ∈ B'_E(0,1)` tel que `d(x, F) = 1`. -/
theorem lem_normaleRiesz_dimFinie {F : Submodule 𝕜 E} (_hFc : IsClosed (F : Set E))
    (hF : F ≠ ⊤) [FiniteDimensional 𝕜 F] : ∃ x ∈ closedBall (0 : E) 1, infDist x F = 1 := by
  have : ProperSpace F := FiniteDimensional.proper_rclike 𝕜 F
  obtain ⟨u, hu⟩ : ∃ u : E, u ∉ F := by
    by_contra h'
    push Not at h'
    exact hF (Submodule.eq_top_iff'.2 h')
  -- un point `v ∈ F` réalisant la distance `d(u, F)`
  obtain ⟨v, hv⟩ : ∃ v : F, ∀ y : F, dist u v ≤ dist u y := by
    refine Continuous.exists_forall_le (continuous_const.dist continuous_subtype_val) ?_
    refine tendsto_atTop_mono (fun y : F => ?_)
      ((tendsto_dist_right_cocompact_atTop (0 : F)).atTop_add (tendsto_const_nhds (x := -‖u‖)))
    have := dist_triangle (y : E) u 0
    simp only [dist_zero_right, Submodule.norm_coe] at this ⊢
    rw [dist_comm] at this
    linarith
  have huv : u - v ≠ 0 := sub_ne_zero.2 fun h => hu (h ▸ v.2)
  have hd : infDist u F = ‖u - v‖ := by
    refine le_antisymm (dist_eq_norm u v ▸ infDist_le_dist_of_mem v.2)
      ((le_infDist ⟨0, F.zero_mem⟩).2 fun y hy => ?_)
    rw [← dist_eq_norm]
    exact hv ⟨y, hy⟩
  set r := ‖u - v‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 huv
  have hnorm : ‖((r⁻¹ : ℝ) : 𝕜) • (u - v)‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hrpos), ← hr,
      inv_mul_cancel₀ hrpos.ne']
  refine ⟨((r⁻¹ : ℝ) : 𝕜) • (u - v), by rw [mem_closedBall, dist_zero_right, hnorm],
    le_antisymm ?_ ?_⟩
  · calc infDist (((r⁻¹ : ℝ) : 𝕜) • (u - v)) F ≤ dist (((r⁻¹ : ℝ) : 𝕜) • (u - v)) 0 :=
          infDist_le_dist_of_mem F.zero_mem
      _ = 1 := by rw [dist_zero_right, hnorm]
  · refine (le_infDist ⟨0, F.zero_mem⟩).2 fun y hy => ?_
    have hmem : (v : E) + ((r : ℝ) : 𝕜) • y ∈ F := F.add_mem v.2 (F.smul_mem _ hy)
    have h1 : r ≤ ‖u - ((v : E) + ((r : ℝ) : 𝕜) • y)‖ := by
      have := infDist_le_dist_of_mem (x := u) hmem
      rwa [hd, dist_eq_norm] at this
    have h2 : ((r⁻¹ : ℝ) : 𝕜) • (u - v) - y =
        ((r⁻¹ : ℝ) : 𝕜) • (u - ((v : E) + ((r : ℝ) : 𝕜) • y)) := by
      rw [sub_add_eq_sub_sub, smul_sub _ (u - v), smul_smul, ← RCLike.ofReal_mul,
        inv_mul_cancel₀ hrpos.ne', RCLike.ofReal_one, one_smul]
    rw [dist_eq_norm, h2, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hrpos)]
    rw [le_inv_mul_iff₀ hrpos, mul_one]
    exact h1

/-- **Th. `th:bouleCompRiesz` (Compacité de Riesz).** Pour tout evn `E`, sont équivalents :
(i) `E` est de dimension finie ; (ii) `B'_E(0,1)` est compacte ; (iii) `B'_E(0,1)` est
recouverte par un nombre fini de boules ouvertes `B_E(x_i, 1)`. -/
theorem th_bouleCompRiesz :
    List.TFAE [FiniteDimensional 𝕜 E, IsCompact (closedBall (0 : E) 1),
      ∃ t : Finset E, closedBall (0 : E) 1 ⊆ ⋃ x ∈ t, ball x 1] := by
  tfae_have 1 → 2 := fun _ => by
    have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
    exact isCompact_closedBall 0 1
  tfae_have 2 → 3 := fun h =>
    h.elim_finite_subcover (fun x : E => ball x 1) (fun _ => isOpen_ball)
      (fun x _ => mem_iUnion.2 ⟨x, mem_ball_self one_pos⟩)
  tfae_have 3 → 1 := fun ⟨t, ht⟩ => by
    by_contra hfin
    set F := Submodule.span 𝕜 (t : Set E)
    have hF : F ≠ ⊤ := fun h => hfin (by
      have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := h ▸ inferInstance
      exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl))
    obtain ⟨x, hx, hdx⟩ := lem_normaleRiesz_dimFinie F.closed_of_finiteDimensional hF
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
    have := infDist_le_dist_of_mem (x := x) (Submodule.subset_span hy : y ∈ (F : Set E))
    rw [mem_ball] at hxy
    linarith
  tfae_finish

end Riesz

end M1Analyse
