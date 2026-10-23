/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# §1.4 La topologie faible (`subsec:evtlc`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section « La topologie faible » de la
sous-section `subsec:evtlc` (la sous-sous-section elle-même n'a pas de label).

Les topologies faible et *faible du cours sont celles de Mathlib : `WeakSpace 𝕜 E` (l'espace `E`
muni de la topologie faible) et `WeakDual 𝕜 E` (le dual topologique `E^*` muni de la topologie
*faible), tous deux des cas particuliers de `WeakBilin`.
-/

open Set Filter Topology Metric

namespace M1Analyse

section TopoFaible

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- **Déf. `def:topoFaible` (Topologie faible).** La topologie faible sur `E` (topologie de
`WeakSpace 𝕜 E`) est définie par la famille de semi-normes `x ↦ |l(x)|`, `l ∈ E^*`. -/
theorem def_topoFaible_faible :
    ∃ p : SeminormFamily 𝕜 (WeakSpace 𝕜 E) (StrongDual 𝕜 E),
      WithSeminorms p ∧ ∀ (l : StrongDual 𝕜 E) (x : E), p l x = ‖l x‖ :=
  ⟨(topDualPairing 𝕜 E).flip.toSeminormFamily,
    (topDualPairing 𝕜 E).flip.weakBilin_withSeminorms, fun _ _ => rfl⟩

/-- **Déf. `def:topoFaible` (Topologie *faible).** La topologie *faible sur `E^*` (topologie
de `WeakDual 𝕜 E`) est définie par la famille de semi-normes `l ↦ |l(x)|`, `x ∈ E`. -/
theorem def_topoFaible_faibleEtoile :
    ∃ p : SeminormFamily 𝕜 (WeakDual 𝕜 E) E,
      WithSeminorms p ∧ ∀ (l : WeakDual 𝕜 E) (x : E), p x l = ‖l x‖ :=
  ⟨(topDualPairing 𝕜 E).toSeminormFamily,
    (topDualPairing 𝕜 E).weakBilin_withSeminorms, fun _ _ => rfl⟩

/-- **Déf. `def:topoFaible`, caractérisation.** La topologie faible est la topologie la plus
grossière rendant continues toutes les formes linéaires `l ∈ E^*` : une topologie `t` sur `E`
rend continues toutes les `l ∈ E^*` si et seulement si elle est plus fine que la topologie
faible (en Mathlib, `t ≤ t'` signifie que `t` est plus fine que `t'`). -/
theorem def_topoFaible_faible_plusGrossiere (t : TopologicalSpace (WeakSpace 𝕜 E)) :
    (∀ l : StrongDual 𝕜 E, Continuous[t, _] (fun x => l ((toWeakSpace 𝕜 E).symm x))) ↔
      t ≤ instTopologicalSpaceWeakSpace 𝕜 E := by
  constructor
  · intro h
    rw [← continuous_id_iff_le]
    exact @WeakBilin.continuous_of_continuous_eval _ _ _ _ _ _ _ _ _ _
      (topDualPairing 𝕜 E).flip t id h
  · intro h l
    exact continuous_le_dom h (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip l :)

/-- **Déf. `def:topoFaible`, caractérisation.** La topologie *faible est la topologie la plus
grossière rendant continues les applications `l ∈ E^* ↦ l(x)`, `x ∈ E`. -/
theorem def_topoFaible_faibleEtoile_plusGrossiere (t : TopologicalSpace (WeakDual 𝕜 E)) :
    (∀ x : E, Continuous[t, _] (fun l : WeakDual 𝕜 E => l x)) ↔
      t ≤ instTopologicalSpaceWeakDual 𝕜 E := by
  constructor
  · intro h
    rw [← continuous_id_iff_le]
    exact (WeakDual.continuous_of_continuous_eval (g := id) h :)
  · intro h x
    exact continuous_le_dom h (WeakDual.eval_continuous (𝕜 := 𝕜) x :)

/-- **Remarque (sans label) suivant `prop:bouleMetrisable`.** Si `A : E → F` est linéaire
continue, alors `A` est continue de `(E, faible)` dans `(F, faible)`, et son adjoint
`A^* : l ↦ l ∘ A` est continu de `(F^*, *faible)` dans `(E^*, *faible)`. -/
theorem rem_operateur_continu_faible (A : E →L[𝕜] F) :
    Continuous (fun x : WeakSpace 𝕜 E => toWeakSpace 𝕜 F (A ((toWeakSpace 𝕜 E).symm x))) ∧
    Continuous (fun l : WeakDual 𝕜 F =>
      (StrongDual.toWeakDual ((WeakDual.toStrongDual l).comp A) : WeakDual 𝕜 E)) :=
  ⟨(WeakSpace.map A).continuous,
    WeakDual.continuous_of_continuous_eval fun x => WeakDual.eval_continuous (A x)⟩

end TopoFaible

section BouleMetrisable

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- La boule unité fermée `B^* = B'_{E^*}(0,1)` du dual (pour la norme d'opérateur), vue comme
partie de `WeakDual 𝕜 E`. -/
def bouleDuale (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Set (WeakDual 𝕜 E) :=
  WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1

/-- La distance `eqdef:met_faible_boule` : `d(u,v) = max_n min {2^{-n}, |u(x_n) - v(x_n)|}`
(le maximum est écrit comme un supremum, qui est atteint). -/
noncomputable def distFaible (x : ℕ → E) (u v : WeakDual 𝕜 E) : ℝ :=
  ⨆ n, min ((2 : ℝ)⁻¹ ^ n) ‖u (x n) - v (x n)‖

lemma distFaible_bddAbove (x : ℕ → E) (u v : WeakDual 𝕜 E) :
    BddAbove (range fun n => min ((2 : ℝ)⁻¹ ^ n) ‖u (x n) - v (x n)‖) :=
  ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))⟩

lemma le_distFaible (x : ℕ → E) (u v : WeakDual 𝕜 E) (n : ℕ) :
    min ((2 : ℝ)⁻¹ ^ n) ‖u (x n) - v (x n)‖ ≤ distFaible x u v :=
  le_ciSup (distFaible_bddAbove x u v) n

lemma distFaible_le {x : ℕ → E} {u v : WeakDual 𝕜 E} {c : ℝ}
    (h : ∀ n, min ((2 : ℝ)⁻¹ ^ n) ‖u (x n) - v (x n)‖ ≤ c) : distFaible x u v ≤ c :=
  ciSup_le h

lemma distFaible_self (x : ℕ → E) (u : WeakDual 𝕜 E) : distFaible x u u = 0 := by
  apply le_antisymm (distFaible_le fun n => by simp)
  exact (le_min (by positivity) (norm_nonneg _)).trans (le_distFaible x u u 0)

lemma distFaible_comm (x : ℕ → E) (u v : WeakDual 𝕜 E) :
    distFaible x u v = distFaible x v u := by
  simp only [distFaible, norm_sub_rev]

lemma distFaible_triangle (x : ℕ → E) (u v w : WeakDual 𝕜 E) :
    distFaible x u w ≤ distFaible x u v + distFaible x v w := by
  refine distFaible_le fun n => ?_
  have h1 := le_distFaible x u v n
  have h2 := le_distFaible x v w n
  have ht : ‖u (x n) - w (x n)‖ ≤ ‖u (x n) - v (x n)‖ + ‖v (x n) - w (x n)‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hs := norm_nonneg (u (x n) - v (x n))
  have hs' := norm_nonneg (v (x n) - w (x n))
  have ha : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  refine le_trans ?_ (add_le_add h1 h2)
  rcases min_cases ((2 : ℝ)⁻¹ ^ n) ‖u (x n) - v (x n)‖ with h | h <;>
    rcases min_cases ((2 : ℝ)⁻¹ ^ n) ‖v (x n) - w (x n)‖ with h' | h' <;>
    · rw [h.1, h'.1]
      first
        | exact (min_le_left _ _).trans (by linarith)
        | exact (min_le_right _ _).trans (by linarith)

/-- **Prop. `prop:bouleMetrisable`, cœur de la preuve (`eq:vois_faible_boule_evtlc`).**
Soit `(x_n)` une suite dense dans la boule unité de `E` (`adhérence({x_n}) = B'_E(0,1)`).
Pour `u ∈ B^*`, les boules
`{v ∈ B^* | d(u,v) < η}`, `η > 0`, forment une base de voisinages de `u` pour la topologie
*faible restreinte à `B^*`. -/
theorem prop_bouleMetrisable_nhds (x : ℕ → E)
    (hdense : closure (range x) = closedBall (0 : E) 1) (u : bouleDuale 𝕜 E) :
    (𝓝 u).HasBasis (fun η : ℝ => 0 < η)
      (fun η => {v : bouleDuale 𝕜 E | distFaible x (u : WeakDual 𝕜 E) v < η}) := by
  set s : ℝ → Set (bouleDuale 𝕜 E) :=
    fun η => {v : bouleDuale 𝕜 E | distFaible x (u : WeakDual 𝕜 E) v < η} with hs_def
  have hB : (⨅ η ∈ Ioi (0 : ℝ), 𝓟 (s η)).HasBasis (fun η => η ∈ Ioi (0 : ℝ)) s := by
    refine hasBasis_biInf_principal ?_ ⟨1, mem_Ioi.2 one_pos⟩
    intro a ha b hb
    refine ⟨min a b, mem_Ioi.2 (lt_min ha hb), fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hs_def, mem_ofPred_eq] at hv ⊢; exact hv.trans_le (min_le_left _ _)
    · simp only [hs_def, mem_ofPred_eq] at hv ⊢; exact hv.trans_le (min_le_right _ _)
  suffices h : 𝓝 u = ⨅ η ∈ Ioi (0 : ℝ), 𝓟 (s η) by rw [h]; exact hB
  -- norme d'un élément de `B^*`
  have hnorm : ∀ v : bouleDuale 𝕜 E, ∀ y : E, ‖(v : WeakDual 𝕜 E) y‖ ≤ ‖y‖ := by
    intro v y
    have hv : ‖WeakDual.toStrongDual (v : WeakDual 𝕜 E)‖ ≤ 1 := by
      simpa [bouleDuale] using v.2
    calc ‖(v : WeakDual 𝕜 E) y‖ = ‖WeakDual.toStrongDual (v : WeakDual 𝕜 E) y‖ := rfl
      _ ≤ ‖WeakDual.toStrongDual (v : WeakDual 𝕜 E)‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := by gcongr
      _ = ‖y‖ := one_mul _
  apply le_antisymm
  · -- toute boule pour `d` est un voisinage
    refine hB.ge_iff.2 fun η hη => ?_
    have hη : 0 < η := hη
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hev : ∀ n : Fin (K + 1), ∀ᶠ v : bouleDuale 𝕜 E in 𝓝 u,
        ‖(u : WeakDual 𝕜 E) (x n) - (v : WeakDual 𝕜 E) (x n)‖ < η / 2 := by
      intro n
      have hc : Continuous fun v : bouleDuale 𝕜 E =>
          ‖(u : WeakDual 𝕜 E) (x n) - (v : WeakDual 𝕜 E) (x n)‖ :=
        (continuous_const.sub
          ((WeakDual.eval_continuous (x n)).comp continuous_subtype_val)).norm
      exact hc.continuousAt.eventually_lt continuous_const.continuousAt
        (by simpa using half_pos hη)
    filter_upwards [Filter.eventually_all.2 hev] with v hv
    show distFaible x (u : WeakDual 𝕜 E) v < η
    refine lt_of_le_of_lt (distFaible_le (c := max (η / 2) ((2 : ℝ)⁻¹ ^ K)) fun n => ?_)
      (max_lt (half_lt_self hη) hK)
    rcases le_or_gt n K with hn | hn
    · exact (min_le_right _ _).trans ((hv ⟨n, Nat.lt_succ_of_le hn⟩).le.trans (le_max_left _ _))
    · exact (min_le_left _ _).trans ((pow_le_pow_of_le_one (by norm_num) (by norm_num)
        hn.le).trans (le_max_right _ _))
  · -- tout voisinage contient une boule pour `d`
    rw [nhds_subtype, ← tendsto_iff_comap,
      (WeakDual.withSeminorms 𝕜 E).tendsto_nhds]
    intro y ε hε
    simp only [WeakDual.seminormFamily_apply]
    set R : ℝ := ‖y‖ + 1 with hR
    have hRpos : 0 < R := by positivity
    have hz : ((R : 𝕜))⁻¹ • y ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hRpos]
      rw [inv_mul_le_iff₀ hRpos]; linarith
    have hε3 : 0 < ε / (3 * R) := by positivity
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := Metric.mem_closure_iff.1 (hdense.ge hz) _ hε3
    have hη : 0 < min (ε / (3 * R)) ((2 : ℝ)⁻¹ ^ n) := lt_min hε3 (by positivity)
    refine hB.eventually_iff.2 ⟨_, hη, fun v hv => ?_⟩
    have hv' : distFaible x (u : WeakDual 𝕜 E) v < min (ε / (3 * R)) ((2 : ℝ)⁻¹ ^ n) := hv
    have h1 := (le_distFaible x (u : WeakDual 𝕜 E) v n).trans_lt hv'
    have h2 : ‖(u : WeakDual 𝕜 E) (x n) - (v : WeakDual 𝕜 E) (x n)‖ < ε / (3 * R) := by
      rcases min_cases ((2 : ℝ)⁻¹ ^ n) ‖(u : WeakDual 𝕜 E) (x n) - (v : WeakDual 𝕜 E) (x n)‖
        with h | h
      · rw [h.1] at h1; exact absurd (h1.trans_le (min_le_right _ _)) (lt_irrefl _)
      · rw [h.1] at h1; exact h1.trans_le (min_le_left _ _)
    set z : E := ((R : 𝕜))⁻¹ • y
    have hyz : y = (R : 𝕜) • z := by
      have : (R : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hRpos.ne'
      simp only [z, smul_smul, mul_inv_cancel₀ this, one_smul]
    clear_value z
    have hdz : dist z (x n) < ε / (3 * R) := hn
    have key : ‖(v : WeakDual 𝕜 E) z - (u : WeakDual 𝕜 E) z‖ < ε / R := by
      have e1 : ‖(v : WeakDual 𝕜 E) z - (v : WeakDual 𝕜 E) (x n)‖ < ε / (3 * R) := by
        rw [← map_sub]; exact (hnorm v _).trans_lt (by rwa [← dist_eq_norm])
      have e3 : ‖(u : WeakDual 𝕜 E) (x n) - (u : WeakDual 𝕜 E) z‖ < ε / (3 * R) := by
        rw [← map_sub]; exact (hnorm u _).trans_lt (by rwa [← dist_eq_norm, dist_comm])
      have e2 : ‖(v : WeakDual 𝕜 E) (x n) - (u : WeakDual 𝕜 E) (x n)‖ < ε / (3 * R) := by
        rwa [norm_sub_rev]
      have t1 := norm_sub_le_norm_sub_add_norm_sub ((v : WeakDual 𝕜 E) z)
        ((v : WeakDual 𝕜 E) (x n)) ((u : WeakDual 𝕜 E) z)
      have t2 := norm_sub_le_norm_sub_add_norm_sub ((v : WeakDual 𝕜 E) (x n))
        ((u : WeakDual 𝕜 E) (x n)) ((u : WeakDual 𝕜 E) z)
      have : ε / (3 * R) + ε / (3 * R) + ε / (3 * R) = ε / R := by field_simp; ring
      linarith
    show ‖(v : WeakDual 𝕜 E) y - (u : WeakDual 𝕜 E) y‖ < ε
    rw [hyz, map_smul, map_smul, ← smul_sub, norm_smul,
      RCLike.norm_ofReal, abs_of_pos hRpos]
    calc R * ‖(v : WeakDual 𝕜 E) z - (u : WeakDual 𝕜 E) z‖ < R * (ε / R) := by gcongr
      _ = ε := by field_simp

/-- **Prop. `prop:bouleMetrisable` (Métrisabilité de la topologie *faible restreinte à un
borné).** Soit `E` un evn séparable, `(x_n)` une suite dense dans la boule unité de `E`, et
`B^* = B'_{E^*}(0,1)`. Alors la restriction à `B^*` de la topologie *faible est métrisable,
pour la distance `d` de `eqdef:met_faible_boule` : il existe une structure d'espace métrique
sur `B^*`, de distance `d`, dont la topologie est la topologie *faible induite.
« `(x_n)` dense dans la boule unité » est formalisé par `adhérence({x_n}) = B'_E(0,1)`.
Remarque : l'hypothèse de séparabilité est redondante (elle découle de l'existence de `(x_n)`) ;
elle est conservée pour suivre le cours. -/
theorem prop_bouleMetrisable [TopologicalSpace.SeparableSpace E] (x : ℕ → E)
    (hdense : closure (range x) = closedBall (0 : E) 1) :
    ∃ m : MetricSpace (bouleDuale 𝕜 E),
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (bouleDuale 𝕜 E)) ∧
      ∀ u v : bouleDuale 𝕜 E, m.dist u v = distFaible x (u : WeakDual 𝕜 E) v := by
  have hb := prop_bouleMetrisable_nhds (𝕜 := 𝕜) x hdense
  refine ⟨MetricSpace.ofDistTopology (fun u v : bouleDuale 𝕜 E => distFaible x u.1 v.1)
    (fun u => distFaible_self x u.1) (fun u v => distFaible_comm x u.1 v.1)
    (fun u v w => distFaible_triangle x u.1 v.1 w.1) (fun s => ?_) (fun u v huv => ?_),
    rfl, fun _ _ => rfl⟩
  · rw [isOpen_iff_mem_nhds]
    exact forall₂_congr fun u _ => by
      simpa [and_comm, subset_def] using (hb u).mem_iff (t := s)
  · by_contra hne
    obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := t2_separation hne
    obtain ⟨η, hη, hηU⟩ := (hb u).mem_iff.1 (hU.mem_nhds huU)
    have hvU : v ∈ U := hηU (show distFaible x u.1 v.1 < η by rw [huv]; exact hη)
    exact Set.disjoint_left.1 hUV hvU hvV

/-- **Prop. `prop:bouleMetrisable`, version Mathlib.** Si `E` est séparable, la boule unité
fermée `B^*` du dual, munie de la topologie *faible, est métrisable
(`WeakDual.metrizable_of_isCompact`, via le théorème de Banach–Alaoglu). -/
theorem prop_bouleMetrisable_mathlib [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.MetrizableSpace (bouleDuale 𝕜 E) :=
  WeakDual.metrizable_of_isCompact 𝕜 E _ (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1)

end BouleMetrisable

end M1Analyse
