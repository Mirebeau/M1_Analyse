/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import M1Analyse.Dualite.HahnBanach

/-!
# §3.3 Formes géométriques de Hahn-Banach (`subsec:HahnBanachGeom`)

Source : `Include/Dualite.tex`, sous-section `subsec:HahnBanachGeom`, jusqu'au
`th:separFermeComp` inclus (la suite de la sous-section, après un en-tête de sous-section mis en
commentaire, est formalisée dans `M1Analyse/Dualite/CompaciteFaible.lean`).

La jauge du cours est à valeurs dans `[0, ∞]` avec la convention `inf ∅ = ∞` ; elle diffère donc
de la jauge `gauge` de Mathlib (à valeurs réelles, avec `inf ∅ = 0`) hors des points absorbés. On
l'introduit fidèlement (`M1Analyse.jauge`, à valeurs dans `ℝ≥0∞`). Les théorèmes de séparation
sont déduits de `geometric_hahn_banach_open` et `geometric_hahn_banach_closed_compact`.
-/

open Set Topology Filter Metric
open scoped ENNReal

namespace M1Analyse

section Jauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- La jauge `p_C(x) := inf {t > 0 | x/t ∈ C} ∈ [0, ∞]` d'une partie `C` (`prop:jaugeCvx`), avec
la convention `inf ∅ = ∞`.
Lien avec Mathlib : pour `C` convexe, absorbant et contenant `0`, coïncide avec la jauge `gauge`
de Mathlib (`prop_jaugeCvx_eq_gauge`) ; `gauge` est à valeurs réelles, avec la convention
`inf ∅ = 0`, d'où cette définition à valeurs dans `[0, ∞]` pour les parties non absorbantes. -/
noncomputable def jauge (C : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ // 0 < t ∧ t⁻¹ • x ∈ C}, ENNReal.ofReal t

variable {C : Set E}

theorem jauge_le_ofReal_of_mem {x : E} {t : ℝ} (ht : 0 < t) (hx : t⁻¹ • x ∈ C) :
    jauge C x ≤ ENNReal.ofReal t :=
  iInf_le (fun t : {t : ℝ // 0 < t ∧ t⁻¹ • x ∈ C} => ENNReal.ofReal t) ⟨t, ht, hx⟩

theorem inv_smul_mem_of_le (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {x : E} {s t : ℝ}
    (hs : 0 < s) (hx : s⁻¹ • x ∈ C) (hst : s ≤ t) : t⁻¹ • x ∈ C := by
  have ht : 0 < t := hs.trans_le hst
  have h := hC.smul_mem_of_zero_mem h0 hx ⟨div_nonneg hs.le ht.le, (div_le_one ht).2 hst⟩
  convert h using 1
  rw [smul_smul]
  congr 1
  field_simp

theorem jauge_le_ofReal_iff (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {x : E} {r : ℝ}
    (hr : 0 ≤ r) : jauge C x ≤ ENNReal.ofReal r ↔ ∀ t, r < t → t⁻¹ • x ∈ C := by
  constructor
  · intro h t hrt
    have htpos : 0 < t := hr.trans_lt hrt
    have hlt : jauge C x < ENNReal.ofReal t :=
      h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff htpos).2 hrt)
    obtain ⟨⟨s, hs, hsx⟩, hst⟩ := iInf_lt_iff.1 hlt
    exact inv_smul_mem_of_le hC h0 hs hsx ((ENNReal.ofReal_lt_ofReal_iff htpos).1 hst).le
  · intro h
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := hε
    have := jauge_le_ofReal_of_mem (C := C) (x := x) (t := r + ε) (by positivity)
      (h _ (lt_add_of_pos_right r hε'))
    rwa [ENNReal.ofReal_add hr ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this

private theorem ennreal_le_of_forall_ofReal {a b : ℝ≥0∞}
    (h : ∀ r : ℝ, 0 ≤ r → b ≤ ENNReal.ofReal r → a ≤ ENNReal.ofReal r) : a ≤ b := by
  rcases eq_or_ne b ⊤ with hb | hb
  · simp [hb]
  · have := h b.toReal ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal hb])
    rwa [ENNReal.ofReal_toReal hb] at this

theorem jauge_zero (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) : jauge C 0 = 0 := by
  refine le_antisymm ?_ bot_le
  rw [← ENNReal.ofReal_zero]
  exact (jauge_le_ofReal_iff hC h0 le_rfl).2 fun t _ => by simpa using h0

theorem jauge_smul (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    jauge C (c • x) = ENNReal.ofReal c * jauge C x := by
  rcases hc.eq_or_lt with rfl | hpos
  · simp [jauge_zero hC h0]
  have key : ∀ r : ℝ, 0 ≤ r →
      (jauge C (c • x) ≤ ENNReal.ofReal r ↔ ENNReal.ofReal c * jauge C x ≤ ENNReal.ofReal r) := by
    intro r hr
    rw [jauge_le_ofReal_iff hC h0 hr, mul_comm, ← ENNReal.le_div_iff_mul_le
      (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_div_of_pos hpos, jauge_le_ofReal_iff hC h0 (by positivity)]
    constructor
    · intro h t ht
      have h' := h (c * t) (by rwa [div_lt_iff₀ hpos, mul_comm] at ht)
      convert h' using 1
      rw [smul_smul]
      congr 1
      field_simp
    · intro h t ht
      have h' := h (t / c) (by rwa [div_lt_div_iff_of_pos_right hpos])
      convert h' using 1
      rw [smul_smul]
      congr 1
      field_simp
  exact le_antisymm (ennreal_le_of_forall_ofReal fun r hr h => (key r hr).2 h)
    (ennreal_le_of_forall_ofReal fun r hr h => (key r hr).1 h)

theorem jauge_add_le (hC : Convex ℝ C) (x y : E) :
    jauge C (x + y) ≤ jauge C x + jauge C y := by
  refine ENNReal.le_iInf_add_iInf fun ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩ => ?_
  have hst : 0 < s + t := add_pos hs ht
  have hmem : (s + t)⁻¹ • (x + y) ∈ C := by
    have h := hC hsx hty (a := s / (s + t)) (b := t / (s + t)) (by positivity) (by positivity)
      (by field_simp)
    convert h using 1
    rw [smul_add, smul_smul, smul_smul]
    congr 2 <;> field_simp
  calc jauge C (x + y) ≤ ENNReal.ofReal (s + t) := jauge_le_ofReal_of_mem hst hmem
    _ = ENNReal.ofReal s + ENNReal.ofReal t := ENNReal.ofReal_add hs.le ht.le

theorem jauge_lt_one_subset (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    {x | jauge C x < 1} ⊆ C := by
  intro x hx
  obtain ⟨⟨s, hs, hsx⟩, hlt⟩ := iInf_lt_iff.1 (show jauge C x < 1 from hx)
  have := inv_smul_mem_of_le hC h0 hs hsx (ENNReal.ofReal_lt_one.1 hlt).le
  simpa using this

theorem subset_jauge_le_one : C ⊆ {x | jauge C x ≤ 1} := by
  intro x hx
  have := jauge_le_ofReal_of_mem (C := C) (x := x) one_pos (by simpa using hx)
  simpa using this

/-- **Prop. `prop:jaugeCvx` (Jauge d'un convexe).** Soit `C` un convexe contenant `0` d'un
`ℝ`-ev `E`. La jauge `p_C : E → [0, ∞]` satisfait `p_C(λx) = λ p_C(x)` (convention
`0 × ∞ = 0`) et `p_C(x+y) ≤ p_C(x) + p_C(y)` pour `λ ≥ 0`, `x, y ∈ E`, et
`{p_C < 1} ⊆ C ⊆ {p_C ≤ 1}`. -/
theorem prop_jaugeCvx (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    (∀ c : ℝ, 0 ≤ c → ∀ x, jauge C (c • x) = ENNReal.ofReal c * jauge C x) ∧
    (∀ x y, jauge C (x + y) ≤ jauge C x + jauge C y) ∧
    ({x | jauge C x < 1} ⊆ C ∧ C ⊆ {x | jauge C x ≤ 1}) :=
  ⟨fun _ hc x => jauge_smul hC h0 hc x, jauge_add_le hC,
    jauge_lt_one_subset hC h0, subset_jauge_le_one⟩

/-- **Prop. `prop:jaugeCvx`, cas fini.** Si `p_C` prend des valeurs finies, alors
`x ↦ p_C(x) ∈ ℝ` est sous-linéaire (`def:sousLin`). -/
theorem prop_jaugeCvx_sousLin (hC : Convex ℝ C) (h0 : (0 : E) ∈ C)
    (hfin : ∀ x, jauge C x ≠ ⊤) : SousLineaire (fun x => (jauge C x).toReal) := by
  refine ⟨fun c hc x => ?_, fun x y => ?_⟩
  · simp only [jauge_smul hC h0 hc, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  · rw [← ENNReal.toReal_add (hfin x) (hfin y)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x, hfin y⟩) (jauge_add_le hC x y)

/-- **Prop. `prop:jaugeCvx`, cas symétrique.** Si `p_C` prend des valeurs finies et est
symétrique, alors c'est une semi-norme. -/
theorem prop_jaugeCvx_semiNorme (hC : Convex ℝ C) (h0 : (0 : E) ∈ C)
    (hfin : ∀ x, jauge C x ≠ ⊤) (hsym : ∀ x, jauge C (-x) = jauge C x) :
    ∃ q : Seminorm ℝ E, ∀ x, q x = (jauge C x).toReal := by
  have hs := prop_jaugeCvx_sousLin hC h0 hfin
  refine ⟨Seminorm.of (fun x => (jauge C x).toReal) hs.2 fun a x => ?_, fun _ => rfl⟩
  have hhom : ∀ c : ℝ, 0 ≤ c → ∀ y, (jauge C (c • y)).toReal = c * (jauge C y).toReal :=
    hs.1
  rcases le_or_gt 0 a with ha | ha
  · rw [hhom a ha, Real.norm_eq_abs, abs_of_nonneg ha]
  · have : a • x = -((-a) • x) := by rw [neg_smul, neg_neg]
    rw [this, hsym, hhom (-a) (by linarith), Real.norm_eq_abs, abs_of_neg ha]

/-- **Prop. `prop:jaugeCvx`, lien avec Mathlib.** Si `C` est convexe, contient `0` et est
absorbant, la jauge du cours coïncide avec la jauge `gauge` de Mathlib (à valeurs réelles). -/
theorem prop_jaugeCvx_eq_gauge (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (habs : Absorbent ℝ C)
    (x : E) : jauge C x = ENNReal.ofReal (gauge C x) := by
  have key : ∀ r : ℝ, 0 ≤ r →
      (jauge C x ≤ ENNReal.ofReal r ↔ ENNReal.ofReal (gauge C x) ≤ ENNReal.ofReal r) := by
    intro r hr
    rw [jauge_le_ofReal_iff hC h0 hr, ENNReal.ofReal_le_ofReal_iff hr]
    constructor
    · intro h
      refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
      have ht0 : 0 < t := hr.trans_lt ht
      exact gauge_le_of_mem ht0.le ((mem_smul_set_iff_inv_smul_mem₀ ht0.ne' _ _).2 (h t ht))
    · intro h t ht
      obtain ⟨b, hb, hbt, hxb⟩ := exists_lt_of_gauge_lt habs (h.trans_lt ht)
      exact inv_smul_mem_of_le hC h0 hb ((mem_smul_set_iff_inv_smul_mem₀ hb.ne' _ _).1 hxb)
        hbt.le
  exact le_antisymm (ennreal_le_of_forall_ofReal fun r hr h => (key r hr).2 h)
    (ennreal_le_of_forall_ofReal fun r hr h => (key r hr).1 h)

end Jauge

section EVN

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- **Lemme `lem:jaugeOuvertCvx`, cas ouvert.** Soit `C` un convexe ouvert contenant `0` d'un
`ℝ`-evn. Alors `p_C` est à valeurs finies, `p_C : E → ℝ` est lipschitzienne, et
`C = {p_C < 1}`. -/
theorem lem_jaugeOuvertCvx_ouvert (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hO : IsOpen C) :
    (∀ x, jauge C x ≠ ⊤) ∧ (∃ K, LipschitzWith K (fun x => (jauge C x).toReal)) ∧
      C = {x | jauge C x < 1} := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 h0
  have hbound : ∀ h : E, jauge C h ≤ ENNReal.ofReal (‖h‖ / r) := by
    intro h
    refine (jauge_le_ofReal_iff hC h0 (by positivity)).2 fun t ht => hball ?_
    have htpos : 0 < t := lt_of_le_of_lt (by positivity) ht
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos,
      inv_mul_lt_iff₀ htpos]
    rw [div_lt_iff₀ hr] at ht
    linarith
  have hfin : ∀ x, jauge C x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound x)
  refine ⟨hfin, ⟨_, LipschitzWith.of_le_add_mul' (1 / r) fun x y => ?_⟩, ?_⟩
  · have h1 : (jauge C x).toReal ≤ (jauge C y).toReal + (jauge C (x - y)).toReal := by
      rw [← ENNReal.toReal_add (hfin y) (hfin _)]
      refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin y, hfin _⟩) ?_
      have := jauge_add_le hC y (x - y)
      rwa [add_sub_cancel] at this
    have h2 : (jauge C (x - y)).toReal ≤ ‖x - y‖ / r :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound _)
    rw [dist_eq_norm, one_div_mul_eq_div]
    linarith
  · refine Subset.antisymm (fun x hx => ?_) (jauge_lt_one_subset hC h0)
    have hT : Tendsto (fun t : ℝ => t • x) (𝓝 1) (𝓝 x) := by
      have hc : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
      simpa using hc.tendsto 1
    obtain ⟨t, htC, ht1⟩ :=
      (((hT.eventually (hO.mem_nhds hx)).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have := jauge_le_ofReal_of_mem (C := C) (x := x) (inv_pos.2 ht0) (by rwa [inv_inv])
    exact lt_of_le_of_lt this (ENNReal.ofReal_lt_one.2 (inv_lt_one_of_one_lt₀ ht1))

/-- **Lemme `lem:jaugeOuvertCvx`, cas fermé.** Soit `C` un convexe fermé contenant `0` d'un
`ℝ`-evn. Alors `p_C : E → [0, ∞]` est semi-continue inférieurement, et `C = {p_C ≤ 1}`. -/
theorem lem_jaugeOuvertCvx_ferme (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hF : IsClosed C) :
    LowerSemicontinuous (jauge C) ∧ C = {x | jauge C x ≤ 1} := by
  have hpre : ∀ r : ℝ, 0 ≤ r →
      {x | jauge C x ≤ ENNReal.ofReal r} = ⋂ t ∈ Ioi r, {x | t⁻¹ • x ∈ C} := by
    intro r hr
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_Ioi]
    exact jauge_le_ofReal_iff hC h0 hr
  refine ⟨lowerSemicontinuous_iff_isClosed_preimage.2 fun y => ?_, ?_⟩
  · rcases eq_or_ne y ⊤ with rfl | hy
    · simp
    · have : jauge C ⁻¹' Iic y = {x | jauge C x ≤ ENNReal.ofReal y.toReal} := by
        rw [ENNReal.ofReal_toReal hy]; rfl
      rw [this, hpre _ ENNReal.toReal_nonneg]
      exact isClosed_biInter fun t _ => hF.preimage (continuous_const_smul _)
  · refine Subset.antisymm subset_jauge_le_one fun x hx => ?_
    have hx' : ∀ t : ℝ, 1 < t → t⁻¹ • x ∈ C := by
      have : jauge C x ≤ ENNReal.ofReal 1 := by simpa using hx
      exact (jauge_le_ofReal_iff hC h0 zero_le_one).1 this
    have hT : Tendsto (fun t : ℝ => t⁻¹ • x) (𝓝[>] 1) (𝓝 x) := by
      have : ContinuousAt (fun t : ℝ => t⁻¹ • x) 1 :=
        ((continuousAt_inv₀ one_ne_zero).smul continuousAt_const)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    exact hF.mem_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hx' t ht)

/-- **Th. `th:separOuvertPt` (Séparation d'un ouvert convexe et d'un point).** Soient `E` un evn,
`C ⊆ E` un ouvert convexe contenant `0` et `x ∈ E \ C`. Il existe `φ ∈ E^*` telle que
`φ(x) = 1` et `φ < 1` sur `C`. -/
theorem th_separOuvertPt (hC : Convex ℝ C) (hO : IsOpen C) (h0 : (0 : E) ∈ C) {x : E}
    (hx : x ∉ C) : ∃ φ : StrongDual ℝ E, φ x = 1 ∧ ∀ y ∈ C, φ y < 1 := by
  obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_open hC hO (convex_singleton x)
    (disjoint_singleton_right.2 hx)
  have hu : 0 < u := by simpa using hfC 0 h0
  have hfxu : u ≤ f x := hfx x rfl
  have hfx0 : 0 < f x := hu.trans_le hfxu
  refine ⟨(f x)⁻¹ • f, by simp [hfx0.ne'], fun y hy => ?_⟩
  simp only [smul_apply, smul_eq_mul]
  rw [inv_mul_lt_one₀ hfx0]
  exact (hfC y hy).trans_le hfxu

/-- **Cor. `corol:separOuvertPt`, premier point.** Si `C` est un ouvert convexe d'un evn `E` ne
contenant pas `0`, il existe `φ ∈ E^*` telle que `φ > 0` sur `C`. -/
theorem corol_separOuvertPt_zero (hC : Convex ℝ C) (hO : IsOpen C) (h0 : (0 : E) ∉ C) :
    ∃ φ : StrongDual ℝ E, ∀ y ∈ C, 0 < φ y := by
  obtain ⟨f, u, hfC, hf0⟩ := geometric_hahn_banach_open hC hO (convex_singleton 0)
    (disjoint_singleton_right.2 h0)
  have hu : u ≤ 0 := by simpa using hf0 0 rfl
  exact ⟨-f, fun y hy => by simpa using (hfC y hy).trans_le hu⟩

/-- **Cor. `corol:separOuvertPt`, second point.** Soient `A` un convexe et `B` un ouvert convexe
d'un evn `E`, non vides et disjoints. Il existe `φ ∈ E^*` et `α ∈ ℝ` tels que
`φ(a) ≤ α < φ(b)` pour tous `a ∈ A`, `b ∈ B`. -/
theorem corol_separOuvertPt {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hBo : IsOpen B)
    (_hAne : A.Nonempty) (_hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ (φ : StrongDual ℝ E) (α : ℝ), ∀ a ∈ A, ∀ b ∈ B, φ a ≤ α ∧ α < φ b := by
  obtain ⟨f, u, hfB, hfA⟩ := geometric_hahn_banach_open hB hBo hA hAB.symm
  refine ⟨-f, -u, fun a ha b hb => ⟨?_, ?_⟩⟩
  · simpa using hfA a ha
  · simpa using hfB b hb

/-- **Th. `th:separFermeComp` (Séparation stricte d'un fermé et d'un compact convexes).** Soient
`A, B ⊆ E` convexes, non vides, disjoints, avec `A` fermé et `B` compact. Il existe `φ ∈ E^*`
telle que `sup_A φ < inf_B φ`. La clause `BddAbove (φ '' A)` explicite que `sup_A φ` est fini
(en Lean, le `sSup` d'une partie non majorée de `ℝ` vaut `0` par convention). -/
theorem th_separFermeComp {A B : Set E} (hA : Convex ℝ A) (hAf : IsClosed A) (hB : Convex ℝ B)
    (hBc : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ φ : StrongDual ℝ E, BddAbove (φ '' A) ∧ sSup (φ '' A) < sInf (φ '' B) := by
  obtain ⟨f, u, v, hfA, huv, hfB⟩ := geometric_hahn_banach_closed_compact hA hAf hB hBc hAB
  refine ⟨f, ⟨u, by rintro _ ⟨a, ha, rfl⟩; exact (hfA a ha).le⟩, ?_⟩
  have h1 : sSup (f '' A) ≤ u :=
    csSup_le (hAne.image f) (by rintro _ ⟨a, ha, rfl⟩; exact (hfA a ha).le)
  have h2 : v ≤ sInf (f '' B) :=
    le_csInf (hBne.image f) (by rintro _ ⟨b, hb, rfl⟩; exact (hfB b hb).le)
  linarith

/-- **Th. `th:separFermeComp`, dernier point.** Sous les mêmes hypothèses, si `0 ∈ A`, on peut
choisir `φ ∈ E^*` telle que `sup_A φ < 1 < inf_B φ`. La clause `BddAbove (φ '' A)` explicite
que `sup_A φ` est fini (en Lean, le `sSup` d'une partie non majorée de `ℝ` vaut `0`). -/
theorem th_separFermeComp_zero {A B : Set E} (hA : Convex ℝ A) (hAf : IsClosed A)
    (hB : Convex ℝ B) (hBc : IsCompact B) (h0 : (0 : E) ∈ A) (hBne : B.Nonempty)
    (hAB : Disjoint A B) :
    ∃ φ : StrongDual ℝ E, BddAbove (φ '' A) ∧ sSup (φ '' A) < 1 ∧ 1 < sInf (φ '' B) := by
  obtain ⟨f, u, v, hfA, huv, hfB⟩ := geometric_hahn_banach_closed_compact hA hAf hB hBc hAB
  have hu : 0 < u := by simpa using hfA 0 h0
  set m := (u + v) / 2 with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  refine ⟨m⁻¹ • f, ⟨m⁻¹ * u, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    simp only [smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hfA a ha).le (inv_nonneg.2 hmpos.le)
  · have : sSup ((m⁻¹ • f) '' A) ≤ m⁻¹ * u :=
      csSup_le (Set.Nonempty.image _ (⟨0, h0⟩ : A.Nonempty)) (by
        rintro _ ⟨a, ha, rfl⟩
        simp only [smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hfA a ha).le (inv_nonneg.2 hmpos.le))
    refine this.trans_lt ?_
    rw [inv_mul_lt_one₀ hmpos, hm]
    linarith
  · have : m⁻¹ * v ≤ sInf ((m⁻¹ • f) '' B) :=
      le_csInf (hBne.image _) (by
        rintro _ ⟨b, hb, rfl⟩
        simp only [smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hfB b hb).le (inv_nonneg.2 hmpos.le))
    refine lt_of_lt_of_le ?_ this
    rw [one_lt_inv_mul₀ hmpos, hm]
    linarith

end EVN

end M1Analyse
