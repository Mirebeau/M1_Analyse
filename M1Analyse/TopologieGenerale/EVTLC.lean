/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# §1.4 Espaces vectoriels topologiques localement convexes (`subsec:evtlc`)

Source : `Include/TopologieGenerale.tex`, sous-section `subsec:evtlc`, partie générale
(avant `Exemples d'espaces fonctionnels`).

Un evtlc `(E, (|·|_i)_{i ∈ I})` est représenté par une famille de semi-normes Mathlib
`p : SeminormFamily 𝕜 E ι` et une topologie `TopologicalSpace E` vérifiant `WithSeminorms p`
(la topologie de `E` est celle définie par `p`). Le maximum fini `max_{i ∈ I₀} |x|_i` du cours
est `(I₀.sup p) x` (qui vaut `0` si `I₀ = ∅`).

Le seul objet propre au cours est la distance `evtlcDist` de `eqdef:evtlc_dist`, associée à une
famille dénombrable de semi-normes.
-/

open Set Filter Topology Bornology Pointwise

namespace M1Analyse

variable {𝕜 E F ι κ : Type*}

section Topologie

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- La topologie définie par une famille de semi-normes (au sens de Mathlib) est la topologie la
plus grossière rendant continues les applications `y ↦ |y - x|_i`. -/
private lemma moduleFilterBasis_topology_eq_iInf (p : SeminormFamily 𝕜 E ι) :
    p.moduleFilterBasis.topology =
      ⨅ (i : ι) (x : E), TopologicalSpace.induced (fun y => p i (y - x)) inferInstance := by
  let t0 : TopologicalSpace E := p.moduleFilterBasis.topology
  have hp0 : WithSeminorms p := ⟨rfl⟩
  apply le_antisymm
  · have _ := hp0.isTopologicalAddGroup
    refine le_iInf₂ fun i x => continuous_iff_le_induced.1 ?_
    exact (hp0.continuous_seminorm i).comp (continuous_id.sub continuous_const)
  · refine le_of_nhds_le_nhds fun y => ?_
    refine (hp0.hasBasis_ball (x := y)).ge_iff.2 fun sr hr => ?_
    clear hp0 t0
    let _ : TopologicalSpace E :=
      ⨅ (i : ι) (x : E), TopologicalSpace.induced (fun y => p i (y - x)) inferInstance
    rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
    refine (biInter_finset_mem sr.1).2 fun i _ => ?_
    have : (p i).ball y sr.2 = (fun z => p i (z - y)) ⁻¹' Iio sr.2 := by
      ext; simp [Seminorm.mem_ball]
    rw [this]
    have hcont : Continuous[⨅ (i : ι) (x : E),
        TopologicalSpace.induced (fun y => p i (y - x)) inferInstance, _]
        (fun z => p i (z - y)) :=
      continuous_iInf_dom (continuous_iInf_dom continuous_induced_dom)
    exact hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simpa using hr))

/-- **Déf. `def:evtlc` (evtlc).** La topologie d'un evtlc `(E, (|·|_i)_{i ∈ I})` est la
topologie la plus grossière qui rend continues les applications `y ↦ |y - x|_i`, pour tout
`x ∈ E` et tout `i ∈ I`. Autrement dit, `WithSeminorms p` (la topologie de `E` est celle
définie par `p` au sens de Mathlib) équivaut à ce que la topologie de `E` soit cette borne
inférieure de topologies induites. -/
theorem def_evtlc [t : TopologicalSpace E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t = ⨅ (i : ι) (x : E), TopologicalSpace.induced (fun y => p i (y - x)) inferInstance := by
  rw [← moduleFilterBasis_topology_eq_iInf]
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩

variable [TopologicalSpace E] {p : SeminormFamily 𝕜 E ι}

/-- **Éq. `eq:evtlc_vois` (Base de voisinages).** Dans un evtlc, une base de voisinages de
`x ∈ E` est formée par les ensembles
`B_{I₀}(x, ε) = {y ∈ E | ∀ i ∈ I₀, |x - y|_i < ε}`, pour `ε > 0` et `I₀ ⊆ I` fini. -/
theorem eq_evtlc_vois (hp : WithSeminorms p) (x : E) :
    (𝓝 x).HasBasis (fun s : Finset ι × ℝ => 0 < s.2)
      (fun s => {y | ∀ i ∈ s.1, p i (x - y) < s.2}) := by
  refine hp.hasBasis_ball.congr (fun _ => Iff.rfl) fun s hs => ?_
  ext y
  simp only [Seminorm.mem_ball, mem_ofPred_eq]
  exact ⟨fun h i hi => by rw [map_sub_rev]; exact (Seminorm.le_finset_sup_apply hi).trans_lt h,
    fun h => Seminorm.finset_sup_apply_lt hs fun i hi => by rw [map_sub_rev]; exact h i hi⟩

/-- **Déf. `def:evtlc`, convergence des suites.** Une suite `x_n` d'un evtlc converge vers `x`
ssi `|x - x_n|_i → 0` pour tout `i ∈ I`. -/
theorem def_evtlc_tendsto (hp : WithSeminorms p) (u : ℕ → E) (x : E) :
    Tendsto u atTop (𝓝 x) ↔ ∀ i, Tendsto (fun n => p i (x - u n)) atTop (𝓝 0) := by
  rw [hp.tendsto_nhds u x]
  refine forall_congr' fun i => ?_
  rw [Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _), map_sub_rev (p i) x]

/-- **Déf. `def:evtlc`, cas des evn.** Tout evn est un evtlc, dont la famille de semi-normes est
réduite à un élément (la norme). -/
theorem def_evtlc_evn (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    WithSeminorms (fun _ : Fin 1 => normSeminorm 𝕜 F) :=
  norm_withSeminorms 𝕜 F

/-- **Lemme `lem:evtlc_separe` (Séparation dans les evtlc).** Un evtlc est séparé ssi pour tout
`x ∈ E`, `(∀ i ∈ I, |x|_i = 0) ⇒ x = 0`. -/
theorem lem_evtlc_separe (hp : WithSeminorms p) :
    T2Space E ↔ ∀ x : E, (∀ i, p i x = 0) → x = 0 := by
  have := hp.isTopologicalAddGroup
  constructor
  · intro _ x hx
    by_contra h
    obtain ⟨i, hi⟩ := hp.separating_of_T1 x h
    exact hi (hx i)
  · intro h
    have : T1Space E := hp.T1_of_separating fun x hx => by
      by_contra! H
      exact hx (h x H)
    infer_instance

variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {q : SeminormFamily 𝕜 F κ}

/-- **Lemme `lem:evtlcLinCont` (Continuité linéaire entre evtlc), éq. `eq:cont_lin_evtlc`.**
Une application linéaire `u : E → F` entre evtlc est continue ssi pour tout `j ∈ J` il existe
`I_j ⊆ I` fini et une constante `C_j` tels que `|u(x)|_j ≤ C_j max_{i ∈ I_j} |x|_i`. -/
theorem lem_evtlcLinCont (hp : WithSeminorms p) (hq : WithSeminorms q) (u : E →ₗ[𝕜] F) :
    Continuous u ↔ ∀ j, ∃ I : Finset ι, ∃ C : ℝ, ∀ x, q j (u x) ≤ C * (I.sup p) x := by
  constructor
  · intro hu j
    obtain ⟨s, C, -, hC⟩ :=
      Seminorm.bound_of_continuous hp ((q j).comp u) ((hq.continuous_seminorm j).comp hu)
    exact ⟨s, C, fun x => by simpa [NNReal.smul_def] using hC x⟩
  · intro h
    exact WithSeminorms.continuous_of_isBounded hp hq u (Seminorm.IsBounded.of_real h)

/-- **Éq. `eq:cont_lin_evtlc_evn`.** Une application linéaire d'un evtlc vers un evn
`(F, ‖·‖_F)` est continue ssi il existe `I₀ ⊆ I` fini et une constante `C` tels que
`‖u(x)‖_F ≤ C max_{i ∈ I₀} |x|_i`. -/
theorem eq_cont_lin_evtlc_evn {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (hp : WithSeminorms p) (u : E →ₗ[𝕜] G) :
    Continuous u ↔ ∃ I : Finset ι, ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C * (I.sup p) x := by
  rw [lem_evtlcLinCont hp (norm_withSeminorms 𝕜 G) u]
  simp

/-- **Éq. `eq:cont_lin_evtlc_evn`, cas du corps de base.** Une forme linéaire sur un evtlc est
continue ssi il existe `I₀ ⊆ I` fini et une constante `C` tels que `|u(x)| ≤ C max_{i ∈ I₀} |x|_i`.
-/
theorem eq_cont_lin_evtlc_evn_corps (hp : WithSeminorms p) (u : E →ₗ[𝕜] 𝕜) :
    Continuous u ↔ ∃ I : Finset ι, ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C * (I.sup p) x :=
  eq_cont_lin_evtlc_evn hp u

omit [TopologicalSpace E] in
/-- **Rem. `rem:sommeMaxEvtlc` (Somme ou maximum de semi-normes).** Le maximum et la somme d'un
nombre fini de semi-normes sont équivalents :
`max_{i ∈ I₀} |x|_i ≤ ∑_{i ∈ I₀} |x|_i ≤ #I₀ · max_{i ∈ I₀} |x|_i`. -/
theorem rem_sommeMaxEvtlc (p : SeminormFamily 𝕜 E ι) (I : Finset ι) (x : E) :
    (I.sup p) x ≤ ∑ i ∈ I, p i x ∧ ∑ i ∈ I, p i x ≤ I.card * (I.sup p) x := by
  refine ⟨?_, ?_⟩
  · have := Seminorm.finset_sup_le_sum p I x
    simpa using this
  · have := Finset.sum_le_card_nsmul I (fun i => p i x) ((I.sup p) x)
      fun i hi => Seminorm.le_finset_sup_apply hi
    simpa [nsmul_eq_mul] using this

/-- **Rem. `rem:sommeMaxEvtlc`, critère de continuité.** On peut remplacer le maximum par une
somme dans `eq:cont_lin_evtlc` (quitte à modifier les constantes). -/
theorem rem_sommeMaxEvtlc_cont (hp : WithSeminorms p) (hq : WithSeminorms q) (u : E →ₗ[𝕜] F) :
    Continuous u ↔ ∀ j, ∃ I : Finset ι, ∃ C : ℝ, ∀ x, q j (u x) ≤ C * ∑ i ∈ I, p i x := by
  rw [lem_evtlcLinCont hp hq u]
  refine forall_congr' fun j => ⟨fun ⟨I, C, h⟩ => ⟨I, max C 0, fun x => ?_⟩,
    fun ⟨I, C, h⟩ => ⟨I, max C 0 * I.card, fun x => ?_⟩⟩
  · have h1 := (rem_sommeMaxEvtlc p I x).1
    have h2 : 0 ≤ (I.sup p) x := apply_nonneg _ _
    calc q j (u x) ≤ C * (I.sup p) x := h x
      _ ≤ max C 0 * (I.sup p) x := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      _ ≤ max C 0 * ∑ i ∈ I, p i x := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  · have h1 := (rem_sommeMaxEvtlc p I x).2
    have h2 : 0 ≤ ∑ i ∈ I, p i x := Finset.sum_nonneg fun i _ => apply_nonneg _ _
    calc q j (u x) ≤ C * ∑ i ∈ I, p i x := h x
      _ ≤ max C 0 * ∑ i ∈ I, p i x := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      _ ≤ max C 0 * (I.card * (I.sup p) x) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
      _ = max C 0 * I.card * (I.sup p) x := by ring

end Topologie

section Gradue

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Rem. `rem:evtlcGradue` (Suite graduée de semi-normes), graduation.** Pour une famille
dénombrable `(|·|_n)_{n ∈ ℕ}`, la famille `|x|'_N := max_{0 ≤ n ≤ N} |x|_n` est graduée :
pour tout `x`, la suite `(|x|'_N)_N` est croissante. -/
theorem rem_evtlcGradue_monotone (p : SeminormFamily 𝕜 E ℕ) (x : E) :
    Monotone fun N => (Finset.Iic N).sup p x := fun _ _ h =>
  (Finset.sup_mono (f := p) (Finset.Iic_subset_Iic.2 h) : _ ≤ _) x

/-- **Rem. `rem:evtlcGradue`, même topologie.** La famille graduée `(|·|'_N)_N` définit la même
topologie que la famille initiale `(|·|_n)_n`. -/
theorem rem_evtlcGradue_withSeminorms [TopologicalSpace E] (p : SeminormFamily 𝕜 E ℕ) :
    WithSeminorms p ↔ WithSeminorms (fun N => (Finset.Iic N).sup p) := by
  refine ⟨fun hp => hp.partial_sups, fun hp => hp.congr ?_ ?_⟩
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i ≤ (Finset.Iic i).sup p)
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl

/-- **Rem. `rem:evtlcGradue`, cas gradué.** Si la famille initiale est déjà graduée, alors
`|·|'_n = |·|_n`. -/
theorem rem_evtlcGradue_eq (p : SeminormFamily 𝕜 E ℕ) (hp : ∀ x, Monotone fun n => p n x) :
    (fun N => (Finset.Iic N).sup p) = p := by
  funext N
  ext x
  exact le_antisymm
    (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun n hn => hp x (Finset.mem_Iic.1 hn))
    (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 le_rfl))

/-- **Éq. `eqdef:boule_graduee`, égalité.** Pour `ε > 0`,
`B_N(x, ε) = {y | ∀ n ≤ N, |y - x|_n < ε} = {y | |y - x|'_N < ε}`. -/
theorem eqdef_boule_graduee_eq (p : SeminormFamily 𝕜 E ℕ) (x : E) (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    {y | ∀ n ≤ N, p n (y - x) < ε} = {y | (Finset.Iic N).sup p (y - x) < ε} := by
  ext y
  simp only [mem_ofPred_eq]
  exact ⟨fun h => Seminorm.finset_sup_apply_lt hε fun n hn => h n (Finset.mem_Iic.1 hn),
    fun h n hn => (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hn)).trans_lt h⟩

/-- **Éq. `eqdef:boule_graduee` (Base de voisinages, cas dénombrable).** Pour une famille
dénombrable de semi-normes, les ensembles `B_N(x, ε) = {y | ∀ n ≤ N, |y - x|_n < ε}`, pour
`N ∈ ℕ` et `ε > 0`, forment une base de voisinages de `x`. -/
theorem eqdef_boule_graduee [TopologicalSpace E] {p : SeminormFamily 𝕜 E ℕ}
    (hp : WithSeminorms p) (x : E) :
    (𝓝 x).HasBasis (fun Nε : ℕ × ℝ => 0 < Nε.2)
      (fun Nε => {y | ∀ n ≤ Nε.1, p n (y - x) < Nε.2}) := by
  refine (eq_evtlc_vois hp x).to_hasBasis
    (fun sr hr => ⟨(sr.1.sup id, sr.2), hr, fun y hy i hi => ?_⟩)
    (fun Nε hε => ⟨(Finset.Iic Nε.1, Nε.2), hε, fun y hy n hn => ?_⟩)
  · rw [map_sub_rev]; exact hy i (Finset.le_sup (f := id) hi)
  · rw [map_sub_rev]; exact hy n (Finset.mem_Iic.2 hn)

end Gradue

section Distance

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- La distance `eqdef:evtlc_dist` associée à une famille dénombrable de semi-normes :
`d(x, y) := max_{n ∈ ℕ} min {2^{-n}, |x - y|_n}` (borne supérieure, atteinte d'après
`eqdef_evtlc_dist`).
Lien avec Mathlib : les familles de semi-normes sont les `SeminormFamily` de Mathlib (topologie
`WithSeminorms`) ; `evtlcMetric` munit `E` de la structure `MetricSpace` correspondante, qui
définit la topologie de l'evtlc (`prop_distanceEvtlcs`). -/
noncomputable def evtlcDist (p : SeminormFamily 𝕜 E ℕ) (x y : E) : ℝ :=
  ⨆ n : ℕ, min ((2 : ℝ)⁻¹ ^ n) (p n (x - y))

variable (p : SeminormFamily 𝕜 E ℕ)

lemma evtlcDist_bddAbove (x y : E) :
    BddAbove (range fun n : ℕ => min ((2 : ℝ)⁻¹ ^ n) (p n (x - y))) :=
  ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))⟩

lemma le_evtlcDist (x y : E) (n : ℕ) : min ((2 : ℝ)⁻¹ ^ n) (p n (x - y)) ≤ evtlcDist p x y :=
  le_ciSup (evtlcDist_bddAbove p x y) n

lemma evtlcDist_nonneg (x y : E) : 0 ≤ evtlcDist p x y :=
  (le_min (by positivity) (apply_nonneg _ _)).trans (le_evtlcDist p x y 0)

lemma evtlcDist_self (x : E) : evtlcDist p x x = 0 :=
  le_antisymm (ciSup_le fun n => by simp) (evtlcDist_nonneg p x x)

lemma evtlcDist_comm (x y : E) : evtlcDist p x y = evtlcDist p y x := by
  simp only [evtlcDist, map_sub_rev (p _)]

private lemma min_le_min_add {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : d ≤ b + c) : min a d ≤ min a b + min a c := by
  simp only [min_def]
  split_ifs <;> linarith

lemma evtlcDist_triangle (x y z : E) : evtlcDist p x z ≤ evtlcDist p x y + evtlcDist p y z := by
  refine ciSup_le fun n => ?_
  have h : p n (x - z) ≤ p n (x - y) + p n (y - z) := by
    rw [← sub_add_sub_cancel x y z]; exact map_add_le_add _ _ _
  exact (min_le_min_add (by positivity) (apply_nonneg _ _) (apply_nonneg _ _) h).trans
    (add_le_add (le_evtlcDist p x y n) (le_evtlcDist p y z n))

lemma evtlcDist_eq_zero {x y : E} (hsep : ∀ x : E, (∀ n, p n x = 0) → x = 0)
    (h : evtlcDist p x y = 0) : x = y := by
  refine sub_eq_zero.1 (hsep _ fun n => le_antisymm ?_ (apply_nonneg _ _))
  have := (le_evtlcDist p x y n).trans h.le
  rcases min_le_iff.1 this with h' | h'
  · exact absurd h' (not_le.2 (by positivity))
  · exact h'

/-- Majoration de `d` par un maximum fini, pour tout `N`. -/
private lemma evtlcDist_le_max (x y : E) (N : ℕ) :
    evtlcDist p x y ≤ max ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun n => min ((2 : ℝ)⁻¹ ^ n) (p n (x - y))) ((2 : ℝ)⁻¹ ^ N) := by
  refine ciSup_le fun n => ?_
  rcases le_or_gt n N with hn | hn
  · exact (Finset.le_sup' (fun n => min ((2 : ℝ)⁻¹ ^ n) (p n (x - y)))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hn))).trans (le_max_left _ _)
  · exact (min_le_left _ _).trans <| (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      hn.le).trans (le_max_right _ _)

/-- **Éq. `eqdef:evtlc_dist`.** La borne supérieure définissant `d(x, y)` est un maximum :
il existe `n ∈ ℕ` tel que `d(x, y) = min {2^{-n}, |x - y|_n}`. -/
theorem eqdef_evtlc_dist (x y : E) :
    ∃ n : ℕ, evtlcDist p x y = min ((2 : ℝ)⁻¹ ^ n) (p n (x - y)) := by
  rcases (evtlcDist_nonneg p x y).eq_or_lt with h | h
  · refine ⟨0, le_antisymm ?_ (le_evtlcDist p x y 0)⟩
    rw [← h]; exact le_min (by norm_num) (apply_nonneg _ _)
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one h (by norm_num : (2 : ℝ)⁻¹ < 1)
    obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      fun n => min ((2 : ℝ)⁻¹ ^ n) (p n (x - y))
    have hle := evtlcDist_le_max p x y N
    rw [hn] at hle
    refine ⟨n, le_antisymm ?_ (le_evtlcDist p x y n)⟩
    rcases le_max_iff.1 hle with h' | h'
    · exact h'
    · exact absurd h' (not_le.2 hN)

/-- Caractérisation de `d(x, y) < η` (version sans logarithme de `eq:boule_evtlc`). -/
lemma evtlcDist_lt_iff (x y : E) {η : ℝ} (hη : 0 < η) :
    evtlcDist p x y < η ↔ ∀ n : ℕ, η ≤ (2 : ℝ)⁻¹ ^ n → p n (x - y) < η := by
  constructor
  · intro h n hn
    rcases min_lt_iff.1 ((le_evtlcDist p x y n).trans_lt h) with h' | h'
    · exact absurd h' (not_lt.2 hn)
    · exact h'
  · intro h
    have hterm : ∀ n, min ((2 : ℝ)⁻¹ ^ n) (p n (x - y)) < η := fun n => by
      rcases le_or_gt η ((2 : ℝ)⁻¹ ^ n) with hn | hn
      · exact (min_le_right _ _).trans_lt (h n hn)
      · exact (min_le_left _ _).trans_lt hn
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (2 : ℝ)⁻¹ < 1)
    obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      fun n => min ((2 : ℝ)⁻¹ ^ n) (p n (x - y))
    refine (evtlcDist_le_max p x y N).trans_lt (max_lt ?_ hN)
    rw [hn]; exact hterm n

/-- **Éq. `eq:boule_evtlc` (Boule pour la distance `d`).** Pour `η > 0`,
`B_d(x, η) = {y ∈ E | ∀ n ≤ -log₂ η, |y - x|_n < η}`.

Remarque : le cours écrit l'inégalité stricte `n < -log₂ η`, ce qui est inexact lorsque
`-log₂ η` est un entier `N` : pour `η = 2^{-N}`, le terme `min {2^{-N}, |x - y|_N}` vaut `η`
dès que `|x - y|_N ≥ η`, et alors `d(x, y) ≥ η`. L'inégalité large `n ≤ -log₂ η` est correcte
(et c'est elle qu'utilise la preuve du cours, via `B_{⌊-log₂ η⌋}(x, η) ⊆ B_d(x, η)`). -/
theorem eq_boule_evtlc (x : E) {η : ℝ} (hη : 0 < η) :
    {y | evtlcDist p x y < η} = {y | ∀ n : ℕ, (n : ℝ) ≤ -Real.logb 2 η → p n (y - x) < η} := by
  ext y
  simp only [mem_ofPred_eq, evtlcDist_lt_iff p x y hη, map_sub_rev (p _) y x]
  refine forall_congr' fun n => imp_congr_left ?_
  rw [le_neg, Real.logb_le_iff_le_rpow (by norm_num) hη, Real.rpow_neg (by norm_num),
    Real.rpow_natCast, inv_pow]

/-- Pseudo-distance sur `E` associée à la fonction `evtlcDist`. -/
@[instance_reducible]
noncomputable def evtlcPseudoMetric : PseudoMetricSpace E where
  dist := evtlcDist p
  dist_self := evtlcDist_self p
  dist_comm := evtlcDist_comm p
  dist_triangle := evtlcDist_triangle p

/-- Distance sur `E` associée à `evtlcDist`, lorsque la famille de semi-normes sépare les
points (cf. `lem:evtlc_separe`). -/
@[instance_reducible]
noncomputable def evtlcMetric (hsep : ∀ x : E, (∀ n, p n x = 0) → x = 0) : MetricSpace E where
  __ := evtlcPseudoMetric p
  eq_of_dist_eq_zero := evtlcDist_eq_zero p hsep

variable [t : TopologicalSpace E] {p}

/-- **Prop. `prop:distanceEvtlcs` (Distance sur un evtlcs), voisinages.** Les boules
`B_d(x, η)`, `η > 0`, forment une base de voisinages de `x` pour la topologie de l'evtlc. -/
theorem prop_distanceEvtlcs_nhds (hp : WithSeminorms p) (x : E) :
    (𝓝 x).HasBasis (fun η : ℝ => 0 < η) (fun η => {y | evtlcDist p x y < η}) := by
  refine (eqdef_boule_graduee hp x).to_hasBasis
    (fun Nε hε => ⟨min Nε.2 ((2 : ℝ)⁻¹ ^ (Nε.1 + 1)), lt_min hε (by positivity),
      fun y hy n hn => ?_⟩)
    (fun η hη => ?_)
  · have hpos : 0 < min Nε.2 ((2 : ℝ)⁻¹ ^ (Nε.1 + 1)) := lt_min hε (by positivity)
    have h := (evtlcDist_lt_iff p x y hpos).1 hy n
      ((min_le_right _ _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)))
    rw [map_sub_rev]
    exact h.trans_le (min_le_left _ _)
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨(N, η), hη, fun y hy => ?_⟩
    refine (evtlcDist_lt_iff p x y hη).2 fun n hn => ?_
    have hnN : n ≤ N := by
      by_contra! H
      exact absurd ((pow_le_pow_of_le_one (by norm_num) (by norm_num) H.le).trans_lt hN)
        (not_lt.2 hn)
    rw [map_sub_rev]
    exact hy n hnN

/-- **Prop. `prop:distanceEvtlcs` (Distance sur un evtlcs).** Soit `E` un evtlc séparé, muni d'une
famille dénombrable de semi-normes `(|·|_n)_{n ∈ ℕ}`. Alors
`d(x, y) = max_n min {2^{-n}, |x - y|_n}`
est une distance sur `E` (`evtlcMetric`), et la topologie qu'elle définit est celle de `E`. -/
theorem prop_distanceEvtlcs [T2Space E] (hp : WithSeminorms p) :
    (evtlcMetric p ((lem_evtlc_separe hp).1 inferInstance)).toUniformSpace.toTopologicalSpace
      = t := by
  let _ := evtlcMetric p ((lem_evtlc_separe hp).1 inferInstance)
  refine TopologicalSpace.ext_nhds fun x => ?_
  refine (Metric.nhds_basis_ball (x := x)).eq_of_same_basis ?_
  convert prop_distanceEvtlcs_nhds hp x using 2 with η
  ext y
  change evtlcDist p y x < η ↔ evtlcDist p x y < η
  rw [evtlcDist_comm]

end Distance

section LineairBorne

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {p : SeminormFamily 𝕜 E ι}

/-- **Déf. `def:lineairBorne` (Partie linéairement bornée).** Une partie `A` d'un evtlc est
linéairement bornée ssi chaque semi-norme est bornée sur `A`. Cette notion coïncide avec la notion
de partie bornée (au sens de von Neumann) de Mathlib, `Bornology.IsVonNBounded`.
Remarque : le cours se place dans un evtlc séparé ; cette hypothèse est inutile ici. -/
theorem def_lineairBorne (hp : WithSeminorms p) (A : Set E) :
    IsVonNBounded 𝕜 A ↔ ∀ i, BddAbove (p i '' A) :=
  hp.isVonNBounded_iff_seminorm_bddAbove

omit [TopologicalSpace E] in
/-- **Déf. `def:lineairBorne`, caractérisation métrique.** Si la famille de semi-normes est
dénombrable et si `d` désigne la distance `eqdef:evtlc_dist`, alors `A` est linéairement bornée
ssi `∀ ε > 0, ∃ δ > 0, δ A ⊆ B_d(0, ε)`.
Remarque : cette caractérisation ne fait pas intervenir la topologie, ni la séparation. -/
theorem def_lineairBorne_dist (p : SeminormFamily 𝕜 E ℕ) (A : Set E) :
    (∀ n, BddAbove (p n '' A)) ↔
      ∀ ε > 0, ∃ δ > (0 : ℝ), (δ : 𝕜) • A ⊆ {y | evtlcDist p 0 y < ε} := by
  constructor
  · intro h ε hε
    choose M hM using h
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
    obtain ⟨B, hBpos, hbound⟩ : ∃ B : ℝ, 0 < B ∧ ∀ n ≤ N, ∀ a ∈ A, p n a ≤ B :=
      ⟨∑ n ∈ Finset.range (N + 1), |M n| + 1,
        add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) one_pos,
        fun n hn a ha => by
      have h1 : p n a ≤ |M n| := (hM n (mem_image_of_mem _ ha)).trans (le_abs_self _)
      have h2 : |M n| ≤ ∑ n ∈ Finset.range (N + 1), |M n| :=
        Finset.single_le_sum (f := fun n => |M n|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
      linarith⟩
    have hδ : 0 < ε / (2 * B) := div_pos hε (mul_pos two_pos hBpos)
    refine ⟨ε / (2 * B), hδ, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    refine (evtlcDist_lt_iff p 0 _ hε).2 fun n hn => ?_
    have hnN : n ≤ N := by
      by_contra! H
      exact absurd ((pow_le_pow_of_le_one (by norm_num) (by norm_num) H.le).trans_lt hN)
        (not_lt.2 hn)
    rw [zero_sub, map_neg_eq_map, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hδ]
    calc ε / (2 * B) * p n a ≤ ε / (2 * B) * B :=
          mul_le_mul_of_nonneg_left (hbound n hnN a ha) hδ.le
      _ = ε / 2 := by field_simp [hBpos.ne']
      _ < ε := half_lt_self hε
  · intro h n
    obtain ⟨δ, hδ, hA⟩ := h ((2 : ℝ)⁻¹ ^ n) (by positivity)
    refine ⟨(2 : ℝ)⁻¹ ^ n / δ, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have := (evtlcDist_lt_iff p 0 _ (by positivity)).1 (hA (smul_mem_smul_set ha)) n le_rfl
    rw [zero_sub, map_neg_eq_map, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hδ] at this
    rw [le_div_iff₀ hδ, mul_comm]
    exact this.le

end LineairBorne

end M1Analyse
