/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

/-!
# §1.2 Espaces métriques (`subsec:metric`)

Source : `Include/TopologieGenerale.tex`, sous-section `subsec:metric`.

Les objets du cours sont ceux de Mathlib : espace métrique `MetricSpace`, boules `Metric.ball`
et `Metric.closedBall`, `∞`-distance `EMetricSpace` (distance à valeurs dans `ℝ≥0∞`),
uniforme continuité `UniformContinuous`, applications höldériennes `HolderWith` et
lipschitziennes `LipschitzWith`, équicontinuité `EquicontinuousAt` / `UniformEquicontinuous`,
topologie de la convergence uniforme `UniformFun` (notée `I →ᵤ Y`).

Notions propres au cours, absentes de Mathlib, introduites ici par une `def` :
* `IsDistance d` : la fonction `d : X → X → ℝ` satisfait les axiomes de distance de
  `def:distance` (sert à énoncer « ... est une distance » sans introduire d'instance) ;
* `IsModuleCont ω`, `IsSousAdditif ω` : module de continuité (`def:moduleCont`) ;
* `distCvSimple` : la distance de `prop:distCvSimple` sur un produit dénombrable.

Choix de formalisation pour les modules de continuité : `ω : ℝ≥0 → ℝ≥0∞` (le cours :
`ω : ℝ₊ → [0, ∞]`) ; les inégalités `d_Y(f x, f x') ≤ ω(d_X(x, x'))` sont écrites
`edist (f x) (f x') ≤ ω (nndist x x')` (pour un espace métrique, `edist = ENNReal.ofReal ∘ dist`).

Non formalisé : `lem:regModuleCont` (régularisation `C^∞` d'un module de continuité, preuve par
convolution multiplicative avec une fonction bosse : construction longue, hors périmètre).
-/

open Set Filter TopologicalSpace Topology
open scoped NNReal ENNReal UniformConvergence

namespace M1Analyse

variable {X Y : Type*}

/-! ### Distance, boules -/

/-- Les axiomes de distance du cours (`def:distance`) pour une fonction `d : X → X → ℝ` :
séparation (`d ≥ 0`, avec égalité ssi `x = y`), symétrie, inégalité triangulaire.
Prédicat auxiliaire, utilisé pour énoncer « `d` est une distance » sans instance. -/
def IsDistance (d : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y ∧ (d x y = 0 ↔ x = y)) ∧ (∀ x y, d x y = d y x) ∧
    ∀ x y z, d x z ≤ d x y + d y z

/-- **Déf. `def:distance` (Espace métrique), sens direct.** La distance d'un espace métrique
Mathlib `MetricSpace X` satisfait les axiomes du cours (séparation, symétrie, inégalité
triangulaire). -/
theorem def_distance [MetricSpace X] : IsDistance (dist : X → X → ℝ) :=
  ⟨fun _ _ => ⟨dist_nonneg, dist_eq_zero⟩, dist_comm, dist_triangle⟩

/-- Structure d'espace métrique Mathlib associée à une fonction `d` satisfaisant les axiomes
de distance du cours. -/
@[instance_reducible]
noncomputable def metricSpaceOfIsDistance (d : X → X → ℝ) (hd : IsDistance d) :
    MetricSpace X where
  dist := d
  dist_self x := (hd.1 x x).2.2 rfl
  dist_comm := hd.2.1
  dist_triangle := hd.2.2
  eq_of_dist_eq_zero h := (hd.1 _ _).2.1 h

/-- **Déf. `def:distance` (Espace métrique), sens réciproque.** Toute fonction
`d : X → X → ℝ` satisfaisant les axiomes du cours est la distance d'une structure d'espace
métrique Mathlib sur `X`. -/
theorem def_distance_of_axioms (d : X → X → ℝ) (hd : IsDistance d) :
    ∃ m : MetricSpace X, ∀ x y, @dist X m.toDist x y = d x y :=
  ⟨metricSpaceOfIsDistance d hd, fun _ _ => rfl⟩

/-- **Déf. `def:boule` (Boules).** Les boules ouverte `B(x,r) = {y | d(x,y) < r}` et fermée
`B'(x,r) = {y | d(x,y) ≤ r}` du cours sont `Metric.ball x r` et `Metric.closedBall x r`. -/
theorem def_boule [MetricSpace X] (x : X) (r : ℝ) :
    Metric.ball x r = {y | dist x y < r} ∧ Metric.closedBall x r = {y | dist x y ≤ r} := by
  refine ⟨?_, ?_⟩ <;> ext y <;> simp [dist_comm]

/-- **Déf. `def:boule` (Topologie métrique).** La topologie Mathlib d'un espace métrique est la
topologie métrique du cours : les boules ouvertes `B(x,r)`, `x ∈ X`, `r > 0`, en forment une
base d'ouverts. -/
theorem def_boule_base [MetricSpace X] :
    IsTopologicalBasis {B : Set X | ∃ x r, 0 < r ∧ B = Metric.ball x r} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨x, r, -, rfl⟩; exact Metric.isOpen_ball
  · intro a U ha hU
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU a ha
    exact ⟨_, ⟨a, ε, hε, rfl⟩, Metric.mem_ball_self hε, hsub⟩

/-- **Rem. `rem:distInfinie` (`∞`-distance).** Une `∞`-distance est la distance `edist` (à
valeurs dans `[0, ∞]`) d'un `EMetricSpace` Mathlib. Alors `d := min{1, d_∞}` est une distance
(à valeurs réelles) qui définit la même topologie : les boules `{y | d(x,y) < r}`, `r > 0`,
forment une base de voisinages de `x` pour la topologie de `d_∞`. -/
theorem rem_distInfinie [EMetricSpace X] :
    IsDistance (fun x y : X => (min 1 (edist x y)).toReal) ∧
      ∀ x : X, (𝓝 x).HasBasis (fun r : ℝ => 0 < r)
        (fun r => {y | (min 1 (edist x y)).toReal < r}) := by
  have hfin : ∀ x y : X, min 1 (edist x y) ≠ ⊤ :=
    fun x y => ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  refine ⟨⟨fun x y => ⟨ENNReal.toReal_nonneg, ?_⟩, fun x y => by simp [edist_comm],
    fun x y z => ?_⟩, fun x => ?_⟩
  · rw [ENNReal.toReal_eq_zero_iff]
    constructor
    · rintro (h | h)
      · rcases min_eq_iff.mp h with h' | h'
        · exact absurd h'.1 one_ne_zero
        · exact edist_eq_zero.mp h'.1
      · exact absurd h (hfin x y)
    · rintro rfl; simp
  · apply ENNReal.toReal_le_add _ (hfin x y) (hfin y z)
    calc min 1 (edist x z) ≤ min 1 (edist x y + edist y z) :=
          min_le_min_left _ (edist_triangle x y z)
      _ ≤ min 1 (edist x y) + min 1 (edist y z) := by
          rcases le_total 1 (edist x y) with h1 | h1 <;>
          rcases le_total 1 (edist y z) with h2 | h2
          · exact min_le_left _ _ |>.trans (by simp [h1])
          · exact min_le_left _ _ |>.trans (by simp [h1])
          · exact min_le_left _ _ |>.trans (by simp [h2])
          · rw [min_eq_right h1, min_eq_right h2]; exact min_le_right _ _
  · refine (Metric.nhds_basis_eball (x := x)).to_hasBasis (fun ε hε => ?_) (fun r hr => ?_)
    · obtain ⟨e, he0, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
      refine ⟨min (1 / 2) e, lt_min (by norm_num) (by exact_mod_cast he0), fun y hy => ?_⟩
      change (min 1 (edist x y)).toReal < min (1 / 2) (e : ℝ) at hy
      rw [Metric.mem_eball, edist_comm]
      have h1 : min 1 (edist x y) < ENNReal.ofReal (min (1 / 2) (e : ℝ)) := by
        rwa [← ENNReal.ofReal_toReal (hfin x y),
          ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hy)]
      have h2 : ENNReal.ofReal (min (1 / 2) (e : ℝ)) < 1 := by
        rw [ENNReal.ofReal_lt_one]; exact (min_le_left _ _).trans_lt (by norm_num)
      have h3 : edist x y < ENNReal.ofReal (min (1 / 2) (e : ℝ)) := by
        rcases min_lt_iff.mp h1 with h | h
        · exact absurd (h.trans h2) (lt_irrefl _)
        · exact h
      calc edist x y < ENNReal.ofReal (min (1 / 2) (e : ℝ)) := h3
        _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ < ε := by rwa [ENNReal.ofReal_coe_nnreal]
    · refine ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.mpr hr, fun y hy => ?_⟩
      rw [Metric.mem_eball, edist_comm] at hy
      exact ENNReal.toReal_lt_of_lt_ofReal ((min_le_right _ _).trans_lt hy)

/-- Les axiomes d'une `∞`-distance (`rem:distInfinie`) : ce sont ceux de `def:distance`,
la valeur `+∞` étant permise. -/
theorem rem_distInfinie_axioms [EMetricSpace X] :
    (∀ x y : X, edist x y = 0 ↔ x = y) ∧ (∀ x y : X, edist x y = edist y x) ∧
      ∀ x y z : X, edist x z ≤ edist x y + edist y z :=
  ⟨fun _ _ => edist_eq_zero, edist_comm, edist_triangle⟩

/-- **Prop. `prop:baseVoisMetric`, premier point.** Dans un espace métrique, tout point `x`
admet la base dénombrable de voisinages `𝒲_x = {B(x, 1/n) | n ∈ ℕ*}`. -/
theorem prop_baseVoisMetric [MetricSpace X] (x : X) :
    (𝓝 x).HasBasis (fun n : ℕ => 0 < n) (fun n => Metric.ball x (1 / n)) :=
  Metric.nhds_basis_ball_inv_nat_pos

/-- **Prop. `prop:baseVoisMetric`, second point.** Si `(xₙ)` est une suite dense de l'espace
métrique `X` (qui est donc séparable), alors `{B(xₙ, r) | n ∈ ℕ, r ∈ ℚ₊*}` est une base
(dénombrable) d'ouverts. -/
theorem prop_baseVoisMetric_sep [MetricSpace X] (u : ℕ → X) (hu : DenseRange u) :
    IsTopologicalBasis {B : Set X | ∃ n : ℕ, ∃ r : ℚ, 0 < r ∧ B = Metric.ball (u n) r} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨n, r, -, rfl⟩; exact Metric.isOpen_ball
  · intro a U ha hU
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU a ha
    obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (half_pos hε)
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp hu a r (by exact_mod_cast hr0)
    refine ⟨_, ⟨n, r, by exact_mod_cast hr0, rfl⟩, ?_, fun y hy => hsub ?_⟩
    · exact hn
    · rw [Metric.mem_ball] at hy ⊢
      linarith [dist_triangle y (u n) a, dist_comm a (u n)]

/-! ### Modules de continuité -/

/-- **Déf. `def:moduleCont` (Module de continuité).** Un module de continuité est une
application `ω : ℝ₊ → [0, ∞]` telle que `ω(s) → 0` lorsque `s → 0`.
Choix (à valider) : la limite est prise au sens de `𝓝 0` dans `ℝ≥0`, *point `0` inclus*
(convention française de limite en un point du domaine) ; ceci impose `ω(0) = 0`, et équivaut à
`ω 0 = 0 ∧ ω(s) → 0` quand `s → 0⁺` (cf. `isModuleCont_iff`). -/
def IsModuleCont (ω : ℝ≥0 → ℝ≥0∞) : Prop :=
  Tendsto ω (𝓝 0) (𝓝 0)

/-- **Déf. `def:moduleCont` (Sous-additivité).** Un module de continuité `ω` est sous-additif si
`ω(s + t) ≤ ω(s) + ω(t)` pour tous `s, t ≥ 0`. -/
def IsSousAdditif (ω : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ s t, ω (s + t) ≤ ω s + ω t

/-- Un module de continuité s'annule en `0`. -/
theorem IsModuleCont.map_zero {ω : ℝ≥0 → ℝ≥0∞} (h : IsModuleCont ω) : ω 0 = 0 :=
  tendsto_nhds_unique (tendsto_pure_nhds ω 0) (h.mono_left (pure_le_nhds 0))

/-- Explicitation du choix fait dans `IsModuleCont` (`def:moduleCont`) : la condition
`ω(s) → 0` quand `s → 0` (point `0` inclus) équivaut à `ω(0) = 0` et `ω(s) → 0` quand
`s → 0, s > 0`. -/
theorem isModuleCont_iff (ω : ℝ≥0 → ℝ≥0∞) :
    IsModuleCont ω ↔ ω 0 = 0 ∧ Tendsto ω (𝓝[>] 0) (𝓝 0) := by
  constructor
  · intro h
    exact ⟨tendsto_nhds_unique (tendsto_pure_nhds ω 0) (h.mono_left (pure_le_nhds 0)),
      h.mono_left nhdsWithin_le_nhds⟩
  · rintro ⟨h0, h⟩
    have : 𝓝 (0 : ℝ≥0) = 𝓝[>] 0 ⊔ pure 0 := by
      have hu : (univ : Set ℝ≥0) = insert 0 (Ioi 0) := by
        ext t; simp
      rw [← nhdsWithin_univ, hu, nhdsWithin_insert, sup_comm]
    rw [IsModuleCont, this, tendsto_sup]
    exact ⟨h, by simpa [h0] using tendsto_pure_nhds ω 0⟩

/-- Sous-additivité itérée : `ω(n s) ≤ n ω(s)`. -/
theorem IsSousAdditif.le_nsmul {ω : ℝ≥0 → ℝ≥0∞} (h : IsSousAdditif ω) (h0 : ω 0 = 0)
    (n : ℕ) (s : ℝ≥0) : ω (n * s) ≤ n * ω s := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    calc ω ((n + 1 : ℕ) * s) = ω (n * s + s) := by push_cast; ring_nf
      _ ≤ ω (n * s) + ω s := h _ _
      _ ≤ n * ω s + ω s := by gcongr
      _ = (n + 1 : ℕ) * ω s := by push_cast; ring

/-- **Rem. `rem:dist_of_mod_cont`, premier point.** Un module de continuité sous-additif est
à valeurs finies. -/
theorem rem_dist_of_mod_cont_fini {ω : ℝ≥0 → ℝ≥0∞} (hω : IsModuleCont ω)
    (hs : IsSousAdditif ω) (s : ℝ≥0) : ω s ≠ ⊤ := by
  have ht : Tendsto (fun n : ℕ => ω (s / n)) atTop (𝓝 0) :=
    hω.comp (tendsto_const_div_atTop_nhds_zero_nat s)
  obtain ⟨n, hn⟩ := ((ht.eventually (gt_mem_nhds ENNReal.zero_lt_top)).and
    (eventually_ge_atTop 1)).exists
  have hs' : s = n * (s / n) := by
    rw [mul_div_cancel₀]; exact_mod_cast (by omega : n ≠ 0)
  rw [hs']
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hn.1.ne)
    (hs.le_nsmul hω.map_zero n _)

/-- **Rem. `rem:dist_of_mod_cont`, second point.** Si de plus `ω` est croissant et non
identiquement nul, et si `d` est la distance d'un espace métrique `X`, alors `ω ∘ d` est une
distance (à valeurs réelles, `ω` étant fini) définissant la même topologie : les boules
`{y | ω(d(x,y)) < r}`, `r > 0`, forment une base de voisinages de `x`. -/
theorem rem_dist_of_mod_cont [MetricSpace X] {ω : ℝ≥0 → ℝ≥0∞} (hω : IsModuleCont ω)
    (hs : IsSousAdditif ω) (hmono : Monotone ω) (hne : ∃ s, ω s ≠ 0) :
    IsDistance (fun x y : X => (ω (nndist x y)).toReal) ∧
      ∀ x : X, (𝓝 x).HasBasis (fun r : ℝ => 0 < r)
        (fun r => {y | (ω (nndist x y)).toReal < r}) := by
  have hfin := rem_dist_of_mod_cont_fini hω hs
  have hpos : ∀ s, 0 < s → ω s ≠ 0 := by
    intro s hs0 hzero
    obtain ⟨s₀, hs₀⟩ := hne
    obtain ⟨n, hn⟩ := exists_nat_gt (s₀ / s)
    have hn0 : (0 : ℝ≥0) < n := lt_of_le_of_lt zero_le hn
    have h1 : s₀ / n ≤ s := by
      rw [div_le_iff₀ hn0, mul_comm]; exact ((div_lt_iff₀ hs0).mp hn).le
    have h2 : s₀ = n * (s₀ / n) := by rw [mul_div_cancel₀ _ hn0.ne']
    apply hs₀
    rw [h2]
    refine le_antisymm ?_ zero_le
    calc ω (n * (s₀ / n)) ≤ n * ω (s₀ / n) := hs.le_nsmul hω.map_zero n _
      _ ≤ n * ω s := by gcongr; exact hmono h1
      _ = 0 := by rw [hzero, mul_zero]
  refine ⟨⟨fun x y => ⟨ENNReal.toReal_nonneg, ?_⟩, fun x y => by simp only [nndist_comm],
    fun x y z => ?_⟩, fun x => ?_⟩
  · rw [ENNReal.toReal_eq_zero_iff]
    constructor
    · rintro (h | h)
      · by_contra hxy
        exact hpos _ (by simpa [pos_iff_ne_zero] using hxy) h
      · exact absurd h (hfin _)
    · rintro rfl; left; rw [nndist_self, hω.map_zero]
  · apply ENNReal.toReal_le_add _ (hfin _) (hfin _)
    exact (hmono (nndist_triangle x y z)).trans (hs _ _)
  · refine Metric.nhds_basis_ball.to_hasBasis (fun r hr => ?_) (fun ε hε => ?_)
    · have hr' : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr
      refine ⟨(ω r.toNNReal).toReal, ENNReal.toReal_pos (hpos _ hr') (hfin _), fun y hy => ?_⟩
      change (ω (nndist x y)).toReal < (ω r.toNNReal).toReal at hy
      rw [ENNReal.toReal_lt_toReal (hfin _) (hfin _)] at hy
      have := hmono.reflect_lt hy
      rw [Metric.mem_ball, dist_comm, dist_nndist]
      exact (Real.lt_toNNReal_iff_coe_lt).mp this
    · have h1 : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ω t < ENNReal.ofReal ε :=
        hω (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
      refine ⟨δ, hδ, fun y hy => ?_⟩
      have h2 : dist (nndist x y) 0 < δ := by
        have : dist (nndist x y) 0 = dist x y := by simp [NNReal.dist_eq]
        rw [this, dist_comm]; exact hy
      exact ENNReal.toReal_lt_of_lt_ofReal (hδ' h2)

/-! ### Continuité, uniforme continuité -/

/-- Lemme technique : l'existence d'un module de continuité `ω` tel que `r(a) ≤ ω(d(a))` pour
tout `a` équivaut à la condition `∀ ε > 0, ∃ δ > 0, d(a) ≤ δ ⇒ r(a) ≤ ε`. Le sens réciproque
utilise `ω(t) := sup {r(a) | d(a) ≤ t}`, comme dans la preuve de `lem:contDistance`. -/
theorem exists_moduleCont_iff {α : Type*} (r : α → ℝ) (d : α → ℝ≥0) :
    (∃ ω, IsModuleCont ω ∧ ∀ a, ENNReal.ofReal (r a) ≤ ω (d a)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a, (d a : ℝ) ≤ δ → r a ≤ ε := by
  constructor
  · rintro ⟨ω, hω, hle⟩ ε hε
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ω t < ENNReal.ofReal ε :=
      hω (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨δ / 2, half_pos hδ, fun a ha => ?_⟩
    have h2 : dist (d a) 0 < δ := by
      have : dist (d a) 0 = d a := by simp [NNReal.dist_eq]
      rw [this]; linarith
    exact ((ENNReal.ofReal_lt_ofReal_iff hε).mp ((hle a).trans_lt (hδ' h2))).le
  · intro h
    refine ⟨fun t => ⨆ a, ⨆ (_ : d a ≤ t), ENNReal.ofReal (r a), ?_,
      fun a => le_iSup₂_of_le a le_rfl le_rfl⟩
    rw [IsModuleCont, ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨e, he0, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    obtain ⟨δ, hδ, hδ'⟩ := h e (by exact_mod_cast he0)
    filter_upwards [Iio_mem_nhds (Real.toNNReal_pos.mpr hδ)] with t ht
    refine iSup₂_le fun a ha => ?_
    have : (d a : ℝ) ≤ δ := by
      have := (ha.trans_lt ht).le
      rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hδ.le] at this
    calc ENNReal.ofReal (r a) ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (hδ' a this)
      _ ≤ ε := by rw [ENNReal.ofReal_coe_nnreal]; exact heε.le

/-- Lemme technique : dans une condition `ε`-`δ`, on peut remplacer les inégalités strictes par
des inégalités larges. -/
theorem epsDelta_lt_iff_le {α : Type*} (r d : α → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a, d a < δ → r a < ε) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a, d a ≤ δ → r a ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    exact ⟨δ / 2, half_pos hδ, fun a ha => (h' a (by linarith)).le⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun a ha => by linarith [h' a ha.le]⟩

/-- **Lemme `lem:contDistance` (Continuité entre espaces métriques).** Pour `f : X → Y` entre
espaces métriques et `x ∈ X`, sont équivalents : (i) `f` est continue en `x` ;
(ii) `∀ ε > 0, ∃ δ > 0, ∀ x', d(x,x') < δ ⇒ d(f x, f x') < ε` ; (iii) idem avec `≤` ;
(iv) il existe un module de continuité `ω_x` avec `d(f x, f x') ≤ ω_x(d(x,x'))` pour tout `x'` ;
(v) pour toute suite `xₙ → x`, on a `f(xₙ) → f(x)`. -/
theorem lem_contDistance [MetricSpace X] [MetricSpace Y] (f : X → Y) (x : X) :
    List.TFAE
      [ ContinuousAt f x,
        ∀ ε > 0, ∃ δ > 0, ∀ x', dist x x' < δ → dist (f x) (f x') < ε,
        ∀ ε > 0, ∃ δ > 0, ∀ x', dist x x' ≤ δ → dist (f x) (f x') ≤ ε,
        ∃ ω, IsModuleCont ω ∧ ∀ x', edist (f x) (f x') ≤ ω (nndist x x'),
        ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 (f x)) ] := by
  tfae_have 1 ↔ 2 := by
    rw [Metric.continuousAt_iff]
    simp only [dist_comm]
  tfae_have 2 ↔ 3 :=
    epsDelta_lt_iff_le (fun x' => dist (f x) (f x')) (fun x' => dist x x')
  tfae_have 3 ↔ 4 := by
    simp only [edist_dist]
    rw [exists_moduleCont_iff (fun x' => dist (f x) (f x')) (fun x' => nndist x x')]
    simp only [coe_nndist]
  tfae_have 1 ↔ 5 := tendsto_nhds_iff_seq_tendsto
  tfae_finish

/-- **Déf. `def:unifContinu` (Uniforme continuité).** `f` est uniformément continue (au sens
Mathlib `UniformContinuous`) ssi il existe un module de continuité `ω` tel que
`d_Y(f x, f x') ≤ ω(d_X(x, x'))` pour tous `x, x'`. -/
theorem def_unifContinu [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    UniformContinuous f ↔ ∃ ω, IsModuleCont ω ∧ ∀ x x', edist (f x) (f x') ≤ ω (nndist x x') := by
  have h1 := epsDelta_lt_iff_le (fun p : X × X => dist (f p.1) (f p.2)) (fun p => dist p.1 p.2)
  have h2 := exists_moduleCont_iff (fun p : X × X => dist (f p.1) (f p.2))
    (fun p => nndist p.1 p.2)
  simp only [Prod.forall, coe_nndist] at h1 h2
  simp only [edist_dist]
  rw [h2, ← h1, Metric.uniformContinuous_iff]

/-- **Déf. `def:unifContinu` (Uniforme continuité, forme équivalente).**
`f` est uniformément continue ssi `∀ ε > 0, ∃ δ > 0, ∀ x x', d_X(x,x') ≤ δ ⇒
d_Y(f x, f x') ≤ ε`. -/
theorem def_unifContinu_epsDelta [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x x', dist x x' ≤ δ → dist (f x) (f x') ≤ ε := by
  have h1 := epsDelta_lt_iff_le (fun p : X × X => dist (f p.1) (f p.2)) (fun p => dist p.1 p.2)
  simp only [Prod.forall] at h1
  rw [Metric.uniformContinuous_iff]
  simp only [gt_iff_lt]
  exact h1

/-- **Déf. `def:unifContinu` (Applications höldériennes).** Pour `α ∈ ]0,1[`, `f` est
`α`-höldérienne au sens du cours (`∃ K ∈ ℝ, d_Y(f x, f x') ≤ K d_X(x,x')^α`) ssi elle l'est
au sens Mathlib `HolderWith C α f` pour une constante `C ≥ 0`.
Remarque : l'hypothèse `α ∈ ]0,1[` du cours n'est pas utilisée par la preuve. -/
theorem def_unifContinu_holder [MetricSpace X] [MetricSpace Y] (f : X → Y) (α : ℝ≥0)
    (_hα : α ∈ Ioo 0 1) :
    (∃ K : ℝ, ∀ x x', dist (f x) (f x') ≤ K * dist x x' ^ (α : ℝ)) ↔
      ∃ C : ℝ≥0, HolderWith C α f := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K.toNNReal, fun x x' => ?_⟩
    have h := ENNReal.ofReal_rpow_of_nonneg (dist_nonneg (x := x) (y := x')) α.2
    rw [edist_dist, edist_dist]
    erw [h]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc dist (f x) (f x') ≤ K * dist x x' ^ (α : ℝ) := hK x x'
      _ ≤ K.toNNReal * dist x x' ^ (α : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (by positivity)
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.dist_le⟩

/-- **Déf. `def:unifContinu` (Applications lipschitziennes).** `f` est lipschitzienne au sens du
cours (`∃ K ∈ ℝ, d_Y(f x, f x') ≤ K d_X(x,x')`) ssi `LipschitzWith K f` pour un `K ≥ 0`. -/
theorem def_unifContinu_lipschitz [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    (∃ K : ℝ, ∀ x x', dist (f x) (f x') ≤ K * dist x x') ↔ ∃ K : ℝ≥0, LipschitzWith K f :=
  ⟨fun ⟨_, hK⟩ => ⟨_, LipschitzWith.of_dist_le' hK⟩, fun ⟨K, hK⟩ => ⟨K, hK.dist_le_mul⟩⟩

/-- **Déf. `def:unifContinu` (Applications contractantes).** `f` est `K`-lipschitzienne pour un
certain `K < 1` ssi `LipschitzWith K f` pour un `K ∈ [0, 1[`. (Mathlib `ContractingWith K f`
désigne la même notion, mais seulement pour `f : X → X`.) -/
theorem def_unifContinu_contractante [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    (∃ K : ℝ, K < 1 ∧ ∀ x x', dist (f x) (f x') ≤ K * dist x x') ↔
      ∃ K : ℝ≥0, K < 1 ∧ LipschitzWith K f :=
  ⟨fun ⟨_, h1, hK⟩ => ⟨_, Real.toNNReal_lt_one.mpr h1, LipschitzWith.of_dist_le' hK⟩,
    fun ⟨K, h1, hK⟩ => ⟨K, by exact_mod_cast h1, hK.dist_le_mul⟩⟩

/-! ### Convergence simple, convergence uniforme, équicontinuité -/

/-- Lemme technique : inégalité triangulaire pour `min a ·`. -/
theorem min_le_min_add_min {a c p q : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : c ≤ p + q) : min a c ≤ min a p + min a q := by
  have := le_min ha hq
  rcases le_total a p with h1 | h1
  · rw [min_eq_left h1]; linarith [min_le_left a c]
  · rw [min_eq_right h1]
    rcases le_total a q with h2 | h2
    · rw [min_eq_left h2]; linarith [min_le_left a c]
    · rw [min_eq_right h2]; linarith [min_le_right a c]

section CvSimple

variable {Z : ℕ → Type*} [∀ n, MetricSpace (Z n)]

/-- La distance de `prop:distCvSimple` sur le produit `Πₙ Zₙ` d'une famille dénombrable
d'espaces métriques : `d(x, y) := sup_n min{2⁻ⁿ, dₙ(xₙ, yₙ)}`. Le cours écrit `max` ; le `sup`
est effectivement atteint (`distCvSimple_max`). -/
noncomputable def distCvSimple (x y : ∀ n, Z n) : ℝ :=
  ⨆ n, min ((2 : ℝ)⁻¹ ^ n) (dist (x n) (y n))

/-- Les termes définissant `distCvSimple` sont majorés par `1`. -/
theorem distCvSimple_bddAbove (x y : ∀ n, Z n) :
    BddAbove (range fun n => min ((2 : ℝ)⁻¹ ^ n) (dist (x n) (y n))) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))⟩

/-- Chaque terme `min{2⁻ⁿ, dₙ(xₙ, yₙ)}` est majoré par `distCvSimple x y`. -/
theorem le_distCvSimple (x y : ∀ n, Z n) (n : ℕ) :
    min ((2 : ℝ)⁻¹ ^ n) (dist (x n) (y n)) ≤ distCvSimple x y :=
  le_ciSup (distCvSimple_bddAbove x y) n

/-- Le `sup` définissant `distCvSimple` est un `max` (comme écrit dans le cours). -/
theorem distCvSimple_max (x y : ∀ n, Z n) :
    ∃ n, distCvSimple x y = min ((2 : ℝ)⁻¹ ^ n) (dist (x n) (y n)) := by
  set u : ℕ → ℝ := fun n => min ((2 : ℝ)⁻¹ ^ n) (dist (x n) (y n))
  by_contra hcon
  push Not at hcon
  have hlt : ∀ n, u n < distCvSimple x y :=
    fun n => lt_of_le_of_ne (le_distCvSimple x y n) (hcon n).symm
  have hpos : 0 < distCvSimple x y :=
    lt_of_le_of_lt (le_min (by positivity) dist_nonneg) (hlt 0)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨m, -, hm⟩ := (Finset.range (N + 1)).exists_max_image u ⟨0, by simp⟩
  have : distCvSimple x y ≤ max (u m) ((2 : ℝ)⁻¹ ^ N) := by
    refine ciSup_le fun n => ?_
    rcases le_or_gt n N with hn | hn
    · exact (hm n (Finset.mem_range.mpr (by omega))).trans (le_max_left _ _)
    · exact (min_le_left _ _).trans ((pow_le_pow_of_le_one (by norm_num) (by norm_num)
        hn.le).trans (le_max_right _ _))
  exact absurd this (not_le.mpr (max_lt (hlt m) hN))

/-- `distCvSimple` satisfait les axiomes de distance. -/
theorem isDistance_distCvSimple : IsDistance (distCvSimple (Z := Z)) := by
  refine ⟨fun x y => ⟨(le_min (by positivity) dist_nonneg).trans (le_distCvSimple x y 0), ?_⟩,
    fun x y => by simp only [distCvSimple, dist_comm], fun x y z => ?_⟩
  · constructor
    · intro h
      funext n
      have h1 := (le_distCvSimple x y n).trans h.le
      rcases min_le_iff.mp h1 with h2 | h2
      · exact (not_le.mpr (by positivity) h2).elim
      · exact dist_le_zero.mp h2
    · rintro rfl
      simp [distCvSimple]
  · refine ciSup_le fun n => ?_
    exact (min_le_min_add_min (by positivity) dist_nonneg dist_nonneg (dist_triangle _ _ _)).trans
      (add_le_add (le_distCvSimple x y n) (le_distCvSimple y z n))

/-- **Prop. `prop:distCvSimple` (Distance associée à la convergence simple).** Pour une famille
dénombrable `(Zₙ, dₙ)` d'espaces métriques, `d(x, y) := maxₙ min{2⁻ⁿ, dₙ(xₙ, yₙ)}` est une
distance sur `Πₙ Zₙ` qui métrise la topologie produit : ses boules `{y | d(x,y) < r}`, `r > 0`,
forment une base de voisinages de `x` pour la topologie produit (Mathlib `Pi.topologicalSpace`). -/
theorem prop_distCvSimple :
    IsDistance (distCvSimple (Z := Z)) ∧
      ∀ x : ∀ n, Z n, (𝓝 x).HasBasis (fun r : ℝ => 0 < r)
        (fun r => {y | distCvSimple x y < r}) := by
  refine ⟨isDistance_distCvSimple, fun x => ?_⟩
  have hb := @Metric.nhds_basis_ball _
    (metricSpaceOfIsDistance _ (isDistance_distCvSimple (Z := Z))).toPseudoMetricSpace x
  have heq : @nhds _ (metricSpaceOfIsDistance _
      (isDistance_distCvSimple (Z := Z))).toUniformSpace.toTopologicalSpace x = 𝓝 x := by
    apply le_antisymm
    · rw [nhds_pi]
      refine Filter.le_pi.mpr fun n => (hb.tendsto_iff Metric.nhds_basis_ball).mpr
        fun ε hε => ⟨min ε ((2 : ℝ)⁻¹ ^ n), lt_min hε (by positivity), fun y hy => ?_⟩
      change distCvSimple y x < min ε ((2 : ℝ)⁻¹ ^ n) at hy
      have h1 := (le_distCvSimple y x n).trans_lt hy
      rw [Metric.mem_ball]
      rcases le_total ((2 : ℝ)⁻¹ ^ n) (dist (y n) (x n)) with h2 | h2
      · rw [min_eq_left h2] at h1; linarith [min_le_right ε ((2 : ℝ)⁻¹ ^ n)]
      · rw [min_eq_right h2] at h1; exact h1.trans_le (min_le_left _ _)
    · refine hb.ge_iff.mpr fun ε hε => ?_
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2 : ℝ)⁻¹ < 1)
      have hev : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N, dist (y n) (x n) < ε / 2 :=
        (Finset.range N).eventually_all.mpr fun n _ =>
          (continuous_apply n).continuousAt.eventually (Metric.ball_mem_nhds (x n) (half_pos hε))
      filter_upwards [hev] with y hy
      change distCvSimple y x < ε
      have : distCvSimple y x ≤ ε / 2 := by
        refine ciSup_le fun n => ?_
        rcases lt_or_ge n N with hn | hn
        · exact (min_le_right _ _).trans (hy n (Finset.mem_range.mpr hn)).le
        · exact (min_le_left _ _).trans
            ((pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN.le)
      linarith
  refine (heq ▸ hb).to_hasBasis (fun r hr => ⟨r, hr, fun y hy => ?_⟩)
    (fun r hr => ⟨r, hr, fun y hy => ?_⟩)
  · change distCvSimple x y < r at hy
    change distCvSimple y x < r
    rwa [isDistance_distCvSimple.2.1]
  · change distCvSimple y x < r at hy
    change distCvSimple x y < r
    rwa [isDistance_distCvSimple.2.1]

end CvSimple

/-- **Déf. `def:dist_unif` (Distance associée à la convergence uniforme).** Sur `Y^I`, muni de la
topologie de la convergence uniforme (Mathlib `I →ᵤ Y`), `min{1, d_∞}` avec
`d_∞(f, g) = sup_i d(f i, g i)` est une distance définissant cette topologie (cf.
`rem:distInfinie`). Remarque : le cours traite un produit `Πᵢ Xᵢ` d'espaces éventuellement
distincts ; Mathlib ne définit la topologie de la convergence uniforme que pour `Y^I`
(cas utilisé dans `rem:equicont`), d'où la restriction à ce cas. -/
theorem def_dist_unif {I : Type*} [MetricSpace Y] :
    IsDistance (fun f g : I →ᵤ Y =>
        (min 1 (⨆ i, edist (UniformFun.toFun f i) (UniformFun.toFun g i))).toReal) ∧
      ∀ f : I →ᵤ Y, (𝓝 f).HasBasis (fun r : ℝ => 0 < r)
        (fun r => {g | (min 1 (⨆ i, edist (UniformFun.toFun f i)
          (UniformFun.toFun g i))).toReal < r}) :=
  rem_distInfinie (X := I →ᵤ Y)

/-- **Rem. `rem:equicont` (i) (Équicontinuité en un point).** La famille `(fᵢ)` est
équicontinue en `x` au sens du cours (module de continuité `ω_x` commun :
`d(fᵢ x, fᵢ x') ≤ ω_x(d(x, x'))`) ssi elle l'est au sens Mathlib `EquicontinuousAt`. -/
theorem rem_equicont_at [MetricSpace X] [MetricSpace Y] {I : Type*} (f : I → X → Y) (x : X) :
    (∃ ω, IsModuleCont ω ∧ ∀ x', ∀ i, edist (f i x) (f i x') ≤ ω (nndist x x')) ↔
      EquicontinuousAt f x := by
  have h1 := epsDelta_lt_iff_le (fun p : X × I => dist (f p.2 x) (f p.2 p.1))
    (fun p => dist x p.1)
  have h2 := exists_moduleCont_iff (fun p : X × I => dist (f p.2 x) (f p.2 p.1))
    (fun p => nndist x p.1)
  simp only [Prod.forall, coe_nndist] at h1 h2
  simp only [edist_dist]
  rw [h2, ← h1, Metric.equicontinuousAt_iff]
  simp only [gt_iff_lt, dist_comm x]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    exact ⟨δ, hδ, fun x' hx' i => h' x' i hx'⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    exact ⟨δ, hδ, fun x' i hx' => h' x' hx' i⟩

/-- **Rem. `rem:equicont` (i), reformulation.** La famille `(fᵢ)` est équicontinue en `x` ssi
`F : x ↦ (fᵢ x)ᵢ` est continue en `x` pour la topologie de la convergence uniforme sur `Y^I`. -/
theorem rem_equicont_at_unif [MetricSpace X] [MetricSpace Y] {I : Type*} (f : I → X → Y)
    (x : X) : EquicontinuousAt f x ↔
      ContinuousAt (fun x' => UniformFun.ofFun (fun i => f i x')) x :=
  equicontinuousAt_iff_continuousAt

/-- **Rem. `rem:equicont` (ii) (Uniforme équicontinuité).** La famille `(fᵢ)` est uniformément
équicontinue au sens du cours (module de continuité `ω` commun) ssi elle l'est au sens Mathlib
`UniformEquicontinuous`. -/
theorem rem_equicont_unif [MetricSpace X] [MetricSpace Y] {I : Type*} (f : I → X → Y) :
    (∃ ω, IsModuleCont ω ∧ ∀ x x', ∀ i, edist (f i x) (f i x') ≤ ω (nndist x x')) ↔
      UniformEquicontinuous f := by
  have h1 := epsDelta_lt_iff_le (fun p : X × X × I => dist (f p.2.2 p.1) (f p.2.2 p.2.1))
    (fun p => dist p.1 p.2.1)
  have h2 := exists_moduleCont_iff (fun p : X × X × I => dist (f p.2.2 p.1) (f p.2.2 p.2.1))
    (fun p => nndist p.1 p.2.1)
  simp only [Prod.forall, coe_nndist] at h1 h2
  simp only [edist_dist]
  rw [h2, ← h1, Metric.uniformEquicontinuous_iff]
  simp only [gt_iff_lt]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    exact ⟨δ, hδ, fun x x' hx' i => h' x x' i hx'⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    exact ⟨δ, hδ, fun x x' i hx' => h' x x' hx' i⟩

/-- **Rem. `rem:equicont` (ii), reformulation.** La famille `(fᵢ)` est uniformément
équicontinue ssi `F : x ↦ (fᵢ x)ᵢ` est uniformément continue à valeurs dans `Y^I` muni de la
structure de la convergence uniforme. -/
theorem rem_equicont_unif_unif [MetricSpace X] [MetricSpace Y] {I : Type*} (f : I → X → Y) :
    UniformEquicontinuous f ↔
      UniformContinuous (fun x' => UniformFun.ofFun (fun i => f i x')) :=
  uniformEquicontinuous_iff_uniformContinuous

end M1Analyse
