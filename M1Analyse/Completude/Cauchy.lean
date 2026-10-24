/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import M1Analyse.TopologieGenerale.EVTLC

/-!
# §2.1 Critère de Cauchy (`subsec:Cauchy`)

Source : `Include/Completude.tex`, sous-section `subsec:Cauchy` (l'introduction du chapitre ne
contient pas d'énoncé numéroté).

Les objets du cours sont ceux de Mathlib : suite de Cauchy = `CauchySeq`, espace complet =
`CompleteSpace`, partie complète = `IsComplete`, Banach = evn + `CompleteSpace`,
`L(E,F)` = `E →L[𝕜] F`, dual = `StrongDual 𝕜 E`. Un Fréchet est représenté par un evtlc
`E` (famille `p : SeminormFamily 𝕜 E ℕ` avec `WithSeminorms p`, cf. `subsec:evtlc`), muni de sa
structure uniforme de groupe topologique ; on montre que la complétude au sens de Mathlib équivaut
à la complétude pour la distance `evtlcDist` du cours (`eqdef:evtlc_dist`).
-/

open Set Filter Topology Uniformity Finset

namespace M1Analyse

section Metrique

variable {X : Type*} [MetricSpace X]

/-- **Déf. `def:suiteCauchy` (Suite de Cauchy).** Une suite `(x_n)` d'un espace métrique est de
Cauchy ssi `∀ ε > 0, ∃ N, ∀ p, q ≥ N, d(x_p, x_q) ≤ ε`. -/
theorem def_suiteCauchy (x : ℕ → X) :
    CauchySeq x ↔ ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, dist (x p) (x q) ≤ ε := by
  rw [Metric.cauchySeq_iff]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun p hp q hq => (hN p hp q hq).le⟩
  · obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    exact ⟨N, fun p hp q hq => (hN p hp q hq).trans_lt (half_lt_self hε)⟩

/-- **Déf. `def:suiteCauchy`, propriétés.** Une suite de Cauchy est bornée et admet au plus une
limite ; une suite de Cauchy admettant une sous-suite convergente est convergente ;
réciproquement toute suite convergente est de Cauchy. -/
theorem def_suiteCauchy_proprietes :
    (∀ x : ℕ → X, CauchySeq x → Bornology.IsBounded (range x)) ∧
    (∀ (x : ℕ → X) (l l' : X), Tendsto x atTop (𝓝 l) → Tendsto x atTop (𝓝 l') → l = l') ∧
    (∀ (x : ℕ → X) (φ : ℕ → ℕ) (l : X), CauchySeq x → StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 l) → Tendsto x atTop (𝓝 l)) ∧
    (∀ (x : ℕ → X) (l : X), Tendsto x atTop (𝓝 l) → CauchySeq x) :=
  ⟨fun _ hx => hx.isBounded_range,
    fun _ _ _ h h' => tendsto_nhds_unique h h',
    fun _ _ _ hx hφ h => tendsto_nhds_of_cauchySeq_of_subseq hx hφ.tendsto_atTop h,
    fun _ _ h => h.cauchySeq⟩

/-- **Éq. `eqdef:suiteCauchyMin`.** Une suite `(x_n)` est de Cauchy ssi il existe une suite
`ε(n) → 0` telle que `d(x_p, x_q) ≤ ε(min(p, q))` pour tous `p, q ∈ ℕ`. -/
theorem eqdef_suiteCauchyMin (x : ℕ → X) :
    CauchySeq x ↔ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ p q : ℕ, dist (x p) (x q) ≤ ε (min p q) := by
  constructor
  · intro hx
    obtain ⟨b, -, hb, hb0⟩ := cauchySeq_iff_le_tendsto_0.1 hx
    exact ⟨b, hb0, fun p q => hb p q _ (min_le_left p q) (min_le_right p q)⟩
  · rintro ⟨ε, hε0, hε⟩
    rw [def_suiteCauchy]
    intro δ hδ
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hε0) δ hδ
    refine ⟨N, fun p hp q hq => (hε p q).trans ?_⟩
    have := hN (min p q) (le_min hp hq)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le

/-- **Déf. `def:complet` (Complétude), espace métrique.** Un espace métrique est complet
(`CompleteSpace`) ssi toutes ses suites de Cauchy y sont convergentes. -/
theorem def_complet :
    CompleteSpace X ↔ ∀ x : ℕ → X, CauchySeq x → ∃ l, Tendsto x atTop (𝓝 l) :=
  ⟨fun _ _ hx => cauchySeq_tendsto_of_complete hx, Metric.complete_of_cauchySeq_tendsto⟩

end Metrique

/-- **Déf. `def:complet` (Complétude), espace de Banach.** Un evn `E` est un Banach
(`CompleteSpace E`) ssi toute suite vérifiant le critère de Cauchy pour la norme
(`∀ ε > 0, ∃ N, ∀ p, q ≥ N, ‖x_p - x_q‖ ≤ ε`) admet une limite `l` (`‖x_n - l‖ → 0`). -/
theorem def_complet_banach {E : Type*} [NormedAddCommGroup E] :
    CompleteSpace E ↔ ∀ x : ℕ → E,
      (∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, ‖x p - x q‖ ≤ ε) →
      ∃ l, Tendsto (fun n => ‖x n - l‖) atTop (𝓝 0) := by
  simp only [def_complet, def_suiteCauchy, dist_eq_norm, ← tendsto_iff_norm_sub_tendsto_zero]

section Frechet

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [UniformSpace E] [IsUniformAddGroup E] {p : SeminormFamily 𝕜 E ℕ}

/-- Les ensembles `{(x, y) | d(x, y) < η}`, `η > 0`, forment une base de la structure uniforme
d'un evtlc muni d'une famille dénombrable de semi-normes, `d` étant la distance
`eqdef:evtlc_dist`. -/
lemma uniformity_hasBasis_evtlcDist (hp : WithSeminorms p) :
    (𝓤 E).HasBasis (fun η : ℝ => 0 < η) (fun η => {q | evtlcDist p q.1 q.2 < η}) := by
  rw [uniformity_eq_comap_nhds_zero E]
  refine ((prop_distanceEvtlcs_nhds hp 0).comap (fun q : E × E => q.2 - q.1)).congr
    (fun _ => Iff.rfl) fun η _ => ?_
  ext q
  simp only [Set.mem_preimage, mem_ofPred_eq, evtlcDist, zero_sub, map_neg_eq_map,
    map_sub_rev (p _) q.2]

omit [IsUniformAddGroup E] in
/-- La convergence dans un evtlc à famille dénombrable de semi-normes équivaut à la convergence
pour la distance `eqdef:evtlc_dist`. -/
lemma tendsto_iff_evtlcDist (hp : WithSeminorms p) (u : ℕ → E) (x : E) :
    Tendsto u atTop (𝓝 x) ↔ Tendsto (fun n => evtlcDist p (u n) x) atTop (𝓝 0) := by
  rw [(prop_distanceEvtlcs_nhds hp x).tendsto_right_iff, Metric.tendsto_atTop]
  refine ⟨fun h η hη => ?_, fun h η hη => ?_⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.1 (h η hη)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (evtlcDist_nonneg p _ _), evtlcDist_comm]
    exact hN n hn
  · obtain ⟨N, hN⟩ := h η hη
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (evtlcDist_nonneg p _ _), evtlcDist_comm] at this

/-- **Déf. `def:complet` (Complétude), espace de Fréchet.** Soit `E` un evtlc muni d'une famille
dénombrable de semi-normes `(|·|_n)_{n ∈ ℕ}`, et `d` la distance associée (`eqdef:evtlc_dist`).
Alors `E` est complet au sens de Mathlib (pour sa structure uniforme de groupe topologique) ssi
toute suite de Cauchy pour `d` converge pour `d` ; i.e. `E` est un Fréchet au sens du cours ssi
`CompleteSpace E`.
Remarque : le cours suppose de plus `E` séparé ; cette hypothèse n'est pas utilisée ici. -/
theorem def_complet_frechet (hp : WithSeminorms p) :
    CompleteSpace E ↔ ∀ u : ℕ → E,
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, evtlcDist p (u m) (u n) ≤ ε) →
      ∃ x, Tendsto (fun n => evtlcDist p (u n) x) atTop (𝓝 0) := by
  have hB := uniformity_hasBasis_evtlcDist hp
  have hcauchy : ∀ u : ℕ → E, CauchySeq u ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, evtlcDist p (u m) (u n) ≤ ε := by
    intro u
    rw [hB.cauchySeq_iff]
    refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
    · obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun m hm n hn => (hN m hm n hn).le⟩
    · obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
      exact ⟨N, fun m hm n hn => (hN m hm n hn).trans_lt (half_lt_self hε)⟩
  have : (𝓤 E).IsCountablyGenerated :=
    (hB.to_hasBasis (p' := fun _ : ℕ => True) (s' := fun n : ℕ =>
        {q : E × E | evtlcDist p q.1 q.2 < 1 / ((n : ℝ) + 1)})
      (fun η hη => by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
        exact ⟨n, trivial, fun q hq => lt_trans hq hn⟩)
      (fun n _ => ⟨_, Nat.one_div_pos_of_nat, subset_rfl⟩)).isCountablyGenerated
  refine ⟨fun _ u hu => ?_, fun h => UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_⟩
  · obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete ((hcauchy u).2 hu)
    exact ⟨x, (tendsto_iff_evtlcDist hp u x).1 hx⟩
  · obtain ⟨x, hx⟩ := h u ((hcauchy u).1 hu)
    exact ⟨x, (tendsto_iff_evtlcDist hp u x).2 hx⟩

end Frechet

/-- **Lemme `lem:serie_Banach` (Séries dans un Banach).** Un evn `E` est complet ssi toute
série absolument convergente (`∑ ‖x_n‖ < ∞`) y est convergente (la suite des sommes partielles
`∑_{n < N} x_n` admet une limite).
Preuve (via Mathlib, même stratégie que le cours) :
`NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace` (sommes partielles de Cauchy ;
réciproquement, sous-suite à incréments sommables d'une suite de Cauchy). -/
theorem lem_serie_Banach {E : Type*} [NormedAddCommGroup E] :
    CompleteSpace E ↔ ∀ x : ℕ → E, Summable (fun n => ‖x n‖) →
      ∃ l, Tendsto (fun N => ∑ n ∈ range N, x n) atTop (𝓝 l) :=
  NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace.symm

/-- **Prop. `prop:fermeComplet`.** Une partie `A` d'un espace métrique complet `X` est complète
(pour la distance induite, i.e. le sous-espace `↥A` est complet) ssi elle est fermée. On donne
aussi la version `IsComplete A` de Mathlib.
Preuve (différente du cours) : lemmes Mathlib `IsComplete.isClosed` et `IsClosed.isComplete`
(formulés avec les filtres de Cauchy), sans l'argument séquentiel du cours. -/
theorem prop_fermeComplet {X : Type*} [MetricSpace X] [CompleteSpace X] (A : Set X) :
    (CompleteSpace A ↔ IsClosed A) ∧ (IsComplete A ↔ IsClosed A) :=
  have h : IsComplete A ↔ IsClosed A := ⟨IsComplete.isClosed, IsClosed.isComplete⟩
  ⟨completeSpace_coe_iff_isComplete.trans h, h⟩

/-- **Prop. `prop:LEFcomplet`.** Soient `E` un evn et `F` un Banach. Alors `L(E,F)` est un Banach,
et en particulier le dual `E*` est un Banach.
Preuve (différente du cours) : instances de complétude de Mathlib : `L(E,F)` est fermé (linéarité
et continuité passent à la limite) dans l'espace complet des applications `E → F` muni de la
convergence uniforme sur les bornés. -/
theorem prop_LEFcomplet {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] :
    CompleteSpace (E →L[𝕜] F) ∧ CompleteSpace (StrongDual 𝕜 E) :=
  ⟨inferInstance, inferInstance⟩

end M1Analyse
