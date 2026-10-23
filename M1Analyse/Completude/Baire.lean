/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ZetaValues

/-!
# §2.5 Théorème de Baire (`subsec:Baire`)

Source : `Include/Completude.tex`, sous-section `subsec:Baire`.

Les objets du cours sont ceux de Mathlib : `IsGδ`, `residual X` (parties grasses / co-maigres),
`IsMeagre`, `BaireSpace` (dont une instance est fournie pour tout espace métrique complet par
`BaireSpace.of_pseudoEMetricSpace_completeSpace`). Le diamètre `δ_n` du cours, qui peut valoir
`+∞`, est `Metric.ediam` (à valeurs dans `ℝ≥0∞`).
-/

open Set Filter Topology MeasureTheory

namespace M1Analyse

variable {X : Type*}

/-- **Lemme `lem:fermeEmboite` (Fermés emboités).** Dans un espace métrique complet, une suite
décroissante de fermés non vides dont le diamètre tend vers `0` a pour intersection un
singleton. -/
theorem lem_fermeEmboite [MetricSpace X] [CompleteSpace X] (F : ℕ → Set X)
    (hF : ∀ n, IsClosed (F n)) (hne : ∀ n, (F n).Nonempty) (hdec : Antitone F)
    (hdiam : Tendsto (fun n => Metric.ediam (F n)) atTop (𝓝 0)) :
    ∃ x, ⋂ n, F n = {x} := by
  choose x hx using hne
  have hcau : CauchySeq x := by
    refine EMetric.cauchySeq_iff_le_tendsto_0.2 ⟨_, fun n m N hn hm => ?_, hdiam⟩
    exact Metric.edist_le_ediam_of_mem (hdec hn (hx n)) (hdec hm (hx m))
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hyF : ∀ n, y ∈ F n := fun n =>
    (hF n).mem_of_tendsto hy (eventually_atTop.2 ⟨n, fun p hp => hdec hp (hx p)⟩)
  refine ⟨y, Subset.antisymm (fun z hz => ?_) (singleton_subset_iff.2 (mem_iInter.2 hyF))⟩
  rw [mem_iInter] at hz
  have h0 : edist z y ≤ 0 :=
    ge_of_tendsto' hdiam fun n => Metric.edist_le_ediam_of_mem (hz n) (hyF n)
  exact edist_le_zero.1 h0

/-- **Th. `th:BaireOuvert` (Baire).** Dans un espace métrique complet, une intersection
dénombrable d'ouverts denses est dense. -/
theorem th_BaireOuvert [MetricSpace X] [CompleteSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hd : ∀ n, Dense (U n)) : Dense (⋂ n, U n) :=
  dense_iInter_of_isOpen_nat hU hd

/-- **Cor. `corol:BaireFerme` (Baire, complémentaire).** Dans un espace métrique complet, une
réunion dénombrable de fermés d'intérieur vide est d'intérieur vide. -/
theorem corol_BaireFerme [MetricSpace X] [CompleteSpace X] (F : ℕ → Set X)
    (hF : ∀ n, IsClosed (F n)) (hint : ∀ n, interior (F n) = ∅) :
    interior (⋃ n, F n) = ∅ := by
  have hd : Dense (⋂ n, (F n)ᶜ) :=
    th_BaireOuvert _ (fun n => (hF n).isOpen_compl)
      (fun n => interior_eq_empty_iff_dense_compl.1 (hint n))
  rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
  exact hd

/-- **Rem. `rem:terminologieBaire` (`G_δ`).** Un `G_δ` (Mathlib : `IsGδ`) est une intersection
dénombrable d'ouverts. -/
theorem rem_terminologieBaire_Gdelta [TopologicalSpace X] (s : Set X) :
    IsGδ s ↔ ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ s = ⋂ n, U n :=
  isGδ_iff_eq_iInter_nat

/-- **Rem. `rem:terminologieBaire` (Ensemble maigre).** Dans un espace métrique complet, une
partie est maigre (Mathlib : `IsMeagre`) ssi elle est contenue dans un `F_σ` (réunion
dénombrable de fermés) d'intérieur vide.
Remarque : la définition de Mathlib (réunion dénombrable de parties nulle part denses) coïncide
avec celle du cours dans tout espace de Baire, en particulier dans un espace métrique complet. -/
theorem rem_terminologieBaire_maigre [MetricSpace X] [CompleteSpace X] (s : Set X) :
    IsMeagre s ↔ ∃ F : ℕ → Set X, (∀ n, IsClosed (F n)) ∧ interior (⋃ n, F n) = ∅ ∧
      s ⊆ ⋃ n, F n := by
  unfold IsMeagre
  rw [mem_residual]
  constructor
  · rintro ⟨t, hts, hG, hd⟩
    obtain ⟨U, hU, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hG
    refine ⟨fun n => (U n)ᶜ, fun n => (hU n).isClosed_compl, ?_, ?_⟩
    · rw [← compl_iInter, interior_compl, hd.closure_eq, compl_univ]
    · rw [← compl_iInter]; exact subset_compl_comm.1 hts
  · rintro ⟨F, hF, hint, hs⟩
    refine ⟨(⋃ n, F n)ᶜ, compl_subset_compl.2 hs, ?_, ?_⟩
    · rw [compl_iUnion]
      exact IsGδ.iInter_of_isOpen fun n => (hF n).isOpen_compl
    · exact interior_eq_empty_iff_dense_compl.1 hint

/-- **Rem. `rem:terminologieBaire` (Ensemble gras).** Le complémentaire d'un ensemble maigre
est dit co-maigre ou gras (Mathlib : `s ∈ residual X`) ; dans un espace métrique complet,
c'est exactement une partie contenant un `G_δ` dense. -/
theorem rem_terminologieBaire_gras [MetricSpace X] [CompleteSpace X] (s : Set X) :
    (IsMeagre sᶜ ↔ s ∈ residual X) ∧ (s ∈ residual X ↔ ∃ t ⊆ s, IsGδ t ∧ Dense t) := by
  refine ⟨?_, mem_residual⟩
  unfold IsMeagre
  rw [compl_compl]

/-- L'ouvert `U_n` de l'exemple `ex:GrasQ`, associé à une énumération `(q_k)_{k > 0}` de `ℚ` :
`U_n := ⋃_{k > 0} ]q_k - 1/(n k²), q_k + 1/(n k²)[`. -/
noncomputable def exGrasQ_U (q : ℕ → ℚ) (n : ℕ) : Set ℝ :=
  ⋃ k, ⋃ (_ : 0 < k), Ioo ((q k : ℝ) - 1 / (n * k ^ 2)) ((q k : ℝ) + 1 / (n * k ^ 2))

/-- **Ex. `ex:GrasQ`, première partie.** Si `(q_k)_{k > 0}` énumère `ℚ`, alors pour tout `n > 0`,
`U_n` est un ouvert dense de `ℝ`, de mesure `|U_n| ≤ π²/(3n)`.
Remarque : l'énumération est modélisée par `q : ℕ → ℚ` dont la restriction aux indices `k > 0`
est surjective (la valeur `q 0` ne sert pas). -/
theorem ex_GrasQ_U (q : ℕ → ℚ) (hq : ∀ r : ℚ, ∃ k, 0 < k ∧ q k = r) (n : ℕ) (hn : 0 < n) :
    IsOpen (exGrasQ_U q n) ∧ Dense (exGrasQ_U q n) ∧
      volume (exGrasQ_U q n) ≤ ENNReal.ofReal (Real.pi ^ 2 / (3 * n)) := by
  refine ⟨isOpen_iUnion fun k => isOpen_iUnion fun _ => isOpen_Ioo, ?_, ?_⟩
  · refine Rat.isDenseEmbedding_coe_real.dense.mono ?_
    rintro _ ⟨r, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hq r
    have : (0 : ℝ) < 1 / (n * k ^ 2) := by positivity
    exact mem_iUnion₂.2 ⟨k, hk, by constructor <;> linarith⟩
  · have hsum : HasSum (fun k : ℕ => 2 / n * (1 / (k : ℝ) ^ 2)) (2 / n * (Real.pi ^ 2 / 6)) :=
      hasSum_zeta_two.mul_left _
    calc volume (exGrasQ_U q n)
        ≤ ∑' k : ℕ, volume (Ioo ((q k : ℝ) - 1 / (n * k ^ 2)) ((q k : ℝ) + 1 / (n * k ^ 2))) := by
          refine (measure_mono ?_).trans (measure_iUnion_le _)
          exact iUnion_mono fun k => iUnion_subset fun _ => subset_rfl
      _ = ∑' k : ℕ, ENNReal.ofReal (2 / n * (1 / (k : ℝ) ^ 2)) := by
          congr 1; ext k; rw [Real.volume_Ioo]; congr 1; field_simp; ring
      _ = ENNReal.ofReal (2 / n * (Real.pi ^ 2 / 6)) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum.summable,
            hsum.tsum_eq]
      _ = ENNReal.ofReal (Real.pi ^ 2 / (3 * n)) := by congr 1; field_simp; ring

/-- **Ex. `ex:GrasQ`, seconde partie.** `U_∞ := ⋂_{n > 0} U_n` est un ensemble gras de mesure
nulle contenant `ℚ`, et son complémentaire est un ensemble maigre de mesure pleine. -/
theorem ex_GrasQ (q : ℕ → ℚ) (hq : ∀ r : ℚ, ∃ k, 0 < k ∧ q k = r) :
    (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n) ∈ residual ℝ ∧
      volume (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n) = 0 ∧
      range ((↑) : ℚ → ℝ) ⊆ ⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n ∧
      IsMeagre (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n)ᶜ ∧
      (∀ᵐ x ∂volume, x ∈ (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n)ᶜ) := by
  have hres : (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n) ∈ residual ℝ := by
    refine (countable_iInter_mem.2 fun n => countable_iInter_mem.2 fun hn => ?_)
    obtain ⟨ho, hd, -⟩ := ex_GrasQ_U q hq n hn
    exact residual_of_dense_open ho hd
  have hvol : volume (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n) = 0 := by
    have hle : ∀ n : ℕ, volume (⋂ n, ⋂ (_ : 0 < n), exGrasQ_U q n) ≤
        ENNReal.ofReal (Real.pi ^ 2 / 3 * (1 / ((n : ℝ) + 1))) := fun n => by
      refine (measure_mono (iInter₂_subset (n + 1) n.succ_pos)).trans ?_
      refine ((ex_GrasQ_U q hq (n + 1) n.succ_pos).2.2).trans (le_of_eq ?_)
      congr 1; push_cast; field_simp
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.pi ^ 2 / 3 * (1 / ((n : ℝ) + 1))))
        atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.pi ^ 2 / 3)
      rwa [mul_zero] at h
    exact le_antisymm (ge_of_tendsto' hlim hle) bot_le
  refine ⟨hres, hvol, ?_, by unfold IsMeagre; rwa [compl_compl], ?_⟩
  · rintro _ ⟨r, rfl⟩
    refine mem_iInter₂.2 fun n hn => ?_
    obtain ⟨k, hk, rfl⟩ := hq r
    have : (0 : ℝ) < 1 / (n * k ^ 2) := by positivity
    exact mem_iUnion₂.2 ⟨k, hk, by constructor <;> linarith⟩
  · exact compl_mem_ae_iff.2 hvol

/-- **Ex. `ex:grasNonDen`.** Soit `X` un espace métrique complet non vide et sans points isolés
(i.e. `𝓝[≠] x` est non trivial pour tout `x`), et `A ⊆ X` gras. Alors `A` est indénombrable. -/
theorem ex_grasNonDen [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (hX : ∀ x : X, (𝓝[≠] x).NeBot) (A : Set X) (hA : A ∈ residual X) : ¬ A.Countable := by
  intro hc
  have hres : A ∩ ⋂ x ∈ A, {x}ᶜ ∈ residual X := by
    refine inter_mem hA ((countable_bInter_mem hc).2 fun x _ => ?_)
    exact residual_of_dense_open isOpen_compl_singleton (dense_compl_singleton x)
  obtain ⟨y, hyA, hy⟩ := (dense_of_mem_residual hres).nonempty
  exact (mem_iInter₂.1 hy y hyA) rfl

end M1Analyse
