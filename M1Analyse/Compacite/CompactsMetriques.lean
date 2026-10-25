/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Topology.EMetricSpace.Basic

/-!
# §3.2 Compacts métriques (`subsec:compactMetric`)

Source : `Include/Compacite.tex`, sous-section `subsec:compactMetric`.

Les objets du cours sont ceux de Mathlib : un espace métrique `(X, d)` est `MetricSpace X`
(toujours séparé, donc « compact » au sens du cours = `CompactSpace X`), la précompacité est
`TotallyBounded` (pour l'espace entier : `TotallyBounded (univ : Set X)`), une valeur
d'adhérence de la suite `x` est un point `a` tel que `MapClusterPt a atTop x`
(cf. `eqdef:adherence_suite`), l'uniforme continuité est `UniformContinuous` et
l'(uniforme) équicontinuité est `Equicontinuous` (`UniformEquicontinuous`).
-/

open Set Filter Topology Metric

namespace M1Analyse

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **Déf. `def:precompact` (Précompacité).** Un espace métrique `X` est précompact
(`TotallyBounded univ`) ssi pour tout `ε > 0` il admet une couverture finie par des boules
ouvertes de rayon `ε`. -/
theorem def_precompact :
    TotallyBounded (univ : Set X) ↔
      ∀ ε > 0, ∃ t : Set X, t.Finite ∧ (⋃ x ∈ t, ball x ε) = univ := by
  rw [Metric.totallyBounded_iff]
  simp only [univ_subset_iff]

/-- **Rem. `rem:precompact_separable`, premier point.** Tout espace précompact est
séparable. -/
theorem rem_precompact_separable (h : TotallyBounded (univ : Set X)) :
    TopologicalSpace.SeparableSpace X :=
  TopologicalSpace.isSeparable_univ_iff.1 h.isSeparable

/-- **Rem. `rem:precompact_separable`, second point.** Un espace est précompact ssi pour tout
`ε > 0` il peut être couvert par un nombre fini de parties, chacune de diamètre au plus `ε`. -/
theorem rem_precompact_separable_diam :
    TotallyBounded (univ : Set X) ↔
      ∀ ε > 0, ∃ 𝒜 : Set (Set X), 𝒜.Finite ∧ ⋃₀ 𝒜 = univ ∧
        ∀ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ ε := by
  rw [def_precompact]
  constructor
  · intro h ε hε
    obtain ⟨t, ht, hcov⟩ := h (ε / 2) (by positivity)
    refine ⟨(fun y => ball y (ε / 2)) '' t, ht.image _, by rwa [sUnion_image], ?_⟩
    rintro _ ⟨y, -, rfl⟩ x hx z hz
    rw [mem_ball] at hx hz
    linarith [dist_triangle_right x z y]
  · intro h ε hε
    obtain ⟨𝒜, h𝒜, hcov, hdiam⟩ := h (ε / 2) (by positivity)
    have : Finite {A // A ∈ 𝒜 ∧ A.Nonempty} :=
      (h𝒜.subset fun _ hA => hA.1).to_subtype
    refine ⟨range fun A : {A // A ∈ 𝒜 ∧ A.Nonempty} => A.2.2.some, finite_range _, ?_⟩
    refine eq_univ_of_univ_subset fun x _ => ?_
    obtain ⟨A, hA, hxA⟩ : x ∈ ⋃₀ 𝒜 := hcov ▸ mem_univ x
    refine mem_iUnion₂.2 ⟨_, ⟨⟨A, hA, x, hxA⟩, rfl⟩, ?_⟩
    rw [mem_ball]
    have := hdiam A hA x hxA _ (Set.Nonempty.some_mem (⟨x, hxA⟩ : A.Nonempty))
    linarith

/-- **Rem. `rem:precompact_separable`, conséquence.** Une partie `s` d'un espace métrique
englobant `𝕏` est précompacte (pour la distance induite) ssi pour tout `ε > 0` elle est
couverte par un nombre fini de boules de rayon `ε` centrées en des points de `𝕏` (pas
nécessairement de `s`). -/
theorem rem_precompact_separable_englobant (s : Set X) :
    TotallyBounded (univ : Set s) ↔
      ∀ ε > 0, ∃ t : Set X, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x ε := by
  rw [← Metric.totallyBounded_iff, ← totallyBounded_image_iff
    isUniformEmbedding_subtype_val.isUniformInducing, image_univ, Subtype.range_coe]

/-- **Th. `th:BolzanoWeierstrass` (Compacité via Bolzano-Weierstrass).** Pour un espace
métrique `X`, sont équivalents : (i) `X` est compact ; (ii) toute suite à valeurs dans `X`
admet une valeur d'adhérence ; (iii) `X` est précompact et complet.
Preuve (différente du cours) : (i) ⇔ (iii) par `isCompact_iff_totallyBounded_isComplete` de
Mathlib, (ii) ⇒ (i) par la compacité séquentielle (`isCompact_iff_isSeqCompact`), sans le
nombre de Lebesgue ni l'extraction par boules emboîtées du cours. -/
theorem th_BolzanoWeierstrass :
    List.TFAE [CompactSpace X,
      ∀ x : ℕ → X, ∃ a, MapClusterPt a atTop x,
      TotallyBounded (univ : Set X) ∧ CompleteSpace X] := by
  tfae_have 1 ↔ 3 := by
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
      completeSpace_iff_isComplete_univ]
  tfae_have 1 → 2 := fun _ x => by
    obtain ⟨a, -, ha⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := x) (by simp)
    exact ⟨a, ha⟩
  tfae_have 2 → 1 := fun h => by
    rw [← isCompact_univ_iff, isCompact_iff_isSeqCompact]
    intro x _
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, mem_univ a, ha.tendsto_subseq⟩
  tfae_finish

/-- **Th. `th:BolzanoWeierstrass`, suite (Sous-suite convergente).** Un espace métrique est
compact ssi toute suite à valeurs dans `X` admet une sous-suite convergente. -/
theorem th_BolzanoWeierstrass_sousSuite :
    CompactSpace X ↔
      ∀ x : ℕ → X, ∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  refine ((th_BolzanoWeierstrass (X := X)).out 1 2).trans ?_
  exact forall_congr' fun x => exists_congr fun a =>
    ⟨fun h => h.tendsto_subseq,
      fun ⟨_, hφ, h⟩ => MapClusterPt.of_comp hφ.tendsto_atTop h.mapClusterPt⟩

/-- **Th. `th:Heine` (Heine).** Soit `X` métrique compact et `Y` métrique. Toute fonction
continue `f : X → Y` est uniformément continue.
Preuve (différente du cours) : lemme de Mathlib (par les entourages uniformes), au lieu de
l'argument par suites et sous-suite convergente du cours. -/
theorem th_Heine [CompactSpace X] {f : X → Y} (hf : Continuous f) : UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf

/-- **Th. `th:Heine`, suite (Familles équicontinues).** Sous les hypothèses du théorème de
Heine, toute famille équicontinue `(f_i : X → Y)_{i ∈ I}` est uniformément équicontinue. -/
theorem th_Heine_equicontinue [CompactSpace X] {ι : Type*} {f : ι → X → Y}
    (hf : Equicontinuous f) : UniformEquicontinuous f :=
  CompactSpace.uniformEquicontinuous_of_equicontinuous hf

/-- **Prop. `prop:noAdhCv`.** Soit `(x_n)` une suite à valeurs dans un espace métrique compact
`X`, n'admettant pas d'autre valeur d'adhérence que (peut-être) `x_*`. Alors `x_n → x_*`. -/
theorem prop_noAdhCv [CompactSpace X] (x : ℕ → X) (xLim : X)
    (h : ∀ a, MapClusterPt a atTop x → a = xLim) : Tendsto x atTop (𝓝 xLim) :=
  tendsto_nhds_of_unique_mapClusterPt h

end M1Analyse
