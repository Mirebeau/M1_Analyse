/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic

/-!
# §1.1.2 Comparaison de topologies (`subsubsec:compTopo`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section `subsubsec:compTopo`.

Les topologies sur `X` sont les objets Mathlib `TopologicalSpace X`. Attention : l'ordre de
Mathlib sur `TopologicalSpace X` est *inverse* de l'inclusion des ouverts : `t₁ ≤ t₂` signifie
que `t₁` est **plus fine** que `t₂` (elle a plus d'ouverts). Ainsi `⊥` est la topologie fine
(discrète) et `⊤` la topologie grossière ; l'intersection d'une famille de topologies est
`sSup`. La topologie engendrée est `generateFrom`, et une base d'ouverts est
`IsTopologicalBasis`.
-/

open Set TopologicalSpace Topology Filter

namespace M1Analyse

universe u

variable {X : Type u}

/-! ### Finesse d'une topologie -/

/-- **Déf. `def:finesseTopo` (Finesse d'une topologie).** La topologie `t₁` est plus fine que
`t₂` (elle possède plus d'ouverts : `𝕌₁ ⊃ 𝕌₂`) si et seulement si `t₁ ≤ t₂` dans l'ordre de
Mathlib (qui est donc inversé par rapport à l'inclusion des ouverts). -/
theorem def_finesseTopo (t₁ t₂ : TopologicalSpace X) :
    t₁ ≤ t₂ ↔ {U : Set X | IsOpen[t₂] U} ⊆ {U | IsOpen[t₁] U} :=
  TopologicalSpace.le_def

/-- **Déf. `def:finesseTopo`, topologie fine.** La topologie fine `𝕌 = 𝒫(X)` est la topologie
discrète `⊥` de Mathlib (la plus fine de toutes) : toute partie est ouverte. -/
theorem def_finesseTopo_fine : {U : Set X | IsOpen[⊥] U} = univ :=
  eq_univ_of_forall fun U => by
    let _ : TopologicalSpace X := ⊥
    have : DiscreteTopology X := ⟨rfl⟩
    exact isOpen_discrete U

/-- **Déf. `def:finesseTopo`, topologie grossière.** La topologie grossière `𝕌 = {∅, X}` est
la topologie `⊤` de Mathlib (la moins fine de toutes). -/
theorem def_finesseTopo_grossiere : {U : Set X | IsOpen[⊤] U} = {∅, univ} := by
  ext U
  simp [TopologicalSpace.isOpen_top_iff]

/-- **Déf. `def:finesseTopo`, intersection de topologies.** L'intersection d'une famille
quelconque `T` de topologies est une topologie : c'est `sSup T` dans l'ordre de Mathlib
(remarque non numérotée suivant `def:finesseTopo`). Pour `T = ∅`, on obtient `𝒫(X)`. -/
theorem def_finesseTopo_inter (T : Set (TopologicalSpace X)) :
    {U : Set X | IsOpen[sSup T] U} = ⋂ t ∈ T, {U | IsOpen[t] U} := by
  ext U
  simp [isOpen_sSup_iff]

/-! ### Topologie engendrée -/

/-- **Déf. `def:topoEngendree` (Topologie engendrée).** La topologie `generateFrom 𝕌₀` de
Mathlib est la plus petite topologie sur `X` contenant `𝕌₀` : ses ouverts forment le plus petit
élément (pour l'inclusion) de l'ensemble des topologies `𝕌` (vues comme parties de `𝒫(X)`)
telles que `𝕌₀ ⊆ 𝕌`. -/
theorem def_topoEngendree (𝕌₀ : Set (Set X)) :
    IsLeast {𝕌 : Set (Set X) | (∃ t : TopologicalSpace X, 𝕌 = {U | IsOpen[t] U}) ∧ 𝕌₀ ⊆ 𝕌}
      {U | IsOpen[generateFrom 𝕌₀] U} := by
  refine ⟨⟨⟨_, rfl⟩, fun U hU => isOpen_generateFrom_of_mem hU⟩, ?_⟩
  rintro _ ⟨⟨t, rfl⟩, h⟩
  exact (TopologicalSpace.le_def.mp (le_generateFrom_iff_subset_isOpen.mpr h))

/-- **Déf. `def:topoEngendree`, description explicite.** Les éléments de la topologie engendrée
par `𝕌₀` sont `X` lui-même, ainsi que les unions quelconques d'intersections finies d'éléments
de `𝕌₀` : `U = ⋃_{i ∈ I} ⋂_{1 ≤ j ≤ J(i)} U_{ij}`, avec `J : I → ℕ*` et `U_{ij} ∈ 𝕌₀`
(remarque non numérotée suivant `def:topoEngendree` ; les indices `j` parcourent `Fin (J i)`).
Preuve (absente du cours) : via la base de Mathlib `isTopologicalBasis_of_subbasis`, formée
des intersections finies d'éléments de `𝕌₀` ; l'intersection vide donne le cas `U = X`. -/
theorem def_topoEngendree_description (𝕌₀ : Set (Set X)) (U : Set X) :
    IsOpen[generateFrom 𝕌₀] U ↔ U = univ ∨
      ∃ (I : Type u) (J : I → ℕ) (V : (i : I) → Fin (J i) → Set X),
        (∀ i, 0 < J i) ∧ (∀ i j, V i j ∈ 𝕌₀) ∧ U = ⋃ i, ⋂ j, V i j := by
  let t : TopologicalSpace X := generateFrom 𝕌₀
  constructor
  · intro hU
    obtain ⟨S, hS, rfl⟩ := (isTopologicalBasis_of_subbasis (t := t) rfl).open_iff_eq_sUnion.mp hU
    by_cases hS' : univ ∈ S
    · exact Or.inl (eq_univ_of_univ_subset (subset_sUnion_of_mem hS'))
    right
    have key : ∀ s : S, ∃ (n : ℕ) (v : Fin n → Set X),
        0 < n ∧ (∀ j, v j ∈ 𝕌₀) ∧ (s : Set X) = ⋂ j, v j := by
      rintro ⟨s, hs⟩
      obtain ⟨f, ⟨hf, hf𝕌⟩, rfl⟩ := hS hs
      obtain ⟨n, v, -, hv⟩ := hf.fin_param
      refine ⟨n, v, ?_, fun j => hf𝕌 (hv ▸ mem_range_self j), by
        change ⋂₀ f = _
        rw [← hv, sInter_range]⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        apply hS'
        have : f = ∅ := by rw [← hv]; exact range_eq_empty _
        simpa [this] using hs
      · exact hn
    choose J V hJ hV hsV using key
    refine ⟨S, J, V, hJ, hV, ?_⟩
    rw [sUnion_eq_iUnion]
    exact iUnion_congr hsV
  · rintro (rfl | ⟨I, J, V, -, hV, rfl⟩)
    · exact isOpen_univ
    · exact isOpen_iUnion fun i => isOpen_iInter_of_finite fun j =>
        isOpen_generateFrom_of_mem (hV i j)

/-! ### Base d'ouverts -/

/-- **Prop. `prop:baseOuverts` (Base d'ouverts), définition.** Une base d'ouverts au sens de
Mathlib (`IsTopologicalBasis 𝕌₀` pour la topologie `t`) est exactement une partie
`𝕌₀ ⊆ 𝒫(X)` satisfaisant (i) la couverture de `X` et (ii) la stabilité par intersection en
tout point, et telle que `t` soit la topologie engendrée par `𝕌₀`. -/
theorem prop_baseOuverts_iff [t : TopologicalSpace X] (𝕌₀ : Set (Set X)) :
    IsTopologicalBasis 𝕌₀ ↔
      ⋃₀ 𝕌₀ = univ ∧
      (∀ U ∈ 𝕌₀, ∀ V ∈ 𝕌₀, ∀ x ∈ U ∩ V, ∃ W ∈ 𝕌₀, x ∈ W ∧ W ⊆ U ∩ V) ∧
      t = generateFrom 𝕌₀ :=
  ⟨fun h => ⟨h.sUnion_eq, h.exists_subset_inter, h.eq_generateFrom⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃⟩⟩

/-- **Prop. `prop:baseOuverts` (Base d'ouverts).** Si `𝕌₀ ⊆ 𝒫(X)` satisfait (i) la couverture
de `X` et (ii) la stabilité par intersection en tout point, alors la topologie engendrée par
`𝕌₀` consiste en les unions quelconques d'éléments de `𝕌₀` (éq. `eq:topo_engendree`).
Preuve (différente du cours) : lemme de Mathlib `IsTopologicalBasis.open_iff_eq_sUnion`, au
lieu de vérifier que les unions d'éléments de `𝕌₀` forment une topologie. -/
theorem prop_baseOuverts (𝕌₀ : Set (Set X)) (h₁ : ⋃₀ 𝕌₀ = univ)
    (h₂ : ∀ U ∈ 𝕌₀, ∀ V ∈ 𝕌₀, ∀ x ∈ U ∩ V, ∃ W ∈ 𝕌₀, x ∈ W ∧ W ⊆ U ∩ V) :
    {U : Set X | IsOpen[generateFrom 𝕌₀] U} = {U | ∃ 𝒰 ⊆ 𝕌₀, U = ⋃₀ 𝒰} := by
  let t : TopologicalSpace X := generateFrom 𝕌₀
  have hB : IsTopologicalBasis 𝕌₀ := ⟨h₂, h₁, rfl⟩
  ext U
  exact hB.open_iff_eq_sUnion

/-- **Cor. `corol:baseOuverts`.** Soit `(X, 𝕌)` un espace topologique et `𝕌₀ ⊆ 𝕌` tel que pour
tout ouvert `U` et tout `x ∈ U`, il existe `U_x ∈ 𝕌₀` avec `x ∈ U_x ⊆ U`. Alors `𝕌₀` est une
base d'ouverts pour la topologie `𝕌` : il vérifie (i), (ii), et engendre `𝕌`
(cf. `prop_baseOuverts_iff`).
Preuve (différente du cours) : critère de Mathlib `isTopologicalBasis_of_isOpen_of_nhds`,
au lieu de la vérification directe de (i), (ii) et de `U = ⋃_{x ∈ U} U_x`. -/
theorem corol_baseOuverts [t : TopologicalSpace X] (𝕌₀ : Set (Set X))
    (h𝕌₀ : ∀ U ∈ 𝕌₀, IsOpen U) (h : ∀ U, IsOpen U → ∀ x ∈ U, ∃ V ∈ 𝕌₀, x ∈ V ∧ V ⊆ U) :
    ⋃₀ 𝕌₀ = univ ∧
      (∀ U ∈ 𝕌₀, ∀ V ∈ 𝕌₀, ∀ x ∈ U ∩ V, ∃ W ∈ 𝕌₀, x ∈ W ∧ W ⊆ U ∩ V) ∧
      t = generateFrom 𝕌₀ :=
  (prop_baseOuverts_iff 𝕌₀).mp
    (isTopologicalBasis_of_isOpen_of_nhds h𝕌₀ fun x U hx hU => h U hU x hx)

/-! ### Exemples -/

/-- **Ex. `ex:topoOrdre` (Topologie de l'ordre).** Sur un ensemble totalement ordonné `X` ayant
au moins deux points, les intervalles `]-∞, b[`, `]a, b[`, `]a, ∞[` forment une base d'ouverts
(au sens de `prop:baseOuverts` : couverture et stabilité par intersection), et la topologie
qu'ils engendrent est la topologie de l'ordre de Mathlib (`OrderTopology`, engendrée par les
`]a, ∞[` et `]-∞, b[`). -/
theorem ex_topoOrdre [TopologicalSpace X] [LinearOrder X] [OrderTopology X] [Nontrivial X] :
    IsTopologicalBasis
      {s : Set X | (∃ b, s = Iio b) ∨ (∃ a b, s = Ioo a b) ∨ (∃ a, s = Ioi a)} := by
  set B : Set (Set X) := {s | (∃ b, s = Iio b) ∨ (∃ a b, s = Ioo a b) ∨ (∃ a, s = Ioi a)}
  refine (prop_baseOuverts_iff B).mpr ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := exists_pair_ne X
    wlog h : a < b generalizing a b
    · exact this b a hab.symm (lt_of_le_of_ne (not_lt.mp h) hab.symm)
    refine eq_univ_of_forall fun x => ?_
    rcases lt_or_ge x b with hx | hx
    · exact ⟨Iio b, Or.inl ⟨b, rfl⟩, hx⟩
    · exact ⟨Ioi a, Or.inr (Or.inr ⟨a, rfl⟩), lt_of_lt_of_le h hx⟩
  · -- l'intersection de deux intervalles ouverts est un intervalle ouvert
    have hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B := by
      rintro U (⟨b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩) V (⟨d, rfl⟩ | ⟨c, d, rfl⟩ | ⟨c, rfl⟩)
      · exact Or.inl ⟨min b d, Iio_inter_Iio⟩
      · exact Or.inr (Or.inl ⟨c, min b d, by
        ext; simp only [mem_inter_iff, mem_Iio, mem_Ioo, lt_min_iff]; tauto⟩)
      · exact Or.inr (Or.inl ⟨c, b, by
        ext; simp only [mem_inter_iff, mem_Iio, mem_Ioo, mem_Ioi]; tauto⟩)
      · exact Or.inr (Or.inl ⟨a, min b d, by
        ext; simp only [mem_inter_iff, mem_Iio, mem_Ioo, lt_min_iff]; tauto⟩)
      · exact Or.inr (Or.inl ⟨max a c, min b d, Ioo_inter_Ioo⟩)
      · exact Or.inr (Or.inl ⟨max a c, b, by
        ext; simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]; tauto⟩)
      · exact Or.inr (Or.inl ⟨a, d, Ioi_inter_Iio⟩)
      · exact Or.inr (Or.inl ⟨max a c, d, by
        ext; simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]; tauto⟩)
      · exact Or.inr (Or.inr ⟨max a c, Ioi_inter_Ioi⟩)
    exact fun U hU V hV x hx => ⟨U ∩ V, hinter U hU V hV, hx, subset_rfl⟩
  · rw [OrderTopology.topology_eq_generate_intervals (α := X)]
    apply le_antisymm
    · refine le_generateFrom ?_
      rintro _ (⟨b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, rfl⟩)
      · exact GenerateOpen.basic _ ⟨b, Or.inr rfl⟩
      · rw [← Ioi_inter_Iio]
        exact GenerateOpen.inter _ _ (GenerateOpen.basic _ ⟨a, Or.inl rfl⟩)
          (GenerateOpen.basic _ ⟨b, Or.inr rfl⟩)
      · exact GenerateOpen.basic _ ⟨a, Or.inl rfl⟩
    · refine le_generateFrom ?_
      rintro _ ⟨a, rfl | rfl⟩
      · exact GenerateOpen.basic _ (Or.inr (Or.inr ⟨a, rfl⟩))
      · exact GenerateOpen.basic _ (Or.inl ⟨a, rfl⟩)

/-- **Ex. `ex:topoProduit` (Topologie produit).** La topologie produit de Mathlib sur
`Π i, X i` admet pour base d'ouverts les produits `Π i, U i` d'ouverts `U i` de `X i`, avec
`U i = X i` sauf pour un nombre fini d'indices.
Preuve (différente du cours) : la topologie produit étant celle de Mathlib, on montre que ces
pavés sont ouverts et contiennent un pavé de `isTopologicalBasis_pi` dans tout voisinage
(`isTopologicalBasis_of_isOpen_of_nhds`), au lieu de vérifier les axiomes (i)–(ii). -/
theorem ex_topoProduit {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] :
    IsTopologicalBasis {S : Set (Π i, X i) | ∃ U : Π i, Set (X i),
      (∀ i, IsOpen (U i)) ∧ {i | U i ≠ univ}.Finite ∧ S = univ.pi U} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨U, hU, hF, rfl⟩
    have : univ.pi U = {i | U i ≠ univ}.pi U := by
      ext x
      simp only [Set.mem_pi, mem_univ, forall_const]
      refine ⟨fun h i _ => h i, fun h i => ?_⟩
      by_cases hi : U i = univ
      · exact hi ▸ mem_univ _
      · exact h i hi
    rw [this]
    exact isOpen_set_pi hF fun i _ => hU i
  · intro x O hx hO
    obtain ⟨_, ⟨U, F, hU, rfl⟩, hxS, hSO⟩ :=
      (isTopologicalBasis_pi fun i => isTopologicalBasis_opens (α := X i)).exists_subset_of_mem_open
        hx hO
    classical
    let V : Π i, Set (X i) := fun i => if i ∈ F then U i else univ
    refine ⟨univ.pi V, ⟨V, fun i => ?_, ?_, rfl⟩, fun i _ => ?_, ?_⟩
    · by_cases hi : i ∈ F
      · simpa [V, hi] using hU i hi
      · simp [V, hi]
    · refine F.finite_toSet.subset fun i hi => ?_
      by_contra hiF
      have hiF' : i ∉ F := hiF
      exact hi (by simp [V, hiF'])
    · by_cases hi : i ∈ F
      · simpa [V, hi] using hxS i hi
      · simp [V, hi]
    · refine Subset.trans ?_ hSO
      intro y hy i hi
      have hi' : i ∈ F := hi
      simpa [V, hi'] using hy i (mem_univ i)

/-- **Ex. `ex:topoProduit`, convergence simple.** Lorsque `X i = X` pour tout `i`, le produit
s'identifie à `X^I = I → X`, et la topologie produit correspond à la convergence simple :
`f_n → g` si et seulement si `f_n(i) → g(i)` pour tout `i ∈ I` (remarque non numérotée suivant
`ex:topoProduit`). -/
theorem ex_topoProduit_convergenceSimple {I : Type*} [TopologicalSpace X]
    (f : ℕ → I → X) (g : I → X) :
    Tendsto f atTop (𝓝 g) ↔ ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i)) :=
  tendsto_pi_nhds

end M1Analyse
