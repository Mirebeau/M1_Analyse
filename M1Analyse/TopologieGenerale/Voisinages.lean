/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Sequences

/-!
# §1.1.3 Voisinages (`subsubsec:Vois`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section `subsubsec:Vois`.

Le filtre des voisinages `𝒱_x` du cours est le filtre Mathlib `𝓝 x` ; une base de voisinages
est exprimée par `Filter.HasBasis` ; « à base de voisinages dénombrable » et « à base
dénombrable » sont `FirstCountableTopology` et `SecondCountableTopology` ; la convergence d'une
suite est `Filter.Tendsto x atTop (𝓝 a)` ; une valeur d'adhérence d'une suite est un
`MapClusterPt a atTop x`. Chaque énoncé ci-dessous, nommé d'après le label LaTeX correspondant,
relie l'objet Mathlib à la définition du cours ou établit le résultat annoncé.
-/

open Set Filter TopologicalSpace Topology

namespace M1Analyse

variable {X : Type*}

/-- **Déf. `def:filtre_vois` (Filtre des voisinages).** Un voisinage de `x` est une partie `V`
contenant un ouvert contenant `x`. Mathlib : `V ∈ 𝓝 x`. -/
theorem def_filtre_vois [TopologicalSpace X] (x : X) (V : Set X) :
    V ∈ 𝓝 x ↔ ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V := by
  rw [mem_nhds_iff]
  exact ⟨fun ⟨U, hUV, hU, hx⟩ => ⟨U, hU, hx, hUV⟩, fun ⟨U, hU, hx, hUV⟩ => ⟨U, hUV, hU, hx⟩⟩

/-- **Éq. `eqdef:Vx`.** `𝒱_x = {V ⊆ X | x ∈ V̊}` : l'ensemble des voisinages de `x` (les
éléments du filtre Mathlib `𝓝 x`) est l'ensemble des parties dont `x` est un point intérieur. -/
theorem eqdef_Vx [TopologicalSpace X] (x : X) :
    {V : Set X | V ∈ 𝓝 x} = {V | x ∈ interior V} := by
  ext V
  exact mem_interior_iff_mem_nhds.symm

/-- **Prop. `prop:adh_vois` (Caractérisation de l'adhérence).**
`Ā = {x | ∀ V ∈ 𝒱_x, A ∩ V ≠ ∅}` et `Å = {x | ∃ V ∈ 𝒱_x, V ⊆ A}`. -/
theorem prop_adh_vois [TopologicalSpace X] (A : Set X) :
    closure A = {x | ∀ V ∈ 𝓝 x, (A ∩ V).Nonempty} ∧
    interior A = {x | ∃ V ∈ 𝓝 x, V ⊆ A} := by
  constructor
  · ext x
    simp only [mem_ofPred_eq, mem_closure_iff_nhds, inter_comm A]
  · ext x
    simp only [mem_ofPred_eq, mem_interior_iff_mem_nhds]
    exact ⟨fun h => ⟨A, h, subset_rfl⟩, fun ⟨V, hV, hVA⟩ => mem_of_superset hV hVA⟩

/-- **Déf. `def:base_vois` (Base de voisinages).** Une partie `𝒲 ⊆ 𝒱_x` est une base de
voisinages de `x` si `∀ V ∈ 𝒱_x, ∃ W ∈ 𝒲, W ⊆ V`. Mathlib : `(𝓝 x).HasBasis (· ∈ 𝒲) id`. -/
theorem def_base_vois [TopologicalSpace X] (x : X) (𝒲 : Set (Set X)) :
    (𝓝 x).HasBasis (· ∈ 𝒲) id ↔ (∀ W ∈ 𝒲, W ∈ 𝓝 x) ∧ ∀ V ∈ 𝓝 x, ∃ W ∈ 𝒲, W ⊆ V := by
  constructor
  · intro h
    exact ⟨fun W hW => h.mem_of_mem hW, fun V hV => h.mem_iff.mp hV⟩
  · rintro ⟨h𝒲, hV⟩
    refine ⟨fun V => ⟨hV V, fun ⟨W, hW, hWV⟩ => mem_of_superset (h𝒲 W hW) hWV⟩⟩

/-- **Rem. `rem:topoVois` (Topologie définie par des bases de voisinages), premier point.**
Soit, pour tout `x ∈ X`, un ensemble non vide `𝒲 x` de parties de `X` contenant chacune `x`,
tel que `∀ U V ∈ 𝒲 x, ∃ W ∈ 𝒲 x, W ⊆ U ∩ V`. Alors
`𝕌 := {U ⊆ X | ∀ x ∈ U, ∃ V ∈ 𝒲 x, V ⊆ U}` est (l'ensemble des ouverts d')une unique
topologie sur `X`.
Remarque : l'hypothèse `x ∈ W` pour `W ∈ 𝒲 x` n'est pas utilisée pour ce premier point. -/
theorem rem_topoVois_topologie (𝒲 : X → Set (Set X)) (hne : ∀ x, (𝒲 x).Nonempty)
    (_hmem : ∀ x, ∀ W ∈ 𝒲 x, x ∈ W)
    (hdir : ∀ x, ∀ U ∈ 𝒲 x, ∀ V ∈ 𝒲 x, ∃ W ∈ 𝒲 x, W ⊆ U ∩ V) :
    ∃! t : TopologicalSpace X,
      {U | IsOpen[t] U} = {U | ∀ x ∈ U, ∃ V ∈ 𝒲 x, V ⊆ U} := by
  refine ⟨{ IsOpen := fun U => ∀ x ∈ U, ∃ V ∈ 𝒲 x, V ⊆ U
            isOpen_univ := fun x _ => (hne x).imp fun V hV => ⟨hV, subset_univ V⟩
            isOpen_inter := ?_
            isOpen_sUnion := ?_ }, rfl, ?_⟩
  · intro U V hU hV x ⟨hxU, hxV⟩
    obtain ⟨A, hA, hAU⟩ := hU x hxU
    obtain ⟨B, hB, hBV⟩ := hV x hxV
    obtain ⟨W, hW, hWAB⟩ := hdir x A hA B hB
    exact ⟨W, hW, hWAB.trans (inter_subset_inter hAU hBV)⟩
  · intro 𝒰 h𝒰 x ⟨U, hU𝒰, hxU⟩
    obtain ⟨V, hV, hVU⟩ := h𝒰 U hU𝒰 x hxU
    exact ⟨V, hV, hVU.trans (subset_sUnion_of_mem hU𝒰)⟩
  · intro t ht
    apply TopologicalSpace.ext
    funext U
    exact propext (Set.ext_iff.mp ht U)

/-- **Rem. `rem:topoVois` (Topologie définie par des bases de voisinages), second point.**
Sous les hypothèses du premier point, si de plus
`∀ x, ∀ U ∈ 𝒲 x, ∀ y ∈ U, ∃ V ∈ 𝒲 y, V ⊆ U`, alors pour la topologie `𝕌` ainsi définie,
`𝒲 x` est une base de voisinages de `x` pour tout `x`, et `⋃ₓ 𝒲 x` est une base d'ouverts. -/
theorem rem_topoVois_base (𝒲 : X → Set (Set X)) (hne : ∀ x, (𝒲 x).Nonempty)
    (hmem : ∀ x, ∀ W ∈ 𝒲 x, x ∈ W)
    (hdir : ∀ x, ∀ U ∈ 𝒲 x, ∀ V ∈ 𝒲 x, ∃ W ∈ 𝒲 x, W ⊆ U ∩ V)
    (hcomp : ∀ x, ∀ U ∈ 𝒲 x, ∀ y ∈ U, ∃ V ∈ 𝒲 y, V ⊆ U) :
    ∃ t : TopologicalSpace X,
      {U | IsOpen[t] U} = {U | ∀ x ∈ U, ∃ V ∈ 𝒲 x, V ⊆ U} ∧
      (∀ x, (@nhds X t x).HasBasis (· ∈ 𝒲 x) id) ∧
      @IsTopologicalBasis X t (⋃ x, 𝒲 x) := by
  obtain ⟨t, ht, -⟩ := rem_topoVois_topologie 𝒲 hne hmem hdir
  have hopen : ∀ U, IsOpen[t] U ↔ ∀ x ∈ U, ∃ V ∈ 𝒲 x, V ⊆ U := fun U => Set.ext_iff.mp ht U
  have hW : ∀ x, ∀ W ∈ 𝒲 x, IsOpen[t] W := fun x W hW => (hopen W).mpr (hcomp x W hW)
  let _ := t
  refine ⟨t, ht, fun x => ?_, ?_⟩
  · refine ⟨fun V => ⟨fun hV => ?_, fun ⟨W, hW', hWV⟩ => ?_⟩⟩
    · obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
      obtain ⟨W, hW', hWU⟩ := (hopen U).mp hU x hxU
      exact ⟨W, hW', hWU.trans hUV⟩
    · exact mem_nhds_iff.mpr ⟨W, hWV, hW x W hW', hmem x W hW'⟩
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · intro W hWU
      obtain ⟨x, hx⟩ := mem_iUnion.mp hWU
      exact hW x W hx
    · intro a U haU hU
      obtain ⟨W, hW', hWU⟩ := (hopen U).mp hU a haU
      exact ⟨W, mem_iUnion.mpr ⟨a, hW'⟩, hmem a W hW', hWU⟩

/-- **Déf. `def:denVois` (Topologie à base de voisinages dénombrable, first countable).**
Tout point admet une base de voisinages dénombrable. Mathlib : `FirstCountableTopology X`. -/
theorem def_denVois_first [TopologicalSpace X] :
    FirstCountableTopology X ↔
      ∀ x : X, ∃ 𝒲 : Set (Set X), 𝒲.Countable ∧ (𝓝 x).HasBasis (· ∈ 𝒲) id := by
  constructor
  · intro _ x
    obtain ⟨u, hu⟩ := isCountablyGenerated_iff_exists_antitone_basis.mp
      (FirstCountableTopology.nhds_generated_countable x)
    refine ⟨range u, countable_range u, ?_⟩
    refine hu.toHasBasis.to_hasBasis (fun n _ => ⟨u n, mem_range_self n, subset_rfl⟩) ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨n, trivial, subset_rfl⟩
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨𝒲, hc, hb⟩ := h x
    exact (HasCountableBasis.mk hb hc).isCountablyGenerated

/-- **Déf. `def:denVois` (Topologie à base dénombrable, second countable).**
La topologie admet une base dénombrable d'ouverts. Mathlib : `SecondCountableTopology X`. -/
theorem def_denVois_second [TopologicalSpace X] :
    SecondCountableTopology X ↔ ∃ ℬ : Set (Set X), ℬ.Countable ∧ IsTopologicalBasis ℬ := by
  constructor
  · intro _
    obtain ⟨ℬ, hc, -, hb⟩ := exists_countable_basis X
    exact ⟨ℬ, hc, hb⟩
  · rintro ⟨ℬ, hc, hb⟩
    exact hb.secondCountableTopology hc

/-- **Déf. `def:cvSuite` (Convergence d'une suite).** `x_n → a` ssi tout voisinage de `a`
contient tous les termes de la suite à partir d'un certain rang.
Mathlib : `Tendsto x atTop (𝓝 a)`. -/
theorem def_cvSuite [TopologicalSpace X] (x : ℕ → X) (a : X) :
    Tendsto x atTop (𝓝 a) ↔ ∀ V ∈ 𝓝 a, ∃ N : ℕ, ∀ n ≥ N, x n ∈ V :=
  tendsto_atTop'

/-- **Prop. `prop:adhSuite` (Caractérisation séquentielle de l'adhérence).** Dans un espace à
base de voisinages dénombrable, `Ā` est l'ensemble des limites de suites convergentes
d'éléments de `A`. -/
theorem prop_adhSuite [TopologicalSpace X] [FirstCountableTopology X] (A : Set X) :
    closure A = {a | ∃ x : ℕ → X, (∀ n, x n ∈ A) ∧ Tendsto x atTop (𝓝 a)} := by
  ext a
  exact mem_closure_iff_seq_limit

/-- **Prop. `prop:adhSuite`, inclusion `⊇`.** La limite d'une suite convergente d'éléments de
`A` appartient à `Ā`, sans hypothèse de dénombrabilité (comme noté dans la preuve du cours). -/
theorem prop_adhSuite_supset [TopologicalSpace X] (A : Set X) :
    {a | ∃ x : ℕ → X, (∀ n, x n ∈ A) ∧ Tendsto x atTop (𝓝 a)} ⊆ closure A := by
  rintro a ⟨x, hxA, hx⟩
  exact mem_closure_of_tendsto hx (Eventually.of_forall hxA)

/-- **Éq. `eqdef:adherence_suite` (Valeurs d'adhérence d'une suite).**
`Adh((x_n)_n) := ⋂_{N ≥ 0} closure {x_n | n ≥ N}`. Cet ensemble coïncide avec l'ensemble des
`a` tels que `MapClusterPt a atTop x` (valeurs d'adhérence au sens de Mathlib). -/
theorem eqdef_adherence_suite [TopologicalSpace X] (x : ℕ → X) :
    ⋂ N : ℕ, closure (x '' Ici N) = {a | MapClusterPt a atTop x} := by
  ext a
  simp only [mem_iInter, mem_ofPred_eq, mapClusterPt_atTop_iff_forall_mem_closure]

/-- **Prop. `prop:adhSousSuite` (Convergence d'une sous-suite vers toute valeur d'adhérence).**
Dans un espace à base de voisinages dénombrable, `Adh((x_n)_n)` (cf. `eqdef:adherence_suite`)
est l'ensemble des limites de suites extraites `x ∘ φ`, `φ` strictement croissante. -/
theorem prop_adhSousSuite [TopologicalSpace X] [FirstCountableTopology X] (x : ℕ → X) :
    ⋂ N : ℕ, closure (x '' Ici N) =
      {a | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)} := by
  rw [eqdef_adherence_suite]
  ext a
  exact ⟨fun h => h.tendsto_subseq,
    fun ⟨φ, hφ, h⟩ => MapClusterPt.of_comp hφ.tendsto_atTop h.mapClusterPt⟩

/-- **Prop. `prop:adhSousSuite`, inclusion `⊇`.** Toute limite d'une suite extraite est une
valeur d'adhérence, sans hypothèse de dénombrabilité (comme noté dans la preuve du cours). -/
theorem prop_adhSousSuite_supset [TopologicalSpace X] (x : ℕ → X) :
    {a | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)} ⊆
      ⋂ N : ℕ, closure (x '' Ici N) := by
  rw [eqdef_adherence_suite]
  rintro a ⟨φ, hφ, h⟩
  exact MapClusterPt.of_comp hφ.tendsto_atTop h.mapClusterPt

/-- **Rem. `rem:axiomFiltre` (Axiomes de filtre).** L'ensemble `𝒱_x` des voisinages de `x` est
un filtre de `(𝒫(X), ⊆)` : il est non vide, clos par sur-ensemble (upper closure), et
filtrant à gauche (downward directed). (C'est la structure `Filter X` de Mathlib.) -/
theorem rem_axiomFiltre [TopologicalSpace X] (x : X) :
    {V : Set X | V ∈ 𝓝 x}.Nonempty ∧
    (∀ V ∈ 𝓝 x, ∀ W : Set X, V ⊆ W → W ∈ 𝓝 x) ∧
    (∀ V₀ ∈ 𝓝 x, ∀ V₁ ∈ 𝓝 x, ∃ W ∈ 𝓝 x, W ⊆ V₀ ∧ W ⊆ V₁) :=
  ⟨⟨univ, univ_mem⟩, fun _ hV _ hVW => mem_of_superset hV hVW,
    fun V₀ h₀ V₁ h₁ => ⟨V₀ ∩ V₁, inter_mem h₀ h₁, inter_subset_left, inter_subset_right⟩⟩

end M1Analyse
