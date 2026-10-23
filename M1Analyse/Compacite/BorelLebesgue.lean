/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# §3.1 Axiome de Borel-Lebesgue (`subsec:axiomBorelLeb`)

Source : `Include/Compacite.tex`, sous-section `subsec:axiomBorelLeb` (l'introduction du
chapitre ne contient pas d'énoncé numéroté).

Les objets du cours sont ceux de Mathlib, avec une différence de convention : dans le cours,
un espace *compact* est par définition **séparé** et vérifie l'axiome de Borel-Lebesgue, tandis
que `CompactSpace X` (resp. `IsCompact K`) de Mathlib ne demande que l'axiome de
Borel-Lebesgue. Un compact au sens du cours est donc `[CompactSpace X] [T2Space X]` ; une partie
compacte au sens du cours d'un espace séparé est une partie `IsCompact K` (la séparation de `K`
étant héritée de celle de l'espace). Espace localement compact séparé :
`[LocallyCompactSpace X] [T2Space X]` ; compactifié d'Alexandrov : `OnePoint X`.
-/

open Set Filter Topology

namespace M1Analyse

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Déf. `def:compact` (Compact).** Un espace topologique est compact au sens du cours
(séparé et vérifiant l'axiome de Borel-Lebesgue : de toute couverture `𝒰` de `X` par des
ouverts on peut extraire une sous-couverture finie) ssi il est `CompactSpace` et `T2Space`
au sens de Mathlib.
Remarque : `CompactSpace` de Mathlib n'inclut pas la séparation. -/
theorem def_compact :
    (CompactSpace X ∧ T2Space X) ↔
      T2Space X ∧ ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = univ →
        ∃ 𝒰₀ ⊆ 𝒰, 𝒰₀.Finite ∧ ⋃₀ 𝒰₀ = univ := by
  rw [and_comm]
  refine and_congr_right fun _ => ?_
  rw [← isCompact_univ_iff, isCompact_iff_finite_subcover]
  constructor
  · intro h 𝒰 hU hcov
    obtain ⟨t, ht⟩ := h (fun U : 𝒰 => (U : Set X)) (fun U => hU U U.2)
      (by rw [← sUnion_eq_iUnion, hcov])
    refine ⟨(fun U : 𝒰 => (U : Set X)) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
    · rintro _ ⟨U, _, rfl⟩
      exact U.2
    · refine eq_univ_of_univ_subset (ht.trans ?_)
      rw [sUnion_image]
      exact fun x hx => by simpa using hx
  · classical
    intro h ι U hU hcov
    obtain ⟨𝒰₀, h𝒰₀, hfin, hcov₀⟩ := h (range U) (by rintro _ ⟨i, rfl⟩; exact hU i)
      (by rw [sUnion_range]; exact eq_univ_of_univ_subset hcov)
    choose f hf using fun V : 𝒰₀ => h𝒰₀ V.2
    have : Fintype 𝒰₀ := hfin.fintype
    refine ⟨Finset.univ.image f, ?_⟩
    intro x _
    have hx : x ∈ ⋃₀ 𝒰₀ := hcov₀ ▸ mem_univ x
    obtain ⟨V, hV, hxV⟩ := hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_iUnion, exists_prop]
    exact ⟨f ⟨V, hV⟩, ⟨⟨V, hV⟩, rfl⟩, by rw [hf ⟨V, hV⟩]; exact hxV⟩

/-- **Déf. `def:compact`, suite (Partie compacte).** Une partie `K` est compacte (au sens de
Mathlib) ssi `K`, muni de la topologie induite, est un espace compact. Dans un espace séparé,
`K` est alors aussi séparé, donc compact au sens du cours. -/
theorem def_compact_partie [T2Space X] (K : Set X) :
    IsCompact K ↔ CompactSpace K ∧ T2Space K :=
  ⟨fun h => ⟨isCompact_iff_compactSpace.1 h, inferInstance⟩,
    fun h => isCompact_iff_compactSpace.2 h.1⟩

/-- **Rem. `rem:fermeBorelLeb` (Borel-Lebesgue pour les fermés).** Si `X` est compact et si
`(F_i)_{i ∈ I}` est une famille de fermés d'intersection vide, alors une sous-famille finie est
d'intersection vide. (La séparation n'est pas utilisée.) -/
theorem rem_fermeBorelLeb [CompactSpace X] [T2Space X] {ι : Type*} (F : ι → Set X)
    (hF : ∀ i, IsClosed (F i)) (h : ⋂ i, F i = ∅) :
    ∃ J : Finset ι, ⋂ i ∈ J, F i = ∅ := by
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subfamily_closed F hF (by simp [h])
  exact ⟨J, by simpa using hJ⟩

/-- **Rem. `rem:fermeBorelLeb`, suite (Fermés emboîtés).** Dans un compact, une intersection
décroissante de fermés non vides est non vide. -/
theorem rem_fermeBorelLeb_emboites [CompactSpace X] [T2Space X] (F : ℕ → Set X)
    (hF : ∀ n, IsClosed (F n)) (hne : ∀ n, (F n).Nonempty) (hdec : Antitone F) :
    (⋂ n, F n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
    (fun n => hdec (Nat.le_succ n)) hne (hF 0).isCompact hF

/-- **Rem. `rem:fermeBorelLeb`, suite (Valeurs d'adhérence).** Dans un compact, toute suite
admet au moins une valeur d'adhérence (au sens de `eqdef:adherence_suite`, c.-à-d.
`MapClusterPt a atTop x`). -/
theorem rem_fermeBorelLeb_adherence [CompactSpace X] [T2Space X] (x : ℕ → X) :
    ∃ a, MapClusterPt a atTop x := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := x)
    (by simp)
  exact ⟨a, ha⟩

/-- **Lemme `lem:compImplFerme`.** Dans un espace séparé, toute partie compacte est fermée. -/
theorem lem_compImplFerme [T2Space X] {F : Set X} (hF : IsCompact F) : IsClosed F :=
  hF.isClosed

/-- **Cor. `corol:compSsiFerme`.** Dans un espace compact, une partie est compacte ssi elle est
fermée. -/
theorem corol_compSsiFerme [CompactSpace X] [T2Space X] (F : Set X) :
    IsCompact F ↔ IsClosed F :=
  ⟨IsCompact.isClosed, IsClosed.isCompact⟩

/-- **Prop. `prop:compactImage` (Image continue directe d'un compact).** Soient `X`, `Y`
séparés et `f : X → Y` continue. Pour tout compact `K ⊆ X`, l'image directe `f(K)` est
compacte. -/
theorem prop_compactImage [T2Space X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) : IsCompact (f '' K) :=
  hK.image hf

/-- **Cor. `corol:homeoCompact`.** Soient `X`, `Y` compacts et `f : X → Y` une bijection
continue, de réciproque `g`. Alors `g = f⁻¹` est continue. -/
theorem corol_homeoCompact [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {g : Y → X} (hgf : Function.LeftInverse g f)
    (hfg : Function.RightInverse g f) : Continuous g :=
  (hf.homeoOfEquivCompactToT2 (f := ⟨f, g, hgf, hfg⟩)).symm.continuous

/-- **Déf. `def:locCompact` (Espace localement compact séparé).** Dans un espace séparé, les
conditions (i) « tout point admet un voisinage compact » et (ii) « tout point admet une base de
voisinages compacts » sont équivalentes. -/
theorem def_locCompact [T2Space X] :
    (∀ x : X, ∃ K ∈ 𝓝 x, IsCompact K) ↔
      ∀ x : X, (𝓝 x).HasBasis (fun K => K ∈ 𝓝 x ∧ IsCompact K) id := by
  constructor
  · intro h
    have : WeaklyLocallyCompactSpace X :=
      ⟨fun x => let ⟨K, hK, hc⟩ := h x; ⟨K, hc, hK⟩⟩
    exact compact_basis_nhds
  · intro h x
    obtain ⟨K, ⟨hK, hc⟩, -⟩ := (h x).mem_iff.1 univ_mem
    exact ⟨K, hK, hc⟩

/-- **Déf. `def:locCompact`, lien avec Mathlib.** La condition (ii) est
`LocallyCompactSpace X` de Mathlib, et la condition (i) est `WeaklyLocallyCompactSpace X`. -/
theorem def_locCompact_mathlib :
    (LocallyCompactSpace X ↔ ∀ x : X, (𝓝 x).HasBasis (fun K => K ∈ 𝓝 x ∧ IsCompact K) id) ∧
    (WeaklyLocallyCompactSpace X ↔ ∀ x : X, ∃ K ∈ 𝓝 x, IsCompact K) := by
  refine ⟨⟨fun _ => compact_basis_nhds, fun h => LocallyCompactSpace.of_hasBasis h
    fun _ _ hK => hK.2⟩, ⟨fun _ x => ?_, fun h => ⟨fun x => ?_⟩⟩⟩
  · obtain ⟨K, hc, hK⟩ := exists_compact_mem_nhds x
    exact ⟨K, hK, hc⟩
  · obtain ⟨K, hK, hc⟩ := h x
    exact ⟨K, hc, hK⟩

/-- **Déf. `def:compactAlex` (Compactifié d'Alexandrov).** Pour `X` localement compact séparé,
le compactifié d'Alexandrov `X̃ = X ⊔ {ω}` est `OnePoint X` (avec `ω = ∞`), et ses ouverts sont
exactement les `U ∈ 𝕌` (vus dans `X̃`) et les `X̃ ∖ K` avec `K ⊆ X` compact :
`𝕌̃ = 𝕌 ∪ {X̃ ∖ K | K ⊆ X compact}`. (Seule la séparation de `X` est utile ici.) -/
theorem def_compactAlex [LocallyCompactSpace X] [T2Space X] (s : Set (OnePoint X)) :
    IsOpen s ↔ (∃ U : Set X, IsOpen U ∧ s = (↑) '' U) ∨
      (∃ K : Set X, IsCompact K ∧ s = ((↑) '' K)ᶜ) := by
  constructor
  · intro hs
    by_cases h : (OnePoint.infty : OnePoint X) ∈ s
    · refine Or.inr ⟨((↑) ⁻¹' s)ᶜ, (OnePoint.isOpen_iff_of_mem' h).1 hs |>.1, ?_⟩
      ext z
      induction z using OnePoint.rec with
      | infty => simp [h]
      | coe x => simp
    · refine Or.inl ⟨(↑) ⁻¹' s, (OnePoint.isOpen_iff_of_notMem h).1 hs, ?_⟩
      ext z
      induction z using OnePoint.rec with
      | infty => simp [h]
      | coe x => simp
  · rintro (⟨U, hU, rfl⟩ | ⟨K, hK, rfl⟩)
    · exact OnePoint.isOpen_image_coe.2 hU
    · exact OnePoint.isOpen_compl_image_coe.2 ⟨hK.isClosed, hK⟩

/-- **Déf. `def:compactAlex`, suite.** Le compactifié d'Alexandrov d'un espace localement
compact séparé est compact (au sens du cours : compact et séparé). -/
theorem def_compactAlex_compact [LocallyCompactSpace X] [T2Space X] :
    CompactSpace (OnePoint X) ∧ T2Space (OnePoint X) :=
  ⟨inferInstance, inferInstance⟩

end M1Analyse
