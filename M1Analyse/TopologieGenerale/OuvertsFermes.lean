/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Bases

/-!
# §1.1.1 Ouverts et fermés (`subsubsec:ouvertsFermes`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section `subsubsec:ouvertsFermes`.

Les objets du cours (topologie, fermés, intérieur, adhérence, densité, séparabilité) sont ceux
de Mathlib ; chaque énoncé ci-dessous, nommé d'après le label LaTeX correspondant, montre que
l'objet Mathlib coïncide avec la définition du cours, ou en établit les propriétés annoncées.
-/

open Set TopologicalSpace Topology

namespace M1Analyse

variable {X : Type*}

/-- **Déf. `def:topo` (Espace topologique), sens direct.**
Les ouverts d'une topologie Mathlib `TopologicalSpace X` satisfont les trois axiomes (i)–(iii)
du cours : `∅, X ∈ 𝕌` ; union quelconque ; intersection de deux ouverts.
Remarque : l'axiome `∅ ∈ 𝕌` est redondant, puisque `∅` est l'union vide (`rem:unionVide`) ;
pour cette raison il ne figure pas dans la définition de `TopologicalSpace` de Mathlib, et
`isOpen_empty` y est un théorème. -/
theorem def_topo_axioms [TopologicalSpace X] :
    (IsOpen (∅ : Set X) ∧ IsOpen (univ : Set X)) ∧
    (∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → IsOpen (⋃₀ 𝒰)) ∧
    (∀ U V : Set X, IsOpen U → IsOpen V → IsOpen (U ∩ V)) :=
  ⟨⟨isOpen_empty, isOpen_univ⟩, fun _ h => isOpen_sUnion h, fun _ _ => IsOpen.inter⟩

/-- **Déf. `def:topo` (Espace topologique), sens réciproque.**
Toute partie `𝕌 ⊆ 𝒫(X)` satisfaisant les axiomes (i)–(iii) est l'ensemble des ouverts
d'une (unique) topologie Mathlib sur `X`.
Remarque : l'hypothèse `∅ ∈ 𝕌` (dans `h₁`) est redondante, comme indiqué dans `rem:unionVide`
(`∅ = ⋃₀ ∅ ∈ 𝕌` par (ii)) ; elle est absente de la définition de `TopologicalSpace` de Mathlib,
et n'est pas utilisée dans la preuve. -/
theorem def_topo_of_axioms (𝕌 : Set (Set X))
    (h₁ : ∅ ∈ 𝕌 ∧ univ ∈ 𝕌)
    (h₂ : ∀ 𝒰 ⊆ 𝕌, ⋃₀ 𝒰 ∈ 𝕌)
    (h₃ : ∀ U ∈ 𝕌, ∀ V ∈ 𝕌, U ∩ V ∈ 𝕌) :
    ∃! t : TopologicalSpace X, {U | IsOpen[t] U} = 𝕌 := by
  refine ⟨{ IsOpen := (· ∈ 𝕌), isOpen_univ := h₁.2,
            isOpen_inter := fun U V hU hV => h₃ U hU V hV,
            isOpen_sUnion := fun 𝒰 h => h₂ 𝒰 h }, rfl, ?_⟩
  intro t ht
  apply TopologicalSpace.ext
  funext U
  exact propext (Set.ext_iff.mp ht U)

/-- **Déf. `def:topo`, topologie induite.** Les ouverts de la topologie induite sur `A`
(topologie Mathlib du sous-type `↥A`), vus comme parties de `X`, sont exactement
`𝕌_A = {U ∩ A | U ∈ 𝕌}`. -/
theorem def_topo_induite [TopologicalSpace X] (A : Set X) :
    {B : Set X | ∃ V : Set A, IsOpen V ∧ B = (↑) '' V} = {B | ∃ U, IsOpen U ∧ B = U ∩ A} := by
  ext B
  simp only [mem_ofPred_eq, isOpen_induced_iff]
  constructor
  · rintro ⟨V, ⟨U, hU, rfl⟩, rfl⟩
    exact ⟨U, hU, by rw [Subtype.image_preimage_coe, inter_comm]⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨_, ⟨U, hU, rfl⟩, by rw [Subtype.image_preimage_coe, inter_comm]⟩

/-- **Éq. `eq:finter_open`.** L'intersection d'un nombre fini d'ouverts est un ouvert.
Le cours suppose `I ≥ 1` ; cette hypothèse est superflue ici, car l'intersection vide de
parties de `X` vaut `X` (cf. `rem:unionVide`), qui est ouvert. -/
theorem eq_finter_open [TopologicalSpace X] (I : ℕ) (U : Fin I → Set X)
    (hU : ∀ i, IsOpen (U i)) : IsOpen (⋂ i, U i) :=
  isOpen_iInter_of_finite hU

/-- **Rem. `rem:unionVide`.** L'union vide est vide, et l'intersection vide de parties de `X`
est `X` tout entier. -/
theorem rem_unionVide :
    ⋃₀ (∅ : Set (Set X)) = ∅ ∧ ⋂₀ (∅ : Set (Set X)) = univ :=
  ⟨sUnion_empty, sInter_empty⟩

/-- **Rem. `rem:fermes` (Fermés).** Un fermé est le complémentaire d'un ouvert, et
(i) `∅` et `X` sont fermés, (ii) une intersection quelconque de fermés est fermée,
(iii) une union finie de fermés est fermée. -/
theorem rem_fermes [TopologicalSpace X] :
    (∀ F : Set X, IsClosed F ↔ ∃ U, IsOpen U ∧ F = Uᶜ) ∧
    (IsClosed (∅ : Set X) ∧ IsClosed (univ : Set X)) ∧
    (∀ 𝓕 : Set (Set X), (∀ F ∈ 𝓕, IsClosed F) → IsClosed (⋂₀ 𝓕)) ∧
    (∀ (I : ℕ) (F : Fin I → Set X), (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)) := by
  refine ⟨fun F => ⟨fun h => ⟨Fᶜ, h.isOpen_compl, (compl_compl F).symm⟩, ?_⟩,
    ⟨isClosed_empty, isClosed_univ⟩, fun _ h => isClosed_sInter h,
    fun _ _ h => isClosed_iUnion_of_finite h⟩
  rintro ⟨U, hU, rfl⟩
  exact hU.isClosed_compl

/-- **Déf. `def:interieur` (Intérieur).** L'intérieur `Å` est le plus grand ouvert contenu
dans `A`, et il est donné par la formule `Å = ⋃ {U ∈ 𝕌 | U ⊆ A}` (`eqdef:int_adh`). -/
theorem def_interieur [TopologicalSpace X] (A : Set X) :
    IsGreatest {U | IsOpen U ∧ U ⊆ A} (interior A) ∧
    interior A = ⋃₀ {U | IsOpen U ∧ U ⊆ A} :=
  ⟨⟨⟨isOpen_interior, interior_subset⟩, fun _ hU => interior_maximal hU.2 hU.1⟩, rfl⟩

/-- **Déf. `def:interieur` (Adhérence).** L'adhérence `Ā` est le plus petit fermé contenant
`A`, et elle est donnée par la formule `Ā = ⋂ {F ∈ 𝔽 | A ⊆ F}` (`eqdef:int_adh`). -/
theorem def_adherence [TopologicalSpace X] (A : Set X) :
    IsLeast {F | IsClosed F ∧ A ⊆ F} (closure A) ∧
    closure A = ⋂₀ {F | IsClosed F ∧ A ⊆ F} :=
  ⟨⟨⟨isClosed_closure, subset_closure⟩, fun _ hF => closure_minimal hF.2 hF.1⟩, rfl⟩

/-- **Éq. `eq:int_adh_compl`.** `X ∖ Å = closure (X ∖ A)` et `interior (X ∖ A) = X ∖ Ā`. -/
theorem eq_int_adh_compl [TopologicalSpace X] (A : Set X) :
    (interior A)ᶜ = closure Aᶜ ∧ interior Aᶜ = (closure A)ᶜ :=
  ⟨closure_compl.symm, interior_compl⟩

/-- **Éq. `eq:int_inter_adh_cup`.** `interior (A ∩ B) = Å ∩ B̊` et
`closure (A ∪ B) = Ā ∪ B̄`. -/
theorem eq_int_inter_adh_cup [TopologicalSpace X] (A B : Set X) :
    interior (A ∩ B) = interior A ∩ interior B ∧ closure (A ∪ B) = closure A ∪ closure B :=
  ⟨interior_inter, closure_union⟩

/-- **Déf. `def:dense` (Partie dense).** `A` est dense ssi `Ā = X`.
Mathlib : `Dense A`. -/
theorem def_dense [TopologicalSpace X] (A : Set X) : Dense A ↔ closure A = univ :=
  dense_iff_closure_eq

/-- **Déf. `def:dense` (Séparabilité).** `X` est séparable ssi il admet une partie
dénombrable dense. Mathlib : `SeparableSpace X`. -/
theorem def_separable [TopologicalSpace X] :
    SeparableSpace X ↔ ∃ A : Set X, A.Countable ∧ Dense A :=
  ⟨fun _ => exists_countable_dense X, fun ⟨A, hc, hd⟩ => ⟨⟨A, hc, hd⟩⟩⟩

end M1Analyse
