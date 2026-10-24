/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# §2.3 Prolongements (`subsec:prolongements`)

Source : `Include/Completude.tex`, sous-section `subsec:prolongements`.

Les objets du cours sont ceux de Mathlib : prolongement par densité = `Dense.extend`,
complété d'un espace métrique = `UniformSpace.Completion`, isométrie = `Isometry`,
bijection isométrique = `IsometryEquiv` (`≃ᵢ`).

Un module de continuité (`def:moduleCont`) est représenté par une fonction
`ω : ℝ≥0 → ℝ≥0∞` (ou `ℝ≥0 → ℝ≥0` lorsqu'il est à valeurs finies) telle que `ω(s) → 0` lorsque
`s → 0` (au sens `Tendsto ω (𝓝 0) (𝓝 0)`, qui inclut le point `s = 0`, d'où `ω(0) = 0`) ;
« `f` admet le module de continuité `ω` » signifie `d(f(x), f(y)) ≤ ω(d(x,y))` pour tous `x, y`.
-/

open Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace M1Analyse

/-- **Prop. `prop:prolongement_complet` (Prolongement des fonctions uniformément continues).**
Soient `(X,d)` un espace métrique, `(Y,d_Y)` un complet, `A ⊆ X` une partie dense, et
`f : A → Y` admettant un module de continuité `ω` (continu et croissant). Alors `f` admet une
unique extension continue `F : X → Y`, qui admet de plus le même module de continuité `ω`.
Preuve (différente du cours) : extension par `Dense.extend` de Mathlib (limites selon un
filtre) ; le module `ω` passe à `X × X` car l'inégalité définit un fermé contenant `A × A`. -/
theorem prop_prolongement_complet {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {A : Set X} (hA : Dense A) (f : A → Y) (ω : ℝ≥0 → ℝ≥0∞)
    (hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (hωc : Continuous ω) (_hωm : Monotone ω)
    (hf : ∀ a b : A, edist (f a) (f b) ≤ ω (nndist a b)) :
    ∃ F : X → Y, (Continuous F ∧ ∀ a : A, F a = f a) ∧
      (∀ x x' : X, edist (F x) (F x') ≤ ω (nndist x x')) ∧
      ∀ G : X → Y, Continuous G → (∀ a : A, G a = f a) → G = F := by
  -- `f` est uniformément continue.
  have hfu : UniformContinuous f := by
    refine Metric.uniformContinuous_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδω⟩ := Metric.eventually_nhds_iff.1
      (hω0.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    refine ⟨δ, hδ, fun {a b} hab => ?_⟩
    have h1 : dist (nndist a b) 0 < δ := by
      rwa [NNReal.dist_eq, NNReal.coe_zero, sub_zero, coe_nndist,
        abs_of_nonneg dist_nonneg]
    exact edist_lt_ofReal.1 ((hf a b).trans_lt (hδω h1))
  set F := hA.extend f with hF
  have hFc : Continuous F := (hA.uniformContinuous_extend hfu).continuous
  have hFA : ∀ a : A, F a = f a := hA.extend_of_ind hfu
  refine ⟨F, ⟨hFc, hFA⟩, fun x x' => ?_, fun G hG hGA => ?_⟩
  · -- L'ensemble des couples vérifiant l'inégalité est fermé et contient `A × A`, dense.
    have hS : IsClosed {q : X × X | edist (F q.1) (F q.2) ≤ ω (nndist q.1 q.2)} :=
      isClosed_le ((hFc.comp continuous_fst).edist (hFc.comp continuous_snd))
        (hωc.comp continuous_nndist)
    have hsub : A ×ˢ A ⊆ {q : X × X | edist (F q.1) (F q.2) ≤ ω (nndist q.1 q.2)} := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      change edist (F a) (F b) ≤ ω (nndist a b)
      rw [hFA ⟨a, ha⟩, hFA ⟨b, hb⟩]
      exact hf ⟨a, ha⟩ ⟨b, hb⟩
    have := closure_minimal hsub hS
    rw [(hA.prod hA).closure_eq] at this
    exact this (mem_univ (x, x'))
  · exact Continuous.ext_on hA hG hFc fun a ha => (hGA ⟨a, ha⟩).trans (hFA ⟨a, ha⟩).symm

/-- **Prop. `prop:espaceComplete` (Complété d'un espace métrique), existence.** Pour tout espace
métrique `(A,d)`, il existe un espace métrique complet `X` et une isométrie `ι : A → X`
d'image dense (une partie dense de `X` est donc en bijection isométrique avec `A`).
Mathlib : `X = UniformSpace.Completion A`.
Preuve (différente du cours) : complété de Mathlib, construit par filtres de Cauchy
minimaux et non comme quotient des suites de Cauchy. -/
theorem prop_espaceComplete {A : Type u} [MetricSpace A] :
    ∃ (X : Type u) (_ : MetricSpace X), CompleteSpace X ∧
      ∃ ι : A → X, Isometry ι ∧ DenseRange ι :=
  ⟨UniformSpace.Completion A, inferInstance, inferInstance, (↑),
    UniformSpace.Completion.coe_isometry, UniformSpace.Completion.denseRange_coe⟩

/-- **Prop. `prop:espaceComplete` (Complété d'un espace métrique), unicité.** Le complété est
unique à isométrie près : si `ι : A → X` et `ι' : A → X'` sont deux isométries d'image dense dans
des espaces métriques complets, il existe une bijection isométrique `e : X ≃ᵢ X'` telle que
`e ∘ ι = ι'`. -/
theorem prop_espaceComplete_unique {A X X' : Type*} [MetricSpace A] [MetricSpace X]
    [MetricSpace X'] [CompleteSpace X] [CompleteSpace X'] (ι : A → X) (ι' : A → X')
    (hι : Isometry ι) (hι' : Isometry ι') (hd : DenseRange ι) (hd' : DenseRange ι') :
    ∃ e : X ≃ᵢ X', ∀ a, e (ι a) = ι' a := by
  let pkg : AbstractCompletion A :=
    ⟨X, ι, inferInstance, inferInstance, inferInstance, hι.isUniformInducing, hd⟩
  let pkg' : AbstractCompletion A :=
    ⟨X', ι', inferInstance, inferInstance, inferInstance, hι'.isUniformInducing, hd'⟩
  let e : X ≃ᵤ X' := pkg.compareEquiv pkg'
  have he : ∀ a, e (ι a) = ι' a := pkg.compare_coe pkg'
  have hiso : Isometry e := by
    refine Isometry.of_dist_eq fun x y => ?_
    refine hd.induction_on₂ (p := fun x y => dist (e x) (e y) = dist x y)
      (isClosed_eq ((e.continuous.comp continuous_fst).dist (e.continuous.comp continuous_snd))
        continuous_dist) (fun a b => ?_) x y
    rw [he, he, hι'.dist_eq, hι.dist_eq]
  exact ⟨⟨e.toEquiv, hiso.edist_eq⟩, he⟩

/-- La fonction `F(x) := inf_{y ∈ A} f(y) + ω(d(x,y))` de l'exemple `ex:extUnifCont`. -/
noncomputable def extensionInf {X : Type*} [MetricSpace X] {A : Set X} (ω : ℝ≥0 → ℝ≥0)
    (f : A → ℝ) (x : X) : ℝ :=
  ⨅ y : A, f y + ω (nndist x y)

/-- **Ex. `ex:extUnifCont` (Extension de fonctions uniformément continues).** Soient `(X,d)` un
espace métrique, `A ⊆ X` non vide et `f : A → ℝ` admettant un module de continuité `ω` croissant
et sous-additif. Alors `F(x) := inf_{y ∈ A} f(y) + ω(d(x,y))` est à valeurs finies (l'ensemble
dont on prend l'inf est minoré), prolonge `f` et admet le module de continuité `ω`.
Remarque : `ω` est pris à valeurs dans `ℝ₊`, ce qui ne restreint pas la généralité, un module
de continuité sous-additif étant à valeurs finies (`rem:dist_of_mod_cont`). -/
theorem ex_extUnifCont {X : Type*} [MetricSpace X] {A : Set X} (hA : A.Nonempty) (f : A → ℝ)
    (ω : ℝ≥0 → ℝ≥0) (hω0 : Tendsto ω (𝓝 0) (𝓝 0)) (hωm : Monotone ω)
    (hωs : ∀ s t, ω (s + t) ≤ ω s + ω t) (hf : ∀ a b : A, dist (f a) (f b) ≤ ω (nndist a b)) :
    (∀ x : X, BddBelow (range fun y : A => f y + ω (nndist x y))) ∧
    (∀ a : A, extensionInf ω f a = f a) ∧
    ∀ x z : X, dist (extensionInf ω f x) (extensionInf ω f z) ≤ ω (nndist x z) := by
  have : Nonempty A := hA.to_subtype
  have hω00 : ω 0 = 0 :=
    tendsto_nhds_unique (tendsto_pure_nhds ω 0) (hω0.mono_left (pure_le_nhds 0))
  have htri : ∀ a b c : X, (ω (nndist a c) : ℝ) ≤ ω (nndist a b) + ω (nndist b c) := by
    intro a b c
    exact_mod_cast (hωm (nndist_triangle a b c)).trans (hωs _ _)
  have hf' : ∀ a b : A, f a - f b ≤ ω (nndist (a : X) b) := fun a b =>
    (le_abs_self _).trans (hf a b)
  -- Minoration : `f(y) + ω(d(x,y)) ≥ f(y₀) - ω(d(x,y₀))`.
  have hbdd : ∀ x : X, BddBelow (range fun y : A => f y + ω (nndist x y)) := by
    intro x
    obtain ⟨y₀⟩ := ‹Nonempty A›
    refine ⟨f y₀ - ω (nndist x y₀), ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := hf' y₀ y
    have h2 := htri y₀ x y
    rw [nndist_comm (y₀ : X) x] at h2
    linarith
  refine ⟨hbdd, fun a => le_antisymm ?_ ?_, fun x z => ?_⟩
  · refine (ciInf_le (hbdd a) a).trans ?_
    simp [hω00]
  · exact le_ciInf fun y => by linarith [hf' a y]
  · -- `F(z) ≤ F(x) + ω(d(x,z))`, et symétriquement.
    have key : ∀ x z : X, extensionInf ω f z ≤ extensionInf ω f x + ω (nndist x z) := by
      intro x z
      rw [← sub_le_iff_le_add]
      refine le_ciInf fun y => ?_
      have h1 := ciInf_le (hbdd z) y
      have h2 := htri z x y
      rw [nndist_comm z x] at h2
      change extensionInf ω f z ≤ _ at h1
      linarith
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · have := key z x
      rw [nndist_comm z x] at this
      linarith
    · linarith [key x z]

end M1Analyse
