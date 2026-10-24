/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Instances.Discrete

/-!
# §3.4 Produits de compacts (`subsec:compactProd`)

Source : `Include/Compacite.tex`, sous-section `subsec:compactProd`.

Les objets du cours sont ceux de Mathlib : le produit `∏ X_i` muni de la topologie produit est
`(i : ι) → X i`, un « compact métrique » est un espace compact métrisable
(`TopologicalSpace.MetrizableSpace`), le dual `E^*` muni de la topologie *faible est
`WeakDual 𝕜 E` (boule unité : `toStrongDual ⁻¹' closedBall 0 1`), l'enveloppe convexe est
`convexHull ℝ`. Pour le théorème d'Ascoli, `X` étant compact, les applications continues
`X → Y` sont bornées et l'on travaille dans `X →ᵇ Y`, dont la distance est celle de la
convergence uniforme `d(f, g) = sup_x d_Y(f x, g x)` (un maximum, par `corol:bornesAtteintes`).
-/

open Set Filter Topology Metric

namespace M1Analyse

/-- **Th. `th:compProdTycho` (Tychonov).** Un produit d'espaces compacts (séparés) est compact
(et séparé) pour la topologie produit.
Preuve (absente du cours, qui ne traite que le cas dénombrable métrique) : instance de
Mathlib, par ultrafiltres. -/
theorem th_compProdTycho {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] :
    CompactSpace ((i : ι) → X i) ∧ T2Space ((i : ι) → X i) :=
  ⟨inferInstance, inferInstance⟩

/-- **Th. `th:compProdTycho`, cas dénombrable.** Le produit d'une famille dénombrable de
compacts métriques est un compact métrique (compact et métrisable).
Preuve (différente du cours) : instances de Mathlib : Tychonov général (ultrafiltres), et
métrisabilité car la structure uniforme d'un produit dénombrable est à base dénombrable ; sans
l'extraction diagonale du cours. -/
theorem th_compProdTycho_metrique {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace ((i : ι) → X i) ∧ TopologicalSpace.MetrizableSpace ((i : ι) → X i) :=
  ⟨inferInstance, inferInstance⟩

/-- **Ex. `ex:formuleLogique` (Satisfiabilité de formules logiques).** Une formule logique est
une application `f : {0,1}^ℕ → {0,1}` (ici `{0,1} = Bool`) ne dépendant que d'un nombre fini de
variables : `f(x) = f(x_0, …, x_N, 0, 0, …)`. Un ensemble `𝓕` de formules logiques est
satisfiable (`∃ x, ∀ f ∈ 𝓕, f x = 1`) ssi toutes ses parties finies sont satisfiables. -/
theorem ex_formuleLogique (𝓕 : Set ((ℕ → Bool) → Bool))
    (h𝓕 : ∀ f ∈ 𝓕, ∃ N : ℕ, ∀ x, f x = f (fun i => if i ≤ N then x i else false)) :
    (∃ x, ∀ f ∈ 𝓕, f x = true) ↔
      ∀ 𝓕₀ ⊆ 𝓕, 𝓕₀.Finite → ∃ x, ∀ f ∈ 𝓕₀, f x = true := by
  -- les formules logiques sont continues pour la topologie produit
  have hcont : ∀ f ∈ 𝓕, Continuous f := by
    intro f hf
    obtain ⟨N, hN⟩ := h𝓕 f hf
    let F : (Fin (N + 1) → Bool) → Bool :=
      fun y => f (fun i => if h : i ≤ N then y ⟨i, by omega⟩ else false)
    have : f = F ∘ fun x (j : Fin (N + 1)) => x j := by
      funext x
      simp only [Function.comp_apply, F]
      rw [hN x]
      congr 1
    rw [this]
    exact continuous_of_discreteTopology.comp (continuous_pi fun j => continuous_apply _)
  constructor
  · rintro ⟨x, hx⟩ 𝓕₀ h𝓕₀ -
    exact ⟨x, fun f hf => hx f (h𝓕₀ hf)⟩
  · intro h
    by_contra hsat
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed
      (fun f : 𝓕 => (f : (ℕ → Bool) → Bool) ⁻¹' {true})
      (fun f => isClosed_singleton.preimage (hcont f f.2)) (by
        rw [univ_disjoint, eq_empty_iff_forall_notMem]
        intro x hx
        exact hsat ⟨x, fun f hf => by simpa using mem_iInter.1 hx ⟨f, hf⟩⟩)
    obtain ⟨x, hx⟩ := h (Subtype.val '' (u : Set 𝓕)) (by rintro _ ⟨f, -, rfl⟩; exact f.2)
      (u.finite_toSet.image _)
    rw [univ_disjoint, eq_empty_iff_forall_notMem] at hu
    exact hu x (mem_iInter₂.2 fun f hf => hx f ⟨f, hf, rfl⟩)

section BanachAlaoglu

variable (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Th. `th:BanachAlaoglu` (Banach-Alaoglu).** La boule unité fermée `B = B'_{E^*}(0,1)` du
dual d'un Banach `E` est compacte pour la topologie *faible (et `WeakDual 𝕜 E` est séparé).
(La complétude de `E` n'est pas utilisée.)
Preuve (absente du cours, qui ne traite que le cas séparable) : théorème de Mathlib
`WeakDual.isCompact_closedBall` (plongement dans un produit de disques et Tychonov). -/
theorem th_BanachAlaoglu [CompleteSpace E] :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) ∧
      T2Space (WeakDual 𝕜 E) :=
  ⟨WeakDual.isCompact_closedBall 0 1, inferInstance⟩

/-- **Th. `th:BanachAlaoglu`, cas séparable.** Si `E` est séparable, alors `B`, munie de la
topologie *faible, est un compact métrique (compact et métrisable).
Preuve (différente du cours) : compacité par le cas général ; métrisabilité (Mathlib) car les
évaluations en une suite dense séparent les points, d'où un plongement du compact dans un produit
dénombrable métrisable. Sans l'extraction diagonale du cours. -/
theorem th_BanachAlaoglu_separable [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    CompactSpace (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) ∧
      TopologicalSpace.MetrizableSpace
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) :=
  ⟨isCompact_iff_compactSpace.1 (WeakDual.isCompact_closedBall 0 1),
    WeakDual.metrizable_of_isCompact 𝕜 E _ (WeakDual.isCompact_closedBall 0 1)⟩

end BanachAlaoglu

section Ascoli

open BoundedContinuousFunction

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]

/-- **Th. `th:AscoliLip` (Ascoli).** Soient `X`, `Y` des espaces métriques compacts. L'ensemble
`Lip_1(X, Y)` des applications `1`-Lipschitz est compact pour la topologie de la convergence
uniforme (distance `d(f, g) = max_x d_Y(f x, g x)` de `X →ᵇ Y`).
Preuve (différente du cours) : `arzela_ascoli₂` de Mathlib (fermé, équicontinu, à valeurs dans un
compact) : précompacité par discrétisation finie (valeurs sur un recouvrement fini de `X`, arrondies
dans un `ε`-réseau fini de `Y`) ; pas d'extraction diagonale sur une partie dense. -/
theorem th_AscoliLip : IsCompact {f : X →ᵇ Y | LipschitzWith 1 f} := by
  have hset : {f : X →ᵇ Y | LipschitzWith 1 f} =
      ⋂ (x : X) (y : X), {f : X →ᵇ Y | dist (f x) (f y) ≤ dist x y} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hf x y
      simpa using hf.dist_le_mul x y
    · intro hf
      exact LipschitzWith.of_dist_le_mul fun x y => by simpa using hf x y
  refine arzela_ascoli₂ univ isCompact_univ _ ?_ (fun _ _ _ => mem_univ _) ?_
  · rw [hset]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
  · refine (Metric.uniformEquicontinuous_of_continuity_modulus id tendsto_id _
      fun x y f => ?_).equicontinuous
    simpa using f.2.dist_le_mul x y

/-- **Cor. `corol:AscoliEquicont` (Ascoli équicontinu).** Soient `X`, `Y` des espaces métriques
compacts et `𝓕 ⊆ C⁰(X, Y)` (ici `X →ᵇ Y`) une famille équicontinue. Alors `𝓕` est uniformément
équicontinue, et `𝓕̄` est compact pour la topologie de la convergence uniforme.
Preuve (différente du cours) : Heine et Arzelà-Ascoli de Mathlib appliqués directement, sans
se ramener à `th:AscoliLip` par le changement de distance `ω ∘ d_X`. -/
theorem corol_AscoliEquicont (𝓕 : Set (X →ᵇ Y))
    (h𝓕 : Equicontinuous ((↑) : 𝓕 → X → Y)) :
    UniformEquicontinuous ((↑) : 𝓕 → X → Y) ∧ IsCompact (closure 𝓕) :=
  ⟨CompactSpace.uniformEquicontinuous_of_equicontinuous h𝓕,
    arzela_ascoli univ isCompact_univ 𝓕 (fun _ _ _ => mem_univ _) h𝓕⟩

end Ascoli

/-- **Prop. `prop:hullCompact` (Compacité de l'enveloppe convexe fermée).** Soit `K` une partie
d'un `ℝ`-Banach. Si `K̄` est compact, alors `H = closure (Hull K)` est compact.
Preuve (différente du cours) : l'enveloppe convexe d'une partie précompacte est précompacte
(Mathlib : `Hull K ⊆ Hull t + V`, `t` réseau fini et `Hull t` compact), et `H` est fermé dans un
complet ; pas d'extraction diagonale. -/
theorem prop_hullCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact (closure K)) : IsCompact (closure (convexHull ℝ K)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨(hK.totallyBounded.subset subset_closure).convexHull.closure,
    isClosed_closure.isComplete⟩

section Caratheodory

variable {d : ℕ}

/-- Somme d'une fonction prolongée par zéro le long d'un plongement. -/
private theorem sum_extend_embedding {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ↪ κ) (g : ι → M) : ∑ j, Function.extend e g 0 j = ∑ i, g i := by
  classical
  calc ∑ j, Function.extend e g 0 j = ∑ j ∈ Finset.univ.map e, Function.extend e g 0 j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hj
        rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply]
    _ = ∑ i, Function.extend e g 0 (e i) := Finset.sum_map _ _ _
    _ = ∑ i, g i := by simp only [e.injective.extend_apply]

/-- Le simplexe `Δ^d = {λ ∈ ℝ_+^{d+1} | ∑ λ_i = 1}` est compact. -/
private theorem isCompact_simplexe (n : ℕ) :
    IsCompact {l : Fin n → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1} := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    ?_ ?_
  · rw [ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le continuous_const
      (continuous_apply (A := fun _ : Fin n => ℝ) i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · rintro l ⟨hl, hl1⟩ i -
    exact ⟨hl i, hl1 ▸ Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)⟩

/-- **Th. `th:Caratheodory` (Carathéodory).** Pour tout `A ⊆ ℝ^d`, l'enveloppe convexe de `A`
est l'ensemble des combinaisons convexes `∑_{0 ≤ i ≤ d} λ_i x_i` de `d + 1` points de `A`,
avec `λ ∈ Δ^d`.
Preuve (via Mathlib, même stratégie que le cours) : `eq_pos_convex_span_of_mem_convexHull` (une
représentation de cardinal minimal est affinement indépendante, donc a au plus `d + 1` points),
complétée par des poids nuls. -/
theorem th_Caratheodory (A : Set (EuclideanSpace ℝ (Fin d))) :
    convexHull ℝ A = {y | ∃ (l : Fin (d + 1) → ℝ) (x : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
      (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ (∀ i, x i ∈ A) ∧ y = ∑ i, l i • x i} := by
  ext y
  constructor
  · intro hy
    obtain ⟨ι, _, z, w, hzA, hz, hw, hw1, hy⟩ := eq_pos_convex_span_of_mem_convexHull hy
    have hcard : Fintype.card ι ≤ Fintype.card (Fin (d + 1)) := by
      refine hz.card_le_finrank_succ.trans ?_
      simp only [Fintype.card_fin, add_le_add_iff_right]
      exact (Submodule.finrank_le _).trans (by simp)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hw1
    obtain ⟨i₀⟩ := hne
    refine ⟨Function.extend e w 0, Function.extend e z fun _ => z i₀, fun j => ?_, ?_,
      fun j => ?_, ?_⟩
    · by_cases h : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := h
        rw [e.injective.extend_apply]
        exact (hw i).le
      · rw [Function.extend_apply' _ _ _ h]
        rfl
    · rw [sum_extend_embedding e w, hw1]
    · by_cases h : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := h
        rw [e.injective.extend_apply]
        exact hzA (mem_range_self i)
      · rw [Function.extend_apply' _ _ _ h]
        exact hzA (mem_range_self i₀)
    · have : ∀ j, Function.extend e w 0 j • Function.extend e z (fun _ => z i₀) j =
          Function.extend e (fun i => w i • z i) 0 j := fun j => by
        by_cases h : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := h
          simp only [e.injective.extend_apply]
        · simp only [Function.extend_apply' _ _ _ h, Pi.zero_apply, zero_smul]
      simp_rw [this]
      rw [sum_extend_embedding e _, hy]
  · rintro ⟨l, x, hl, hl1, hx, rfl⟩
    exact (convex_convexHull ℝ A).sum_mem (fun i _ => hl i) hl1
      (fun i _ => subset_convexHull ℝ A (hx i))

/-- **Th. `th:Caratheodory`, conséquence.** L'enveloppe convexe d'un compact `K ⊆ ℝ^d` est
compacte. -/
theorem th_Caratheodory_compact {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  let Φ : (Fin (d + 1) → ℝ) × (Fin (d + 1) → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d) := fun p => ∑ i, p.1 i • p.2 i
  have hΦ : Continuous Φ := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  have : convexHull ℝ K =
      Φ '' ({l : Fin (d + 1) → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1} ×ˢ univ.pi fun _ => K) := by
    rw [th_Caratheodory]
    ext y
    constructor
    · rintro ⟨l, x, hl, hl1, hx, rfl⟩
      exact ⟨(l, x), ⟨⟨hl, hl1⟩, fun i _ => hx i⟩, rfl⟩
    · rintro ⟨⟨l, x⟩, ⟨⟨hl, hl1⟩, hx⟩, rfl⟩
      exact ⟨l, x, hl, hl1, fun i => hx i (mem_univ i), rfl⟩
  rw [this]
  exact ((isCompact_simplexe (d + 1)).prod (isCompact_univ_pi fun _ => hK)).image hΦ

end Caratheodory

end M1Analyse
