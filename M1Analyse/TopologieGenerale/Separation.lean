/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic

/-!
# §1.1.4 Séparation (`subsubsec:separation`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section `subsubsec:separation`.

Les espaces séparés (T2) et l'axiome T1 du cours sont les classes Mathlib `T2Space` et
`T1Space`. La topologie cofinie de l'exemple `ex:T1nonT2` est `CofiniteTopology ℕ`.
La topologie de Zariski sur `ℂ^d` (absente de Mathlib sous cette forme : Mathlib la définit
sur le spectre premier d'un anneau) est construite ici par ses fermés, à l'aide de
`TopologicalSpace.ofClosed`, sur le synonyme de type `M1Analyse.Zariski d`.
-/

open Set Filter Topology

namespace M1Analyse

variable {X : Type*} [TopologicalSpace X]

/-- **Déf. `def:separe` (Espace séparé, T2).** `X` est séparé (`T2Space X`) ssi deux points
distincts admettent toujours des voisinages disjoints :
`∀ x, ∀ y ≠ x, ∃ U ∈ 𝒱_x, ∃ V ∈ 𝒱_y, U ∩ V = ∅`. -/
theorem def_separe :
    T2Space X ↔ ∀ x : X, ∀ y : X, y ≠ x → ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, U ∩ V = ∅ := by
  rw [t2Space_iff_nhds]
  simp only [Pairwise, ← disjoint_iff_inter_eq_empty]
  exact ⟨fun h x y hxy => h hxy.symm, fun h x y hxy => h x y (Ne.symm hxy)⟩

/-- **Rem. `rem:uniqueLim` (Unicité de la limite).** Dans un espace séparé, toute suite admet
au plus une limite. -/
theorem rem_uniqueLim [T2Space X] (u : ℕ → X) (a b : X)
    (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

/-- **Rem. `rem:T1` (Axiome T1 de Fréchet).** `X` satisfait l'axiome T1 (`T1Space X`) ssi,
étant donnés deux points distincts, chacun admet un voisinage ne contenant pas l'autre. -/
theorem rem_T1 :
    T1Space X ↔ ∀ x y : X, x ≠ y → (∃ U ∈ 𝓝 x, y ∉ U) ∧ (∃ V ∈ 𝓝 y, x ∉ V) := by
  have key : T1Space X ↔ ∀ x y : X, x ≠ y → ∃ U ∈ 𝓝 x, y ∉ U := by
    rw [t1Space_iff_exists_open]
    refine ⟨fun h x y hxy => ?_, fun h x y hxy => ?_⟩
    · obtain ⟨U, hU, hxU, hyU⟩ := h hxy
      exact ⟨U, hU.mem_nhds hxU, hyU⟩
    · obtain ⟨U, hU, hyU⟩ := h x y hxy
      obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
      exact ⟨V, hV, hxV, fun hy => hyU (hVU hy)⟩
  rw [key]
  exact ⟨fun h x y hxy => ⟨h x y hxy, h y x hxy.symm⟩, fun h x y hxy => (h x y hxy).1⟩

/-- Dans la topologie cofinie sur `ℕ`, la suite `n ↦ n` converge vers tout point. -/
theorem tendsto_cofiniteTopology_nat (a : CofiniteTopology ℕ) :
    Tendsto (fun n : ℕ => CofiniteTopology.of n) atTop (𝓝 a) := by
  rw [CofiniteTopology.nhds_eq, ← Nat.cofinite_eq_atTop]
  exact le_sup_of_le_right CofiniteTopology.of.injective.tendsto_cofinite

/-- **Rem. `rem:T1`, suite.** L'axiome T1 ne garantit pas l'unicité de la limite : dans
l'espace T1 `ℕ` muni de la topologie cofinie (cf. `ex:T1nonT2`), la suite `n ↦ n` admet deux
limites distinctes (en fait, tout point en est limite). -/
theorem rem_T1_nonUnique :
    T1Space (CofiniteTopology ℕ) ∧ ∃ (u : ℕ → CofiniteTopology ℕ) (a b : CofiniteTopology ℕ),
      a ≠ b ∧ Tendsto u atTop (𝓝 a) ∧ Tendsto u atTop (𝓝 b) :=
  ⟨inferInstance, _, CofiniteTopology.of 0, CofiniteTopology.of 1, by decide,
    tendsto_cofiniteTopology_nat _, tendsto_cofiniteTopology_nat _⟩

/-- **Ex. `ex:T1nonT2` (Topologie cofinie).** Sur `ℕ` muni de la topologie cofinie
(`CofiniteTopology ℕ`), les fermés sont les parties finies (et `ℕ` lui-même) ; cet espace est
T1 mais pas T2.
Remarque : le cours dit « la topologie dont les fermés sont les parties finies » ; il faut
ajouter `ℕ` tout entier, qui est fermé dans toute topologie. -/
theorem ex_T1nonT2_cofinie :
    (∀ F : Set (CofiniteTopology ℕ), IsClosed F ↔ F.Finite ∨ F = univ) ∧
    T1Space (CofiniteTopology ℕ) ∧ ¬ T2Space (CofiniteTopology ℕ) := by
  refine ⟨fun F => CofiniteTopology.isClosed_iff.trans or_comm, inferInstance, fun h => ?_⟩
  have := rem_uniqueLim _ _ _ (tendsto_cofiniteTopology_nat (CofiniteTopology.of 0))
    (tendsto_cofiniteTopology_nat (CofiniteTopology.of 1))
  exact absurd this (by decide)

/-! ### Topologie de Zariski sur `ℂ^d` -/

open MvPolynomial

/-- L'ensemble `ℂ^d`, destiné à être muni de la topologie de Zariski (`ex:T1nonT2`). -/
def Zariski (d : ℕ) : Type := Fin d → ℂ

/-- Fermé de Zariski de `ℂ^d` (`ex:T1nonT2`) : ensemble de la forme
`{x ∈ ℂ^d | P₁(x) = ⋯ = P_I(x) = 0}`, où `I ≥ 0` est un entier et
`P₁, …, P_I ∈ ℂ[X₁, …, X_d]`. -/
def IsZariskiClosed (d : ℕ) (F : Set (Zariski d)) : Prop :=
  ∃ (I : ℕ) (P : Fin I → MvPolynomial (Fin d) ℂ), F = {x | ∀ i, eval x (P i) = 0}

/-- L'ensemble des zéros communs d'une famille quelconque de polynômes est un fermé de Zariski
(théorème de la base de Hilbert : l'idéal engendré est de type fini). -/
theorem isZariskiClosed_zeroLocus (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) :
    IsZariskiClosed d {x | ∀ p ∈ S, eval x p = 0} := by
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (Ideal.span S) : (Ideal.span S).FG)
  refine ⟨t.toList.length, fun i => t.toList.get i, ?_⟩
  ext x
  have hker : ∀ T : Set (MvPolynomial (Fin d) ℂ),
      (∀ p ∈ T, eval x p = 0) ↔ Ideal.span T ≤ RingHom.ker (eval x) := fun T => by
    rw [Ideal.span_le]; rfl
  simp only [mem_ofPred_eq]
  rw [hker S, ← ht, Submodule.span_le]
  constructor
  · intro h i
    exact h (Finset.mem_toList.mp (List.get_mem _ _))
  · intro h p hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hp)
    exact h i

/-- Les fermés de Zariski satisfont les axiomes des fermés (`rem:fermes`) : `Zariski d` est
muni de la topologie correspondante (preuve du cours, par la base de Hilbert). -/
instance (d : ℕ) : TopologicalSpace (Zariski d) :=
  TopologicalSpace.ofClosed {F | IsZariskiClosed d F}
    -- `∅` : `I = 1`, `P₁ = 1`.
    ⟨1, fun _ => 1, by
      ext x
      exact ⟨fun h => absurd h (notMem_empty x), fun h => by simpa using h 0⟩⟩
    -- intersection quelconque : base de Hilbert.
    (fun A hA => by
      have := isZariskiClosed_zeroLocus d
        {p | ∃ F ∈ A, ∃ (I : ℕ) (P : Fin I → MvPolynomial (Fin d) ℂ) (i : Fin I),
          F = {x | ∀ i, eval x (P i) = 0} ∧ p = P i}
      show IsZariskiClosed d (⋂₀ A)
      convert this using 2
      ext x
      simp only [mem_sInter, mem_ofPred_eq]
      constructor
      · rintro h p ⟨F, hF, I, P, i, rfl, rfl⟩
        exact h _ hF i
      · intro h F hF
        obtain ⟨I, P, rfl⟩ := hA hF
        exact fun i => h _ ⟨_, hF, I, P, i, rfl, rfl⟩)
    -- union de deux fermés : famille des produits `P_i Q_j`.
    (fun A ⟨I, P, hA⟩ B ⟨J, Q, hB⟩ => by
      refine ⟨I * J, fun k => P (finProdFinEquiv.symm k).1 * Q (finProdFinEquiv.symm k).2, ?_⟩
      ext x
      subst hA hB
      simp only [map_mul, mul_eq_zero]
      constructor
      · rintro (h | h) k
        · exact Or.inl (h _)
        · exact Or.inr (h _)
      · intro h
        by_contra hc
        have hc' : ¬ ((∀ i, eval x (P i) = 0) ∨ ∀ j, eval x (Q j) = 0) := hc
        rw [not_or] at hc'
        have hi : ¬ ∀ i, eval x (P i) = 0 := hc'.1
        have hj : ¬ ∀ j, eval x (Q j) = 0 := hc'.2
        simp only [not_forall] at hi hj
        obtain ⟨i, hi⟩ := hi
        obtain ⟨j, hj⟩ := hj
        have := h (finProdFinEquiv (i, j))
        simp only [Equiv.symm_apply_apply] at this
        tauto)

/-- **Ex. `ex:T1nonT2` (Topologie de Zariski), fermés.** Les fermés de `Zariski d` sont
exactement les fermés de Zariski `{P₁ = ⋯ = P_I = 0}`. -/
theorem ex_T1nonT2_zariski_isClosed (d : ℕ) (F : Set (Zariski d)) :
    IsClosed F ↔ IsZariskiClosed d F := by
  rw [← isOpen_compl_iff]
  change IsZariskiClosed d Fᶜᶜ ↔ _
  rw [compl_compl]

/-- **Ex. `ex:T1nonT2` (Topologie de Zariski), T1 et non T2.** `ℂ^d` muni de la topologie de
Zariski est T1, et n'est pas T2 dès que `d ≥ 1`.
Remarque : l'hypothèse `d ≥ 1` est nécessaire (non explicite dans le cours) : `ℂ^0` est un
point, donc séparé. -/
theorem ex_T1nonT2_zariski (d : ℕ) (hd : 1 ≤ d) :
    T1Space (Zariski d) ∧ ¬ T2Space (Zariski d) := by
  refine ⟨⟨fun a => ?_⟩, fun h => ?_⟩
  · -- `{a} = {X_k - a_k = 0, k = 1, …, d}`.
    rw [ex_T1nonT2_zariski_isClosed]
    refine ⟨d, fun k => X k - C (a k), ?_⟩
    ext x
    simp only [mem_singleton_iff, map_sub, eval_X, eval_C, sub_eq_zero]
    exact ⟨fun h k => h ▸ rfl, fun h => funext h⟩
  · -- deux points distincts
    let x : Zariski d := fun _ => 0
    let y : Zariski d := fun _ => 1
    have hxy : x ≠ y := fun h => by
      have := congrFun h ⟨0, hd⟩
      simp [x, y] at this
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
    obtain ⟨I, P, hP⟩ := (ex_T1nonT2_zariski_isClosed d Uᶜ).mp hU.isClosed_compl
    obtain ⟨J, Q, hQ⟩ := (ex_T1nonT2_zariski_isClosed d Vᶜ).mp hV.isClosed_compl
    have hx : x ∉ Uᶜ := fun h => h hxU
    have hy : y ∉ Vᶜ := fun h => h hyV
    rw [hP] at hx
    rw [hQ] at hy
    have hx' : ¬ ∀ i, eval x (P i) = 0 := hx
    have hy' : ¬ ∀ j, eval y (Q j) = 0 := hy
    simp only [not_forall] at hx' hy'
    obtain ⟨i, hi⟩ := hx'
    obtain ⟨j, hj⟩ := hy'
    -- `P_i Q_j` s'annule partout, donc est nul.
    have hzero : P i * Q j = 0 := by
      apply MvPolynomial.funext
      intro z
      simp only [map_mul, map_zero, mul_eq_zero]
      by_cases hz : z ∈ U
      · have hzV : (z : Zariski d) ∈ Vᶜ := fun h' => hUV.ne_of_mem hz h' rfl
        rw [hQ] at hzV
        exact Or.inr (hzV j)
      · have hzU : (z : Zariski d) ∈ Uᶜ := hz
        rw [hP] at hzU
        exact Or.inl (hzU i)
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact hi (by rw [h0, map_zero])
    · exact hj (by rw [h0, map_zero])

end M1Analyse
