/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import M1Analyse.TopologieGenerale.EspacesFonctionnels

/-!
# §5 Fonctions test : séparabilité de `𝓓(Ω)` (début du chapitre `Sobolev`)

Source : `Include/Sobolev.tex`, début du chapitre (avant `subsec:convLp`).

`𝓓(Ω)` est l'espace `TestFunction` de Mathlib, muni de la topologie de limite inductive des
`𝓓_K(Ω)` (`ContDiffMapSupportedIn`).

Non formalisé : `lem:intDerivIter` (présenté sans preuve dans le cours), inutile pour la
preuve suivie de `prop:testFunSeparab`.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

private instance testFunSeparab_finDim (i : ℕ) : FiniteDimensional ℝ (ℝᵈ [×i]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear)
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- Restriction à `K` de la dérivée `i`-ème. -/
private noncomputable def testFunSeparab_res (K : Compacts ℝᵈ) (i : ℕ)
    (f : 𝓓_{K}(ℝᵈ, ℝ)) : C(K, ℝᵈ [×i]→L[ℝ] ℝ) :=
  ((ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f : ℝᵈ →ᵇ (ℝᵈ [×i]→L[ℝ] ℝ)) :
    C(ℝᵈ, ℝᵈ [×i]→L[ℝ] ℝ)).restrict K

private lemma testFunSeparab_dist (K : Compacts ℝᵈ) (i : ℕ) (f g : 𝓓_{K}(ℝᵈ, ℝ)) :
    dist (testFunSeparab_res K i f) (testFunSeparab_res K i g) =
      dist (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f)
        (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i g) := by
  apply le_antisymm
  · rw [ContinuousMap.dist_le dist_nonneg]
    intro x
    exact BoundedContinuousFunction.dist_coe_le_dist
      (f := ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f)
      (g := ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i g) (x : ℝᵈ)
  · rw [BoundedContinuousFunction.dist_le dist_nonneg]
    intro x
    by_cases hx : x ∈ (K : Set ℝᵈ)
    · exact ContinuousMap.dist_apply_le_dist (f := testFunSeparab_res K i f)
        (g := testFunSeparab_res K i g) ⟨x, hx⟩
    · simp only [ContDiffMapSupportedIn.structureMapLM_top_apply]
      rw [ContDiffMapSupportedIn.iteratedFDeriv_zero_on_compl f hx,
        ContDiffMapSupportedIn.iteratedFDeriv_zero_on_compl g hx]
      simp

private lemma testFunSeparab_induced (K : Compacts ℝᵈ) (i : ℕ) :
    (inferInstance : TopologicalSpace (ℝᵈ →ᵇ (ℝᵈ [×i]→L[ℝ] ℝ))).induced
        (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i : 𝓓_{K}(ℝᵈ, ℝ) → _) =
      (inferInstance : TopologicalSpace C(K, ℝᵈ [×i]→L[ℝ] ℝ)).induced
        (testFunSeparab_res K i) := by
  have h : PseudoMetricSpace.induced
        (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i : 𝓓_{K}(ℝᵈ, ℝ) → _) inferInstance =
      PseudoMetricSpace.induced (testFunSeparab_res K i) inferInstance := by
    ext f g
    exact (testFunSeparab_dist K i f g).symm
  exact congrArg (fun m : PseudoMetricSpace 𝓓_{K}(ℝᵈ, ℝ) ↦ m.toUniformSpace.toTopologicalSpace) h

private lemma testFunSeparab_secondCountable (K : Compacts ℝᵈ) :
    SecondCountableTopology 𝓓_{K}(ℝᵈ, ℝ) := by
  change @SecondCountableTopology _ (⨅ (i : ℕ), _)
  refine secondCountableTopology_iInf fun i ↦ ?_
  rw [testFunSeparab_induced K i]
  exact secondCountableTopology_induced _ _ _

/-- **Prop. `prop:testFunSeparab` (Séparabilité de `𝓓(Ω)`).** L'espace des fonctions test
`𝓓(Ω)` (muni de sa topologie de limite inductive) est séparable.
Preuve (différente du cours) : sans `lem:intDerivIter` ni Stone–Weierstrass. La topologie de
`𝓓_K` est la borne inférieure des topologies induites par `f ↦ D^i f` (`i ∈ ℕ`) ; comme `D^i f`
est nulle hors de `K`, chacune est induite par `f ↦ (D^i f)|_K ∈ C(K, G_i)`, espace à base
dénombrable (`K` compact, `G_i` de dimension finie) : `𝓓_K` est à base dénombrable. On conclut
par une suite exhaustive de compacts `K_n` de `Ω` et la continuité des inclusions
`𝓓_{K_n} → 𝓓(Ω)`. -/
theorem prop_testFunSeparab (Ω : TopologicalSpace.Opens ℝᵈ) :
    TopologicalSpace.SeparableSpace 𝓓(Ω, ℝ) := by
  obtain ⟨K, hK⟩ := prop_exhaustComp Ω.isOpen
  let L : ℕ → Compacts ℝᵈ := fun n ↦ ⟨K n, hK.1 n⟩
  have hLΩ : ∀ n, ((L n : Compacts ℝᵈ) : Set ℝᵈ) ⊆ Ω := fun n ↦
    hK.2.1 ▸ subset_iUnion K n
  have hD : ∀ n, ∃ D : Set 𝓓_{L n}(ℝᵈ, ℝ), D.Countable ∧ Dense D := fun n ↦ by
    have := testFunSeparab_secondCountable (L n)
    exact exists_countable_dense _
  choose D hDc hDd using hD
  refine ⟨⟨⋃ n, TestFunction.ofSupportedIn (hLΩ n) '' D n,
    countable_iUnion fun n ↦ (hDc n).image _, fun f ↦ ?_⟩⟩
  obtain ⟨n, hn⟩ := hK.exists_subset f.hasCompactSupport f.tsupport_subset
  let g : 𝓓_{L n}(ℝᵈ, ℝ) := ⟨f, f.contDiff, fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hn h)⟩
  have hfg : f = TestFunction.ofSupportedIn (hLΩ n) g := by ext x; rfl
  have := (TestFunction.continuous_ofSupportedIn (hLΩ n)).range_subset_closure_image_dense
    (hDd n) ⟨g, hfg.symm⟩
  exact closure_mono (subset_iUnion (fun n ↦ TestFunction.ofSupportedIn (hLΩ n) '' D n) n) this

end M1Analyse
