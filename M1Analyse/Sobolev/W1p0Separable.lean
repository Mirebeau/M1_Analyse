/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.W1p
import M1Analyse.Sobolev.FonctionsTest

/-!
# Séparabilité de `W^{1,p}_0(Ω)` (`rem:bcDirichlet`)

`W^{1,p}_0(Ω)` est séparable, pour tout `p ∈ [1, ∞]` : c'est l'adhérence de l'image de
`𝓓(Ω)`, séparable (`prop_testFunSeparab`), par l'injection continue `φ ↦ (φ, ∇φ)`.
-/

open MeasureTheory Set
open scoped ENNReal Distributions

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Une fonction test est dans `L^p(Ω)`. -/
private lemma sepW10_memLp (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) (φ : 𝓓(Ω, ℝ)) :
    MemLp φ p (volume.restrict (Ω : Set ℝᵈ)) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- Majoration `‖φ‖_{L^p(Ω)} ≤ |K|^{1/p} ‖φ‖_∞` pour `supp φ ⊆ K`. -/
private lemma sepW10_norm_le (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    (K : TopologicalSpace.Compacts ℝᵈ) (φ : 𝓓(Ω, ℝ)) (hφ : Function.support φ ⊆ K) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) :
    ‖(sepW10_memLp Ω p φ).toLp φ‖ ≤ (volume (K : Set ℝᵈ) ^ p.toReal⁻¹).toReal * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hK : volume (K : Set ℝᵈ) < ∞ := K.isCompact.measure_lt_top
  have h1 : eLpNorm φ p (volume.restrict (Ω : Set ℝᵈ)) ≤
      volume (K : Set ℝᵈ) ^ p.toReal⁻¹ * ENNReal.ofReal C := by
    calc eLpNorm φ p (volume.restrict (Ω : Set ℝᵈ)) ≤ eLpNorm φ p volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm φ p (volume.restrict (K : Set ℝᵈ)) :=
          (eLpNorm_restrict_eq_of_support_subset φ.continuous.aestronglyMeasurable hφ).symm
      _ ≤ _ := by
          refine (eLpNorm_le_of_ae_bound φ.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall hC)).trans_eq ?_
          rw [Measure.restrict_apply_univ]
  rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.ne) ENNReal.ofReal_ne_top) h1

/-- L'injection continue `𝓓(Ω) → L^p(Ω)`. -/
private noncomputable def sepW10_toLp (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : 𝓓(Ω, ℝ) →L[ℝ] Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) :=
  TestFunction.mkCLM ℝ (fun φ => (sepW10_memLp Ω p φ).toLp φ)
    (fun φ ψ => by rw [← MemLp.toLp_add]; rfl)
    (fun c φ => by rw [← MemLp.toLp_const_smul]; rfl)
    (fun K hK => by
      let L : 𝓓_{K}(ℝᵈ, ℝ) →+ Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) :=
        AddMonoidHom.mk' (fun f => (sepW10_memLp Ω p (TestFunction.ofSupportedIn hK f)).toLp _)
          (fun f g => by rw [← MemLp.toLp_add]; rfl)
      refine continuous_of_continuousAt_zero L ?_
      let B := ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ (E := ℝᵈ) (F := ℝ)
        (n := ⊤) (K := K)
      have hB : Filter.Tendsto (fun f => ‖B f‖) (nhds 0) (nhds 0) :=
        (continuous_norm.comp B.continuous).tendsto' 0 0 (by simp)
      rw [ContinuousAt, map_zero]
      refine squeeze_zero_norm (fun f => sepW10_norm_le Ω p K _ ?_ _ fun x => ?_)
        (by simpa using hB.const_mul (volume (K : Set ℝᵈ) ^ p.toReal⁻¹).toReal)
      · exact subset_tsupport _ |>.trans f.tsupport_subset
      · exact BoundedContinuousFunction.norm_coe_le_norm (B f) x)

/-- `φ ↦ (φ, ∇φ)` est continue de `𝓓(Ω)` dans `L^p(Ω) × L^p(Ω)^d`. -/
private lemma sepW10_continuous (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Continuous (testGrad Ω p) := by
  have h1 : (fun φ => (testGrad Ω p φ).fst) = sepW10_toLp Ω p := by
    funext φ
    exact Lp.ext ((testGrad_fst Ω p φ).trans (sepW10_memLp Ω p φ).coeFn_toLp.symm)
  have h2 : ∀ i, (fun φ => (testGrad Ω p φ).snd i) =
      sepW10_toLp Ω p ∘ TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    funext φ
    refine Lp.ext ((testGrad_snd Ω p φ i).trans ?_)
    refine (Filter.EventuallyEq.trans ?_ (sepW10_memLp Ω p _).coeFn_toLp.symm)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [TestFunction.lineDerivCLM_eq_fderivCLM]
    simp
  have hfst : Continuous fun φ => (testGrad Ω p φ).fst := h1 ▸ (sepW10_toLp Ω p).continuous
  have hsnd : Continuous fun φ => WithLp.ofLp (testGrad Ω p φ).snd :=
    continuous_pi fun i => h2 i ▸ (sepW10_toLp Ω p).continuous.comp
      (TestFunction.lineDerivCLM ℝ _).continuous
  have h : Continuous fun φ => WithLp.ofLp (testGrad Ω p φ) :=
    hfst.prodMk ((PiLp.continuousLinearEquiv p ℝ _).symm.continuous.comp hsnd)
  exact (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.continuous.comp h

/-- **Rem. `rem:bcDirichlet`, séparabilité.** `W^{1,p}_0(Ω)` est séparable, pour tout
`p ∈ [1, ∞]`.
Preuve (différente du cours, qui la déduit de celle de `W^{1,p}(Ω)`, `p < ∞`) : l'injection
`φ ↦ (φ, ∇φ)` de `𝓓(Ω)` dans `L^p(Ω) × L^p(Ω)^d` est continue (sur chaque `𝓓_K`,
`‖φ‖_{L^p} ≤ |K|^{1/p} ‖φ‖_∞`) ; `𝓓(Ω)` est séparable (`prop_testFunSeparab`), donc l'image et
son adhérence `W^{1,p}_0(Ω)` aussi. Le cas `p = ∞` est couvert, bien que `W^{1,∞}(Ω)` ne soit
pas séparable. -/
theorem rem_bcDirichlet_separable (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    TopologicalSpace.SeparableSpace (W1p0 Ω p) := by
  have := prop_testFunSeparab Ω
  have h : TopologicalSpace.IsSeparable (W1p0 Ω p : Set (LpGrad Ω p)) := by
    rw [W1p0, Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact (TopologicalSpace.isSeparable_range (sepW10_continuous Ω p)).closure
  exact h.separableSpace

end M1Analyse
